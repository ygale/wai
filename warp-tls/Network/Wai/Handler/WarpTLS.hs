{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternGuards #-}

-- | HTTP over SSL/TLS support for Warp via the TLS package.

module Network.Wai.Handler.WarpTLS (
    -- * Settings
      TLSSettings
    , certFile
    , keyFile
    , onInsecure
    , tlsLogging
    , tlsAllowedVersions
    , tlsCiphers
    , defaultTlsSettings
    , tlsSettings
    , tlsSettingsMemory
    , tlsSettingsChain
    , tlsSettingsChainMemory
    , OnInsecure (..)
    -- * Runner
    , runTLS
    , runTLSSocket
    -- * Exception
    , WarpTLSException (..)
    ) where

import qualified Network.TLS as TLS
import Data.X509 (CertificateChain(CertificateChain))
import Data.X509.File (readSignedObject)
import Data.X509.Memory (readSignedObjectFromMemory)
import Network.Wai.Handler.Warp
import Network.Wai (Application)
import Network.Socket (Socket, sClose, withSocketsDo, SockAddr)
import qualified Data.ByteString as S
import qualified Data.ByteString.Lazy as L
import Control.Exception (bracket, finally, handle, fromException, try, IOException)
import qualified Network.TLS.Extra as TLSExtra
import qualified Data.ByteString as B
import Data.Streaming.Network (bindPortTCP, acceptSafe, safeRecv)
import Control.Applicative ((<$>))
import qualified Data.IORef as I
import Control.Exception (Exception, throwIO)
import Data.Typeable (Typeable)
import Data.Default.Class (def)
import qualified Crypto.Random.AESCtr
import Network.Wai.Handler.Warp.Buffer (allocateBuffer, bufferSize, freeBuffer)
import Network.Socket.ByteString (sendAll)
import Control.Monad (unless, void)
import Data.ByteString.Lazy.Internal (defaultChunkSize)
import qualified System.IO as IO
import System.IO.Error (isEOFError)

----------------------------------------------------------------

data TLSSettings = TLSSettings {
    certFile :: FilePath
    -- ^ File containing the certificate.
  , chainFiles :: [FilePath]
    -- ^ Files containing chain certificates.
  , keyFile :: FilePath
    -- ^ File containing the key.
  , certMemory :: Maybe S.ByteString
    -- ^ Bytes representing the certificate file.
  , chainMemory :: Maybe [S.ByteString]
    -- ^ Bytes representing chain certificate files.
  , keyMemory :: Maybe S.ByteString
    -- ^ Bytes representing the key file.
  , onInsecure :: OnInsecure
    -- ^ Do we allow insecure connections with this server as well? Default
    -- is a simple text response stating that a secure connection is required.
    --
    -- Since 1.4.0
  , tlsLogging :: TLS.Logging
    -- ^ The level of logging to turn on.
    --
    -- Default: 'TLS.defaultLogging'.
    --
    -- Since 1.4.0
  , tlsAllowedVersions :: [TLS.Version]
    -- ^ The TLS versions this server accepts.
    --
    -- Default: '[TLS.TLS10,TLS.TLS11,TLS.TLS12]'.
    --
    -- Since 1.4.2
  , tlsCiphers :: [TLS.Cipher]
    -- ^ The TLS ciphers this server accepts.
    --
    -- Default: '[TLSExtra.cipher_AES128_SHA1, TLSExtra.cipher_AES256_SHA1, TLSEtra.cipher_RC4_128_MD5, TLSExtra.cipher_RC4_128_SHA1]'
    --
    -- Since 1.4.2
  }

-- | Default 'TLSSettings'. Use this to create 'TLSSettings' with the field record name.
defaultTlsSettings :: TLSSettings
defaultTlsSettings = TLSSettings {
    certFile = "certificate.pem"
  , chainFiles = []
  , keyFile = "key.pem"
  , certMemory = Nothing
  , chainMemory = Nothing
  , keyMemory = Nothing
  , onInsecure = DenyInsecure "This server only accepts secure HTTPS connections."
  , tlsLogging = def
  , tlsAllowedVersions = [TLS.TLS10,TLS.TLS11,TLS.TLS12]
  , tlsCiphers = ciphers
  }

-- taken from stunnel example in tls-extra
ciphers :: [TLS.Cipher]
ciphers =
    [ TLSExtra.cipher_AES128_SHA1
    , TLSExtra.cipher_AES256_SHA1
    , TLSExtra.cipher_RC4_128_MD5
    , TLSExtra.cipher_RC4_128_SHA1
    ]

----------------------------------------------------------------

-- | An action when a plain HTTP comes to HTTP over TLS/SSL port.
data OnInsecure = DenyInsecure L.ByteString
                | AllowInsecure

----------------------------------------------------------------

-- | A smart constructor for 'TLSSettings'.
tlsSettings :: FilePath -- ^ Certificate file
            -> FilePath -- ^ Key file
            -> TLSSettings
tlsSettings cert key = defaultTlsSettings {
    certFile = cert
  , chainFiles = []
  , keyFile = key
  }

-- | A smart constructor for 'TLSSettings', but uses in-memory representations
-- of the certificate and key
--
-- Since 3.0.1
tlsSettingsMemory
    :: S.ByteString -- ^ Certificate bytes
    -> S.ByteString -- ^ Key bytes
    -> TLSSettings
tlsSettingsMemory cert key = defaultTlsSettings
    { certMemory = Just cert
    , chainMemory = Just []
    , keyMemory = Just key
    }

-- | A smart constructor for 'TLSSettings', with chain certificates.
--
-- Since 3.0.2
tlsSettingsChain
    :: FilePath -- ^ Certificate file
    -> [FilePath] -- ^ Chain certificate files
    -> FilePath -- ^ Key file
    -> TLSSettings
tlsSettingsChain cert chains key = defaultTlsSettings {
    certFile = cert
  , chainFiles = chains
  , keyFile = key
  }

-- | A smart constructor for 'TLSSettings', but uses in-memory representations
-- of the certificates and key, including chain certificates.
--
-- Since 3.0.2
tlsSettingsChainMemory
    :: S.ByteString -- ^ Certificate bytes
    -> [S.ByteString] -- ^ Chain certificate bytes
    -> S.ByteString -- ^ Key bytes
    -> TLSSettings
tlsSettingsChainMemory cert chains key = defaultTlsSettings
    { certMemory = Just cert
    , chainMemory = Just chains
    , keyMemory = Just key
    }

----------------------------------------------------------------


-- | Running 'Application' with 'TLSSettings' and 'Settings'.
runTLS :: TLSSettings -> Settings -> Application -> IO ()
runTLS tset set app = withSocketsDo $
    bracket
        (bindPortTCP (getPort set) (getHost set))
        sClose
        (\sock -> runTLSSocket tset set sock app)

----------------------------------------------------------------

-- | Running 'Application' with 'TLSSettings' and 'Settings' using
--   specified 'Socket'.
runTLSSocket :: TLSSettings -> Settings -> Socket -> Application -> IO ()
runTLSSocket tlsset@TLSSettings{..} set sock app = do
    credential <- case (certMemory, keyMemory) of
        (Nothing, Nothing) ->
            either error id <$> TLS.credentialLoadX509 certFile keyFile
        (mcert, mkey) -> do
            cert <- maybe (S.readFile certFile) return mcert
            key <- maybe (S.readFile keyFile) return mkey
            either error return $ TLS.credentialLoadX509FromMemory cert key
    chains <- maybe
                (mapM readSignedObject chainFiles)
                (return . map readSignedObjectFromMemory)
                chainMemory
    runTLSSocket' tlsset set (addChains chains credential) sock app
  where
    addChains chains (CertificateChain cert, key) =
        (CertificateChain $ concat $ cert : chains, key)

runTLSSocket' :: TLSSettings -> Settings -> TLS.Credential -> Socket -> Application -> IO ()
runTLSSocket' tlsset@TLSSettings{..} set credential sock app =
    runSettingsConnectionMakerSecure set get app
  where
    get = getter tlsset sock params
    params = def {
        TLS.serverWantClientCert = False
      , TLS.serverSupported = def {
          TLS.supportedVersions = tlsAllowedVersions
        , TLS.supportedCiphers  = tlsCiphers
        }
      , TLS.serverShared = def {
          TLS.sharedCredentials = TLS.Credentials [credential]
          }
      }

----------------------------------------------------------------

getter :: TLS.TLSParams params => TLSSettings -> Socket -> params -> IO (IO (Connection, Bool), SockAddr)
getter tlsset@TLSSettings{..} sock params = do
    (s, sa) <- acceptSafe sock
    return (mkConn tlsset s params, sa)

mkConn :: TLS.TLSParams params => TLSSettings -> Socket -> params -> IO (Connection, Bool)
mkConn tlsset s params = do
    firstBS <- safeRecv s 4096
    cachedRef <- I.newIORef firstBS
    if not (B.null firstBS) && B.head firstBS == 0x16 then
        httpOverTls tlsset s cachedRef params
      else
        plainHTTP tlsset s cachedRef

----------------------------------------------------------------

httpOverTls :: TLS.TLSParams params => TLSSettings -> Socket -> I.IORef B.ByteString -> params -> IO (Connection, Bool)
httpOverTls TLSSettings{..} s cachedRef params = do
    gen <- Crypto.Random.AESCtr.makeSystem
    ctx <- TLS.contextNew backend params gen
    TLS.contextHookSetLogging ctx tlsLogging
    TLS.handshake ctx
    readBuf <- allocateBuffer bufferSize
    writeBuf <- allocateBuffer bufferSize
    return (conn ctx readBuf writeBuf, True)
  where
    backend = TLS.Backend {
        TLS.backendFlush = return ()
      , TLS.backendClose = sClose s
      , TLS.backendSend  = sendAll s
      , TLS.backendRecv  = getNext cachedRef s
      }
    conn ctx readBuf writeBuf = Connection {
        connSendMany         = TLS.sendData ctx . L.fromChunks
      , connSendAll          = TLS.sendData ctx . L.fromChunks . return
      , connSendFile         = sendfile
      , connClose            = close
      , connRecv             = recv
      , connSendFileOverride = NotOverride
      , connReadBuffer       = readBuf
      , connWriteBuffer      = writeBuf
      , connBufferSize       = bufferSize
      }
      where
        sendfile fp offset len _th headers = do
            TLS.sendData ctx $ L.fromChunks headers
            IO.withBinaryFile fp IO.ReadMode $ \h -> do
                IO.hSeek h IO.AbsoluteSeek offset
                loop h $ fromIntegral len
          where
            loop _ remaining | remaining <= 0 = return ()
            loop h remaining = do
                bs <- B.hGetSome h defaultChunkSize
                unless (B.null bs) $ do
                    let x = B.take remaining bs
                    TLS.sendData ctx $ L.fromChunks [x]
                    loop h $ remaining - B.length x

        close = freeBuffer readBuf `finally`
                freeBuffer writeBuf `finally`
                void (tryIO $ TLS.bye ctx) `finally`
                TLS.contextClose ctx

        recv = handle onEOF go
          where
            onEOF e
              | Just TLS.Error_EOF <- fromException e       = return B.empty
              | Just ioe <- fromException e, isEOFError ioe = return B.empty                  | otherwise                                   = throwIO e
            go = do
                x <- TLS.recvData ctx
                if B.null x then
                    go
                  else
                    return x

tryIO :: IO a -> IO (Either IOException a)
tryIO = try

----------------------------------------------------------------

plainHTTP :: TLSSettings -> Socket -> I.IORef B.ByteString -> IO (Connection, Bool)
plainHTTP TLSSettings{..} s cachedRef = case onInsecure of
    AllowInsecure -> do
        conn' <- socketConnection s
        return (conn' { connRecv = getNext cachedRef s 4096 }, False)
    DenyInsecure lbs -> do
        sendAll s "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\n"
        mapM_ (sendAll s) $ L.toChunks lbs
        sClose s
        throwIO InsecureConnectionDenied

----------------------------------------------------------------

getNext :: I.IORef B.ByteString -> Socket -> Int -> IO B.ByteString
getNext cachedRef s size = do
    cached <- I.readIORef cachedRef
    loop cached
  where
    loop bs | B.length bs >= size = do
        let (x, y) = B.splitAt size bs
        I.writeIORef cachedRef y
        return x
    loop bs1 = do
        bs2 <- safeRecv s 4096
        if B.null bs2 then do
            -- FIXME does this deserve an exception being thrown?
            I.writeIORef cachedRef B.empty
            return bs1
          else
            loop $ B.append bs1 bs2

----------------------------------------------------------------

data WarpTLSException = InsecureConnectionDenied
    deriving (Show, Typeable)
instance Exception WarpTLSException
