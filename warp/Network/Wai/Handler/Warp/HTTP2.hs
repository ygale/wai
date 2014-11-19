{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Network.Wai.Handler.Warp.HTTP2 (isHTTP2, http2) where

import Blaze.ByteString.Builder
import Control.Arrow (first)
import Control.Concurrent (forkIO)
import Control.Concurrent.STM
import Control.Monad (when, unless, void)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import Data.CaseInsensitive (foldedCase, mk)
import Data.IORef (IORef, readIORef, newIORef, writeIORef, modifyIORef)
import Data.IntMap (IntMap)
import qualified Data.IntMap as M
import Data.Maybe (fromJust)
import Data.Monoid (mempty)
import qualified Network.HTTP.Types as H
import Network.Socket (SockAddr)
import Network.Wai
import Network.Wai.Handler.Warp.Header
import Network.Wai.Handler.Warp.Response
import qualified Network.Wai.Handler.Warp.Settings as S (Settings, settingsNoParsePath, settingsServerName)
import Network.Wai.Handler.Warp.Types
import Network.Wai.Internal (Request(..), Response(..), ResponseReceived(..))
import System.IO (withFile, IOMode(..))

import Network.HTTP2
import Network.HPACK

----------------------------------------------------------------

data Req = ReqHead HeaderList
         | ReqDatC ByteString
         | ReqDatE ByteString

data Rsp = RspFrame ByteString
         | RspDone

type ReqQueue = TQueue Req
type RspQueue = TQueue Rsp

data Context = Context {
    http2settings :: IORef Settings
  -- fixme: clean up for frames whose end stream do not arrive
  , idTable :: IORef (IntMap ReqQueue)
  , outputQ :: RspQueue
  , encodeHeaderTable :: IORef HeaderTable
  , decodeHeaderTable :: IORef HeaderTable
  }

----------------------------------------------------------------

newContext :: IO Context
newContext = do
    st <- newIORef defaultSettings
    tbl <- newIORef (M.empty)
    outQ <- newTQueueIO
    eht <- newHeaderTableForEncoding 4096 >>= newIORef
    dht <- newHeaderTableForDecoding 4096 >>= newIORef
    return $ Context st tbl outQ eht dht

----------------------------------------------------------------

http2ver :: H.HttpVersion
http2ver = H.HttpVersion 2 0

isHTTP2 :: Transport -> Bool
isHTTP2 TCP = False
isHTTP2 tls = useHTTP2
  where
    useHTTP2 = case tlsNegotiatedProtocol tls of
        Nothing    -> False
        Just proto -> "h2-" `BS.isPrefixOf` proto

----------------------------------------------------------------

http2 :: Connection -> InternalInfo -> SockAddr -> Transport -> S.Settings -> Source -> Application -> IO ()
http2 conn ii addr transport settings src app = do
    checkTLS
    checkPreface
    ctx <- newContext
    let enqout = enqueueRsp ctx ii settings
        mkreq = mkRequest settings addr
    void . forkIO $ frameReader ctx mkreq enqout src app
    let rsp = RspFrame $ settingsFrame id []
    atomically $ writeTQueue (outputQ ctx) rsp
    frameSender conn ctx
  where
    checkTLS = case transport of
        TCP -> inadequateSecurity conn
        tls -> unless (tls12orLater tls) $ inadequateSecurity conn
    tls12orLater tls = tlsMajorVersion tls == 3 && tlsMinorVersion tls >= 3
    checkPreface = do
        bytes <- readSource src
        when (BS.length bytes < connectionPrefaceLength) $ protocolError conn
        let (preface, frames) = BS.splitAt connectionPrefaceLength bytes
        when (connectionPreface /= preface) $ protocolError conn
        leftoverSource src frames

----------------------------------------------------------------

goaway :: Connection -> ErrorCodeId -> ByteString -> IO ()
goaway Connection{..} etype debugmsg = do
    let einfo = encodeInfo id 0
        frame = GoAwayFrame (toStreamIdentifier 0) etype debugmsg
        bytestream = encodeFrame einfo frame
    connSendAll bytestream
    connClose

protocolError :: Connection -> IO ()
protocolError conn = goaway conn ProtocolError "Preface mismatch"

inadequateSecurity :: Connection -> IO ()
inadequateSecurity conn = goaway conn InadequateSecurity "Weak TLS"

----------------------------------------------------------------

data Next = None | Done | Fork ReqQueue Int

frameReader :: Context -> MkReq -> EnqRsp -> Source -> Application -> IO ()
frameReader ctx mkreq enqout src app = do
    bs <- readSource src
    unless (BS.null bs) $ do
        case decodeFrame defaultSettings bs of -- fixme
            Left x            -> error (show x) -- fixme
            Right (frame,bs') -> do
                leftoverSource src bs'
                x <- switch ctx frame
                case x of
                    Done -> return ()
                    None -> frameReader ctx mkreq enqout src app
                    Fork inpQ stid -> do
                        void . forkIO $ reqReader mkreq enqout inpQ stid app
                        frameReader ctx mkreq enqout src app

switch :: Context -> Frame -> IO Next
switch Context{..} Frame{ framePayload = HeadersFrame _ hdrblk,
                          frameHeader = FrameHeader{..} } = do
    putStrLn "HeadersFrame"
    hdrtbl <- readIORef decodeHeaderTable
    (hdrtbl', hdr) <- decodeHeader hdrtbl hdrblk
    writeIORef decodeHeaderTable hdrtbl'
    m0 <- readIORef idTable
    let stid = fromStreamIdentifier streamId
    case M.lookup stid m0 of
        Just _  -> error "bad header frame" -- fixme
        Nothing -> do
            let end = testEndStream flags
            inpQ <- newTQueueIO
            unless end $ modifyIORef idTable $ \m -> M.insert stid inpQ m
            -- fixme: need to testEndHeader. ContinuationFrame is not
            -- support yet.
            atomically $ writeTQueue inpQ (ReqHead hdr)
            return $ Fork inpQ stid

switch Context{..} Frame{ framePayload = DataFrame body,
                          frameHeader = FrameHeader{..} } = do
    putStrLn "DataFrame"
    m0 <- readIORef idTable
    let stid = fromStreamIdentifier streamId
    case M.lookup stid m0 of
        Nothing -> error "No such stream" -- fixme
        Just q  -> do
            let end = testEndStream flags
                tag = if end then ReqDatE else ReqDatC
            atomically $ writeTQueue q (tag body)
            when end $ modifyIORef idTable $ \m -> M.delete stid m
            return None

switch Context{..} Frame{ framePayload = SettingsFrame alist,
                          frameHeader = FrameHeader{..} } = do
    if alist == [] then
        when (testAck flags) $ return () -- fixme: clearing timeout
      else do
        modifyIORef http2settings $ \old -> updateSettings old alist
        let rsp = RspFrame $ settingsFrame setAck []
        atomically $ writeTQueue outputQ rsp
    return None

-- fixme :: clean up should be more complex than this
switch Context{..} Frame{ framePayload = GoAwayFrame _ _ _,
                          frameHeader = FrameHeader{..} } = do
    putStrLn "GoAwayFrame"
    atomically $ writeTQueue outputQ RspDone
    return Done
{-
-- resetting
switch Context{..} (RSTStreamFrame _)     = undefined
-- ponging
switch Context{..} (PingFrame _)          = undefined
-- cleanup
switch Context{..} (GoAwayFrame _ _ _)    = undefined

-- Not supported yet
switch Context{..} (PriorityFrame _)      = undefined
switch Context{..} (WindowUpdateFrame _)  = undefined
switch Context{..} (PushPromiseFrame _ _) = undefined
switch Context{..} (UnknownFrame _ _)     = undefined
switch Context{..} (ContinuationFrame _)  = undefined
-}
switch _ Frame{..} = do
    putStrLn "switch"
    print $ toFrameTypeId $ framePayloadToFrameType framePayload
    return None

----------------------------------------------------------------

reqReader :: MkReq -> EnqRsp -> TQueue Req -> Int -> Application -> IO ()
reqReader mkreq enqout inpq stid app = do
    frag <- atomically $ readTQueue inpq
    case frag of
        ReqDatC _   -> error "ReqDatC" -- FIXMEX
        ReqDatE _   -> error "ReqDatE" -- FIXMEX
        ReqHead hdr -> do
            let req = mkreq hdr
            void $ app req $ enqout stid

----------------------------------------------------------------

type MkReq = HeaderList -> Request

-- fixme: fromJust -> protocol error?
mkRequest :: S.Settings -> SockAddr -> MkReq
mkRequest settings addr hdr = req
  where
    (unparsedPath,query) = B8.break (=='?') $ fromJust $ lookup ":path" hdr -- fixme
    path = H.extractPath unparsedPath
    req = Request {
        requestMethod = fromJust $ lookup ":method" hdr -- fixme
      , httpVersion = http2ver
      , rawPathInfo = if S.settingsNoParsePath settings then unparsedPath else path
      , pathInfo = H.decodePathSegments path
      , rawQueryString = query
      , queryString = H.parseQuery query
      , requestHeaders = map (first mk) hdr -- fixme: removing ":foo"
      , isSecure = True
      , remoteHost = addr
      , requestBody = undefined -- FIXMEX: from fragments
      , vault = mempty
      , requestBodyLength = ChunkedBody -- fixme
      , requestHeaderHost = lookup ":authority" hdr
      , requestHeaderRange = lookup "range" hdr
      }


----------------------------------------------------------------

{-
ResponseFile Status ResponseHeaders FilePath (Maybe FilePart)
ResponseBuilder Status ResponseHeaders Builder
ResponseStream Status ResponseHeaders StreamingBody
ResponseRaw (IO ByteString -> (ByteString -> IO ()) -> IO ()) Response
-}

-- enqueueRsp :: TQueue Rsp -> Int -> Response -> IO ResponseReceived

type EnqRsp = Int -> Response -> IO ResponseReceived

-- fixme: more efficient buffer handling
enqueueRsp :: Context -> InternalInfo -> S.Settings -> EnqRsp
enqueueRsp ctx@Context{..} ii settings stid (ResponseBuilder st hdr0 bb) = do
    hdrframe <- headerFrame ctx ii settings stid st hdr0
    atomically $ writeTQueue outputQ $ RspFrame hdrframe
    atomically $ writeTQueue outputQ $ RspFrame datframe
    return ResponseReceived
  where
    einfo = encodeInfo setEndStream stid
    datframe = encodeFrame einfo $ DataFrame $ toByteString bb

enqueueRsp ctx@Context{..} ii settings stid (ResponseFile st hdr0 file _) = do
    hdrframe <- headerFrame ctx ii settings stid st hdr0
    atomically $ writeTQueue outputQ $ RspFrame hdrframe
    withFile file ReadMode loop
    return ResponseReceived
  where
    -- fixme: more efficient buffering
    einfoEnd = encodeInfo setEndStream stid
    einfo = encodeInfo id stid
    loop hdl = do
        bs <- BS.hGet hdl 2048 -- fixme
        if BS.null bs then do
            -- fixme: this frame should be removed
            let datframe = encodeFrame einfoEnd $ DataFrame bs
            atomically $ writeTQueue outputQ $ RspFrame datframe
          else do
            let datframe = encodeFrame einfo $ DataFrame bs
            atomically $ writeTQueue outputQ $ RspFrame datframe
            loop hdl

enqueueRsp _ _ _ _ _ = do -- fixme
    putStrLn "enqueueRsp"
    return ResponseReceived

----------------------------------------------------------------

-- fixme: packing bytestrings
frameSender :: Connection -> Context -> IO ()
frameSender Connection{..} Context{..} = loop
  where
    loop = do
        cont <- readQ >>= send
        when cont loop
    readQ = atomically $ readTQueue outputQ
    send (RspFrame bs) = do
        connSendAll bs
        return True
    send RspDone = return False

----------------------------------------------------------------

settingsFrame :: (FrameFlags -> FrameFlags) -> SettingsList -> ByteString
settingsFrame func alist = encodeFrame einfo $ SettingsFrame alist
  where
    einfo = encodeInfo func 0

headerFrame :: Context -> InternalInfo -> S.Settings -> Int -> H.Status -> H.ResponseHeaders -> IO ByteString
headerFrame Context{..} ii settings stid st hdr0 = do
    hdr1 <- addServerAndDate hdr0
    let hdr2 = (":status", status) : map (first foldedCase) hdr1
    ehdrtbl <- readIORef encodeHeaderTable
    (ehdrtbl',hdrfrg) <- encodeHeader defaultEncodeStrategy ehdrtbl hdr2
    writeIORef encodeHeaderTable ehdrtbl'
    return $ encodeFrame einfo $ HeadersFrame Nothing hdrfrg
  where
    dc = dateCacher ii
    rspidxhdr = indexResponseHeader hdr0
    defServer = S.settingsServerName settings
    addServerAndDate = addDate dc rspidxhdr . addServer defServer rspidxhdr
    status = B8.pack $ show $ H.statusCode st
    einfo = encodeInfo setEndHeader stid
