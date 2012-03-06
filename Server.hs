{-# OPTIONS_GHC -fglasgow-exts -XViewPatterns #-}

import Network.SRP
import Network
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as CB
import qualified Data.ByteString.Lazy as LB
import System.Environment
import Control.Concurrent (forkIO, threadDelay)
import Data.Word
import Data.Maybe
import System.IO
import System.Path.NameManip
import Codec.Crypto.SimpleAES

padto bs size   | size > CB.length bs = CB.append bs (CB.replicate (size-(CB.length bs)) ('0'))
                | size < CB.length bs = CB.take size bs
                | size == CB.length bs = bs

main = withSocketsDo $ do
            files <- getArgs
            sock <- listenOn (PortNumber 7331)
            (h, _, _) <- accept sock
            result <- initiateHost h
            case result of
                Nothing -> return ()
                Just (username, sessionkey) -> giveFiles files h username ((CB.pack (show sessionkey)) `padto` 32)
            sClose sock

giveFiles files handle username sessionkey = do
    let filename = head files
    filesize <- getFileSize filename
    putStrLn $ "Sending: " ++ filename ++ (show filesize) ++ " to " ++ username  ++ " " ++ (show sessionkey)
    
    filecontent <- LB.readFile filename
    --let filecontent2 = LB.append filecontent (LB.replicate (fromInteger (16 - (filesize `mod` 16))) (0 :: Word8))
    hPutStrLn handle (show filesize)
    hPutStrLn handle (filename_part filename)
    hSetBuffering handle (BlockBuffering Nothing)
    iv <- newIV
    encryptedFile <- (encodeWithAES sessionkey filecontent)
    LB.hPut handle encryptedFile
    hFlush handle
    return ()

startiv = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] :: [Word8]

encodeWithAES pass = (encryptMsg ECB pass)

getFileSize path = do
  handle <- openFile path ReadMode
  filesize <- hFileSize handle
  hClose handle
  return filesize
