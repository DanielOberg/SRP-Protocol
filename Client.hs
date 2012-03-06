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
import Control.Monad
import GHC.Int
import Codec.Crypto.SimpleAES

padto bs size   | size > CB.length bs = CB.append bs (CB.replicate (size-(CB.length bs)) ('0'))
                | size < CB.length bs = CB.take size bs
                | size == CB.length bs = bs

main = withSocketsDo $ do
            serveraddress <- getArgs
            h <- connectTo (head serveraddress) (PortNumber 7331)
            result <- initiateUser h
            case result of
                Nothing -> return ()
                Just (username, sessionkey) -> getFiles h ((CB.pack (show sessionkey)) `padto` 32)
            threadDelay 100

getFiles handle sessionkey = do
    filelength <- liftM (\x -> (read x :: Int64)) (hGetLine handle)
    filename   <- hGetLine handle
    --filehandle <- openFile (filename_part filename) WriteMode
    putStrLn $ "Server wants to send: " ++ filename ++ " which is " ++ (show filelength) ++ " " ++ (show sessionkey)
    hSetBuffering handle (BlockBuffering Nothing)
    filecontent <- LB.hGetContents handle
    LB.writeFile filename (LB.take filelength (decodeWithAES sessionkey filecontent))
    --hClose filehandle 
    return ()

decodeWithAES pass = (decryptMsg ECB pass)
