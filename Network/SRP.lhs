SRP Protocol Design (http://srp.stanford.edu/design.html)
Code by Daniel Swe.

Recommendations from RFC 5054 (http://tools.ietf.org/html/rfc5054#ref-SRP-6)


SRP is the newest addition to a new class of strong authentication protocols that 
resist all the well-known passive and active attacks over the network. SRP borrows 
some elements from other key-exchange and identification protocols and 
adds some subtle modifications and refinements. The result is a protocol that 
preserves the strength and efficiency of the EKE family protocols while fixing some 
of their shortcomings.

> module Network.SRP (
>                       initiateHost, 
>                       initiateUser
>                    ) where

> import qualified Data.Digest.Pure.SHA as SHA
> import Data.ByteString.Lazy (ByteString)
> import qualified Data.ByteString.Lazy.Char8 as B
> import Data.Bits (xor)
> import System.IO
> import System.Random
> import Control.Concurrent (forkIO, threadDelay)
> import Network
> import Prelude hiding ((^^))
> import Data.Char
> import Data.Binary
> --import Test.QuickCheck

The following is a description of SRP-6 and 6a, the latest versions of SRP:

  N    A large safe prime (N = 2q+1, where q is prime)

> {-Large safe prime, all computations are performed modulo n', recommended to be > 512 bits-}
> n' = 0xEEAF0AB9ADB38DD69C33F80AFA8FC5E86072618775FF3C0B9EA2314C9C256576D674DF7496EA81D3383B4813D692C6E0E0D5D8E250B98BE48E495C1D6089DAD15DC7D7B46154D6B6CE8EF4AD69B15D4982559B297BCF1885C529F566660E57EC68EDBC3C05726CC02FD4CBF4976EAA9AFD5138FE8376435B9FC61D2FC0EB06E3
>

> nsize = B.length (encode n')


  g    A generator modulo N

> g = 2  {-A primitive root modulo n-}

  k    Multiplier parameter (k = H(N, g) in SRP-6a, k = 3 for legacy SRP-6)

> k = sha1 [encode n', pad g]

  s    User's salt
  I    Username
  p    Cleartext Password
  H()  One-way hash function

> sha1 :: [ByteString] -> Integer
> sha1 = SHA.integerDigest . SHA.sha1 . B.concat

> hashStr :: [String] -> Integer
> hashStr = SHA.integerDigest . SHA.sha256 . B.pack . unwords 

> hashInteger :: [Integer] -> Integer
> hashInteger = hashStr . map show

> pad :: Integer -> ByteString
> pad i = B.append (B.replicate padsize '\0') bytestr_i
>       where
>           bytestr_i = encode i
>           isize = B.length bytestr_i
>           padsize = fromIntegral (nsize - isize)

  ^    (Modular) Exponentiation

> (^^) :: Integer -> Integer -> Integer
> (^^) = powerWithModulus n'

  u    Random scrambling parameter
  a,b  Secret ephemeral values
  A,B  Public ephemeral values
  x    Private key (derived from p and s)
  v    Password verifier

The host stores passwords using the following formula:

  x = H(s, p)               (s is chosen randomly)
  v = g^x                   (computes password verifier)

The host then keeps {I, s, v} in its password database. 

> calcx :: String -> Integer -> String -> Integer
> calcx i' s p = sha1 [encode s, encode (sha1 [encode (i' ++ ":" ++ p)])]
> calcv = (g ^^)
> passwordDatabase = (i', s', v') where
>                       p' = "password"
>                       i' = "username"
>                       s' = 0xBEB25379D1A8581EB5A727673A2441EE
>                       v' = calcv (calcx i' s' p') 

The authentication protocol itself goes as follows:

User -> Host:  I, A = g^a                  (identifies self, a = random number)
Host -> User:  s, B = kv + g^b             (sends salt, b = random number)

        Both:  u = H(A, B)

        User:  x = H(s, p)                 (user enters password)
        User:  S = (B - kg^x) ^ (a + ux)   (computes session key)
        User:  K = H(S)

        Host:  S = (Av^u) ^ b              (computes session key)
        Host:  K = H(S)

> calcUserM1AndK i' s a a' b' u p = (m'1, k')
>                       where
>                           m'1 = hashInteger [hashInteger [n'] `xor` hashInteger [g], 
>                                   hashStr [i'], hashInteger [s], a', 
>                                   b', k']
>                           k'  = hashInteger [s']
>                           s' = (b' - (k*g^^x)) ^^ (a + u*x)
>                           x  = calcx i' s p

> calcHostM1AndK i' s b a' b' u v = (m'1, k')
>                       where
>                           m'1 = hashInteger [hashInteger [n'] `xor` hashInteger [g], 
>                                   hashStr [i'], hashInteger [s], a', 
>                                   b', k']
>                           k'  = hashInteger [s']
>                           s' = (a' * (v^^u)) ^^ b

> calcA a = g^^a `mod` n'

> calcB v b = (k*v+g^^b) `mod` n'


> userToHost i' a h p = do 
>           let a' = calcA a
>           send h [i', show a'] {-I, A-}
>           (s, b') <- receiveIntegerAndInteger h
>           let u = sha1 [pad a', pad b']
>           if ((b' `mod` n') == 0) || (u == 0)
>               then 
>                   do
>                       putStrLn "Received a random value b where b mod n == 0 or u == 0"
>                       return Nothing
>               else
>                   do
>                       let (m'1, k') = calcUserM1AndK i' s a a' b' u p
>                       send h [show m'1]
>                       m'2_from_host <- receiveInteger h
>                       let m'2 = hashInteger [a', m'1, k']
>                       if m'2 /= m'2_from_host
>                           then
>                               do
>                                   putStrLn (show m'2 ++ "/=" ++ show m'2_from_host)
>                                   return Nothing
>                           else
>                               return (Just (i', k'))


> hostToUser b h = do
>               let (_,s,v) = passwordDatabase
>               let b' = calcB v b
>               (i', a') <- receiveStringAndInteger h
>               if a' `mod` n' == 0 
>                   then
>                       return Nothing
>                   else
>                       do
>                           let u = sha1 [pad a', pad b']
>                           send h [show s, show b']
>                           m'1_from_user <- receiveInteger h
>                           let (m'1, k') = calcHostM1AndK i' s b a' b' u v
>                           if m'1 /= m'1_from_user
>                               then
>                                   do
>                                       putStrLn ("->" ++ show m'1 ++ "/=" ++ show m'1_from_user ++ "<-")
>                                       return Nothing
>                               else
>                                   do
>                                       let m'2 = hashInteger [a', m'1_from_user, k']
>                                       send h [show m'2]
>                                       return (Just (i', k'))

Now the two parties have a shared, strong session key K. To complete authentication, they need to prove to each other that their keys match. One possible way:

User -> Host:  M = H(H(N) xor H(g), H(I), s, A, B, K)
Host -> User:  H(A, M, K) 

The two parties also employ the following safeguards:

   1. The user will abort if he receives B == 0 (mod N) or u == 0.
   2. The host will abort if it detects that A == 0 (mod N).
   3. The user must show his proof of K first. If the server detects that the user's proof is incorrect, it must abort without showing its own proof of K.


> {-main = withSocketsDo $ do
>           randomGen <- newStdGen
>           let ((a, r1), (b, r2)) = (randomR (3, 1000) randomGen, randomR (3, 1000) randomGen)
>           let (i', s', v') = passwordDatabase
>           forkIO $ host
>           threadDelay 5000
>           result <- user a
>           putStr $ show result
>           runtest-}

> initiateHost h = do
>           b <- getStdRandom (randomR ((2^512), (2^1024)))
>           putStrLn "Server started, listening"
>           --sock <- listenOn (PortNumber 7331)
>           --(h, _, _) <- accept sock
>           hSetBuffering h LineBuffering
>           putStrLn "Server accepted connection"
>           result <- hostToUser b h
>           case result of
>               Nothing -> putStrLn "HOST: WARNING EXPLODING COOKIES"
>               Just (i', k') -> putStrLn ( "HOST: SUCCESS:" ++ show i' ++ "," ++ show k' )
>           --sClose sock
>           return result

> initiateUser h = do
>           a <- getStdRandom (randomR ((2^512), (2^1024)))
>           --h <- connectTo "127.0.0.1" (PortNumber 7331)
>           hSetBuffering h LineBuffering
>           result <- userToHost "username" a h "password"
>           putStrLn "Client started, connected"
>           case result of
>               Nothing -> putStrLn "USER: WARNING EXPLODING COOKIES"
>               Just (i', k') -> putStrLn ( "USER: SUCCESS:" ++ show i' ++ "," ++ show k')
>           return result

> send h = hPutStrLn h . unwords

> receiveInteger h = do
>           line <- hGetLine h
>           return (read line :: Integer)

> receiveIntegerAndInteger h = do
>           line <- hGetLine h
>           let words' = words line
>           return (read (words' !! 0) :: Integer, read (words' !! 1) :: Integer)

> receiveStringAndInteger h = do
>           line <- hGetLine h
>           let words' = words line
>           return (words' !! 0, read (words' !! 1) :: Integer)




    > instance Arbitrary Char where
    >     arbitrary     = choose ('\0', '\128')
    >     coarbitrary c = variant (ord c `rem` 4)
    > 
    > 
    > runtest = do
    >       quickCheck prop_SameResult
    >       quickCheck prop_NotSameResult
    > 
    > prop_SameResult a b i' p s = a > 1 && b>1 ==> calcUserM1AndK i' s a a' b' u p == calcHostM1AndK i' s b a' b' u v
    >                   where
    >                       u  = sha1 [pad a', pad b']
    >                       a' = calcA a
    >                       b' = calcB v b
    >                       v = calcv (calcx i' s p) 
    > prop_NotSameResult a b i' p s p' = a > 1 && b>1 && p /= p' ==> calcUserM1AndK i' s a a' b' u p /= calcHostM1AndK i' s b a' b' u v
    >                   where
    >                       u  = sha1 [pad a', pad b']
    >                       a' = calcA a
    >                       b' = calcB v b
    >                       v = calcv (calcx i' s p') 

> -- Daniel Fischer (http://www.mail-archive.com/haskell-cafe@haskell.org/msg08243.html)
> -- calculate a power with respect to a modulus, first tests and
> -- forwarding to another helper
> powerWithModulus :: Integer -> Integer -> Integer -> Integer
> powerWithModulus mo n k
>    | mo < 0     = powerWithModulus (-mo) n k
>    | mo == 0    = n^k
>    | k < 0      = error "powerWithModulus: negative exponent"
>    | k == 0     = 1
>    | k == 1     = n `mod` mo
>    | mo == 1    = 0
>    | odd k      = powerMod mo n n (k-1)
>    | otherwise  = powerMod mo 1 n k
> 
> -- calculate the power with auxiliary value to account for
> -- odd exponents on the way, we have @mo >= 2@ and @k >= 1@
> powerMod :: Integer -> Integer -> Integer -> Integer -> Integer
> powerMod mo aux val k
>    | k == 1 = (aux * val) `mod` mo
>    | odd k  =
>       ((powerMod mo $! ((aux*val) `mod` mo)) $! (val^2 `mod` mo)) $! (k `quot` 2)
>    | even k = (powerMod mo aux $! (val^2 `mod` mo)) $! (k `quot` 2)
> 
