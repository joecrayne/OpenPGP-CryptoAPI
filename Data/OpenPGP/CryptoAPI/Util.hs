module Data.OpenPGP.CryptoAPI.Util where

import Numeric
import Control.Applicative
import Data.Binary
import Data.Binary.Get (runGetOrFail)
import qualified Data.Serialize as Serialize
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LZ
import qualified Data.OpenPGP as OpenPGP

swing :: (((a -> b) -> b) -> c -> d) -> c -> a -> d
swing f c a = f ($ a) c

hush :: Either a b -> Maybe b
hush (Left _) = Nothing
hush (Right x) = Just x

toStrictBS :: LZ.ByteString -> BS.ByteString
toStrictBS = BS.concat . LZ.toChunks

toLazyBS :: BS.ByteString -> LZ.ByteString
toLazyBS = LZ.fromChunks . (:[])

oo :: (b -> c) -> (a -> a1 -> b) -> a -> a1 -> c
oo = (.) . (.)

hexString :: [Word8] -> String
hexString = foldr (pad `oo` showHex) ""
	where
	pad s | odd $ length s = '0':s
	      | otherwise = s

maybeDecode :: (Binary a) => LZ.ByteString -> Maybe a
maybeDecode = maybeGet get

maybeGet :: (Binary a) => Get a -> LZ.ByteString -> Maybe a
maybeGet g bs = (\(_,_,x) -> x) <$> hush (runGetOrFail g bs)

sDecode :: (Serialize.Serialize a) => BS.ByteString -> Maybe a
sDecode = hush . Serialize.decode

keyIdMatch :: String -> String -> Bool
keyIdMatch x y = all (uncurry (==)) $ uncurry (flip zip) $
	unzip $ zip (reverse x) (reverse y)

fromJustMPI :: Maybe OpenPGP.MPI -> Integer
fromJustMPI (Just (OpenPGP.MPI x)) = x
fromJustMPI _ = error "Not a Just MPI, Data.OpenPGP.CryptoAPI"

isSecretKey :: OpenPGP.Packet -> Bool
isSecretKey (OpenPGP.SecretKeyPacket {}) = True
isSecretKey                            _ = False

isAsymmetricSessionKey :: OpenPGP.Packet -> Bool
isAsymmetricSessionKey (OpenPGP.AsymmetricSessionKeyPacket {}) = True
isAsymmetricSessionKey                                       _ = False

isSymmetricSessionKey :: OpenPGP.Packet -> Bool
isSymmetricSessionKey (OpenPGP.SymmetricSessionKeyPacket {}) = True
isSymmetricSessionKey                                      _ = False

isEncryptedData :: OpenPGP.Packet -> Bool
isEncryptedData (OpenPGP.EncryptedDataPacket {}) = True
isEncryptedData                                _ = False

isUserID :: OpenPGP.Packet -> Bool
isUserID (OpenPGP.UserIDPacket {})        = True
isUserID _                                = False

isSignable :: OpenPGP.Packet -> Bool
isSignable (OpenPGP.LiteralDataPacket {}) = True
isSignable (OpenPGP.PublicKeyPacket {})   = True
isSignable (OpenPGP.SecretKeyPacket {})   = True
isSignable _                              = False

isKey :: OpenPGP.Packet -> Bool
isKey (OpenPGP.SecretKeyPacket {}) = True
isKey (OpenPGP.PublicKeyPacket {}) = True
isKey                            _ = False
