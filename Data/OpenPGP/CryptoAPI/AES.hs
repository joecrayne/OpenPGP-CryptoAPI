{-# LANGUAGE EmptyDataDecls      #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.OpenPGP.CryptoAPI.AES (AES128,AES192,AES256) where

import Crypto.Cipher.AES
import Crypto.Classes
import Crypto.Types (BitLength)
import Data.Serialize
import Data.Tagged (Tagged(..))

data Mode = ECB | CBC IV | CTR IV

encryptBlk key ECB      = encryptECB key
encryptBlk key (CBC iv) = encryptCBC key iv
encryptBlk key (CTR iv) = encryptCTR key iv

decryptBlk key ECB      = decryptECB key
decryptBlk key (CBC iv) = decryptCBC key iv
decryptBlk key (CTR iv) = decryptCTR key iv

data M128
data M192
data M256
type AES128 = AES M128
type AES192 = AES M192
type AES256 = AES M256

newtype AES mode = AES Key

class AESMode mode where
    aesMode :: mode -> Mode
    aesMode       _  = ECB
    aesBlockSize :: mode -> Tagged k BitLength
    aesBlockSize       _  = Tagged 128
    aesKeyLength :: mode -> BitLength

instance AESMode M128 where aesKeyLength _ = 128
instance AESMode M192 where aesKeyLength _ = 192
instance AESMode M256 where aesKeyLength _ = 256

instance AESMode mode => Serialize (AES mode) where
    put (AES k) = putByteString . keyOfCtx $ k
    get = do
        bs <- getBytes (aesKeyLength (undefined::mode) `div` 8) 
        return . AES . initKey $ bs
            
instance AESMode mode => BlockCipher (AES mode) where
    blockSize = aesBlockSize (undefined :: mode)
    encryptBlock (AES key) = encryptBlk key (aesMode (undefined::mode))
    decryptBlock (AES key) = decryptBlk key (aesMode (undefined::mode))
    buildKey = Just . AES . initKey
    keyLength = Tagged $ aesKeyLength (undefined :: mode)

