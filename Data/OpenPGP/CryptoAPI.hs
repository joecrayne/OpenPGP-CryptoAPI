module Data.OpenPGP.CryptoAPI (fingerprint, sign, verify, encrypt, decryptAsymmetric, decryptSymmetric, decryptSecretKey) where

import Data.Char
import Data.Bits
import Data.List (find)
import Data.Maybe (mapMaybe, catMaybes, listToMaybe)
import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (StateT(..), runStateT)
import Data.Binary (encode, decode, get, Word16)
import Crypto.Classes hiding (hash,sign,verify,encode,cfb,unCfb)
import Data.Tagged (untag, asTaggedTypeOf, Tagged(..))
import Crypto.Modes (cfb, unCfb, zeroIV)
import Crypto.Types (IV)
import Crypto.Random (GenError(GenErrorOther))
import Crypto.Hash.CryptoAPI (MD5,SHA1,RIPEMD160,SHA256,SHA384,SHA512,SHA224)
import Crypto.Random.API (CPRG,cprgGenBytes)
import Data.OpenPGP.CryptoAPI.AES (AES128,AES192,AES256)
import qualified Data.Serialize as Serialize
import qualified Crypto.PubKey.RSA as RSA
import qualified Crypto.PubKey.RSA.PKCS15 as RSA
import Crypto.PubKey.HashDescr
import qualified Crypto.PubKey.DSA as DSA
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LZ

import qualified Data.OpenPGP as OpenPGP
import Data.OpenPGP.CryptoAPI.Util
import Data.OpenPGP.CryptoAPI.Blowfish128

-- | An encryption routine
type Encrypt g = (LZ.ByteString -> g -> (LZ.ByteString, g))

-- | A decryption routine, Bool=True to do resynchronization
type Decrypt = (Bool -> LZ.ByteString -> (LZ.ByteString, LZ.ByteString))

-- Start differently-formatted section
-- | This should be in Crypto.Classes and is based on buildKeyIO
buildKeyGen :: (BlockCipher k, CPRG g) => g -> Either GenError (k, g)
buildKeyGen = runStateT (go (0::Int))
  where
  go 1000 = lift $ Left $ GenErrorOther
                  "Tried 1000 times to generate a key from the system entropy.\
                  \  No keys were returned! Perhaps the system entropy is broken\
                  \ or perhaps the BlockCipher instance being used has a non-flat\
                  \ keyspace."
  go i = do
	let bs = keyLength
	kd <- StateT $ \g -> return $ cprgGenBytes ((7 + untag bs) `div` 8) g
	case buildKey kd of
		Nothing -> go (i+1)
		Just k  -> return $ k `asTaggedTypeOf` bs
-- End differently-formatted section

find_key :: OpenPGP.Message -> String -> Maybe OpenPGP.Packet
find_key = OpenPGP.find_key fingerprint

hash :: OpenPGP.HashAlgorithm -> LZ.ByteString -> (BS.ByteString, String)
hash OpenPGP.MD5 = hash_ (undefined :: MD5)
hash OpenPGP.SHA1 = hash_ (undefined :: SHA1)
hash OpenPGP.RIPEMD160 = hash_ (undefined :: RIPEMD160)
hash OpenPGP.SHA256 = hash_ (undefined :: SHA256)
hash OpenPGP.SHA384 = hash_ (undefined :: SHA384)
hash OpenPGP.SHA512 = hash_ (undefined :: SHA512)
hash OpenPGP.SHA224 = hash_ (undefined :: SHA224)
hash _ = error "Unsupported HashAlgorithm in hash"

hash_ :: (Hash c d) => d -> LZ.ByteString -> (BS.ByteString, String)
hash_ d bs = (hbs, map toUpper $ pad $ hexString $ BS.unpack hbs)
	where
	hbs = Serialize.encode $ hashFunc d bs
	pad s = replicate (len - length s) '0' ++ s
	len = (outputLength `for` d) `div` 8


blockBytes :: (BlockCipher k, Num n) => k -> n
blockBytes k = fromIntegral $ blockSizeBytes `for` k

pgpCFBPrefix :: (BlockCipher k, CPRG g) => k -> g -> (LZ.ByteString, g)
pgpCFBPrefix k g =
	(toLazyBS $ str `BS.append` BS.reverse (BS.take 2 $ BS.reverse str), g')
	where
	(str,g') = cprgGenBytes (blockSizeBytes `for` k) g

pgpCFB :: (BlockCipher k, CPRG g) => k -> (LZ.ByteString -> LZ.ByteString -> LZ.ByteString) -> Encrypt g
pgpCFB k sufGen bs g =
	(simpleCFB k zeroIV (LZ.concat [p, bs, sufGen p bs]), g')
	where
	(p,g') = pgpCFBPrefix k g

simpleCFB :: (BlockCipher k) => k -> IV k -> LZ.ByteString -> LZ.ByteString
simpleCFB k iv = padThenUnpad k (fst . cfb k iv)

pgpUnCFB :: (BlockCipher k) => k -> Decrypt
pgpUnCFB k False s = LZ.splitAt (2 + blockBytes k) $ simpleUnCFB k zeroIV s
pgpUnCFB k True s = (simpleUnCFB k zeroIV prefix, simpleUnCFB k iv content)
	where
	Just iv = sDecode $ toStrictBS $ LZ.drop 2 prefix
	(prefix, content) = LZ.splitAt (2 + blockBytes k) s

simpleUnCFB :: (BlockCipher k) => k -> IV k -> LZ.ByteString -> LZ.ByteString
simpleUnCFB k iv = padThenUnpad k (fst . unCfb k iv)

padThenUnpad :: (BlockCipher k) => k -> (LZ.ByteString -> LZ.ByteString) -> LZ.ByteString -> LZ.ByteString
padThenUnpad k f s = dropPadEnd (f padded)
	where
	dropPadEnd s = LZ.take (LZ.length s - padAmount) s
	padded = s `LZ.append` LZ.replicate padAmount 0
	padAmount = blockBytes k - (LZ.length s `mod` blockBytes k)

addBitLen :: LZ.ByteString -> LZ.ByteString
addBitLen bytes = encode (bitLen bytes :: Word16) `LZ.append` bytes
	where
	bitLen bytes = (fromIntegral (LZ.length bytes) - 1) * 8 + sigBit bytes
	sigBit bytes = fst $ until ((==0) . snd)
		(first (+1) . second (`shiftR` 1)) (0,LZ.index bytes 0)

-- Drops 2 because the value is an MPI
rsaDecrypt :: RSA.PrivateKey -> BS.ByteString -> Maybe BS.ByteString
rsaDecrypt pk = hush . RSA.decrypt Nothing pk . BS.drop 2

rsaEncrypt :: (CPRG g) => RSA.PublicKey -> BS.ByteString -> StateT g (Either GenError) BS.ByteString
rsaEncrypt pk bs = StateT (\g ->
		case RSA.encrypt g pk bs of
			-- (Left (RSA.RandomGenFailure e)) -> Left e
			(Left e,_) -> Left (GenErrorOther $ show e)
			(Right v,g) -> Right (v,g)
	)

integerBytesize :: Integer -> Int
integerBytesize i = fromIntegral $ LZ.length (encode (OpenPGP.MPI i)) - 2

keyParam :: Char -> OpenPGP.Packet -> Integer
keyParam c k = fromJustMPI $ lookup c (OpenPGP.key k)

keyAlgorithmIs :: OpenPGP.KeyAlgorithm -> OpenPGP.Packet -> Bool
keyAlgorithmIs algo p = OpenPGP.key_algorithm p == algo

secretKeys :: OpenPGP.Message -> ([(String, RSA.PrivateKey)], [(String, DSA.PrivateKey)])
secretKeys (OpenPGP.Message keys) =
	(
		map (fingerprint &&& privateRSAkey) rsa,
		map (fingerprint &&& privateDSAkey) dsa
	)
	where
	dsa = secrets OpenPGP.DSA
	rsa = secrets OpenPGP.RSA
	secrets algo = filter (swing all [isSecretKey, keyAlgorithmIs algo]) keys

privateRSAkey :: OpenPGP.Packet -> RSA.PrivateKey
privateRSAkey k =
	-- Invert p and q because u is pinv not qinv
	RSA.PrivateKey pubkey d q p
		(d `mod` (q-1))
		(d `mod` (p-1))
		(keyParam 'u' k)
	where
	d = keyParam 'd' k
	p = keyParam 'p' k
	q = keyParam 'q' k
	pubkey = rsaKey k

rsaKey :: OpenPGP.Packet -> RSA.PublicKey
rsaKey k =
	RSA.PublicKey (integerBytesize n) n (keyParam 'e' k)
	where
	n = keyParam 'n' k

privateDSAkey :: OpenPGP.Packet -> DSA.PrivateKey
privateDSAkey k = DSA.PrivateKey
	(DSA.Params (keyParam 'p' k) (keyParam 'g' k) (keyParam 'q' k))
    (keyParam 'x' k)

dsaKey :: OpenPGP.Packet -> DSA.PublicKey
dsaKey k = DSA.PublicKey
	(DSA.Params (keyParam 'p' k) (keyParam 'g' k) (keyParam 'q' k))
    (keyParam 'y' k)

-- | Generate a key fingerprint from a PublicKeyPacket or SecretKeyPacket
-- <http://tools.ietf.org/html/rfc4880#section-12.2>
fingerprint :: OpenPGP.Packet -> String
fingerprint p
	| OpenPGP.version p == 4 = snd $ hash OpenPGP.SHA1 material
	| OpenPGP.version p `elem` [2, 3] = snd $ hash OpenPGP.MD5 material
	| otherwise = error "Unsupported Packet version or type in fingerprint"
	where
	material = LZ.concat $ OpenPGP.fingerprint_material p

-- | Verify a message signature
verify ::
	OpenPGP.Message          -- ^ Keys that may have made the signature
	-> OpenPGP.SignatureOver -- ^ Signatures to verify
	-> OpenPGP.SignatureOver -- ^ Will only contain signatures that passed
verify keys over =
	over {OpenPGP.signatures_over = mapMaybe (uncurry $ verifyOne keys) sigs}
	where
	sigs = map (\s -> (s, toStrictBS $ encode over `LZ.append` OpenPGP.trailer s))
		(OpenPGP.signatures_over over)

verifyOne :: OpenPGP.Message -> OpenPGP.Packet -> BS.ByteString -> Maybe OpenPGP.Packet
verifyOne keys sig over = fmap (const sig) $ maybeKey >>=
	case OpenPGP.key_algorithm sig of
		OpenPGP.DSA -> dsaVerify
		alg | alg `elem` [OpenPGP.RSA,OpenPGP.RSA_S] -> rsaVerify
		    | otherwise -> const Nothing
	where
	dsaVerify k = let k' = dsaKey k in
		Just $ DSA.verify (dsaTruncate k' . bhash) k' dsaSig over
	rsaVerify k = Just $ RSA.verify desc (rsaKey k) over rsaSig
	[rsaSig] = map (toStrictBS . LZ.drop 2 . encode) (OpenPGP.signature sig)
	dsaSig = let [OpenPGP.MPI r, OpenPGP.MPI s] = OpenPGP.signature sig in
		DSA.Signature r s
	dsaTruncate (DSA.PublicKey (DSA.Params _ _ q) _) = BS.take (integerBytesize q)
	bhash = fst . hash hash_algo . toLazyBS
	-- padding = emsa_pkcs1_v1_5_hash_padding hash_algo
	desc = hashAlgoDesc hash_algo
	hash_algo = OpenPGP.hash_algorithm sig
	maybeKey = OpenPGP.signature_issuer sig >>= find_key keys

hashAlgoDesc OpenPGP.MD5       = hashDescrMD5
hashAlgoDesc OpenPGP.SHA1      = hashDescrSHA1
hashAlgoDesc OpenPGP.RIPEMD160 = hashDescrRIPEMD160
hashAlgoDesc OpenPGP.SHA256    = hashDescrSHA256
hashAlgoDesc OpenPGP.SHA384    = hashDescrSHA384
hashAlgoDesc OpenPGP.SHA512    = hashDescrSHA512
hashAlgoDesc OpenPGP.SHA224    = hashDescrSHA224
hashAlgoDesc _ =
	error "Unsupported HashAlgorithm in hashAlgoDesc"

-- | Make a signature
--
-- In order to set more options on a signature, pass in a signature packet.
sign :: (CPRG g) => -- CryptoRandomGen g) =>
	OpenPGP.Message          -- ^ SecretKeys, one of which will be used
	-> OpenPGP.SignatureOver -- ^ Data to sign, and optional signature packet
	-> OpenPGP.HashAlgorithm -- ^ HashAlgorithm to use in signature
	-> String                -- ^ KeyID of key to choose
	-> Integer               -- ^ Timestamp for signature (unless sig supplied)
	-> g                     -- ^ Random number generator
	-> (OpenPGP.SignatureOver, g)
sign keys over hsh keyid timestamp g = (over {OpenPGP.signatures_over = [sig]}, g')
	where
	(final, g') = case OpenPGP.key_algorithm sig of
		OpenPGP.DSA -> ([dsaR, dsaS], dsaG)
		kalgo | kalgo `elem` [OpenPGP.RSA,OpenPGP.RSA_S] -> ([toNum rsaFinal], g)
		      | otherwise ->
			error ("Unsupported key algorithm " ++ show kalgo ++ "in sign")
	(DSA.Signature dsaR dsaS,dsaG) = let k' = privateDSAkey k in
		DSA.sign g k' (dsaTruncate k' . bhash) dta
	(Right rsaFinal,_) = RSA.signSafer g desc (privateRSAkey k) dta
	dsaTruncate (DSA.PrivateKey (DSA.Params _ _ q) _) = BS.take (integerBytesize q)
	dta     = toStrictBS $ encode over `LZ.append` OpenPGP.trailer sig
	sig     = findSigOrDefault (listToMaybe $ OpenPGP.signatures_over over)
	-- padding = emsa_pkcs1_v1_5_hash_padding hsh
	desc = hashAlgoDesc hsh
	bhash   = fst . hash hsh . toLazyBS
	toNum   = BS.foldl (\a b -> a `shiftL` 8 .|. fromIntegral b) 0
	Just k  = find_key keys keyid

	-- Either a SignaturePacket was found, or we need to make one
	findSigOrDefault (Just s) = OpenPGP.signaturePacket
		(OpenPGP.version s)
		(OpenPGP.signature_type s)
		(OpenPGP.key_algorithm k) -- force to algo of key
		hsh -- force hash algorithm
		(OpenPGP.hashed_subpackets s)
		(OpenPGP.unhashed_subpackets s)
		(OpenPGP.hash_head s)
		(map OpenPGP.MPI final)
	findSigOrDefault Nothing  = OpenPGP.signaturePacket
		4
		defaultStype
		(OpenPGP.key_algorithm k) -- force to algo of key
		hsh
		([
			-- Do we really need to pass in timestamp just for the default?
			OpenPGP.SignatureCreationTimePacket $ fromIntegral timestamp,
			OpenPGP.IssuerPacket $ fingerprint k
		] ++ (case over of
			OpenPGP.KeySignature  {} -> [OpenPGP.KeyFlagsPacket {
					OpenPGP.certify_keys = True,
					OpenPGP.sign_data = True,
					OpenPGP.encrypt_communication = False,
					OpenPGP.encrypt_storage = False,
					OpenPGP.split_key = False,
					OpenPGP.authentication = False,
					OpenPGP.group_key = False
				}]
			_ -> []
		))
		[]
		0 -- TODO
		(map OpenPGP.MPI final)

	defaultStype = case over of
		OpenPGP.DataSignature ld _
			| OpenPGP.format ld == 'b'     -> 0x00
			| otherwise                    -> 0x01
		OpenPGP.KeySignature {}           -> 0x1F
		OpenPGP.SubkeySignature {}        -> 0x18
		OpenPGP.CertificationSignature {} -> 0x13

encrypt :: (CPRG g) =>
	[BS.ByteString]               -- ^ Passphrases, all of which will be used
	-> OpenPGP.Message            -- ^ PublicKeys, all of which will be used
	-> OpenPGP.SymmetricAlgorithm -- ^ Cipher to use
	-> OpenPGP.Message            -- ^ The 'OpenPGP.Message' to encrypt
	-> g                          -- ^ Random number generator
	-> Either GenError (OpenPGP.Message, g)
encrypt pass (OpenPGP.Message keys) algo msg = runStateT $ do
	(sk, encP) <- sessionFor algo msg
	OpenPGP.Message . (++[encP]) <$> liftA2 (++)
		(mapM (encryptSessionKeyAsymmetric sk) (filter isKey keys))
		(mapM (encryptSessionKeySymmetric (LZ.take (LZ.length sk - 2) sk) algo) pass)

encryptSessionKeyAsymmetric :: (CPRG g) => LZ.ByteString -> OpenPGP.Packet -> StateT g (Either GenError) OpenPGP.Packet
encryptSessionKeyAsymmetric sk pk = OpenPGP.AsymmetricSessionKeyPacket 3
	(fingerprint pk)
	(OpenPGP.key_algorithm pk)
	. addBitLen <$> encd (OpenPGP.key_algorithm pk)
	where
	encd OpenPGP.RSA = toLazyBS <$> rsaEncrypt (rsaKey pk) (toStrictBS sk)
	encd _ = lift $ Left $ GenErrorOther $ "Unsupported PublicKey: " ++ show pk

encryptSessionKeySymmetric :: (CPRG g) => LZ.ByteString -> OpenPGP.SymmetricAlgorithm -> BS.ByteString -> StateT g (Either GenError) OpenPGP.Packet
encryptSessionKeySymmetric sk salgo pass = do
	s2k <- s2k
	return $ OpenPGP.SymmetricSessionKeyPacket 4 salgo s2k
		(string2sencrypt salgo s2k (toLazyBS pass) sk)
	where
	halgo = s2kHashAlgorithmFor salgo
	s2k = OpenPGP.IteratedSaltedS2K halgo . decode . toLazyBS <$>
		(StateT $ \g -> Right $ cprgGenBytes 8 g) <*> pure 65536

s2kHashAlgorithmFor :: OpenPGP.SymmetricAlgorithm -> OpenPGP.HashAlgorithm
s2kHashAlgorithmFor OpenPGP.AES128 = s2kHashAlgorithm `for` (undefined :: AES128)
s2kHashAlgorithmFor OpenPGP.AES192 = s2kHashAlgorithm `for` (undefined :: AES192)
s2kHashAlgorithmFor OpenPGP.AES256 = s2kHashAlgorithm `for` (undefined :: AES256)
s2kHashAlgorithmFor OpenPGP.Blowfish = s2kHashAlgorithm `for` (undefined :: Blowfish128)
s2kHashAlgorithmFor algo = error $ "Unsupported SymmetricAlgorithm " ++ show algo ++ " in Data.OpenPGP.CryptoAPI.s2kHashAlgorithmFor"

s2kHashAlgorithm :: (BlockCipher k) => Tagged k OpenPGP.HashAlgorithm
s2kHashAlgorithm = v
	where
	v = Tagged $ case () of
		_ | ksize <= 160 -> OpenPGP.SHA1
		  | ksize <= 256 -> OpenPGP.SHA256
		  | otherwise    -> OpenPGP.SHA512
	ksize = keyLength `tagOfTag` v

tagOfTag :: Tagged a c -> Tagged a b -> c
tagOfTag a b = a `for` (undefined `asTaggedTypeOf` b)

sessionFor :: (CPRG g) => OpenPGP.SymmetricAlgorithm -> OpenPGP.Message -> StateT g (Either GenError) (LZ.ByteString, OpenPGP.Packet)
sessionFor algo@OpenPGP.AES128 msg = do
	sk <- StateT buildKeyGen
	encP <- newSession (sk :: AES128) msg
	return (sessionKeyEncode sk algo, encP)
sessionFor algo@OpenPGP.AES192 msg = do
	sk <- StateT buildKeyGen
	encP <- newSession (sk :: AES192) msg
	return (sessionKeyEncode sk algo, encP)
sessionFor algo@OpenPGP.AES256 msg = do
	sk <- StateT buildKeyGen
	encP <- newSession (sk :: AES256) msg
	return (sessionKeyEncode sk algo, encP)
sessionFor algo@OpenPGP.Blowfish msg = do
	sk <- StateT buildKeyGen
	encP <- newSession (sk :: Blowfish128) msg
	return (sessionKeyEncode sk algo, encP)
sessionFor algo _ = lift $ Left $ GenErrorOther $ "Unsupported cipher: " ++ show algo

sessionKeyEncode :: (BlockCipher k) => k -> OpenPGP.SymmetricAlgorithm -> LZ.ByteString
sessionKeyEncode sk algo =
	LZ.concat [encode algo, toLazyBS bs, encode $ checksum bs]
	where
	bs = Serialize.encode sk

newSession :: (BlockCipher k, CPRG g, Monad m) => k -> OpenPGP.Message -> StateT g m OpenPGP.Packet
newSession sk msg = do
	encd <- StateT $ return . pgpCFB sk (encode `oo` mkMDC) (encode msg)
	return $ OpenPGP.EncryptedDataPacket 1 encd

mkMDC :: LZ.ByteString -> LZ.ByteString -> OpenPGP.Packet
mkMDC prefix msg = OpenPGP.ModificationDetectionCodePacket $ toLazyBS $ fst $
	hash OpenPGP.SHA1 $ LZ.concat [prefix, msg, LZ.pack [0xD3, 0x14]]

checksum :: BS.ByteString -> Word16
checksum key = fromIntegral $
	BS.foldl' (\x y -> x + fromIntegral y) (0::Integer) key `mod` 65536

decryptSecretKey ::
	BS.ByteString           -- ^ Passphrase
	-> OpenPGP.Packet       -- ^ Encrypted SecretKeyPacket
	-> Maybe OpenPGP.Packet -- ^ Decrypted SecretKeyPacket
decryptSecretKey pass k@(OpenPGP.SecretKeyPacket {
		OpenPGP.version = 4, OpenPGP.key_algorithm = kalgo,
		OpenPGP.s2k = s2k, OpenPGP.symmetric_algorithm = salgo,
		OpenPGP.key = existing, OpenPGP.encrypted_data = encd
	}) | chkF material == toStrictBS chk =
		fmap (\m -> k {
			OpenPGP.s2k_useage = 0,
			OpenPGP.symmetric_algorithm = OpenPGP.Unencrypted,
			OpenPGP.encrypted_data = LZ.empty,
			OpenPGP.key = m
		}) parseMaterial
	   | otherwise = Nothing
	where
	parseMaterial = maybeGet
		(foldM (\m f -> do {mpi <- get; return $ (f,mpi):m}) existing
		(OpenPGP.secret_key_fields kalgo)) material
	(material, chk) = LZ.splitAt (LZ.length decd - chkSize) decd
	(chkSize, chkF)
		| OpenPGP.s2k_useage k == 254 = (20, fst . hash OpenPGP.SHA1)
		| otherwise = (2, Serialize.encode . checksum . toStrictBS)
	decd = string2sdecrypt salgo s2k (toLazyBS pass) (EncipheredWithIV encd)
decryptSecretKey _ _ = Nothing

-- | Decrypt an OpenPGP message using secret key
decryptAsymmetric ::
	OpenPGP.Message    -- ^ SecretKeys, one of which will be used
	-> OpenPGP.Message -- ^ A 'OpenPGP.Message' containing AsymmetricSessionKey and EncryptedData
	-> Maybe OpenPGP.Message
decryptAsymmetric keys msg@(OpenPGP.Message pkts) = do
	(_, d) <- getAsymmetricSessionKey keys msg
	pkt <- find isEncryptedData pkts
	decryptPacket d pkt

-- | Decrypt an OpenPGP message using passphrase
decryptSymmetric ::
	[BS.ByteString]    -- ^ Passphrases, one of which will be used
	-> OpenPGP.Message -- ^ A 'OpenPGP.Message' containing SymetricSessionKey and EncryptedData
	-> Maybe OpenPGP.Message
decryptSymmetric pass msg@(OpenPGP.Message pkts) = do
	let ds = map snd $ getSymmetricSessionKey pass msg
	pkt <- find isEncryptedData pkts
	listToMaybe $ mapMaybe (`decryptPacket` pkt) ds

-- | Decrypt a single packet, given the decryptor
decryptPacket :: Decrypt -> OpenPGP.Packet -> Maybe OpenPGP.Message
decryptPacket d (OpenPGP.EncryptedDataPacket {
		OpenPGP.version = 1,
		OpenPGP.encrypted_data = encd
	}) | Just (mkMDC prefix msg) == maybeDecode mdc = maybeDecode msg
	   | otherwise = Nothing
	where
	(msg,mdc) = LZ.splitAt (LZ.length content - 22) content
	(prefix, content) = d False encd
decryptPacket d (OpenPGP.EncryptedDataPacket {
		OpenPGP.version = 0,
		OpenPGP.encrypted_data = encd
	}) = maybeDecode (snd $ d True encd)
decryptPacket _ _ = error "Can only decrypt EncryptedDataPacket in Data.OpenPGP.CryptoAPI.decryptPacket"

getSymmetricSessionKey ::
	[BS.ByteString]    -- ^ Passphrases, one of which will be used
	-> OpenPGP.Message -- ^ An OpenPGP Message containing SymmetricSessionKey
	-> [(OpenPGP.SymmetricAlgorithm, Decrypt)]
getSymmetricSessionKey pass (OpenPGP.Message ps) =
	concatMap (\OpenPGP.SymmetricSessionKeyPacket {
			OpenPGP.s2k = s2k, OpenPGP.symmetric_algorithm = algo,
			OpenPGP.encrypted_data = encd
		} ->
		if LZ.null encd then
			map ((,) algo . string2decrypt algo s2k) pass'
		else
			mapMaybe (\p -> decodeSess $ string2sdecrypt algo s2k p (EncipheredZeroIV encd)) pass'
	) sessionKeys
	where
	decodeSess s = let (a, k) = LZ.splitAt 1 s in
		(,) (decode a) <$> decodeSymKey (decode a) (toStrictBS k)
	sessionKeys = filter isSymmetricSessionKey ps
	pass' = map toLazyBS pass

-- | Decrypt an asymmetrically encrypted symmetric session key
getAsymmetricSessionKey ::
	OpenPGP.Message    -- ^ SecretKeys, one of which will be used
	-> OpenPGP.Message -- ^ An OpenPGP Message containing AssymetricSessionKey
	-> Maybe (OpenPGP.SymmetricAlgorithm, Decrypt)
getAsymmetricSessionKey keys (OpenPGP.Message ps) =
	listToMaybe $ mapMaybe decodeSessionKey $ catMaybes $
	concatMap (\(sk,ks) ->
		map ($ toStrictBS $ OpenPGP.encrypted_data sk) ks
	) toTry
	where
	toTry = map (id &&& lookupKey) sessionKeys

	lookupKey (OpenPGP.AsymmetricSessionKeyPacket {
		OpenPGP.key_algorithm = OpenPGP.RSA,
		OpenPGP.key_id = key_id
	}) | all (=='0') key_id = map (rsaDecrypt . snd) rsa
	   | otherwise = map (rsaDecrypt . snd) $
		filter (keyIdMatch key_id . fst) rsa
	lookupKey _ = []

	sessionKeys = filter isAsymmetricSessionKey ps
	(rsa, _) = secretKeys keys

decodeSessionKey :: BS.ByteString -> Maybe (OpenPGP.SymmetricAlgorithm, Decrypt)
decodeSessionKey sk
	| checksum key == (decode (toLazyBS chk) :: Word16) = do
		algo <- maybeDecode (toLazyBS algoByte)
		decrypt <- decodeSymKey algo key
		return (algo, decrypt)
	| otherwise = Nothing
	where
	(key, chk) = BS.splitAt (BS.length rest - 2) rest
	(algoByte, rest) = BS.splitAt 1 sk

decodeSymKey :: OpenPGP.SymmetricAlgorithm -> BS.ByteString -> Maybe Decrypt
decodeSymKey OpenPGP.AES128 k = pgpUnCFB <$> (`asTypeOf` (undefined :: AES128)) <$> sDecode k
decodeSymKey OpenPGP.AES192 k = pgpUnCFB <$> (`asTypeOf` (undefined :: AES192)) <$> sDecode k
decodeSymKey OpenPGP.AES256 k = pgpUnCFB <$> (`asTypeOf` (undefined :: AES256)) <$> sDecode k
decodeSymKey OpenPGP.Blowfish k = pgpUnCFB <$> (`asTypeOf` (undefined :: Blowfish128)) <$> sDecode k
decodeSymKey _ _ = Nothing

string2sencrypt :: OpenPGP.SymmetricAlgorithm -> OpenPGP.S2K -> LZ.ByteString -> LZ.ByteString -> LZ.ByteString
string2sencrypt OpenPGP.AES128 s2k s = simpleCFB (string2key s2k s :: AES128) zeroIV
string2sencrypt OpenPGP.AES192 s2k s = simpleCFB (string2key s2k s :: AES192) zeroIV
string2sencrypt OpenPGP.AES256 s2k s = simpleCFB (string2key s2k s :: AES256) zeroIV
string2sencrypt OpenPGP.Blowfish s2k s = simpleCFB (string2key s2k s :: Blowfish128) zeroIV
string2sencrypt algo _ _ = error $ "Unsupported symmetric algorithm : " ++ show algo ++ " in Data.OpenPGP.CryptoAPI.string2sencrypt"

string2decrypt :: OpenPGP.SymmetricAlgorithm -> OpenPGP.S2K -> LZ.ByteString -> Decrypt
string2decrypt OpenPGP.AES128 s2k s = pgpUnCFB (string2key s2k s :: AES128)
string2decrypt OpenPGP.AES192 s2k s = pgpUnCFB (string2key s2k s :: AES192)
string2decrypt OpenPGP.AES256 s2k s = pgpUnCFB (string2key s2k s :: AES256)
string2decrypt OpenPGP.Blowfish s2k s = pgpUnCFB (string2key s2k s :: Blowfish128)
string2decrypt algo _ _ = error $ "Unsupported symmetric algorithm : " ++ show algo ++ " in Data.OpenPGP.CryptoAPI.string2decrypt"

string2sdecrypt :: OpenPGP.SymmetricAlgorithm -> OpenPGP.S2K -> LZ.ByteString -> Enciphered -> LZ.ByteString
string2sdecrypt OpenPGP.AES128 s2k s = withIV $ simpleUnCFB (string2key s2k s :: AES128)
string2sdecrypt OpenPGP.AES192 s2k s = withIV $ simpleUnCFB (string2key s2k s :: AES192)
string2sdecrypt OpenPGP.AES256 s2k s = withIV $ simpleUnCFB (string2key s2k s :: AES256)
string2sdecrypt OpenPGP.Blowfish s2k s = withIV $ simpleUnCFB (string2key s2k s :: Blowfish128)
string2sdecrypt algo _ _ = error $ "Unsupported symmetric algorithm : " ++ show algo ++ " in Data.OpenPGP.CryptoAPI.string2sdecrypt"

data Enciphered = EncipheredWithIV !LZ.ByteString | EncipheredZeroIV !LZ.ByteString

withIV :: (BlockCipher k) => (IV k -> LZ.ByteString -> LZ.ByteString) -> Enciphered -> LZ.ByteString
withIV f (EncipheredWithIV s) = f iv $ LZ.drop (fromIntegral $ BS.length $ Serialize.encode iv) s
	where
	iv = let Right x = Serialize.decode (toStrictBS s) in x
withIV f (EncipheredZeroIV s) = f zeroIV s

string2key :: (BlockCipher k) => OpenPGP.S2K -> LZ.ByteString -> k
string2key s2k s = k
	where
	Just k = buildKey $ toStrictBS $
		LZ.take ksize $ OpenPGP.string2key (fst `oo` hash) s2k s
	ksize = fromIntegral (keyLength `for` k) `div` 8
