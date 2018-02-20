{-# LANGUAGE StrictData #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Crypto.Hash.MerkleTree (
  MerkleTree(..),
  MerkleHash(..),
  MerkleNode(..),

  -- ** Constructors
  mkMerkleTree,
  mkRootHash,
  mkLeafRootHash,
  emptyHash,

  -- ** Merkle Proof
  MerkleProof(..),
  merkleProof,
  validateMerkleProof,

  -- ** Size
  mtRootHash,
  mtSize,
  mtHashString,
  mtHeight,

  -- ** Testing
  testMerkleProofN,
) where

import Protolude hiding (hash)

import Crypto.Hash (Digest, SHA3_256(..), hash)

import qualified Data.List as List
import qualified Data.Serialize as S
import qualified Data.ByteArray as B
import qualified Data.ByteArray.Encoding as B
import qualified Data.ByteString as BS

import System.Random (randomRIO)

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

-- | A merkle tree root.
newtype MerkleHash a = MerkleHash
  { getMerkleHash :: ByteString
  } deriving (Show, Eq, Ord,  Generic, S.Serialize)

instance B.ByteArrayAccess (MerkleHash a) where
  length (MerkleHash bs) = B.length bs
  withByteArray (MerkleHash bs) f = B.withByteArray bs f

-- | A merkle tree.
data MerkleTree a
  = MerkleEmpty
  | MerkleTree Word32 (MerkleNode a)
  deriving (Show, Eq, Generic, S.Serialize)

data MerkleNode a
  = MerkleBranch {
      mRootHash  :: MerkleHash a
    , mLeft  :: MerkleNode a
    , mRight :: MerkleNode a
  }
  | MerkleLeaf {
      mRootHash :: MerkleHash a
    , mVal  :: a
  }
  deriving (Eq, Show, Generic, S.Serialize)

instance Foldable MerkleTree where
  foldMap _ MerkleEmpty      = mempty
  foldMap f (MerkleTree _ n) = foldMap f n

  null MerkleEmpty = True
  null _           = False

  length MerkleEmpty      = 0
  length (MerkleTree s _) = fromIntegral s

instance Foldable MerkleNode where
  foldMap f x = case x of
    MerkleLeaf{mVal}            -> f mVal
    MerkleBranch{mLeft, mRight} ->
      foldMap f mLeft `mappend` foldMap f mRight

-- | Returns root of merkle tree.
mtRootHash :: MerkleTree a -> MerkleHash a
mtRootHash MerkleEmpty      = emptyHash
mtRootHash (MerkleTree _ x) = mRootHash x

-- | Returns root of merkle tree root hashed.
mtHashString :: MerkleTree a -> ByteString
mtHashString = B.convert . mtRootHash

mtSize :: MerkleTree a -> Word32
mtSize MerkleEmpty      = 0
mtSize (MerkleTree s _) = s

emptyHash :: MerkleHash a
emptyHash = MerkleHash (merkleHash mempty)

-- | Merkle tree height
mtHeight :: Int -> Int
mtHeight ntx
  | ntx < 2 = 0
  | even ntx  = 1 + mtHeight (ntx `div` 2)
  | otherwise = mtHeight $ ntx + 1

-- | Merkle tree width
mtWidth
  :: Int -- ^ Number of transactions (leaf nodes).
  -> Int -- ^ Height at which we want to compute the width.
  -> Int -- ^ Width of the merkle tree.
mtWidth ntx h = (ntx + (1 `shiftL` h) - 1) `shiftR` h

-- | Return the largest power of two such that it's smaller than n.
powerOfTwo :: (Bits a, Num a) => a -> a
powerOfTwo n
   | n .&. (n - 1) == 0 = n `shiftR` 1
   | otherwise = go n
 where
    go w = if w .&. (w - 1) == 0 then w else go (w .&. (w - 1))

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

mkLeaf :: ByteString -> MerkleNode ByteString
mkLeaf a =
  MerkleLeaf
  { mVal  = a
  , mRootHash = mkLeafRootHash a
  }

mkLeafRootHash :: B.ByteArrayAccess a => a -> MerkleHash a
mkLeafRootHash a = MerkleHash $ merkleHash (BS.singleton 0 <> B.convert a)

mkBranch :: MerkleNode a -> MerkleNode a -> MerkleNode a
mkBranch a b =
  MerkleBranch
  { mLeft  = a
  , mRight = b
  , mRootHash  = mkRootHash (mRootHash a) (mRootHash b)
  }

mkRootHash :: MerkleHash a -> MerkleHash a -> MerkleHash a
mkRootHash (MerkleHash l) (MerkleHash r) = MerkleHash $ merkleHash $ mconcat
  [ BS.singleton 1, B.convert l, B.convert r ]

-- | Smart constructor for 'MerkleTree'.
mkMerkleTree :: [ByteString] -> MerkleTree ByteString
mkMerkleTree [] = MerkleEmpty
mkMerkleTree ls = MerkleTree (fromIntegral lsLen) (go lsLen ls)
  where
    lsLen = length ls
    go _  [x] = mkLeaf x
    go len xs = mkBranch (go i l) (go (len - i) r)
      where
        i = powerOfTwo len
        (l, r) = splitAt i xs

-------------------------------------------------------------------------------
-- Merkle Proofs
-------------------------------------------------------------------------------

newtype MerkleProof a = MerkleProof { getMerkleProof :: [ProofElem a] }
  deriving (Show, Eq, Ord, Generic, S.Serialize)

data ProofElem a = ProofElem
  { nodeRoot    :: MerkleHash a
  , siblingRoot :: MerkleHash a
  , nodeSide    :: Side
  } deriving (Show, Eq, Ord, Generic, S.Serialize)

data Side = L | R
  deriving (Show, Eq, Ord, Generic, S.Serialize)

-- | Construct a merkle tree proof of inclusion
-- Walks the entire tree recursively, building a list of "proof elements"
-- that are comprised of the current node's root and it's sibling's root,
-- and whether it is the left or right sibling (this is necessary to determine
-- the order in which to hash each proof element root and it's sibling root).
-- The list is ordered such that the for each element, the next element in
-- the list is the proof element corresponding to the node's parent node.
merkleProof :: forall a. MerkleTree a -> MerkleHash a -> MerkleProof a
merkleProof MerkleEmpty _ = MerkleProof []
merkleProof (MerkleTree _ rootNode) leafRoot = MerkleProof $ constructPath [] rootNode
  where
    constructPath :: [ProofElem a] -> MerkleNode a -> [ProofElem a]
    constructPath pElems (MerkleLeaf leafRoot' _)
      | leafRoot == leafRoot' = pElems
      | otherwise             = []
    constructPath pElems (MerkleBranch bRoot ln rn) = lPath ++ rPath
      where
        lProofElem = ProofElem (mRootHash ln) (mRootHash rn) L
        rProofElem = ProofElem (mRootHash rn) (mRootHash ln) R

        lPath = constructPath (lProofElem:pElems) ln
        rPath = constructPath (rProofElem:pElems) rn

-- | Validate a merkle tree proof of inclusion
validateMerkleProof :: forall a. MerkleProof a ->  MerkleHash a -> MerkleHash a -> Bool
validateMerkleProof (MerkleProof proofElems) treeRoot leafRoot =
    validate proofElems leafRoot
  where
    validate :: [ProofElem a] -> MerkleHash a -> Bool
    validate [] proofRoot = proofRoot == treeRoot
    validate (pElem:pElems) proofRoot
      | proofRoot /= nodeRoot pElem = False
      | otherwise = validate pElems $ hashProofElem pElem

    hashProofElem :: ProofElem a -> MerkleHash a
    hashProofElem (ProofElem pRoot sibRoot side) =
      case side of
        L -> mkRootHash pRoot sibRoot
        R -> mkRootHash sibRoot pRoot

-------------------------------------------------------------------------------
-- Hashing
-------------------------------------------------------------------------------

-- | Compute SHA-256 hash of a bytestring.
-- Maximum input size is (2^{64}-1)/8 bytes.
--
-- > Output size         : 256
-- > Internal state size : 1600
-- > Block size          : 1088
-- > Length size         : n/a
-- > Word size           : 64
-- > Rounds              : 24
sha256 :: ByteString -> ByteString
sha256 x = B.convertToBase B.Base16 (hash x :: Digest SHA3_256)

-- | Hash function to use for merkle tree
merkleHash :: ByteString -> ByteString
merkleHash = sha256

-------------------------------------------------------------------------------
-- Testing
-------------------------------------------------------------------------------

-- | Constructs a merkle tree and random leaf root to test inclusion of
testMerkleProofN :: Int -> IO Bool
testMerkleProofN n
  | n < 2 = panic "Cannot construct a merkle tree with < 2 nodes"
  | otherwise = do
      randN <- randomRIO (1,n) :: IO Int
      let mtree = mkMerkleTree $ map show [1..n]
          randLeaf = mkLeafRootHash $ show randN
          proof = merkleProof mtree randLeaf
      return $ validateMerkleProof proof (mtRootHash mtree) randLeaf
