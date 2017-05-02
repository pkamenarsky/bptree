{-# OPTIONS_GHC -fglasgow-exts #-}

module BPlusTree where

-- Implementation of B+ Tree, using a RecordFile as the underlying
-- primitive. A B+ Tree is a BTree where all the actual data is in the
-- keys.

-- A B+ tree is a tree of nodes, or blocks, which take up a fixed
-- amount of space on disk. We implement this using 'RecordFile' as a
-- convenient abstraction.

-- There are two kinds of nodes, leaf nodes and internal nodes. An
-- internal node contains only keys + pointers to other nodes. A leaf
-- node contains only keys + pointer to actual data.

-- Some complexity is added by the fact that keys can be of differing
-- lengths.

-- An internal node takes the following structure:
--
-- [ <p1> | kA | <p2> | kB | <p3> | kC | <p4> ]
--
-- where, e.g., <p1> points to the place to search for all keys less
-- than or equal to kA, <p2> points to the place to search for all
-- keys > kA and <= kB, and <p4> to the place to search for keys > kC.
--
-- The ps may either point to another internal node, for more searching, or
-- a leaf node.

-- A leaf node takes the structure:
--
-- [ kA | vA | kB | vB | kC | vC | <p> ]
--
-- where the 'vA' is the value corresponding to 'kA' and <p> points to
-- the next leaf node along.

-- Where we differ from the common B+ tree is that our keys are
-- variable length.  This makes the splitting code substantially more
-- fiddly. We need to know that no key is more than one quarter of the
-- length of a node, and no (key/value) pair is more than one quarter
-- of the length of a node. We don't get the 50% utilisation lower
-- bound of a fixed-key B+ tree, but a lower 25% bound.

-- INVARIANTS : All leaf nodes at same depth.
-- All internal nodes at least half full, except possibly the root node.
-- All leaf nodes at least half full (except possibly root)



-- a IMBPlusTree is an in-memory BPlusTree. Not particularly useful
-- except for testing purposes, the point of BPlusTrees is disk
-- storage.

-- A 'pointer' in an IMBPlusTree is just an Int index into the Seq.
-- The keys / values are always ByteStrings

import qualified Data.Sequence as S
import Data.Sequence(Seq,(|>))

import qualified Data.Foldable as F

import qualified Data.ByteString.Char8 as B
import Data.ByteString.Char8(ByteString)

import qualified Data.List as L

import Data.Word
import Data.Char
import Data.Ord

import Control.Monad.State

import Test.QuickCheck

import ADQL.BinaryUtils

data IMBPlusTree = IMBPlusTree Int Int (Seq IMBPlusNode)
                   deriving (Show)

newtype IMBPlusPtr = IMBPP Int deriving (Show,Eq)

data IMBPlusNode = IMBPLeaf [(ByteString,ByteString)] (Maybe IMBPlusPtr)
                 | IMBPInternal IMBPlusPtr [(ByteString,IMBPlusPtr)]
                   deriving (Show)

kvlength []          = 0
kvlength ((k,v):kvs) = B.length k + B.length v + kvlength kvs

nodesize (IMBPLeaf kvs _) = kvlength kvs + 4
nodesize (IMBPInternal _ kps) = 4 + sum [ B.length k + 4 | (k,_) <- kps ]

class Monad m => MonadBPlus m where
  root :: m IMBPlusPtr
  setRoot :: IMBPlusPtr -> m ()
  getSize :: m Int
  getNode :: IMBPlusPtr -> m IMBPlusNode
  setNode :: IMBPlusPtr -> IMBPlusNode -> m ()
  createNode :: IMBPlusNode -> m IMBPlusPtr
  allNodes :: m [IMBPlusPtr]

createRoot n = createNode n >>= setRoot

insert k v = do { rt <- root; insert' rt [] k v }

insert' node path k v = do
  nd <- getNode node
  case nd of
    IMBPLeaf kvs mptr -> insert'leaf node path k v kvs mptr
    IMBPInternal lp kps -> insert'internal node path k v lp kps

-- leaf split strategy:
-- (1) split contents of leave into two roughly equal parts
-- (2) insert new node into appropriate half
-- (3) expand / create parent node as appropriate
-- subtlety: have to split list by bytes not elements
-- subtlety: we put the 'middle element" in opposite side from
-- new element, otherwise we may overflow.
insert'leaf node path k v kvs mptr = do
  sz <- getSize
  if nodesize (IMBPLeaf ((k,v):kvs) mptr) <= sz then
    setNode node (IMBPLeaf (L.insert (k,v) kvs) mptr)
   else
        let (lefts,(rk,rv):rights) = splitAt (half-1) kvs
            half = length . takeWhile (< sz `div` 2) . 
                   scanl (\n (k,v) -> B.length k + B.length v + n) 0 $
                   kvs
            (lefts',rights'@((midk,_):_)) =
              if k < rk then (L.insert (k,v) lefts,(rk,rv):rights)
              else (lefts++[(rk,rv)],L.insert (k,v) rights)
            leftnode = node
        in do
          rightnode <- createNode (IMBPLeaf rights' mptr)
          setNode leftnode (IMBPLeaf lefts' (Just rightnode))
          case path of
            -- This was a "root leaf", we're making a new root
            [] -> createRoot (IMBPInternal leftnode [(midk,rightnode)])
            -- propagate new link up we've split a leaf, so we need to
            -- add an extra pointer to the parents
            p:pp -> insert'link p pp leftnode midk rightnode

insert'internal node path k v lp [] = insert' lp (node:path) k v
insert'internal node path k v lp ((rk,rp):kps) = 
  if (k<rk) then insert' lp (node:path) k v
  else insert'internal node path k v rp kps

-- insert'link : insert a new link into internal node 'node', just to the
-- right of 'leftnode', with discriminating key 'k'.
-- If the node gets full, will need to split and recurse
-- subtlety: can't split in half by list length. need to actually
-- work by byte length.
-- subtlety: we "promote" one key to the next level up. Whether we
-- take the last from the left or the first from the right depends
-- which side this key goes.
insert'link node path leftnode k rightnode = do
  sz <- getSize
  nd <- getNode node
  case nd of
    IMBPInternal lp kps ->
      if nodesize (IMBPInternal lp ((k,rightnode):kps)) <= sz then
        setNode node (insert'link'kps nd leftnode k rightnode)
      else
        let (alllkps,(rk,rp):rkps) = splitAt (half-1) kps
            half = length . takeWhile (< sz `div` 2) . 
                   scanl (\n (b,_) -> n + 4 + B.length b) 0 $
                   kps
            lkps = init alllkps
            (lrk,lrp) = last alllkps
            (left,midkey,right) = 
              if (k<lrk) then 
                (insert'link'kps (IMBPInternal lp lkps) leftnode k rightnode
                ,lrk
                ,IMBPInternal lrp ((rk,rp):rkps))
              else if (k>rk) then
                (IMBPInternal lp (lkps++[(lrk,lrp)])
                ,rk
                ,insert'link'kps (IMBPInternal rp rkps) leftnode k rightnode)
                   else
                (IMBPInternal lp (lkps++[(lrk,lrp)])
                ,k
                ,IMBPInternal rightnode ((rk,rp):rkps))
            leftp = node
        in do
          setNode leftp left
          rightp <- createNode right
          case path of
                []   -> createRoot (IMBPInternal leftp [(midkey,rightp)])
                p:pp -> insert'link p pp leftp midkey rightp
           
insert'link'kps (IMBPInternal lp kps) leftnode k rightnode =
  if lp == leftnode then
    IMBPInternal lp ((k,rightnode):kps)
  else let (lkps,(rk,rn):rkps) = span (\(_,n) -> n /= leftnode) kps
  in IMBPInternal lp (lkps ++ ((rk,rn):(k,rightnode):rkps))
  

insequence :: MonadBPlus m => m [(ByteString,ByteString)]
insequence = do { rt <- root; insequence' rt }

insequence' n = do
  nd <- getNode n
  case nd of
    IMBPLeaf kvs Nothing -> return kvs
    IMBPLeaf kvs (Just p) -> (kvs ++) `liftM` insequence' p
    IMBPInternal lp _ -> insequence' lp 

insequence_trav :: MonadBPlus m => m [(ByteString,ByteString)]
insequence_trav = do { rt <- root; insequence_trav' rt }
insequence_trav' rt = do { nd <- getNode rt; trav nd }
 where
    trav (IMBPLeaf kvs _) = return kvs
    trav (IMBPInternal lp []) = insequence_trav' lp
    trav (IMBPInternal lp ((rk,rp):xs)) =  
      liftM2 (++) (insequence_trav' lp) (trav (IMBPInternal rp xs))

-- IMBPlusTree is a simple abstract model of MonadBPlus

newtype IMAbstractBPlus a = IMABP { runIMABP :: State IMBPlusTree a }
                          deriving Monad

instance MonadBPlus IMAbstractBPlus where
  root = do { IMBPlusTree sz rt nodes <- IMABP get; return (IMBPP rt) }
  setRoot (IMBPP newrt) = do
    IMBPlusTree sz rt nodes <- IMABP get
    IMABP . put $ IMBPlusTree sz newrt nodes
  getSize = do { IMBPlusTree sz rt nodes <- IMABP get; return sz }
  getNode (IMBPP n) = do
    IMBPlusTree sz rt nodes <- IMABP get
    return (S.index nodes n)
  setNode (IMBPP n) nd = do
    IMBPlusTree sz rt nodes <- IMABP get
    IMABP . put $ IMBPlusTree sz rt (S.update n nd nodes)
  createNode nd = do
    IMBPlusTree sz rt nodes <- IMABP get
    IMABP . put $ IMBPlusTree sz rt (nodes |> nd)
    return (IMBPP $ S.length nodes)
  allNodes = do
    IMBPlusTree sz rt nodes <- IMABP get
    return (map IMBPP [0..(S.length nodes - 1)])
empty sz = IMBPlusTree sz 0 (S.singleton (IMBPLeaf [] Nothing))

runOnEmpty sz act = (execState . runIMABP) act (empty sz)

-- Making nodes 8 times as large is because key = value. 4 times as large
-- with all values one char long ought to work but doesn't seem to.
fromStrings sz l = runOnEmpty sz $ mapM_ (\k -> insert (B.pack k) (B.pack k)) l
fromStringsSafe l = fromStrings ((maximum $ 0 : map length l) * 8 + 36) l

withStrings sz l act = 
  (evalState . runIMABP)
  (do mapM_ (\k -> insert (B.pack k) (B.pack k)) l
      act)
  (empty sz)
  
withStringsSafe l act = 
  withStrings ((maximum $ 0 : map length l) * 8 + 36) l act
  
pp_tree :: MonadBPlus m => m String
pp_tree = do
  sz <- getSize
  rt <- root
  nodes <- allNodes
  nodedescs <- mapM (\p -> do nd <- getNode p
                              return (pp_node p nd)) nodes
  return $ "B+-Tree with blocksize " ++ show sz ++ 
    " and root node " ++ show rt ++ "\n" ++
    unlines nodedescs
  
pp_node p (IMBPLeaf kvs mptr) =
  "Leaf ID : " ++ pp_ptr p ++ " " ++ show kvs ++ 
  maybe " -|" (\n -> " -> " ++ pp_ptr n) mptr
pp_node p (IMBPInternal lp kps) = 
  "Node ID : " ++ pp_ptr p ++
  " [" ++ pp_ptr lp ++ 
  concatMap (\(k,p) -> "|" ++ show k ++ "|" ++ pp_ptr p) kps
  ++ "]"
pp_ptr (IMBPP n) = show n

reachable_ids  = root >>= reachable_ids' 
reachable_ids' n = do
  node <- getNode n
  let children = reachable_ids'' node
  ((n :) . concat) `fmap` (mapM reachable_ids' children)
  
reachable_ids'' (IMBPLeaf _ _) = []
reachable_ids'' (IMBPInternal lp kps) = lp : map snd kps

-- prop_sort : the tree structure manages to sort the list
prop_sort l = withStringsSafe l insequence ==
              (L.sort . map (\x->(B.pack x,B.pack x))) l
              
-- prop_traverse : the linked list traversal is the same
-- as the tree traversal
prop_traverse l = withStringsSafe l insequence == 
                  withStringsSafe l insequence_trav
                                    
-- All nodes are reachable from the root
prop_all_reachable l =
  let t@(IMBPlusTree _ _ nodes) = fromStringsSafe l
  in L.sort (reachable_ids t) == [0..(S.length nodes -1)]
     
-- All nodes fit within the size
prop_nodes_fit l =
  let t@(IMBPlusTree sz _ nodes) = fromStringsSafe l
  in all ((<=sz) . nodesize) . F.toList $ nodes

-- All nodes are at least 25% full
prop_nodes_qfull l =
  let t@(IMBPlusTree sz rt nodes) = fromStringsSafe l
      nonrootnodes = map (S.index nodes) ([0..(S.length nodes - 1)] L.\\ [rt])
  in all ((>=(sz`div`4)) . nodesize) $ nonrootnodes

-- The tree structure is honest
prop_tree_respected l = prop_tree_respected' . fromStringsSafe $ l

prop_tree_respected' (IMBPlusTree _ rt nodes) = 
  prop_tree_respected'node rt nodes Nothing Nothing
  
prop_tree_respected'node rt nodes lb ub =
  case S.index nodes rt of 
    IMBPLeaf kvs _ -> all (prop_tree_respected'inbounds lb ub) (map fst kvs)
    IMBPInternal lp kps -> prop_tree_respected'internal nodes lp kps lb ub

prop_tree_respected'internal nodes (IMBPP lp) [] lb ub =
  prop_tree_respected'node lp nodes lb ub
prop_tree_respected'internal nodes (IMBPP lp) ((k,p):kps) lb ub =
  prop_tree_respected'inbounds lb ub k &&
  prop_tree_respected'node lp nodes lb (Just k) &&
  prop_tree_respected'internal nodes p kps (Just k) ub

prop_tree_respected'inbounds lb ub k =
  (case lb of Nothing -> True; Just lk -> lk <= k) &&
  (case ub of Nothing -> True; Just rk -> k  < rk)
  
tidy_counterexample l =
  let chars   = "0123456789abcdefghijklmnopqrstuvwxyz"
      ordered = L.sort (zip l [0..])
      renamed = zipWith (\(s,n) m -> (replicate (length s) (chars !! m),n))
                ordered [0..]
  in map fst . L.sortBy (comparing snd) $ renamed
     
instance Arbitrary Char where
    arbitrary     = choose ('\32', '\128')
    coarbitrary c = variant (ord c `rem` 4)
    
cex1 = ["bbbbbbbbbbbbbbbbbbbbb","0000000000000","111111","dddddddddddddddddddddd","99","88888888888888888888888","3333333333","7777777777777777777","44444444","2222222222222222222","5555555555555","cccccccccccccccccccccc","666666666666","hhhhhhhhhhhhhhhhh","ggggggggggggggggggggg","iiiiiiiiiiiiiiiiiii","eeeeeeeee","fffffffff","a","jjjjjjjj"]                            
cex2 = ["gggg","aaaaaaaaaaaaaaaaaa","666666666666666","bbbbbbbbbb","333333333","9999999999","1111111","eeeeeeeeeeeeeeeee","2222222222","55555555555555555555555","ddddddddddddddddddd","","8888888888888888888888","jjjjjjjjjj","ffffffffffffffffffffff","44444444444444444","hhhhhhhhh","ii","77777777777777777777","ccccc"]
cex3 = ["44444444","2222222","111","3333333333","55","000"]
cex4 = ["222222","","111111","44444444","33333333"]
cex5 = ["111111111111111","0000000000000","44","22222222222222222","33333"]
cex6 =  ["5555","2","88888888888888888888888888888888888888","4444444444444444444444444444444444444","6666666666666","9999999999","000","33333333333333333333333333","111","aaa","777777777777777777777777777"]

-- Byte (on-disk) format for B-tree.
-- 
-- A B-tree file has a fixed blocksize, which is always a multiple of
-- 512 bytes. The first block in the file is a header block:

-- Header block:
--  4 bytes - File type 'ADB+'
--  4 bytes - version (1)
--  4 bytes - block size
--  4 bytes - index of "root" block

data BPlusFileDescriptor = BPFD { bpfdBlocksize :: Word32,
                                  bpfdRoot :: Word32 }

readBPlusHeader :: ByteString -> BPlusFileDescriptor
readBPlusHeader bs
  | ftype /= B.pack "ADB+" = error "readBPlusHeader : not a B+ Tree file"
  | fversion /= 1 = error $ "readBPlusHeader : unsupported version " ++ 
                   show fversion
  | otherwise = BPFD {bpfdBlocksize = fblocksize,
                      bpfdRoot = froot}
 where ftype      = B.take 4 bs
       fversion   = bsNthWord32 1 bs
       fblocksize = bsNthWord32 2 bs
       froot      = bsNthWord32 3 bs
      
writeBPlusHeader :: BPlusFileDescriptor -> ByteString
writeBPlusHeader bfpd = 
  B.concat [B.pack "ADB+",
            word32ToBs 1,
            word32ToBs (bpfdBlocksize bfpd),
            word32ToBs (bpfdRoot bfpd),
            B.replicate (fromIntegral (bpfdBlocksize bfpd) - 16) '\0']
                        
-- Then all the other blocks are node blocks. The node blocks all 
-- start with a four byte tag.

readBPlusNode :: ByteString -> IMBPlusNode
readBPlusNode bs =
  case bsNthWord32 0 bs of
    1 -> readLeafNode bs
    2 -> readInternalNode bs
    
writeBPlusNode :: Int -> IMBPlusNode -> ByteString
writeBPlusNode sz nd =
  let bs = case nd of
        IMBPLeaf _ _     -> writeLeafNode nd
        IMBPInternal _ _ -> writeInternalNode nd
      l = B.length bs
  in if l <= sz then
        B.append bs (B.replicate (sz - l) '\0')
  else error$"writeBPlusNode : node didn't fit, " ++ show l ++ " > " ++ show sz
    
-- 4 bytes - tag 1 : LeafNode
-- 4 bytes - pointer to next leaf (0 for end leaf)
-- 4 bytes - number of key-value pairs
-- n * [
--       4 bytes -- key length
--       * bytes -- key (should we pad?)
--       4 bytes -- value length
--       * bytes -- value
--     ]

readLeafNode :: ByteString -> IMBPlusNode
readLeafNode bs =
  let mptr = case bsNthWord32 1 bs of 0 -> Nothing
                                      n -> Just . IMBPP $ (fromIntegral n)
      npairs = bsNthWord32 2 bs
  in IMBPLeaf (readKVs npairs (B.drop 12 bs)) mptr

readKVs :: Word32 -> ByteString -> [(ByteString,ByteString)]
readKVs 0 bs = []
readKVs n bs =
  let keyl        = fromIntegral $ bsNthWord32 0 bs
      (key,rest)  = B.splitAt keyl (B.drop 4 bs)
      vl          = fromIntegral $ bsNthWord32 0 rest
      (val,rest') = B.splitAt vl (B.drop 4 rest)
  in (key,val) : readKVs (n-1) rest'  
      
writeLeafNode :: IMBPlusNode -> ByteString
writeLeafNode (IMBPLeaf kvs mptr) =
  B.concat $ [word32ToBs 1,
              word32ToBs . fromIntegral $ maybe 0 (\(IMBPP n) -> n) mptr, 
              word32ToBs . fromIntegral $ length kvs] ++
             concatMap (\(k,v) -> [word32ToBs . fromIntegral $ B.length k,
                                   k,
                                   word32ToBs . fromIntegral $ B.length v,
                                   v]) kvs

-- 4 bytes - tag 2 : Internal Node
-- 4 bytes - number of keys
-- 4 bytes - left-pointer
-- n * [
--       4 bytes -- key length
--       * bytes -- key
--       4 bytes -- pointer
--     ]

readInternalNode :: ByteString -> IMBPlusNode
readInternalNode bs = 
  let nkeys = bsNthWord32 1 bs
      lp = IMBPP . fromIntegral $ bsNthWord32 2 bs
  in IMBPInternal lp (readKPs nkeys (B.drop 12 bs))

readKPs 0 bs = []
readKPs n bs = 
  let keyl        = fromIntegral $ bsNthWord32 0 bs
      (key,rest)  = B.splitAt keyl (B.drop 4 bs)
      p           = IMBPP . fromIntegral $ bsNthWord32 0 rest
  in (key,p) : readKPs (n-1) (B.drop 4 rest)

writeInternalNode :: IMBPlusNode -> ByteString
writeInternalNode (IMBPInternal lp kps) =
  B.concat $ [word32ToBs 2,
              word32ToBs . fromIntegral $ length kps,
              word32ToBs . fromIntegral . (\(IMBPP n) -> n) $ lp
              ] ++
             concatMap
             (\(k,p) -> [word32ToBs . fromIntegral $ B.length k,
                         k,
                         word32ToBs . fromIntegral . (\(IMBPP n) -> n) $ p]) kps

newtype ByteStringBPlusTree a = 
  BSBP { runBSBP :: State (Int,IMBPlusPtr,ByteString) a }
  deriving Monad
                                         
getBSBlock sz n bs = B.take sz . B.drop (n*sz) $ bs
setBSBlock sz n bs block = B.concat [B.take (n*sz) bs,
                                     block,
                                     B.drop ((n+1)*sz) bs]
                           
instance MonadBPlus ByteStringBPlusTree where
  root = BSBP get >>= \(_,rt,_) -> return rt
  setRoot newrt = do
    (sz,rt,bs) <- BSBP get
    BSBP . put $ (sz,newrt,bs)
  getSize = BSBP get >>= \(sz,_,_) -> return sz
  getNode (IMBPP n) = do 
    (sz,rt,bs) <- BSBP get
    return . readBPlusNode $ getBSBlock sz n bs
  setNode (IMBPP n) nd = do
    (sz,rt,bs) <- BSBP get
    BSBP . put $ (sz,rt,setBSBlock sz n bs (writeBPlusNode sz nd))
  createNode nd = do
    (sz,rt,bs) <- BSBP get
    BSBP . put $ (sz,rt,bs `B.append` (writeBPlusNode sz nd))
    return (IMBPP (B.length bs `div` sz))
    
emptyBS sz = (sz,IMBPP 0,writeBPlusNode sz (IMBPLeaf [] Nothing))
runOnEmptyBS sz act = (execState . runBSBP) act (emptyBS sz)
fromStringsBS sz l = runOnEmptyBS sz $ mapM_ (\k -> insert (B.pack k) (B.pack k)) l
--fromStringsSafe l = fromStrings ((maximum $ 0 : map length l) * 8 + 36) l
