module ArrowBackend where

import qualified Data.Set as Set
import Data.List (permutations, intercalate)
import Control.Monad.State

data Dialogue = Empty
            | Atom String
            | Up Dialogue
            | Union Dialogue Dialogue
            | C [Dialogue]
            | W [Dialogue]
            | I [String]
            | SPE [String]
            | SPEstar [String]
            | SPE' [Dialogue]
            | PFA1 [String]
            | PFA1star [String]
            | PFAn [String]
            | PFAnstar [String]
            | PE [String]
            | PEstar [String]

instance Show Dialogue where
  show Empty         = "~"
  show (Atom s)      = s
  show (Up d)        = "(Up "    ++ show d ++ ")"
  show (Union d1 d2) = show d1 ++ " ∪ " ++ show d2
  show (I ss)        = "(I "     ++ unwords ss ++ ")"
  show (C ds)        = "(C "     ++ unwords (show <$> ds) ++ ")"
  show (W ds)        = "(W "     ++ unwords (show <$> ds) ++ ")"
  show (SPE xs)      = "(SPE "   ++ unwords xs ++ ")"
  show (SPEstar xs)  = "(SPE* "  ++ unwords xs ++ ")"
  show (SPE' ds)     = "(SPE' "  ++ unwords (show <$> ds) ++ ")"
  show (PFA1 xs)     = "(PFA1 "  ++ unwords xs ++ ")"
  show (PFA1star xs) = "(PFA1* " ++ unwords xs ++ ")"
  show (PFAn xs)     = "(PFAn "  ++ unwords xs ++ ")"
  show (PFAnstar xs) = "(PFAn* " ++ unwords xs ++ ")"
  show (PE xs)       = "(PE "    ++ unwords xs ++ ")"
  show (PEstar xs)   = "(PE* "   ++ unwords xs ++ ")"

data Response = One String
              | Tup [String]

instance Show Response where
  show (One s) = s
  show (Tup ss) = "(" ++ unwords ss ++ ")"

-------------------------------------
----------- Simplification ----------
-------------------------------------

-- Completely simplify
simplify :: Dialogue -> Dialogue
simplify d = maybe d simplify (simplify1 d)

-- Convenience function. Same as simplify, but returns
-- a Maybe so that it can be used in monadic sequence.
simplifyM :: Dialogue -> Maybe Dialogue
simplifyM = Just . simplify

-- Applies a single simplification rule
simplify1 :: Dialogue -> Maybe Dialogue
-- Rule 1: zero subdialogues
simplify1 (C []) = Just Empty
simplify1 (W []) = Just Empty
simplify1 (I []) = Just Empty
simplify1 (SPE []) = Just Empty
simplify1 (SPEstar []) = Just Empty
simplify1 (SPE' []) = Just Empty
simplify1 (PFA1 []) = Just Empty
simplify1 (PFA1star []) = Just Empty
simplify1 (PFAn []) = Just Empty
simplify1 (PFAnstar []) = Just Empty
simplify1 (PE []) = Just Empty
simplify1 (PEstar []) = Just Empty
-- Rule 2: one subdialogue
simplify1 (C [d]) = Just d
--simplify1 (W [d]) = Just d         -- This rule cannot exist with arrows
simplify1 (I [x]) = Just (Atom x)
simplify1 (SPE [x]) = Just (Atom x)
simplify1 (SPEstar [x]) = Just (Atom x)
simplify1 (SPE' [d]) = Just d
simplify1 (PFA1 [x]) = Just (Atom x)
simplify1 (PFA1star [x]) = Just (Atom x)
simplify1 (PFAn [x]) = Just (Atom x)
simplify1 (PFAnstar [x]) = Just (Atom x)
simplify1 (PE [x]) = Just (Atom x)
simplify1 (PEstar [x]) = Just (Atom x)
-- Other rules
simplify1 (C ds) = case removeEmptyDialogues ds of
  Just newsubs -> Just (C newsubs)
  Nothing      -> case flattenCurries ds of
    Just newsubs -> Just (C newsubs)
    Nothing      -> C <$> simplifyL ds
simplify1 (SPE' ds) = case removeEmptyDialogues ds of
  Just newsubs -> Just (SPE' newsubs)
  Nothing      -> SPE' <$> simplifyL ds
simplify1 (W ds) = case removeEmptyDialogues ds of
  Just newsubs -> Just (W newsubs)
  Nothing      -> W <$> simplifyL ds
simplify1 (Union d1 d2) = case simplify1 d1 of
  Just d1' -> Just (Union d1' d2)
  Nothing  -> case simplify1 d2 of
    Just d2' -> Just (Union d1 d2')
    Nothing  -> Nothing
simplify1 _ = Nothing

-- Simplifies the first dialogue it can
simplifyL :: [Dialogue] -> Maybe [Dialogue]
simplifyL [] = Nothing
simplifyL (d:ds) = case simplify1 d of
  Just newd -> Just (newd:ds)
  Nothing   -> (d:) <$> simplifyL ds

-----------------------------------------
-- Reduction
-----------------------------------------

data RS = RS [Dialogue -> Dialogue] Dialogue [Response]

instance Show RS where
  show (RS lam d inp) = "(Lam{len=" ++ show (length lam) ++ "}, " ++ show d ++ ", " ++ show inp ++ ")"

-- Builts a reduction state and reduces as far as possible.
-- Should always reduce to at most one state.
dialogueAcceptsInput :: Dialogue -> [Response] -> Bool
dialogueAcceptsInput d inp = case reduceStar [RS [const Empty] d inp] of
  [RS [] Empty []] -> True
  _                -> False

-- Reduces zero or more times, as far as possible
reduceStar :: [RS] -> [RS]
reduceStar rs = case rs >>= reduce of
  []  -> rs
  rs' -> reduceStar rs'

-- Implements the reduction relation (~>) described in the document.
-- The non-determinism is handled with lists.
reduce :: RS -> [RS]
-- [empty]
reduce (RS (f:lam) Empty inp) = [RS lam (f Empty) inp]
-- [atom]
reduce (RS (f:lam) (Atom x) ((One y):inp))
  | x == y    = [RS lam (f Empty) inp]
  | otherwise = []
-- [arrow]
reduce (RS (f1:f2:lam) (Up d) inp) = [RS (f2 . f1 : lam) d inp]
-- [union]
reduce (RS lam (Union d1 d2) inp) = [RS lam d1 inp, RS lam d2 inp]
-- [C]
reduce (RS lam (C (d:ds)) inp) = [RS ((\d' -> simplify (C (d':ds))):lam) d inp]
-- [W]
reduce (RS lam (W ds) inp) =
  do (dcon, d) <- extractEach [] ds
     return (RS (dcon:lam) d inp)
  where extractEach d1 [] = []
        extractEach d1 (d:ds) = (\d' -> simplify (W (d1++[d']++ds)), d)
                              : extractEach (d1++[d]) ds
-- [I]
reduce (RS (f:lam) (I ss) ((Tup rs):inp))
  | ss `setEq` rs = [RS lam (f Empty) inp]
  | otherwise     = []
-- [SPE]
reduce (RS lam (SPE xs) ((One y):inp))
  | y `elem` xs = [RS lam (simplify (I (xs `setSubtract` [y]))) inp]
  | otherwise   = []
-- [SPE*]
reduce (RS lam (SPEstar xs) ((One y):inp))
  | y `elem` xs = [RS lam (simplify (SPEstar (xs `setSubtract` [y]))) inp]
  | otherwise   = []
reduce (RS lam (SPEstar xs) ((Tup ys):inp))
  | xs `setEq` ys = [RS lam Empty inp]
  | otherwise     = []
-- [SPE']
reduce (RS lam (SPE' ds) inp) =
  do (dcon, d) <- extractEach [] ds
     return (RS (dcon:lam) d inp)
  where extractEach d1 [] = []
        extractEach d1 (d:ds) = (\d' -> simplify (SPE' (d1++[d']++ds)), d)
                              : extractEach (d1++[d]) ds
-- [PFA1]
reduce (RS lam (PFA1 (x:xs)) ((One y):inp))
  | x == y    = [RS lam (simplify (I xs)) inp]
  | otherwise = []
-- [PFA1star]
reduce (RS lam (PFA1star (x:xs)) ((One y):inp))
  | x == y    = [RS lam (simplify (PFA1star xs)) inp]
  | otherwise = []
reduce (RS lam (PFA1star xs) ((Tup ys):inp))
  | xs `setEq` ys = [RS lam Empty inp]
  | otherwise = []
-- [PE]
reduce (RS lam (PE xs) ((Tup ys):inp))
  | ys `subsetOf` xs = [RS lam (simplify (I (xs `setSubtract` ys))) inp]
  | otherwise        = []
reduce (RS lam (PE xs) ((One y):inp)) = reduce (RS lam (PE xs) ((Tup [y]):inp))
-- [PE*]
reduce (RS lam (PEstar xs) ((Tup ys):inp))
  | ys `subsetOf` xs = [RS lam (simplify (PEstar (xs `setSubtract` ys))) inp]
  | otherwise        = []
reduce (RS lam (PEstar xs) ((One y):inp)) = reduce (RS lam (PEstar xs) ((Tup [y]):inp))
reduce _ = []

--------------------------------
--- Staging
--------------------------------

initDialogue :: Dialogue -> Maybe RS
initDialogue d = Just (RS [const Empty] d [])

stage :: Response -> RS -> Maybe RS
stage inp (RS lam d _) =
  case consumeOneInput [RS lam d [inp]] of
    []              -> Nothing
    [RS lam' d' []] -> Just (RS lam' d' [])
    other           -> Nothing
  where consumeOneInput states = states >>= (\state ->
          case reduce state of
            [] -> []
            [RS lam' d' []] -> [RS lam' d' []]
            other -> consumeOneInput other
          )

verifyComplete :: RS -> Maybe ()
verifyComplete (RS [] Empty []) = Just ()
verifyComplete _ = Nothing

-----------------------------------------------------
-- Generating Episodes
-----------------------------------------------------

getPossibleReductions :: RS -> [Response] -> [(RS, Response)]
getPossibleReductions state resps = resps >>= (\resp ->
  case stage resp state of
    Just newState -> [(newState, resp)]
    Nothing       -> []
  )

genEpisodes :: RS -> [Response] -> [[Response]]
genEpisodes state resps =
  case getPossibleReductions state resps of
    [] -> [[]]
    reds -> reds >>= (\(state, resp) ->
        fmap (resp:) (genEpisodes state resps)
      )

printEpisodes :: [[Response]] -> String
printEpisodes respss =
  "(" ++ intercalate "\n" ((\resps ->
    "(" ++ intercalate " " ((\resp ->
      show resp
      ) <$> resps) ++ ")"
    ) <$> respss) ++ ")"

--------------------------------
------ Utility Functions -------
--------------------------------

-- Removes empty dialogues from the list. Returns Nothing if nothing was removed.
removeEmptyDialogues :: [Dialogue] -> Maybe [Dialogue]
removeEmptyDialogues [] = Nothing
removeEmptyDialogues (Empty:ds) = Just (maybe ds id (removeEmptyDialogues ds))
removeEmptyDialogues (d:ds) = (d:) <$> removeEmptyDialogues ds

-- Removes C-dialogues from the list inserting the subdialogues instead. Only
-- a single layer is flattened.
flattenCurries :: [Dialogue] -> Maybe [Dialogue]
flattenCurries [] = Nothing
flattenCurries ((C cs):ds) = Just (cs ++ maybe ds id (flattenCurries ds))
flattenCurries (d:ds) = (d:) <$> flattenCurries ds

-- Convenience function. Wrapper around Set.isSubsetOf
subsetOf :: (Ord a) => [a] -> [a] -> Bool
subsetOf l1 l2 = Set.isSubsetOf (Set.fromList l1) (Set.fromList l2)

-- Convenience function. Wrapper around set equality
setEq :: (Ord a) => [a] -> [a] -> Bool
setEq l1 l2 = Set.fromList l1 == Set.fromList l2

-- Returns the first list with elements from the second list removed.
-- The order of the remaining elements is preserved.
setSubtract :: (Eq a) => [a] -> [a] -> [a]
setSubtract l1 [] = l1
setSubtract [] _ = []
setSubtract l1 (x:xs) = setSubtract (remove x l1) xs
  where remove _ [] = []
        remove y (x:xs) = if x == y then remove y xs else x : remove y xs

-- If the second list can be reordered into a prefix of the first list,
-- then the first list is returned with that prefix removed.
removePrefix :: (Ord a) => [a] -> [a] -> Maybe [a]
removePrefix list prefix = rmp list (Set.fromList prefix)
  where rmp [] prefix = if prefix == Set.empty then Just [] else Nothing
        rmp (x:xs) prefix
         | prefix == Set.empty = Just (x:xs)
         | Set.member x prefix = rmp xs (Set.delete x prefix)
         | otherwise           = Nothing

------------------------------------------------------
-- Tests. The result_ values should all be (Just ~) --
------------------------------------------------------
      
dialogueA = W [C [Up (Atom "a"), Atom "b"], C [Atom "x", Atom "y"]]
resultA = initDialogue dialogueA
      >>= stage (One "a")
      >>= stage (One "x")
      >>= stage (One "y")
      >>= stage (One "b")
      >>= verifyComplete

dialogueB = W [I ["a", "b", "c"], I ["x", "y"]]
resultB = initDialogue dialogueB
      >>= stage (Tup ["x", "y"])
      >>= stage (Tup ["a", "b", "c"])
      >>= verifyComplete

dialogueC = PEstar ["a", "b", "c", "d", "e"]
resultC = initDialogue dialogueC
      >>= stage (Tup ["c", "e"])
      >>= stage (One "b")
      >>= stage (Tup ["a", "d"])
      >>= verifyComplete

dialogueD = Union (C [Atom "a", Atom "b", Atom "c"]) (C [Atom "c", Atom "b", Atom "a"])
resultD = initDialogue dialogueD
      >>= stage (One "a")
      >>= stage (One "b")
      >>= stage (One "c")
      >>= verifyComplete

dialogueE = W [C [Up (Atom "a"), Atom "b"], C [Up (Atom "x"), Atom "y"]]

dialogueF = W [C [Up (Atom "a"), Up (Atom "b"), Up (Atom "c"), Up (Atom "d"), Atom "e"], C [Atom "u", Up (Atom "v"), Atom "x", Atom "y"]]

dialogueG = W [Atom "a", C [Up (Atom "x"), Atom "y"]]

-----------------------------------------------------
-- Main Program
-----------------------------------------------------

rs = RS [const Empty] dialogueE []
--resps = [One "a", One "b", One "x", One "y"]
--resps = [One "a", One "b", One "c"]
resps = [One "a", One "b", One "c", One "d", One "e", One "u", One "v", One "x", One "y"]

