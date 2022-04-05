import qualified Data.Set as Set
import Data.List (permutations, intercalate)
import Control.Monad.State
import System.Environment (getArgs)

data Dialog = Empty
            | Atom String
            | Up Dialog
            | Union Dialog Dialog
            | C [Dialog]
            | W [Dialog]
            | I [String]
            | SPE [String]
            | SPEstar [String]
            | SPE' [Dialog]
            | PFA1 [String]
            | PFA1star [String]
            | PFAn [String]
            | PFAnstar [String]
            | PE [String]
            | PEstar [String]

instance Show Dialog where
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
--  show (Union d1 d2) = "(Union " ++ show d1 ++ " " ++ show d2 ++ ")"

data Response = One String
              | Tup [String]

instance Show Response where
  show (One s) = s
  show (Tup ss) = "(" ++ unwords ss ++ ")"

-------------------------------------
----------- Simplification ----------
-------------------------------------

-- Completely simplify
simplify :: Dialog -> Dialog
simplify d = maybe d simplify (simplify1 d)

-- Convenience function. Same as simplify, but returns a Maybe so that
-- it can be used in monadic sequence.
simplifyM :: Dialog -> Maybe Dialog
simplifyM = Just . simplify

-- Applies a single simplification rule
simplify1 :: Dialog -> Maybe Dialog
-- Rule 1: zero subdialogs
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
-- Rule 2: one subdialog
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
simplify1 (C ds) = case removeEmptyDialogs ds of
  Just newsubs -> Just (C newsubs)
  Nothing      -> case flattenCurries ds of
    Just newsubs -> Just (C newsubs)
    Nothing      -> C <$> simplifyL ds
simplify1 (SPE' ds) = case removeEmptyDialogs ds of
  Just newsubs -> Just (SPE' newsubs)
  Nothing      -> SPE' <$> simplifyL ds
simplify1 (W ds) = case removeEmptyDialogs ds of
  Just newsubs -> Just (W newsubs)
  Nothing      -> W <$> simplifyL ds
simplify1 (Union d1 d2) = case simplify1 d1 of
  Just d1' -> Just (Union d1' d2)
  Nothing  -> case simplify1 d2 of
    Just d2' -> Just (Union d1 d2')
    Nothing  -> Nothing
simplify1 _ = Nothing

-- Simplifies the first dialog it can
simplifyL :: [Dialog] -> Maybe [Dialog]
simplifyL [] = Nothing
simplifyL (d:ds) = case simplify1 d of
  Just newd -> Just (newd:ds)
  Nothing   -> (d:) <$> simplifyL ds

-----------------------------------------
-- Reduction
-----------------------------------------

data RS = RS [Dialog -> Dialog] Dialog [Response]

instance Show RS where
  show (RS lam d inp) = "(Lam{len=" ++ show (length lam) ++ "}, " ++ show d ++ ", " ++ show inp ++ ")"

-- Builts a reduction state and reduces as far as possible.
-- Should always reduce to at most one state.
dialogAcceptsInput :: Dialog -> [Response] -> Bool
dialogAcceptsInput d inp = case reduceStar [RS [const Empty] d inp] of
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

-- Removes empty dialogs from the list. Returns Nothing if nothing was removed.
removeEmptyDialogs :: [Dialog] -> Maybe [Dialog]
removeEmptyDialogs [] = Nothing
removeEmptyDialogs (Empty:ds) = Just (maybe ds id (removeEmptyDialogs ds))
removeEmptyDialogs (d:ds) = (d:) <$> removeEmptyDialogs ds

-- Removes C-dialogs from the list inserting the subdialogs instead. Only
-- a single layer is flattened.
flattenCurries :: [Dialog] -> Maybe [Dialog]
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

-----------------------------------------------------
-- Main Program
-----------------------------------------------------

-- Only supports Atom, Up, C, W
findAllResponses :: Dialog -> [Response]
findAllResponses (Atom x) = [One x]
findAllResponses (Up d) = findAllResponses d
findAllResponses (C ds) = ds >>= findAllResponses
findAllResponses (W ds) = ds >>= findAllResponses
findAllResponses _ = []

-- run using `runhaskell gen-episodes.sh <idx>`
-- where `<idx>` is the index into `dialogExamples`
main :: IO ()
main = do
  args <- getArgs
  let idx = read (head args) :: Int
  let thedialog = dialogExamples !! idx
  let rs = RS [const Empty] thedialog []
  let resps = findAllResponses thedialog
  putStrLn (printEpisodes (genEpisodes rs resps))

dialogExamples :: [Dialog]
dialogExamples = [
  W [(W [(Up (Atom "a")), (Atom "b")]), (C [(Atom "d"), (Atom "c")])],
  W [(W [(Atom "b"), (C [(Atom "a"), (Up (Up (Atom "c")))])]), (Atom "d")],
  W [(Atom "b"), (Atom "d"), (C [(Up (Atom "a")), (Atom "c")])],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "a"), (C [(Up (Atom "b")), (Atom "d")]), (Atom "c")],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "a"), (Atom "b")]), (Atom "c")],
  W [(W [(Atom "c"), (Atom "a")]), (Atom "b"), (Atom "d")],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(Atom "a"), (Atom "b"), (C [(Atom "d"), (Up (Atom "c"))])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(C [(Up (Atom "b")), (Up (Atom "a"))]), (W [(Atom "d"), (Atom "c")])],
  W [(Atom "a"), (Atom "d"), (W [(Atom "b"), (Atom "c")])],
  W [(C [(Atom "d"), (Atom "b")]), (W [(Atom "c"), (Up (Atom "a"))])],
  W [(Atom "a"), (Atom "b"), (C [(Up (Atom "d")), (Up (Atom "c"))])],
  W [(Atom "a"), (Atom "b"), (W [(Atom "c"), (Atom "d")])],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "d"), (Atom "c"), (W [(Atom "a"), (Up (Atom "b"))])],
  W [(C [(C [(Up (Up (Atom "c"))), (Atom "b")]), (Up (Atom "d"))]), (Atom "a")],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(C [(Up (Atom "a")), (Atom "b")]), (W [(Atom "c"), (Atom "d")])],
  W [(C [(Atom "b"), (Up (Atom "a")), (Up (Atom "d"))]), (Atom "c")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(W [(Atom "b"), (Atom "a")]), (Atom "d"), (Atom "c")],
  W [(W [(Up (Atom "b")), (Up (Atom "c"))]), (C [(Up (Atom "a")), (Up (Atom "d"))])],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "c"), (Atom "d"), (C [(Up (Atom "a")), (Up (Atom "b"))])],
  W [(C [(Atom "a"), (Atom "b")]), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(W [(Atom "c"), (Up (Atom "d"))]), (C [(Atom "b"), (Atom "a")])],
  W [(C [(Up (Atom "b")), (Atom "a")]), (C [(Up (Atom "d")), (Up (Atom "c"))])],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (C [(Atom "a"), (Up (Atom "c")), (Atom "b")])],
  W [(C [(Atom "d"), (Atom "b")]), (W [(Atom "c"), (Up (Atom "a"))])],
  W [(C [(Atom "a"), (Atom "c")]), (Atom "d"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "c"), (Atom "a"), (Atom "b")])],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(Atom "c"), (W [(Atom "b"), (Atom "d")]), (Atom "a")],
  W [(Atom "c"), (Atom "a"), (C [(Up (Atom "d")), (Up (Atom "b"))])],
  W [(Atom "c"), (W [(Atom "a"), (Atom "d"), (Up (Atom "b"))])],
  W [(W [(Atom "b"), (Atom "a")]), (W [(Atom "d"), (Atom "c")])],
  W [(W [(Atom "c"), (Atom "b")]), (W [(Atom "d"), (Atom "a")])],
  W [(Atom "b"), (Atom "d"), (C [(Up (Atom "a")), (Atom "c")])],
  W [(Atom "c"), (Atom "b"), (W [(Atom "a"), (Up (Atom "d"))])],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(W [(Atom "a"), (Up (Atom "c"))]), (W [(Atom "b"), (Up (Atom "d"))])],
  W [(Atom "b"), (Atom "a"), (W [(Atom "d"), (Up (Atom "c"))])],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(Atom "d"), (Atom "b"), (W [(Up (Atom "a")), (Atom "c")])],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(Atom "a"), (Atom "c"), (W [(Atom "b"), (Up (Atom "d"))])],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(C [(C [(Atom "b"), (Up (Up (Atom "c")))]), (Up (Atom "d"))]), (Atom "a")],
  W [(W [(Atom "b"), (Atom "a"), (Atom "c")]), (Atom "d")],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "a"), (C [(Atom "c"), (Atom "d")]), (Atom "b")],
  W [(W [(Atom "d"), (Atom "b")]), (W [(Atom "c"), (Up (Atom "a"))])],
  W [(W [(Atom "a"), (Atom "c")]), (W [(Up (Atom "b")), (Atom "d")])],
  W [(C [(Atom "d"), (Up (Atom "a"))]), (W [(Atom "b"), (Atom "c")])],
  W [(C [(Up (Atom "a")), (Atom "d")]), (W [(Up (Atom "b")), (Atom "c")])],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(C [(Atom "d"), (Atom "a")]), (Atom "c"), (Atom "b")],
  W [(Atom "c"), (W [(Atom "a"), (Up (Atom "b")), (Atom "d")])],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "b"), (Atom "a"), (C [(Up (Atom "c")), (Up (Atom "d"))])],
  W [(W [(Up (Atom "a")), (Atom "b")]), (C [(Atom "c"), (Atom "d")])],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(C [(Up (Atom "a")), (Up (Atom "b"))]), (Atom "d"), (Atom "c")],
  W [(C [(C [(Atom "d"), (Atom "c")]), (Up (Atom "a"))]), (Atom "b")],
  W [(W [(Atom "c"), (Atom "d")]), (Atom "b"), (Atom "a")],
  W [(Atom "d"), (C [(Up (Atom "a")), (C [(Up (Up (Atom "b"))), (Atom "c")])])],
  W [(Atom "b"), (Atom "d"), (C [(Atom "c"), (Up (Atom "a"))])],
  W [(Atom "d"), (Atom "a"), (C [(Atom "b"), (Up (Atom "c"))])],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (Atom "c"), (W [(Atom "a"), (Atom "b")])],
  W [(Atom "b"), (C [(Up (Atom "d")), (Atom "c"), (Atom "a")])],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (Atom "c"), (W [(Atom "a"), (Atom "d")])],
  W [(Atom "c"), (Atom "a"), (C [(Up (Atom "b")), (Up (Atom "d"))])],
  W [(Atom "b"), (Atom "d"), (W [(Atom "c"), (Atom "a")])],
  W [(Atom "c"), (Atom "d"), (C [(Atom "b"), (Atom "a")])],
  W [(C [(Up (Atom "a")), (Up (Atom "d"))]), (Atom "b"), (Atom "c")],
  W [(Atom "a"), (C [(Up (Atom "b")), (Up (Atom "d"))]), (Atom "c")],
  W [(Atom "b"), (Atom "d"), (Atom "c"), (Atom "a")],
  W [(Atom "a"), (C [(Up (Atom "c")), (Up (Atom "b")), (Atom "d")])],
  W [(Atom "a"), (Atom "b"), (W [(Atom "c"), (Atom "d")])],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (C [(Up (Atom "d")), (Up (Atom "a"))])],
  W [(Atom "b"), (Atom "a"), (W [(Atom "d"), (Up (Atom "c"))])],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(Atom "b"), (W [(W [(Up (Atom "c")), (Atom "a")]), (Atom "d")])],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(W [(Atom "d"), (C [(Atom "c"), (Up (Up (Atom "a")))])]), (Atom "b")],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(W [(Atom "c"), (Up (Atom "a"))]), (W [(Atom "b"), (Atom "d")])],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(W [(Up (Atom "c")), (Atom "a")]), (Atom "b"), (Atom "d")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "c"), (Atom "b"), (Atom "a"), (Atom "d")],
  W [(Atom "d"), (Atom "b"), (C [(Up (Atom "a")), (Atom "c")])],
  W [(Atom "c"), (Atom "b"), (Atom "a"), (Atom "d")],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(C [(Atom "b"), (Atom "c")]), (C [(Atom "d"), (Up (Atom "a"))])],
  W [(C [(Atom "b"), (Atom "c")]), (W [(Atom "a"), (Up (Atom "d"))])],
  W [(Atom "d"), (Atom "b"), (C [(Atom "c"), (Atom "a")])],
  W [(C [(Atom "a"), (Atom "c")]), (W [(Up (Atom "d")), (Atom "b")])],
  W [(W [(Atom "b"), (Up (Atom "d"))]), (C [(Atom "c"), (Up (Atom "a"))])],
  W [(W [(Atom "c"), (Up (Atom "d"))]), (C [(Up (Atom "a")), (Up (Atom "b"))])],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(C [(W [(Atom "a"), (Atom "c")]), (Up (Atom "b"))]), (Atom "d")],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(C [(Atom "b"), (Atom "a")]), (Atom "c"), (Atom "d")],
  W [(Atom "a"), (Atom "d"), (C [(Atom "b"), (Up (Atom "c"))])],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(C [(Atom "b"), (Up (Atom "c")), (Up (Atom "d"))]), (Atom "a")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(W [(Atom "d"), (Atom "c"), (Up (Atom "a"))]), (Atom "b")],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(W [(Up (Atom "a")), (Atom "d")]), (C [(Atom "c"), (Up (Atom "b"))])],
  W [(Atom "a"), (Atom "b"), (C [(Up (Atom "c")), (Atom "d")])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "c"), (Atom "a"), (W [(Up (Atom "d")), (Up (Atom "b"))])],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "c"), (Atom "a")]), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(W [(C [(Atom "c"), (Atom "b")]), (Up (Atom "a"))]), (Atom "d")],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(Atom "d"), (C [(Atom "c"), (Up (Atom "a"))]), (Atom "b")],
  W [(Atom "b"), (C [(Atom "d"), (Atom "c")]), (Atom "a")],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(C [(Atom "d"), (Up (Atom "a"))]), (W [(Atom "b"), (Atom "c")])],
  W [(Atom "d"), (Atom "c"), (C [(Atom "b"), (Atom "a")])],
  W [(W [(Atom "d"), (Up (Atom "c"))]), (C [(Up (Atom "b")), (Atom "a")])],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (C [(Atom "d"), (Atom "b"), (Atom "c")])],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (W [(C [(Atom "a"), (Up (Atom "b"))]), (Atom "c")])],
  W [(Atom "c"), (Atom "b"), (Atom "a"), (Atom "d")],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(C [(Atom "b"), (Up (Atom "d"))]), (Atom "a"), (Atom "c")],
  W [(W [(Atom "a"), (Atom "c")]), (Atom "b"), (Atom "d")],
  W [(Atom "d"), (W [(W [(Atom "c"), (Up (Up (Atom "a")))]), (Atom "b")])],
  W [(W [(Atom "a"), (Atom "d")]), (Atom "c"), (Atom "b")],
  W [(Atom "b"), (W [(Up (Atom "d")), (Atom "c"), (Atom "a")])],
  W [(Atom "b"), (C [(Up (Atom "d")), (Up (Atom "a"))]), (Atom "c")],
  W [(Atom "b"), (W [(Atom "d"), (Atom "c")]), (Atom "a")],
  W [(W [(Atom "c"), (Atom "b")]), (W [(Atom "a"), (Atom "d")])],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (C [(Atom "a"), (Up (Atom "d"))])],
  W [(Atom "d"), (Atom "c"), (W [(Atom "a"), (Up (Atom "b"))])],
  W [(Atom "d"), (C [(Up (Atom "a")), (Up (Atom "c")), (Up (Atom "b"))])],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(Atom "a"), (W [(Up (Atom "b")), (Up (Atom "c"))]), (Atom "d")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(Atom "c"), (W [(Up (Atom "b")), (Up (Atom "a"))]), (Atom "d")],
  W [(C [(Atom "b"), (Atom "d")]), (Atom "a"), (Atom "c")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (C [(Atom "c"), (Atom "b")]), (Atom "a")],
  W [(Atom "d"), (W [(Atom "a"), (Atom "b")]), (Atom "c")],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(Atom "a"), (W [(W [(Atom "d"), (Atom "b")]), (Atom "c")])],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (C [(Up (Atom "a")), (Up (Atom "d"))]), (Atom "c")],
  W [(W [(W [(Atom "a"), (Atom "d")]), (Atom "c")]), (Atom "b")],
  W [(C [(Atom "b"), (Atom "a")]), (W [(Up (Atom "c")), (Up (Atom "d"))])],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(C [(Up (Atom "c")), (Up (Atom "a"))]), (Atom "b"), (Atom "d")],
  W [(W [(Atom "c"), (Atom "b")]), (C [(Up (Atom "d")), (Atom "a")])],
  W [(Atom "d"), (W [(Up (Atom "a")), (Atom "c"), (Atom "b")])],
  W [(Atom "a"), (Atom "b"), (W [(Atom "c"), (Atom "d")])],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(Atom "c"), (C [(Up (Atom "a")), (Up (Atom "d"))]), (Atom "b")],
  W [(C [(Atom "c"), (Up (Atom "d"))]), (C [(Up (Atom "a")), (Atom "b")])],
  W [(C [(Atom "c"), (Atom "d")]), (Atom "b"), (Atom "a")],
  W [(W [(Up (Atom "d")), (W [(Atom "a"), (Atom "c")])]), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(C [(Up (Atom "c")), (Up (Atom "b"))]), (C [(Atom "a"), (Atom "d")])],
  W [(Atom "c"), (Atom "b"), (Atom "a"), (Atom "d")],
  W [(W [(Atom "b"), (Up (Atom "c"))]), (C [(Up (Atom "a")), (Up (Atom "d"))])],
  W [(W [(Atom "d"), (Atom "b")]), (W [(Up (Atom "c")), (Atom "a")])],
  W [(C [(Up (Atom "c")), (Up (Atom "b"))]), (W [(Atom "d"), (Atom "a")])],
  W [(Atom "b"), (Atom "a"), (C [(Atom "d"), (Up (Atom "c"))])],
  W [(Atom "b"), (Atom "a"), (W [(Up (Atom "d")), (Atom "c")])],
  W [(C [(Atom "c"), (Atom "a")]), (C [(Atom "b"), (Atom "d")])],
  W [(W [(Atom "a"), (Atom "c")]), (Atom "b"), (Atom "d")],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(W [(C [(Up (Up (Atom "d"))), (Up (Atom "b"))]), (Atom "a")]), (Atom "c")],
  W [(C [(Atom "b"), (Up (Atom "a"))]), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (W [(Atom "d"), (C [(Atom "a"), (Up (Atom "c"))])])],
  W [(Atom "d"), (C [(Atom "c"), (Up (Atom "a"))]), (Atom "b")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(W [(Up (Atom "c")), (Up (Atom "a"))]), (Atom "b"), (Atom "d")],
  W [(Atom "c"), (Atom "d"), (W [(Atom "b"), (Up (Atom "a"))])],
  W [(Atom "a"), (Atom "c"), (C [(Up (Atom "b")), (Atom "d")])],
  W [(C [(Up (Atom "b")), (Up (Atom "a")), (Atom "d")]), (Atom "c")],
  W [(Atom "c"), (Atom "a"), (W [(Atom "b"), (Atom "d")])],
  W [(W [(Up (Atom "b")), (Atom "a")]), (Atom "c"), (Atom "d")],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(Atom "b"), (C [(Atom "a"), (Atom "d")]), (Atom "c")],
  W [(Atom "d"), (W [(Up (Atom "b")), (Atom "a")]), (Atom "c")],
  W [(Atom "c"), (Atom "d"), (W [(Up (Atom "b")), (Atom "a")])],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(C [(Up (Atom "c")), (Up (Atom "a"))]), (Atom "d"), (Atom "b")],
  W [(Atom "d"), (C [(Up (Atom "b")), (Up (Atom "a")), (Up (Atom "c"))])],
  W [(Atom "a"), (C [(Atom "d"), (Up (Atom "b")), (Up (Atom "c"))])],
  W [(Atom "d"), (C [(Atom "c"), (Up (Atom "b")), (Up (Atom "a"))])],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "b"), (W [(Atom "c"), (Up (Atom "d")), (Up (Atom "a"))])],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(W [(Up (Atom "b")), (Atom "d")]), (Atom "c"), (Atom "a")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(C [(Atom "c"), (W [(Up (Up (Atom "d"))), (Atom "a")])]), (Atom "b")],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(C [(Atom "c"), (Up (Atom "a"))]), (Atom "d"), (Atom "b")],
  W [(C [(Up (Atom "a")), (Up (Atom "b"))]), (C [(Atom "d"), (Up (Atom "c"))])],
  W [(Atom "b"), (Atom "c"), (C [(Atom "a"), (Up (Atom "d"))])],
  W [(W [(Atom "b"), (Up (Atom "a"))]), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "a"), (Atom "b"), (C [(Atom "c"), (Atom "d")])],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (C [(Atom "b"), (Up (Atom "a"))]), (Atom "c")],
  W [(Atom "a"), (C [(Atom "d"), (Atom "c")]), (Atom "b")],
  W [(Atom "c"), (W [(Atom "a"), (Atom "d"), (Atom "b")])],
  W [(Atom "a"), (W [(Atom "c"), (Up (Atom "d")), (Atom "b")])],
  W [(Atom "b"), (Atom "d"), (Atom "c"), (Atom "a")],
  W [(Atom "c"), (W [(Up (Atom "d")), (Atom "a")]), (Atom "b")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(W [(Up (Atom "a")), (Atom "b")]), (W [(Atom "d"), (Atom "c")])],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(W [(Atom "c"), (Atom "b")]), (C [(Up (Atom "d")), (Atom "a")])],
  W [(C [(Atom "b"), (Up (Atom "a"))]), (W [(Atom "c"), (Atom "d")])],
  W [(C [(Atom "c"), (Atom "a")]), (Atom "d"), (Atom "b")],
  W [(W [(C [(Up (Up (Atom "c"))), (Up (Up (Atom "b")))]), (Up (Atom "d"))]), (Atom "a")],
  W [(W [(Up (Atom "d")), (Atom "b")]), (W [(Up (Atom "a")), (Atom "c")])],
  W [(Atom "c"), (Atom "b"), (C [(Atom "d"), (Up (Atom "a"))])],
  W [(Atom "a"), (W [(Atom "b"), (Atom "d")]), (Atom "c")],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(C [(Atom "a"), (Up (Atom "b"))]), (C [(Atom "d"), (Atom "c")])],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(C [(Atom "b"), (Atom "a")]), (Atom "d"), (Atom "c")],
  W [(C [(Atom "b"), (Up (Atom "a"))]), (C [(Up (Atom "d")), (Atom "c")])],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(C [(Atom "b"), (Atom "a")]), (W [(Up (Atom "d")), (Atom "c")])],
  W [(W [(Atom "b"), (Atom "c")]), (Atom "d"), (Atom "a")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(W [(Up (Atom "d")), (Atom "a")]), (Atom "b"), (Atom "c")],
  W [(Atom "b"), (Atom "a"), (C [(Up (Atom "d")), (Atom "c")])],
  W [(W [(Atom "d"), (Atom "a")]), (C [(Atom "c"), (Atom "b")])],
  W [(Atom "b"), (Atom "c"), (W [(Up (Atom "d")), (Atom "a")])],
  W [(W [(Atom "a"), (Up (Atom "c"))]), (W [(Atom "b"), (Atom "d")])],
  W [(Atom "b"), (C [(Atom "c"), (Up (Atom "d")), (Up (Atom "a"))])],
  W [(C [(Up (Atom "b")), (Up (Atom "d"))]), (Atom "a"), (Atom "c")],
  W [(W [(W [(Atom "a"), (Up (Atom "c"))]), (Atom "b")]), (Atom "d")],
  W [(Atom "c"), (W [(Atom "d"), (Up (Atom "b"))]), (Atom "a")],
  W [(W [(Atom "a"), (Atom "c")]), (C [(Up (Atom "d")), (Atom "b")])],
  W [(C [(Atom "c"), (Up (Atom "a"))]), (W [(Up (Atom "d")), (Atom "b")])],
  W [(W [(Up (Atom "c")), (Atom "d")]), (C [(Up (Atom "b")), (Atom "a")])],
  W [(Atom "b"), (W [(Up (Atom "c")), (Atom "a"), (Atom "d")])],
  W [(C [(C [(Atom "c"), (Up (Up (Atom "b")))]), (Up (Atom "d"))]), (Atom "a")],
  W [(Atom "c"), (C [(Up (Atom "b")), (Atom "d")]), (Atom "a")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(C [(Up (Atom "d")), (Up (Atom "c"))]), (Atom "a"), (Atom "b")],
  W [(W [(Up (Atom "d")), (Up (Atom "c"))]), (Atom "a"), (Atom "b")],
  W [(W [(Up (Atom "d")), (Atom "b")]), (Atom "a"), (Atom "c")],
  W [(W [(Atom "c"), (Atom "d")]), (C [(Up (Atom "b")), (Atom "a")])],
  W [(Atom "b"), (Atom "d"), (Atom "c"), (Atom "a")],
  W [(W [(Atom "a"), (Atom "b")]), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(C [(Atom "a"), (Atom "b")]), (W [(Up (Atom "c")), (Atom "d")])],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(Atom "a"), (C [(Atom "b"), (Atom "d"), (Atom "c")])],
  W [(C [(Atom "b"), (Up (Atom "d"))]), (C [(Up (Atom "a")), (Up (Atom "c"))])],
  W [(W [(Atom "d"), (W [(Up (Up (Atom "c"))), (Atom "a")])]), (Atom "b")],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(C [(Atom "a"), (Atom "d")]), (C [(Up (Atom "b")), (Atom "c")])],
  W [(W [(Up (Atom "b")), (Atom "c")]), (Atom "a"), (Atom "d")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(W [(Atom "c"), (Atom "b")]), (C [(Up (Atom "a")), (Up (Atom "d"))])],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(W [(Atom "c"), (Atom "b")]), (C [(Up (Atom "d")), (Atom "a")])],
  W [(Atom "a"), (Atom "d"), (W [(Atom "b"), (Atom "c")])],
  W [(W [(Atom "b"), (Atom "d")]), (Atom "a"), (Atom "c")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(C [(Up (Atom "c")), (Atom "a")]), (Atom "d"), (Atom "b")],
  W [(Atom "b"), (Atom "c"), (C [(Atom "a"), (Up (Atom "d"))])],
  W [(Atom "b"), (Atom "a"), (W [(Atom "c"), (Atom "d")])],
  W [(C [(Atom "c"), (Up (Atom "a")), (Atom "b")]), (Atom "d")],
  W [(Atom "d"), (C [(Atom "a"), (Atom "c")]), (Atom "b")],
  W [(Atom "a"), (C [(Atom "b"), (C [(Atom "d"), (Up (Up (Atom "c")))])])],
  W [(C [(Atom "a"), (Atom "d")]), (C [(Up (Atom "b")), (Up (Atom "c"))])],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(Atom "c"), (W [(C [(Up (Up (Atom "d"))), (Up (Atom "b"))]), (Atom "a")])],
  W [(W [(Atom "c"), (Atom "b")]), (Atom "a"), (Atom "d")],
  W [(C [(Atom "c"), (Up (Atom "d"))]), (C [(Up (Atom "b")), (Up (Atom "a"))])],
  W [(W [(Atom "c"), (Up (Atom "a")), (Atom "b")]), (Atom "d")],
  W [(Atom "c"), (Atom "a"), (C [(Up (Atom "d")), (Up (Atom "b"))])],
  W [(W [(Atom "b"), (Atom "d")]), (W [(Atom "a"), (Up (Atom "c"))])],
  W [(W [(Atom "d"), (C [(Up (Up (Atom "b"))), (Up (Up (Atom "c")))])]), (Atom "a")],
  W [(Atom "d"), (C [(Up (Atom "c")), (Atom "b")]), (Atom "a")],
  W [(Atom "c"), (W [(Atom "d"), (Atom "a"), (Atom "b")])],
  W [(W [(W [(Atom "d"), (Up (Atom "b"))]), (Atom "a")]), (Atom "c")],
  W [(W [(Up (Atom "d")), (Atom "a")]), (W [(Atom "c"), (Atom "b")])],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(C [(Atom "a"), (Atom "d")]), (Atom "c"), (Atom "b")],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(W [(Atom "c"), (Atom "d"), (Atom "a")]), (Atom "b")],
  W [(W [(Up (Atom "a")), (Up (Atom "d"))]), (Atom "b"), (Atom "c")],
  W [(Atom "b"), (W [(Atom "a"), (Atom "d")]), (Atom "c")],
  W [(C [(Up (Atom "d")), (Atom "b")]), (Atom "c"), (Atom "a")],
  W [(Atom "d"), (Atom "c"), (W [(Atom "b"), (Atom "a")])],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(W [(Atom "b"), (Atom "c")]), (C [(Atom "a"), (Up (Atom "d"))])],
  W [(Atom "a"), (Atom "c"), (W [(Up (Atom "d")), (Atom "b")])],
  W [(W [(C [(Atom "a"), (Atom "d")]), (Atom "c")]), (Atom "b")],
  W [(Atom "d"), (Atom "c"), (C [(Up (Atom "b")), (Atom "a")])],
  W [(C [(Atom "a"), (Atom "c")]), (W [(Atom "d"), (Atom "b")])],
  W [(Atom "d"), (W [(Atom "c"), (Atom "b")]), (Atom "a")],
  W [(Atom "c"), (W [(Atom "d"), (Atom "a")]), (Atom "b")],
  W [(Atom "b"), (W [(Atom "a"), (Atom "d")]), (Atom "c")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "d"), (W [(Up (Atom "b")), (Atom "c"), (Atom "a")])],
  W [(Atom "c"), (C [(Atom "d"), (C [(Up (Up (Atom "b"))), (Up (Up (Atom "a")))])])],
  W [(Atom "b"), (C [(Up (Atom "a")), (Atom "c"), (Atom "d")])],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(Atom "d"), (Atom "b"), (W [(Atom "a"), (Atom "c")])],
  W [(W [(Atom "c"), (Up (Atom "d"))]), (W [(Atom "b"), (Atom "a")])],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "c"), (Up (Atom "a"))]), (Atom "b")],
  W [(Atom "c"), (Atom "d"), (C [(Atom "a"), (Up (Atom "b"))])],
  W [(Atom "c"), (C [(Up (Atom "b")), (Atom "a")]), (Atom "d")],
  W [(Atom "c"), (W [(Atom "d"), (Atom "a")]), (Atom "b")],
  W [(Atom "b"), (W [(Up (Atom "c")), (Atom "a")]), (Atom "d")],
  W [(Atom "d"), (W [(Up (Atom "b")), (Atom "a")]), (Atom "c")],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(Atom "d"), (W [(Atom "b"), (Atom "a"), (Atom "c")])],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(C [(Atom "a"), (Atom "b")]), (Atom "d"), (Atom "c")],
  W [(C [(Up (Atom "c")), (Atom "a")]), (Atom "b"), (Atom "d")],
  W [(Atom "b"), (W [(C [(Atom "d"), (Up (Atom "c"))]), (Atom "a")])],
  W [(W [(Atom "a"), (Atom "c")]), (W [(Up (Atom "b")), (Atom "d")])],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(C [(Atom "d"), (Atom "b")]), (W [(Atom "a"), (Up (Atom "c"))])],
  W [(Atom "c"), (C [(Up (Atom "d")), (Atom "b")]), (Atom "a")],
  W [(Atom "d"), (C [(Up (Atom "c")), (Atom "a"), (Atom "b")])],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(Atom "d"), (C [(W [(Atom "b"), (Up (Up (Atom "c")))]), (Atom "a")])],
  W [(C [(Atom "a"), (Up (Atom "b"))]), (Atom "d"), (Atom "c")],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(Atom "b"), (Atom "d"), (C [(Atom "c"), (Up (Atom "a"))])],
  W [(Atom "c"), (C [(Up (Atom "a")), (Up (Atom "b")), (Up (Atom "d"))])],
  W [(Atom "b"), (Atom "d"), (C [(Up (Atom "c")), (Up (Atom "a"))])],
  W [(Atom "a"), (Atom "c"), (C [(Up (Atom "d")), (Atom "b")])],
  W [(Atom "c"), (C [(Atom "a"), (Atom "b"), (Up (Atom "d"))])],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(C [(C [(Up (Up (Atom "d"))), (Atom "c")]), (Atom "a")]), (Atom "b")],
  W [(C [(Atom "d"), (Up (Atom "c"))]), (C [(Atom "b"), (Atom "a")])],
  W [(W [(Up (Atom "d")), (Atom "a")]), (Atom "b"), (Atom "c")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(W [(Up (Atom "a")), (Atom "b")]), (C [(Atom "c"), (Atom "d")])],
  W [(W [(Atom "a"), (Atom "b")]), (C [(Atom "c"), (Up (Atom "d"))])],
  W [(C [(Atom "a"), (Atom "b")]), (C [(Atom "c"), (Up (Atom "d"))])],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(C [(Atom "c"), (Atom "d")]), (Atom "b"), (Atom "a")],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(C [(Up (Atom "a")), (Up (Atom "b"))]), (Atom "c"), (Atom "d")],
  W [(C [(Atom "d"), (Atom "c"), (Up (Atom "a"))]), (Atom "b")],
  W [(C [(Up (Atom "d")), (C [(Up (Up (Atom "b"))), (Up (Up (Atom "a")))])]), (Atom "c")],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(W [(Atom "d"), (Atom "c")]), (C [(Atom "a"), (Up (Atom "b"))])],
  W [(Atom "b"), (Atom "d"), (Atom "c"), (Atom "a")],
  W [(C [(Up (Atom "d")), (Atom "b")]), (Atom "c"), (Atom "a")],
  W [(Atom "d"), (C [(Atom "b"), (C [(Up (Up (Atom "c"))), (Up (Up (Atom "a")))])])],
  W [(C [(Up (Atom "d")), (Atom "a"), (Atom "b")]), (Atom "c")],
  W [(W [(Atom "d"), (Atom "a")]), (W [(Atom "c"), (Atom "b")])],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (C [(Up (Atom "c")), (Atom "a")]), (Atom "d")],
  W [(W [(W [(Up (Up (Atom "a"))), (Atom "b")]), (Up (Atom "c"))]), (Atom "d")],
  W [(Atom "c"), (W [(Up (Atom "a")), (Atom "d")]), (Atom "b")],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(C [(Atom "b"), (Atom "c")]), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (Atom "b"), (C [(Atom "c"), (Atom "d")])],
  W [(C [(W [(Atom "c"), (Atom "b")]), (Up (Atom "a"))]), (Atom "d")],
  W [(C [(Atom "a"), (Atom "b"), (Atom "d")]), (Atom "c")],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(W [(Atom "b"), (Atom "d")]), (C [(Atom "a"), (Atom "c")])],
  W [(Atom "d"), (Atom "c"), (C [(Up (Atom "a")), (Up (Atom "b"))])],
  W [(W [(Up (Atom "c")), (Atom "a")]), (Atom "d"), (Atom "b")],
  W [(C [(Atom "a"), (Atom "c")]), (Atom "d"), (Atom "b")],
  W [(Atom "d"), (Atom "c"), (C [(Up (Atom "b")), (Atom "a")])],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(W [(Atom "d"), (Atom "c")]), (C [(Up (Atom "a")), (Up (Atom "b"))])],
  W [(Atom "c"), (Atom "b"), (C [(Atom "d"), (Atom "a")])],
  W [(Atom "d"), (Atom "c"), (Atom "b"), (Atom "a")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(Atom "c"), (C [(Up (Atom "d")), (Atom "b"), (Up (Atom "a"))])],
  W [(Atom "d"), (Atom "b"), (W [(Atom "c"), (Atom "a")])],
  W [(W [(Up (Atom "c")), (Atom "b")]), (Atom "d"), (Atom "a")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(Atom "d"), (W [(Atom "c"), (Atom "a"), (Atom "b")])],
  W [(W [(Atom "b"), (Up (Atom "d"))]), (W [(Atom "c"), (Atom "a")])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "d"), (W [(Atom "c"), (Atom "b"), (Atom "a")])],
  W [(W [(Up (Atom "c")), (Atom "d")]), (W [(Atom "b"), (Atom "a")])],
  W [(Atom "d"), (Atom "a"), (W [(Atom "c"), (Atom "b")])],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "c"), (W [(Atom "b"), (Atom "a")]), (Atom "d")],
  W [(W [(Atom "a"), (Atom "b")]), (W [(Atom "c"), (Atom "d")])],
  W [(Atom "c"), (W [(W [(Atom "b"), (Atom "d")]), (Atom "a")])],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(C [(W [(Atom "a"), (Up (Up (Atom "d")))]), (Up (Atom "b"))]), (Atom "c")],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(Atom "d"), (W [(Atom "b"), (Atom "c")]), (Atom "a")],
  W [(W [(Up (Atom "b")), (Atom "c")]), (Atom "d"), (Atom "a")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(W [(Atom "d"), (Atom "a")]), (W [(Up (Atom "c")), (Atom "b")])],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(Atom "d"), (Atom "c"), (C [(Atom "b"), (Atom "a")])],
  W [(W [(Atom "c"), (Up (Atom "d"))]), (W [(Atom "b"), (Atom "a")])],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (Atom "c"), (W [(Atom "a"), (Atom "b")])],
  W [(C [(Atom "a"), (Atom "d")]), (C [(Up (Atom "c")), (Up (Atom "b"))])],
  W [(Atom "a"), (W [(Up (Atom "d")), (Atom "c")]), (Atom "b")],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(W [(Up (Atom "b")), (Atom "a")]), (W [(Atom "c"), (Atom "d")])],
  W [(Atom "a"), (C [(Atom "d"), (Up (Atom "c"))]), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(W [(C [(Atom "a"), (Atom "b")]), (Up (Atom "c"))]), (Atom "d")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(Atom "d"), (Atom "b"), (C [(Atom "a"), (Atom "c")])],
  W [(Atom "c"), (C [(Atom "d"), (Atom "a"), (Atom "b")])],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (Atom "a"), (C [(Up (Atom "c")), (Up (Atom "b"))])],
  W [(Atom "c"), (W [(Atom "b"), (Up (Atom "a"))]), (Atom "d")],
  W [(W [(Atom "b"), (Up (Atom "d"))]), (Atom "c"), (Atom "a")],
  W [(C [(Up (Atom "b")), (Atom "c")]), (W [(Up (Atom "a")), (Atom "d")])],
  W [(Atom "d"), (W [(Atom "c"), (Up (Atom "a"))]), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (Atom "a"), (Atom "d")],
  W [(Atom "a"), (C [(Atom "b"), (Atom "c")]), (Atom "d")],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(Atom "d"), (C [(Up (Atom "b")), (Atom "c")]), (Atom "a")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(Atom "d"), (W [(Atom "b"), (Atom "c"), (Up (Atom "a"))])],
  W [(Atom "b"), (Atom "d"), (W [(Atom "a"), (Atom "c")])],
  W [(Atom "b"), (C [(Atom "d"), (Up (Atom "c")), (Up (Atom "a"))])],
  W [(Atom "d"), (Atom "b"), (C [(Up (Atom "c")), (Up (Atom "a"))])],
  W [(W [(W [(Up (Atom "b")), (Up (Atom "a"))]), (Atom "c")]), (Atom "d")],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(C [(Atom "d"), (Up (Atom "b"))]), (C [(Up (Atom "c")), (Up (Atom "a"))])],
  W [(C [(Atom "a"), (Up (Atom "d"))]), (C [(Atom "b"), (Up (Atom "c"))])],
  W [(C [(Up (Atom "a")), (Up (Atom "c"))]), (Atom "d"), (Atom "b")],
  W [(C [(Atom "d"), (Up (Atom "a"))]), (Atom "c"), (Atom "b")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (Atom "c"), (C [(Up (Atom "b")), (Atom "a")])],
  W [(Atom "c"), (Atom "a"), (W [(Atom "b"), (Up (Atom "d"))])],
  W [(C [(Up (Atom "b")), (Atom "a")]), (C [(Up (Atom "d")), (Atom "c")])],
  W [(C [(Atom "c"), (Up (Atom "a"))]), (W [(Atom "b"), (Up (Atom "d"))])],
  W [(C [(Up (Atom "b")), (Up (Atom "a"))]), (C [(Up (Atom "c")), (Atom "d")])],
  W [(Atom "d"), (C [(Atom "b"), (Atom "c"), (Atom "a")])],
  W [(Atom "d"), (Atom "b"), (W [(Up (Atom "c")), (Atom "a")])],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (Atom "c"), (Atom "b"), (Atom "a")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(W [(Atom "d"), (Atom "c")]), (C [(Up (Atom "b")), (Up (Atom "a"))])],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(C [(Up (Atom "b")), (Atom "c")]), (W [(Atom "d"), (Atom "a")])],
  W [(W [(Atom "a"), (Atom "d")]), (C [(Atom "c"), (Atom "b")])],
  W [(Atom "a"), (W [(Up (Atom "d")), (C [(Atom "c"), (Atom "b")])])],
  W [(Atom "a"), (Atom "c"), (C [(Up (Atom "d")), (Atom "b")])],
  W [(Atom "d"), (W [(Up (Atom "a")), (Atom "c"), (Atom "b")])],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "b"), (C [(Atom "a"), (Atom "c"), (Atom "d")])],
  W [(Atom "c"), (W [(Up (Atom "a")), (Atom "d")]), (Atom "b")],
  W [(Atom "c"), (W [(Atom "b"), (Atom "a"), (Up (Atom "d"))])],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(C [(Up (Atom "b")), (Up (Atom "a")), (Atom "c")]), (Atom "d")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(W [(Up (Atom "d")), (Up (Atom "a")), (Up (Atom "b"))]), (Atom "c")],
  W [(Atom "a"), (Atom "b"), (C [(Up (Atom "d")), (Up (Atom "c"))])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "a"), (Atom "b")]), (Atom "c")],
  W [(Atom "c"), (W [(Atom "a"), (Atom "d"), (Atom "b")])],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(W [(Up (Atom "d")), (Atom "b")]), (Atom "a"), (Atom "c")],
  W [(Atom "c"), (W [(Atom "a"), (Atom "b")]), (Atom "d")],
  W [(C [(Atom "b"), (C [(Up (Up (Atom "d"))), (Up (Up (Atom "c")))])]), (Atom "a")],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(C [(Atom "c"), (Atom "d")]), (Atom "a"), (Atom "b")],
  W [(Atom "b"), (C [(Up (Atom "a")), (Atom "d")]), (Atom "c")],
  W [(Atom "c"), (C [(Atom "d"), (Up (Atom "b"))]), (Atom "a")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(W [(Atom "d"), (Up (Atom "b"))]), (Atom "c"), (Atom "a")],
  W [(Atom "c"), (Atom "b"), (C [(Atom "d"), (Up (Atom "a"))])],
  W [(Atom "c"), (C [(Up (Atom "a")), (Atom "b")]), (Atom "d")],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(Atom "b"), (Atom "c"), (C [(Up (Atom "d")), (Up (Atom "a"))])],
  W [(Atom "c"), (Atom "a"), (W [(Atom "b"), (Atom "d")])],
  W [(Atom "c"), (Atom "b"), (W [(Atom "a"), (Atom "d")])],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(Atom "b"), (Atom "d"), (W [(Atom "a"), (Atom "c")])],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(C [(Up (Atom "a")), (Up (Atom "b"))]), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (W [(Up (Atom "c")), (C [(Up (Up (Atom "a"))), (Up (Atom "b"))])])],
  W [(W [(Atom "c"), (Atom "a")]), (W [(Atom "d"), (Atom "b")])],
  W [(W [(Atom "a"), (Atom "d")]), (Atom "b"), (Atom "c")],
  W [(Atom "d"), (Atom "c"), (Atom "b"), (Atom "a")],
  W [(C [(Up (Atom "c")), (Up (Atom "b"))]), (W [(Up (Atom "a")), (Atom "d")])],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(Atom "a"), (W [(Up (Atom "d")), (Up (Atom "b"))]), (Atom "c")],
  W [(Atom "a"), (W [(Atom "b"), (Atom "c")]), (Atom "d")],
  W [(Atom "a"), (Atom "b"), (W [(Atom "c"), (Up (Atom "d"))])],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(Atom "d"), (C [(Atom "b"), (Atom "a")]), (Atom "c")],
  W [(C [(Atom "a"), (Atom "b")]), (Atom "d"), (Atom "c")],
  W [(Atom "c"), (Atom "d"), (W [(Up (Atom "b")), (Atom "a")])],
  W [(C [(Atom "d"), (W [(Atom "a"), (Atom "b")])]), (Atom "c")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "a"), (Atom "b"), (Atom "c")])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (Atom "a"), (W [(Atom "c"), (Atom "b")])],
  W [(Atom "d"), (Atom "a"), (W [(Atom "b"), (Up (Atom "c"))])],
  W [(Atom "b"), (Atom "d"), (C [(Up (Atom "a")), (Atom "c")])],
  W [(W [(Atom "c"), (Up (Atom "d"))]), (Atom "a"), (Atom "b")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(C [(Up (Atom "d")), (Atom "b")]), (Atom "c"), (Atom "a")],
  W [(Atom "a"), (C [(Atom "d"), (Up (Atom "c")), (Atom "b")])],
  W [(W [(Atom "b"), (Atom "a")]), (Atom "c"), (Atom "d")],
  W [(C [(Atom "c"), (W [(Atom "b"), (Up (Up (Atom "a")))])]), (Atom "d")],
  W [(C [(Up (Atom "c")), (Atom "a")]), (Atom "d"), (Atom "b")],
  W [(Atom "d"), (W [(Up (Atom "b")), (Atom "a")]), (Atom "c")],
  W [(Atom "c"), (Atom "b"), (W [(Atom "a"), (Atom "d")])],
  W [(W [(Atom "d"), (Up (Atom "a"))]), (C [(Up (Atom "b")), (Up (Atom "c"))])],
  W [(W [(Up (Atom "b")), (Atom "c")]), (C [(Atom "a"), (Up (Atom "d"))])],
  W [(Atom "d"), (Atom "c"), (W [(Atom "b"), (Atom "a")])],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "b"), (Up (Atom "a"))]), (Atom "c")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (C [(C [(Atom "c"), (Up (Up (Atom "b")))]), (Atom "d")])],
  W [(C [(Up (Atom "d")), (Up (Atom "a"))]), (C [(Up (Atom "b")), (Atom "c")])],
  W [(Atom "c"), (W [(Atom "b"), (Atom "d")]), (Atom "a")],
  W [(W [(Atom "b"), (Atom "c"), (Atom "d")]), (Atom "a")],
  W [(Atom "a"), (W [(Up (Atom "c")), (W [(Atom "d"), (Up (Up (Atom "b")))])])],
  W [(Atom "d"), (C [(Atom "b"), (Atom "a")]), (Atom "c")],
  W [(W [(Atom "c"), (Up (Atom "a"))]), (W [(Atom "d"), (Atom "b")])],
  W [(C [(Atom "b"), (Up (Atom "c"))]), (C [(Atom "a"), (Up (Atom "d"))])],
  W [(C [(Up (Atom "c")), (Up (Atom "b"))]), (C [(Up (Atom "d")), (Atom "a")])],
  W [(W [(Atom "a"), (Atom "d")]), (C [(Up (Atom "c")), (Atom "b")])],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(C [(Up (Atom "d")), (Atom "c")]), (W [(Atom "b"), (Up (Atom "a"))])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(W [(Atom "c"), (Atom "d")]), (W [(Atom "a"), (Up (Atom "b"))])],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(C [(Atom "b"), (Atom "d")]), (C [(Up (Atom "c")), (Up (Atom "a"))])],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "b"), (Atom "a"), (Atom "c")])],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(Atom "a"), (C [(Atom "b"), (Up (Atom "d"))]), (Atom "c")],
  W [(Atom "a"), (Atom "b"), (C [(Atom "d"), (Atom "c")])],
  W [(C [(Up (Atom "c")), (Up (Atom "d"))]), (C [(Atom "a"), (Up (Atom "b"))])],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(Atom "d"), (C [(W [(Atom "a"), (Atom "b")]), (Up (Atom "c"))])],
  W [(C [(Up (Atom "c")), (Atom "a"), (Atom "b")]), (Atom "d")],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(W [(Atom "c"), (Up (Atom "d"))]), (Atom "b"), (Atom "a")],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(W [(Atom "a"), (Atom "b"), (Atom "c")]), (Atom "d")],
  W [(Atom "a"), (C [(Up (Atom "c")), (Up (Atom "d"))]), (Atom "b")],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(C [(C [(Up (Up (Atom "d"))), (Up (Up (Atom "b")))]), (Atom "a")]), (Atom "c")],
  W [(Atom "a"), (C [(Up (Atom "c")), (Atom "d")]), (Atom "b")],
  W [(W [(Atom "d"), (C [(Up (Atom "a")), (Atom "c")])]), (Atom "b")],
  W [(C [(Up (Atom "d")), (Atom "b")]), (Atom "a"), (Atom "c")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(Atom "a"), (W [(Up (Atom "c")), (Atom "b")]), (Atom "d")],
  W [(W [(Atom "b"), (Atom "a")]), (Atom "d"), (Atom "c")],
  W [(C [(Atom "a"), (Atom "c"), (Atom "b")]), (Atom "d")],
  W [(Atom "d"), (C [(Atom "a"), (Atom "c")]), (Atom "b")],
  W [(W [(Atom "d"), (Up (Atom "a"))]), (C [(Up (Atom "c")), (Up (Atom "b"))])],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(W [(Atom "a"), (Atom "b")]), (W [(Atom "c"), (Atom "d")])],
  W [(C [(Atom "b"), (Atom "c")]), (Atom "a"), (Atom "d")],
  W [(W [(Atom "d"), (Up (Atom "b"))]), (C [(Up (Atom "c")), (Up (Atom "a"))])],
  W [(W [(Atom "b"), (Atom "c"), (Atom "d")]), (Atom "a")],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(C [(Up (Atom "c")), (Atom "b")]), (W [(Atom "d"), (Atom "a")])],
  W [(Atom "a"), (C [(Atom "b"), (Up (Atom "d"))]), (Atom "c")],
  W [(W [(Atom "b"), (Atom "a")]), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(Atom "a"), (Atom "c"), (C [(Up (Atom "b")), (Up (Atom "d"))])],
  W [(W [(Up (Atom "a")), (Atom "b")]), (C [(Up (Atom "d")), (Atom "c")])],
  W [(C [(Up (Atom "a")), (Atom "b")]), (Atom "c"), (Atom "d")],
  W [(Atom "a"), (C [(Up (Atom "b")), (Atom "c"), (Atom "d")])],
  W [(W [(Atom "b"), (Atom "a")]), (W [(Atom "d"), (Atom "c")])],
  W [(Atom "d"), (W [(Up (Atom "c")), (Up (Atom "b")), (Atom "a")])],
  W [(W [(Atom "c"), (W [(Atom "a"), (Atom "d")])]), (Atom "b")],
  W [(C [(Atom "a"), (Up (Atom "d"))]), (C [(Up (Atom "c")), (Up (Atom "b"))])],
  W [(Atom "a"), (W [(Up (Atom "c")), (W [(Atom "d"), (Up (Atom "b"))])])],
  W [(Atom "a"), (Atom "d"), (W [(Up (Atom "c")), (Up (Atom "b"))])],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (Atom "b"), (W [(Atom "a"), (Atom "c")])],
  W [(Atom "c"), (Atom "b"), (W [(Atom "a"), (Atom "d")])],
  W [(C [(Atom "b"), (W [(Atom "c"), (Atom "d")])]), (Atom "a")],
  W [(Atom "b"), (W [(Atom "c"), (Atom "a")]), (Atom "d")],
  W [(Atom "d"), (Atom "c"), (W [(Up (Atom "a")), (Up (Atom "b"))])],
  W [(Atom "b"), (Atom "c"), (C [(Up (Atom "d")), (Atom "a")])],
  W [(W [(Atom "a"), (Up (Atom "d"))]), (C [(Atom "c"), (Atom "b")])],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "a"), (Atom "b")]), (Atom "c")],
  W [(Atom "c"), (Atom "a"), (W [(Atom "b"), (Up (Atom "d"))])],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(W [(Atom "a"), (W [(Atom "b"), (Atom "d")])]), (Atom "c")],
  W [(C [(Up (Atom "b")), (Atom "c")]), (Atom "a"), (Atom "d")],
  W [(Atom "a"), (Atom "c"), (W [(Atom "b"), (Atom "d")])],
  W [(Atom "d"), (Atom "c"), (C [(Up (Atom "a")), (Up (Atom "b"))])],
  W [(C [(Up (Atom "d")), (Up (Atom "a")), (Atom "b")]), (Atom "c")],
  W [(C [(Up (Atom "a")), (Up (Atom "b"))]), (Atom "d"), (Atom "c")],
  W [(Atom "a"), (Atom "c"), (C [(Atom "d"), (Up (Atom "b"))])],
  W [(Atom "b"), (C [(Atom "c"), (Up (Atom "d"))]), (Atom "a")],
  W [(Atom "c"), (Atom "b"), (Atom "a"), (Atom "d")],
  W [(Atom "b"), (Atom "c"), (C [(Atom "d"), (Up (Atom "a"))])],
  W [(W [(Up (Atom "a")), (Atom "d")]), (W [(Atom "c"), (Atom "b")])],
  W [(W [(Atom "c"), (Atom "a")]), (C [(Atom "b"), (Up (Atom "d"))])],
  W [(W [(Atom "a"), (Atom "c")]), (W [(Atom "d"), (Atom "b")])],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "b"), (Atom "c"), (W [(Atom "d"), (Atom "a")])],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(C [(Up (Atom "c")), (W [(Atom "d"), (Atom "a")])]), (Atom "b")],
  W [(Atom "d"), (W [(C [(Up (Up (Atom "c"))), (Atom "b")]), (Atom "a")])],
  W [(C [(Atom "b"), (Up (Atom "a"))]), (Atom "c"), (Atom "d")],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(W [(Up (Atom "d")), (Up (Atom "c"))]), (C [(Atom "a"), (Up (Atom "b"))])],
  W [(C [(Up (Atom "a")), (Up (Atom "c"))]), (Atom "d"), (Atom "b")],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(Atom "c"), (Atom "b"), (Atom "a"), (Atom "d")],
  W [(W [(W [(Atom "c"), (Up (Up (Atom "a")))]), (Atom "d")]), (Atom "b")],
  W [(Atom "d"), (C [(Up (Atom "a")), (Atom "c")]), (Atom "b")],
  W [(Atom "c"), (W [(Up (Atom "b")), (W [(Atom "a"), (Atom "d")])])],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(Atom "d"), (Atom "c"), (C [(Atom "b"), (Atom "a")])],
  W [(C [(Up (Atom "b")), (Up (Atom "d"))]), (C [(Atom "a"), (Atom "c")])],
  W [(C [(Up (Atom "b")), (Up (Atom "a"))]), (Atom "d"), (Atom "c")],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (C [(Atom "a"), (Atom "d")])],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(Atom "d"), (C [(Up (Atom "b")), (Up (Atom "a"))]), (Atom "c")],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(Atom "d"), (Atom "a"), (C [(Atom "c"), (Up (Atom "b"))])],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(W [(Atom "d"), (Atom "a")]), (Atom "c"), (Atom "b")],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(W [(Atom "c"), (C [(Atom "b"), (Up (Up (Atom "a")))])]), (Atom "d")],
  W [(C [(Up (Atom "b")), (Atom "d")]), (Atom "a"), (Atom "c")],
  W [(W [(Atom "a"), (Atom "d")]), (Atom "c"), (Atom "b")],
  W [(C [(Up (Atom "b")), (Atom "a")]), (Atom "c"), (Atom "d")],
  W [(W [(Atom "a"), (Atom "c")]), (Atom "b"), (Atom "d")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (C [(Up (Atom "a")), (Atom "c")]), (Atom "d")],
  W [(Atom "c"), (Atom "d"), (C [(Up (Atom "b")), (Up (Atom "a"))])],
  W [(C [(Up (Atom "a")), (Atom "d")]), (W [(Up (Atom "b")), (Atom "c")])],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(Atom "b"), (Atom "c"), (C [(Atom "d"), (Atom "a")])],
  W [(C [(Up (Atom "a")), (Atom "b"), (Atom "c")]), (Atom "d")],
  W [(Atom "b"), (Atom "a"), (W [(Atom "d"), (Up (Atom "c"))])],
  W [(C [(Atom "a"), (Atom "b")]), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (W [(Atom "d"), (Atom "a"), (Atom "c")])],
  W [(C [(Atom "b"), (Up (Atom "c"))]), (Atom "d"), (Atom "a")],
  W [(Atom "d"), (W [(Atom "a"), (Up (Atom "c")), (Up (Atom "b"))])],
  W [(Atom "a"), (Atom "c"), (C [(Up (Atom "b")), (Atom "d")])],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "a"), (W [(Atom "c"), (Up (Atom "d")), (Atom "b")])],
  W [(C [(W [(Atom "b"), (Atom "c")]), (Atom "a")]), (Atom "d")],
  W [(W [(Atom "c"), (Atom "d")]), (Atom "a"), (Atom "b")],
  W [(C [(Atom "a"), (Atom "c")]), (Atom "d"), (Atom "b")],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(W [(Up (Atom "a")), (Atom "d")]), (W [(Atom "b"), (Atom "c")])],
  W [(Atom "c"), (Atom "b"), (W [(Atom "a"), (Atom "d")])],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(Atom "a"), (Atom "b"), (W [(Atom "d"), (Up (Atom "c"))])],
  W [(Atom "d"), (Atom "c"), (Atom "b"), (Atom "a")],
  W [(W [(Atom "d"), (Atom "c"), (Atom "b")]), (Atom "a")],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (Atom "b"), (C [(Atom "c"), (Up (Atom "a"))])],
  W [(C [(Up (Atom "d")), (Up (Atom "c"))]), (Atom "b"), (Atom "a")],
  W [(Atom "a"), (W [(Up (Atom "b")), (C [(Up (Atom "d")), (Up (Atom "c"))])])],
  W [(W [(Atom "c"), (Up (Atom "d"))]), (Atom "a"), (Atom "b")],
  W [(Atom "d"), (W [(Atom "b"), (Up (Atom "a"))]), (Atom "c")],
  W [(C [(Up (Atom "c")), (Up (Atom "d")), (Atom "a")]), (Atom "b")],
  W [(Atom "d"), (W [(Up (Atom "a")), (Atom "b"), (Atom "c")])],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(C [(Up (Atom "c")), (W [(Atom "a"), (Atom "d")])]), (Atom "b")],
  W [(Atom "a"), (Atom "d"), (Atom "b"), (Atom "c")],
  W [(Atom "d"), (C [(Up (Atom "b")), (C [(Up (Up (Atom "c"))), (Atom "a")])])],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "a"), (Atom "d"), (W [(Up (Atom "b")), (Up (Atom "c"))])],
  W [(C [(Atom "b"), (Up (Atom "c"))]), (W [(Atom "d"), (Atom "a")])],
  W [(W [(Up (Atom "c")), (Atom "d")]), (C [(Up (Atom "a")), (Up (Atom "b"))])],
  W [(C [(Up (Atom "d")), (Up (Atom "a"))]), (C [(Atom "b"), (Atom "c")])],
  W [(C [(Atom "c"), (Atom "d")]), (Atom "a"), (Atom "b")],
  W [(Atom "d"), (Atom "c"), (C [(Up (Atom "a")), (Atom "b")])],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(C [(Atom "c"), (Atom "d")]), (Atom "a"), (Atom "b")],
  W [(C [(Atom "a"), (Up (Atom "d")), (Atom "b")]), (Atom "c")],
  W [(Atom "c"), (W [(C [(Atom "d"), (Atom "a")]), (Atom "b")])],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "b"), (W [(Atom "d"), (Atom "c"), (Up (Atom "a"))])],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(Atom "c"), (Atom "d"), (W [(Up (Atom "a")), (Atom "b")])],
  W [(Atom "b"), (W [(Up (Atom "d")), (Atom "a")]), (Atom "c")],
  W [(Atom "d"), (W [(Up (Atom "c")), (W [(Up (Atom "b")), (Up (Atom "a"))])])],
  W [(W [(Up (Atom "a")), (Atom "d"), (Atom "c")]), (Atom "b")],
  W [(W [(Atom "c"), (Atom "a")]), (W [(Atom "b"), (Up (Atom "d"))])],
  W [(Atom "c"), (W [(Up (Atom "d")), (Atom "b")]), (Atom "a")],
  W [(Atom "d"), (C [(Up (Atom "b")), (C [(Atom "a"), (Atom "c")])])],
  W [(Atom "c"), (C [(Atom "d"), (C [(Atom "b"), (Atom "a")])])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(Atom "a"), (C [(Atom "d"), (Atom "c"), (Up (Atom "b"))])],
  W [(Atom "c"), (C [(Atom "b"), (Up (Atom "d"))]), (Atom "a")],
  W [(W [(C [(Up (Atom "a")), (Up (Atom "b"))]), (Atom "d")]), (Atom "c")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "c"), (Atom "b"), (Atom "a"), (Atom "d")],
  W [(Atom "c"), (W [(Atom "b"), (Atom "a")]), (Atom "d")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(W [(Up (Atom "d")), (Atom "a")]), (C [(Up (Atom "b")), (Atom "c")])],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(Atom "a"), (Atom "b"), (C [(Up (Atom "d")), (Atom "c")])],
  W [(C [(Up (Atom "d")), (Up (Atom "c"))]), (C [(Atom "a"), (Up (Atom "b"))])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "d"), (Atom "c"), (Atom "b"), (Atom "a")],
  W [(C [(Up (Atom "c")), (Atom "d")]), (Atom "a"), (Atom "b")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(W [(Up (Atom "a")), (Up (Atom "d")), (Atom "c")]), (Atom "b")],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (Atom "c"), (C [(Up (Atom "b")), (Up (Atom "a"))])],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(Atom "d"), (C [(C [(Atom "a"), (Up (Up (Atom "b")))]), (Atom "c")])],
  W [(Atom "a"), (C [(Atom "b"), (Up (Atom "c")), (Up (Atom "d"))])],
  W [(C [(Atom "d"), (Atom "c")]), (W [(Atom "b"), (Atom "a")])],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (Atom "d"), (Atom "c"), (Atom "a")],
  W [(W [(W [(Atom "d"), (Up (Up (Atom "b")))]), (Atom "c")]), (Atom "a")],
  W [(Atom "a"), (W [(Atom "b"), (Atom "d"), (Atom "c")])],
  W [(W [(Atom "a"), (Up (Atom "c"))]), (Atom "d"), (Atom "b")],
  W [(Atom "b"), (C [(Up (Atom "a")), (Atom "c")]), (Atom "d")],
  W [(W [(Atom "a"), (Atom "b"), (Atom "c")]), (Atom "d")],
  W [(Atom "a"), (W [(Atom "d"), (Atom "c")]), (Atom "b")],
  W [(W [(Up (Atom "d")), (Atom "b")]), (W [(Atom "a"), (Up (Atom "c"))])],
  W [(Atom "c"), (Atom "b"), (Atom "a"), (Atom "d")],
  W [(Atom "b"), (C [(Up (Atom "c")), (W [(Up (Up (Atom "a"))), (Up (Up (Atom "d")))])])],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "c"), (C [(Up (Atom "d")), (Atom "b")]), (Atom "a")],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(W [(Atom "b"), (C [(Up (Up (Atom "c"))), (Up (Atom "d"))])]), (Atom "a")],
  W [(Atom "b"), (W [(Atom "d"), (Atom "c"), (Atom "a")])],
  W [(Atom "a"), (C [(Atom "b"), (Atom "d")]), (Atom "c")],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(C [(Atom "b"), (Up (Atom "a")), (Atom "d")]), (Atom "c")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "c"), (Atom "d"), (W [(Atom "b"), (Atom "a")])],
  W [(C [(Up (Atom "a")), (Atom "c")]), (Atom "b"), (Atom "d")],
  W [(W [(Atom "d"), (Up (Atom "a")), (Atom "c")]), (Atom "b")],
  W [(W [(Atom "d"), (Atom "c")]), (Atom "b"), (Atom "a")],
  W [(Atom "c"), (W [(Atom "d"), (Atom "b")]), (Atom "a")],
  W [(C [(Up (Atom "d")), (Up (Atom "a"))]), (W [(Atom "b"), (Atom "c")])],
  W [(Atom "d"), (W [(Atom "b"), (Atom "c")]), (Atom "a")],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "a"), (C [(Up (Atom "d")), (Atom "b")]), (Atom "c")],
  W [(C [(Up (Atom "b")), (Up (Atom "d"))]), (C [(Up (Atom "a")), (Atom "c")])],
  W [(Atom "d"), (Atom "c"), (Atom "b"), (Atom "a")],
  W [(Atom "a"), (W [(Up (Atom "d")), (Atom "c")]), (Atom "b")],
  W [(W [(Atom "c"), (Atom "d"), (Atom "b")]), (Atom "a")],
  W [(C [(Atom "b"), (Up (Atom "a"))]), (W [(Up (Atom "d")), (Up (Atom "c"))])],
  W [(C [(Atom "c"), (Atom "d")]), (Atom "b"), (Atom "a")],
  W [(C [(Atom "b"), (Up (Atom "c"))]), (Atom "a"), (Atom "d")],
  W [(C [(Up (Atom "d")), (Up (Atom "a"))]), (C [(Atom "b"), (Up (Atom "c"))])],
  W [(Atom "b"), (C [(Atom "c"), (C [(Atom "a"), (Up (Up (Atom "d")))])])],
  W [(C [(Up (Atom "b")), (Atom "a")]), (Atom "c"), (Atom "d")],
  W [(Atom "c"), (Atom "d"), (W [(Atom "b"), (Atom "a")])],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(Atom "d"), (W [(Atom "a"), (Atom "c")]), (Atom "b")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "a"), (C [(Up (Atom "d")), (W [(Atom "c"), (Up (Up (Atom "b")))])])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(W [(Atom "d"), (Up (Atom "c")), (Atom "a")]), (Atom "b")],
  W [(Atom "b"), (W [(Atom "c"), (Atom "d"), (Up (Atom "a"))])],
  W [(Atom "b"), (W [(Atom "a"), (Atom "c")]), (Atom "d")],
  W [(Atom "c"), (Atom "a"), (W [(Atom "b"), (Atom "d")])],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(C [(Up (Atom "c")), (Up (Atom "d"))]), (C [(Up (Atom "a")), (Atom "b")])],
  W [(Atom "b"), (Atom "c"), (C [(Up (Atom "a")), (Up (Atom "d"))])],
  W [(C [(W [(Atom "b"), (Atom "a")]), (Up (Atom "c"))]), (Atom "d")],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(Atom "c"), (W [(Atom "d"), (Up (Atom "a")), (Atom "b")])],
  W [(C [(Atom "a"), (Up (Atom "b"))]), (W [(Atom "c"), (Up (Atom "d"))])],
  W [(C [(Up (Atom "a")), (Up (Atom "b"))]), (C [(Up (Atom "c")), (Atom "d")])],
  W [(W [(Atom "d"), (Atom "b")]), (Atom "a"), (Atom "c")],
  W [(C [(Atom "a"), (Up (Atom "d"))]), (W [(Atom "b"), (Atom "c")])],
  W [(Atom "d"), (W [(Up (Atom "b")), (Atom "a")]), (Atom "c")],
  W [(C [(Atom "a"), (Atom "c")]), (Atom "b"), (Atom "d")],
  W [(Atom "c"), (Atom "b"), (C [(Up (Atom "a")), (Atom "d")])],
  W [(Atom "a"), (W [(Atom "c"), (Atom "d")]), (Atom "b")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(Atom "d"), (Atom "c"), (W [(Up (Atom "a")), (Up (Atom "b"))])],
  W [(C [(C [(Up (Up (Atom "b"))), (Atom "a")]), (Atom "c")]), (Atom "d")],
  W [(Atom "d"), (Atom "a"), (Atom "c"), (Atom "b")],
  W [(Atom "d"), (C [(Up (Atom "a")), (W [(Up (Up (Atom "b"))), (Up (Up (Atom "c")))])])],
  W [(Atom "c"), (C [(Atom "b"), (Up (Atom "d")), (Up (Atom "a"))])],
  W [(Atom "c"), (W [(Up (Atom "d")), (Atom "a")]), (Atom "b")],
  W [(W [(Atom "d"), (Up (Atom "a")), (Atom "c")]), (Atom "b")],
  W [(Atom "c"), (Atom "a"), (W [(Atom "d"), (Up (Atom "b"))])],
  W [(W [(Atom "d"), (Atom "b")]), (Atom "a"), (Atom "c")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(C [(Atom "c"), (Up (Atom "b"))]), (Atom "a"), (Atom "d")],
  W [(W [(Atom "a"), (Atom "b")]), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (Atom "a"), (Atom "b"), (Atom "c")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "a"), (C [(Atom "d"), (W [(Up (Up (Atom "b"))), (Atom "c")])])],
  W [(Atom "b"), (Atom "c"), (C [(Up (Atom "d")), (Atom "a")])],
  W [(C [(Atom "c"), (Up (Atom "a"))]), (C [(Up (Atom "b")), (Up (Atom "d"))])],
  W [(W [(Atom "b"), (Atom "c")]), (C [(Up (Atom "d")), (Atom "a")])],
  W [(W [(Up (Atom "b")), (C [(Atom "d"), (Atom "c")])]), (Atom "a")],
  W [(Atom "a"), (Atom "d"), (W [(Up (Atom "b")), (Atom "c")])],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(Atom "d"), (Atom "c"), (C [(Up (Atom "b")), (Atom "a")])],
  W [(C [(Atom "a"), (Up (Atom "b"))]), (W [(Up (Atom "d")), (Atom "c")])],
  W [(Atom "c"), (Atom "a"), (Atom "b"), (Atom "d")],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(C [(Up (Atom "a")), (Up (Atom "d"))]), (Atom "b"), (Atom "c")],
  W [(W [(Atom "d"), (Atom "a")]), (Atom "c"), (Atom "b")],
  W [(W [(Atom "c"), (Atom "d")]), (Atom "b"), (Atom "a")],
  W [(C [(Atom "d"), (Atom "c")]), (W [(Up (Atom "b")), (Atom "a")])],
  W [(W [(Up (Atom "d")), (Up (Atom "c"))]), (Atom "b"), (Atom "a")],
  W [(W [(Atom "d"), (W [(Atom "c"), (Atom "a")])]), (Atom "b")],
  W [(Atom "a"), (Atom "d"), (Atom "c"), (Atom "b")],
  W [(C [(C [(Up (Up (Atom "a"))), (Atom "c")]), (Up (Atom "b"))]), (Atom "d")],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(Atom "b"), (Atom "d"), (C [(Up (Atom "a")), (Atom "c")])],
  W [(W [(Up (Atom "d")), (Atom "b")]), (C [(Atom "a"), (Up (Atom "c"))])],
  W [(C [(Up (Atom "c")), (Up (Atom "a"))]), (W [(Atom "b"), (Atom "d")])],
  W [(W [(Atom "b"), (Up (Atom "a"))]), (C [(Up (Atom "d")), (Atom "c")])],
  W [(W [(Up (Atom "c")), (Atom "b")]), (Atom "d"), (Atom "a")],
  W [(Atom "d"), (C [(Atom "c"), (W [(Atom "a"), (Atom "b")])])],
  W [(W [(Up (Atom "d")), (Atom "b")]), (Atom "c"), (Atom "a")],
  W [(C [(Atom "c"), (Atom "d"), (Up (Atom "a"))]), (Atom "b")],
  W [(C [(Up (Atom "a")), (Up (Atom "d"))]), (C [(Up (Atom "b")), (Up (Atom "c"))])],
  W [(Atom "c"), (W [(Up (Atom "a")), (Atom "b")]), (Atom "d")],
  W [(Atom "d"), (Atom "b"), (Atom "a"), (Atom "c")],
  W [(Atom "b"), (W [(Atom "c"), (Atom "a"), (Atom "d")])],
  W [(C [(Atom "a"), (Up (Atom "c"))]), (W [(Atom "b"), (Atom "d")])],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(W [(Atom "c"), (Atom "a")]), (Atom "d"), (Atom "b")],
  W [(W [(Atom "a"), (Atom "c")]), (Atom "d"), (Atom "b")],
  W [(C [(Atom "d"), (Up (Atom "a"))]), (C [(Up (Atom "b")), (Atom "c")])],
  W [(Atom "a"), (W [(Atom "d"), (Atom "b")]), (Atom "c")],
  W [(Atom "c"), (W [(Atom "b"), (Atom "d")]), (Atom "a")],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(Atom "d"), (Atom "c"), (Atom "b"), (Atom "a")],
  W [(Atom "a"), (W [(Atom "d"), (Up (Atom "b"))]), (Atom "c")],
  W [(C [(Atom "b"), (Up (Atom "c"))]), (C [(Atom "a"), (Atom "d")])],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(Atom "b"), (W [(Atom "a"), (Atom "d"), (Atom "c")])],
  W [(Atom "c"), (Atom "d"), (Atom "b"), (Atom "a")],
  W [(Atom "a"), (C [(Atom "d"), (Up (Atom "b"))]), (Atom "c")],
  W [(Atom "b"), (Atom "a"), (Atom "c"), (Atom "d")],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(Atom "d"), (Atom "c"), (Atom "b"), (Atom "a")],
  W [(Atom "a"), (Atom "c"), (Atom "b"), (Atom "d")],
  W [(Atom "c"), (Atom "a"), (C [(Up (Atom "d")), (Atom "b")])],
  W [(W [(Atom "c"), (Up (Atom "a"))]), (Atom "b"), (Atom "d")],
  W [(Atom "c"), (Atom "d"), (C [(Up (Atom "b")), (Up (Atom "a"))])],
  W [(W [(Atom "c"), (W [(Atom "d"), (Atom "a")])]), (Atom "b")],
  W [(Atom "d"), (Atom "c"), (Atom "a"), (Atom "b")],
  W [(C [(Atom "a"), (Atom "b")]), (Atom "c"), (Atom "d")],
  W [(Atom "b"), (W [(Up (Atom "d")), (Up (Atom "c"))]), (Atom "a")],
  W [(Atom "b"), (Atom "a"), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(W [(Atom "c"), (Atom "b")]), (C [(Up (Atom "d")), (Atom "a")])],
  W [(W [(Atom "d"), (Atom "a")]), (Atom "c"), (Atom "b")],
  W [(Atom "b"), (Atom "c"), (C [(Up (Atom "a")), (Atom "d")])],
  W [(Atom "c"), (Atom "b"), (Atom "d"), (Atom "a")],
  W [(C [(C [(Atom "c"), (Up (Up (Atom "a")))]), (Atom "d")]), (Atom "b")],
  W [(W [(Up (Atom "b")), (Up (Atom "c"))]), (C [(Up (Atom "a")), (Up (Atom "d"))])],
  W [(Atom "d"), (W [(C [(Up (Up (Atom "b"))), (Up (Atom "a"))]), (Atom "c")])],
  W [(Atom "c"), (C [(Atom "d"), (Atom "a")]), (Atom "b")],
  W [(Atom "b"), (Atom "d"), (W [(Atom "c"), (Atom "a")])],
  W [(C [(Atom "b"), (Up (Atom "c"))]), (C [(Atom "d"), (Up (Atom "a"))])],
  W [(Atom "a"), (Atom "c"), (Atom "d"), (Atom "b")],
  W [(C [(Atom "b"), (Atom "d")]), (C [(Up (Atom "a")), (Atom "c")])],
  W [(Atom "c"), (C [(Up (Atom "d")), (Up (Atom "b"))]), (Atom "a")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "d"), (W [(Atom "a"), (Atom "c")]), (Atom "b")],
  W [(Atom "b"), (Atom "d"), (Atom "a"), (Atom "c")],
  W [(C [(Atom "a"), (Atom "b")]), (Atom "c"), (Atom "d")],
  W [(Atom "d"), (W [(Up (Atom "a")), (Atom "c")]), (Atom "b")],
  W [(Atom "a"), (Atom "b"), (Atom "d"), (Atom "c")],
  W [(Atom "b"), (Atom "a"), (C [(Up (Atom "c")), (Atom "d")])],
  W [(Atom "d"), (W [(Up (Atom "b")), (Atom "a"), (Atom "c")])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(W [(Up (Atom "b")), (Up (Atom "d"))]), (W [(Up (Atom "c")), (Atom "a")])],
  W [(Atom "c"), (Atom "d"), (Atom "a"), (Atom "b")],
  W [(W [(Atom "d"), (Atom "a")]), (W [(Up (Atom "b")), (Atom "c")])],
  W [(Atom "a"), (C [(Up (Atom "b")), (Atom "c")]), (Atom "d")],
  W [(Atom "b"), (C [(Up (Atom "d")), (Atom "c")]), (Atom "a")],
  W [(Atom "c"), (Atom "a"), (Atom "d"), (Atom "b")],
  W [(Atom "b"), (Atom "c"), (Atom "d"), (Atom "a")],
  W [(C [(Up (Atom "a")), (Up (Atom "d"))]), (W [(Atom "b"), (Atom "c")])],
  W [(Atom "a"), (C [(Atom "c"), (Up (Atom "b"))]), (Atom "d")],
  W [(Atom "a"), (Atom "c"), (W [(Atom "b"), (Atom "d")])],
  W [(Atom "a"), (W [(Atom "b"), (Atom "d")]), (Atom "c")],
  W [(C [(Atom "c"), (Up (Atom "d"))]), (Atom "a"), (Atom "b")],
  W [(Atom "b"), (Atom "d"), (W [(Atom "a"), (Up (Atom "c"))])],
  W [(Atom "b"), (Atom "d"), (C [(Atom "c"), (Atom "a")])],
  W [(W [(Atom "b"), (Up (Atom "d"))]), (Atom "a"), (Atom "c")],
  W [(Atom "b"), (Atom "a"), (C [(Atom "c"), (Up (Atom "d"))])],
  W [(W [(Up (Atom "a")), (Up (Atom "b"))]), (W [(Atom "c"), (Atom "d")])],
  W [(Atom "a"), (W [(Atom "b"), (Atom "d"), (Atom "c")])],
  W [(Atom "b"), (Atom "c"), (Atom "a"), (Atom "d")],
  W [(Atom "d"), (Atom "a"), (C [(Up (Atom "b")), (Up (Atom "c"))])],
  W [(Atom "d"), (Atom "b"), (Atom "c"), (Atom "a")],
  W [(W [(Up (Atom "d")), (Atom "b")]), (Atom "a"), (Atom "c")],
  W [(C [(Atom "b"), (Up (Atom "c"))]), (Atom "a"), (Atom "d")],
  W [(W [(Atom "b"), (Atom "c")]), (Atom "a"), (Atom "d")],
  W [(Atom "a"), (Atom "b"), (Atom "c"), (Atom "d")],
  W [(W [(Up (Atom "b")), (Up (Atom "c"))]), (Atom "d"), (Atom "a")]
  ]
