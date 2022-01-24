import qualified Data.Set as Set

data Dialog = Empty
            | Atom String
            | I [String]
            | C [Dialog]
            | Up Dialog
--            | SPE [String]
--            | SPEstar [String]
--            | SPE' [Dialog]
--            | PFA1 [String]
--            | PFA1star [String]
--            | PFAn [String]
--            | PFAnstar [String]
--            | PE [String]
--            | PEstar [String]
            | W [Dialog]
--            | Union Dialog Dialog

instance Show Dialog where
  show Empty = "~"
  show (Atom s) = s
  show (I ss) = "(I " ++ unwords ss ++ ")"
  show (C ds) = "(C " ++ unwords (show <$> ds) ++ ")"
  show (Up d) = "(Up " ++ show d ++ ")"
  show (W ds) = "(W " ++ unwords (show <$> ds) ++ ")"

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
--simplify1 (SPE []) = Just Empty
--simplify1 (SPEstar []) = Just Empty
--simplify1 (SPE' []) = Just Empty
--simplify1 (PFA1 []) = Just Empty
--simplify1 (PFA1star []) = Just Empty
--simplify1 (PFAn []) = Just Empty
--simplify1 (PFAnstar []) = Just Empty
--simplify1 (PE []) = Just Empty
--simplify1 (PEstar []) = Just Empty
-- Rule 2: one subdialog
simplify1 (C [d]) = Just d
simplify1 (W [d]) = Just d
simplify1 (I [x]) = Just (Atom x)
--simplify1 (SPE [x]) = Just (Atom x)
--simplify1 (SPEstar [x]) = Just (Atom x)
--simplify1 (SPE' [d]) = Just d
--simplify1 (PFA1 [x]) = Just (Atom x)
--simplify1 (PFA1star [x]) = Just (Atom x)
--simplify1 (PFAn [x]) = Just (Atom x)
--simplify1 (PFAnstar [x]) = Just (Atom x)
--simplify1 (PE [x]) = Just (Atom x)
--simplify1 (PEstar [x]) = Just (Atom x)
-- Other rules
simplify1 (C ds) = case removeEmptyDialogs ds of
  Just newsubs -> Just (C newsubs)
  Nothing      -> case flattenCurries ds of
    Just newsubs -> Just (C newsubs)
    Nothing      -> C <$> simplifyL ds
--simplify1 (SPE' ds) = SPE' <$> simplifyL ds
simplify1 (W ds) = case removeEmptyDialogs ds of
  Just newsubs -> Just (W newsubs)
  Nothing      -> W <$> simplifyL ds
--simplify1 (Union d1 d2) = case simplify1 d1 of
--  Just d1' -> Just (Union d1' d2)
--  Nothing  -> case simplify1 d2 of
--    Just d2' -> Just (Union d1 d2')
--    Nothing  -> Nothing
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

type DCons = Dialog -> Dialog

type ReductionState = ([DCons], Dialog, [Response])

-- Builts a reduction state and reduces as far as possible.
-- Should always reduce to at most one state.
stage :: Dialog -> [Response] -> Maybe Dialog
stage d rs = case reduceStar [([const Empty], d, rs)] of
  [(dcons, d, [])] -> Just (foldr ($) d dcons)
  _                -> Nothing

-- Reduce as far as possible
reduceStar :: [ReductionState] -> [ReductionState]
reduceStar rs = case rs >>= reduce of
  [] -> rs
  rs' -> reduceStar rs'

-- Implements the reduction relation (~>) described in the document.
-- The non-determinism is handled with lists.
reduce :: ReductionState -> [ReductionState]
-- [empty]
reduce (f:lam, Empty, inp) = [(lam, f Empty, inp)]
-- [atom]
reduce (f:lam, Atom x, (One y):inp)
  | x == y    = [(lam, f Empty, inp)]
  | otherwise = []
-- [arrow]
reduce (f1:f2:lam, Up d, inp) = [(f2 . f1 : lam, d, inp)]
-- [C]
reduce (lam, C (d:ds), inp) = [((\d' -> simplify (C (d':ds))):lam, d, inp)]
-- [W]
reduce (lam, W ds, inp) =
  do (dcon, d) <- extractEach [] ds
     return (dcon:lam, d, inp)
  where extractEach d1 [] = []
        extractEach d1 (d:ds) = (\d' -> simplify (W (d1++[d']++ds)), d)
                              : extractEach (d1++[d]) ds
-- [I]
reduce (f:lam, I ss, (Tup rs):inp)
  | ss `setEq` rs = [(lam, f Empty, inp)]
  | otherwise     = []
reduce _ = []

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

showTriple :: ReductionState -> String
showTriple (lam, d, inp) = "(Lambda, " ++ show d ++ ", " ++ show inp ++ ")"

------------------------------------------------------
-- Tests. The result_ values should all be (Just ~) --
------------------------------------------------------
      
dialogA = W [C [Up (Atom "a"), Atom "b"], C [Atom "x", Atom "y"]]
tripleA = [([const Empty], dialogA, [One "a", One "x", One "y", One "b"])]

dialogB = W [I ["a", "b", "c"], I ["x", "y"]]
tripleB = [([const Empty], dialogB, [Tup ["x", "y"], Tup ["a", "b", "c"]])]