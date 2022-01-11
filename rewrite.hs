{- rewrite.hs
 - Haskell dialog rewrite and simplification rules.
 - Does not support uparrow notation (the W-mnemonic
 - means subdialogs are arbitrarily interweaved)
 -}

import qualified Data.Set as Set

--------------------------------
------ Dialog Definition -------
--------------------------------

data Dialog = Empty
            | Single String
            | C [Dialog]
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
            | W [Dialog]
            | Union Dialog Dialog

instance Show Dialog where
  show Empty = "~"
  show (Single s) = s
  show (C ds) = "(C " ++ unwords (show <$> ds) ++ ")"
  show (I xs) = "(I " ++ unwords xs ++ ")"
  show (SPE xs) = "(SPE " ++ unwords xs ++ ")"
  show (SPEstar xs) = "(SPE* " ++ unwords xs ++ ")"
  show (SPE' ds) = "(SPE' " ++ unwords (show <$> ds) ++ ")"
  show (PFA1 xs) = "(PFA1 " ++ unwords xs ++ ")"
  show (PFA1star xs) = "(PFA1* " ++ unwords xs ++ ")"
  show (PFAn xs) = "(PFAn " ++ unwords xs ++ ")"
  show (PFAnstar xs) = "(PFAn* " ++ unwords xs ++ ")"
  show (PE xs) = "(PE " ++ unwords xs ++ ")"
  show (PEstar xs) = "(PE* " ++ unwords xs ++ ")"
  show (W ds) = "W " ++ unwords (show <$> ds) ++ ")"
  show (Union d1 d2) = "(Union " ++ show d1 ++ " " ++ show d2 ++ ")"

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
simplify1 (W []) = Just Empty
-- Rule 2: one subdialog
simplify1 (C [d]) = Just d
simplify1 (I [x]) = Just (Single x)
simplify1 (SPE [x]) = Just (Single x)
simplify1 (SPEstar [x]) = Just (Single x)
simplify1 (SPE' [d]) = Just d
simplify1 (PFA1 [x]) = Just (Single x)
simplify1 (PFA1star [x]) = Just (Single x)
simplify1 (PFAn [x]) = Just (Single x)
simplify1 (PFAnstar [x]) = Just (Single x)
simplify1 (PE [x]) = Just (Single x)
simplify1 (PEstar [x]) = Just (Single x)
simplify1 (W [d]) = Just d
-- Other rules
simplify1 (C ds) = case removeEmptyDialogs ds of
  Just newsubs -> Just (C newsubs)
  Nothing      -> case flattenCurries ds of
    Just newsubs -> Just (C newsubs)
    Nothing      -> C <$> simplifyL ds
simplify1 (SPE' ds) = SPE' <$> simplifyL ds
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

-------------------------------------
------------ Staging ----------------
-------------------------------------

stage :: [String] -> Dialog -> Maybe Dialog
stage _ Empty = Nothing
stage [] _ = Nothing
stage [y] (Single x)
 | x == y    = Just Empty
 | otherwise = Nothing
stage _ (Single _) = Nothing
stage x (C (d:ds)) = case stage x d of
  Just newd -> Just (C (newd:ds))
  Nothing   -> Nothing
stage _ (C []) = Nothing
stage xs (I ds) =
  if xs `setEq` ds then Just Empty else Nothing
stage [x] (SPE xs) =
  if [x] `subsetOf` xs then Just (I (setSubtract xs [x])) else Nothing
stage _ (SPE _) = Nothing
stage [x] (SPEstar xs) =
  if [x] `subsetOf` xs then Just (SPEstar (setSubtract xs [x])) else Nothing
stage xr (SPEstar xs) =
  if xr `setEq` xs then Just Empty else Nothing
stage xs (SPE' ds) =
  do (staged, rest) <- stageFirstGet xs ds
     return (C [staged, SPE' rest])
stage [y] (PFA1 (x:xs))
 | x == y    = Just (I xs)
 | otherwise = Nothing
stage _ (PFA1 _) = Nothing
stage [y] (PFA1star (x:xs))
 | x == y    = Just (PFA1star xs)
 | otherwise = Nothing
stage ys (PFA1star xs)
 | ys `setEq` xs = Just Empty
 | otherwise     = Nothing
stage ys (PFAn xs) = case removePrefix xs ys of
  Just newxs -> Just (I newxs)
  Nothing    -> Nothing
stage ys (PFAnstar xs) = case removePrefix xs ys of
  Just newxs -> Just (PFAnstar newxs)
  Nothing    -> Nothing
stage ys (PE xs)
 | ys `subsetOf` xs = Just (I (xs `setSubtract` ys))
 | otherwise        = Nothing
stage ys (PEstar xs)
 | ys `subsetOf` xs = Just (PEstar (xs `setSubtract` ys))
 | otherwise        = Nothing
stage ys (W ds) = W <$> stageFirst ys ds
stage ys (Union d1 d2) = case (stage ys d1, stage ys d2) of
  (Nothing, Nothing) -> Nothing
  (Nothing, Just d2') -> Just d2'
  (Just d1', Nothing) -> Just d1'
  (Just d1', Just d2') -> Just (Union d1' d2')

-- Stages the given response with the first dialog it can.
-- If successful, returns (stageddialog, otherdialogs)
stageFirstGet :: [String] -> [Dialog] -> Maybe (Dialog, [Dialog])
stageFirstGet xs [] = Nothing
stageFirstGet xs (d:ds) = case stage xs d of
  Just newd -> Just (newd, ds)
  Nothing   -> do (staged, rest) <- stageFirstGet xs ds
                  return (staged, d:rest)

-- Stages the given response with the first dialog it can
stageFirst :: [String] -> [Dialog] -> Maybe [Dialog]
stageFirst _ [] = Nothing
stageFirst xs (d:ds) = case stage xs d of
  Just newd -> Just (newd:ds)
  Nothing   -> (d:) <$> (stageFirst xs ds)

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

------------------------------------------------------
-- Tests. The result_ values should all be (Just ~) --
------------------------------------------------------

dialogA = C [Single "size", Single "blend", Single "cream"]
resultA = Just dialogA
  >>= stage ["size"] >>= simplifyM
  >>= stage ["blend"] >>= simplifyM
  >>= stage ["cream"] >>= simplifyM

dialogB = C [Single "size", I ["blend", "cream"]]
resultB = Just dialogB
  >>= stage ["size"] >>= simplifyM
  >>= stage ["blend", "cream"] >>= simplifyM

dialogC = PEstar ["a", "b", "c", "d"]
resultC = Just dialogC
  >>= stage ["d", "b"] >>= simplifyM
  >>= stage ["a"] >>= simplifyM
  >>= stage ["c"] >>= simplifyM

dialogD = SPE' [C [Single "a", Single "b"], I ["c", "d"]]
resultD = Just dialogD
  >>= stage ["a"] >>= simplifyM
  >>= stage ["b"] >>= simplifyM
  >>= stage ["c", "d"] >>= simplifyM

dialogE = Union (C [Single "a", Single "c", Single "b"]) (PFAnstar ["a", "b", "c"])
resultE = Just dialogE
  >>= stage ["a"] >>= simplifyM
  >>= stage ["b", "c"] >>= simplifyM
             
dialogF = W [C [Single "a", Single "b"], C [Single "c", Single "d"]]
resultF = Just dialogF
  >>= stage ["c"] >>= simplifyM
  >>= stage ["a"] >>= simplifyM
  >>= stage ["b"] >>= simplifyM
  >>= stage ["d"] >>= simplifyM

------------------------------------------------------
-- Stager Coordination
------------------------------------------------------

-- An episode is a list of utterances. An utterance is a list of strings.
type Episode = [[String]]

-- Stage an episode
stageEpisode :: Episode -> Dialog -> Maybe Dialog
stageEpisode [] d = Just d
stageEpisode (r:rs) d = stage r d >>= simplifyM >>= stageEpisode rs

------------------------------------------------------
-- Expansion
------------------------------------------------------

{-
type EnumSpec = [Episode]   -- [[[String]]]

expand :: Dialog -> EnumSpec
expand Empty = []
expand (Single x) = [[[x]]]
expand (C []) = []
expand (C [d]) = expand d
expand (C (d:ds)) = uncurry (++) <$> cartProd (expand d) (expand (C ds))
expand (I xs) = [[xs]]

cartProd :: [a] -> [b] -> [(a, b)]
cartProd _ [] = []
cartProd [] _ = []
cartProd [a] bs = (\b -> (a,b)) <$> bs
cartProd as [b] = (\a -> (a,b)) <$> as
cartProd (x:xs) (y:ys) = (x, y):((\y' -> (x,y'))<$>ys) ++ ((\x' -> (x',y))<$>xs) ++ (cartProd xs ys)
-}
