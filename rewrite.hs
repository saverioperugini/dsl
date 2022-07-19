{- rewrite.hs
 - Haskell dialogue rewrite and simplification rules.
 - Does not support uparrow notation.
 -}

import qualified Data.Set as Set
import Control.Applicative ((<|>))

--------------------------------
------ Dialogue Definition -------
--------------------------------

data Dialogue = Empty
            | Atom String
            | C [Dialogue]
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
            | Union Dialogue Dialogue

instance Show Dialogue where
  show Empty = "~"
  show (Atom s) = s
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
  show (Union d1 d2) = "(Union " ++ show d1 ++ " " ++ show d2 ++ ")"

-------------------------------------
----------- Simplification ----------
-------------------------------------

-- Completely simplify
simplify :: Dialogue -> Dialogue
simplify d = maybe d simplify (simplifySelfOrSub d)

-- Convenience function. Same as simplify, but returns a Maybe so that
-- it can be used in monadic sequence.
simplifyM :: Dialogue -> Maybe Dialogue
simplifyM = Just . simplify

simplifySelfOrSub :: Dialogue -> Maybe Dialogue
simplifySelfOrSub d = simplify1 d <|> simplifySub d

simplifySub :: Dialogue -> Maybe Dialogue
simplifySub (C ds) = C <$> simplifyFirst ds
simplifySub (SPE' ds) = SPE' <$> simplifyFirst ds
simplifySub _ = Nothing

simplifyFirst :: [Dialogue] -> Maybe [Dialogue]
simplifyFirst [] = Nothing
simplifyFirst (d:ds) =
      ((:ds) <$> simplifySelfOrSub d)
  <|> ((d:) <$> simplifyFirst ds)

-- Applies a single simplification rule
simplify1 :: Dialogue -> Maybe Dialogue
simplify1 d =
      empty1_rule d
  <|> empty2_rule d
  <|> empty3_rule d
  <|> empty4_rule d
  <|> atom1_rule d
  <|> atom2_rule d
  <|> flatten_rule d

empty1_rule :: Dialogue -> Maybe Dialogue
empty1_rule (C []) = Just Empty
empty1_rule (I []) = Just Empty
empty1_rule (SPE []) = Just Empty
empty1_rule (SPEstar []) = Just Empty
empty1_rule (SPE' []) = Just Empty
empty1_rule (PFA1 []) = Just Empty
empty1_rule (PFA1star []) = Just Empty
empty1_rule (PFAn []) = Just Empty
empty1_rule (PFAnstar []) = Just Empty
empty1_rule (PE []) = Just Empty
empty1_rule (PEstar []) = Just Empty
empty1_rule _ = Nothing

empty2_rule :: Dialogue -> Maybe Dialogue
empty2_rule d = case d of
  (C ds)    -> C <$> removeEmpty ds
  (SPE' ds) -> SPE' <$> removeEmpty ds
  _         -> Nothing
  where removeEmpty [] = Nothing
        removeEmpty (Empty:ds) = Just ds
        removeEmpty (d:ds) = (d:) <$> removeEmpty ds

empty3_rule :: Dialogue -> Maybe Dialogue
empty3_rule (Union Empty d) = Just d
empty3_rule _ = Nothing

empty4_rule :: Dialogue -> Maybe Dialogue
empty4_rule (Union d Empty) = Just d
empty4_rule _ = Nothing

atom1_rule :: Dialogue -> Maybe Dialogue
atom1_rule (C [d]) = Just d
atom1_rule (SPE' [d]) = Just d
atom1_rule _ = Nothing

atom2_rule :: Dialogue -> Maybe Dialogue
atom2_rule (I [x]) = Just (Atom x)
atom2_rule (SPE [x]) = Just (Atom x)
atom2_rule (SPEstar [x]) = Just (Atom x)
atom2_rule (PFA1 [x]) = Just (Atom x)
atom2_rule (PFA1star [x]) = Just (Atom x)
atom2_rule (PFAn [x]) = Just (Atom x)
atom2_rule (PFAnstar [x]) = Just (Atom x)
atom2_rule (PE [x]) = Just (Atom x)
atom2_rule (PEstar [x]) = Just (Atom x)
atom2_rule _ = Nothing

flatten_rule :: Dialogue -> Maybe Dialogue
flatten_rule (C ds) = C <$> flatten ds
  where flatten [] = Nothing
        flatten ((C cs):ds) = Just (cs ++ ds)
        flatten (d:ds) = (d:) <$> flatten ds
flatten_rule _ = Nothing

-------------------------------------
------------ Staging ----------------
-------------------------------------

stage :: [String] -> Dialogue -> Maybe Dialogue
stage _ Empty = Nothing
stage [] _ = Nothing
stage [y] (Atom x)
 | x == y    = Just Empty
 | otherwise = Nothing
stage _ (Atom _) = Nothing
stage x (C (d:ds)) = (C . (:ds)) <$> stage x d
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
stage ys (PFAn xs) = I <$> removePrefix xs ys
stage ys (PFAnstar xs) = PFAnstar <$> removePrefix xs ys
stage ys (PE xs)
 | ys `subsetOf` xs = Just (I (xs `setSubtract` ys))
 | otherwise        = Nothing
stage ys (PEstar xs)
 | ys `subsetOf` xs = Just (PEstar (xs `setSubtract` ys))
 | otherwise        = Nothing
stage ys (Union d1 d2) = case (stage ys d1, stage ys d2) of
  (Nothing, Nothing) -> Nothing
  (Nothing, Just d2') -> Just d2'
  (Just d1', Nothing) -> Just d1'
  (Just d1', Just d2') -> Just (Union d1' d2')

-- Stages the given response with the first dialogue it can.
-- If successful, returns (stageddialogue, otherdialogues)
stageFirstGet :: [String] -> [Dialogue] -> Maybe (Dialogue, [Dialogue])
stageFirstGet xs [] = Nothing
stageFirstGet xs (d:ds) = case stage xs d of
  Just newd -> Just (newd, ds)
  Nothing   -> do (staged, rest) <- stageFirstGet xs ds
                  return (staged, d:rest)

-- Stages the given response with the first dialogue it can
stageFirst :: [String] -> [Dialogue] -> Maybe [Dialogue]
stageFirst _ [] = Nothing
stageFirst xs (d:ds) = case stage xs d of
  Just newd -> Just (newd:ds)
  Nothing   -> (d:) <$> (stageFirst xs ds)

--------------------------------
------ Utility Functions -------
--------------------------------

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

dialogueA = C [Atom "size", Atom "blend", Atom "cream"]
resultA = Just dialogueA
  >>= stage ["size"] >>= simplifyM
  >>= stage ["blend"] >>= simplifyM
  >>= stage ["cream"] >>= simplifyM

dialogueB = C [Atom "size", I ["blend", "cream"]]
resultB = Just dialogueB
  >>= stage ["size"] >>= simplifyM
  >>= stage ["blend", "cream"] >>= simplifyM

dialogueC = PEstar ["a", "b", "c", "d"]
resultC = Just dialogueC
  >>= stage ["d", "b"] >>= simplifyM
  >>= stage ["a"] >>= simplifyM
  >>= stage ["c"] >>= simplifyM

dialogueD = SPE' [C [Atom "a", Atom "b"], I ["c", "d"]]
resultD = Just dialogueD
  >>= stage ["a"] >>= simplifyM
  >>= stage ["b"] >>= simplifyM
  >>= stage ["c", "d"] >>= simplifyM

dialogueE = Union (C [Atom "a", Atom "c", Atom "b"]) (PFAnstar ["a", "b", "c"])
resultE = Just dialogueE
  >>= stage ["a"] >>= simplifyM
  >>= stage ["b", "c"] >>= simplifyM
