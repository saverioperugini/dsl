import qualified Data.Set as Set

data Dialogue = Empty
            | Single String
            | C [Dialogue]
            | Up Dialogue Integer
--            | I [String]
--            | SPE [String]
--            | SPEstar [String]
--            | SPE' [Dialogue]
--            | PFA1 [String]
--            | PFA1star [String]
--            | PFAn [String]
--            | PFAnstar [String]
--            | PE [String]
--            | PEstar [String]
            | W [Dialogue]
--            | Union Dialogue Dialogue

instance Show Dialogue where
  show Empty = "~"
  show (Single s) = s
  show (C ds) = "(C " ++ unwords (show <$> ds) ++ ")"
  show (Up d i) = "(Up " ++ show d ++ " " ++ show i ++ ")"
  show (W ds) = "(W " ++ unwords (show <$> ds) ++ ")"

-- Staging now takes a response and a stack of dialogues
stage :: String -> [Dialogue] -> Maybe [Dialogue]
stage _ [] = Nothing
stage y (Empty:rest) = stage y rest
stage y ((Single x):rest)
 | x == y    = Just rest
 | otherwise = Nothing
stage y ((C []):rest) = stage y rest
stage y ((C (d1:d2s)):rest) = stage y (d1 : C d2s : rest)
stage y ((Up d 0):rest) = stage y (d:rest)
stage y [Up d _] = Nothing
stage y ((Up d n):_:[]) = Nothing
stage y ((Up d n):d1:d2:rest) = stage y (Up d (n-1):(insert d1 d2):rest)
stage y ((W threads):rest) = help [] threads
  where help _ [] = Nothing
        help xs (z:zs) = case stage y (z : W (xs++zs) : rest) of
          Just stack -> Just stack
          Nothing    -> help (xs ++ [z]) zs

-- inserts the first dialogue into the second dialogue
-- acts like "requeueing" the dialogue after it has been suspended
insert :: Dialogue -> Dialogue -> Dialogue
insert d1 Empty = d1
insert d1 (Single _) = d1   -- this is very bad
insert d1 (C d2) = C (d1:d2)
insert d1 (W d2) = W (d1:d2)


dialogueA :: Dialogue 
dialogueA = W [
  W [
    C [Up (Single "a") 1, Single "b"],
    C [Up (Single "c") 2, Single "d"]
    ],
  Single "e",
  Single "f"
  ]
