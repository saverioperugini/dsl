import qualified Data.Map as Map
import qualified Data.Set as Set
import ArrowBackend

--- Dialogue configuration ---

initialState = SPE' [Atom "size", Atom "blend", Atom "cream"]

prompts = Map.fromList [
  ("size", "What size would you like?"),
  ("blend", "What blend would you like?"),
  ("cream", "Do you want cream?")
  ]

responses = Map.fromList [
  ("small", "size"),
  ("medium", "size"),
  ("large", "size"),
  ("mocha", "blend"),
  ("latte", "blend"),
  ("black", "blend"),
  ("yes", "cream"),
  ("no", "cream")
  ]

------------------------------

red :: String -> String
red s = "\x1B[31m" ++ s ++ "\x1B[0m"

getDialogComponent :: RS -> Dialog
getDialogComponent (RS _ d _) = d

execDialog :: RS -> IO ()
execDialog d = case getNextTask (getDialogComponent d) of
  Just t  -> case Map.lookup t prompts of
    Just prompt -> do
      putStr "[sys] "
      putStrLn prompt
      putStr "[usr] "
      usrinp <- getLine
      case Map.lookup usrinp responses of
        Just t' -> case stage (One t') d of
          Just d' -> do
            putStrLn "[sys] Ok."
            execDialog d'
          Nothing -> do
            putStrLn $ red "[sys] Error, cannot do this task at this time"
            execDialog d
        Nothing -> do
          putStrLn $ red "[sys] Error, did not recognize that response."
          execDialog d
    Nothing -> putStrLn $ red "[sys] Error, no prompt found for this task!"
  Nothing -> putStrLn "Dialogue complete!"

-- Get the task to prompt for next
getNextTask :: Dialog -> Maybe String
getNextTask Empty = Nothing
getNextTask (Atom s) = Just s
getNextTask (Up d) = getNextTask d
getNextTask (Union d1 _) = getNextTask d1
getNextTask (C (x:_)) = getNextTask x
getNextTask (W (x:_)) = getNextTask x
getNextTask (I (s:_)) = Just s
getNextTask (SPE (s:_)) = Just s
getNextTask (SPEstar (s:_)) = Just s
getNextTask (SPE' (x:_)) = getNextTask x
getNextTask (PFA1 (s:_)) = Just s
getNextTask (PFA1star (s:_)) = Just s
getNextTask (PFAn (s:_)) = Just s
getNextTask (PFAnstar (s:_)) = Just s
getNextTask (PE (s:_)) = Just s
getNextTask (PEstar (s:_)) = Just s
getNextTask _ = Nothing

main :: IO ()
main = execDialog (RS [const Empty] initialState [])