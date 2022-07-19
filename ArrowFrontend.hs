import qualified Data.Map as Map
import qualified Data.Set as Set
import ArrowBackend

--- Dialogue configuration ---

initialState = W [
  C [Up (Atom "protein"), Up (Atom "rice"), Up (Atom "beans"), Atom "side"],
  C [Atom "plant-based", Atom "lifestyle", Atom "avoiding"]
  ]

prompts = Map.fromList [
  ("protein", "What protein would you like? [steak, chicken]"),
  ("rice", "What rice would you like? [white, brown]"),
  ("beans", "What beans would you like? [black, pinto]"),
  ("side", "What side would you like? [chips, salsa, tortilla]"),
  ("plant-based", "Would you like a plant-based meal? [vegetarian, vegan, not-plant-based]"),
  ("lifestyle", "Set a lifestyle preference? [paleo, keto, no-lifestyle]"),
  ("avoiding", "Are you avoiding any ingredients? [gluten, dairy, soy, not-avoiding]")
  ]

responses = Map.fromList [
  ("steak", "protein"),
  ("chicken", "protein"),
  ("white", "rice"),
  ("brown", "rice"),
  ("black", "beans"),
  ("pinto", "beans"),
  ("chips", "side"),
  ("salsa", "side"),
  ("tortilla", "side"),
  ("vegetarian", "plant-based"),
  ("vegan", "plant-based"),
  ("not-plant-based", "plant-based"),
  ("paleo", "lifestyle"),
  ("keto", "lifestyle"),
  ("no-lifestyle", "lifestyle"),
  ("gluten", "avoiding"),
  ("dairy", "avoiding"),
  ("soy", "avoiding"),
  ("not-avoiding", "avoiding")
  ]

------------------------------

red :: String -> String
red s = "\x1B[31m" ++ s ++ "\x1B[0m"

getDialogueComponent :: RS -> Dialogue
getDialogueComponent (RS _ d _) = d

execDialogue :: RS -> IO ()
execDialogue d = case getNextTask (getDialogueComponent d) of
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
            execDialogue d'
          Nothing -> do
            putStrLn $ red "[sys] Error, cannot do this task at this time"
            execDialogue d
        Nothing -> do
          putStrLn $ red "[sys] Error, did not recognize that response."
          execDialogue d
    Nothing -> putStrLn $ red "[sys] Error, no prompt found for this task!"
  Nothing -> putStrLn "Dialogue complete!"

-- Get the task to prompt for next
getNextTask :: Dialogue -> Maybe String
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
main = execDialogue (RS [const Empty] initialState [])
