
module Main

-- idris-ct
import Basic.Category
import Graph.Graph
import Graph.Path
import Basic.Functor
import Discrete.DiscreteCategory

-- typedefs
import Typedefs.Typedefs
import Typedefs.TermParse
import Typedefs.TermWrite

import TGraph
import GraphCat

-- base
import Data.Vect
import JSONFormat
import Language.JSON

%access public export
%default total

checkFSM : String -> FSMCheck ()
checkFSM fileContent = do
    content <- maybe (Left JSONError) Right (parse fileContent)
    fsm <- maybe (Left InvalidFSM) Right (Typedefs.TermParse.deserializeJSON FSMExec
      [ (Nat ** expectNat)
      , (List (Nat, Nat) ** expectListEdges)
      , (List Nat ** expectListNat)
      ]
      content)
    (cat ** a ** b ** m) <- validateExec fsm
    let v = lastStep cat a b m
    pure ()


toTDef : FSMCheck () -> Ty [] TResult
toTDef (Left err) = Right (toTDefErr err)
toTDef (Right r) = Left r

partial
main : IO ()
main = do
    [_,filename] <- getArgs
      | _ => putStrLn "Usage: fsm-oracle FILE"
    content <-  (readFile filename)
    let asFSMCheck = either (const (Left FSError)) Right content
    let checkedFSM = asFSMCheck >>= checkFSM
    printLn (TermWrite.serializeJSON [] [] TResult (toTDef checkedFSM))


