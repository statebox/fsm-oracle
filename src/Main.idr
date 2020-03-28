
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

-- tparsec
import Relation.Indexed
import Data.NEList

import TGraph
import GraphCat

-- base
import Data.Vect
import JSONFormat
import Language.JSON

%access public export
%default total

partial
main : IO ()
main = do
    [_,filename] <- getArgs
      | _ => putStrLn "Wrong cmdline args"
    Right content <- readFile filename
      | Left err => putStrLn ("Filesystem error: " ++ show err)
    let Just content = parse content
      | Nothing => putStrLn ("invalid JSON")
    let Just fsm = Typedefs.TermParse.deserializeJSON FSMExec
      [(Nat ** expectNat), (List (Nat, Nat) ** expectListEdges)] content
      | Nothing => putStrLn "invalid FSM termdef"
    let Right (cat ** a ** b ** m) = validateExec fsm
      | Left err => printLn (TermWrite.serializeJSON [] [] TResult (Right (toTDefErr err)))
    let v = lastStep cat a b m
    printLn (TermWrite.serializeJSON [] [] TResult (Left ()))


