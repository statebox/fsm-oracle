
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
import Language.JSON
import Language.JSON.Data

%access public export
%default total

listPairToJSON : List (Nat, Nat) -> JSON
listPairToJSON xs = JArray $ map
  (\(a, b) => JObject [("input", JNumber $ cast a), ("output", JNumber $ cast b)]) xs

expectNat : JSON -> Maybe Nat
expectNat (JNumber n) = if n < 0 then Nothing
                                 else Just $ Prelude.toNat {a=Int} $ cast n
expectNat _ = Nothing

expectPair : JSON -> Maybe (Nat, Nat)
expectPair (JObject [("input", a),("output", b)])= [| MkPair (expectNat a) (expectNat b) |]
expectPair _ = Nothing

expectListPair : JSON -> Maybe (List (Nat, Nat))
expectListPair (JArray ls) = traverse expectPair ls
expectListPair _ = Nothing

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
            [(Nat ** expectNat), (List (Nat, Nat) ** expectListPair)] content
            | Nothing => putStrLn "invalid FSM termdef"
          let Right (cat ** a ** b ** m) = validateExec fsm
            | Left err => putStrLn "fail" -- printLn (TermWrite.serializeJSON [] [] TFSMErr (toTDefErr err))
          let v = lastStep cat a b m
          putStrLn "FSM is valid"

