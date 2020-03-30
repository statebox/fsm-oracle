module JSONFormat

import Data.Vect
import Language.JSON
import Language.JSON.Data

import TGraph

import Typedefs.Typedefs

listPairToJSON : List (Nat, Nat) -> JSON
listPairToJSON xs = JArray $ map
  (\(a, b) => JObject [("input", JNumber $ cast a), ("output", JNumber $ cast b)]) xs

export
expectNat : JSON -> Maybe Nat
expectNat (JNumber n) = if n < 0 then Nothing
                                 else Just $ Prelude.toNat {a=Int} $ cast n
expectNat _ = Nothing

expectEdges : JSON -> Maybe (Nat, Nat)
expectEdges (JObject [("input", a),("output", b)])= [| MkPair (expectNat a) (expectNat b) |]
expectEdges _ = Nothing

expectList : JSON -> Maybe (List JSON)
expectList (JArray ls) = Just ls
expectList _ = Nothing

export
expectListNat : JSON -> Maybe (List Nat)
expectListNat js = expectList js >>= traverse expectNat

export
expectListEdges : JSON -> Maybe (List (Nat, Nat))
expectListEdges js = expectList js >>= traverse expectEdges

public export
TResult : TDefR 0
TResult = TSum [T1, TFSMErr]

