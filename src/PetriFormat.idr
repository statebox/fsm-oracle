
module PetriFormat

import Typedefs.Typedefs
import Typedefs.Library
import Typedefs.Idris
import Typedefs.Names
import Data.Vect
import PetriGraph

public export
App : TDef' n b -> Vect n (TDef' m b) -> TDef' m b
App td args = TApp (TName "" td) args

public export
TEdges : TDefR 1
TEdges = App TList [TProd [TList,  TList]]

public export
TState : TDefR 1
TState = TList

public export
TPetriSpec : TDefR 1
TPetriSpec = TProd [TNat1, TEdges]

public export
convertSpec : Ty' StandardIdris [Nat] TPetriSpec -> Maybe (n ** PetriSpec n)
convertSpec (places, edges) =
    MkDPair (length edges) . MkPetriSpec places
        <$> convertList places (fromList edges)
  where
    convertList : (p : Nat) ->  (Vect n (List Nat, List Nat))
               -> Maybe (Vect n (List (Fin p), List (Fin p)))
    convertList p = traverse (\(a, b) => [| MkPair (traverse (\v => natToFin v p) a)
                                                   (traverse (\v => natToFin v p) b) |])

public export
TTree : TDefR 1
TTree = TMu
  [ ("Tensor", TProd [TVar 0, TVar 0])
  , ("Sequence", TProd [TVar 0, TVar 0])
  , ("Sym", TProd [TVar 1, TVar 1])
  , ("Id", TVar 1)
  , ("Mor", TVar 1)
  ]

-- converts from TDef to Tree
convertTree : Ty' StandardIdris [Nat] TTree -> Tree Nat Nat
convertTree (Inn (Left (a, b))) = Tensor (convertTree a) (convertTree b)
convertTree (Inn (Right (Left (a, b)))) = Sequence (convertTree a) (convertTree b)
convertTree (Inn (Right (Right (Left (a, b))))) = Sym a b
convertTree (Inn (Right (Right (Right (Left i))))) = Id i
convertTree (Inn (Right (Right (Right (Right m))))) = Mor m

-- converts from Tree to TDef
export
convertTree' : Tree Nat Nat -> Ty [Nat] TTree
convertTree' (Tensor a b) = (Inn (Left (convertTree' a, convertTree' b)))
convertTree' (Sequence a b) = (Inn (Right (Left (convertTree' a, convertTree' b))))
convertTree' (Sym a b) = (Inn (Right (Right (Left (a, b)))))
convertTree' (Id x) = (Inn (Right (Right (Right (Left x)))))
convertTree' (Mor x) = (Inn (Right (Right (Right (Right x)))))

public export
convertState : (spec : PetriSpec k) -> List Nat -> Maybe (PetriState spec)
convertState spec = traverse (\s => natToFin s (Places spec))

public export
TPetriExec : TDefR 1
TPetriExec = TProd [ TPetriSpec -- spec
                   , TState     -- initial state
                                -- /!\ the type argument is shared between Tree and List
                   , TTree      -- execution
                   ]

public export
convertExec : Ty' StandardIdris [Nat] TPetriExec -> Either String PetriExec
convertExec ((a, b), c, d) = do (k ** spec) <-  maybeToEither "indices are wrong" $ convertSpec (a , b)
                                path <- maybeToEither "illegal tree" $ checkTree spec (convertTree d)
                                state <- maybeToEither  "Illegal states" $ convertState spec c
                                pure $ MkPetriExec spec path state

