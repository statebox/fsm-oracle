module GraphCat

-- base
import Data.Vect
import Data.Fin

-- idris-ct
import Basic.Category
import Basic.Functor
import Discrete.DiscreteCategory
import Graph.PathCategory
import Graph.Graph
import Graph.Path

-- typedefs
import Typedefs.Names
import Typedefs.Typedefs

import TGraph

-- import Util.Elem

%access public export
%default total

decToEither : e -> Dec a -> Either e a
decToEither e (No _) = Left e
decToEither _ (Yes a) = Right a

constructNEPath : (g : Graph (Fin n)) -> (path : List ((Fin n), (Fin n))) -> {auto ok : NonEmpty path} ->
                FSMCheck (Path g (Basics.fst $ List.head path) (Basics.snd $ List.last path))
constructNEPath g [(x, y)] = do el <- decToEither InvalidPath $ isElem (x,y) (edges g)
                                pure [el]
constructNEPath g ((x, y) :: (y',z) :: pt) with (decEq y y')
  constructNEPath g ((x, y) :: (y,z) :: pt) | Yes Refl =
    do el <- decToEither InvalidPath $ isElem (x,y) (edges g)
       path <- assert_total $ constructNEPath g ((y,z)::pt)
       pure $ el :: path
  constructNEPath g ((x, y) :: (y',z) :: pt) | No ctra = Left InvalidPath

validateExec : Ty [Nat, List (Nat, Nat)] FSMExec -> FSMCheck (cat : Category ** a : obj cat ** b : obj cat ** mor cat a b)
validateExec (spec, state, path) =
  do -- convert into a graph with `n` being the number of states
     (n**g) <- maybe (Left InvalidFSM) Right $ mkTGraph $ fromFSMSpecToEdgeList spec
     -- get the inital state as a fin
     st <- maybe (Left InvalidState) Right $ natToFin (state) n
     -- Convert the edge list into fins
     edgeList <- maybe (Left InvalidPath) Right $ convertList n $ fromFSMPathToEdgeList path
     case nonEmpty edgeList of
       -- if the path is not valid we need to check the initial state is the first state of the path
       Yes nel => case decEq (fst $ head edgeList) st of
                    Yes _ => do path' <- constructNEPath g edgeList
                                pure (pathCategory g ** (fst $ head edgeList) ** (snd $ last edgeList) ** path')
                    No _ => Left InvalidPath
       -- empty path is always valid
       No _ => pure (pathCategory g ** st  ** st ** [])

-- Next refactoring : We'll have to pass the entire graph
mkFunctor : (cat : Category) -> CFunctor cat (discreteCategory ())
mkFunctor (MkCategory _ _ _ _ _ _ _) = MkCFunctor
  (\_ => ())
  (\_, _, _ => Refl)
  (\_ => Refl)              -- Refl = Refl
  (\_, _, _, _, _ => Refl)  -- Refl = Refl

lastStep : (cat : Category) -> (a, b : obj cat) -> (m : mor cat a b)
       -> mor (discreteCategory ()) (mapObj (mkFunctor cat) a) (mapObj (mkFunctor cat) b)
lastStep (MkCategory _ _ _ _ _ _ _) a b m = Refl

IdrisExec : Type
IdrisExec = ((Nat, List (Nat, Nat)), Nat, List (Nat, Nat))

fromIdrisExec : IdrisExec -> Ty [Nat, List (Nat, Nat)] FSMExec
fromIdrisExec ((states, trans), init, path) =
  ( ( states
    ,  trans)
  , init
  , path
  )