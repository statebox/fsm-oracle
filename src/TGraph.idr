module TGraph

-- base
import Data.Vect

-- idris-ct
import Graph.Graph
--import Graph.Path

-- typedefs
import Typedefs.Names
import Typedefs.Typedefs

%access public export
%default total

-- Base definitions

-- Defines naturals
TNat : TDefR 3
TNat = RRef 0

-- Graph definitions

||| The type definition for vertices in the graph is jsut
||| A natural enumerating the vertexes. e.g. 5 means
||| That there are 5 vertexes, denoted 0,1,2,3,4
FSMVertex : TDefR 3
FSMVertex = TNat

||| The type definition for edges in the graph is just a couple
||| of vertexes defining the edge source and target
FSMEdges : TDefR 3
FSMEdges = RRef 1

||| A Finite State Machine is defined by its vertices and a list of edges
||| The definition might not be valid if edges endpoints are out of range
FSMSpec : TDefR 3
FSMSpec = TProd [FSMVertex, FSMEdges]

||| A state is a vertex in the graph (might be out of range)
FSMState : TDefR 3
FSMState = FSMVertex

||| A path is a list of edges (might not be valid)
FSMPath : TDefR 3
FSMPath =  RRef 2-- TList `ap` [FSMEdge]

||| An execution is a FSM, a state representing an inital edge and a path from that edge.
||| The execution might not be valid.
FSMExec : TDefR 3
FSMExec = TProd [FSMSpec, FSMState, FSMPath]

||| Errors related to checking if a FSM description is valid
data FSMError =
  ||| Error in the FSM description
  InvalidFSM |
  ||| Error in the state transitions
  InvalidState |
  ||| Error in the execution path
  InvalidPath |
  ||| Error when parsing the JSON file
  JSONError |
  ||| Error when reading the file
  FSError

TFSMErr : TDefR 0
TFSMErr = TMu [("InvalidFSM", T1),
               ("InvalidState", T1),
               ("InvalidPath", T1),
               ("JSONError", T1),
               ("FSError", T1)
               ]

toTDefErr : FSMError -> Ty [] TFSMErr
toTDefErr InvalidFSM   = Inn (Left ())
toTDefErr InvalidState = Inn (Right (Left ()))
toTDefErr InvalidPath  = Inn (Right (Right (Left ())))
toTDefErr JSONError    = Inn (Right (Right (Right (Left ()))))
toTDefErr FSError      = Inn (Right (Right (Right (Right ()))))

Show FSMError where
  show InvalidFSM   = "Invalid FSM"
  show InvalidState = "Invalid state"
  show InvalidPath  = "Invalid path"
  show JSONError    = "JSON parsing error"
  show FSError      = "Filesystem error"

IdrisType : TDefR 3 -> Type
IdrisType = Ty [Nat, List (Nat, Nat), List Nat]

||| Monad to check errors when compiling FSMs
FSMCheck : Type -> Type
FSMCheck = Either FSMError

convertList : (n : Nat) -> List (Nat, Nat) -> Maybe (List (Fin n, Fin n))
convertList n edges = traverse (\(x,y) => [| MkPair (natToFin x n) (natToFin y n) |]) edges

||| Convert a list of nat into the index into the vector of edges
convertList' : (n : Nat) -> List Nat -> Maybe (List (Fin n))
convertList' n edges = traverse (\x => natToFin x n) edges

-- > record Graph vertices where
-- >   constructor MkGraph
-- >   edges : Vect n (vertices, vertices)

mkTGraph : (Nat, List (Nat, Nat)) -> Maybe (DPair Nat (\size => Graph (Fin size)))
mkTGraph (size, edges) = do convertedEdges <- convertList size edges
                            pure (size ** MkGraph $ fromList convertedEdges)
