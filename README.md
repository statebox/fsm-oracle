# STBS-FSM-ORACLE

A formally verified idris program that evaluates executions for finite state machines (FSM).

The program uses the input provided in `FSMSpec` (see below) to build the underlying graph of the FSM, and generates the free category on it using [idris-ct](https://github.com/statebox/idris-ct/). It then uses the initial state and path provided in the execution (call them `x` and `[x1, ... , xn]`, respectively) to evaluate the composition `idx;x1;...;xn`. It returns success or error depending if this defines a valid morphism in the free category or not.

The project uses [Typedefs](https://github.com/typedefs/typedefs) to encode types, which are serialized/deserialized in/from JSON.

## Installation

-- todo

## Usage
Just put your input in the file: ... , and run:

Idris will return a json output of the following form:

--
If the FSM is not well-defined.

-- 
If the initial state is out of range

--
If the specified execution is not valid.


## Input format

Input formats are defined in the file `Tgraph.idr`.

The input format is `FSMExec`, and is of the form 
`(FSMSpec, FSMState, FSMPath)`. It has to be encoded in JSON (further information below). It consists of three things: A specification of the FSM on which executions are run (`FSMSpec`), an initial state (`FSMState`), and a list of actions (`FSMPath`).

#### `FSMSpec`
The type of `FSMSpec` is `(Nat,List (Nat Nat))`: The FSM is specified as a pair, where the first component denotes the number of states (vertexes) of the FSM, while the second is a list of pairs of vertexes (edgelist) denoting the possible actions.

For instance, `(5,[(2,1),(4,2),(0, 3)])` specifies a FSM having `5` vertexes, enumerated `0,1,2,3,4`, and three possible actions: One going from `2` to `1`, one going from `4` to `2` and one going from `0` to `3`. 

The edgelist has to be in range as specified by the number of vertexes. As such, specifications such as `(5,[(7,1),(4,2),(0, 3)])`
or `(5,[(5,5)])` are considered invalid and will be rejected.

#### `FSMState`
The type of `FSMState` is `Nat`. This specifies an initial vertex from which the computation has to start.

The initial state has to be in range as specified by the number of vertexes in `FSMSpec`. So, for instance, `4` is a valid state for the FSM `(5,[(2,1),(4,2),(0, 3)])`, while `5` is not, and will be rejected.

#### `FSMPath`
The type of `FSMPath` is `List Nat`. It specifies a computation to evaluate.

Each number in the list as to be in range as specified by the length of the edgelist in `FSMSpec`. As such, `[1,0]` and `[0,2]` are valid paths for the FSM `(5,[(2,1),(4,2),(0, 3)])`, while `[3]` is not.

#### Examples 

The following define valid inputs:
`((5, [(1,1),(3,4),(2,1)]) , 3, [1])`
`((5, [(1,1),(1,1),(2,1)]) , 2, [2,1,0])`


The following define invalid inputs:

Invalid `FSMSpec`:
`((5, [(1,1),(5,4),(2,1)]) , 2, [2,0,1])`

Invalid `FSMState`:
`((5, [(1,1),(3,4),(2,1)]) , 6, [2,1,0])`

Invalid `FSMPath`:
`((3,[]), 1, [1])`

#### JSON Encoding

Specifications have to be encoded using JSON. The way JSON encoding is defined can be found in the file `JSONFormat.idr`.



