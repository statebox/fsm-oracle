# Statebox's FSM-Oracle

A formally verified idris program that evaluates executions for finite state machines (FSM) and Petri nets.

The program uses the input provided to build the underlying (hyper)graph of a FSM (Petri net), and generates the (monoidal) free category on it using [idris-ct](https://github.com/statebox/idris-ct/). It then uses the initial state and path provided in the execution (call them `x` and `[x1, ... , xn]`, respectively) to evaluate the composition `idx;x1;...;xn`. It returns success or error depending if this defines a valid morphism in the (monoidal) free category or not.

The project uses [Typedefs](https://github.com/typedefs/typedefs) to encode types, which are serialized/deserialized in/from JSON.

## Installation

We use `elba` to download dependencies and compile the binary, just type:

```
$ elba install
```

This will install the binary in elba's binary folder. Typically `~/.elba/bin` if this folder is in your path you can simply call `fsm-oracle` to test it out.

You can find elba and instructions on how to install it on the [official repository](https://github.com/elba/elba).

## Usage

To evaluate a Petri net, just put your input (as specified below) in a file, for example `input.JSON`, and run:

```
fsm-oracle -p input.json
```

If instead you want to evaluate a FSM, run:

```
fsm-oracle --fsm input.json
```


If the execution is valid, Idris will return a json output of the following form:

```javascript
{
"_0": {}
}
```

If the execution produces an error, the output will be:
```javascript
{
  "_1": {
    "inn" : {
      "_x": {}
    }
  }
}
```

Where `x` denotes an error code according to the following table:

|Error Code|Description|
|---|---|
|`0`| The Petri/FSM specification is invalid.   |
|`1`| The Petri/FSM initial state is invalid.   |
|`2`| The Petri/FSM path is invalid.   |
|`3`|Input cannot be parsed as JSON.   |
|`4`|Filesystem error: File cannot be read.   |

## Input format

Input has to be fed as JSON, and is converted to Idris terms and types through the use of [Typedefs](https://github.com/typedefs/typedefs). The Idris types for Petri net executions are defined in the file `PetriFormat.idr`, while the ones for the FSM case are defined in `FSMFormat.idr`.


### Petri net execution format documentation

The internal input format is a term of type `PetriExec`, and is a record consisting of  a three things: A  term of type `PetriSpec k`, one of type
`PetriPath (Places Spec) k` and one of type `PetriState Spec`.

#### `PetriSpec k`
Internally, the type of `PetriSpec k` depends on a natural number `k`. It is a record consisting of `Places`, of type `Nat`, and `Edges`, of type `Vect k (List (Fin Places), List (Fin Places))`. `Places` enumerates the number of places in the net, while `Edges` consists of `k` pairs `(List (Fin Places), List (Fin Places))`. Each pair represents an edge, with the first component listing its input places, and the second component listing its output places.

A specification is passed to the oracle using lists of pairs. For instance, `(5,[([2,1],[1]),([4],[2,0]),([0], [1,2,3])])` specifies a Petri net of type  `PetriSpec 3`  having:
- `5` vertexes, enumerated `0,1,2,3,4`
- `3` transitions: One going from `2,1` to `1`, one going from `4` to `2,0` and one going from `0` to `1,2,3`. You can denote transitions that produce more than
  one token in the same place by just repeating the token itself, as in `([4], [2,2,0])`.

The `k` parameter is automatically inferred at runtime by parsing the length of the edgelist. The edgelist given at runtime has to be in range as specified by the number of vertexes. Failing to do so produces a type mismatch. As such, a specification such as  `(5,[([5,1],[1]),([4],[2,0]),([0], [1,2,3])])`  is invalid (input of the first transition is not in range), and will produce an error.

#### `PetriState`
The type of `PetriState` is `List (Fin (Places spec))`, with `spec` having type `PetriSpec k` for some `k`. This specifies an initial list of places from which the computation has to start.

Again, the initial state specified in the input has to be in range as specified by the number of vertexes in `PetriSpec`. So, for instance, `[4,2,0]` is a valid state for the FSM `(5,[(2,1),(4,2),(0, 3)])`, while `[5]` is not, and will produce an error.

#### `PetriPath`
An execution for a Petri net is of type `Tree (Fin places) (Fin k)`, where `places` and `k` are the number of places and transitions given in a specification. A path consists in a tree indexed by two natural numbers `o` and `m`
```
data Tree o m = Tensor (Tree o m) (Tree o m)
              | Sequence (Tree o m) (Tree o m)
              | Sym o o
              | Id o
              | Mor m
```

#### Examples

The following define valid inputs:
```
((5, [(1,1),(3,4),(2,1)]) , 3, [1])
((5, [(1,1),(1,1),(2,1)]) , 2, [2,1,0])
```

The following define invalid inputs:

Invalid `FSMSpec`:
`((5, [(1,1),(5,4),(2,1)]) , 2, [2,0,1])`

Invalid `FSMState`:
`((5, [(1,1),(3,4),(2,1)]) , 6, [2,1,0])`

Invalid `FSMPath`:
`((3,[]), 1, [1])`

#### JSON Encoding

Terms of type `FSMSpec` as described above have to be fed as inputs, encoded in JSON format. The way JSON encoding is implemented can be found in the file `JSONFormat.idr`.

We do use the notation:

```javascript
{
  "_1":
  "_2":
  ...
  "_n":
}
```
To encode tuples, and the usual square bracket notation for lists. Pairs defining edges are encoded as:
```javascript
{
  "input":
  "output":
}
```
Where `input` and `output` specify the endpoints of the edge.

Applying these definitions recursively, any term of type `FSMExec` can be encoded. For example, the following is the JSON encoding of the input execution `((5, [(1,1),(3,4),(2,1)]) , 2, [2,0,0])`:


```javascript
{
  "_0": {
    "_0": 5,
    "_1": [
      {
       "input": 1,
       "output": 1
      },
      {
       "input": 3,
       "output": 4
      },
      {
       "input": 2,
       "output": 1
      }]
  },
  "_1": 2,
  "_2": [2, 0, 0]
}
 ```

 ### FSM net execution format documentation

The internal input format is a term of type `FSMExec`, and is of the form
`(FSMSpec, FSMState, FSMPath)`. It consists of three things: A specification of the FSM on which executions are run (`FSMSpec`), an initial state (`FSMState`), and a list of actions to evaluate (`FSMPath`).

#### `FSMSpec`
The type of `FSMSpec` is `(Nat,List (Nat Nat))`: The FSM is specified as a pair, where the first component denotes the number of states (vertexes) of the FSM, while the second is a list of pairs of vertexes (edgelist) denoting the possible actions.

For instance, `(5,[(2,1),(4,2),(0, 3)])` specifies a FSM having `5` vertexes, enumerated `0,1,2,3,4`, and three possible actions: One going from `2` to `1`, one going from `4` to `2` and one going from `0` to `3`.

The edgelist has to be in range as specified by the number of vertexes. As such, specifications such as `(5,[(7,1),(4,2),(0, 3)])`
or `(5,[(5,5)])` are considered invalid and will produce an error.

#### `FSMState`
The type of `FSMState` is `Nat`. This specifies an initial vertex from which the computation has to start.

The initial state has to be in range as specified by the number of vertexes in `FSMSpec`. So, for instance, `4` is a valid state for the FSM `(5,[(2,1),(4,2),(0, 3)])`, while `5` is not, and will produce an error.

#### `FSMPath`
The type of `FSMPath` is `List Nat`. It specifies a computation to evaluate.

Each number in the list has to be in range as specified by the length of the edgelist in `FSMSpec`. As such, `[1,0]` is a valid path for the FSM `(5,[(2,1),(4,2),(0, 3)])` (indicating to first use the action going from `4` to `2` and then the one going from `2` to `1`), while `[3]` is not.

#### Examples

The following define valid inputs:
```
((5, [(1,1),(3,4),(2,1)]) , 3, [1])
((5, [(1,1),(1,1),(2,1)]) , 2, [2,1,0])
```

The following define invalid inputs:

Invalid `FSMSpec`:
`((5, [(1,1),(5,4),(2,1)]) , 2, [2,0,1])`

Invalid `FSMState`:
`((5, [(1,1),(3,4),(2,1)]) , 6, [2,1,0])`

Invalid `FSMPath`:
`((3,[]), 1, [1])`

#### JSON Encoding

Terms of type `FSMSpec` as described above have to be fed as inputs, encoded in JSON format. The way JSON encoding is implemented can be found in the file `JSONFormat.idr`.

We do use the notation:

```javascript
{
  "_1":
  "_2":
  ...
  "_n":
}
```
To encode tuples, and the usual square bracket notation for lists. Pairs defining edges are encoded as:
```javascript
{
  "input":
  "output":
}
```
Where `input` and `output` specify the endpoints of the edge.

Applying these definitions recursively, any term of type `FSMExec` can be encoded. For example, the following is the JSON encoding of the input execution `((5, [(1,1),(3,4),(2,1)]) , 2, [2,0,0])`:


```javascript
{
  "_0": {
    "_0": 5,
    "_1": [
      {
       "input": 1,
       "output": 1
      },
      {
       "input": 3,
       "output": 4
      },
      {
       "input": 2,
       "output": 1
      }]
  },
  "_1": 2,
  "_2": [2, 0, 0]
}
 ```

### License

Unless explicitly stated otherwise all files in this repository are licensed under the GNU Affero General Public License.

Copyright © 2020 [Stichting Statebox](https://statebox.nl).
