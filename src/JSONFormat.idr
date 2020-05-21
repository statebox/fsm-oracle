{-

SPDX-License-Identifier: AGPL-3.0-only

This file is part of `statebox/fsm-oracle`.

Copyright (C) 2020 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.

-}

module JSONFormat

import Data.Vect
import Language.JSON
import Language.JSON.Data

import TGraph

import Typedefs.Typedefs

public export
ParseError : Type -> Type
ParseError = Either String

public export
JSONParser : Type -> Type
JSONParser t = JSON -> ParseError t

export
expectNat : JSONParser Nat
expectNat (JNumber n) = if n < 0 then Left "Expected Nat"
                                 else pure $ Prelude.toNat {a=Int} $ cast n
expectNat _ = Left "Expected Nat"

expectEdges : JSONParser (Nat, Nat)
expectEdges (JObject [("input", a),("output", b)])= [| MkPair (expectNat a) (expectNat b) |]
expectEdges _ = Left "Expected List of edges"

expectList : JSONParser (List JSON)
expectList (JArray ls) = pure ls
expectList _ = Left "Expected List"

export
expectListNat : JSONParser (List Nat)
expectListNat js = expectList js >>= traverse expectNat

export
expectListEdges : JSONParser (List (Nat, Nat))
expectListEdges js = expectList js >>= traverse expectEdges

expectPair : (JSONParser a) -> (JSONParser b) -> JSONParser (a, b)
expectPair pa pb (JObject [("_0", a), ("_1", b)]) = [| MkPair (pa a) (pb b) |]
expectPair pa pb _ = Left "Expected Pair"

export
expectListListEdges : JSON -> Either String (List (List Nat, List Nat))
expectListListEdges js = expectList js >>= traverse (expectPair expectListNat expectListNat)

public export
TResult : TDefR 1
TResult = TSum [T1, TFSMErr]

