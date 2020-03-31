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

