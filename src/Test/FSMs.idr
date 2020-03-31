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

module Test.FSMs

import Data.Vect
import Typedefs.Typedefs
import TGraph

%access export

-- VALID
-- ((5, [(1,1),(3,4),(2,1)]) , 3, [(3,4)])
valid1 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
valid1 = ((5, [(1,1),(3,4),(2,1)]), 3, [1])

-- ((5, [(1,1),(3,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])
valid2 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
valid2 = ((5, [(1,1),(3,4),(2,1)]) , 2, [2,0,0])

-- ((3,[]), 1, [])
valid3 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
valid3 = ((3,[]), 1, [])

-- ((5, [(1,1),(5,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])
invalid1 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid1 = ((5, [(1,1),(5,4),(2,1)]) , 2, [2,0,0])

-- INVALID STATE, OUT OF RANGE
-- ((5, [(1,1),(3,4),(2,1)]) , 6, [(2,1),(1,1),(1,1)])
invalid2 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid2 = ((5, [(1,1),(3,4),(2,1)]) , 6, [2,0,0])

-- ((3,[Nat, List (Nat, Nat)]), 4, [Nat, List (Nat, Nat)])
invalid3 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid3 = ((3,[]), 4, [])

-- INVALID PATH, OUT OF RANGE
-- ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(6,1),(1,1)])
invalid4 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid4 = ((5, [(1,1),(3,4),(2,1)]) , 3, [2, 6, 0])

--  INVALID, PATH AND STATE OUT OF RANGE
-- ((3,[Nat, List (Nat, Nat)]), 1, [(1,1)])
invalid5 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid5 = ((3,[]), 1, [2])

-- PATH NOT MATCHING WITH STATE
-- ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(1,1),(1,1)])
invalid6 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid6 = ((5, [(1,1),(3,4),(2,1)]) , 3, [2,0,0])
