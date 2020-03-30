module Test.FSMs

import Typedefs.Typedefs
import TGraph

-- VALID
-- ((5, [(1,1),(3,4),(2,1)]) , 3, [(3,4)])
valid1 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
valid1 = fromIdrisExec ((5, [(1,1),(3,4),(2,1)]), 3, [(3,4)])

-- ((5, [(1,1),(3,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])
valid2 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
valid2 = fromIdrisExec ((5, [(1,1),(3,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])

-- ((3,[]), 1, [])
valid3 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
valid3 = fromIdrisExec ((3,[]), 1, [])

-- ((5, [(1,1),(5,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])
invalid1 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid1 = fromIdrisExec  ((5, [(1,1),(5,4),(2,1)]) , 2, [(2,1),(1,1),(1,1)])

-- INVALID STATE, OUT OF RANGE
-- ((5, [(1,1),(3,4),(2,1)]) , 6, [(2,1),(1,1),(1,1)])
invalid2 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid2 = fromIdrisExec ((5, [(1,1),(3,4),(2,1)]) , 6, [2,0,0])

-- ((3,[Nat, List (Nat, Nat)]), 4, [Nat, List (Nat, Nat)])
invalid3 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid3 = fromIdrisExec ((3,[]), 4, [])

-- INVALID PATH, OUT OF RANGE
-- ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(6,1),(1,1)])
invalid4 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid4 = fromIdrisExec  ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(6,1),(1,1)])

--  INVALID, PATH AND STATE OUT OF RANGE
-- ((3,[Nat, List (Nat, Nat)]), 1, [(1,1)])
invalid5 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid5 = fromIdrisExec  ((3,[]), 1, [(1,1)])

-- PATH NOT MATCHING WITH STATE
-- ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(1,1),(1,1)])
invalid6 : Ty [Nat, List (Nat, Nat), List Nat] FSMExec
invalid6 = fromIdrisExec  ((5, [(1,1),(3,4),(2,1)]) , 3, [(2,1),(1,1),(1,1)])
