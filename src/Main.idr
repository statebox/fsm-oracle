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

module Main

-- idris-ct
import Basic.Category
import Graph.Graph
import Graph.Path
import Basic.Functor
import Discrete.DiscreteCategory

-- typedefs
import Typedefs.Typedefs
import Typedefs.TermParse
import Typedefs.TermWrite

import TGraph
import GraphCat

-- base
import Data.Vect
import JSONFormat
import Language.JSON

%access public export
%default total

checkFSM : String -> FSMCheck ()
checkFSM fileContent = do
    content <- maybe (Left JSONError) Right (parse fileContent)
    fsm <- maybe (Left InvalidFSM) Right (Typedefs.TermParse.deserializeJSON FSMExec
      [ (Nat ** expectNat)
      , (List (Nat, Nat) ** expectListEdges)
      , (List Nat ** expectListNat)
      ]
      content)
    (cat ** a ** b ** m) <- validateExec fsm
    let v = lastStep cat a b m
    pure ()


toTDef : FSMCheck () -> Ty [] TResult
toTDef (Left err) = Right (toTDefErr err)
toTDef (Right r) = Left r

partial
main : IO ()
main = do
    [_,filename] <- getArgs
      | _ => putStrLn "Usage: fsm-oracle FILE"
    content <-  (readFile filename)
    let asFSMCheck = either (const (Left FSError)) Right content
    let checkedFSM = asFSMCheck >>= checkFSM
    printLn (TermWrite.serializeJSON [] [] TResult (toTDef checkedFSM))


