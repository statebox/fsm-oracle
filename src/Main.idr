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
import Typedefs.Idris
import Typedefs.Library

-- FSM-Oracle
import TGraph
import PetriGraph
import PetriFormat
import GraphCat
import Utils.Either

-- base
import Data.Vect
import JSONFormat
import Language.JSON

%access public export
%default total

checkFSM : JSON -> FSMCheck ()
checkFSM content = do
    fsm <- mapLeft InvalidFSM (Typedefs.TermParse.deserialise
                              StandardParsers
                              []
                              FSMExec
                              content)
    (cat ** a ** b ** m) <- validateExec fsm
    let v = lastStep cat a b m
    pure ()

checkPetri : JSON -> FSMCheck ()
checkPetri content = do
    petri' <- mapLeft InvalidFSM (Typedefs.TermParse.deserialise
                                 StandardParsers
                                 [liftParse expectNat]
                                 TPetriExec
                                 content)
    petri <- mapLeft InvalidFSM (convertExec $ petri')
    let True = isJust $ composeWithId (Spec petri) (Path petri) (State petri)
      | Left InvalidPath
    pure ()

toTDef : FSMCheck () -> Ty' StandardIdris [] TResult
toTDef (Left err) = Right (toTDefErr err)
toTDef (Right r) = Left r

data OracleMode = FSM | Petri

parseMode : String -> Maybe OracleMode
parseMode "-f" = Just FSM
parseMode "--fsm" = Just FSM
parseMode "-p" = Just Petri
parseMode "--petri" = Just Petri
parseMode _ = Nothing

printHelp : IO ()
printHelp = putStrLn "Usage: fsm-oracle [--fsm, --petri] FILE"

pickChecker : OracleMode -> JSON -> FSMCheck ()
pickChecker FSM = checkFSM
pickChecker Petri = checkPetri

partial
main : IO ()
main = do
    [_, mode, filename] <- getArgs
      | printHelp
    let (Just pmode) = parseMode mode
      | printHelp
    content <- readFile filename
    let result = do fileContent <- mapLeft (const FSError) content
                    jsonContent <- maybeToEither JSONError (parse fileContent)
                    (pickChecker pmode) jsonContent
    printLn (TermWrite.serialise StandardContext [] TResult (toTDef result))

