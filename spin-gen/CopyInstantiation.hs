{-
 - filz - a model checked I2C specification                                                                        
 - copyright (c) 2021, ETH Zurich, Systems Group        
 -
 - this program is free software: you can redistribute it and/or modify                                            
 - it under the terms of the gnu general public license as published by                                            
 - the free software foundation, either version 3 of the license, or                                               
 - (at your option) any later version.       
 -
 - this program is distributed in the hope that it will be useful,                                                 
 - but without any warranty; without even the implied warranty of                                                  
 - merchantability or fitness for a particular purpose.  see the                                                   
 - gnu general public license for more details.        
 -
 - you should have received a copy of the gnu general public license                                               
 - along with this program.  if not, see <https://www.gnu.org/licenses/>.                                          
 -}

module CopyInstantiation(copyInstantiation) where

import ParserAST
import CoreAST
import Data.Either
import Data.List
import Data.Maybe

-- safeHead :: [a] -> Maybe a
-- safeHead [] = Nothing
-- safeHead (x:xs) = Just x

procByName :: [Proc] -> String -> Either String Proc
procByName ps nm = 
    case filter (\x -> name x == nm) ps of
        [p] -> (Right p)
        _   -> (Left "Process not found")

applyReplacements  :: [(String,String)] -> Proc -> Either String Proc
applyReplacements repl tmpl =
    let 
        nmp name = case snd <$> find (\(a,b) -> a == name) repl of
            Just x -> x
            Nothing -> name

        imp :: Instr IMeta -> Instr IMeta
        imp (ICall m callName callArgs retArgs) =
            ICall m (nmp callName) callArgs retArgs
        imp x = x
    in
        Right $ instrMap imp tmpl

psForCopy :: [Proc] -> ProcCopy -> Either String Proc
psForCopy ps (ProcCopy destName ofName replacements) = 
    do
        tmpl <- procByName ps ofName 
        let tmpl' = tmpl { name = destName }
        tmpl'' <- applyReplacements replacements tmpl'
        return tmpl''
        

copyInstantiation :: ParserFile -> Either String File 
copyInstantiation (ParserFile ps pcs) =
    let 
        (errs, newps) = partitionEithers $ map (psForCopy ps) pcs   
        err = intercalate "\n" errs
     in
        if errs == [] then 
            Right (File (ps ++ newps))
        else
            Left err
