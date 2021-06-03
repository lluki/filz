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

-- TODO:
-- * Add check that a yield matches the process return type!
-- * Add check that array types must be referenced as arrays
-- * A parameter can be redefined as process variable

module Checker (check_file) where 

import CoreAST
import Data.Maybe (catMaybes)
import qualified Data.Set as Set

-- Utilities 

dups :: (Eq a) => [a] -> [a]
dups [] = []
dups (x:xs) = if x `elem` xs then (x : (dups xs)) else dups xs

getLabels :: IBlock meta -> [String]
getLabels =
    let
        ext (ILabel _ x) = Just x
        ext _ = Nothing
    in
        catMaybes . blockFold ext 

getGotoDests :: IBlock meta -> [String]
getGotoDests =
    let
        ext (IGoto _ s) = Just s 
        ext _ = Nothing
    in 
        catMaybes . blockFold ext 

isCall :: Instr a -> Bool
isCall (ICall _ _ _ _) = True
isCall _ = False

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:xs) = Just x

getAExpVarsUsed :: AExpr -> [String]
getAExpVarsUsed =
    let
        fn (VRef (Var x)) = Just x
        fn (VRef (ArrVar x _)) = Just x
        fn _ = Nothing
    in
        catMaybes . aExprFold fn


getBExpVarsUsed :: BExpr -> [String]
getBExpVarsUsed =
    let
        bfn _ = Nothing
        afn (VRef (Var x)) = Just x
        afn (VRef (ArrVar x _)) = Just x
        afn _ = Nothing
    in
        catMaybes . bExprFold bfn afn 

getBlockVarsUsed :: IBlock a -> [String]
getBlockVarsUsed = concat . blockFold getVarsUsed 

getVarsUsed :: Instr a -> [String]
getVarsUsed (IYield _ e) = concat $ map getAExpVarsUsed e
getVarsUsed (IAssign _ s e) = [varRefName s] ++ (getAExpVarsUsed e)
getVarsUsed (IIf _ be bl1 bl2) =
    (getBExpVarsUsed be) ++ (getBlockVarsUsed bl1) ++ (getBlockVarsUsed bl2) 
getVarsUsed (IWhile _ be bl) = (getBExpVarsUsed be) ++ (getBlockVarsUsed bl)
getVarsUsed (ILabel _ _) = []
getVarsUsed (IGoto _ _) =  []
getVarsUsed (ICall _ _ ca ra) = (concat $ map getAExpVarsUsed ca) ++ ra
getVarsUsed (IAssert _ _) = []


-- check within the process
checkProc :: Proc -> [String]
checkProc p = let
        IBlock instr = body p
        labels = getLabels (body p)
        gotoDests = getGotoDests (body p)
        postfix s = s ++ " in process '" ++ (name p) ++ "'"
        
        -- duplicate labels
        dupLblErr lbl = "Duplicate label '" ++ lbl ++ "'"
        e1 = map dupLblErr $ dups labels

        -- goto destinations exist 
        gotoMissingErr lbl = "Goto destination not defined '" ++ lbl ++ "'"
        e2 = map gotoMissingErr $ Set.toList $
            (Set.fromList gotoDests) `Set.difference` (Set.fromList labels)

        -- variables are defined
        usedVars = Set.fromList $ concat $ map getVarsUsed instr
        stateVars = Set.fromList $ map varName (state p)
        paramVars = Set.fromList $ map varName (inParam p)
        diff = Set.difference
        union = Set.union
        vUndefErr v = "Variable used but not defined '" ++ v ++ "'"

        e3 = map vUndefErr $ Set.toList $
            usedVars `diff` (stateVars `union` paramVars)

        -- no unused variables (ok should be a warning?)
        vUnusedErr v = "Variable defined but not used '" ++ (name p) ++ "'"
        e4 = map vUndefErr $ Set.toList $ stateVars `diff` usedVars
    in 
        map postfix $ e1 ++ e2 ++ e3 ++ e4

-- Is a proc definition and a call instruction compatible?
callCompat :: (Maybe Proc, Instr a) -> [String]
callCompat (Just p, (ICall _ cn ca cra)) =
    let
        Proc pn pi po ps pb = p
        pi_len = length pi
        ca_len = length ca
        e1 = if pi_len /= ca_len then
            ["In call of " ++ pn ++ ". Expected "
            ++ (show pi_len) ++ " arguments, but " ++ (show ca_len) ++ " given."]
            else
            []

        cra_len = length cra
        po_len = length po
        e2 = if cra_len /= po_len then
            ["In call of " ++ pn ++ ". Expected " ++ (show po_len) ++
             " return arguments, but " ++ (show cra_len) ++ " given."]
            else
            []
    in
        e1 ++ e2

callCompat (Nothing, (ICall _ cn _ _)) = ["Process " ++ cn ++ " called but not defined"]
callCompat (Just p, _) = error "Called callCompat with not-ICall Instr" 
    

-- check inter process things (called processes are defined and types match)
checkProcs :: [Proc] -> [String]
checkProcs ps = let
        definedProcs = map name ps
        
        -- get all ICall instructions of a proc
        calls p = let IBlock ins = body p in filter isCall ins

        procByName nm = safeHead $ filter (\x -> (name x) == nm) ps
        callCompatErrs p = map callCompat $
            map (\i -> (procByName (callName i), i)) (calls p)
    
        -- Called procs are defined
        e2 = concat . concat $ map callCompatErrs ps 

        -- Duplicate definitions
        e1 = map ("Duplicate process: " ++) $ dups definedProcs
        
    in
        e1 ++ e2

check_file :: File -> [String]
check_file (File ps) = 
    let
        e1 = concat $ map checkProc ps
        e2 = checkProcs ps
    in
        e1 ++ e2
