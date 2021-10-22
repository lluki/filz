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


-- Check a ParseFile for violations!
--
--
-- TODO:
-- * Add check that a yield matches the process return type!
-- * Add check that array types must be referenced as arrays
-- * A parameter can be redefined as process variable

module CheckerParse (checkParserFile) where 

import ParserAST
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Data.Either
import Data.List
import Debug.Trace
import Utils

-- Utilities 

dups :: (Eq a) => [a] -> [a]
dups [] = []
dups (x:xs) = if x `elem` xs then (x : (dups xs)) else dups xs

getCalls :: IBlock meta -> [String]
getCalls =
    let
        ext (ICall _ cn _ _) = Just cn
        ext _ = Nothing
    in
        catMaybes . blockFold ext 

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
checkProc :: ParserProc -> [String]
checkProc p =
    let
        IBlock instr = body p
        labels = getLabels (body p)
        gotoDests = getGotoDests (body p)
        calls = getCalls (body p)
        postfix s = s ++ " in process '" ++ (name p) ++ "'"
        
        -- duplicate labels
        dupLblErr lbl = "Duplicate label '" ++ lbl ++ "'"
        e1 = map dupLblErr $ dups labels

        -- goto destinations exist 
        gotoMissingErr lbl = "Goto destination not defined '" ++ lbl ++ "'"
        e2 = map gotoMissingErr $ Set.toList $
            (Set.fromList gotoDests) `Set.difference` (Set.fromList labels)

        -- variables are defined
        usedVars' = concat $ map getVarsUsed instr
        stateVars' = map varName (state p)
        paramVars' = map varName (inParam p)
        tmplVars'  = map varName (tmplParam p)
        defVars'   = stateVars' ++ paramVars' ++ tmplVars'

        nonIntTmplErr name =
            "Only int template parameters are supported '" ++ name ++ "'"
        tmplNInt = map varName $ filter (\x -> DInt /= varType x) (tmplParam p)
        e3 = map nonIntTmplErr tmplNInt 

        duplVarDefErr name = "Duplicate variable defined '" ++ name ++ "'"
        e4 = map duplVarDefErr $ dups defVars'

        stateVars = Set.fromList stateVars'
        paramVars = Set.fromList paramVars'
        tmplVars = Set.fromList tmplVars'
        usedVars = Set.fromList usedVars'

        diff = Set.difference
        union = Set.union
        vUndefErr v = "Variable used but not defined '" ++ v ++ "'"

        e5 = map vUndefErr $ Set.toList $
            usedVars `diff` (stateVars `union` paramVars `union` tmplVars)

        -- no unused variables (ok should be a warning?)
        vUnuseErr v = "State variable '" ++ v ++ "' defined but not used '"
            ++ (name p) ++ "'"
        e6 = map vUnuseErr $ Set.toList $ stateVars `diff` usedVars

        -- only generic calls
        e7 = map (\x -> "Only generic calls to 'call' allowed, but found " ++
                "call to '" ++ x ++ "'") $ filter ("call" /=) calls
    in 
        map postfix $ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7


maybeToEither :: String -> Maybe a  -> Either String a 
maybeToEither _ (Just x) = Right x
maybeToEither err (Nothing) = Left err

checkProcInst :: (ProcInst, Maybe ParserProc) -> [String]
checkProcInst ((ProcInst l _ _), Nothing) = ["Layer " ++ l ++ " not defined"]
checkProcInst ((ProcInst layer params _), (Just proc)) =
        let 
            exp_pars = length (tmplParam proc) 
            provided_pars = length params
        in
            if provided_pars == exp_pars then []
            else ["Expecting " ++ show exp_pars ++ " parameters at layer " ++
                layer ++ " but " ++ show provided_pars ++ " given."]


hasCalls :: ParserProc -> Bool
hasCalls =
    let
        isCall (ICall _ _ _ _) = True
        isCall _ = False
    in
        or . (blockFold isCall) . body

checkDev :: ParserFile -> Device -> [String]
checkDev pf dev =
    let 
        (Device dev_name is) = dev

        is' :: [(ProcInst, Maybe ParserProc)]
        is' = map (\x -> (x, getProcByName pf (pi_procname x))) is
        el1 = concat $ map checkProcInst is'

        (ParserFile ps (System layers dis)) = pf
        pfList pre = map (pre ++)
        
        -- Check last layer has no calls, but only if there is a proc defined
        -- at the last layer.
        el2gen pc =
            if hasCalls pc then
            ["Process " ++ (name pc) ++ " at highest layer must not \"call\""]
            else []
        el2 = maybe [] el2gen (safeLast layers >>= (getDevLayerProc pf dev))
    in
        pfList ("In Device " ++ dev_name ++ ": ") $ el1++el2

checkSys pf = 
    let 
        (ParserFile ps (System layers devs)) = pf
    in
        concat $ map (checkDev pf) devs
        
    

-- check inter process things (called processes are defined and types match)
checkProcs :: [ParserProc] -> [String]
checkProcs ps =
    let
        -- duplicate procs
        definedProcs = map name ps
    in
        map ("Duplicate process: " ++) $ dups definedProcs

checkParserFile :: ParserFile -> [String]
checkParserFile pf = 
    let
        (ParserFile ps _) = pf
        e1 = concat $ map checkProc ps
        e2 = checkProcs ps
        e3 = checkSys pf
    in
        e1 ++ e2 ++ e3
