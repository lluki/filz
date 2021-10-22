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

--
-- check instantiated file 
-- test that:
-- the call signatures match
-- no unresolved calls
-- no calls in top level

module CheckerInst (checkInstFile) where 

import InstAST
import Debug.Trace
import Utils

-- Is a proc definition and a call instruction compatible?
callCompat :: (Maybe InstProc, Instr a) -> [String]
callCompat (Just p, (ICall _ cn ca cra)) =
    let
        InstProc pn pi po ps pb = p
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

checkInstFile :: InstFile -> [String]
checkInstFile (InstFile ps _) =
    let
        -- get all ICall instructions of a proc
        calls p = let IBlock ins = body p in filter isCall ins

        -- Called procs are defined
        procByName nm = safeHead $ filter (\x -> (name x) == nm) ps
        callCompatErrs p = map callCompat $
            map (\i -> (procByName (callName i), i)) (calls p)
        e2 = concat . concat $ map callCompatErrs ps 
    in 
        e2
