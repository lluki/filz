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

module DevInstantiation(devInstantiate) where

import ParserAST
import InstAST

import Data.Either
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Control.Lens (over)
import Debug.Trace

-----
-- Stages of process instantiation:
-------

-- Replace "call" with upper_name
pProcReplCall :: String -> InstProc -> InstProc
pProcReplCall upper_name pr =
    let
        iMap i = case i of
            (ICall m _ callArgs retArgs) -> ICall m upper_name callArgs retArgs
            _ -> i
    in  
       (instrMap iMap pr)

pProcRename :: String -> InstProc -> InstProc
pProcRename new_name p = p { InstAST.name = new_name }

pProcTmplInst :: [Integer] -> ParserProc -> InstProc
pProcTmplInst args pp =
    let
        repl :: String -> Maybe Integer
        repl x = M.lookup x $ M.fromList $ zip (map varName $ tmplParam pp) args

        aE :: AExpr -> AExpr
        aE (VRef (Var x)) = fromMaybe (VRef (Var x)) $ (Lit <$> repl x)
        aE x = x

        pp' = over (ppBlock . ibAexprs . aLeaves) aE pp
    in
    InstProc {
           InstAST.name = ParserAST.name pp'
        ,  InstAST.inParam = ParserAST.inParam pp'
        ,  InstAST.outParam = ParserAST.outParam pp'
        ,  InstAST.state = ParserAST.state pp'
        ,  InstAST.body = ParserAST.body pp'
    }
        
        
-- Given a ParserFile context, and a Device, return the instantiated
-- Procs. Instantiated means, the call statements will not contain
-- placeholder names but procname, template parameters instantiated,
-- and the correct name is assigned.
devInst :: ParserFile -> Device -> [InstProc] 
devInst pf dev =
    let
        (Device _ dev_insts) = dev
        px = getInstProcName dev 

        procByName = fromJust . getProcByName pf 
        pI (ProcInst layer proc_params proc_name) =
            let 
                higher_proc_name = 
                    fromMaybe "" $ px <$> getNextLayer pf layer
            in 
                pProcRename (px layer) . 
                pProcReplCall higher_proc_name .
                pProcTmplInst proc_params . 
                procByName $ 
                proc_name
    in
        map pI dev_insts


devInstantiate :: ParserFile -> InstFile
devInstantiate pf = 
    let
        (ParserFile _ (System layers devs)) = pf
        new_procs = concat $ map (devInst pf) devs
    
        -- layer_info
        layerToInfo x = (x, map (\(_,_,procname) -> procname) $
                            filter (\(_,layer,_) -> layer == x) $
                            getDevLayerX pf)

        layer_info = map layerToInfo layers
    in
        InstFile new_procs layer_info
