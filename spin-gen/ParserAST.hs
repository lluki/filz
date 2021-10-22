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
{-
 -  AST as defined in XP files. Additionally to the core AST.
 -  Procs have the same datatype as in Core, but they are templates,
 -  they call an anonymous higher function (only "call" is allowed
 -  in process string).
 -}


-- ReExport all the CoreAST symbols, and also everything defined here
module ParserAST(module ParserAST, module CoreAST) where

import CoreAST
import Data.List
import Utils
import Control.Lens

data ParserProc = ParserProc { name :: String
                             , tmplParam :: [VarDecl]
                             , inParam :: [VarDecl]
                             , outParam :: [DType]
                             , state :: [VarDecl]
                             , body :: IBlock IMeta}
    deriving (Eq,Ord,Show)

ppBlock :: Traversal' ParserProc (IBlock IMeta)
ppBlock f pp =
    let
        pp' new_body = pp { body = new_body }
    in
        pp' <$> f (body pp)

data ParserFile = ParserFile [ParserProc] System
  deriving (Eq, Ord, Show)

data ProcInst = ProcInst { pi_layer :: String
                         , pi_params :: [Integer]
                         , pi_procname :: String }
  deriving (Eq, Ord, Show)

data System = System { sys_layers :: [String],
                       sys_devices :: [Device]
                     }
  deriving (Eq, Ord, Show)

data Device = Device { dev_name :: String
                     , dev_insts :: [ProcInst] }
  deriving (Eq, Ord, Show)

getProcByName :: ParserFile -> String -> Maybe ParserProc
getProcByName (ParserFile ps _) nm =
    safeHead $ filter (\x -> (name x == nm) ) ps

getNextLayer :: ParserFile -> String -> Maybe String
getNextLayer pf layer = 
    let
        (ParserFile _ (System layers _)) = pf
    in do
        idx <- layer `elemIndex` layers
        layers `safeAt` (idx+1)

getLayers :: ParserFile -> [String]
getLayers (ParserFile _ (System l _)) = l

-- Returns the name of the uninstantiated template process to be instantiated
getDevLayerProcName :: ParserFile -> Device -> String -> Maybe String
getDevLayerProcName pf (Device _ dev_insts) layer =
    let 
        matching_pis = filter (\(ProcInst l _ _ ) -> l == layer) dev_insts
    in
        pi_procname <$> safeHead matching_pis 

getDevLayerProc :: ParserFile -> Device -> String -> Maybe ParserProc
getDevLayerProc pf dev layer =
    (getDevLayerProcName pf dev layer) >>= (getProcByName pf)

-- For a device and a layer, return the name of the instantiated process
getInstProcName :: Device -> String -> String
getInstProcName (Device dev_name _) layer = dev_name ++ "_" ++ layer

                            -- devname, layer,  procname
getDevLayerX :: ParserFile -> [(String, String, String)]
getDevLayerX pf  =
   let
        (ParserFile _ (System layers devs)) = pf
        fd layer dev = 
            let 
                (Device devname insts) = dev 
            in
                [(devname, layer, getInstProcName dev layer)]
        fl layer = concat $ map (fd layer) devs
    in
        concat $ map fl layers


