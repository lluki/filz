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
 - Instantiated AST. No more devices, just processes
 -}

module InstAST(module InstAST, module CoreAST) where

import CoreAST

data InstProc = InstProc { name :: String
                 , inParam :: [VarDecl]
                 , outParam :: [DType]
                 , state :: [VarDecl]
                 , body :: IBlock IMeta}
    deriving (Eq,Ord,Show)

-- LayerInfo is a low to high ordered list of tuples. Each tuple contains
-- the layer name as well as the processes to be run on this layer
type LayerInfo = [(String, [String])]

data InstFile = InstFile [InstProc] LayerInfo
    deriving (Eq,Ord,Show)

machineFilter :: (InstProc -> Bool) -> InstFile -> InstFile
machineFilter f (InstFile ps li) = InstFile (filter f ps) li

instrMap :: (Instr IMeta -> Instr IMeta) -> InstProc -> InstProc
instrMap fn proc =
    let
        iMap i = case i of 
            (IYield _ _) -> fn i
            (IAssign _ _ _) -> fn i
            (ILabel _ _) -> fn i
            (IGoto _ _) -> fn i
            (ICall _ _ _ _) -> fn i
            (IAssert _ _) -> fn i
            (IIf a b blk1 blk2) -> IIf a b (blockMap blk1) (blockMap blk2)
            (IWhile a b blk) -> IWhile a b (blockMap blk)

        blockMap (IBlock is) = IBlock $ map iMap is
    in
        proc { body = blockMap (body proc) }


