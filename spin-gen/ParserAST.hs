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
 -  AST as defined in XP files. Additionally to the core AST 
 -}


-- ReExport all the CoreAST symbols, and also everything defined here
module ParserAST(module CoreAST, module ParserAST) where

import CoreAST

data ProcCopy = ProcCopy {
        destName :: String,
        ofName :: String,
        replacements :: [(String,String)]
    }
    

data ParserFile = ParserFile [Proc] [ProcCopy]
