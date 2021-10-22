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
import DevInstantiation
import Data.List
import ParserAST
import Parser
import Text.Pretty.Simple
import qualified Data.Text.IO as Codec
import Text.Megaparsec (errorBundlePretty)
import CheckerParse (checkParserFile)

-- snip snap from pprint output
expectedPF = ParserFile 
    [ ParserProc 
        { name = "NCtrl" 
        , inParam = []
        , outParam = [ DInt ]
        , tmplParam = []
        , state = 
            [ VarDecl 
                { varName = "data" 
                , varType = DInt
                } 
            ]
        , body = IBlock 
            [ ICall 
                { m = 0
                , callName = "call" 
                , callArgs = []
                , retArgs = [ "data" ]
                } 
            ]
        } 
    , ParserProc 
        { name = "ElCtrl" 
        , inParam = []
        , outParam = []
        , tmplParam = []
        , state = 
            [ VarDecl 
                { varName = "data" 
                , varType = DInt
                } 
            ]
        , body = IBlock 
            [ ICall 
                { m = 0
                , callName = "call" 
                , callArgs = []
                , retArgs = [ "data" ]
                } 
            ]
        } 
    ] 
    ( System 
        { sys_layers = 
            [ "Bus" 
            , "Nibble" 
            ] 
        , sys_devices = 
            [ Device 
                { dev_name = "Ctrl" 
                , dev_insts = 
                    [ ProcInst 
                        { pi_layer = "Nibble" 
                        , pi_params = []
                        , pi_procname = "NCtrl" 
                        } 
                    , ProcInst 
                        { pi_layer = "Bus" 
                        , pi_params = []
                        , pi_procname = "ElCtrl" 
                        } 
                    ] 
                } 
            ]
        } 
    )
-- Done snip snap
    
parseParserFile :: FilePath -> IO ParserFile
parseParserFile fp = do
    inp <- Codec.readFile fp
    case runFileParser fp inp of
        Left s -> error (errorBundlePretty s)
        Right sys -> return sys

pp = pPrintNoColor
main = do
    actualPF <- parseParserFile "test.xp" 
    if actualPF /= expectedPF then do
        putStrLn "Parser output does not match expecation"
        putStrLn "Expected\n====="
        pp expectedPF
        putStrLn "Actual\n====="
        pp actualPF
        error "XX"
    else do
       putStrLn "Parser OK" 
    
    putStrLn (intercalate "\n" (checkParserFile actualPF))

    pp actualPF
    putStrLn "becomes"
    let x = devInstantiate actualPF
    pPrintNoColor x
    return ()
   
