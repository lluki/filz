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
 - Promela Generator
 -
 -}
module PromelaGen(generatePromela) where

import CoreAST
import Data.List
import GeneratorOpts


-- Utils
intercal x xs = (intercalate x xs) ++ x
inChanName s = s ++ "_in"
outChanName s = s ++ "_out"
gDtype DInt = "int"
gDtype DBool = "bool"
gDtype DByte = "byte"
gDtype DIntArr = "intarr"


-- generate the channel declecarations for a process
gProcChannels :: Proc -> String
gProcChannels p = let
        my_in_chan_name = inChanName $ name p
        chan_t [] = "int"
        chan_t tps = intercalate "," $ map gDtype tps 

        in_chan_t = chan_t $ map varType $ inParam p
        
        in_chan_decl = "chan " ++ my_in_chan_name ++ " = [0] of {" ++ in_chan_t ++ "};\n"

        my_out_chan_name = outChanName $ name p
        out_chan_t = chan_t $ outParam p
        out_chan_decl = "chan " ++ my_out_chan_name ++ " = [0] of {" ++ out_chan_t ++ "};\n"
    in 
        in_chan_decl ++ out_chan_decl 
    

-- generate the process body
gProc :: Proc -> String
gProc p = let
    my_out_chan_name = outChanName $ name p
    my_in_chan_name = inChanName $ name p

    hdr = "proctype " ++ (name p) ++ "()"

    genAE (Lit x) = show x
    genAE (VRef (Var name)) = name
    genAE (VRef (ArrVar name x)) = name ++ ".arr[" ++ (genAE x) ++ "]"
    genAE (Add x y) = "(" ++ (genAE x) ++ ") + (" ++ (genAE y) ++ ")"
    genAE (Sub x y) = "(" ++ (genAE x) ++ ") - (" ++ (genAE y) ++ ")"
    genAE (Mul x y) = "(" ++ (genAE x) ++ ") * (" ++ (genAE y) ++ ")"
    genAE (Div x y) = "(" ++ (genAE x) ++ ") / (" ++ (genAE y) ++ ")"
    genAE (Neg x) = "-(" ++ (genAE x) ++ ")"
    genAE (BitAnd x y) = "(" ++ (genAE x) ++ ") & ( " ++ (genAE y) ++ ")"
    genAE (BitOr x y) = "(" ++ (genAE x) ++ ") | ( " ++ (genAE y) ++ ")"
    genAE (RShift x y) = "(" ++ (genAE x) ++ ") >> ( " ++ (genAE y) ++ ")"
    genAE (LShift x y) = "(" ++ (genAE x) ++ ") << ( " ++ (genAE y) ++ ")"

    genAES xs = intercalate "," $ map genAE xs

    commasepOrUnderscore [] = "_"
    commasepOrUnderscore ps = intercalate "," $ map varName ps 

    in_exps = commasepOrUnderscore (inParam p)

    genBE (Eq a1 a2) = (genAE a1) ++ " == " ++ (genAE a2)
    genBE (Neq a1 a2) = (genAE a1) ++ " != " ++ (genAE a2)
    genBE (Le a1 a2) = (genAE a1) ++ " < " ++ (genAE a2)
    genBE (Leq a1 a2) = (genAE a1) ++ " <= " ++ (genAE a2)
    genBE (Ge a1 a2) = (genAE a1) ++ " > " ++ (genAE a2)
    genBE (Geq a1 a2) = (genAE a1) ++ " >= " ++ (genAE a2)
    genBE (And b1 b2) = (genBE b1) ++ " && " ++ (genBE b2)
    genBE (Or b1 b2) = (genBE b1) ++ " || " ++ (genBE b2)
    genBE (BTrue) = "true"
    genBE (BFalse) = "false"

    genVR (Var nm) = nm
    genVR (ArrVar nm ax) = nm ++ ".arr[" ++ (genAE ax)  ++ "]"

    gen_instr (IYield _ exps) =
        my_out_chan_name ++ "!" ++ genAES exps  ++ "; " ++ my_in_chan_name ++ "?" ++ in_exps ++ ";"
    gen_instr (IAssign _ vr exp) =  genVR vr ++ " = " ++ genAE exp ++ ";"
    gen_instr (ILabel _ name) =  name ++ ":"
    gen_instr (IGoto _ name) =  "goto " ++ name ++ ";"
    gen_instr (IIf _ cond true_blk false_blk) =  "if\n" ++
        ":: " ++ (genBE cond) ++ " -> " ++ (gen_iblock_inner true_blk) ++
        ":: else -> " ++ (gen_iblock_inner false_blk) ++ "\n" ++
        "fi\n"

    gen_instr (IWhile _ cond blk) = "do\n" ++
        ":: " ++ (genBE cond) ++ " -> " ++ (gen_iblock_inner blk) ++
        ":: else -> break;\n" ++
        "od\n"

    gen_instr (ICall _ name args retargs) = 
        let 
            ic = inChanName name
            oc = outChanName name
        in
            ic ++ "!" ++ (genAES args) ++ ";\n" ++
            oc ++ "?" ++ (intercalate "," retargs) ++ ";\n"

    gen_instr (IAssert _ be) = "assert(" ++ (genBE be) ++ ");"

    gen_iblock_inner (IBlock []) = "skip;\n"
    gen_iblock_inner (IBlock is) = (intercalate "\n" (map gen_instr is)) ++ "\n"

    gen_iblock blk = "{\n" ++ (gen_iblock_inner blk) ++ "\n}"
    
    gen_statevar_decl (VarDecl name typ) = (gDtype typ) ++ " " ++ name
    gen_statevar_decls = intercal ";\n" $
         map gen_statevar_decl ((inParam p) ++ (state p))

    gen_fbody =
        -- This is almost gen_iblock, but it starts with a 
        "{\n" ++
        gen_statevar_decls ++
        my_in_chan_name ++ "?" ++ in_exps ++ ";\n" ++
        (gen_iblock_inner (body p)) ++
        "\n}"
    in
        hdr ++
        gen_fbody

generatePromela :: File -> String
generatePromela (File pcs) = let 
        prelude = "typedef intarr { int arr[" ++ show intarr_size ++ "] }\n"
        header = intercalate "\n" (map gProcChannels pcs) 
        body = intercalate "\n" (map gProc pcs)
    in
        prelude ++ header ++ body
