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
module CGen(generateCDefs, generateCHdrs) where

import InstAST
import GeneratorOpts
import Data.List
import Data.Char (isAlpha,toUpper)
import Data.String.Utils (replace)
import Data.Maybe (catMaybes)

-- utils
enum = zip [0..]
parens x = "(" ++ x ++ ")"
braces x = "{" ++ x ++ "}"
inParens = parens  . intercalate ","
inBraces x = "{\n" ++ (intercalate "\n" x) ++ ";\n}"
nlJoin = intercalate "\n"
nlSemiJoin x = (intercalate ";\n" x ) ++ ";\n"
addrOf x = "&" ++ x


var :: InstProc -> VarRef -> String
var proc vr = 
    let
        gd = var proc -- self reference
        nm = varRefName vr
        prefix = if nm `elem` (map varName $ inParam proc) then ""
              else "global." ++ (name proc) ++ "." 
    in
        case vr of
            (Var nm) -> prefix ++ nm
            (ArrVar nm ax) -> prefix ++ nm ++ ".arr[" ++ (gAE gd ax) ++ "]"

-- generator data, for now just a string encapsulation
type GenData = VarRef -> String

-- generators
gInclude x = "#include \"" ++ (replace ".c" ".h" x) ++ "\""
gHeader ext = nlJoin $ map gInclude [ext, "stdio.h", "stdint.h", "assert.h",
    "stdbool.h"]

gDtype DInt = "int"
gDtype DBool = "bool"
gDtype DByte = "uint8_t"
gDtype DIntArr = "intarr_t"

gInParams :: [VarDecl] -> [String]
gInParams = map (\x -> gDtype (varType x) ++ " " ++ (varName x)) 

gOutParams :: [DType] -> [String]
gOutParams ds = map (\(x,i) -> gDtype i ++ " *out_" ++ show x) $ enum ds

-- Generate a sub struct for that specific process
gPStateStruct :: InstProc -> String
gPStateStruct (InstProc name _ _ state _) =
    let 
        stName = name
        fm (VarDecl n t) = (gDtype t) ++ " " ++ n
        stBody = nlSemiJoin $ map fm $ state ++ [VarDecl "mapos" DInt]
    in 
        "struct {\n" ++
            stBody ++
        "} " ++ stName
 
-- A top level struct containing sub structs for all machines
gStateStruct :: [InstProc] -> String
gStateStruct ps = "static struct {\n" ++ 
        (nlSemiJoin $ map gPStateStruct ps) ++ "\n} global;"

--         
gAE :: GenData -> AExpr -> String
gAE gd (Lit x) = show x
gAE gd (VRef vr) = gd vr
gAE gd (Add x y) = "(" ++ (gAE gd x) ++ ") + (" ++ (gAE gd y) ++ ")"
gAE gd (Sub x y) = "(" ++ (gAE gd x) ++ ") - (" ++ (gAE gd y) ++ ")"
gAE gd (Mul x y) = "(" ++ (gAE gd x) ++ ") * (" ++ (gAE gd y) ++ ")"
gAE gd (Div x y) = "(" ++ (gAE gd x) ++ ") / (" ++ (gAE gd y) ++ ")"
gAE gd (Neg x) = "-(" ++ (gAE gd x) ++ ")"
gAE gd (BitAnd x y) = "(" ++ (gAE gd x) ++ ") & ( " ++ (gAE gd y) ++ ")"
gAE gd (BitOr x y) = "(" ++ (gAE gd x) ++ ") | ( " ++ (gAE gd y) ++ ")"
gAE gd (RShift x y) = "(" ++ (gAE gd x) ++ ") >> ( " ++ (gAE gd y) ++ ")"
gAE gd (LShift x y) = "(" ++ (gAE gd x) ++ ") << ( " ++ (gAE gd y) ++ ")"
gAES gd xs = intercalate "," $ map (gAE gd) xs

gBE gd (Eq a1 a2)  = "(" ++ (gAE gd a1) ++ ") == (" ++ (gAE gd a2) ++ ")"
gBE gd (Neq a1 a2) = "(" ++ (gAE gd a1) ++ ") != (" ++ (gAE gd a2) ++ ")"
gBE gd (Le a1 a2)  = "(" ++ (gAE gd a1) ++ ") < (" ++ (gAE gd a2) ++ ")"
gBE gd (Leq a1 a2) = "(" ++ (gAE gd a1) ++ ") <= (" ++ (gAE gd a2) ++ ")"
gBE gd (Ge a1 a2)  = "(" ++ (gAE gd a1) ++ ") > (" ++ (gAE gd a2) ++ ")"
gBE gd (Geq a1 a2) = "(" ++ (gAE gd a1) ++ ") >= (" ++ (gAE gd a2) ++ ")"
gBE gd (And b1 b2) = "(" ++ (gBE gd b1) ++ ") && (" ++ (gBE gd b2) ++ ")"
gBE gd (Or b1 b2)  = "(" ++ (gBE gd b1) ++ ") || (" ++ (gBE gd b2) ++ ")"
gBE gd (BTrue) = "true"
gBE gd (BFalse) = "false"

--
gInstr :: GenData -> Instr Integer -> String
gInstr gd (IYield mapos xas) =
    let
        one_out :: (Integer, AExpr) -> String
        one_out (i, aex) = "*out_" ++ (show i) ++ " = " ++ (gAE gd aex)
        set_out = map one_out (enum xas)
        set_state = (gd (Var "mapos")) ++ " = " ++ show mapos 
        lbl = "\ncontinuation_" ++ (show mapos) ++ ": 0; "
    in 
        (nlSemiJoin $ set_out ++ [set_state, "return"]) ++ lbl

gInstr gd (IAssign _ vn aexp) =
        (gd vn) ++ " = " ++ (gAE gd aexp) ++ ";"
gInstr gd (IIf _ bexp trueb falseb) =
        let 
            (IBlock elseI) = (falseb)
            elseBlk =  " else { \n" ++ (gIBlock gd falseb) ++ "};\n"
            el = if (length elseI) == 0 then "" else elseBlk
        in
        "if(" ++ (gBE gd bexp) ++ ") {\n" ++
         (gIBlock gd trueb) ++ "\n}" ++ el ++ "\n"

gInstr gd (IWhile _ bexp whileb) = 
        "while(" ++ (gBE gd bexp) ++ ") {\n" ++
         (gIBlock gd whileb) ++ "}\n"

gInstr _ (ILabel _ name) = name ++ ":\n"
gInstr _ (IGoto _ name) = "goto " ++ name ++ ";" 
gInstr gd (ICall _ callName callArgs retArgs) = 
    let
        callPs = map (gAE gd) callArgs
        retPs= map (addrOf . gd . Var) retArgs
        params = inParens (callPs ++ retPs)
    in
        callName ++ params ++ ";"

gInstr gd (IAssert _ arg) = "assert(" ++ (gBE gd arg) ++ ");\n"

isYield :: Instr a -> Bool
isYield (IYield _ _) = True
isYield _ = False

gJumpTable :: GenData -> IBlock Integer -> String
gJumpTable gd blk =
    let 
        yieldPos (IYield a _) = Just a
        yieldPos _ = Nothing
        progYields = catMaybes $ blockFold yieldPos blk
        initYield = [0]
        yields = initYield ++ progYields
        mkCase mapos  = "case " ++ (show mapos) ++
            ": goto continuation_" ++ (show mapos) ++ ";\n"
        cases = concat $ map mkCase yields
    in
        "switch(" ++ (gd (Var "mapos")) ++ ") {\n" ++
        cases ++ "};\n"
        

gIBlock :: GenData -> IBlock Integer -> String
gIBlock gd (IBlock is) = nlJoin (map (gInstr gd) is)
        
gProcDef :: InstProc -> String
gProcDef p =
   let 
        (InstProc name inp outp state body) = p    
        gd = var p
        body' = metaEnumerate body
        arglist = inParens $ (gInParams inp) ++ (gOutParams outp)
        b = inBraces $
            [gJumpTable gd body',
             "continuation_0:",
             gIBlock gd body']
    in
        "void " ++ name ++ arglist ++ b

gProcDecl :: InstProc -> String
gProcDecl p =
   let 
        (InstProc name inp outp state body) = p    
        gd = var p
        (IBlock body') = metaEnumerate body
        arglist = inParens $ (gInParams inp) ++ (gOutParams outp)
    in
        "void " ++ name ++ arglist ++ ";"


generateCDefs :: String -> InstFile -> String
generateCDefs outfn (InstFile ps _) = nlJoin ([gHeader outfn, gStateStruct ps] ++
    (map gProcDef ps))

gHdrMacroName x = "_" ++ (map toUpper $ filter isAlpha x) ++ "_"
gHdrStartBarrier x = "#ifndef " ++ x ++ "\n#define " ++ x ++ "\n"
gHdrEndBarrier = "#endif"

generateCHdrs :: String -> InstFile -> String
generateCHdrs outfn (InstFile ps _) =
    let
        start = gHdrStartBarrier $ gHdrMacroName outfn
        tdef = "typedef struct { int arr[" ++ 
            show intarr_size ++ "];} intarr_t;\n";
        end = gHdrEndBarrier
    in
        nlJoin $ [start, tdef] ++ (map gProcDecl ps) ++ [end]

        
