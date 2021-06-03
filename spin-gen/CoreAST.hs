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

{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}

{-
 - The core AST Definition, with Proc only
 -}

module CoreAST where

import Data.Functor
import Data.Traversable

import Control.Monad.State

data VarRef = Var String
            | ArrVar String AExpr
  deriving (Eq, Ord, Show)

varRefName :: VarRef -> String
varRefName (Var x) = x 
varRefName (ArrVar x _) = x 

data AExpr =
            Lit Integer
          | VRef VarRef
          | Add AExpr AExpr
          | Sub AExpr AExpr
          | Mul AExpr AExpr
          | Div AExpr AExpr
          | Neg AExpr
          | BitAnd AExpr AExpr
          | BitOr AExpr AExpr
          | RShift AExpr AExpr
          | LShift AExpr AExpr
  deriving (Eq, Ord, Show)
        

instance Num AExpr where
  x + y         = Add x y
  x * y         = Mul x y
  x - y         = Sub x y
  abs x         = error "Not implemented"
  signum x      = error "Not implemented"
  fromInteger x = Lit x


data BExpr 
  = Le AExpr AExpr
  | Leq AExpr AExpr
  | Ge AExpr AExpr
  | Geq AExpr AExpr
  | Eq AExpr AExpr
  | Neq AExpr AExpr
  | And BExpr BExpr
  | Or BExpr BExpr
  | BTrue
  | BFalse
  deriving (Eq, Ord, Show)


data IBlock meta = IBlock [Instr meta]
    deriving (Show, Functor, Foldable, Traversable)

-- default meta type
type IMeta = Int


-- an instruction
data Instr meta = IYield meta [AExpr]
           | IAssign meta VarRef AExpr
           | IIf meta BExpr (IBlock meta) (IBlock meta)
           | IWhile meta BExpr (IBlock meta)
           | ILabel meta String
           | IGoto meta String
           | IAssert meta BExpr
           | ICall { m :: meta
                   , callName :: String
                   , callArgs :: [AExpr]
                   , retArgs :: [String] }
           deriving (Show, Functor, Foldable, Traversable)

data DType = DInt | DBool | DByte | DIntArr

data VarDecl = VarDecl {
        varName :: String,
        varType :: DType }

data Proc = Proc { name :: String
                 , inParam :: [VarDecl]
                 , outParam :: [DType]
                 , state :: [VarDecl]
                 , body :: IBlock IMeta}

data File = File [Proc]


-- Utils 
aExprFold :: (AExpr -> a) -> AExpr -> [a]
aExprFold fn c =
        let 
            x = fn c
            rec = aExprFold fn
            xs = case c of 
                (Lit _) -> []
                (VRef (Var _)) -> []
                (VRef (ArrVar _ a)) -> rec a
                (Add a b) -> rec a ++ rec b
                (Sub a b) -> rec a ++ rec b
                (Mul a b) -> rec a ++ rec b
                (Div a b) -> rec a ++ rec b
                (Neg a)   -> rec a
                (BitAnd a b) -> rec a ++ rec b
                (BitOr a b) -> rec a ++ rec b
                (RShift a b) -> rec a ++ rec b
                (LShift a b) -> rec a ++ rec b
        in (x:xs)

bExprFold :: (BExpr -> a) -> (AExpr -> a) -> BExpr -> [a]
bExprFold bfn afn c =
        let 
            x = bfn c
            arec = aExprFold afn
            brec = bExprFold bfn afn
            xs = case c of          
                (Le a1 a2) -> arec a1 ++ arec a2
                (Leq a1 a2) -> arec a1 ++ arec a2
                (Ge a1 a2) -> arec a1 ++ arec a2
                (Geq a1 a2) -> arec a1 ++ arec a2
                (Eq a1 a2) -> arec a1 ++ arec a2
                (Neq a1 a2) -> arec a1 ++ arec a2
                (And b1 b2) -> brec b1 ++ brec b2
                (Or b1 b2) -> brec b1 ++ brec b2
                (BTrue) -> []
                (BFalse) -> []
        in (x:xs)

instrFold :: (Instr m1 -> a) -> (Instr m1) -> [a]
instrFold fn i = let
    rec = blockFold fn
    x = fn i
    xs = case i of 
        (IYield _ _) -> []
        (IAssign _ _ _) -> []
        (IIf _ _ blk1 blk2) -> (rec blk1) ++ (rec blk2)
        (IWhile _ _ blk) -> rec blk
        (ILabel _ _) -> []
        (IGoto _ _) -> []
        (ICall _ _ _ _) -> []
        (IAssert _ _) -> []
    in
        (x:xs)

instrMap :: (Instr IMeta -> Instr IMeta) -> Proc -> Proc
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


blockFold :: (Instr m1 -> a) -> (IBlock m1) -> [a]
blockFold fn (IBlock is) = concat $ map (instrFold fn) is

machineFilter :: (Proc -> Bool) -> File -> File
machineFilter f (File ps) = File (filter f ps)

-- Insert incrementing values in meta 
-- Can be applied to IBlock 
metaEnumerate :: Traversable t => t a -> t Integer
metaEnumerate t = evalState (traverse step t) 1
    where step a = do tag <- get
                      modify succ
                      return tag
