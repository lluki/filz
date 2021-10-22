{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
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
 - The core AST Definition, it knows only about Procs, and Procs
 - are instances.
 - These procs should be properly instanciated, that is if 
 - they do a call
 -}

module CoreAST where

import Data.Functor
import Data.Traversable

import Control.Applicative
import Control.Monad.State
import Control.Lens

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


aLeaves :: Traversal' AExpr AExpr
aLeaves f (Add a1 a2) = (Add <$> aLeaves f a1) <*> aLeaves f a2
aLeaves f (Sub a1 a2) = (Sub <$> aLeaves f a1) <*> aLeaves f a2
aLeaves f (Mul a1 a2) = (Mul <$> aLeaves f a1) <*> aLeaves f a2
aLeaves f (Div a1 a2) = (Div <$> aLeaves f a1) <*> aLeaves f a2
aLeaves f (Neg a1) = Neg <$> aLeaves f a1
aLeaves f (BitAnd a1 a2) = (BitAnd <$> aLeaves f a1) <*> aLeaves f a2
aLeaves f (BitOr a1 a2) = (BitOr <$> aLeaves f a1) <*> aLeaves f a2
aLeaves f (RShift a1 a2) = (RShift <$> aLeaves f a1) <*> aLeaves f a2
aLeaves f (LShift a1 a2) = (LShift <$> aLeaves f a1) <*> aLeaves f a2
aLeaves f x = f x

bAexprs :: Traversal' BExpr AExpr
bAexprs f (Le a1 a2)   = (Le <$> f a1) <*> f a2
bAexprs f (Leq a1 a2)  = (Leq <$> f a1) <*> f a2
bAexprs f (Ge a1 a2)   = (Ge <$> f a1) <*> f a2
bAexprs f (Geq a1 a2)  = (Geq <$> f a1) <*> f a2
bAexprs f (Eq a1 a2)   = (Eq <$> f a1) <*> f a2
bAexprs f (Neq a1 a2)  = (Neq <$> f a1) <*> f a2
bAexprs f (And b1 b2)  = (And <$> bAexprs f b1) <*> bAexprs f b2
bAexprs f (Or b1 b2)  = (Or <$> bAexprs f b1) <*> bAexprs f b2
bAexprs f x = pure x


-- Block
data IBlock meta = IBlock [Instr meta]
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

ibAexprs :: Traversal' (IBlock meta) AExpr
ibAexprs f (IBlock is) = IBlock <$> (sequenceA $ map (iAexprs f) is)

-- default meta type
type IMeta = Int


-- an instruction. This encode explicit calls,
-- the parser will always produce ICall with callName = "call"
-- which are then replaced 
data Instr meta =
             IYield meta [AExpr]
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
           deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

iAexprs :: Traversal' (Instr meta) (AExpr)
iAexprs f (IYield m as) = IYield m <$> traverse f as
iAexprs f (IAssign m vr ae) = IAssign m vr <$> f ae
iAexprs f (IIf m be ibA ibB) = (liftA3 $ IIf m)
    (bAexprs f be) (ibAexprs f ibA) (ibAexprs f ibB)
iAexprs f (IWhile m be blk) = (liftA2 $ IWhile m) (bAexprs f be) (ibAexprs f blk)
iAexprs f (IAssert m be) = IAssert m <$> (bAexprs f be)
iAexprs f (ICall m callName callArgs retArgs) =
    (\x -> ICall m callName x retArgs) <$> (sequenceA $ map f callArgs)
iAexprs f x = pure x


data DType = DInt | DBool | DByte | DIntArr
    deriving (Eq, Ord, Show)

data VarDecl = VarDecl {
        varName :: String,
        varType :: DType }
    deriving (Eq, Ord, Show)

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

blockFold :: (Instr m1 -> a) -> (IBlock m1) -> [a]
blockFold fn (IBlock is) = concat $ map (instrFold fn) is

-- Insert incrementing values in meta 
-- Can be applied to IBlock 
metaEnumerate :: Traversable t => t a -> t Integer
metaEnumerate t = evalState (traverse step t) 1
    where step a = do tag <- get
                      modify succ
                      return tag

-- some handy utils that are used in instantiation and checkers...
isCall :: Instr a -> Bool
isCall (ICall _ _ _ _) = True
isCall _ = False

