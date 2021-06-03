{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

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
 -
 -}

module Parser (runFileParser) where

import ParserAST

import Control.Applicative hiding (many, some) 
import Control.Monad
import Data.Text (Text)
import Data.Void
import Data.Either
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Text.Megaparsec.Debug
import qualified Control.Monad.Combinators.Expr as E
import qualified Data.Text as T
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text

type IInstr = Instr IMeta
type IIBlock = IBlock IMeta
metanull :: IMeta
metanull = 0

-- Lexer definitions
sc :: Parser ()
sc = L.space
  space1                         
  (L.skipLineComment "//")       
  (L.skipBlockComment "/*" "*/") 

symbol :: Text -> Parser Text
symbol = L.symbol sc
lexeme = L.lexeme sc

-- Identifiers
pProcName :: Parser String
pProcName = lexeme ((:) <$> letterChar <*> many (char '_' <|> alphaNumChar) <?> "process identifier")
pVarName = pProcName <?> "variable identifier"
pLabelName = pProcName <?> "label identifiers"

-- Combinators
commaSep p = p `sepBy` (symbol ",")
semiSep p = p `sepBy` (symbol ";")

-- parens/braces
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
braces = between (symbol "{") (symbol "}")

tupleOrSingle :: Parser a -> Parser [a]
tupleOrSingle a = 
    (replicate 1) <$> (try a)
    <|> parens (commaSep a)

-- Arithmetic expression
prefix, postfix :: Text -> (AExpr -> AExpr) -> E.Operator Parser AExpr
prefix  name f = E.Prefix  (f <$ symbol name)
postfix name f = E.Postfix (f <$ symbol name)

binary :: Text -> (AExpr -> AExpr -> AExpr) -> E.Operator Parser AExpr
binary  name f = E.InfixL  (f <$ symbol name)

pVarRef :: Parser VarRef
pVarRef = do
    vn <- pVarName 
    ax' <- optional . try $ do
        _ <- symbol "["
        x <- aExpr
        _ <- symbol "]"
        return x
    return $ case ax' of
        (Just ax) -> ArrVar vn ax
        Nothing -> Var vn
        

aVar :: Parser AExpr
aVar = VRef <$> pVarRef

aLit :: Parser AExpr
aLit = Lit <$> lexeme L.decimal

aTerm :: Parser AExpr
aTerm = choice 
    [ parens aExpr
    , aVar
    , aLit
    ]

aOps :: [[E.Operator Parser AExpr]]
aOps =
    [ [prefix "-" Neg, prefix "+" id]
    , [binary "&" BitAnd, binary "|" BitOr]
    , [binary "*" Mul, binary "/" Div]
    , [binary "+" Add, binary "-" Sub]
    , [binary ">>" RShift, binary "<<" LShift]
    , [binary "&" BitAnd, binary "|" BitOr]
    ]

aExpr :: Parser AExpr
aExpr = E.makeExprParser aTerm aOps

-- Boolean expression
bOperators :: [[E.Operator Parser BExpr]]
bOperators =
    [ 
      [E.InfixL (And <$ symbol "and")],
      [E.InfixL (Or <$ symbol "or")]
    ]

bExpr :: Parser BExpr
bExpr = E.makeExprParser bTerm bOperators

bTerm :: Parser BExpr
bTerm = (try $ parens bExpr) <|> bLit <|> rExpr

bLit :: Parser BExpr
bLit = (symbol "true" *> pure BTrue) <|> (symbol "false" *> pure BFalse)

rExpr :: Parser BExpr
rExpr = do
    a1 <- aExpr
    op <- aRel
    a2 <- aExpr
    return (op a1 a2)

aRel :: Parser (AExpr -> AExpr -> BExpr)
aRel = (symbol ">=" *> pure Geq)
       <|> (symbol ">" *> pure Ge)
       <|> (symbol "<=" *> pure Leq)
       <|> (symbol "<" *> pure Le)
       <|> (symbol "==" *> pure Eq)
       <|> (symbol "!=" *> pure Neq)

-- Type
-- Examples: int 
pDType :: Parser DType
pDType =  (symbol "intarr" *> pure DIntArr) 
      <|> (symbol "byte" *> pure DByte) 
      <|> (symbol "bool" *> pure DBool) 
      <|> (symbol "int" *> pure DInt) 

-- Variable declaration
-- Example: int blu
pVarDecl :: Parser VarDecl 
pVarDecl = do
    dt <- pDType
    vn <- pVarName
    return VarDecl {
        varName = vn,
        varType = dt
    }

-- Instructions & Block
pYield :: Parser IInstr 
pYield = do
    _ <- symbol "yield"
    exps <- tupleOrSingle aExpr
    _ <- symbol ";"
    return (IYield metanull exps)

pAssign :: Parser IInstr
pAssign = do
    dest <- pVarRef
    _ <- symbol "="
    src <- aExpr <* (symbol ";")
    return (IAssign metanull dest src)

pLabel :: Parser IInstr
pLabel = do
    name <- pLabelName
    _ <- symbol ":"
    return (ILabel metanull name)

pWhile :: Parser IInstr
pWhile = do
    _ <- symbol "while"
    cond <- parens bExpr
    blk <- pBlock
    return (IWhile metanull cond blk)

pElseBlk :: Parser IIBlock
pElseBlk = do
    _ <- symbol "else"
    false_blk <- pBlock
    return false_blk

pIf :: Parser IInstr
pIf = do
    _ <- symbol "if"
    cond <- parens bExpr
    true_blk <- pBlock
    false_blk <- try pElseBlk <|> (return (IBlock []))
    return (IIf metanull cond true_blk false_blk)

pGoto :: Parser IInstr
pGoto = do
    _ <- symbol "goto"
    lbl <- pLabelName
    _ <- symbol ";"
    return (IGoto metanull lbl)

-- Example: (a,b,c) = pname(1,2,a);
pCall :: Parser IInstr
pCall = do
    res <- tupleOrSingle pVarName
    _ <- symbol "="
    name <- pProcName
    args <- parens (commaSep aExpr)
    _ <- symbol ";"
    return (ICall metanull name args res)

pAssert :: Parser IInstr
pAssert = do
    _ <- symbol "assert"
    args <- parens bExpr
    _ <- symbol ";"
    return (IAssert metanull args)
    

pInstr :: Parser IInstr
pInstr = (pYield)
     <|> try (pLabel) -- since overlap with pAssign
     <|> try (pAssign)
     <|> try pCall 
     <|> try pAssert 
     <|> try (pWhile)
     <|> try (pIf)
     <|> try pGoto


pBlock :: Parser IIBlock
pBlock = do
    is <- braces (many pInstr)
    return (IBlock is)

-- Process
-- Example:
-- proc (int) NAME(int a) {
-- 
-- }

parseProc :: Parser Proc
parseProc = do
    _ <- sc -- consumes extra whitespace. This is needed, because
            -- megaparsec consumes whitespace after the token, but 
            -- since this is the first parser invoked, we eager consume
            -- whitespace
            
    _ <- symbol "proc"
    outParam <- parens (commaSep pDType)
    name <- pProcName
    inParam <- parens (commaSep pVarDecl)
    _ <- symbol "{"
    bodyState <- many (const <$> pVarDecl <*> (symbol ";")) 
    -- let bodyState = []
    bodyInstr <- many pInstr
    _ <- symbol "}"
    return Proc {
        name = name,
        outParam = outParam,
        inParam = inParam,
        state = bodyState,
        body = IBlock bodyInstr
    }

pReplacement :: Parser (String,String)
pReplacement = do
    from <- pVarName
    _ <- symbol "="
    to <- pVarName
    return (from,to)

parseProcCopy :: Parser ProcCopy
parseProcCopy = 
    do
    _ <- symbol "proccopy"
    destName <- pVarName
    _ <- symbol "of"
    ofName <- pVarName
    -- TODO handle "where"
    rpl <- optional . try $ do  
        symbol "where"
        commaSep pReplacement
    let rpl' = case rpl of
                    (Just rs) -> rs
                    Nothing -> []

    _ <- symbol ";"
    return (ProcCopy destName ofName rpl')

parseProcOrProcCopy :: Parser (Either Proc ProcCopy)
parseProcOrProcCopy = 
    (try $ Left <$> parseProc) <|> (Right <$> parseProcCopy)

parseFile :: Parser ParserFile
parseFile = do
    pps <- (many parseProcOrProcCopy) <* eof
    return $ ParserFile (lefts pps) (rights pps)

runFileParser = runParser parseFile

