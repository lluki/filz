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
import InstAST
import ParserAST

import PromelaGen
import CGen
import Parser 
import CheckerParse
import CheckerInst
import DevInstantiation
import Utils

import System.Environment
import System.Exit
import System.Console.GetOpt

import Data.Maybe (fromMaybe, catMaybes)
import Data.Text (splitOn, pack, unpack)
import Data.List (intercalate)

import qualified Data.Text.IO as Codec
import qualified Data.Set as Set
import Text.Megaparsec (errorBundlePretty)

import Debug.Trace (trace)
import Text.Pretty.Simple


-- Command line flags
data Flag 
    = CHeader | CDef | Promela
    | Input String | Output String | MachineFilter [String]
      deriving Show

parseParserFile :: FilePath -> IO ParserFile
parseParserFile fp = do
    inp <- Codec.readFile fp
    case runFileParser fp inp of
        Left s -> error (errorBundlePretty s)
        Right sys -> return sys

-- This turns a function that returns a list of errors into a IO ()
-- monad that errors when the function returns a non empty list (the
-- list of errors)
errlistToIO :: String -> (a -> [String]) -> a -> IO a
errlistToIO prefix fn obj =
    let errs = fn obj
    in
        if errs == [] then return obj
        else ioError (userError $ prefix ++ intercalate ".\n"  errs)
        

checkParserFile' = errlistToIO "while checking parsed AST:\n" checkParserFile
checkInstFile' = errlistToIO "while checking instantiated AST:\n" checkInstFile
devInstantiate' = return . devInstantiate
    


showMeThis :: Show a => a -> IO a
showMeThis x = do
    pPrintNoColor x
    return x

-- Run the "pipeline", parse, check parse, instantiate, check inst
fileLoad :: String -> IO InstFile
fileLoad infn = 
    (parseParserFile infn) >>=
    checkParserFile' >>=
    devInstantiate' >>= -- showMeThis >>=
    checkInstFile'

applyMachineFilter :: [Flag] -> InstFile -> InstFile
applyMachineFilter fs instf = 
    let 
        filt = maybe
            (\x -> True) -- default if no flag is given
            (\ms -> \m -> (InstAST.name m) `elem` ms)  -- ok we get a list ms of machine names to include
            (getMachineFilter fs)
    in
        machineFilter filt instf

-- Get optional flag (returns Nothing if not found)
getOptFlag :: (Flag -> Maybe a) -> [Flag] -> Maybe a
getOptFlag fn fs = safeHead $ catMaybes $ map fn fs

-- Access a flag, or ioError if not found
getFlag :: (Flag -> Maybe a) -> String -> [Flag] -> IO a
getFlag fn err fs =
    case getOptFlag fn fs of
        Nothing -> ioError (userError err)
        Just s -> return s

getInputFile :: [Flag] -> IO String
getInputFile =
    let
        fn (Input s) = Just s
        fn _ = Nothing
    in
        getFlag fn "need input file: -i FILE"

getOutputFile :: [Flag] -> IO String
getOutputFile = 
    let
        fn (Output s) = Just s
        fn _ = Nothing
    in
        getFlag fn "need output file: -o FILE"

getMachineFilter :: [Flag] -> Maybe [String]
getMachineFilter =
    let
        fn (MachineFilter ms) = Just ms
        fn _ = Nothing
    in 
        getOptFlag fn

getGenerator :: [Flag] -> IO (String, String -> InstFile -> String)
getGenerator = 
    let
        fn CHeader = Just ("C Headers", generateCHdrs)
        fn CDef = Just ("C Definitions", generateCDefs)
        fn Promela = Just ("Promela", (\x -> generatePromela))
        fn _ = Nothing
    in getFlag fn "Specify one of -H -C -P"

        
   
-- String version of splitOn
sSplitOn sep st = map unpack (splitOn (pack sep) (pack st))

options :: [OptDescr Flag]
options =
    let
        machf :: Maybe String -> Flag
        machf Nothing = MachineFilter []
        machf (Just s) = MachineFilter $ sSplitOn "," s
    in         
    [ Option ['H']     ["header"] (NoArg CHeader)       "generate C header"
    , Option ['C']     ["c-definitions"]  (NoArg CDef)  "generate C definitions"
    , Option ['P']     ["promela"] (NoArg Promela)       "generate Promela"
    , Option ['m']     ["machine-filter"]  (OptArg machf "MACHINES")  "machine filter"
    , Option ['o']     ["output"]  (ReqArg Output "FILE")  "output FILE"
    , Option ['i']     ["input"]   (ReqArg Input  "FILE")  "input FILE"
    ]


compilerOpts :: [String] -> IO ([Flag], [String])
compilerOpts argv = 
  case getOpt Permute options argv of
     (o,n,[]  ) -> return (o,n)
     (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
 where header = "Usage: Main [OPTION...]"




main = do
    args <- getArgs
    (flags, _) <- compilerOpts args
    inf <- getInputFile flags
    outf <- getOutputFile flags
    let outfBase = last $ sSplitOn "/" outf
    putStrLn "~~~ XP v 0.00002 ~~~ "
    putStrLn $ "Flags: " ++ (show flags)
    (genName, gen) <- getGenerator flags
    putStrLn $ "Converting " ++ inf ++ " to " ++ outf ++ " as " ++ genName
    -- Parse,check,instant
    sys <- fileLoad inf
    let sys' = applyMachineFilter flags sys
    writeFile outf (gen outfBase sys')
     
    

