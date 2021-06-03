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


import ParserAST
import CoreAST
import CopyInstantiation
import PromelaGen
import CGen
import Parser 
import Checker

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

-- Command line flags
data Flag 
    = CHeader | CDef | Promela
    | Input String | Output String | MachineFilter [String]
      deriving Show

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:xs) = Just x

parseParserFile :: FilePath -> IO ParserFile
parseParserFile fp = do
    inp <- Codec.readFile fp
    case runFileParser fp inp of
        Left s -> error (errorBundlePretty s)
        Right sys -> return sys

parseFile :: FilePath -> IO File
parseFile fp = do
    sys <- parseParserFile fp
    case (copyInstantiation sys) of
        (Left err) -> ioError (userError err)
        (Right fil) -> return fil


check :: File -> IO File
check f = do
    case check_file f of
        [] -> return f
        errs -> error (unlines errs)

parseAndCheck :: String -> IO File
parseAndCheck infn = do
    sys <- parseFile infn
    sys' <- check sys
    return sys'



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

getGenerator :: [Flag] -> IO (String, String -> File -> String)
getGenerator = 
    let
        fn CHeader = Just ("C Headers", generateCHdrs)
        fn CDef = Just ("C Definitions", generateCDefs)
        fn Promela = Just ("Promela", (\x -> generatePromela))
        fn _ = Nothing
    in getFlag fn "Specify one of -H -C -P"

-- getFilter :: [Flag] -> (File -> File)
-- getFilter = 
--     let
--         fn (MachineFilter []) = Just id
--         fn (MachineFilter fs) = Just
--             (machineFilter (\x -> (name x) `elem` fs))
--         fn _ = Nothing
--     in
--         fromMaybe id . getOptFlag fn


doFilterProc :: [String] -> File -> IO File
doFilterProc desired (File act') =
    let
        act = map name act'
        missing = Set.toList $
            (Set.fromList desired) `Set.difference`  (Set.fromList act)
    in 
        if missing /= [] then
            ioError $ userError ("Missing machines: " ++ intercalate "," missing)
        else 
            return $ machineFilter (\x -> (name x) `elem` desired) (File act')
            

doFilter :: [Flag] -> File -> IO File
doFilter flags inf =
    let
        File act' = inf
        -- act is [(Name, Proc)]
        actNames = Set.fromList $ map name act'
        act = map (\x -> (name x, x)) act'

        fn (MachineFilter fs) = Just fs
        fn _ = Nothing

        filter = getOptFlag fn flags
        (Just desired) = filter
    in
        if filter == Nothing then
            return inf
        else 
            doFilterProc desired inf 
    
    
        
   
options :: [OptDescr Flag]
options =
    [ Option ['H']     ["header"] (NoArg CHeader)       "generate C header"
    , Option ['C']     ["c-definitions"]  (NoArg CDef)  "generate C definitions"
    , Option ['P']     ["promela"] (NoArg Promela)       "generate Promela"
    , Option ['m']     ["machine-filter"]  (OptArg machf "MACHINES")  "machine filter"
    , Option ['o']     ["output"]  (ReqArg Output "FILE")  "output FILE"
    , Option ['i']     ["input"]   (ReqArg Input  "FILE")  "input FILE"
    ]

-- String version of splitOn
sSplitOn sep st = map unpack (splitOn (pack sep) (pack st))
   
machf :: Maybe String -> Flag
machf Nothing = MachineFilter []
machf (Just s) = MachineFilter $ sSplitOn "," s

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
    putStrLn "~~~ XP v 0.00001 ~~~ "
    putStrLn $ "Flags: " ++ (show flags)
    putStr $ "Converting " ++ inf ++ " to " ++ outf ++ " "
    sys <- parseAndCheck inf
    (genName, gen) <- getGenerator flags
    putStrLn $ "as " ++ genName
    sys' <- doFilter flags sys
    writeFile outf (gen outfBase sys')
     
    

