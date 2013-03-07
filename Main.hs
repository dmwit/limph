module Main where

import Language.Haskell.Exts
import System.Environment

main = do
	args <- getArgs
	case args of
		[file] -> do
			parseFile file >>= print
		_ -> putStrLn "no, idiot, call this with a file you want to parse"
