module Main where

import System.Environment ( getArgs )
import Parser as P
import Translator as T


parseCalculus s = case P.parseExpr s of
                     Left er -> print er
                     Right e -> T.translator e

main :: IO ()
main = do fileName <- getArgs
          print fileName
          arq <- readFile $ (++) "app/" $ head $ fileName
          parseCalculus arq