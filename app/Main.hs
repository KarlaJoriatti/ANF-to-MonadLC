module Main where

import Parser as P
import Translator as T


parseCalculus s = case P.parseExpr s of
                     Left er -> print er
                     Right e -> T.translator e

main :: IO ()
main = do s <- readFile "app/test.lc"
          parseCalculus s