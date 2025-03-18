{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
module Translator where

import Data.Char
import System.IO
import Control.Monad.RWS
import Parser

newtype TI a   = TI (Int -> (a, Int))

instance Functor TI where
   fmap f (TI m) = TI (\e -> let (a, e') = m e in (f a, e'))

instance Applicative TI where
   pure a = TI (a,)
   TI fs <*> TI vs = TI (\e -> let (f, e') = fs e; (a, e'') = vs e' in (f a, e''))              

instance Monad TI where 
   TI m >>= f  = TI (\e -> let (a, e') = m e; TI fa = f a in fa e')

freshVar :: TI Type
freshVar = TI (\e -> let v = "t"++show e in (Generic v, e+1))

runTI (TI m) n = let (t, _) = m n in t

-- os tres juntos formam o cabecalho basico
-- do arquivo de saida
imports = "{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeOperators, DataKinds, RankNTypes #-} \nimport Control.Eff\nimport Control.Eff.Extend\nimport Debug.Trace\nimport qualified Prelude as P\n\n"
--"handlerAction :: r ~ (f : r') => (forall v.(f v -> (v -> k) -> k) -> (Eff r a -> k) -> Arrs r v a -> f v -> k)\nhandlerAction f h q elem =\n\tf elem (qComp q h)\n\nmakeHandler :: r ~ (f : r') => (forall v.f v -> (v -> s -> Eff r' b) -> s -> Eff r' b) -> (a -> s -> Eff r' b) -> s -> Eff r a -> Eff r' b\nmakeHandler f g =\n\tPrelude.flip (handle_relay' (handlerAction f) g (Prelude.flip $ makeHandler f g))\n\n"
eapp = "eapp :: P.Monad m => m (a -> m b) -> m a -> m b\neapp f x = do\n   res <- f P.<*> x\n   res\n\n"
console = "data Console x where\n    Print :: x -> Console ()\n\nprint x = send (Print x)\n\n"


functionTranslator expr = 
    let (_, _, w) = runRWS (worker expr) () (2, 0) in w
       where
           worker (Free s) = do
               emit "P.return "
               emit s
           worker (Number n) = do
               emit "P.return "
               emit (show n)
           worker (Text s) = do
               emit "P.return "
               emit (show s)
           worker UnitValue = do
               emit "P.return ()"
           worker TrueValue = do
               emit "P.return P.True"
           worker FalseValue = do
               emit "P.return P.False"
           worker (Let i e e') = do
               j <- getIndentation
               emit (i ++ " <- ")
               worker e
               newline
               putIndentation j
               indent
               worker e'
           worker (Lambda i exp@(Lambda x e)) = do
               saveIndentation
               j <- getIndentation
               emit "P.return P.$ \\"
               emit i
               emit " -> "
               newline
               putIndentation j
               indent
               worker exp
           worker (Lambda i e) = do
               saveIndentation
               j <- getIndentation
               emit "P.return P.$ \\"
               emit i
               emit " -> do"
               newline
               putIndentation j
               indent
               emit " "
               worker e
           worker (If c e e') = do
               saveIndentation
               i <- getIndentation
               let s = runTI freshVar i
               emit (show s)
               emit " <- "
               worker c
               newline
               indent
               emit "if "
               emit (show s)
               newline
               putIndentation i
               indent
               emit "then "
               worker e
               newline
               putIndentation i
               indent
               emit "else "
               worker e'
           worker (Application (Free "error") (Text s)) = do
               emit "P.return ("
               emit "P.error "
               emit (show s)
               emit ")"
           worker (Application (Free s) e') = do
               emit "( P.return "
               emit s
               emit " `eapp` "
               worker e'
               emit ")"
           worker (Application e e') = do
               emit "("
               worker e
               emit " `eapp` "
               worker e'
               emit ")"
           worker (Operation op (Free s) (Free s')) = do
               emit "P.return ("
               emit s
               emit (" " ++ show op ++ " ")
               emit s'
               emit ")"
           worker (Operation op (Free s) (Number n)) = do
               emit "P.return ("
               emit s
               emit (" " ++ show op ++ " ")
               emit (show n)
               emit ")"
           worker (Operation op (Number n) (Free s)) = do
               emit "P.return ("
               emit (show n)
               emit (" " ++ show op ++ " ")
               emit s
               emit ")"
           worker (Operation op e e') = do
               emit "("
               emit (" (" ++ show op ++ ") ")
               emit " P.<$> "
               worker e
               emit " P.<*> "
               worker e'
               emit ")"
           worker (Where bindings e) = do
               saveIndentation
               i <- getIndentation
               emitBindings bindings True
               newline
               putIndentation i
               indent
               worker e
           
           emit str = do
               (a, b) <- get 
               tell str
               put (a + length str, b)

           newline = do
               tell "\n"
               (_, b) <- get
               put (0, b)
           
           getIndentation = do
               (_, b) <- get 
               return b
            
           putIndentation b = do
               (a, _) <- get
               put (a, b)

           saveIndentation = do
               (a, _) <- get
               putIndentation a
           
           indent = do
               (a, b) <- get
               if a /= 0 then error "We Screwed up identation"
               else emit (replicate b ' ')
           
           emitMultiBind (Lambda i e) = do
               newline
               indent
               emit "P.return P.$ \\"
               emit i
               i <- getIndentation
               emit " -> "
               emitMultiBind e
           emitMultiBind e = do
               emit "do "
               newline
               indent
               case e of
                 Free s -> emit ("P.return " ++ s)
                 _ -> worker e
           
           emitBindings [] f = return ()          
           emitBindings ((i, Lambda x e):xs) f = do
               if f 
               then emit "let "
               else emit ""
               saveIndentation
               j <- getIndentation
               emit (i ++ " ")
               saveIndentation
               emit x
               emit " = "
               emitMultiBind e
               unless(null xs) $ do
                newline
                putIndentation j
                indent
                emitBindings xs False

-- vai criar restricoes do tipo 'Member e t'
-- onde e vem de uma effect row
takeEfs t [a, b] = return ("Member " ++ show a ++ " " ++ show t)
takeEfs t (e : es) = do b <- takeEfs t es
                        return ("Member " ++ show e ++ " " ++ show t ++ "," ++ b)

-- juntar restricoes
joinStrs a b | null a = b
             | null b = a
             | otherwise = a ++ "," ++ b


saidaTipo (Row efs) f = do t <- freshVar
                           case efs of
                            [x, y] -> if f then return (show x ++ " ", []) else return ("Eff " ++ show t ++ " ", "Member " ++ show x ++ " " ++ show t)
                            _ -> do str <- takeEfs t efs
                                    return ("Eff " ++ show t ++ " ", str)
saidaTipo (Arrow Unit e t) f = do (a, b) <- saidaTipo e f
                                  (a1, b1) <- saidaTipo t f
                                  return (a ++ a1, joinStrs b b1)
saidaTipo (Arrow t1 (Generic i) t2@(Arrow a b c)) f = do t <- freshVar
                                                         (a, b) <- saidaTipo t1 f
                                                         (a2, b2) <- saidaTipo t2 f
                                                         if f then 
                                                            return (a ++ "-> " ++ a2, joinStrs b b2)
                                                         else return (a ++ "-> Eff " ++ show t ++ " (" ++ a2 ++ ")", joinStrs b b2)
saidaTipo (Arrow t1 e t2@(Arrow a b c)) f = do (a, b) <- saidaTipo t1 f
                                               (a1, b1) <- saidaTipo e f
                                               (a2, b2) <- saidaTipo t2 f
                                               return (a ++ "-> " ++ a1 ++"("++ a2 ++ ")", joinStrs b (joinStrs b1 b2))
saidaTipo (Arrow t1 (Generic i) t2) f = do t <- freshVar
                                           (a, b) <- saidaTipo t1 f
                                           (a2, b2) <- saidaTipo t2 f
                                           return (a ++ "-> Eff " ++ show t ++ " " ++ a2, joinStrs b b2)
saidaTipo (Arrow t1 e t2) f = do (a, b) <- saidaTipo t1 f
                                 (a1, b1) <- saidaTipo e f
                                 (a2, b2) <- saidaTipo t2 f
                                 return (a ++ "-> " ++ a1 ++ a2, joinStrs b (joinStrs b1 b2))
saidaTipo t f = return (show t ++ " ", [])

--tipoEx = Arrow (Generic "a") (Row [Generic "State", Generic "b"]) (Arrow Bool (Row [Generic "Amb", Generic "State", Generic "c"]) Unit)

countParams (Arrow t (Generic i) t') = 1 + countParams t'
countParams _ = 1

sendParams :: Int -> [Char]
sendParams 0 = ""
sendParams i = "P.return (\\x" ++ show i ++ " -> " ++ sendParams (i-1)

params ::  Int -> [Char]
params 0 = ""
params n = "x" ++ show n ++ " " ++ params (n-1)


createSend hs [] = return ()
createSend hd ((nome@(c:cs),tipo):xs) = do hPutStr hd (nome ++ " ")
                                           case tipo of
                                            (Arrow Unit _ _) -> hPutStrLn hd ("() = send " ++ [toUpper c] ++ cs)
                                            t -> do let n = countParams t
                                                    if n > 1 then
                                                        do let a = sendParams (n-1)
                                                               p = params (n-1)
                                                           hPutStr hd "x0 = "
                                                           hPutStr hd a
                                                           hPutStr hd $ "send (" ++ [toUpper c] ++ cs ++ " x0 "
                                                           hPutStr hd p 
                                                           hPutStrLn hd $ concat $ replicate n ")"
                                                    else hPutStrLn hd $ "x0 = send (" ++ [toUpper c] ++ cs ++ " x0)"
                                           createSend hd xs


saidaDeclaracoes _ [] = return ()
saidaDeclaracoes hd ((c:cs, tipo):xs) = do hPutStr hd "   "
                                           let name = toUpper c : cs
                                           saidaDecl hd name tipo
                                           saidaDeclaracoes hd xs

-- vai esconder as funcoes do prelude
-- que podem ter nomes iguais aos das
-- funcoes definidas pelo user
takeFunctions [] [] hd = return ()
takeFunctions [] [(x,_)] hd = do hPutStr hd x
                                 hPutStrLn hd ")\n\n"
takeFunctions [(x, _, _)] [] hd = do hPutStr hd x
                                     hPutStrLn hd ")\n\n"
takeFunctions [] ((x,_):xs) hd = do hPutStr hd x
                                    hPutStr hd ", "
                                    takeFunctions [] xs hd
takeFunctions ((x, _, _):xs) [] hd = do hPutStr hd x
                                        hPutStr hd ", "
                                        takeFunctions xs [] hd
takeFunctions ((nomef, _, _):xs) ys hd = do hPutStr hd nomef
                                            hPutStr hd ", "
                                            takeFunctions xs ys hd

saidaEfeitos hs [] = return ()
saidaEfeitos hd ((c:cs, listaDeclaracoes):xs) = do hPutStrLn hd ("data " ++ [toUpper c] ++ cs ++ " x where")
                                                   saidaDeclaracoes hd listaDeclaracoes
                                                   hPutStrLn hd ""
                                                   createSend hd listaDeclaracoes
                                                   hPutStrLn hd ""
                                                   saidaEfeitos hd xs 


saidaDecl hd nome tipo = do let (typee, constraints) = runTI (saidaTipo tipo (isUpper (head nome))) 0
                            if null constraints
                            then hPutStrLn hd (nome ++ " :: " ++ typee)
                            else hPutStrLn hd (nome ++ " :: (" ++ constraints ++ ") => " ++ typee)


saidaFuncoes hd [] = return ()
saidaFuncoes hd ((nome, tipo, Lambda i e):xs) = do saidaDecl hd nome tipo
                                                   hPutStr hd $ nome ++ " " ++ i ++ " = "
                                                   case e of
                                                    (Lambda _ _) -> hPutStrLn hd $ "\n  " ++ functionTranslator e
                                                    _ -> hPutStrLn hd $ "do\n  " ++ functionTranslator e
                                                   --hPutStrLn hd (functionTranslator e)
                                                   hPutStrLn hd ""
                                                   saidaFuncoes hd xs

saida :: ([(String, [(String, Type)])], [(String, Type, Expr)]) -> IO ()
saida (listaEfeitos, listaFuncoes) = do handle <- openFile "app/converted.hs" WriteMode
                                        hPutStr handle imports
                                        --hPutStrLn handle "import Prelude hiding (print,"
                                        --takeFunctions listaFuncoes (concatMap snd listaEfeitos) handle
                                        hPutStr handle console
                                        saidaEfeitos handle listaEfeitos
                                        hPutStrLn handle eapp
                                        saidaFuncoes handle listaFuncoes
                                        hClose handle