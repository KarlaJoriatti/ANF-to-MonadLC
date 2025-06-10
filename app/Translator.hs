{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
module Translator where

import Data.Char
import System.IO
import Control.Monad.RWS
import Parser

newtype TI a = TI (Int -> (a, Int))

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

-- converted.hs header vvvvv
imports = "{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeOperators, DataKinds, RankNTypes #-} \nimport Control.Eff\nimport Control.Eff.Extend\nimport Debug.Trace\nimport qualified Prelude as P\n\n"
eapp = "eapp :: P.Monad m => m (a -> m b) -> m a -> m b\neapp f x = do\n   res <- f P.<*> x\n   res\n\n"
console = "data Console x where\n    Print :: x -> Console ()\n\nprint x = send (Print x)\n\n"
--"handlerAction :: r ~ (f : r') => (forall v.(f v -> (v -> k) -> k) -> (Eff r a -> k) -> Arrs r v a -> f v -> k)\nhandlerAction f h q elem =\n\tf elem (qComp q h)\n\nmakeHandler :: r ~ (f : r') => (forall v.f v -> (v -> s -> Eff r' b) -> s -> Eff r' b) -> (a -> s -> Eff r' b) -> s -> Eff r a -> Eff r' b\nmakeHandler f g =\n\tPrelude.flip (handle_relay' (handlerAction f) g (Prelude.flip $ makeHandler f g))\n\n"
-- converted.hs header ^^^^
header = imports ++ console

-- main translator function
translator :: ([EffectDecl], [(String, Type, Expr)]) -> IO ()
translator (effList, funList) = do 
    handle <- openFile "app/converted.hs" WriteMode
    hPutStr handle header
    effects handle effList
    hPutStrLn handle eapp
    functions handle funList
    hClose handle


effects hs [] = return ()
effects hd ((effectName, declList):xs) = do 
    hPutStrLn hd ("data " ++ [toUpper (head effectName)] ++ tail effectName ++ " x where")
    constDecl hd declList
    hPutStrLn hd ""
    createSend hd declList
    hPutStrLn hd ""
    effects hd xs 

constDecl _ [] = return ()
constDecl hd ((constName, constType):xs) = do 
    hPutStr hd "   "
    declTranslator hd (toUpper (head constName) : tail constName) constType
    constDecl hd xs


functions hd [] = return ()
functions hd ((nome, tipo, Lambda i e):xs) = do 
    declTranslator hd nome tipo
    hPutStr hd $ nome ++ " " ++ i ++ " = "
    case e of
        (Lambda _ _) -> hPutStrLn hd $ "\n  " ++ functionTranslator e
        _ -> hPutStrLn hd $ "do\n  " ++ functionTranslator e
    hPutStrLn hd ""
    functions hd xs


declTranslator hd nome consType = do 
    let (typee, constraints) = runTI (typeTranslator consType (isUpper (head nome))) 0
    if null constraints
    then hPutStrLn hd (nome ++ " :: " ++ typee)
    else hPutStrLn hd (nome ++ " :: (" ++ constraints ++ ") => " ++ typee)


createSend hs [] = return ()
createSend hd ((c:cs,tipo):xs) = do 
    let countParams x = 
            case x of 
                (Arrow t (GenEff i) t') -> 1 + countParams t'
                _ -> 1
        sendParams x = 
            case x of
                0 -> ""
                i -> "P.return (\\x" ++ show i ++ " -> " ++ sendParams (x-1)
        params x =
            case x of
                0 -> ""
                i -> "x" ++ show i ++ " " ++ params (x-1)
    hPutStr hd ([toLower c] ++ cs ++ " ")
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



typeTranslator (Arrow Unit e t) f = do 
    (a1, b1) <- effectsTranslator e f
    (a2, b2) <- typeTranslator t f
    return (a1 ++ a2, joinMembers b1 b2)
typeTranslator (Arrow t1 (GenEff i) t2@(Arrow a b c)) f = do 
    t <- freshVar
    (a1, b1) <- typeTranslator t1 f
    (a2, b2) <- typeTranslator t2 f
    if f then 
        return (a1 ++ "-> " ++ a2, joinMembers b1 b2)
    else 
        return (a1 ++ "-> Eff " ++ show t ++ " (" ++ a2 ++ ")", joinMembers b1 b2)
typeTranslator (Arrow t1 e t2@(Arrow a b c)) f = do 
    (a1, b1) <- typeTranslator t1 f
    (a2, b2) <- effectsTranslator e f
    (a3, b3) <- typeTranslator t2 f
    return (a1 ++ "-> " ++ a2 ++"("++ a3 ++ ")", joinMembers b1 (joinMembers b2 b3))
typeTranslator (Arrow t1 (GenEff i) t2) f = do 
    t <- freshVar
    (a1, b1) <- typeTranslator t1 f
    (a2, b2) <- typeTranslator t2 f
    return (a1 ++ "-> Eff " ++ show t ++ " " ++ a2, joinMembers b1 b2)
typeTranslator (Arrow t1 e t2) f = do 
    (a1, b1) <- typeTranslator t1 f
    (a2, b2) <- effectsTranslator e f
    (a3, b3) <- typeTranslator t2 f
    return (a1 ++ "-> " ++ a2 ++ a3, joinMembers b1 (joinMembers b2 b3))
typeTranslator t f = return (show t ++ " ", [])

--tipoEx = Arrow (Generic "a") (Row [Generic "State", Generic "b"]) (Arrow Bool (Row [Generic "Amb", Generic "State", Generic "c"]) Unit)


effectsTranslator (Row efs) f = do 
    let member t ls = 
            case ls of
                [a, b] -> return ("Member " ++ show a ++ " " ++ show t)
                (e:es) -> do 
                    b <- member t es
                    return ("Member " ++ show e ++ " " ++ show t ++ "," ++ b)
    t <- freshVar
    case efs of
        [x, y] -> if f then return (show x ++ " ", []) else return ("Eff " ++ show t ++ " ", "Member " ++ show x ++ " " ++ show t)
        _ -> do restrics <- member t efs
                return ("Eff " ++ show t ++ " ", restrics)
effectsTranslator e _ = return (show e ++ " ", [])


-- joins Member restrictions
joinMembers a b 
    | a == [] = b
    | b == [] = a
    | otherwise = a ++ "," ++ b


-- translator for functions

functionTranslator :: Expr -> String
functionTranslator expr = 
    let (_, _, w) = runRWS (worker expr) () (2,0,0) in w

worker expr = case expr of 
    Free s            -> emit "P.return " >> emit s
    Number n          -> emit "P.return " >> emit (show n)
    Text s            -> emit "P.return " >> emit (show s)
    UnitValue         -> emit "P.return ()"
    TrueValue         -> emit "P.return P.True"
    FalseValue        -> emit "P.return P.False"
    Let i e e'        -> translateLet i e e'
    Lambda i e        -> translateLambda i e
    If c e e'         -> translateIf c e e'
    Application e e'  -> translateApp e e'
    Operation op e e' -> translateOp op e e'
    Where bindings e  -> translateWhere bindings e


-- string emission and identation functions

emit str = do 
    (a,b,c) <- get
    tell str
    put (a + length str, b,c)

newline = do 
    tell "\n"
    (_, b,c) <- get
    put (0, b,c)

getIndentation = do 
    (_, b, _) <- get 
    return b
            
putIndentation b = do
    (a, _, c) <- get
    put (a, b, c)

saveIndentation = do
    (a, _, _) <- get
    putIndentation a

indent = do
    (a, b, _) <- get
    if a /= 0 then error "We Screwed up identation"
    else emit (replicate b ' ')

freshvar = do
    (a, b, c) <- get
    put(a, b, c+1)
    return ("f" ++ show c)

-- specific translation functions

translateLet i e e' = do
    j <- getIndentation
    emit (i ++ " <- ")
    worker e
    newline
    putIndentation j
    indent
    worker e'

translateLambda i e@(Lambda _ _) = do
    saveIndentation
    j <- getIndentation
    emit "P.return P.$ \\"
    emit i
    emit " -> "
    newline
    putIndentation j
    indent
    worker e
translateLambda i e = do
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

translateIf c e e' = do
    saveIndentation
    i <- getIndentation
    var <- freshvar
    emit var
    emit " <- "
    worker c
    newline
    indent
    emit "if "
    emit var
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

translateApp (Free "error") (Text s) = do
    emit "P.return ( P.error "
    emit (show s)
    emit ")"
translateApp (Free s) e = do
    emit "( P.return "
    emit s
    emit " `eapp` "
    worker e
    emit ")"
translateApp e e' = do
    emit "("
    worker e
    emit " `eapp` "
    worker e'
    emit ")"

translateOp op (Free s) (Free s')  = emitOp op s s'
translateOp op (Free s) (Number n) = emitOp op s (show n)
translateOp op (Number n) (Free s) = emitOp op (show n) s
translateOp op e e' = do
    emit "("
    emit (" (" ++ show op ++ ") ")
    emit " P.<$> "
    worker e
    emit " P.<*> "
    worker e'
    emit ")"

emitOp op s s' = do
    emit "P.return ("
    emit s
    emit (" " ++ show op ++ " ")
    emit s'
    emit ")"

translateWhere bindings e = do
    saveIndentation
    i <- getIndentation
    emitBindings bindings True
    newline
    putIndentation i
    indent
    worker e


-- where binding translation

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

emitBindings [] _ = return ()          
emitBindings ((i, Lambda x e):xs) first = do
    when first (emit "let ")
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

----------------------------------------------------