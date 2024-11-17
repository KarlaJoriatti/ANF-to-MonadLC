{-# LANGUAGE FlexibleContexts #-}
module ParserCalculus where

import System.IO
import Data.Char
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Control.Monad.RWS

newtype TI a   = TI (Int -> (a, Int))

data Expr = Free String
          | Number Integer
          | Text String
          | UnitValue
          | TrueValue
          | FalseValue
          | Let String Expr Expr
          | Lambda String Expr
          | If Expr Expr Expr
          | Application Expr Expr
          | Operation ParserCalculus.Operator Expr Expr
          | Where [(String, Expr)] Expr
        --   | Handler String [(Maybe String, Expr)] Expr


-- TODO: Change it for Application.
data Operator = Sum
              | Sub
              | Mul
              | Div
              | Lt
              | Gt
              | Eq
              | EqEq

data Type = Int
          | Bool
          | String
          | Unit
          | Generic String
          | Arrow Type Type Type -- tipo efeito tipo a -> e b
          -- | Constant String [Type]
          -- | Ref Type
          | Console
          -- | Foo
          -- | Bar
          -- | Pure
          -- | State
          | Row [Effect]
          -- | Computation Type Effect
          deriving (Ord, Eq)
         
type Effect = Type

instance Show Type where
    show Bool = "Bool"
    show Int = "Int"
    show String = "String"
    show Unit = "()"
    show (Generic i) = i
    show (Arrow t e t') = show t ++ " -> " ++ show e ++ " " ++ show t'
    show (Row ls) = show ls
    show (Console) = "Console"

instance Show Expr where
    show expr = 
       let (_, _, w) = runRWS (worker expr) () (0, 0) in w
       where
           worker (Free s) = do
               emit "return "
               emit s
           worker (Number n) = do
               emit "return "
               emit (show n)
           worker (Text s) = do
               emit "return "
               emit (show s)
           worker (UnitValue) = do
               emit "return ()"
           worker (TrueValue) = do
               emit "return True"
           worker (FalseValue) = do
               emit "return False"
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
               emit "\\"
               emit i
               emit " -> "
               newline
               putIndentation j
               indent
               emit " "
               emit "return $ "
               worker exp
           worker (Lambda i e) = do
               saveIndentation
               j <- getIndentation
               emit "\\"
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
               let s = runTI (freshVar) i
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
           worker (Application (Free s) e') = do
               emit "( return "
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
               emit "return ("
               emit s
               emit (" " ++ show op ++ " ")
               emit s'
               emit ")"
           worker (Operation op e e') = do
               emit "("
               emit (" (" ++ show op ++ ") ")
               emit "<$> "
               worker e
               emit " <*> "
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
               emit "return $ \\"
               emit i
               i <- getIndentation
               emit " -> "
               emitMultiBind e
           emitMultiBind e = do
               emit "do "
               newline
               indent
               case e of
                 Free s -> emit ("return " ++ s)
                 _ -> worker e
           
           emitBindings [] f = return ()          
           emitBindings ((i, (Lambda x e)):xs) f = do
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
               when (length xs /= 0) $ do
	          newline
	          putIndentation j
	          indent
	          emitBindings xs False

    
instance Show ParserCalculus.Operator where
    show ParserCalculus.Sum = " + "
    show Sub = " - "
    show Mul = " * "
    show Div = " `div` "
    show Lt  = " < "
    show Gt  = " > "
    show Eq  = " = "
    show EqEq = " == "

instance Functor TI where
   fmap f (TI m) = TI (\e -> let (a, e') = m e in (f a, e'))

instance Applicative TI where
   pure a = TI (\e -> (a, e))
   TI fs <*> TI vs = TI (\e -> let (f, e') = fs e; (a, e'') = vs e' in (f a, e''))              

instance Monad TI where 
   return x = TI (\e -> (x, e))
   TI m >>= f  = TI (\e -> let (a, e') = m e; TI fa = f a in fa e')


freshVar :: TI Type
freshVar = TI (\e -> let v = "t"++show e in (Generic v, e+1))

runTI (TI m) n = let (t, _) = m n in t 

lingDef = emptyDef
          {
            T.identStart = letter <|> char '_'
            , T.identLetter = alphaNum
            , T.reservedNames = ["let", "where", "in", "if", "then", "else", "true", "false", "effect", "bool", "int", "string", "unit", "handler"]
            , T.reservedOpNames = ["=", "_", "+", "->", ":", "\8594", ".", "\8704", "<", ">"]
          }

lexico        = T.makeTokenParser lingDef
reserved      = T.reserved lexico
reservedOp    = T.reservedOp lexico
identifier    = T.identifier lexico
natural       = T.integer lexico
stringLiteral = T.stringLiteral lexico

juntar = foldr (\(a,b) (c,d) -> (a++c, b++d)) ([],[])

partida = do {l <- many bigParser; eof; return (juntar l)}

bigParser = try (do {e <- many1 effectParser; funs <- many parseFunctions; hand <- many handlerParse; return (e, funs)})
           <|> do {funs <- many1 parseFunctions; e <- many effectParser; hand <- many handlerParse; return (e, funs)}
           <|> do {hand <- many1 handlerParse; e <- many effectParser; funs <- many parseFunctions; return (e, funs)}

pp = do {reservedOp "_"; return ()}

handlerParse = do reserved "handler"
                  i <- identifier
                  x <- many pp
                  y <- many identifier
                  reservedOp "{"
                  j <- many parseHandlers
                  reservedOp "}"
                  return ()

parseHandlers = do i <- identifier
                   x <- many pp
                   y <- many identifier
                   reservedOp "="
                   e <- highParser
                   return ()

parseFunctions = do (nome, tipo) <- declParser
                    i <- identifier
                    x <- many pp
                    y <- many identifier
                    reservedOp "="
                    e' <- highParser
                    return (nome, tipo, e')

parseExpr = runParser partida [] "calculus"

varParser = do {i <- identifier; return (Free i)}

textParser = do {i <- stringLiteral; return (Text i)}

lambdaParser = do char '\\'
                  i <- many identifier
                  reservedOp "->"
                  e <- highParser
                  exp <- constructLambda i e
                  return exp
                    
unitP = do reservedOp "("
           reservedOp ")"
           return (UnitValue)
           
numberParser = do i <- natural
                  return (Number i)
                  
trueParser = do reserved "true"
                return (TrueValue)

falseParser = do reserved "false"
                 return (FalseValue)

boolParser = do trueParser
             <|> falseParser
             
operator = do {reservedOp "+"; return (ParserCalculus.Sum)}
           <|> do {reservedOp "-"; return (Sub)}
           <|> do {reservedOp "/"; return (Div)}
           <|> do {reservedOp "*"; return (Mul)}
           <|> do {reservedOp "<"; return (Lt)}
           <|> do {reservedOp ">"; return (Gt)}
           <|> do {reservedOp "="; return (Eq)}
           <|> do {reservedOp "=="; return (EqEq)}

opParser = do reservedOp "("
              e <- highParser
              i <- operator
              e' <- highParser
              reservedOp ")"
              return (Operation i e e')
                  
ifParser = do reserved "if"
              c <- highParser
              reserved "then"
              e <- highParser
              reserved "else"
              e' <- highParser
              return (If c e e')

letParser = do reserved "let"
               i <- identifier
               reservedOp "="
               e <- highParser
               reserved "in"
               e' <- highParser
               return (Let i e e')

bindings = do i <- identifier
              ls <- many identifier
              reservedOp "="
              e' <- highParser
              exp <- constructLambda ls e'
              return (i, exp)

whereParser = do e <- parseNonApp
                 reserved "where"
                 reservedOp "{"
                 ass <- many bindings
                 reservedOp "}"
                 return (Where ass e)

arrowParser = do t <- typeParser
                 reservedOp "\8594" -- arrow
                 e <- eff
                 t' <- ordParser
                 return (Arrow t e t')
                 
eff = try (do {reserved "console"; return (Console)})
        <|> try (rowParser)
        <|> genericEffect

genericEffect = do (x:xs) <- identifier
                   return (Generic ((toUpper x):xs))

ef = do reservedOp ","
        e <- eff
        return e

rowParser = do reservedOp "<"
               e <- eff
               ls <- many ef
               reservedOp ">"
               return (Row (e:ls))

genericParser = do i <- identifier
                   return (Generic i)

ordParser = try (arrowParser)
            <|> typeParser

typeParser = try (do {reserved "bool"; return (Bool)})
               <|> try (do {reserved "int"; return (Int)})
               <|> try (do {reserved "unit"; return (Unit)})
               <|> try (do {reserved "string"; return (String)})
               -- <|> try (do {reserved "console"; return (Console)})
               -- <|> try (arrowParser)
               -- <|> try (rowParser)
               <|> genericParser

declParser = do i <- identifier
                x <- many pp
                l <- many identifier
                reservedOp ":"
                reservedOp "\8704" -- forall
                many identifier
                reservedOp "."
                t <- ordParser
                case l of
                  [] -> return (i, t)
                  (x:xs) -> return (i++x, t)
                

effectParser = do reserved "effect"
                  i <- identifier
                  reservedOp "{"
                  decls <- many declParser
                  reservedOp "}"
                  return (i, decls)

constructLambda [] e = return e
constructLambda [x] e = return (Lambda x e)
constructLambda (x:xs) e = do e' <- constructLambda xs e
                              return (Lambda x e')
                              
takeInput (Lambda i e) = (i ++ " " ++ x, y)
  where (x, y) = takeInput e 
takeInput e = ("", e)

expr :: Parsec String u Expr
expr = chainl1 (between spaces spaces highParser) $ return $ Application

appParser = do reservedOp "("
               e <- expr
               reservedOp ")"
               return e

highParser = try (whereParser)
             <|> parseNonApp

parseNonApp = try (opParser)
              <|> try (appParser)
              <|> unitP
              <|> ifParser
              <|> numberParser
              <|> boolParser
              <|> lambdaParser
              <|> letParser
              <|> varParser
              <|> textParser

-------- saida -----------

cabecalho = "{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeOperators, DataKinds, RankNTypes #-} \nimport Control.Eff\nimport Control.Eff.Extend\nimport Debug.Trace\n\n"
--"handlerAction :: r ~ (f : r') => (forall v.(f v -> (v -> k) -> k) -> (Eff r a -> k) -> Arrs r v a -> f v -> k)\nhandlerAction f h q elem =\n\tf elem (qComp q h)\n\nmakeHandler :: r ~ (f : r') => (forall v.f v -> (v -> s -> Eff r' b) -> s -> Eff r' b) -> (a -> s -> Eff r' b) -> s -> Eff r a -> Eff r' b\nmakeHandler f g =\n\tPrelude.flip (handle_relay' (handlerAction f) g (Prelude.flip $ makeHandler f g))\n\n"

eapp = "eapp :: Monad m => m (a -> m b) -> m a -> m b\neapp f x = do\n   res <- f <*> x\n   res\n\n"

console = "data Console x where\n    Print :: x -> Console ()\n\nprint x = send (Print x)\n\n"

takeEfs t [a, b] = return ([a], "Member " ++ show a ++ " " ++ show t)
takeEfs t (e : es) = do (a, b) <- takeEfs t es
                        return (e:a, "Member " ++ show e ++ " " ++ show t ++ "," ++ b)

joinStrs a b | a == [] = b
             | b == [] = a
             | otherwise = a ++ "," ++ b


teste (Row efs) f = do t <- freshVar
                       case efs of
                         [x, y] -> if f then return (show x ++ " ", []) else return ("Eff " ++ show t ++ " ", "Member " ++ show x ++ " " ++ show t)
                         _ -> do (ls, str) <- takeEfs t efs
                                 return ("Eff " ++ show t ++ " ", str)
teste (Arrow Unit e t) f = do (a, b) <- teste e f
                              (a1, b1) <- teste t f
                              return (a ++ a1, joinStrs b b1)
teste (Arrow t1 (Generic i) t2@(Arrow a b c)) f = do t <- freshVar
                                                     (a, b) <- teste t1 f
                                                     (a2, b2) <- teste t2 f
                                                     if f 
                                                     then return (a ++ "-> " ++ a2, joinStrs b b2)
                                                     else return (a ++ "-> Eff " ++ show t ++ " (" ++ a2 ++ ")", joinStrs b b2)
teste (Arrow t1 e t2@(Arrow a b c)) f = do (a, b) <- teste t1 f
                                           (a1, b1) <- teste e f
                                           (a2, b2) <- teste t2 f
                                           return (a ++ "-> " ++ a1 ++"("++ a2 ++ ")", joinStrs b (joinStrs b1 b2))
teste (Arrow t1 (Generic i) t2) f = do t <- freshVar
                                       (a, b) <- teste t1 f
                                       (a2, b2) <- teste t2 f
                                       return (a ++ "-> Eff " ++ show t ++ " " ++ a2, joinStrs b b2)
teste (Arrow t1 e t2) f = do (a, b) <- teste t1 f
                             (a1, b1) <- teste e f
                             (a2, b2) <- teste t2 f
                             return (a ++ "-> " ++ a1 ++ a2, joinStrs b (joinStrs b1 b2))
teste t f = return (show t ++ " ", [])

--tipoEx = Arrow (Generic "a") (Row [Generic "State", Generic "b"]) (Arrow Bool (Row [Generic "Amb", Generic "State", Generic "c"]) Unit)

countParams (Arrow t (Generic i) t') = 1 + countParams t'
countParams _ = 1

sendParams 0 = ""
sendParams i = "return (\\x" ++ show i ++ " -> " ++ sendParams (i-1)

params 0 = ""
params n = "x" ++ show n ++ " " ++ params (n-1)

createSend hd [] = return ()
createSend hd ((nome@(c:cs), tipo):xs) = do hPutStr hd (nome ++ " ")
		                            case tipo of
		                               (Arrow Unit _ _) -> do {hPutStr hd ("() = send " ++ [toUpper c] ++ cs); hPutStrLn hd ""}
		                               t -> do let n = countParams t
		                                       if n > 1
		                                       then 
		                                         do let a = sendParams (n-1)
		                                                p = params (n-1)
		                                            hPutStr hd "x0 = "
		                                            hPutStr hd a
		                                            hPutStr hd ("send (" ++ [toUpper c] ++ cs ++ " x0 ")
		                                            hPutStr hd p
		                                            hPutStrLn hd (concat (take n (repeat ")")))
		                                       else hPutStrLn hd ("x0 = send (" ++ [toUpper c] ++ cs ++ " x0)")
		                            createSend hd xs

saidaDeclaracoes _ [] = return ()
saidaDeclaracoes hd ((c:cs, tipo):xs) = do hPutStr hd "   "
                                           let name = [toUpper c] ++ cs
                                           saidaDecl hd name tipo
                                           saidaDeclaracoes hd xs

takeFunctions [] [] _ = return ()
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
takeFunctions ((nomef, _, _):xs) ((nomee, _):ys) hd = do hPutStr hd nomef
                                                         hPutStr hd ", "
                                                         hPutStr hd nomee
                                                         hPutStr hd ", "
                                                         takeFunctions xs ys hd

saidaEfeitos hs [] = return ()
saidaEfeitos hd ((c:cs, listaDeclaracoes):xs) = do hPutStrLn hd ("data " ++ [toUpper c] ++ cs ++ " x where")
                                                   saidaDeclaracoes hd listaDeclaracoes
                                                   hPutStrLn hd ""
                                                   createSend hd listaDeclaracoes
                                                   hPutStrLn hd ""
                                                   saidaEfeitos hd xs 


saidaDecl hd nome tipo = do let (typee, constraints) = runTI (teste tipo (isUpper (head nome))) 0
                            if constraints == []
                            then hPutStrLn hd (nome ++ " :: " ++ typee)
                            else hPutStrLn hd (nome ++ " :: (" ++ constraints ++ ") => " ++ typee)


saidaFuncoes hd [] = return ()
saidaFuncoes hd ((nome, tipo, fun):xs) = do saidaDecl hd nome tipo
                                            hPutStr hd (nome ++ " = ")
                                            hPutStrLn hd (show fun)
                                            hPutStrLn hd ""
                                            saidaFuncoes hd xs

saida (listaEfeitos, listaFuncoes) = do handle <- openFile "converted.hs" WriteMode
                                        hPutStr handle cabecalho
                                        hPutStr handle "import Prelude hiding (print,"
                                        takeFunctions listaFuncoes (concat(snd (unzip listaEfeitos))) handle
                                        hPutStr handle console
                                        saidaEfeitos handle listaEfeitos
                                        hPutStrLn handle eapp
                                        saidaFuncoes handle listaFuncoes
                                        hClose handle

parseCalculus s = case parseExpr s of
                     Left er -> print er
                     Right e -> saida e
 
main = do putStrLn "Arquivo: "
          x <- getLine
          s <- readFile x
          parseCalculus s