module Parser where

import Data.Char
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language

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
          | Operation Parser.Operator Expr Expr
          | Where [(String, Expr)] Expr
        --   | Handler String [(Maybe String, Expr)] Expr
          deriving Show


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
          | Console
          | Row [Effect]
          deriving (Ord, Eq)

type Effect = Type

instance Show Parser.Operator where
    show Parser.Sum = " P.+ "
    show Sub = " P.- "
    show Mul = " P.* "
    show Div = " `P.div` "
    show Lt  = " P.< "
    show Gt  = " P.> "
    show Eq  = " P.= "
    show EqEq = " P.== "

instance Show Type where
    show Bool = "P.Bool"
    show Int = "P.Int"
    show String = "P.String"
    show Unit = "()"
    show (Generic i) = i
    show (Arrow t e t') = show t ++ " -> " ++ show e ++ " " ++ show t'
    show (Row ls) = show ls
    show Console = "Console"

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

partida = do {l <- many1 bigParser; eof; return (juntar l)}

bigParser = try (do {e <- many1 effectParser; return (e, [])})
           <|> do {funs <- many1 parseFunctions; return ([], funs)}
           <|> do {hand <- many1 handlerParse; return ([], [])}

pp = do {reservedOp "_"; return ()}

-- we are ignoring handlers
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

varParser = do {Free <$> identifier;}

textParser = do {Text <$> stringLiteral;}

lambdaParser = do char '\\'
                  i <- many identifier
                  reservedOp "->"
                  e <- highParser
                  constructLambda i e

unitP = do reservedOp "("
           reservedOp ")"
           return UnitValue

numberParser = do Number <$> natural

trueParser = do reserved "true"
                return TrueValue

falseParser = do reserved "false"
                 return FalseValue

boolParser = do trueParser
             <|> falseParser

operator = do {reservedOp "+"; return Parser.Sum}
           <|> do {reservedOp "-"; return Sub}
           <|> do {reservedOp "/"; return Div}
           <|> do {reservedOp "*"; return Mul}
           <|> do {reservedOp "<"; return Lt}
           <|> do {reservedOp ">"; return Gt}
           <|> do {reservedOp "="; return Eq}
           <|> do {reservedOp "=="; return EqEq}

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
              If c e <$> highParser

letParser = do reserved "let"
               i <- identifier
               reservedOp "="
               e <- highParser
               reserved "in"
               Let i e <$> highParser

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
                 Arrow t e <$> ordParser

eff = try (do {reserved "console"; return Console})
        <|> try rowParser
        <|> genericEffect

genericEffect = do (x:xs) <- identifier
                   return (Generic (toUpper x:xs))

ef = do reservedOp ","
        eff

rowParser = do reservedOp "<"
               e <- eff
               ls <- many ef
               reservedOp ">"
               return (Row (e:ls))

genericParser = do Generic <$> identifier

ordParser = try arrowParser
            <|> typeParser

typeParser = try (do {reserved "bool"; return Bool})
               <|> try (do {reserved "int"; return Int})
               <|> try (do {reserved "unit"; return Unit})
               <|> try (do {reserved "string"; return String})
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
expr = chainl1 (between spaces spaces highParser) $ return Application

appParser = do reservedOp "("
               e <- expr
               reservedOp ")"
               return e

highParser = try whereParser
             <|> parseNonApp

parseNonApp = try opParser
              <|> try appParser
              <|> unitP
              <|> ifParser
              <|> numberParser
              <|> boolParser
              <|> lambdaParser
              <|> letParser
              <|> varParser
              <|> textParser
