module Hpie.Parser where

import Data.Char
import Data.Functor
import GHC.Base (Alternative (..))
import Hpie.Types (Symbol, Term (..))

type Input = String

data ParserError = EOF | Unexpected | Internal
  deriving (Show, Eq)

newtype Parser a = Parser
  { runParser :: Input -> Either ParserError (Input, a)
  }

instance Functor Parser where
  fmap f (Parser pa) = Parser (fmap (fmap f) . pa)

instance Applicative Parser where
  pure x = Parser (\i -> Right (i, x))
  (<*>) (Parser pab) (Parser pa) =
    Parser
      ( \i -> do
          (i2, ab) <- pab i
          (i3, a) <- pa i2
          return (i3, ab a)
      )

instance Monad Parser where
  (>>=) (Parser pa) f =
    Parser
      ( \i -> do
          (i2, a) <- pa i
          runParser (f a) i2
      )

instance Alternative Parser where
  empty = Parser (\_ -> Left Internal)
  (<|>) (Parser p1) (Parser p2) =
    Parser
      ( \i -> case p1 i of
          Left _ -> p2 i
          Right r -> Right r
      )

eof :: Parser ()
eof = spaces *> Parser f
  where
    f [] = return ("", ())
    f _ = Left Unexpected

many0 :: Parser a -> Parser [a]
many0 p = many1 p <|> return []

many1 :: Parser a -> Parser [a]
many1 p = do
  ph <- p
  ptails <- many0 p
  return $ ph : ptails

(+++) :: Parser a -> Parser b -> Parser (a, b)
(+++) pa pb = (,) <$> pa <*> pb

failure :: ParserError -> Parser a
failure err = Parser (\_ -> Left err)

ws :: Parser ()
ws = char ' ' <|> char '\n' <|> char '\r' <|> char '\t'

spaces :: Parser ()
spaces = many0 ws $> ()

charHelper :: (Char -> Bool) -> Parser Char
charHelper f = Parser go
  where
    go [] = Left EOF
    go (c : cs) =
      if f c
        then Right (cs, c)
        else Left Unexpected

char :: Char -> Parser ()
char ch = charHelper (== ch) $> ()

alpha :: Parser Char
alpha = charHelper isAlpha

number :: Parser Char
number = charHelper isNumber

underline :: Parser Char
underline = charHelper (== '_')

idChar :: Parser Char
idChar = alpha <|> number <|> underline

ident :: Parser Symbol
ident = do
  idHead <- alpha
  idTail <- many0 idChar
  return $ idHead : idTail

string :: String -> Parser ()
string [] = return ()
string (c : cs) = char c >> string cs $> ()

kw :: String -> Parser ()
kw k =
  if k `elem` keywords
    then spaces *> string k
    else failure Internal
  where
    keywords = ["λ", "Π", "Σ", "α", "β", "Nat", "Zero", "Succ", "IndNat", "U"]

token :: Char -> Parser ()
token c = spaces *> char c

parens :: Parser a -> Parser a
parens p = token '(' *> p <* token ')'

pProg :: Parser Term
pProg = pTerm <* eof

pTerm :: Parser Term
pTerm =
  spaces
    *> foldr1
      (<|>)
      [ pPi,
        pLam,
        pApp,
        pSigma,
        pPair,
        pFirst,
        pSecond,
        pNat,
        pZero,
        pSucc,
        pIndNat,
        pU,
        pParens,
        pVar
      ]

pVar :: Parser Term
pVar = Var <$> ident

pPi :: Parser Term
pPi = do
  _ <- kw "Π"
  (x, a) <- parens ((ident <* char ':') +++ pTerm)
  Pi x a <$> pTerm

pLam :: Parser Term
pLam = do
  _ <- kw "λ"
  x <- parens ident
  Lam x <$> pTerm

pApp :: Parser Term
pApp = parens (App <$> pTerm <*> pTerm)

pSigma :: Parser Term
pSigma = do
  _ <- kw "Σ"
  (x, a) <- parens ((ident <* token ':') +++ pTerm)
  Pi x a <$> pTerm

pPair :: Parser Term
pPair = do
  (f, s) <- parens ((pTerm <* token ',') +++ pTerm)
  return $ Pair f s

pFirst :: Parser Term
pFirst = kw "α" *> (First <$> pTerm)

pSecond :: Parser Term
pSecond = kw "β" *> (Second <$> pTerm)

pNat :: Parser Term
pNat = kw "Nat" $> Nat

pZero :: Parser Term
pZero = kw "Zero" $> Zero

pSucc :: Parser Term
pSucc = kw "Succ" *> (Succ <$> pTerm)

pIndNat :: Parser Term
pIndNat = kw "IndNat" *> (IndNat <$> pTerm <*> pTerm <*> pTerm <*> pTerm)

pU :: Parser Term
pU = kw "U" $> U

pParens :: Parser Term
pParens = parens pTerm