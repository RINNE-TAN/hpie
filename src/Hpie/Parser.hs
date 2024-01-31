module Hpie.Parser where

import Data.Char
import Data.Functor
import GHC.Base (Alternative (..))
import Hpie.Types (Symbol, Term (..), TopLevel (..))

type Input = String

data ParserError = EOF | Unexpected String | Internal
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
    f s = Left $ Unexpected s

many0 :: Parser a -> Parser [a]
many0 p = many1 p <|> return []

many1 :: Parser a -> Parser [a]
many1 p = do
  ph <- p
  ptails <- many0 p
  return $ ph : ptails

optional :: Parser a -> Parser (Maybe a)
optional pa = (Just <$> pa) <|> return Nothing

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
        else Left $ Unexpected (c : cs)

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
  let s = idHead : idTail
  if s `elem` keywords
    then failure (Unexpected s)
    else return s

string :: String -> Parser ()
string [] = return ()
string (c : cs) = char c >> string cs $> ()

kw :: String -> Parser ()
kw k =
  if k `elem` keywords
    then spaces *> string k <* spaces
    else failure Internal

keywords :: [String]
keywords =
  [ "λ",
    "Π",
    "Σ",
    "->",
    "Cons",
    "First",
    "Second",
    "Nat",
    "Zero",
    "Succ",
    "IndNat",
    "U",
    "Claim",
    "Define",
    "CheckSame",
    "==="
  ]

token :: Char -> Parser ()
token c = spaces *> char c

parens :: Parser a -> Parser a
parens p = token '(' *> p <* token ')'

pProg :: Parser [TopLevel]
pProg = many1 (pCheckSame <|> pClaim <|> pDefine) <* eof

pCheckSame :: Parser TopLevel
pCheckSame = do
  kw "CheckSame"
  left <- pTerm
  kw "==="
  right <- pTerm
  token ':'
  ty <- pTerm
  return $ CheckSame ty left right

pClaim :: Parser TopLevel
pClaim = kw "Claim" *> (Claim <$> ident <*> pTerm)

pDefine :: Parser TopLevel
pDefine = kw "Define" *> (Define <$> ident <*> pTerm)

-- Atom
pNat, pZero, pU, pVar, pParens :: Parser Term
pNat = kw "Nat" $> Nat
pZero = kw "Zero" $> Zero
pU = kw "U" $> U
pVar = Var <$> ident
pParens = parens pTerm

pAtom :: Parser Term
pAtom =
  spaces
    *> foldr1
      (<|>)
      [ pNat,
        pZero,
        pU,
        pVar,
        pParens
      ]

pApp :: Parser Term
pApp = do
  list <- many1 pAtom
  return $ foldl1 App list

pCons, pFirst, pSecond, pSucc, pIndNat :: Parser Term
pCons = kw "Cons" *> (Cons <$> pAtom <*> pAtom)
pFirst = kw "First" *> (First <$> pAtom)
pSecond = kw "Second" *> (Second <$> pAtom)
pSucc = kw "Succ" *> (Succ <$> pAtom)
pIndNat = kw "IndNat" *> (IndNat <$> pAtom <*> pAtom <*> pAtom <*> pAtom)

pApply :: Parser Term
pApply =
  foldr1
    (<|>)
    [ pCons,
      pFirst,
      pSecond,
      pSucc,
      pIndNat
    ]

pArrow :: Parser Term
pArrow = do
  arrowHead <- pApp <|> pApply
  optional (kw "->") >>= f arrowHead
  where
    f arrowHead Nothing = return arrowHead
    f arrowHead (Just _) = Arrow arrowHead <$> pTerm

pPi, pLam, pSigma :: Parser Term
pPi = do
  _ <- kw "Π"
  (x, a) <- parens ((ident <* token ':') +++ pTerm)
  Pi x a <$> pTerm
pLam = do
  _ <- kw "λ"
  x <- parens ident
  Lam x <$> pTerm
pSigma = do
  _ <- kw "Σ"
  (x, a) <- parens ((ident <* token ':') +++ pTerm)
  Pi x a <$> pTerm

pTerm :: Parser Term
pTerm =
  foldr1
    (<|>)
    [ pPi,
      pLam,
      pSigma,
      pArrow
    ]