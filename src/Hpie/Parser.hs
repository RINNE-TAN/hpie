module Hpie.Parser where

import Data.Functor
import GHC.Base (Alternative (..))
import Hpie.Types

type Input = String

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
    f s = Left $ Unexpected "eof" s

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

charHelper :: [Char] -> Parser Char
charHelper expected = Parser go
  where
    go [] = Left EOF
    go (c : cs) =
      if c `elem` expected
        then Right (cs, c)
        else Left $ Unexpected expected (c : cs)

char :: Char -> Parser ()
char ch = charHelper [ch] $> ()

alpha :: Parser Char
alpha = charHelper (['a' .. 'z'] ++ ['A' .. 'Z'])

number :: Parser Char
number = charHelper ['0' .. '9']

underline :: Parser Char
underline = charHelper ['_']

idChar :: Parser Char
idChar = alpha <|> number <|> underline

ident :: Parser Symbol
ident = do
  idHead <- alpha
  idTail <- many0 idChar
  let s = idHead : idTail
  if s `elem` keywords
    then failure (Unexpected "ident" s)
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
    "Pair",
    "fst",
    "snd",
    "Trivial",
    "Sole",
    "Absurd",
    "IndAbsurd",
    "Bool",
    "True",
    "False",
    "IndBool",
    "IndW",
    "W",
    "U",
    "Sup",
    "Either",
    "Inl",
    "Inr",
    "IndEither",
    "::",
    "==="
  ]

token :: Char -> Parser ()
token c = spaces *> char c

parens :: Parser a -> Parser a
parens p = token '(' *> p <* token ')'

pProg :: Parser [TopLevel]
pProg = many1 ((pCheckSame <|> pClaim <|> pDefine) <* token '.' <* spaces) <* eof

pCheckSame :: Parser TopLevel
pCheckSame = do
  left <- pTerm
  kw "==="
  right <- pTerm
  token ':'
  ty <- pTerm
  return $ CheckSame ty left right

pClaim :: Parser TopLevel
pClaim = Claim <$> (ident <* kw "::") <*> pTerm

pDefine :: Parser TopLevel
pDefine = Define <$> (ident <* token '=') <*> pTerm

-- Atom
pU, pVar, pParens, pTrivial, pSole, pAbsurd, pBool, pTrue, pFalse :: Parser Term
pU = kw "U" $> U
pVar = Var <$> ident
pParens = parens pTerm
pTrivial = kw "Trivial" $> Trivial
pSole = kw "Sole" $> Sole
pAbsurd = kw "Absurd" $> Absurd
pBool = kw "Bool" $> Bool
pTrue = kw "True" $> T
pFalse = kw "False" $> F

pAtom :: Parser Term
pAtom =
  spaces
    *> foldr1
      (<|>)
      [ pU,
        pVar,
        pParens,
        pTrivial,
        pSole,
        pAbsurd,
        pBool,
        pTrue,
        pFalse
      ]

pApp :: Parser Term
pApp = do
  list <- many1 pAtom
  return $ foldl1 App list

pPair, pFirst, pSecond, pIndAbsurd, pIndBool, pW, pSup, pIndW, pEither, pInl, pInr, pIndEither :: Parser Term
pPair = kw "Pair" *> (Pair <$> pAtom <*> pAtom)
pFirst = kw "fst" *> (First <$> pAtom)
pSecond = kw "snd" *> (Second <$> pAtom)
pIndAbsurd = kw "IndAbsurd" *> (IndAbsurd <$> pAtom <*> pAtom)
pIndBool = kw "IndBool" *> (IndBool <$> pAtom <*> pAtom <*> pAtom <*> pAtom)
pW = kw "W" *> (W <$> pAtom <*> pAtom)
pSup = kw "Sup" *> (Sup <$> pAtom <*> pAtom)
pIndW = kw "IndW" *> (IndW <$> pAtom <*> pAtom <*> pAtom)
pEither = kw "Either" *> (Either <$> pAtom <*> pAtom)
pInl = kw "Inl" *> (Inl <$> pAtom)
pInr = kw "Inr" *> (Inr <$> pAtom)
pIndEither = kw "IndEither" *> (IndEither <$> pAtom <*> pAtom <*> pAtom <*> pAtom)

pApply :: Parser Term
pApply =
  foldr1
    (<|>)
    [ pPair,
      pFirst,
      pSecond,
      pIndAbsurd,
      pIndBool,
      pW,
      pSup,
      pIndW,
      pEither,
      pInl,
      pInr,
      pIndEither
    ]

pArrow :: Parser Term
pArrow = do
  arrowHead <- pApp <|> pApply
  optional (kw "->") >>= f arrowHead
  where
    f arrowHead Nothing = return arrowHead
    f arrowHead (Just _) = Arrow arrowHead <$> pTerm

pPi, pLam, pSigma, pCons :: Parser Term
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
  Sigma x a <$> pTerm
pCons = parens (Cons <$> (pTerm <* token ',') <*> pTerm)

pTerm :: Parser Term
pTerm =
  foldr1
    (<|>)
    [ pPi,
      pLam,
      pSigma,
      pCons,
      pArrow
    ]