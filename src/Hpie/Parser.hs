module Hpie.Parser where

import Control.Monad.State
import Data.Functor
import Hpie.Types

keywords :: [String]
keywords = ["U", "data"]

data PState = PState
  { tyConNames :: [Symbol],
    dataConNames :: [Symbol],
    curInput :: String
  }

type Parser = StateT PState (Either ParserError)

initState :: String -> PState
initState input = PState {tyConNames = [], dataConNames = [], curInput = input}

runParser :: Parser a -> String -> Either ParserError (a, PState)
runParser p i = runStateT p (initState i)

nothing :: Parser ()
nothing = return ()

failure :: ParserError -> Parser a
failure err = StateT (\_ -> Left err)

(<|>) :: Parser a -> Parser a -> Parser a
(<|>) (StateT pa) (StateT pb) =
  StateT
    ( \s -> case pa s of
        Left _ -> pb s
        success -> success
    )

(<+>) :: Parser a -> Parser b -> Parser (a, b)
(<+>) pa pb = (,) <$> pa <*> pb

choice :: [Parser a] -> Parser a
choice = foldr (<|>) (failure Internal)

many0 :: Parser a -> Parser [a]
many0 p = many1 p <|> return []

many1 :: Parser a -> Parser [a]
many1 p = do
  ph <- p
  ptails <- many0 p
  return $ ph : ptails

optional :: Parser a -> Parser (Maybe a)
optional pa = (Just <$> pa) <|> return Nothing

chain :: Parser a -> Parser (a -> a -> a) -> Parser a
chain p op = do
  pHead <- p
  rest pHead
  where
    rest x =
      do
        f <- op
        y <- p
        rest (f x y)
        <|> return x

eof :: Parser ()
eof = do
  i <- gets curInput
  case i of
    [] -> return ()
    _ -> failure (Unexpected [] i)

char :: Parser Char
char = do
  st <- get
  case curInput st of
    [] -> failure EOF
    (c : cs) -> do
      put st {curInput = cs}
      return c

litChar :: Char -> Parser Char
litChar c = do
  c' <- char
  if c == c' then return c else failure (Unexpected [c] [c'])

choiceChar :: [Char] -> Parser Char
choiceChar cs = choice (litChar <$> cs)

ident :: Parser Symbol
ident = do
  idHead <- alpha
  idTail <- many0 idChar
  return (idHead : idTail)
  where
    alpha = choiceChar (['a' .. 'z'] ++ ['A' .. 'Z'])
    number = choiceChar ['0' .. '9']
    underline = choiceChar ['_']
    idChar = alpha <|> number <|> underline

string :: String -> Parser ()
string [] = return ()
string (c : cs) = litChar c >> string cs $> ()

token :: Parser a -> Parser a
token p = p <* spaces
  where
    ws = litChar ' ' <|> litChar '\n' <|> litChar '\r' <|> litChar '\t' *> nothing
    spaces = many0 ws $> ()

tokens :: String -> Parser ()
tokens s = token (string s) *> nothing

parens :: Parser a -> Parser a
parens p = tokens "(" *> p <* tokens ")"

brackets :: Parser a -> Parser a
brackets p = tokens "[" *> p <* tokens "]"

braces :: Parser a -> Parser a
braces p = tokens "{" *> p <* tokens "}"

variable :: Parser Symbol
variable = do
  i <- token ident
  tnames <- gets tyConNames
  cnames <- gets dataConNames
  if i `elem` keywords || i `elem` tnames || i `elem` cnames
    then failure (Unexpected "variable" i)
    else return i

tyName :: Parser Symbol
tyName = do
  i <- token ident
  tnames <- gets tyConNames
  if i `elem` tnames
    then return i
    else failure (Unexpected "ty name" i)

dataName :: Parser Symbol
dataName = do
  i <- token ident
  dnames <- gets dataConNames
  if i `elem` dnames
    then return i
    else failure (Unexpected "data name" i)

pU :: Parser Term
pU = tokens "U" $> U

pVarOrCon :: Parser Term
pVarOrCon = do
  i <- token ident
  tnames <- gets tyConNames
  dnames <- gets dataConNames
  if i `elem` tnames
    then return (TyCon i [])
    else
      if i `elem` dnames
        then return (DataCon i [])
        else return (Var i)

pPi :: Parser Term
pPi = do
  (x, ty) <-
    brackets
      ( (variable <* tokens ":")
          <+> pTerm
      )
  tokens "=>"
  Pi x ty <$> pTerm

pSigma :: Parser Term
pSigma = braces $ do
  x <- variable
  tokens ":"
  ty <- pTerm
  tokens "|"
  Sigma x ty <$> pTerm

pLam :: Parser Term
pLam = do
  tokens "\\"
  binds <- many1 variable
  tokens "."
  body <- pTerm
  return $ foldr Lam body binds

pProd :: Parser Term
pProd =
  parens
    ( do
        left <- pTerm
        tokens ","
        Prod left <$> pTerm
    )

pParens :: Parser Term
pParens = parens pTerm

pAtom :: Parser Term
pAtom = choice [pU, pVarOrCon, pPi, pSigma, pLam, pProd, pParens]

pFirst :: Parser Term
pFirst = do
  pair <- pAtom
  tokens ".0"
  return $ First pair

pSecond :: Parser Term
pSecond = do
  pair <- pAtom
  tokens ".1"
  return $ Second pair

pApp :: Parser Term
pApp = do
  list <- many1 (pFirst <|> pSecond <|> pAtom)
  return $ foldl1 App list

pTyCon :: Parser Term
pTyCon = do
  symbol <- tyName
  TyCon symbol <$> many0 pAtom

pDataCon :: Parser Term
pDataCon = do
  symbol <- dataName
  DataCon symbol <$> many0 pAtom

pApply :: Parser Term
pApply = pTyCon <|> pDataCon <|> pApp

pArrow :: Parser Term
pArrow = chain pApply (tokens "->" $> Arrow)

pPair :: Parser Term
pPair = chain pArrow (tokens "*" $> Arrow)

pTerm :: Parser Term
pTerm = pPair

pIsANonDep :: Parser Entry
pIsANonDep = IsA "_" <$> pTerm

pIsA :: Parser Entry
pIsA =
  do
    var <- variable
    tokens ":"
    IsA var <$> pTerm

pDef :: Parser Entry
pDef =
  do
    var <- variable
    tokens "="
    Def var <$> pTerm

pTele :: Parser Tele
pTele = many0 (parens pIsANonDep <|> parens pIsA <|> brackets pDef)

pDataDef :: Parser DataDef
pDataDef = do
  var <- variable
  tele <- pTele
  modify (\s -> s {dataConNames = var : dataConNames s})
  return $ DataDef var tele

pTyDef :: Parser Entry
pTyDef = do
  token (string "data")
  var <- variable
  tele <- pTele
  tokens "where"
  modify (\s -> s {tyConNames = var : tyConNames s})
  TyDef var tele <$> many0 (tokens "|" *> pDataDef)

pProg :: Parser [Entry]
pProg =
  many0
    ( (pTyDef <|> pIsA <|> pDef)
        <* tokens "."
    )
    <* eof

-- terms:
--   a,b,A,B ::=
--     U                        Universe
--   | x                        Variables
--   | \x y z . a               Lambda
--   | a b                      Application
--   | [x : A] => B             Pi type
--   | A -> B                   Nondependent Pi type
--   | {x : A | B}              Sigma type
--   | A * B                    Nondependent Sigma type
--   | (a)                      Parens
--   | a.0                      First
--   | a.1                      Second
--   | C arg ...                Data/Ty Constructor

-- telescopes:
--   D ::=
--                              Empty
--    | (x : A) D               Relevant, dependent argument
--    | (A) D                   Relevent, nondependent argument
--    | [x = b] D

-- declarations:

--     foo : A.                 Type declaration
--     foo = a.                 Definition

--     data T D where          Type constructor, with telescope
--        | C1 D1              Data constructor, with telescope
--        ...
--        | Cn Dn
--     .