module RegexParser where

import Control.Applicative
import Control.Monad

import Data.Functor.Identity

import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

import Regex

type Parser a = ParsecT String () Identity a

regex :: Parser Coq_regex
regex = buildExpressionParser ops atom
        where
          atom = msum [ Chr <$> noneOf "*+?|()"
                      , parens lexer regex ]
          ops = [ [ Postfix (Star <$ char '*')
                  ]
                , [ Infix (return Cat) AssocRight ]
                , [ Infix (Choice <$ char '|') AssocRight] ]


lexer :: GenTokenParser String a Identity
lexer = makeTokenParser haskellDef

parseRegex :: String -> Either ParseError Coq_regex
parseRegex = parse regex "" 
