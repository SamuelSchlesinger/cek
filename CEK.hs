{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module CEK where

import Data.List hiding ((\\))
import Data.Maybe

data C o v a 
  = Ap (C o v a) (C o v a)
  | Lam a (Maybe Type) (C o v a)
  | Var a
  | Val v
  | Let a (C o v a) (C o v a)
  | Prim o (C o v a) (C o v a)

type E o v a = [(a, Value o v a)]

subst :: Eq a => E o v a -> C o v a -> C o v a
subst env (Ap f x) = Ap (subst env f) (subst env x)
subst env (Lam a t b) = Lam a t (subst (env \\ a) b)
subst env (Var a) = maybe (Var a) fromValue $ lookupE env a where
  fromValue :: Eq a => Value o v a -> C o v a
  fromValue (PrimVal v) = Val v
  fromValue (Closure a' env' c) = Lam a' Nothing (subst env' c)
subst _ (Val n) = Val n
subst env (Prim o x y) = Prim o (subst env x) (subst env y)
subst env (Let a x b) = Let a (subst env x) (subst (env \\ a) b)

removeLets :: C o v a -> C o v a
removeLets (Ap f x) = Ap (removeLets f) (removeLets x)
removeLets (Lam a t b) = Lam a t (removeLets b)
removeLets (Var a) = Var a
removeLets (Val a) = Val a
removeLets (Let a x b) = Ap (Lam a Nothing b) x
removeLets (Prim o a b) = Prim o (removeLets a) (removeLets b)

(\\) :: Eq a => E o v a -> a -> E o v a
e \\ a' = filter ((/= a') . fst) e

lookupE :: Eq a => E o v a -> a -> Maybe (Value o v a)
lookupE = flip lookup
               
data K o v a 
  = Arg (E o v a) (C o v a) (K o v a)
  | Top
  | Fun a (C o v a) (E o v a) (K o v a)
  | PrimArg o (E o v a) (C o v a) (K o v a)
  | PrimFun o v (E o v a) (K o v a)

data State o v a 
  = State (C o v a) (E o v a) (K o v a)
  | FailedLookup a 
  | BadApplication (C o v a) 
  | BadPrim o (C o v a) 
  | BadPrimFun o (C o v a)

errorState :: State o v a -> Bool
errorState (State _ _ _) = False
errorState _ = True

class Prim o v where
  prim :: o -> v -> v -> v

data Value o v a = Closure a (E o v a) (C o v a) | PrimVal v

step :: (Prim o v, Eq a) => State o v a -> State o v a
step (State (Var a) e k) 
  = case lookupE e a of
      Just (Closure x e' c') -> State (Lam x Nothing c') e' k
      Just (PrimVal n) -> State (Val n) e k
      Nothing -> FailedLookup a
step s@(State (Lam a t c) e k)
  = case k of
      Top            -> case e of
        [] -> s 
        _   -> State (Lam a t (subst (e \\ a) c)) [] k
      Arg e' c' k'   -> State c' e' (Fun a c e k')
      PrimArg o _ _ _ -> BadPrim o (Lam a t c)
      PrimFun o _ _ _  -> BadPrimFun o (Lam a t c)
      Fun a' c' e' k' -> State c' ((a', Closure a e c) : e') k'
step (State (Val n) e k)
  = case k of
      Top            -> State (Val n) [] Top
      Arg _ _ _      -> BadApplication (Val n)
      PrimArg o e' c' k' -> State c' e' (PrimFun o n e k')
      PrimFun o n' e' k' -> State (Val (prim o n' n)) e' k'
      Fun x c' e' k' -> State c' ((x, PrimVal n) : e') k'
step (State (Ap f x) e k)
  = State f e (Arg e x k)
step (State (Prim opCode a b) e k)
  = State a e (PrimArg opCode e b k)
-- I derived this by the identity (Ap (Lam a t b) x) ~ Let a x b.
-- It is also kind of clear from what the Fun continuation means,
-- but I constantly get this stuff wrong so I wanted to do it this
-- way. I love having such a strenuous test suite. 
step (State (Let a x b) e k)
  = State x e (Fun a b e k) 
step s | errorState s = s
       | otherwise    = error "The impossible happened!"

eval :: (Eq a, Prim o v) => State o v a -> State o v a
eval = until final step

final :: Eq a => State o v a -> Bool
final (State Lam{} [] Top) = True
final (State Val{} [] Top) = True
final s = errorState s

start :: C o v a -> State o v a
start c = State c [] Top

normalize :: (Prim o v, Eq a) => C o v a -> Maybe (C o v a)
normalize c = case eval $ start c of
  State c' _ _ -> Just $ stripTypes c'
  _ -> Nothing

exec :: (Prim o v, Eq a) => C o v a -> State o v a
exec = help . eval . start where
  help = \case
    State a b c -> State (stripTypes a) b c
    s -> s

stripTypes :: C o v a -> C o v a
stripTypes (Lam x _ e) = Lam x Nothing e
stripTypes (Ap f x) = Ap (stripTypes f) (stripTypes x)
stripTypes (Prim o a b) = Prim o (stripTypes a) (stripTypes b)
stripTypes v = v

data OpCode = Add | Sub | Mul | Mod | Div | Exp
  deriving (Eq, Show, Enum, Bounded)

instance Integral n => Prim OpCode n where
  prim Add = (+)
  prim Sub = (-)
  prim Mul = (*)
  prim Mod = mod
  prim Div = div
  prim Exp = (^)

type TestTerm = C OpCode Int Int

id_ :: TestTerm
id_ = Lam 0 (Just Primitive) (Var 0)

const_ :: TestTerm
const_ = Lam 0 (Just Primitive) (Lam 1 (Just Primitive) (Var 0))

app_ :: TestTerm
app_ = Lam 0 (Just Primitive) (Lam 1 (Just Primitive) (Ap (Var 0) (Var 1)))

s_ :: TestTerm
s_ = Lam 0 (Just Primitive) $ Lam 1 (Just Primitive) $ Lam 2 (Just Primitive) $ Ap (Ap (Var 0) (Var 2)) $ Ap (Var 1) (Var 2)

one_ :: TestTerm
one_ = Val 1

two_ :: TestTerm
two_ = Val 2

three_ :: TestTerm
three_ = Val 3

add2_ :: TestTerm
add2_ = Lam 0 (Just Primitive) $ Lam 1 (Just Primitive) $ Prim Add (Var 0) (Var 1)

mul2_ :: TestTerm
mul2_ = Lam 0 (Just Primitive) $ Lam 1 (Just Primitive) $ Prim Mul (Var 0) (Var 1)

terms :: [TestTerm]
terms = [s_, app_, const_, id_, one_, two_, three_, add2_, mul2_]

appTest :: TestTerm -> TestTerm -> Bool
appTest f x = if s == s' then True else False where
  s = exec $ Ap (Ap app_ f) x 
  s' = exec $ Ap f x

appTests :: Bool
appTests = and [ appTest f x | f <- terms, x <- terms ]

idTest :: TestTerm -> Bool
idTest t = if s == s' then True else False where 
  s  = exec $ Ap id_ t 
  s' = exec $ t

idTests :: Bool
idTests = and [ idTest t | t <- terms ]

constTest :: TestTerm -> TestTerm -> Bool
constTest c a = if s == s' then True else False where
  s = exec $ Ap (Ap const_ c) a
  s' = exec $ c

constTests :: Bool
constTests = and [ constTest c a | c <- terms, a <- terms  ]

constIdTest :: TestTerm -> TestTerm -> Bool
constIdTest c a = if s == s' && s' == s'' then True else False where
  s = exec $ Ap (Ap (Ap const_ id_) c) a
  s' = exec $ Ap id_ a
  s'' = exec a

constIdTests :: Bool
constIdTests = and [ constIdTest c a | c <- terms, a <- terms ]

numberTerms :: [TestTerm]
numberTerms = [one_, two_, three_]

addTest :: TestTerm -> TestTerm -> Bool
addTest c a = if s == s' then True else False where
  s = exec $ Prim Add c a
  s' = exec $ Prim Add a c

addTests :: Bool
addTests = and [ addTest c a | c <- numberTerms, a <- numberTerms ]

addConstTest :: TestTerm -> TestTerm -> Bool
addConstTest c a = if s == s' then True else False where
  s = exec $ Prim Add c a
  s' = exec $ Prim Add (Ap (Ap const_ c) one_) a

addConstTests :: Bool
addConstTests = and [ addConstTest c a | c <- numberTerms, a <- numberTerms ]

-- now, we can make a typechecker for this!

data Type
  = Primitive
  | Function Type Type
  deriving (Show, Eq)

interleave :: [a] -> [a] -> [a]
interleave [] as = as
interleave (x : xs) as = x : interleave as xs 

-- doesn't include let expressions
termsOfType :: (Eq o, Eq v, Eq a, Enum o, Enum a, Bounded v, Enum v) => [a] -> Type -> [C o v a]
termsOfType free ty = go free [] ty where
  go as vars Primitive = [ Val v  | v <- [minBound..maxBound]  ] 
            `interleave` [ Var v  | v <- map fst $ filter ((== Primitive) . snd) vars ]
            `interleave` [ Ap f x | t <- manyTypes, f <- termsOfType as (Function t Primitive), x <- termsOfType as t ]
  go (a : as) vars (Function t t') = [ Lam a (Just t) b | b <- go as ((a, t) : vars) t' ]
                        `interleave` [ Var v | v <- map fst $ filter ((== Function t t') . snd) vars ]
  go [] _ _ = error "ran out of free variables"

typecheck :: Eq a => [(a, Type)] -> C o v a -> Maybe Type
typecheck _       (Val _) = Just Primitive
typecheck context (Var a) = lookup a context 
typecheck context (Ap f x) = do
  Function s t <- typecheck context f
  s' <- typecheck context x
  if s == s' then Just t else Nothing
typecheck context (Lam x (Just s) e) = do
  t <- typecheck ((x, s) : context) e
  return (Function s t)
typecheck _ (Lam _ Nothing _) 
  = error "typechecking does not support leaving out type signature at abstraction sites"
typecheck _ (Prim _ _ _) = Just Primitive
typecheck context (Let a x b) = do
  xt <- typecheck context x
  bt <- typecheck ((a, xt) : context) b
  return bt

n_ :: Int
n_ = 100

wellTypedTest :: Type -> Bool
wellTypedTest t = (== 1) . length . group . take n_ 
                $ [ fromJust $ typecheck [] c | c :: TestTerm <- termsOfType [1..] t ]

manyTypes :: [Type]
manyTypes = nub $ interleave (go True) (go False) where
  go :: Bool -> [Type]
  go b = [Primitive] ++ do
    x <- manyTypes
    y <- manyTypes
    return $ if b then Function x y else Function y x 

wellTypedTests :: Bool
wellTypedTests = all wellTypedTest $ take n_ manyTypes

termsOfTypeTest :: Bool
termsOfTypeTest = and $ do
  t <- take n_ manyTypes
  term :: TestTerm <- take n_ $ termsOfType [1..] t
  pure $ if typecheck [] term == Just t then True else False

wellTypedTermsTerminate :: Bool
wellTypedTermsTerminate = all (not . errorState) $ do
  t <- take n_ manyTypes
  term :: TestTerm <- take n_ $ termsOfType [1..] t
  return . eval . start $ term

simpleLetTest :: TestTerm -> Bool
simpleLetTest a = s == s' && not (errorState s || errorState s') where
  s = exec (Let 0 a (Var 0))
  s' = exec a

simpleLetTests :: Bool
simpleLetTests = and $ do
  x <- take n_ manyTypes
  t <- take n_ $ termsOfType [1..] x
  return $ simpleLetTest t

testRewriteRule :: (TestTerm -> TestTerm) -> Bool
testRewriteRule rule = and $ do
  x <- take n_ manyTypes
  t :: TestTerm <- take n_ $ termsOfType [1..] x
  let s = exec t
  let s' = exec $ rule t
  let mtt = typecheck [] t
  case mtt of
    Just tt -> return $ s == s' && tt == x
    Nothing -> return False

tests :: Bool
tests = and 
  [ wellTypedTermsTerminate
  , simpleLetTests
  , testRewriteRule removeLets
  , termsOfTypeTest
  , wellTypedTests
  , addTests
  , addConstTests
  , constIdTests
  , constTests
  , idTests
  , appTests ]

-- $> tests

deriving instance (Show o, Show v, Show a) => Show (State o v a)
deriving instance (Eq o, Eq v, Eq a) => Eq (State o v a)
deriving instance (Show o, Show v, Show a) => Show (C o v a)
deriving instance (Eq o, Eq v, Eq a) => Eq (C o v a)
deriving instance (Show o, Show v, Show a) => Show (K o v a)
deriving instance (Eq o, Eq v, Eq a) => Eq (K o v a)
deriving instance (Show o, Show v, Show a) => Show (Value o v a)
deriving instance (Eq o, Eq v, Eq a) => Eq (Value o v a)
