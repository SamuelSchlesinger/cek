{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module CEK where

data C o v a 
  = Ap (C o v a) (C o v a)
  | Lam a (Maybe Type) (C o v a)
  | Var a
  | Val v
  | Prim o (C o v a) (C o v a)

data E o v a
  = E o v a :+ (a, Value o v a)
  | Nil

lookupE :: Eq a => E o v a -> a -> Maybe (Value o v a)
lookupE (xs :+ (x, y)) x' | x == x'   = Just y
                          | otherwise = lookupE xs x'
lookupE Nil _ = Nothing

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
      Top            -> s
      Arg e' c' k'   -> State c' e' (Fun a c e k')
      PrimArg o _ _ _ -> BadPrim o (Lam a t c)
      PrimFun o _ _ _  -> BadPrimFun o (Lam a t c)
      Fun a' c' e' k' -> State c' (e' :+ (a', Closure a e c)) k'
step s@(State (Val n) _ k)
  = case k of
      Top            -> s
      Arg _ _ _      -> BadApplication (Val n)
      PrimArg o e' c' k' -> State c' e' (PrimFun o n e' k')
      PrimFun o n' e' k' -> State (Val (prim o n' n)) e' k'
      Fun x c' e' k' -> State c' (e' :+ (x, PrimVal n)) k'
step (State (Ap f x) e k)
  = State f e (Arg e x k)
step (State (Prim opCode a b) e k)
  = State a e (PrimArg opCode e b k)
step s | errorState s = s
       | otherwise    = error "The impossible happened!"

eval :: (Eq a, Prim o v, Show a, Show o, Show v) => State o v a -> State o v a
eval = until final step

final :: (Show a, Eq a) => State o v a -> Bool
final (State Lam{} _ Top) = True
final (State Val{}  _ Top) = True
final s | errorState s    = True
final _                   = False

start :: C o v a -> State o v a
start c = State c Nil Top

normalize :: (Prim o v, Show a, Show o, Show v, Eq a) => C o v a -> Maybe (C o v a)
normalize c = case eval $ start c of
  State c' _ _ -> Just $ stripTypes c'
  _ -> Nothing

stripTypes :: C o v a -> C o v a
stripTypes (Lam x _ e) = Lam x Nothing e
stripTypes (Ap f x) = Ap (stripTypes f) (stripTypes x)
stripTypes (Prim o a b) = Prim o (stripTypes a) (stripTypes b)
stripTypes v = v

data OpCode = Add | Sub | Mul
  deriving (Eq, Show)

instance Prim OpCode Integer where
  prim Add = (+)
  prim Sub = (-)
  prim Mul = (*)

type TestTerm = C OpCode Integer Integer

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

terms :: [TestTerm]
terms = [s_, app_, const_, id_, one_, two_, three_]

appTest :: TestTerm -> TestTerm -> Bool
appTest f x = if s == s' then True else False where
  s = normalize $ Ap (Ap app_ f) x 
  s' = normalize $ Ap f x

-- > and [ appTest f x | f <- terms, x <- terms ]

idTest :: TestTerm -> Bool
idTest t = if s == s' then True else False where 
  s  = normalize $ Ap id_ t 
  s' = normalize $ t

-- > and [ idTest t | t <- terms ]

constTest :: TestTerm -> TestTerm -> Bool
constTest c a = if s == s' then True else False where
  s = normalize $ Ap (Ap const_ c) a
  s' = normalize $ c

-- > and [ constTest c a | c <- terms, a <- terms  ]

constIdTest :: TestTerm -> TestTerm -> Bool
constIdTest c a = if s == s' then True else False where
  s = normalize $ Ap (Ap (Ap const_ id_) c) a
  s' = normalize $ Ap id_ a

-- > and [ constIdTest c a | c <- terms, a <- terms ]

addTest :: TestTerm -> TestTerm -> Bool
addTest c a = if s == s' then True else False where
  s = normalize $ Prim Add c a
  s' = normalize $ Prim Add a c

-- > and [ addTest c a | c <- terms, a <- terms ]

addConstTest :: TestTerm -> TestTerm -> Bool
addConstTest c a = if s == s' then True else False where
  s = normalize $ Prim Add c a
  s' = normalize $ Prim Add (Ap (Ap const_ a) one_) c

-- > and [ addConstTest c a | c <- terms, a <- terms ]

-- now, we can make a typechecker for this!

data Type
  = Primitive
  | Function Type Type
  deriving (Show, Eq)

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
typecheck _ (Lam _ Nothing _) = error "do not support leaving out type signature at abstraction sites"
typecheck _ (Prim _ _ _) = Just Primitive

add2_ :: TestTerm
add2_ = Lam 0 (Just Primitive) $ Lam 1 (Just Primitive) $ Prim Add (Var 0) (Var 1)

-- $> typecheck [] add2_ 

deriving instance (Show o, Show v, Show a) => Show (State o v a)
deriving instance (Eq o, Eq v, Eq a) => Eq (State o v a)
deriving instance (Show o, Show v, Show a) => Show (C o v a)
deriving instance (Eq o, Eq v, Eq a) => Eq (C o v a)
deriving instance (Show o, Show v, Show a) => Show (E o v a)
deriving instance (Eq o, Eq v, Eq a) => Eq (E o v a)
deriving instance (Show o, Show v, Show a) => Show (K o v a)
deriving instance (Eq o, Eq v, Eq a) => Eq (K o v a)
deriving instance (Show o, Show v, Show a) => Show (Value o v a)
deriving instance (Eq o, Eq v, Eq a) => Eq (Value o v a)
