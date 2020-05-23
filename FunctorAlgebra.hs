{-# LANGUAGE DeriveFunctor #-}

module FunctorAlgebra where

-- Fixpoint of functors.
-- See https://bartoszmilewski.com/2017/02/28/f-algebras/

-- Fix   :: (* -> *) -> *
-- Fix   :: f (Fix f) -> Fix f
-- unfix :: Fix f     -> f (Fix f)
newtype Fix f = Fix {unfix::f (Fix f)}

type Algebra f a = f a -> a

-- Catamorphism
cata :: Functor f => Algebra f a -> Fix f -> a
cata alg = alg . fmap (cata alg) . unfix


-- Natural numbers as functor

data NatF a = ZeroF | SuccF a
  deriving (Functor, Show)

--instance Functor NatF where
--  fmap f ZeroF = ZeroF
--  fmap f (SuccF a) = SuccF (f a)


-- Fixed points

zeroFix :: Fix NatF
zeroFix = Fix ZeroF

succFix :: Fix NatF -> Fix NatF
succFix n = Fix (SuccF n)

toNatF :: Int -> Fix NatF
toNatF 0 = zeroFix
toNatF n = succFix (toNatF (n - 1))


-- Fibonacci algebra over NatF with carrier (Int, Int)
fib :: Algebra NatF (Int, Int)
fib ZeroF = (1, 1)
fib (SuccF (m, n)) = (n, n + m)

-- Algebra back to natural numbers
nat :: Algebra NatF Int
nat ZeroF = 0
nat (SuccF n) = n + 1

evalFib :: Fix NatF -> (Int, Int)
evalFib = cata fib

-- evalFib zeroFix
-- = evalFib (Fix ZeroF)
-- = cata fib (Fix ZeroF)
-- = (fib . fmap (cata fib) . unfix) (Fix ZeroF)
-- = (fib . fmap (cata fib)) (unfix (Fix ZeroF))
-- = (fib . fmap (cata fib)) ZeroF
-- = fib (fmap (cata fib) ZeroF)
-- = fib ZeroF
-- = (1, 1)

-- evalFib (succFix zeroFix)
-- = cata fib (Fix (SuccF zeroFix))
-- = (fib . fmap (cata fib) . unfix) (Fix (SuccF zeroFix))
-- = (fib . fmap (cata fib)) (unfix (Fix (SuccF zeroFix)))
-- = (fib . fmap (cata fib)) (SuccF zeroFix)
-- = fib (fmap (cata fib) (SuccF zeroFix))
-- = fib (SuccF ((cata fib) zeroFix))
-- = fib (SuccF ((cata fib) (Fix ZeroF)))
-- = fib (SuccF (1, 1))
-- = (1, 2)

-- F algebra over a list functor

data ListF x xs = Nil | Cons x xs
  deriving (Functor, Show)

--instance Functor (ListF x) where
--  fmap f (Cons x xs) = Cons x (f xs)
--  fmap f Nil = Nil

-- Fixed points

nilFix :: Fix (ListF x)
nilFix = Fix Nil

consFix :: x -> Fix (ListF x) -> Fix (ListF x)
consFix x xs = Fix (Cons x xs)

toListF :: [x] -> Fix (ListF x)
toListF = foldr consFix nilFix
--toListF [] = nilFix
--toListF (x:xs) = consFix x (toListF xs)

-- List algebra over ListF with carrier List
list :: Algebra (ListF x) [x]
list Nil = []
list (Cons x xs) = x:xs

evalList :: Fix (ListF x) -> [x]
evalList = cata list

-- Length algebra over ListF with carrier Int
len :: Algebra (ListF x) Int
len Nil = 0
len (Cons _ n) = 1 + n

evalLen :: Fix (ListF x) -> Int
evalLen = cata len


-- Reverse algebra over ListF with carrier []
reverseL :: Algebra (ListF x) [x]
reverseL Nil = []
reverseL (Cons x xs) = xs ++ [x]

evalReverseL :: Fix (ListF x) -> [x]
evalReverseL = cata reverseL


-- Sum algebra over ListF with carrier Int
sumL :: Num n => Algebra (ListF n) n
sumL Nil = 0
sumL (Cons n s) = n + s

evalSumL :: Num n => Fix (ListF n) -> n
evalSumL = cata sumL

-- deriving fold from the list algebra
mkListAlgebra :: (a -> b -> b) -> b -> Algebra (ListF a) b
mkListAlgebra _ b Nil = b
mkListAlgebra f _ (Cons a b) = f a b

foldList :: (a -> b -> b) -> b -> Fix (ListF a) -> b
foldList f b = cata (mkListAlgebra f b)

-- F algebra for arithmetic

data ExprF a
  = Const Int
  | Add a a
  | Mul a a
  deriving (Functor, Show)

--instance Functor ExprF where
--  fmap f (Const n) = Const n
--  fmap f (Add m n) = Add (f m) (f n)
--  fmap f (Mul m n) = Mul (f m) (f n)

-- Fixed points

constFix :: Int -> Fix ExprF
constFix n = Fix (Const n)

addFix :: Fix ExprF -> Fix ExprF -> Fix ExprF
addFix a b = Fix (Add a b)

mulFix :: Fix ExprF -> Fix ExprF -> Fix ExprF
mulFix a b = Fix (Mul a b)


-- evaluation algebra over ExprF with carrier Int

evalExprF :: Algebra ExprF Int
evalExprF (Const n) = n
evalExprF (Add m n) = m + n
evalExprF (Mul m n) = m * n

evalExpr :: Fix ExprF -> Int
evalExpr = cata evalExprF


-- Tree

data TreeF b a
  = Branch a a
  | Leaf b
  deriving (Functor, Show)

leaf :: b -> Fix (TreeF b)
leaf x = Fix (Leaf x)

branch :: Fix (TreeF b) -> Fix (TreeF b) -> Fix (TreeF b)
branch l r = Fix (Branch l r)

evalTreeF :: Algebra (TreeF Int) String
evalTreeF (Branch xs ys) = "(" ++ xs ++ ys ++ ")"
evalTreeF (Leaf x) = show x

evalTree = cata evalTreeF

countNodesF :: Algebra (TreeF a) Int
countNodesF (Branch l r) = l + r
countNodesF (Leaf _) = 1

countNodes = cata countNodesF

depthF :: Algebra (TreeF a) Int
depthF (Branch l r) = if l > r then l + 1 else r + 1
depthF (Leaf _) = 0

depth = cata depthF


-- Coalgebras
type Coalgebra f a = a -> f a

-- Anamorphism
ana :: Functor f => Coalgebra f a -> a -> Fix f
ana coalg = Fix . fmap (ana coalg) . coalg

type StreamF a = (,) a
type Stream a = Fix (StreamF a)

natsCoalg :: Coalgebra (StreamF Int) Int
natsCoalg n = (n, n + 1)

toListAlg :: Algebra (StreamF a) [a]
-- toListAlg (x, xs) = x:xs
toListAlg = uncurry (:)

toList :: Stream a -> [a]
toList = cata toListAlg

interval :: Int -> Int -> [Int]
interval k n = take n $ toList $ ana natsCoalg k

-- Hylomorphism
hylo :: Functor f => Coalgebra f a -> Algebra f b -> a -> b
hylo coalg alg = alg . fmap (hylo coalg alg) . coalg
-- hylo coalg alg = cata alg . ana coalg

intervalWithHylo :: Int -> Int -> [Int]
intervalWithHylo k n = take n $ hylo natsCoalg toListAlg k





