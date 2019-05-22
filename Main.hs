-- the generic f-algebras
type Algebra f a = f a -> a 

-- gives us the initial algebra for the functor f
newtype Fix f = Iso { invIso :: f (Fix f) } 

-- catamorphism from Fix f to a
-- note that invIso and alg map in opposite directions
cata :: Functor f => Algebra f a -> (Fix f -> a) 
cata alg = alg . fmap (cata alg) . invIso 


-- Natural numbers
type Nat = Fix Maybe

-- every 'Maybe a' has a term Nothing, and Iso maps it into a
zero :: Nat
zero = Iso Nothing 

-- Just maps a to 'Maybe a' and Iso maps back to a new term
successor :: Nat -> Nat
successor = Iso . Just 

-- again the silly f-algebra example from above
pleaseWait :: Algebra Maybe String 
pleaseWait (Just string) = "wait.. " ++ string
pleaseWait Nothing = "go!"

nat :: Algebra Maybe Int
nat (Just n) = n + 1
nat Nothing = 0


-- List algebra 
data ListF a x = Cons a x | Nil 

instance Functor (ListF a) where
  fmap f (Cons x xs) = Cons x (f xs)
  fmap f Nil = Nil
  
type List a = Fix (ListF a)

nil :: List a
nil = Iso Nil

cons :: a -> List a -> List a
cons a as = Iso (Cons a as)

lenAlg :: Algebra (ListF a) Int
lenAlg (Cons a n) = n + 1
lenAlg Nil = 0

listAlg :: Algebra (ListF a) [a]
listAlg (Cons a as) = a:as
listAlg Nil = []
 

-- Expression algebra
data ExprF x a = Lit x | Add a a | Prod a a

instance Functor (ExprF x) where
  fmap f (Lit x) = Lit x
  fmap f (Add x y) = Add (f x) (f y)
  fmap f (Prod x y) = Prod (f x) (f y)
  
type Expr x = Fix (ExprF x)

lit :: x -> Expr x
lit = Iso . Lit

add :: Expr x -> Expr x -> Expr x
add x y = Iso (Add x y)

prod :: Expr x -> Expr x -> Expr x
prod x y = Iso (Prod x y)

evalAlg :: Algebra (ExprF Int) Int
evalAlg (Lit x) = x
evalAlg (Add x y) = x + y
evalAlg (Prod x y) = x * y

ppAlg :: Algebra (ExprF Int) String
ppAlg (Lit x) = show(x)
ppAlg (Add x y) = "(" ++ x ++ "+" ++ y ++ ")"
ppAlg (Prod x y) = "(" ++ x ++ "*" ++ y ++ ")"











