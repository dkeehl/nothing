{-# LANGUAGE Rank2Types #-}
import Prelude hiding (succ, pred)

newtype Nat = N { un :: forall a . (a -> a) -> a -> a }
zero :: Nat
zero = N (\f x -> x)

succ :: Nat -> Nat
succ n = N (\f x -> f (un n f x))

one :: Nat
one = succ zero

plus :: Nat -> Nat -> Nat
plus n m = un m succ n

mult :: Nat -> Nat -> Nat
mult n m = un m (plus n) zero

pow :: Nat -> Nat -> Nat
pow n m = un m (mult n) one

pair :: a -> b -> (a -> b -> t) -> t
pair l r f = f l r

first :: a -> b -> a
first l r = l

second :: a -> b -> b
second l r = r

-- Now we can define the predecessor function
zero_p :: (Nat -> Nat -> Nat) -> Nat
zero_p = pair zero zero
succ_p :: ((Nat -> Nat -> Nat) -> Nat) -> (Nat -> Nat -> Nat) -> Nat
succ_p p = pair (succ $ p first) (p first)

pred :: Nat -> Nat
pred n = un n succ_p zero_p second

minus :: Nat -> Nat -> Nat
minus n m = un m pred n

type Boolean = forall a. a -> a -> a 

true :: Boolean
true x y = x

false :: Boolean
false x y = y

ifb :: Boolean -> a -> a -> a
ifb = id   -- \b -> b in lambada form. We don't really need it. 

isZero :: Nat -> Boolean
isZero n = un n (\b -> false) true

-- to define the Y combinator in haskell, we need iso-recursive types.
-- See http://jozefg.bitbucket.org/posts/2013-11-09-iso-recursive-types.html 
newtype Mu f = Mu { unMu :: f (Mu f) }
newtype X' b a = X' { unX :: a -> b }
type X a = Mu (X' a)
unroll = unX . unMu
roll = Mu . X'

y :: (a -> a) -> a
y = \f -> (\x -> f (unroll x x)) $ roll (\x -> f (unroll x x))

divi :: Nat -> Nat -> Nat
divi = y divi'
  where
    divi' self n m = isZero (minus n m) zero (succ $ self (minus n m) m)

-- Converters
churchToInt :: Nat -> Int
churchToInt n = un n (+ 1) 0

main :: IO ()
main = do
    let two = succ $ succ zero
    let three = succ $ succ $ succ zero
    let five = succ $ succ $ succ $ succ $ succ zero
    print $ churchToInt (divi five two)
