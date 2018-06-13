module Nothing

%default total

record Church where
  constructor MkNat
  natF : {a : Type} -> (a -> a) -> a -> a

zero : Church
zero = MkNat $ \_ => \x => x

succ : Church -> Church
succ n = MkNat $ \f => \x => f (natF n f x)

one : Church
one = succ zero

churchToNat : Church -> Nat
churchToNat n = natF n S Z

plus : Church -> Church -> Church
plus n m = natF m succ n

mult : Church -> Church -> Church
mult n m = natF m (plus n) zero 

exp : Church -> Church -> Church
exp n m = natF m (mult n) one

Product : (a : Type) -> (b : Type) -> Type
Product a b = (ty : Type) -> (a -> b -> ty) -> ty 

pair : a -> b -> Product a b
pair l r = \_ => \f => f l r

first : Product a b -> a
first p = p _ (\x => \_ => x)

second : Product a b -> b
second p = p _ (\_ => \x => x)

-- Define predecessor and subtraction
zeroP : Product Church Church
zeroP = pair zero zero 

succP : Product Church Church -> Product Church Church
succP p = pair (succ $ first p) (first p)

nWithPred : Church -> Product Church Church
nWithPred n = natF n succP zeroP

pred : Church -> Church
pred = second . nWithPred

minus : Church -> Church -> Church
minus n m = natF m pred n

-- Primitive recursion
start : a -> Product Church a
start x = pair zero x

step : (Church -> a -> a) -> Product Church a -> Product Church a
step f p = pair (succ $ first p) (f (succ $ first p) (second p))

pr : Church -> ty -> (h : Church -> ty -> ty) -> ty
pr n g h = second $ natF n (step h) (start g)

-- Zero test
Boolean : Type
Boolean = {a : Type} -> a -> a -> a

true : Boolean
true = \x => \_ => x

false : Boolean
false = \_ => \x => x

isZero : Church -> Boolean
isZero n = natF n (\_ => false) true

-- Search from 0 to n for the least number q that n - m * q <= 0
div' : Church -> Church -> Church
div' n m = pr n zero (\q => \pre => isZero (minus n $ mult m pre) pre q)

div : Church -> Church -> Church
div n m = isZero m zero (div' n m)

-- Some other data types
Atom : Type
Atom = (a: Type) -> a -> a

atom : Atom
atom = \_ => \x => x

Sum : Type -> Type -> Type
Sum a b = (ty: Type) -> (a -> ty) -> (b -> ty) -> ty

left : a -> Sum a b
left x = \_ => \l => \r => l x

right : b -> Sum a b
right x = \_ => \l => \r => r x

match : (ty: Type) -> Sum a b -> (a -> ty) -> (b -> ty) -> ty
match ty sum l r = sum ty l r

Option : Type -> Type
Option a = Sum Atom a

none : Option a
none = left atom

some : a -> Option a
some = right

-- An example of option
unpack : (a: Type) -> Option a -> (default: a) -> a
unpack a opt default = match a            -- a indicates the returning type
                             opt
                             (\_ => default) -- the `none` case
                             (\x => x)       -- the `some` case

-- Nat is a recursive type,
-- `Nat = Sum Atom Nat` will not reduce during typechecking.
namespace RecursiveType
  record MuType (f: Type -> Type) where
    constructor Mu
    unMu : f (MuType f)

  N : Type
  N = MuType (Sum Atom)

  partial zero : N
  zero = Mu $ left atom

  partial succ : N -> N
  succ n = Mu $ right n

  -- examples
  partial pred : N -> N
  pred n = match N (unMu n) (\_ => zero) (\x => x)

  B : Type
  B = Sum Atom Atom

  true : B
  true = left atom

  false : B
  false = right atom

  partial isZero : N -> B
  isZero n = match B (unMu n) (\_ => true) (\_ => false)

-- General recursion
-- Type of x in Y combinator
record X a where
  constructor Roll
  unRoll : Lazy (X a -> a)

partial y : (Lazy a -> a) -> a
y f = (\x => f (unRoll x x)) $ Roll (\x => f (unRoll x x))

