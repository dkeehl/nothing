Church : Type
Church = (a : Type) -> (a -> a) -> a -> a

zero : Church
zero = \ty => \f => \x => x

succ : Church -> Church
succ n = \ty => \f => \x => f (n ty f x)

churchToNat : Church -> Nat
churchToNat n = n Nat S Z

plus : Church -> Church -> Church
plus n m = \ty => \f => \x => n ty f (m ty f x)

mult : Church -> Church -> Church
mult n m = \ty => \f => \x => n ty (m ty f) x

exp : Church -> Church -> Church
exp n m = \ty => \f => \x => m (ty -> ty) (n ty) f x

Boolean : Type
Boolean = (a : Type) -> a -> a -> a

true : Boolean
true = \_ => \x => \_ => x

false : Boolean
false = \_ => \_ => \x => x

isZero : Church -> Boolean
isZero n = n _ (\_ => false) true

Product : (a : Type) -> (b : Type) -> Type
Product a b = (ty : Type) -> (a -> b -> ty) -> ty 

pair : a -> b -> Product a b
pair l r = \_ => \f => f l r

first : Product a b -> a
first p = p _ (\x => \_ => x)

second : Product a b -> b
second p = p _ (\_ => \x => x)

zeroP : Product (a -> a) (a -> a)
zeroP = pair id id

succP : {a : Type} -> (f : a -> a) -> Product (a -> a) (a -> a) -> Product (a -> a) (a -> a)
succP f p = pair (\x => f $ first p x) (first p)

nWithPred : {a : Type} -> (f : a -> a) -> Church -> Product (a -> a) (a -> a) 
nWithPred f n = n _ (succP f) zeroP

pred : Church -> Church
pred n = \_ => \f => \x => second (nWithPred f n) x

-- Premitive recursion


-- General recursion
-- Type of x in Y combinator
record X a where
  constructor Roll
  unRoll : Lazy (X a -> a)

y : (Lazy a -> a) -> a
y f = (\x => f (unRoll x x)) $ Roll (\x => f (unRoll x x))

main : IO ()
main = pure ()
