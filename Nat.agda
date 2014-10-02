module Nat where

data ℕ : Set where
    zero : ℕ
    succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}
--for Agda < 2.4.0
--{-# BUILTIN ZERO zero #-}
--{-# BUILTIN SUC succ #-}

one   = succ zero
two   = succ one
three = succ two
four  = succ three
five  = succ four

data Top : Set where
    tt : Top

data Bot : Set where

infix 2 _==_
data _==_ {A : Set} : A -> A -> Set where
    refl : {n : A} -> n == n

transport : {A : Set} {x y : A} -> (P : A -> Set) -> P x -> x == y -> P y
transport P x refl = x

sym : {A : Set} {x y : A} -> x == y -> y == x
sym {A} {x} {y} x==y = transport (λ w -> w == x) refl x==y
--sym refl = refl

trans : {A : Set} {x y z : A} -> x == y -> y == z -> x == z
trans {A} {x} {y} {z} x==y y==z = transport (λ w -> w == z) y==z (sym x==y)
--trans refl refl = refl

cong : {A B : Set} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
cong {A} {B} {x} {y} f x==y = transport (λ w -> f w == f y) refl (sym x==y)
--cong f refl = refl

ind : (P : ℕ -> Set) -> P zero -> ((n : ℕ) -> P n -> P (succ n)) -> (n : ℕ) -> P n
ind P pz pnext zero = pz
ind P pz pnext (succ n) = pnext n (ind P pz pnext n)

pred : ℕ -> ℕ
--pred zero = zero
--pred (succ a) = a
pred a = ind (λ w -> ℕ) zero (λ n pn -> n) a

--infixr 5 _+_
--_+_ : ℕ -> ℕ -> ℕ
--zero + b     = b
--(succ a) + b = succ (a + b)

infixr 5 _+_
_+_ : ℕ -> ℕ -> ℕ
a + b = ind (λ w -> ℕ) b (λ n pn -> (succ pn)) a

--ind P pz pnext (succ n) = pnext n   (ind P pz pnext n)
--      b           a             a-1                 a-1
--                                    |    b + (a-1)   |
--                                    |      pn        |

succ-functional : {x y : ℕ} -> x == y -> succ x == succ y
succ-functional x==y = cong succ x==y

succ-injective : {x y : ℕ} -> succ x == succ y -> x == y
succ-injective refl = refl

infixr 1 _=[_]_
_=[_]_ : {A : Set} {y z : A} -> (x : A) -> x == y -> y == z -> x == z
_ =[ b ] c = trans b c

infix 2 _#
_# : {A : Set} (x : A) -> x == x
x # = refl

add-zero : (a : ℕ) -> a == a + zero
add-zero zero     = refl
add-zero (succ a) = cong succ (add-zero a)

add-succ : (x y : ℕ) -> succ (x + y) == x + succ y
add-succ zero     y =
    succ (zero + y)
    =[ refl ]
    succ y
    =[ refl ]
    zero + succ y #

add-succ (succ x) y =
    succ (succ x + y)
    =[ refl ]
    succ (succ (x + y))
    =[ cong succ (add-succ x y) ]
    succ (x + succ y)
    =[ refl ]
    succ x + succ y #

add-comm : (a b : ℕ) -> (a + b) == (b + a)
add-comm zero     y =
    zero + y
    =[ refl ]
    y
    =[ add-zero y ]
    y + zero #

add-comm (succ x) y =
    succ x + y
    =[ refl ]
    succ (x + y)
    =[ cong succ (add-comm x y) ]
    succ (y + x)
    =[ add-succ y x ]
    y + succ x #
