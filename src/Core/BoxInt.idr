module Core.BoxInt

import Data.Nat

%default total

||| A BoxInt is a signed integer wrapped in a discrete box.
||| It represents concrete particle counts, quadrances, and metric entries
||| in Wildberger's Box Arithmetic.
public export
record BoxInt where
  constructor MkBoxInt
  value : Integer

public export
unwrapBox : BoxInt -> Integer
unwrapBox (MkBoxInt v) = v

public export
intToBoxInt : Integer -> BoxInt
intToBoxInt n = MkBoxInt n

public export
integerToBoxInt : Integer -> BoxInt
integerToBoxInt n = MkBoxInt n

public export
natToBoxInt : Nat -> BoxInt
natToBoxInt n = MkBoxInt (natToInteger n)

||| Exact structural equality for Nat reducing at compile time.
public export
natEq : Nat -> Nat -> Bool
natEq Z Z = True
natEq (S k) (S j) = natEq k j
natEq _ _ = False

||| Exact structural less-than-or-equal comparison for Nat reducing at compile time.
public export
natLTE : Nat -> Nat -> Bool
natLTE Z _ = True
natLTE (S k) Z = False
natLTE (S k) (S j) = natLTE k j

public export
addBox : BoxInt -> BoxInt -> BoxInt
addBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)

public export
subBox : BoxInt -> BoxInt -> BoxInt
subBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a - b)

public export
addBoxLinear : (1 a : BoxInt) -> (1 b : BoxInt) -> BoxInt
addBoxLinear (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)

public export
subBoxLinear : BoxInt -> BoxInt -> BoxInt
subBoxLinear (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a - b)

public export
Num BoxInt where
  (+) (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)
  (*) (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a * b)
  fromInteger n = MkBoxInt n

public export
Neg BoxInt where
  negate (MkBoxInt a) = MkBoxInt (-a)
  (-) (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a - b)

||| Converts a BoxInt absolute value to Nat without typeclass dispatch.
public export
boxToNat : BoxInt -> Nat
boxToNat (MkBoxInt v) =
  case integerToNat v of
    Z => integerToNat (-v)
    S k => S k

||| Computes absolute value of a BoxInt natively without typeclass dispatch.
public export
absBox : BoxInt -> BoxInt
absBox (MkBoxInt v) =
  MkBoxInt (natToInteger (boxToNat (MkBoxInt v)))

public export
Eq BoxInt where
  (MkBoxInt a) == (MkBoxInt b) = a == b




public export
Ord BoxInt where
  compare (MkBoxInt a) (MkBoxInt b) = compare a b

public export
Show BoxInt where
  show (MkBoxInt a) = "[" ++ show a ++ "]"

------------------------------------------------------------------------
-- FAST O(log k) BINARY EXPONENTIATION UTILITIES
------------------------------------------------------------------------

||| Computes integer half of a Nat:
public export
halfNat : Nat -> Nat
halfNat 0 = 0
halfNat 1 = 0
halfNat (S (S n)) = S (halfNat n)

||| Tests if a Nat is odd:
public export
isOddNat : Nat -> Bool
isOddNat 0 = False
isOddNat 1 = True
isOddNat (S (S n)) = isOddNat n

||| Fast binary exponentiation for powers of 2 in O(log k) fuel steps:
public export
fastNatPower2Fuel : (fuel : Nat) -> Nat -> Nat
fastNatPower2Fuel 0 _ = 1
fastNatPower2Fuel (S _) 0 = 1
fastNatPower2Fuel (S fuel) k =
  let half = halfNat k
      halfPow = fastNatPower2Fuel fuel half
      sq = halfPow * halfPow
  in if isOddNat k then sq + sq else sq

||| Fast O(log k) power of 2:
public export
fastNatPower2 : Nat -> Nat
fastNatPower2 k = fastNatPower2Fuel (k + 5) k

||| Fast binary exponentiation for arbitrary base b^k in O(log k) steps:
public export
fastNatPowerFuel : (fuel : Nat) -> (base : Nat) -> (exp : Nat) -> Nat
fastNatPowerFuel 0 _ _ = 1
fastNatPowerFuel (S _) _ 0 = 1
fastNatPowerFuel (S fuel) base exp =
  let half = halfNat exp
      halfPow = fastNatPowerFuel fuel base half
      sq = halfPow * halfPow
  in if isOddNat exp then base * sq else sq

||| Fast O(log k) general exponentiation:
public export
fastNatPower : Nat -> Nat -> Nat
fastNatPower base exp = fastNatPowerFuel (exp + 5) base exp


public export
div : BoxInt -> BoxInt -> BoxInt
div (MkBoxInt a) (MkBoxInt b) = 
  if b == 0 then MkBoxInt 0 else MkBoxInt (a `div` b)

public export
mod : BoxInt -> BoxInt -> BoxInt
mod (MkBoxInt a) (MkBoxInt b) = 
  if b == 0 then MkBoxInt 0 else MkBoxInt (a `mod` b)

||| Direct non-typeclass check for BoxInt zero equality for fast elaborator reduction.
public export
boxZero : BoxInt -> Bool
boxZero (MkBoxInt 0) = True
boxZero _ = False

||| Tests if a BoxInt is strictly positive without typeclass dispatch.
public export
boxPositive : BoxInt -> Bool
boxPositive (MkBoxInt a) =
  case integerToNat a of
    Z => False
    S _ => True

||| Tests if a BoxInt is strictly negative without typeclass dispatch.
public export
boxNegative : BoxInt -> Bool
boxNegative (MkBoxInt a) =
  case integerToNat (-a) of
    Z => False
    S _ => True
