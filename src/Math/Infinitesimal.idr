module Math.Infinitesimal

import Core.BoxInt
import Core.VexelMaxel
import Core.Polynumber

%default total

------------------------------------------------------------------------
-- 1. NILPOTENT INFINITESIMAL MATRIX UNIT (ε² = 0)
------------------------------------------------------------------------

||| The canonical basis infinitesimal token ε as a pure Maxel matrix unit [[0, 1], [0, 0]].
||| Defined as the single basis Pixel [1, 2] with unit weight.
public export
epsilon : Maxel
epsilon = MkMaxel [(MkPixel 1 2, intToBoxInt 1)]

||| Multiplication rule for the infinitesimal token: ε * ε = 0.
||| Computed purely via pixel multiset contraction [1, 2] * [1, 2] => [].
public export
mulEpsilon : Maxel -> Maxel -> Maxel
mulEpsilon e1 e2 = mulMaxel e1 e2

------------------------------------------------------------------------
-- 2. DUAL NUMBERS AS MAXELS
------------------------------------------------------------------------

||| A Dual Number a + b*ε constructed as an upper-triangular Maxel:
||| [[a, b], [0, a]] = a * ([1, 1] + [2, 2]) + b * [1, 2].
public export
dualNumber : (realPart : BoxInt) -> (epsPart : BoxInt) -> Maxel
dualNumber r i =
  MkMaxel [ (MkPixel 1 1, r)
          , (MkPixel 2 2, r)
          , (MkPixel 1 2, i)
          ]

||| Extracts the real scalar part of a Dual Number Maxel.
public export
dualReal : Maxel -> BoxInt
dualReal m = lookupPixel (MkPixel 1 1) m

||| Extracts the nilpotent velocity / derivative part of a Dual Number Maxel.
public export
dualEps : Maxel -> BoxInt
dualEps m = lookupPixel (MkPixel 1 2) m

||| Multiplies two dual numbers via standard Maxel multiset multiplication.
||| (r1 + i1 ε)(r2 + i2 ε) = r1*r2 + (r1*i2 + i1*r2)ε because ε² = 0.
public export
mulDual : Maxel -> Maxel -> Maxel
mulDual d1 d2 = mulMaxel d1 d2

||| Adds two dual numbers using Maxel addition.
public export
addDual : Maxel -> Maxel -> Maxel
addDual d1 d2 = addMaxel d1 d2

||| Scales a dual number by a BoxInt scalar.
public export
scaleDual : BoxInt -> Maxel -> Maxel
scaleDual s d = scaleMaxel s d

------------------------------------------------------------------------
-- 3. DISCRETE AUTOMATIC DIFFERENTIATION VIA DUAL NUMBER MAXELS
------------------------------------------------------------------------

||| Evaluates a Polynumber at a Dual Number Maxel z = a + b*ε.
||| Uses Horner's method with pure Maxel dual addition and multiplication.
public export
evalPolynumberDual : Polynumber -> Maxel -> Maxel
evalPolynumberDual (MkPolynumber cs) z =
  evalListDual cs z
  where
    evalListDual : List BoxInt -> Maxel -> Maxel
    evalListDual [] _ = dualNumber (intToBoxInt 0) (intToBoxInt 0)
    evalListDual (c :: rest) d =
      let restVal = evalListDual rest d
          scaledRest = mulDual d restVal
          constantPart = dualNumber c (intToBoxInt 0)
      in addDual constantPart scaledRest

||| Formal discrete polynomial derivative: d/dx (sum c_k x^k) = sum k * c_k x^(k-1).
public export
formalDerivativePolynumber : Polynumber -> Polynumber
formalDerivativePolynumber (MkPolynumber []) = zeroPolynumber
formalDerivativePolynumber (MkPolynumber (_ :: cs)) =
  let diffList : Nat -> List BoxInt -> List BoxInt
      diffList _ [] = []
      diffList idx (c :: rest) = (natToBoxInt idx * c) :: diffList (S idx) rest
  in trimPolynumber (MkPolynumber (diffList 1 cs))


||| Automatic Differentiation of a Polynumber at a point x = a:
||| Computes (P(a), P'(a)) simultaneously by evaluating P(a + 1*ε).
public export
autoDiffAt : Polynumber -> BoxInt -> (BoxInt, BoxInt)
autoDiffAt p a =
  let z = dualNumber a (intToBoxInt 1)
      res = evalPolynumberDual p z
  in (dualReal res, dualEps res)

||| Audits that Dual Number evaluation computes the exact derivative without continuous limits:
||| For P(x) = 3 + 5x + 2x^2 at x = 4:
||| P(4) = 3 + 20 + 32 = 55.
||| P'(x) = 5 + 4x => P'(4) = 5 + 16 = 21.
||| autoDiffAt P 4 evaluates strictly to (55, 21).
public export
auditAutoDiffProof : Bool
auditAutoDiffProof =
  let p = MkPolynumber [intToBoxInt 3, intToBoxInt 5, intToBoxInt 2] -- 3 + 5x + 2x^2
      (val, deriv) = autoDiffAt p (intToBoxInt 4)
      analyticalDeriv = evalPolynumber (formalDerivativePolynumber p) (intToBoxInt 4)
  in unwrapBox val == 55 && unwrapBox deriv == 21 && deriv == analyticalDeriv
