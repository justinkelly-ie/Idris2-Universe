module Observation.Scientific

import Core.BoxInt
import Core.VexelMaxel
import Core.UnixelFraction

%default total

------------------------------------------------------------------------
-- 1. SCIENTIFIC OBSERVATION RECORD & SCHEMA
------------------------------------------------------------------------

||| A Scientific Observation pairs an exact theoretical rational attractor
||| with an experimentally measured rational bounding interval [lower, upper]
||| and academic citation metadata.
public export
record ScientificObservation where
  constructor MkScientificObservation
  quantityName         : String
  associatedLaw        : Nat
  exactTheory          : UnixelFraction
  measuredLower        : UnixelFraction
  measuredUpper        : UnixelFraction
  unitDimension        : String
  experimentalCitation : String
  experimentalDOI      : String

public export
Eq ScientificObservation where
  (MkScientificObservation q1 l1 t1 low1 up1 u1 c1 doi1) == (MkScientificObservation q2 l2 t2 low2 up2 u2 c2 doi2) =
    q1 == q2 && l1 == l2 && u1 == u2 && c1 == c2 && doi1 == doi2

public export
Show ScientificObservation where
  show (MkScientificObservation q l t low up u c doi) =
    "ScientificObservation(" ++ q ++ " [Law " ++ show l ++ "]" ++
    " | Theory: " ++ show (num t) ++ "/" ++ show (index (den t)) ++ " " ++ u ++
    " | Measured: [" ++ show (num low) ++ "/" ++ show (index (den low)) ++
    ", " ++ show (num up) ++ "/" ++ show (index (den up)) ++ "]" ++
    " | Ref: " ++ c ++ ")"

------------------------------------------------------------------------
-- 2. EXACT RATIONAL INTERVAL CONSISTENCY
------------------------------------------------------------------------

||| Evaluates whether fraction f1 is less than or equal to f2 using cross-multiplication:
||| (n1 / d1) <= (n2 / d2) <=> n1 * d2 <= n2 * d1 (since d1, d2 > 0)
public export
rationalLTE : UnixelFraction -> UnixelFraction -> Bool
rationalLTE (MkUnixelFraction n1 (MkUnixel d1)) (MkUnixelFraction n2 (MkUnixel d2)) =
  let lhs = n1 * natToBoxInt d2
      rhs = n2 * natToBoxInt d1
  in lhs <= rhs

||| Evaluates whether fraction f1 is greater than or equal to f2:
public export
rationalGTE : UnixelFraction -> UnixelFraction -> Bool
rationalGTE f1 f2 = rationalLTE f2 f1

||| Evaluates whether the theoretical value sits strictly within the empirical bounds:
||| measuredLower <= exactTheory <= measuredUpper
public export
isEmpiricallyConsistent : ScientificObservation -> Bool
isEmpiricallyConsistent obs =
  let theory = exactTheory obs
      lower  = measuredLower obs
      upper  = measuredUpper obs
  in rationalGTE theory lower && rationalLTE theory upper

||| Evaluates whether measuredLower <= measuredUpper (valid experimental interval):
public export
isValidInterval : ScientificObservation -> Bool
isValidInterval obs =
  rationalLTE (measuredLower obs) (measuredUpper obs)
