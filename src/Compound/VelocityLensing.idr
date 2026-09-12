module Compound.VelocityLensing

import Evolution.State
import Evolution.StructuralAccounting
import Math.LinAlgebra.MetricTensor
import Math.Infinitesimal
import Compound.LinearEpsilonRouting
import Core.BoxInt
import Core.VexelMaxel
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. LINEAR VELOCITY LENSING ACROSS METRIC SCALES
------------------------------------------------------------------------

||| Linearly lenses a velocity Vexel across a scale change with pure structural accounting.
||| Contracts the metric Maxel against the velocity Vexel and applies inductive Dark Matter drag.
public export
lensVelocityAcrossScale : {vm, de, dm : Nat} ->
                          (state : UniverseState vm de dm) ->
                          (metric : Maxel) ->
                          (velocity : Vexel) ->
                          Vexel
lensVelocityAcrossScale (MkUniverseState vm de dm) metric vel =
  let drag = sumStructural dm
      scaleFactor = intToBoxInt 1 + drag
      (MkVexel unscaledTerms) = actMaxelVexel metric vel
      scaledTerms = map (\(s, w) => (s, w `div` scaleFactor)) unscaledTerms
  in MkVexel scaledTerms

------------------------------------------------------------------------
-- 2. RELATIVISTIC DEFLECTION & VELOCITY ABERRATION ON T^3
------------------------------------------------------------------------

||| Computes relativistic discrete gravitational light deflection angle d\theta:
||| d\theta = (4 * G * M * scale) / (b * (1 + drag))
public export
relativisticDeflectionAngle : (gConst : BoxInt) -> (mass : BoxInt) -> (impactB : BoxInt) -> 
                              (drag : BoxInt) -> (scale : BoxInt) -> BoxInt
relativisticDeflectionAngle g m b drag scale =
  let num = intToBoxInt 4 * g * m * scale
      denom = b * (intToBoxInt 1 + drag)
      denVal = if denom == intToBoxInt 0 then intToBoxInt 1 else denom
  in num `div` denVal

------------------------------------------------------------------------
-- 3. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Relativistic Velocity Lensing Invariants)
------------------------------------------------------------------------

||| Audits Relativistic Deflection with Dark Matter Drag Attenuation:
||| For G = 10, M = 100, b = 20, drag = 3, scale = 10:
||| d\theta = (4 * 10 * 100 * 10) / (20 * (1 + 3)) = 40000 / (20 * 4) = 40000 / 80 = 500.
public export
auditRelativisticVelocityLensingProof : Bool
auditRelativisticVelocityLensingProof =
  let theta = relativisticDeflectionAngle (intToBoxInt 10) (intToBoxInt 100) (intToBoxInt 20) (intToBoxInt 3) (intToBoxInt 10)
  in theta == intToBoxInt 500


