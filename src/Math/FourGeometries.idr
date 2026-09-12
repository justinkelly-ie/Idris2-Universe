module Math.FourGeometries

import public Core.BoxInt
import public Core.VexelMaxel
import public Core.UnixelFraction
import public Math.LinAlgebra.MetricTensor
import public Math.LinAlgebra.TernaryClassifier
import public Compound.HadronicConfinement

%default total

------------------------------------------------------------------------
-- 1. THE 4 FUNDAMENTAL GEOMETRIES OF FINITE COSMOLOGY
------------------------------------------------------------------------

||| The 4 canonical metric geometries governing space, time, gauge, and causality:
||| 1. EllipticGeom  (Blue Sector  / det g = +1 / Spacelike Confinement Canvas)
||| 2. HyperbolicGeom (Red Sector   / det g = -1 / Timelike Non-Abelian Gauge Engine)
||| 3. ParabolicGeom  (Green Sector / det g = 0  / Lightlike Remainder Dissipation Sink)
||| 4. SubstrateGeom  (Causal Poset / g22 = 0, g12 = 1 / Irreversible Cosmological Arrow)
public export
data FundamentalGeometry = 
    EllipticGeom 
  | HyperbolicGeom 
  | ParabolicGeom 
  | SubstrateGeom

public export
Eq FundamentalGeometry where
  EllipticGeom   == EllipticGeom   = True
  HyperbolicGeom == HyperbolicGeom = True
  ParabolicGeom  == ParabolicGeom  = True
  SubstrateGeom  == SubstrateGeom  = True
  _              == _              = False

public export
Show FundamentalGeometry where
  show EllipticGeom   = "Elliptic (Blue, det=+1)"
  show HyperbolicGeom = "Hyperbolic (Red, det=-1)"
  show ParabolicGeom  = "Parabolic (Green, det=0)"
  show SubstrateGeom  = "Substrate (Causal, g22=0)"

------------------------------------------------------------------------
-- 2. CANONICAL MAXEL METRIC TENSORS
------------------------------------------------------------------------

||| Maps each fundamental geometry to its canonical Maxel metric tensor.
%inline
public export
geometryMetric : FundamentalGeometry -> Maxel
geometryMetric EllipticGeom   = gBlue
geometryMetric HyperbolicGeom = gRed
geometryMetric ParabolicGeom  = gBoole
geometryMetric SubstrateGeom  = gSubstrate

||| Computes the exact metric determinant for a fundamental geometry.
%inline
public export
geometryDeterminant : FundamentalGeometry -> BoxInt
geometryDeterminant geom = detMetric (geometryMetric geom)

||| Computes the exact metric trace for a fundamental geometry.
%inline
public export
geometryTrace : FundamentalGeometry -> BoxInt
geometryTrace geom = traceMetric (geometryMetric geom)

||| Evaluates the algebraic Quadrance Q_g(v) of a 2D Vexel under a fundamental geometry:
||| Q_g(v) = v1^2 * g11 + 2 * v1 * v2 * g12 + v2^2 * g22.
%inline
public export
evaluateQuadrance : FundamentalGeometry -> (v1 : BoxInt) -> (v2 : BoxInt) -> BoxInt
evaluateQuadrance geom v1 v2 =
  let g = geometryMetric geom
      g11Val = g11 g
      g12Val = g12 g
      g22Val = g22 g
      term1 = (v1 * v1) * g11Val
      term2 = (intToBoxInt 2 * (v1 * v2)) * g12Val
      term3 = (v2 * v2) * g22Val
  in term1 + term2 + term3

------------------------------------------------------------------------
-- 3. THE 4 GEOMETRIC ACTION THEOREMS
--    Each geometry governs a distinct, non-negotiable physical law
------------------------------------------------------------------------

||| 1. Elliptic Action: Confinement & Positive Quadrance.
||| For any non-zero spatial displacement (1, 0), Q_Elliptic = +1 (strictly positive).
%inline
public export
ellipticConfinementAction : (v1 : BoxInt) -> (v2 : BoxInt) -> BoxInt
ellipticConfinementAction v1 v2 = evaluateQuadrance EllipticGeom v1 v2

||| 2. Hyperbolic Action: Non-Abelian Quantum Phase & Lightcones.
||| Admits lightlike null vectors with zero quadrance (e.g. (1, 1) -> 1 - 1 = 0).
%inline
public export
hyperbolicPhaseAction : (v1 : BoxInt) -> (v2 : BoxInt) -> BoxInt
hyperbolicPhaseAction v1 v2 = evaluateQuadrance HyperbolicGeom v1 v2

||| 3. Parabolic Action: Degenerate Dissipation Channel.
||| Disregards orthogonal direction components (g22 = 0, g12 = 0) allowing remainder drainage.
%inline
public export
parabolicDissipationAction : (v1 : BoxInt) -> (v2 : BoxInt) -> BoxInt
parabolicDissipationAction v1 v2 = evaluateQuadrance ParabolicGeom v1 v2

||| 4. Substrate Action: Irreversible Causal Arrow.
||| Satisfies g22 = 0 (no temporal feedback) and g12 = 1 (unidirectional matter bias).
%inline
public export
substrateCausalArrowAction : Maxel -> Bool
substrateCausalArrowAction g =
  g22 g == intToBoxInt 0 && g12 g == intToBoxInt 1

------------------------------------------------------------------------
-- 4. COSMIC BUDGET DECOMPOSITION ACROSS THE 4 GEOMETRIES
------------------------------------------------------------------------

||| Decomposes the 4th Primorial budget (210) across the Chromogeometric Triad and Substrate:
||| - Elliptic Blue Sector     = 27  (3^3 Spacetime Lattice Basis)
||| - Hyperbolic Red Sector    = 128 (2^7 Symplectic Law ROM)
||| - Parabolic Green Sector   = 55  (Accumulated Dark Matter Residue)
||| Total Budget = 27 + 128 + 55 = 210 = 2 * 3 * 5 * 7.
%inline
public export
cosmicBudgetByGeometry : FundamentalGeometry -> Nat
cosmicBudgetByGeometry EllipticGeom   = 27
cosmicBudgetByGeometry HyperbolicGeom = 128
cosmicBudgetByGeometry ParabolicGeom  = 55
cosmicBudgetByGeometry SubstrateGeom  = 210

||| Evaluates the exact rational chance proportion of each geometry.
%inline
public export
cosmicChanceByGeometry : FundamentalGeometry -> UnixelFraction
cosmicChanceByGeometry geom =
  let tally = cosmicBudgetByGeometry geom
  in if geom == SubstrateGeom
       then unitUnixelFraction
       else hehnerTallyToChance tally 210

------------------------------------------------------------------------
-- 5. CONSTRUCTIVE FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits the Determinant Classification of the 4 Geometries:
||| det(Elliptic)   = +1
||| det(Hyperbolic) = -1
||| det(Parabolic)  = 0
||| det(Substrate)  = -1 (with asymmetric g22 = 0)
%inline
public export
auditFourGeometriesDeterminantsProof : Bool
auditFourGeometriesDeterminantsProof =
  let detEll = geometryDeterminant EllipticGeom
      detHyp = geometryDeterminant HyperbolicGeom
      detPar = geometryDeterminant ParabolicGeom
      detSub = geometryDeterminant SubstrateGeom
  in detEll == intToBoxInt 1 &&
     detHyp == intToBoxInt (-1) &&
     detPar == intToBoxInt 0 &&
     detSub == intToBoxInt (-1)

||| Audits the Cosmic Synthesis of the 4 Geometries:
||| 1. Quadrance of (1, 1) under Hyperbolic is exactly 0 (Lightcone).
||| 2. Quadrance of (1, 0) under Elliptic is exactly 1 (Confinement).
||| 3. Budget partition 27 + 128 + 55 == 210 (Primorial 210).
public export
auditFourGeometriesCosmicSynthesisProof : Bool
auditFourGeometriesCosmicSynthesisProof =
  let one = intToBoxInt 1
      zero = intToBoxInt 0
      qHyp = hyperbolicPhaseAction one one
      qEll = ellipticConfinementAction one zero
      bTotal = cosmicBudgetByGeometry EllipticGeom +
               cosmicBudgetByGeometry HyperbolicGeom +
               cosmicBudgetByGeometry ParabolicGeom
      okHyp = qHyp == intToBoxInt 0
      okEll = qEll == intToBoxInt 1
      okTot = natEq bTotal 210
  in okHyp && okEll && okTot
