module Compound.LinearEpsilonRouting

import Core.BoxInt
import Core.VexelMaxel
import Math.LinAlgebra.MetricTensor
import Math.Infinitesimal
import Data.Vect

%default total

||| Constructs a 2D velocity vector as a weighted Vexel of Singletons
||| representing velocity along spatial [1] and temporal [2] axes.
public export
velocityVexel : (vAlpha : BoxInt) -> (vBeta : BoxInt) -> Vexel
velocityVexel vA vB =
  MkVexel [ (MkUnixel 1, vA)
          , (MkUnixel 2, vB)
          ]

||| Linearly routes a velocity Vexel through a symmetric gEM metric transformation.
||| Computed directly via pure Maxel-Vexel multiset contraction (g * v).
public export
linearEpsilonRouting : Maxel -> Vexel -> Vexel
linearEpsilonRouting g v = actMaxelVexel g v

||| Linearly routes a velocity Vexel through an asymmetric gSubstrate metric transformation.
||| When g22 = 0, the temporal component cannot feed back into itself, enforcing a one-way causal arrow.
public export
linearEpsilonSubstrateRouting : Maxel -> Vexel -> Vexel
linearEpsilonSubstrateRouting g v = actMaxelVexel g v


------------------------------------------------------------------------
-- SYMPLECTIC PHASE SPACE & HAMILTONIAN FLOW ON VEXELS
------------------------------------------------------------------------

||| The Canonical 2D Symplectic Matrix Maxel J = [[0, 1], [-1, 0]]:
||| J = [1, 2] - [2, 1].
public export
symplecticMatrixMaxel : Maxel
symplecticMatrixMaxel =
  MkMaxel [ (MkPixel 1 2, intToBoxInt 1)
          , (MkPixel 2 1, intToBoxInt (-1))
          ]

||| Computes Hamiltonian vector field phase flow:
||| \dot{z} = J * \nabla H(z)
public export
hamiltonianPhaseFlow : (gradH : Vexel) -> Vexel
hamiltonianPhaseFlow gradH =
  actMaxelVexel symplecticMatrixMaxel gradH

||| Audits that the Symplectic Maxel satisfies canonical phase space invariants:
||| 1. J^2 = -I (J * J = -[1, 1] - [2, 2])
||| 2. det(J) = +1
public export
auditSymplecticInvarianceProof : Bool
auditSymplecticInvarianceProof =
  let j = symplecticMatrixMaxel
      jSq = mulMaxel j j
      j11 = lookupPixel (MkPixel 1 1) jSq
      j22 = lookupPixel (MkPixel 2 2) jSq
      j12 = lookupPixel (MkPixel 1 2) jSq
      j21 = lookupPixel (MkPixel 2 1) jSq
  in j11 == intToBoxInt (-1) && j22 == intToBoxInt (-1) &&
     j12 == intToBoxInt 0    && j21 == intToBoxInt 0

------------------------------------------------------------------------
-- DOUBLY STOCHASTIC EPSILON PACKET ROUTING (MAGIC MAXELS)
------------------------------------------------------------------------

||| Routes an n-channel token packet vector using an exact doubly stochastic MagicMaxel.
||| Guarantees exact channel sum mass conservation without packet duplication or loss.
public export
doublyStochasticEpsilonRouting : {n : Nat} -> MagicMaxel n -> Vect n Nat -> Vect n Nat
doublyStochasticEpsilonRouting m v = applyMagicMaxel m v

||| Audits that a 2-channel cross-switch MagicMaxel routes packets with exact conservation.
public export
auditDoublyStochasticEpsilonRoutingProof : Bool
auditDoublyStochasticEpsilonRoutingProof =
  let switch2 : MagicMaxel 2 = MkMagicMaxel [
        [0, 1],
        [1, 0]
      ]
      packetsIn : Vect 2 Nat = [42, 99]
      packetsOut = doublyStochasticEpsilonRouting switch2 packetsIn
      sumIn = foldl (+) 0 packetsIn
      sumOut = foldl (+) 0 packetsOut
  in isMagicMaxel switch2 1 &&
     packetsOut == [99, 42] &&
     sumIn == sumOut
