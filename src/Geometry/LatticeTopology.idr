module Geometry.LatticeTopology

import Core.BoxInt
import Core.VexelMaxel
import Math.LinAlgebra.TernaryClassifier
import Core.NarayAlphabet
import Data.Vect
import Data.Fin

%default total

||| A discrete 3D Spatial Coordinate vector situated on the 3x3x3 maxel grid.
||| Each coordinate component x, y, z is an exact ternary value in {-1, 0, +1}.
public export
record Coord3D where
  constructor MkCoord3D
  coordX : TernaryBit
  coordY : TernaryBit
  coordZ : TernaryBit

public export
Eq Coord3D where
  (MkCoord3D x1 y1 z1) == (MkCoord3D x2 y2 z2) =
    x1 == x2 && y1 == y2 && z1 == z2

public export
Show Coord3D where
  show (MkCoord3D x y z) = 
    "(" ++ show (bitToInt x) ++ ", " ++ show (bitToInt y) ++ ", " ++ show (bitToInt z) ++ ")"

------------------------------------------------------------------------
-- 1. BIJECTIVE TERNARY INDEXING (Fin 27 <=> Coord3D)
------------------------------------------------------------------------

public export
ternaryNat : TernaryBit -> Nat
ternaryNat Bit3MinusOne = 0
ternaryNat Bit3Zero     = 1
ternaryNat Bit3PlusOne  = 2

public export
natToTernaryBit : Nat -> TernaryBit
natToTernaryBit 0 = Bit3MinusOne
natToTernaryBit 1 = Bit3Zero
natToTernaryBit _ = Bit3PlusOne

||| Maps a 3D coordinate (x,y,z) to a unique 1D cell index in Fin 27.
||| index = (x + 1) + 3*(y + 1) + 9*(z + 1)
public export
coordToFin27 : Coord3D -> Fin 27
coordToFin27 (MkCoord3D x y z) =
  let u = ternaryNat x
      v = ternaryNat y
      w = ternaryNat z
      idx = u + (3 * v) + (9 * w)
  in case natToFin idx 27 of
       Just f  => f
       Nothing => 0

||| Maps a 1D cell index in Fin 27 to its unique 3D spatial coordinate.
public export
fin27ToCoord : Fin 27 -> Coord3D
fin27ToCoord finIdx =
  let idx = finToNat finIdx
      uNat = idx `mod` 3
      vNat = (idx `div` 3) `mod` 3
      wNat = idx `div` 9
      x = natToTernaryBit uNat
      y = natToTernaryBit vNat
      z = natToTernaryBit wNat
  in MkCoord3D x y z

------------------------------------------------------------------------
-- 2. TOROIDAL PERIODIC NEIGHBORHOOD GRAPH (T^3 Topology)
------------------------------------------------------------------------

||| Moves one step along a ternary axis with periodic toroidal wrapping modulo 3 using F3 addition.
public export
shiftTernaryForward : TernaryBit -> TernaryBit
shiftTernaryForward b = case addNaray (Naray3 b) (Naray3 Bit3PlusOne) of Naray3 b' => b'

public export
shiftTernaryBackward : TernaryBit -> TernaryBit
shiftTernaryBackward b = case addNaray (Naray3 b) (Naray3 Bit3MinusOne) of Naray3 b' => b'

||| The 6 cardinal directions on the 3D lattice.
public export
data CardinalDir = DirEast | DirWest | DirNorth | DirSouth | DirUp | DirDown

||| Computes the adjacent face neighbor coordinate along a cardinal direction.
public export
stepNeighbor : CardinalDir -> Coord3D -> Coord3D
stepNeighbor DirEast  (MkCoord3D x y z) = MkCoord3D (shiftTernaryForward x) y z
stepNeighbor DirWest  (MkCoord3D x y z) = MkCoord3D (shiftTernaryBackward x) y z
stepNeighbor DirNorth (MkCoord3D x y z) = MkCoord3D x (shiftTernaryForward y) z
stepNeighbor DirSouth (MkCoord3D x y z) = MkCoord3D x (shiftTernaryBackward y) z
stepNeighbor DirUp    (MkCoord3D x y z) = MkCoord3D x y (shiftTernaryForward z)
stepNeighbor DirDown  (MkCoord3D x y z) = MkCoord3D x y (shiftTernaryBackward z)

||| Returns the 6 face neighbors of a cell index on the discrete 3-torus.
public export
getFaceNeighbors : Fin 27 -> Vect 6 (Fin 27)
getFaceNeighbors idx =
  let c = fin27ToCoord idx
      e = coordToFin27 (stepNeighbor DirEast c)
      w = coordToFin27 (stepNeighbor DirWest c)
      n = coordToFin27 (stepNeighbor DirNorth c)
      s = coordToFin27 (stepNeighbor DirSouth c)
      u = coordToFin27 (stepNeighbor DirUp c)
      d = coordToFin27 (stepNeighbor DirDown c)
  in [e, w, n, s, u, d]

------------------------------------------------------------------------
-- 3. DISCRETE EXTERIOR CALCULUS & SPATIAL FLUX OPERATORS
------------------------------------------------------------------------

||| Helper to safely look up cell value by Fin 27 index.
public export
lookupCell : Fin 27 -> Vect 27 BoxInt -> BoxInt
lookupCell idx grid = index idx grid

||| Computes the Discrete Laplacian ΔV on a single cell:
||| ΔV(r) = Σ (V(neighbor) - V(r)) for all 6 face neighbors
public export
cellLaplacian : Fin 27 -> Vect 27 BoxInt -> BoxInt
cellLaplacian idx grid =
  let selfVal   = lookupCell idx grid
      neighbors = getFaceNeighbors idx
      sumNeighbors = foldl (\acc, nIdx => acc + lookupCell nIdx grid) (intToBoxInt 0) neighbors
  in sumNeighbors - (intToBoxInt 6 * selfVal)

||| Generates the full Discrete Laplacian field ΔV for all 27 cells.
public export
discreteLaplacian27 : Vect 27 BoxInt -> Vect 27 BoxInt
discreteLaplacian27 grid =
  tabulate (\idx => cellLaplacian idx grid)

||| Computes the total sum of a 27-cell field.
public export
sumField27 : Vect 27 BoxInt -> BoxInt
sumField27 grid = foldl (+) (intToBoxInt 0) grid

||| Propagates spatial field flux by one discrete time step under diffusion parameter kappa:
||| V_{t+1}(r) = V_t(r) + kappa * ΔV(r)
||| Exactly preserves total field sum (sum V_{t+1} == sum V_t).
public export
stepFluxPropagation : BoxInt -> Vect 27 BoxInt -> Vect 27 BoxInt
stepFluxPropagation kappa grid =
  let lap = discreteLaplacian27 grid
  in zipWith (\v, l => v + (kappa * l)) grid lap

------------------------------------------------------------------------
-- 4. PURE BOXEL MULTISET LATTICE & FLUX OPERATORS
------------------------------------------------------------------------

||| Maps a 1D cell index in Fin 27 to its 3D coordinate Voxel [x, y, z] in {0, 1, 2}^3.
public export
fin27ToVoxel : Fin 27 -> Voxel
fin27ToVoxel idx =
  let (MkCoord3D x y z) = fin27ToCoord idx
  in MkVoxel (ternaryNat x) (ternaryNat y) (ternaryNat z)

||| Converts a flat 27-cell scalar field into a 3D Boxel multiset.
public export
field27ToBoxel : Vect 27 BoxInt -> Boxel
field27ToBoxel grid =
  let paired = tabulate (\idx => (fin27ToVoxel idx, lookupCell idx grid))
  in canonicalizeBoxel (MkBoxel (toList paired))

||| Converts a 3D Boxel multiset back into a flat 27-cell scalar field.
public export
boxelToField27 : Boxel -> Vect 27 BoxInt
boxelToField27 b =
  tabulate (\idx => lookupVoxel (fin27ToVoxel idx) b)

||| Computes the Discrete 3D Laplacian field directly on a Boxel multiset.
public export
discreteLaplacianBoxel : Boxel -> Boxel
discreteLaplacianBoxel b =
  let field = boxelToField27 b
      lap   = discreteLaplacian27 field
  in field27ToBoxel lap

||| Audits that discrete Laplacian flux on the compact 3-torus vanishes identically without leakage.
public export
auditToroidalBoxelFluxProof : Boxel -> Bool
auditToroidalBoxelFluxProof b =
  totalBoxelWeight (discreteLaplacianBoxel b) == intToBoxInt 0
