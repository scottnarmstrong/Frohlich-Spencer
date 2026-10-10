module

public import FroehlichSpencer.FS82.SourceInterface.BridgeOperators
public import FroehlichSpencer.FS82.Gaussian.LatticeBridgeHigher
public import FroehlichSpencer.FS82.Gaussian.IntegerExactness
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex

@[expose] public section

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.Surface

/--
After the source C2 link twist, vertex differential is the literal
C1 lattice coboundary on zero-extended vertex fields.
-/
theorem sourceD0_physical_extension_eq_coboundary (R : RectBox4)
    (x : EuclideanSpace ℝ (SourceDualZeroCells R.side)) :
    Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
        (Gaussian.euclideanToFinsupp
          ((latticeExactOneComplex (B := R.side) R.origin).d₀ x)) =
      sourceRealLatticeCoboundary
        (sourcePhysicalDualZeroExtension R.origin
          (sourceDualZeroToChain x)) := by
  have hq : Gaussian.euclideanToFinsupp
      (sourceDualTLinear (sourceDualD₀ x)) =
      sourceDualTMap (Gaussian.euclideanToFinsupp (sourceDualD₀ x)) := by
    ext e
    simp [sourceDualTLinear, sourceDualTMap_apply]
  change Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
      (Gaussian.euclideanToFinsupp (sourceDualTLinear (sourceDualD₀ x))) = _
  rw [hq]
  rw [← sourcePhysicalDualZeroExtension_sourceDualTMap R.origin (sourceDualD₀ x)]
  rw [← sourcePhysicalDualZeroExtension_twist_commutes R.origin
    (sourceDualOneToChain (sourceDualD₀ x))]
  rw [sourceDualD₀_physical_bridge]
  rw [latticeOrientationSignTwist_involutive]
  have hzero : dualOrientationSignTwist (sourceDualZeroToChain x) =
      sourceDualZeroToChain x := by
    change dualOrientationSignTwist
        (embedDualSubtype sourceDualZeroEmbedding (Gaussian.euclideanToFinsupp x)) = _
    exact dualOrientationSignTwist_embedSourceZero _
  rw [hzero]


/-- The source differential on a vertex basis has the physical incidence
coefficients of the literal lattice coboundary. -/
theorem sourceD0_vertexBasis_coefficient (R : RectBox4)
    (v : SourceDualZeroCells R.side) (e : SourceDualOneCells R.side) :
    ((latticeExactOneComplex (B := R.side) R.origin).d₀
      (WithLp.toLp 2 (Pi.single v (1 : ℝ)))) e =
      (((Cubical.latticeCoboundaryBasis
        (Cubical.dualCellEmbedding R.origin v.1) : Cubical.LatticeChain 4)
          (Cubical.lambdaStarEmbedding R.origin e) : ℤ) : ℝ) := by
  let b : EuclideanSpace ℝ (SourceDualZeroCells R.side) :=
    WithLp.toLp 2 (Pi.single v (1 : ℝ))
  have hphys := congrArg (fun q : Cubical.RealLatticeChain 4 =>
      q (Cubical.lambdaStarEmbedding R.origin e))
    (sourceD0_physical_extension_eq_coboundary R b)
  have hleft :
      Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
          (Gaussian.euclideanToFinsupp
            ((latticeExactOneComplex (B := R.side) R.origin).d₀ b))
        (Cubical.lambdaStarEmbedding R.origin e) =
        ((latticeExactOneComplex (B := R.side) R.origin).d₀ b) e := by
    rw [Cubical.lambdaStarRealZeroExtension_eq_embDomain]
    simp [Finsupp.embDomain_apply]
  have hq : Gaussian.euclideanToFinsupp b = Finsupp.single v (1 : ℝ) := by
    ext w
    simp [b, Finsupp.single_apply, eq_comm]
  have hvertex : sourcePhysicalDualZeroExtension R.origin
      (sourceDualZeroToChain b) =
      Finsupp.single (Cubical.dualCellEmbedding R.origin v.1) (1 : ℝ) := by
    change sourcePhysicalDualZeroExtension R.origin
        (embedDualSubtype sourceDualZeroEmbedding (Gaussian.euclideanToFinsupp b)) = _
    rw [sourcePhysicalDualZeroExtension_embedDualSubtype, hq]
    simp [Finsupp.linearCombination_single, sourceDualZeroEmbedding]
  have hright :
      sourceRealLatticeCoboundary
          (sourcePhysicalDualZeroExtension R.origin (sourceDualZeroToChain b))
        (Cubical.lambdaStarEmbedding R.origin e) =
        (((Cubical.latticeCoboundaryBasis
          (Cubical.dualCellEmbedding R.origin v.1) : Cubical.LatticeChain 4)
            (Cubical.lambdaStarEmbedding R.origin e) : ℤ) : ℝ) := by
    rw [hvertex, sourceRealLatticeCoboundary_single]
    simp [Cubical.castLatticeChain, Finsupp.mapRange]
  rw [hleft] at hphys
  rw [hright] at hphys
  exact hphys

end FroehlichSpencer.FS82.Surface
end
