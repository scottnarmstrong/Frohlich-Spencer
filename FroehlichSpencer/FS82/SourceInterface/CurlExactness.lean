module
public import FroehlichSpencer.FS82.SourceInterface.CarrierTransport
public import FroehlichSpencer.FS82.SourceInterface.BridgeOperators
public import FroehlichSpencer.FS82.Gaussian.LatticeBridgeHigher

@[expose] public section
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical
namespace FroehlichSpencer.FS82.Surface

theorem sourceCurl_zero_forces_internal_d1 (R : RectBox4)
    (x : RealDualField R) (hx : latticeCurl R x = 0) :
    (latticeExactOneComplex (B := R.side) R.origin).d₁
      (x : EuclideanSpace ℝ (SourceDualOneCells R.side)) = 0 := by
  let C := latticeExactOneComplex (B := R.side) R.origin
  let x' : EuclideanSpace ℝ (SourceDualOneCells R.side) := x
  have hcurl : Cubical.realifyLatticeLinearMap Cubical.latticeCoboundary
      (Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
        (Gaussian.euclideanToFinsupp x')) = 0 := by
    rw [← latticeCurl_bridge R x]
    exact hx
  have hTq : sourceDualTMap (Gaussian.euclideanToFinsupp
      (sourceDualTLinear x')) = Gaussian.euclideanToFinsupp x' := by
    ext e
    simp only [sourceDualTMap_apply, Gaussian.euclideanToFinsupp_apply,
      sourceDualTLinear_apply]
    calc
      dualCellOrientationSign e.1 * (dualCellOrientationSign e.1 * x' e) =
          dualCellOrientationSign e.1 ^ 2 * x' e := by ring
      _ = x' e := by rw [dualCellOrientationSign_sq]; ring
  change sourceDualD₁ (sourceDualTLinear x') = 0
  ext f
  rw [sourceDualD₁_physical_coefficient]
  rw [hTq]
  have hcoef := congrArg (fun q : Cubical.RealLatticeChain 4 =>
    q (Cubical.dualCellEmbedding (B := R.side) R.origin f.1)) hcurl
  have hCobMap : sourceRealLatticeCoboundary =
      Cubical.realifyLatticeLinearMap Cubical.latticeCoboundary := by
    apply LinearMap.ext
    intro q
    classical
    induction q using Finsupp.induction_linear with
    | zero => simp [sourceRealLatticeCoboundary, Cubical.realifyLatticeLinearMap]
    | add q r hq hr => simp [map_add, hq, hr]
    | single c a =>
        simp [sourceRealLatticeCoboundary, Cubical.realifyLatticeLinearMap,
          Finsupp.linearCombination_single,
          FroehlichSpencer.FS82.Cubical.latticeCoboundary_basis]
  have hCob := congrArg (fun F : Cubical.RealLatticeChain 4 →ₗ[ℝ]
      Cubical.RealLatticeChain 4 => F
        (Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
          (Gaussian.euclideanToFinsupp x'))) hCobMap
  have hcoefSource := congrArg (fun q : Cubical.RealLatticeChain 4 =>
    q (Cubical.dualCellEmbedding (B := R.side) R.origin f.1)) hCob
  rw [← hcoefSource] at hcoef
  rw [hcoef]
  simp

theorem latticeCurlKernel_annihilatesCoClosed_gate (R : RectBox4)
    (μ : W R) :
    (latticeCurl R).ker ≤
      (InnerProductSpace.toDualMap ℝ (RealDualField R) (μ : RealDualField R)).ker := by
  intro x hx
  let C := latticeExactOneComplex (B := R.side) R.origin
  let e := literalWEquivCoClosed R
  let μ' : coClosed C := e μ
  let x' : EuclideanSpace ℝ (SourceDualOneCells R.side) := x
  have hxCurl : latticeCurl R (x : RealDualField R) = 0 :=
    LinearMap.mem_ker.mp hx
  have hxD1 := sourceCurl_zero_forces_internal_d1 R (x : RealDualField R) hxCurl
  have hxker : x' ∈ C.d₁.ker := by
    change C.d₁ x' = 0
    exact hxD1
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp (C.exactOne hxker)
  have hclosed : C.d₀.adjoint μ' = 0 := LinearMap.mem_ker.mp μ'.property
  have hinner : inner ℝ (μ' : EuclideanSpace ℝ (SourceDualOneCells R.side)) x' = 0 := by
    rw [← hu]
    rw [← LinearMap.adjoint_inner_left C.d₀ u μ']
    rw [hclosed]
    simp
  have hinnerLit : inner ℝ (μ : RealDualField R) (x : RealDualField R) = 0 := by
    have hh := hinner
    rw [literalWEquivCoClosed_apply_val R μ] at hh
    change inner ℝ
      (((μ : W R) : RealDualField R) : EuclideanSpace ℝ (SourceDualOneCells R.side))
      (((x : RealDualField R) : EuclideanSpace ℝ (SourceDualOneCells R.side))) = 0 at hh
    exact hh
  change inner ℝ (μ : RealDualField R) (x : RealDualField R) = 0
  exact hinnerLit


end FroehlichSpencer.FS82.Surface
end
