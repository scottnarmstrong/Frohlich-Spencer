/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Duality
public import FroehlichSpencer.FS82.XY.DualComplexD
public import FroehlichSpencer.FS82.XY.Duality
public import FroehlichSpencer.FS82.Cubical.RealFilling
public import FroehlichSpencer.FS82.Cubical.DualStokes
public import FroehlichSpencer.FS82.Wilson.CubeLoopField
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Endpoint residuals in dimensions at least three

The endpoint path and the finite grounded Hodge complex are defined in every
dimension. A real bond flow with the endpoint boundary is a competitor for
the projection residual, by the cubical star/filling identity.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Wilson
open scoped InnerProductSpace

noncomputable section
open Classical

variable {d : ℕ} (hd : 3 ≤ d) {B : Box d}

/-- Compress the cubical star of a primal chain to its complementary dual
form carrier. -/
noncomputable def xyDualDStarCompressLinear (k : ℕ) :
    RealChain d B →ₗ[ℝ] EuclideanSpace ℝ (DualDForm B (d - k)) :=
  finsuppToEuclidean.comp
    ((dualDCompressSubtype (dualDFormEmbedding (B := B) (d - k))).comp starMap)

/-- On a chain supported in degree `k`, complementary-star compression loses
no coefficients. -/
theorem xyDualDStarCompressLinear_embed (k : ℕ) (p : RealChain d B)
    (hp : realHomogeneousSupport p k) :
    dualDFormToChain (d - k) (xyDualDStarCompressLinear (d := d) (B := B) k p) =
      starMap p := by
  have hs : dualRealHomogeneousSupport (starMap p) (d - k) :=
    dualDStarMap_homogeneousSupport p k hp
  have hsupport : ((starMap p).support : Set (DualCell d B)) ⊆
      Set.range (dualDFormEmbedding (B := B) (d - k)) := by
    intro c hc
    exact ⟨⟨c, hs c hc⟩, rfl⟩
  dsimp [xyDualDStarCompressLinear, dualDFormToChain,
    dualDFormEmbedding]
  rw [euclideanToFinsupp_finsuppToEuclidean]
  exact dualDEmbedCompress_eq_self_of_support
    (dualDFormEmbedding (B := B) (d - k)) (starMap p) hsupport

/-- Differentiating the compressed star of a real plaquette filling gives the
compressed star of its bond boundary. -/
theorem xyDualD₁_starFilling (hd : 3 ≤ d) (p : RealChain d B)
    (hp : realHomogeneousSupport p 2) :
    dualDD₁ (B := B) (xyDualDStarCompressLinear (d := d) (B := B) 2 p) =
      xyDualDStarCompressLinear (d := d) (B := B) 1 (realBoundary p) := by
  apply dualDFormToChain_injective (d - 1)
  calc
    dualDFormToChain (d - 1)
        (dualDD₁ (xyDualDStarCompressLinear (d := d) (B := B) 2 p)) =
        dualExteriorDifference (starMap p) := by
          rw [dualDD₁_embed_eq_derivative hd,
            xyDualDStarCompressLinear_embed (d := d) (B := B) 2 p hp]
    _ = starMap (realBoundary p) := primalDualStar_incidence_identity p
    _ = dualDFormToChain (d - 1)
        (xyDualDStarCompressLinear (d := d) (B := B) 1 (realBoundary p)) := by
          rw [xyDualDStarCompressLinear_embed (d := d) (B := B) 1
            (realBoundary p) (realBoundary_homogeneousSupport p 2 (by omega) hp)]

/-- The real dual `(d - 1)`-form associated with the cubical endpoint path. -/
noncomputable def xyDualDEndpointPathVector (x y : XYSites B) :
    EuclideanSpace ℝ (DualDForm B (d - 1)) :=
  xyDualDStarCompressLinear (d := d) (B := B) 1
    (castIntegerChain (xyEndpointPath x y))

/-- The co-closed source of the dual endpoint path. -/
noncomputable def xyDualDEndpointPathSource (x y : XYSites B) :
    EuclideanSpace ℝ (DualDForm B (d - 2)) :=
  (dualDExactOneComplex hd B).d₁.adjoint
    (xyDualDEndpointPathVector x y)

/-- The endpoint source as a member of the co-closed subspace. -/
noncomputable def xyDualDEndpointPathSourceCoClosed (x y : XYSites B) :
    coClosed (dualDExactOneComplex hd B) := by
  refine ⟨xyDualDEndpointPathSource (hd := hd) x y, ?_⟩
  apply LinearMap.mem_ker.mpr
  let C := dualDExactOneComplex hd B
  let φ := xyDualDEndpointPathVector x y
  let g := C.d₀.adjoint (C.d₁.adjoint φ)
  have hg : inner ℝ g g = 0 := calc
    inner ℝ g g = inner ℝ (C.d₁.adjoint φ) (C.d₀ g) := by
      exact LinearMap.adjoint_inner_left C.d₀ g (C.d₁.adjoint φ)
    _ = inner ℝ φ (C.d₁ (C.d₀ g)) := by
      exact LinearMap.adjoint_inner_left C.d₁ (C.d₀ g) φ
    _ = 0 := by
      have h := congrArg (fun f => f g) C.complex
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
      rw [h]
      simp
  exact inner_self_eq_zero.mp hg

/-- The Hodge solution of the endpoint source. -/
noncomputable def xyDualDEndpointPathTau (x y : XYSites B) :
    coClosed (dualDExactOneComplex hd B) :=
  hodgeInverseOnCoClosed (dualDExactOneComplex hd B)
    (xyDualDEndpointPathSourceCoClosed (hd := hd) x y)

/-- The squared norm left after projecting the endpoint path onto exact
`(d - 1)`-forms. -/
noncomputable def xyDualDEndpointResidualEnergy (x y : XYSites B) : ℝ :=
  inner ℝ (loopFieldResidual (dualDExactOneComplex hd B)
      (xyDualDEndpointPathVector x y))
    (loopFieldResidual (dualDExactOneComplex hd B)
      (xyDualDEndpointPathVector x y))

/-- Squared energy of a real bond chain. -/
noncomputable def xyDualDBondEnergy (J : RealChain d B) : ℝ :=
  ∑ b : XYBonds B, J b.1 ^ 2

/-- The star of a real bond chain, compressed to dual forms of degree `d-1`. -/
noncomputable def xyDualDStarBondVector (J : RealChain d B) :
    EuclideanSpace ℝ (DualDForm B (d - 1)) :=
  xyDualDStarCompressLinear (d := d) (B := B) 1 J

/-- Compression of the star does not discard coefficients of a homogeneous
bond chain. -/
theorem dualDStarBondVector_embed (J : RealChain d B)
    (hJ : realHomogeneousSupport J 1) :
    dualDFormToChain (d - 1) (xyDualDStarBondVector (d := d) (B := B) J) =
      starMap J := by
  exact xyDualDStarCompressLinear_embed (d := d) (B := B) 1 J hJ

/-- The star identification preserves the squared bond energy. -/
theorem xyDualDStarBondVector_energy (hd : 3 ≤ d) (J : RealChain d B)
    (hJ : realHomogeneousSupport J 1) :
    inner ℝ (xyDualDStarBondVector (d := d) (B := B) J)
      (xyDualDStarBondVector (d := d) (B := B) J) = xyDualDBondEnergy J := by
  classical
  let e : XYBonds B ≃ DualDForm B (d - 1) :=
    { toFun := fun b => ⟨primalDualCellEquiv b.1, by
        have h := dualDStarComplementaryDegree b.1
        rw [b.2] at h
        omega⟩
      invFun := fun p => ⟨primalDualCellEquiv.symm p.1, by
        have h := dualDStarComplementaryDegree (primalDualCellEquiv.symm p.1)
        simp only [Equiv.apply_symm_apply] at h
        rw [p.2] at h
        omega⟩
      left_inv := by intro b; apply Subtype.ext; simp
      right_inv := by intro p; apply Subtype.ext; simp }
  have happly (b : XYBonds B) :
      xyDualDStarBondVector (d := d) (B := B) J (e b) = J b.1 := by
    have hcoord :
        xyDualDStarBondVector (d := d) (B := B) J (e b) =
          starMap J (dualDFormEmbedding (B := B) (d - 1) (e b)) := by
      have h := congrArg (fun q : DualRealChain d B =>
        q (dualDFormEmbedding (B := B) (d - 1) (e b)))
        (dualDStarBondVector_embed (d := d) (B := B) J hJ)
      change dualDEmbedSubtype (dualDFormEmbedding (B := B) (d - 1))
          (euclideanToFinsupp
            (xyDualDStarBondVector (d := d) (B := B) J))
          (dualDFormEmbedding (B := B) (d - 1) (e b)) = _ at h
      rw [dualDEmbedSubtype_apply_at_image] at h
      exact h
    have hstar : starMap J (primalDualCellEquiv b.1) = J b.1 := by
      simp [starMap, Finsupp.equivMapDomain_apply]
    have heval :
        starMap J (dualDFormEmbedding (B := B) (d - 1) (e b)) =
          starMap J (primalDualCellEquiv b.1) := by
      simp [dualDFormEmbedding, e]
    exact hcoord.trans (heval.trans hstar)
  rw [PiLp.inner_apply]
  calc
    (∑ p : DualDForm B (d - 1),
        xyDualDStarBondVector (d := d) (B := B) J p *
          xyDualDStarBondVector (d := d) (B := B) J p) =
      ∑ b : XYBonds B,
        xyDualDStarBondVector (d := d) (B := B) J (e b) *
          xyDualDStarBondVector (d := d) (B := B) J (e b) := by
            exact (Equiv.sum_comp e (fun p : DualDForm B (d - 1) =>
              xyDualDStarBondVector (d := d) (B := B) J p *
                xyDualDStarBondVector (d := d) (B := B) J p)).symm
    _ = xyDualDBondEnergy J := by
      unfold xyDualDBondEnergy
      apply Finset.sum_congr rfl
      intro b hb
      rw [happly b]
      simp only [pow_two]

/-- The analytic endpoint residual equals its source energy after the Hodge
projection. -/
theorem xyDualDEndpointResidualEnergy_eq_sub (x y : XYSites B) :
    xyDualDEndpointResidualEnergy (hd := hd) x y =
      inner ℝ (xyDualDEndpointPathVector x y)
          (xyDualDEndpointPathVector x y) -
        inner ℝ (xyDualDEndpointPathSourceCoClosed (hd := hd) x y :
          EuclideanSpace ℝ (DualDForm B (d - 2)))
          (xyDualDEndpointPathTau (hd := hd) x y :
            EuclideanSpace ℝ (DualDForm B (d - 2))) := by
  let C := dualDExactOneComplex hd B
  let φ := xyDualDEndpointPathVector x y
  let μ := xyDualDEndpointPathSourceCoClosed (hd := hd) x y
  let τ := xyDualDEndpointPathTau (hd := hd) x y
  have hodge : hodgeOnCoClosed C τ = μ := by
    exact hodgeOnCoClosed_hodgeInverse C
      (xyDualDEndpointPathSourceCoClosed (hd := hd) x y)
  have hcurl : C.d₁.adjoint (C.d₁ τ.1) = μ.1 := by
    have h := congrArg Subtype.val hodge
    simpa [hodgeOnCoClosed, formLaplacian, C, τ, μ] using h
  have hsource : C.d₁.adjoint φ = μ.1 := by
    rfl
  have horth : ∀ α : EuclideanSpace ℝ (DualDForm B (d - 2)),
      inner ℝ (φ - C.d₁ τ.1) (C.d₁ α) = 0 := by
    intro α
    calc
      inner ℝ (φ - C.d₁ τ.1) (C.d₁ α) =
          inner ℝ (C.d₁.adjoint φ) α -
            inner ℝ (C.d₁.adjoint (C.d₁ τ.1)) α := by
              rw [inner_sub_left,
                ← LinearMap.adjoint_inner_left C.d₁ α φ,
                ← LinearMap.adjoint_inner_left C.d₁ α (C.d₁ τ.1)]
      _ = 0 := by rw [hsource, hcurl]; simp
  have hproj : (LinearMap.range C.d₁).starProjection φ = C.d₁ τ.1 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact LinearMap.mem_range_self C.d₁ τ.1
    · intro v hv
      rcases hv with ⟨α, rfl⟩
      exact horth α
  have hres : loopFieldResidual C φ = φ - C.d₁ τ.1 := by
    simp only [loopFieldResidual, hproj]
  have hnorm : inner ℝ (C.d₁ τ.1) (C.d₁ τ.1) = inner ℝ μ.1 τ.1 := by
    rw [← hcurl]
    exact (LinearMap.adjoint_inner_left C.d₁ τ.1 (C.d₁ τ.1)).symm
  let ε := φ - C.d₁ τ.1
  have hεorth : inner ℝ ε (C.d₁ τ.1) = 0 := by
    simpa [ε] using horth τ.1
  have hεorth' : inner ℝ (C.d₁ τ.1) ε = 0 := by
    rw [real_inner_comm]
    exact hεorth
  have hpyth : inner ℝ φ φ =
      inner ℝ ε ε + inner ℝ (C.d₁ τ.1) (C.d₁ τ.1) := by
    have hdecomp : ε + C.d₁ τ.1 = φ := by simp [ε]
    rw [← hdecomp]
    simp only [inner_add_left, inner_add_right]
    rw [hεorth, hεorth']
    ring
  change inner ℝ (loopFieldResidual C φ) (loopFieldResidual C φ) = _
  rw [hres]
  calc
    inner ℝ ε ε = (inner ℝ ε ε + inner ℝ (C.d₁ τ.1) (C.d₁ τ.1)) -
        inner ℝ (C.d₁ τ.1) (C.d₁ τ.1) := by ring
    _ = inner ℝ φ φ - inner ℝ μ.1 τ.1 := by rw [← hpyth, hnorm]

/-- Any real unit bond flow between the endpoints bounds the residual energy. -/
theorem xyDualDEndpointResidualEnergy_le_of_bondFlow (x y : XYSites B)
    (J : RealChain d B) (hJ : realHomogeneousSupport J 1)
    (hboundary : realBoundary J = castIntegerChain (xyEndpointSource x y)) :
    xyDualDEndpointResidualEnergy (hd := hd) x y ≤
      xyDualDBondEnergy (d := d) (B := B) J := by
  let C := dualDExactOneComplex hd B
  let path := castIntegerChain (xyEndpointPath x y)
  have hpathdeg : realHomogeneousSupport path 1 := by
    intro c hc
    exact xyEndpointPath_homogeneousSupport x y c (Finsupp.support_mapRange hc)
  have hpathbd : realBoundary path = castIntegerChain (xyEndpointSource x y) := by
    have hcast : castIntegerChain (boundary (xyEndpointPath x y)) = realBoundary path := by
      simpa [realBoundary, path] using
        (realifyLinearMap_cast boundary (xyEndpointPath x y)).symm
    rw [← hcast, xyEndpointPath_boundary]
  let q := path - J
  have hqdeg : realHomogeneousSupport q 1 := by
    intro c hc
    have hqval : q c ≠ 0 := Finsupp.mem_support_iff.mp hc
    have hs : c ∈ path.support ∨ c ∈ J.support := by
      by_contra hnot
      have hnp : c ∉ path.support := fun hp => hnot (Or.inl hp)
      have hnj : c ∉ J.support := fun hj => hnot (Or.inr hj)
      have hp0 : path c = 0 := by
        by_contra hp
        exact hnp (Finsupp.mem_support_iff.mpr hp)
      have hj0 : J c = 0 := by
        by_contra hj
        exact hnj (Finsupp.mem_support_iff.mpr hj)
      exact hqval (by simp [q, hp0, hj0])
    rcases hs with hp | hj
    · exact hpathdeg c hp
    · exact hJ c hj
  have hqcycle : realBoundary q = 0 := by
    dsimp [q]
    rw [map_sub, hpathbd, hboundary, sub_self]
  let anchor : Anchor d B := fun i => ⟨0, Nat.zero_lt_succ (B i)⟩
  obtain ⟨hfill, hfilldeg⟩ :=
    real_positiveDegree_filling anchor q 1 (by omega) hqdeg hqcycle
  let η := realFillingOperator anchor q
  have hηbd : realBoundary η = q := hfill
  have hηdeg : realHomogeneousSupport η 2 := by simpa [η] using hfilldeg
  let shift : EuclideanSpace ℝ (DualDForm B (d - 2)) :=
      xyDualDStarCompressLinear (d := d) (B := B) 2 η
  have hshift : (dualDExactOneComplex hd B).d₁ shift =
      xyDualDEndpointPathVector x y - xyDualDStarBondVector J := by
    apply dualDFormToChain_injective (d - 1)
    calc
      dualDFormToChain (d - 1) ((dualDExactOneComplex hd B).d₁ shift) =
          dualDFormToChain (d - 1)
            (xyDualDStarCompressLinear (d := d) (B := B) 1 (realBoundary η)) := by
              change dualDFormToChain (d - 1)
                (dualDD₁ (xyDualDStarCompressLinear (d := d) (B := B) 2 η)) = _
              rw [xyDualD₁_starFilling (d := d) hd η hηdeg]
      _ = starMap (realBoundary η) :=
            xyDualDStarCompressLinear_embed (d := d) (B := B) 1
              (realBoundary η) (realBoundary_homogeneousSupport η 2 (by omega) hηdeg)
      _ = starMap path - starMap J := by
            rw [hηbd]
            simp only [q, map_sub]
      _ = dualDFormToChain (d - 1)
          (xyDualDEndpointPathVector x y - xyDualDStarBondVector J) := by
            rw [← xyDualDStarCompressLinear_embed (d := d) (B := B) 1 path hpathdeg,
              ← dualDStarBondVector_embed (d := d) (B := B) J hJ]
            simp only [xyDualDEndpointPathVector, xyDualDStarBondVector, map_sub]
            rw [show path = castIntegerChain (xyEndpointPath x y) by rfl]
  have hres0 := norm_loopFieldResidual_le C
    (xyDualDEndpointPathVector x y) shift
  have hres : ‖loopFieldResidual C (xyDualDEndpointPathVector x y)‖ ≤
      ‖xyDualDStarBondVector J‖ := by
    have hnormarg : xyDualDEndpointPathVector x y - C.d₁ shift =
        xyDualDStarBondVector J := by
      rw [hshift]
      abel
    rw [hnormarg] at hres0
    exact hres0
  have hresSq : ‖loopFieldResidual C (xyDualDEndpointPathVector x y)‖ ^ 2 ≤
      ‖xyDualDStarBondVector J‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hres 2
  have henergy := xyDualDStarBondVector_energy (d := d) (B := B) hd J hJ
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hresSq
  rw [← henergy]
  exact hresSq

/-- The real cubical boundary is square-zero in every dimension. -/
theorem xyDualDRealBoundary_square_zero :
    (realBoundary : RealChain d B →ₗ[ℝ] RealChain d B) * realBoundary = 0 := by
  have h := congrArg (realifyLinearMap (d := d) (B := B))
    (boundary_square_zero (d := d) (B := B))
  rw [realifyLinearMap_mul] at h
  have hzero : realifyLinearMap (0 : Chain d B →ₗ[ℤ] Chain d B) = 0 := by
    ext q c
    simp [realifyLinearMap, castIntegerChain]
  rw [hzero] at h
  simpa only [realBoundary] using h

/-- The Hodge projection determines a real bond flow whose boundary is the
endpoint dipole and whose energy is exactly the endpoint residual. -/
theorem exists_xyDualDEndpointResidualMinimizingFlow (x y : XYSites B) :
    ∃ J : RealChain d B,
      realHomogeneousSupport J 1 ∧
      realBoundary J = castIntegerChain (xyEndpointSource x y) ∧
      xyDualDBondEnergy J = xyDualDEndpointResidualEnergy (hd := hd) x y := by
  let C := dualDExactOneComplex hd B
  let φ := xyDualDEndpointPathVector x y
  let μ := xyDualDEndpointPathSourceCoClosed (hd := hd) x y
  let τ := xyDualDEndpointPathTau (hd := hd) x y
  let path := castIntegerChain (xyEndpointPath x y)
  have hpathdeg : realHomogeneousSupport path 1 := by
    intro c hc
    exact xyEndpointPath_homogeneousSupport x y c (Finsupp.support_mapRange hc)
  have hpathbd : realBoundary path = castIntegerChain (xyEndpointSource x y) := by
    have hcast : castIntegerChain (boundary (xyEndpointPath x y)) = realBoundary path := by
      simpa [realBoundary, path] using
        (realifyLinearMap_cast boundary (xyEndpointPath x y)).symm
    rw [← hcast, xyEndpointPath_boundary]
  have hodge : hodgeOnCoClosed C τ = μ := by
    exact hodgeOnCoClosed_hodgeInverse C μ
  have hcurl : C.d₁.adjoint (C.d₁ τ.1) = μ.1 := by
    have h := congrArg Subtype.val hodge
    simpa [hodgeOnCoClosed, formLaplacian, C, τ, μ] using h
  have hsource : C.d₁.adjoint φ = μ.1 := by rfl
  have horth : ∀ α : EuclideanSpace ℝ (DualDForm B (d - 2)),
      inner ℝ (φ - C.d₁ τ.1) (C.d₁ α) = 0 := by
    intro α
    calc
      inner ℝ (φ - C.d₁ τ.1) (C.d₁ α) =
          inner ℝ (C.d₁.adjoint φ) α -
            inner ℝ (C.d₁.adjoint (C.d₁ τ.1)) α := by
              rw [inner_sub_left,
                ← LinearMap.adjoint_inner_left C.d₁ α φ,
                ← LinearMap.adjoint_inner_left C.d₁ α (C.d₁ τ.1)]
      _ = 0 := by rw [hsource, hcurl]; simp
  have hproj : (LinearMap.range C.d₁).starProjection φ = C.d₁ τ.1 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact LinearMap.mem_range_self C.d₁ τ.1
    · intro v hv
      rcases hv with ⟨α, rfl⟩
      exact horth α
  have hres : loopFieldResidual C φ = φ - C.d₁ τ.1 := by
    simp only [loopFieldResidual, hproj]
  let η : RealChain d B :=
    starMapInverse (dualDFormToChain (d - 2) τ.1)
  have hηdegree : realHomogeneousSupport η 2 := by
    have hq : dualRealHomogeneousSupport (dualDFormToChain (d - 2) τ.1)
        (d - 2) :=
      dualDEmbedSubtype_homogeneous (dualDFormEmbedding (B := B) (d - 2))
        (d - 2) (by intro a; exact a.2) (euclideanToFinsupp τ.1)
    have h := dualDStarMapInverse_homogeneousSupport
      (dualDFormToChain (d - 2) τ.1) (d - 2) hq
    have hdeg : d - (d - 2) = 2 := by omega
    rw [hdeg] at h
    simpa [η] using h
  have hηstar : starMap η = dualDFormToChain (d - 2) τ.1 := by
    simp [η, starMap_starMapInverse]
  have hτboundary : C.d₁ τ.1 =
      xyDualDStarCompressLinear (d := d) (B := B) 1 (realBoundary η) := by
    apply dualDFormToChain_injective (d - 1)
    calc
      dualDFormToChain (d - 1) (C.d₁ τ.1) =
          dualExteriorDifference (dualDFormToChain (d - 2) τ.1) := by
            exact dualDD₁_embed_eq_derivative hd τ.1
      _ = starMap (realBoundary η) := by
            rw [← hηstar]
            exact primalDualStar_incidence_identity η
      _ = dualDFormToChain (d - 1)
          (xyDualDStarCompressLinear (d := d) (B := B) 1 (realBoundary η)) := by
            exact (xyDualDStarCompressLinear_embed (d := d) (B := B) 1
              (realBoundary η) (realBoundary_homogeneousSupport η 2
                (by omega) hηdegree)).symm
  let J : RealChain d B := path - realBoundary η
  have hJ : realHomogeneousSupport J 1 := by
    intro c hc
    have hs : c ∈ path.support ∨ c ∈ (realBoundary η).support := by
      by_contra hnot
      have hp0 : path c = 0 := by
        by_contra hp
        exact hnot (Or.inl (Finsupp.mem_support_iff.mpr hp))
      have hb0 : realBoundary η c = 0 := by
        by_contra hb
        exact hnot (Or.inr (Finsupp.mem_support_iff.mpr hb))
      exact (Finsupp.mem_support_iff.mp hc) (by simp [J, hp0, hb0])
    rcases hs with hp | hb
    · exact hpathdeg c hp
    · exact realBoundary_homogeneousSupport η 2 (by omega) hηdegree c hb
  have hboundary : realBoundary J = castIntegerChain (xyEndpointSource x y) := by
    have hsquare : realBoundary (realBoundary η) = 0 := by
      have h := congrArg (fun f : RealChain d B →ₗ[ℝ] RealChain d B => f η)
        (xyDualDRealBoundary_square_zero (d := d) (B := B))
      change realBoundary (realBoundary η) = 0 at h
      exact h
    calc
      realBoundary J = realBoundary path - realBoundary (realBoundary η) := by
        simp [J, map_sub]
      _ = castIntegerChain (xyEndpointSource x y) := by
        rw [hpathbd, hsquare, sub_zero]
  have hvector : xyDualDStarBondVector (d := d) (B := B) J =
      loopFieldResidual C φ := by
    rw [hres]
    change xyDualDStarCompressLinear (d := d) (B := B) 1 J = _
    dsimp [J]
    rw [map_sub, hτboundary]
    simp [φ, path, xyDualDEndpointPathVector]
  have henergy := xyDualDStarBondVector_energy (d := d) (B := B) hd J hJ
  refine ⟨J, hJ, hboundary, ?_⟩
  rw [← henergy, hvector]
  rfl

end
end FroehlichSpencer.FS82.XY
