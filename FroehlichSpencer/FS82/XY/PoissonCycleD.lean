/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.CycleChartD
public import FroehlichSpencer.FS82.XY.HodgeCycleGramD
public import FroehlichSpencer.FS82.XY.QuotientGaussianD
public import FroehlichSpencer.FS82.Gaussian.SourceImageGaussian
public import FroehlichSpencer.FS82.Poisson.FiniteModel
public import FroehlichSpencer.FS82.Cubical.DualStokes

/-!
# All-dimensional cycle chart for the XY Hodge/Poisson bridge

The finite dual differential is the star of the primal plaquette boundary.
Filling the real bond cycles therefore gives a chart from cycles to the image
of the dual differential. This module begins the finite Poisson comparison in
that chart.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open Module
open scoped InnerProductSpace

/-- Compress the cubical star of a primal `k`-chain to the complementary
dual-form carrier. -/
noncomputable def dualDStarCompressLinear {d : ℕ} {B : Box d} (k : ℕ) :
    RealChain d B →ₗ[ℝ] EuclideanSpace ℝ (DualDForm B (d - k)) :=
  (finsuppToEuclidean.comp
    (dualDCompressSubtype (dualDFormEmbedding (B := B) (d - k)))).comp starMap

/-- On a chain of degree `k`, compression loses no star coefficients. -/
theorem dualDStarCompressLinear_embed {d : ℕ} (B : Box d) (k : ℕ)
    (p : RealChain d B) (hp : realHomogeneousSupport p k) :
    dualDFormToChain (d - k) (dualDStarCompressLinear k p) = starMap p := by
  have hs : dualRealHomogeneousSupport (starMap p) (d - k) :=
    dualDStarMap_homogeneousSupport p k hp
  have hsupport : ((starMap p).support : Set (DualCell d B)) ⊆
      Set.range (dualDFormEmbedding (B := B) (d - k)) := by
    intro c hc
    exact ⟨⟨c, hs c hc⟩, rfl⟩
  dsimp [dualDStarCompressLinear, dualDFormToChain,
    dualDFormEmbedding]
  rw [euclideanToFinsupp_finsuppToEuclidean]
  exact dualDEmbedCompress_eq_self_of_support
    (dualDFormEmbedding (B := B) (d - k)) (starMap p) hsupport

/-- The dual differential of the star of a real plaquette filling is the
star of its bond boundary. -/
theorem dualDD₁_starFilling {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (p : RealChain d B) (hp : realHomogeneousSupport p 2) :
    dualDD₁ (B := B)
        (dualDStarCompressLinear (B := B) 2 p) =
      dualDStarCompressLinear (B := B) 1 (realBoundary p) := by
  apply dualDFormToChain_injective (d - 1)
  calc
    dualDFormToChain (d - 1)
        (dualDD₁ (dualDStarCompressLinear (B := B) 2 p)) =
        dualExteriorDifference (starMap p) := by
          rw [dualDD₁_embed_eq_derivative hd,
            dualDStarCompressLinear_embed B 2 p hp]
    _ = starMap (realBoundary p) := primalDualStar_incidence_identity p
    _ = dualDFormToChain (d - 1)
        (dualDStarCompressLinear (B := B) 1 (realBoundary p)) := by
          rw [dualDStarCompressLinear_embed B 1 (realBoundary p)
            (realBoundary_homogeneousSupport p 2 (by omega) hp)]

/-- A fixed prism filling operator gives a linear lift of every real bond
cycle to a dual `(d - 2)`-form. -/
noncomputable def dualDCycleFillingLift {d : ℕ} {B : Box d} :
    degreeOneRealCycleSubspace (B := B) →ₗ[ℝ]
      EuclideanSpace ℝ (DualDForm B (d - 2)) := by
  let anchor : Anchor d B := fun i => ⟨0, Nat.zero_lt_succ (B i)⟩
  exact (dualDStarCompressLinear (B := B) 2).comp
    ((realFillingOperator anchor).comp
      (degreeOneRealCycleSubspace (B := B)).subtype)

/-- Differentiating the prism lift returns the star of its bond cycle. -/
theorem dualDD₁_cycleFillingLift {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (c : degreeOneRealCycleSubspace (B := B)) :
    dualDD₁ (B := B) (dualDCycleFillingLift c) =
      dualDStarCompressLinear (B := B) 1 c.1 := by
  let anchor : Anchor d B := fun i => ⟨0, Nat.zero_lt_succ (B i)⟩
  have hfill := real_positiveDegree_filling anchor c.1 1 (by omega)
    c.2.1 c.2.2
  change dualDD₁ (B := B)
      (dualDStarCompressLinear (B := B) 2
        (realFillingOperator anchor c.1)) = _
  rw [dualDD₁_starFilling hd (realFillingOperator anchor c.1)
    (by simpa using hfill.2)]
  rw [hfill.1]

/-- The real cubical boundary squares to zero. -/
theorem realBoundary_square_zero {d : ℕ} {B : Box d} :
    (realBoundary (d := d) (B := B)).comp
      (realBoundary (d := d) (B := B)) = 0 := by
  change realifyLinearMap (boundary (d := d) (B := B)) *
      realifyLinearMap (boundary (d := d) (B := B)) = 0
  rw [← realifyLinearMap_mul, boundary_square_zero]
  apply LinearMap.ext
  intro q
  ext c
  change (Finsupp.linearCombination ℝ (fun x : Cell d B =>
    castIntegerChain ((0 : Chain d B →ₗ[ℤ] Chain d B) (basisChain x))) q) c = 0
  have hfun : (fun x : Cell d B => castIntegerChain
      ((0 : Chain d B →ₗ[ℤ] Chain d B) (basisChain x))) = 0 := by
    funext x
    simp [castIntegerChain]
  rw [hfun, Finsupp.linearCombination_zero]
  simp

/-- Inverse star turns the dual differential into the primal boundary. -/
theorem starMapInverse_dualExteriorDifference {d : ℕ} {B : Box d}
    (q : DualRealChain d B) :
    starMapInverse (dualExteriorDifference q) =
      realBoundary (starMapInverse q) := by
  simpa only [starMap_starMapInverse] using
    (primalDualStar_boundary_identity (starMapInverse q))

/-- The real cycle space and the image of the degree-`d - 2` dual
differential are linearly equivalent. The forward map is the fixed prism
filling chart; the inverse is star followed by inverse star. -/
noncomputable def dualDRangeToCycle {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (y : LinearMap.range (dualDD₁ (B := B))) :
    degreeOneRealCycleSubspace (B := B) :=
  ⟨starMapInverse (dualDFormToChain (d - 1) y.1), by
    constructor
    · intro c hc
      have hyDegree : dualRealHomogeneousSupport
          (dualDFormToChain (d - 1) y.1) (d - 1) :=
        dualDEmbedSubtype_homogeneous (dualDFormEmbedding (d - 1))
          (d - 1) (by intro a; exact a.2) (euclideanToFinsupp y.1)
      have hdegree := dualDStarMapInverse_homogeneousSupport
        (dualDFormToChain (d - 1) y.1) (d - 1) hyDegree
      have hsub : d - (d - 1) = 1 := by omega
      rw [hsub] at hdegree
      exact hdegree c hc
    · rcases y.2 with ⟨α, hα⟩
      have hrepr := dualDD₁_embed_eq_derivative hd α
      have hval : dualDFormToChain (d - 1) y.1 =
          dualExteriorDifference (dualDFormToChain (d - 2) α) := by
        rw [← hα, hrepr]
      rw [hval, starMapInverse_dualExteriorDifference]
      have hsquare := congrArg
        (fun T : RealChain d B →ₗ[ℝ] RealChain d B =>
          T (starMapInverse (dualDFormToChain (d - 2) α)))
        (realBoundary_square_zero (d := d) (B := B))
      exact hsquare⟩

@[simp] theorem dualDRangeToCycle_val {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (y : LinearMap.range (dualDD₁ (B := B))) :
    (dualDRangeToCycle hd y).1 =
      starMapInverse (dualDFormToChain (d - 1) y.1) := rfl

noncomputable def dualDCycleRangeEquiv {d : ℕ} (hd : 3 ≤ d) {B : Box d} :
    degreeOneRealCycleSubspace (B := B) ≃ₗ[ℝ]
      LinearMap.range (dualDD₁ (B := B)) where
  toFun c := ⟨dualDD₁ (dualDCycleFillingLift c),
    by change ∃ z, dualDD₁ z = dualDD₁ (dualDCycleFillingLift c)
       exact ⟨dualDCycleFillingLift c, rfl⟩⟩
  invFun := dualDRangeToCycle hd
  left_inv c := by
    apply Subtype.ext
    change starMapInverse (dualDFormToChain (d - 1)
      (dualDD₁ (dualDCycleFillingLift c))) = c.1
    rw [dualDD₁_cycleFillingLift hd c]
    rw [dualDStarCompressLinear_embed B 1 c.1 c.2.1]
    exact starMapInverse_starMap c.1
  right_inv y := by
    apply Subtype.ext
    apply dualDFormToChain_injective (d - 1)
    change dualDFormToChain (d - 1)
      (dualDD₁ (dualDCycleFillingLift (dualDRangeToCycle hd y))) =
        dualDFormToChain (d - 1) y.1
    rw [dualDD₁_cycleFillingLift hd]
    rw [dualDStarCompressLinear_embed B 1
      (dualDRangeToCycle hd y).1 (dualDRangeToCycle hd y).2.1]
    rw [dualDRangeToCycle_val]
    exact starMap_starMapInverse (dualDFormToChain (d - 1) y.1)
  map_add' x y := by
    apply Subtype.ext
    change dualDD₁ (dualDCycleFillingLift (x + y)) =
      dualDD₁ (dualDCycleFillingLift x) + dualDD₁ (dualDCycleFillingLift y)
    exact map_add (dualDD₁.comp dualDCycleFillingLift) x y
  map_smul' a x := by
    apply Subtype.ext
    change dualDD₁ (dualDCycleFillingLift (a • x)) =
      a • dualDD₁ (dualDCycleFillingLift x)
    exact map_smul (dualDD₁.comp dualDCycleFillingLift) a x

/-- Zero extension from a fixed-degree dual form carrier preserves the
Euclidean inner product. -/
theorem dualDFormToChain_inner {d : ℕ} {B : Box d} (k : ℕ)
    (u v : EuclideanSpace ℝ (DualDForm B k)) :
    inner ℝ (finsuppToEuclidean (dualDFormToChain k u))
        (finsuppToEuclidean (dualDFormToChain k v)) = inner ℝ u v := by
  classical
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [finsuppToEuclidean_apply, RCLike.inner_apply]
  let f : DualCell d B → ℝ := fun c =>
    dualDFormToChain k v c * dualDFormToChain k u c
  have hout (c : {c : DualCell d B // dualCellDegree c ≠ k}) :
      f c.1 = 0 := by
    have hnot : c.1 ∉ Set.range (dualDFormEmbedding (B := B) k) := by
      rintro ⟨a, ha⟩
      apply c.2
      rw [← ha]
      exact a.2
    have hu : dualDFormToChain k u c.1 = 0 := by
      change dualDEmbedSubtype (dualDFormEmbedding (B := B) k)
        (euclideanToFinsupp u) c.1 = 0
      rw [dualDEmbedSubtype_eq_embDomain]
      exact Finsupp.embDomain_of_notMem_range _ _ _ hnot
    simp [f, hu]
  have houtsum :
      (∑ a : {c : DualCell d B // dualCellDegree c ≠ k}, f a.1) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact hout a
  have hparts := (Fintype.sum_subtype_add_sum_subtype
    (fun c : DualCell d B => dualCellDegree c = k) f).symm
  have hpos :
      @Finset.sum {c : DualCell d B // dualCellDegree c = k} ℝ inferInstance
        (@Finset.univ _
          (Subtype.fintype (fun c : DualCell d B => dualCellDegree c = k)))
        (fun a => f a.1) =
        ∑ a : DualDForm B k, f (dualDFormEmbedding k a) := by
    let e : {c : DualCell d B // dualCellDegree c = k} ≃ DualDForm B k :=
      Equiv.refl _
    exact @Fintype.sum_equiv
      {c : DualCell d B // dualCellDegree c = k} (DualDForm B k) ℝ
      (Subtype.fintype (fun c : DualCell d B => dualCellDegree c = k))
      (dualDFormFintype k) inferInstance e _ _
      (by intro a; rfl)
  rw [hpos] at hparts
  have hin (a : DualDForm B k) :
      f (dualDFormEmbedding k a) = v a * u a := by
    have hu : dualDFormToChain k u (dualDFormEmbedding k a) = u a := by
      change dualDEmbedSubtype (dualDFormEmbedding (B := B) k)
        (euclideanToFinsupp u) (dualDFormEmbedding k a) = u a
      exact dualDEmbedSubtype_apply_at_image _ _ _
    have hv : dualDFormToChain k v (dualDFormEmbedding k a) = v a := by
      change dualDEmbedSubtype (dualDFormEmbedding (B := B) k)
        (euclideanToFinsupp v) (dualDFormEmbedding k a) = v a
      exact dualDEmbedSubtype_apply_at_image _ _ _
    simp [f, hu, hv]
  change (∑ c : DualCell d B, f c) = ∑ a : DualDForm B k, v a * u a
  calc
    _ = (∑ a : DualDForm B k, f (dualDFormEmbedding k a)) +
        ∑ a : {c : DualCell d B // dualCellDegree c ≠ k}, f a.1 := by
          exact hparts
    _ = ∑ a : DualDForm B k, v a * u a := by
          rw [houtsum, add_zero]
          apply Finset.sum_congr rfl
          intro a ha
          exact hin a
    _ = inner ℝ u v := by
          rw [PiLp.inner_apply]
          simp [RCLike.inner_apply, mul_comm]

/-- The image basis obtained by differentiating the real cycle basis through
the prism chart. -/
noncomputable def dualDImageCycleBasis {d : ℕ} (hd : 3 ≤ d) (B : Box d) :
    Basis (Fin (degreeOneCycleBasis B).1) ℝ
      (LinearMap.range (dualDD₁ (B := B))) :=
  (degreeOneRealCycleBasisExplicit B).map (dualDCycleRangeEquiv hd)

@[simp] theorem dualDImageCycleBasis_apply {d : ℕ} (hd : 3 ≤ d)
    (B : Box d) (i : Fin (degreeOneCycleBasis B).1) :
    dualDImageCycleBasis hd B i =
      dualDCycleRangeEquiv hd (degreeOneRealCycleBasisExplicit B i) := by
  rfl

/-- Under zero extension, a cycle image basis vector is the cubical star of
the corresponding integral bond cycle. -/
theorem dualDImageCycleBasis_toChain {d : ℕ} (hd : 3 ≤ d)
    (B : Box d) (i : Fin (degreeOneCycleBasis B).1) :
    dualDFormToChain (d - 1)
        ((dualDImageCycleBasis hd B i : LinearMap.range dualDD₁) :
          EuclideanSpace ℝ (DualDForm B (d - 1))) =
      starMap (castIntegerChain (degreeOneCycleBasisChain B i)) := by
  rw [dualDImageCycleBasis_apply]
  change dualDFormToChain (d - 1)
    (dualDD₁ (dualDCycleFillingLift (degreeOneRealCycleBasisExplicit B i))) = _
  rw [dualDD₁_cycleFillingLift hd]
  rw [dualDStarCompressLinear_embed B 1 _
    (degreeOneRealCycleBasisExplicit B i).2.1]
  rw [degreeOneRealCycleBasisExplicit_val]

noncomputable def dualDImageCycleBasisForHodge {d : ℕ} (hd : 3 ≤ d)
    (B : Box d) :
    Basis (Fin (degreeOneCycleBasis B).1) ℝ
      ((dualDExactOneComplex hd B).d₁.range) := by
  change Basis (Fin (degreeOneCycleBasis B).1) ℝ (LinearMap.range dualDD₁)
  exact dualDImageCycleBasis hd B

/-- The Hodge image Gram matrix in the all-D cycle chart is the primal
bond-cycle Gram matrix. -/
theorem dualDImageCycleGram_eq_cycleGram {d : ℕ} (hd : 3 ≤ d)
    (B : Box d) :
    Matrix.gram ℝ (fun i =>
      (dualDImageCycleBasis hd B i : EuclideanSpace ℝ (DualDForm B (d - 1)))) =
      degreeOneCycleGramMatrix B := by
  ext i j
  simp only [Matrix.gram_apply]
  have hchain (a : Fin (degreeOneCycleBasis B).1) :
      dualDFormToChain (d - 1)
          ((dualDImageCycleBasis hd B) a : EuclideanSpace ℝ
            (DualDForm B (d - 1))) =
        starMap (castIntegerChain (degreeOneCycleBasisChain B a)) := by
    rw [dualDImageCycleBasis_apply]
    change dualDFormToChain (d - 1)
      (dualDD₁ (dualDCycleFillingLift (degreeOneRealCycleBasisExplicit B a))) = _
    rw [dualDD₁_cycleFillingLift hd]
    rw [dualDStarCompressLinear_embed B 1 _
      (degreeOneRealCycleBasisExplicit B a).2.1]
    rw [degreeOneRealCycleBasisExplicit_val]
  change inner ℝ (dualDImageCycleBasis hd B i).1
      (dualDImageCycleBasis hd B j).1 = _
  rw [← dualDFormToChain_inner (d - 1)
    (dualDImageCycleBasis hd B i).1 (dualDImageCycleBasis hd B j).1]
  rw [hchain i, hchain j]
  simp only [degreeOneCycleGramMatrix, Matrix.gram_apply]
  exact starMap_finsuppToEuclidean_inner _ _

/-- Inverse Hodge energy in the cubical chord chart: the source is evaluated
on fixed plaquette lifts, and the inverse cycle Gram matrix gives the dual
quadratic. -/
theorem dualDHodgeInverse_eq_inverseCycleGram {d : ℕ} (hd : 3 ≤ d)
    (B : Box d) (μ : DualDCoClosed hd B) :
    inner ℝ μ.1
        (hodgeInverseOnCoClosed (dualDExactOneComplex hd B) μ).1 =
      dotProduct
        (hodgeLiftCoordinates (dualDExactOneComplex hd B)
          (dualDImageCycleBasisForHodge hd B)
          (dualDCycleFillingLift ∘ degreeOneRealCycleBasisExplicit B) μ)
        ((degreeOneCycleGramMatrix B)⁻¹.mulVec
          (hodgeLiftCoordinates (dualDExactOneComplex hd B)
            (dualDImageCycleBasisForHodge hd B)
            (dualDCycleFillingLift ∘ degreeOneRealCycleBasisExplicit B) μ)) := by
  let C := dualDExactOneComplex hd B
  let b := dualDImageCycleBasisForHodge hd B
  let lift : Fin (degreeOneCycleBasis B).1 →
      EuclideanSpace ℝ (DualDForm B (d - 2)) :=
    dualDCycleFillingLift ∘ degreeOneRealCycleBasisExplicit B
  have hlift (i : Fin (degreeOneCycleBasis B).1) :
      C.d₁ (lift i) = (b i : EuclideanSpace ℝ (DualDForm B (d - 1))) := by
    change dualDD₁ (dualDCycleFillingLift
        (degreeOneRealCycleBasisExplicit B i)) =
      (dualDImageCycleBasis hd B i : EuclideanSpace ℝ (DualDForm B (d - 1)))
    rw [dualDImageCycleBasis_apply]
    rfl
  have hgram : hodgeImageGram C b = degreeOneCycleGramMatrix B := by
    change Matrix.gram ℝ (fun i =>
      (dualDImageCycleBasisForHodge hd B i : EuclideanSpace ℝ
        (DualDForm B (d - 1)))) = degreeOneCycleGramMatrix B
    exact dualDImageCycleGram_eq_cycleGram hd B
  have h := hodgeInverseQuadratic_eq_inverseImageGram C b lift hlift μ
  rw [hgram] at h
  simpa [C, b, lift, hodgeLiftCoordinates] using h

/-- The higher-form vector of the XY endpoint path, obtained by star and
compression from its primal bond chain. -/
noncomputable def dualDXYPathVector {d : ℕ} {B : Box d}
    (x y : XYSites B) : EuclideanSpace ℝ (DualDForm B (d - 1)) :=
  dualDStarCompressLinear (B := B) 1
    (castIntegerChain (xyBondModeChain (xyEndpointPathModes x y)))

theorem dualDXYPathVector_embed {d : ℕ} {B : Box d}
    (x y : XYSites B) :
    dualDFormToChain (d - 1) (dualDXYPathVector x y) =
      starMap (castIntegerChain (xyBondModeChain (xyEndpointPathModes x y))) := by
  exact dualDStarCompressLinear_embed B 1 _ (by
    intro c hc
    exact xyBondModeChain_homogeneousSupport _ c
      (Finsupp.support_mapRange hc))

/-- For any vector in the top form carrier, its adjoint derivative is
co-closed because the finite complex squares to zero. -/
theorem dualDD₁_adjoint_mem_coClosed {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (φ : EuclideanSpace ℝ (DualDForm B (d - 1))) :
    (dualDD₁ (B := B)).adjoint φ ∈ coClosed (dualDExactOneComplex hd B) := by
  apply LinearMap.mem_ker.mpr
  change (dualDD₀ (B := B)).adjoint
      ((dualDD₁ (B := B)).adjoint φ) = 0
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  let z := (dualDD₀ (B := B)).adjoint
    ((dualDD₁ (B := B)).adjoint φ)
  have hz : (dualDD₁ (B := B)) ((dualDD₀ (B := B)) z) = 0 := by
    have h := congrArg (fun f :
        EuclideanSpace ℝ (DualDForm B (d - 3)) →ₗ[ℝ]
          EuclideanSpace ℝ (DualDForm B (d - 1)) => f z)
      (dualDD₁_comp_D₀_zero (B := B) hd)
    change (dualDD₁ (B := B)) ((dualDD₀ (B := B)) z) = 0 at h
    exact h
  calc
    inner ℝ z z = inner ℝ ((dualDD₁ (B := B)).adjoint φ)
        ((dualDD₀ (B := B)) z) := by
          rw [show z = (dualDD₀ (B := B)).adjoint
            ((dualDD₁ (B := B)).adjoint φ) from rfl]
          exact LinearMap.adjoint_inner_left _ _ _
    _ = inner ℝ φ ((dualDD₁ (B := B))
          ((dualDD₀ (B := B)) z)) :=
            LinearMap.adjoint_inner_left _ _ _
    _ = 0 := by rw [hz]; simp [inner]

/-- The endpoint path source is its codifferential and is co-closed. -/
noncomputable def dualDXYPathSource {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (x y : XYSites B) : DualDCoClosed hd B :=
  ⟨(dualDD₁ (B := B)).adjoint (dualDXYPathVector x y),
    dualDD₁_adjoint_mem_coClosed hd (dualDXYPathVector x y)⟩

/-- The finite Hodge projection of the endpoint path source. -/
noncomputable def dualDXYPathTau {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (x y : XYSites B) : DualDCoClosed hd B :=
  hodgeInverseOnCoClosed (dualDExactOneComplex hd B)
    (dualDXYPathSource hd x y)

/-- The endpoint residual energy after its co-closed Hodge projection. -/
noncomputable def dualDXYResidualEnergy {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (x y : XYSites B) : ℝ :=
  inner ℝ (dualDXYPathVector x y) (dualDXYPathVector x y) -
    inner ℝ (dualDXYPathSource hd x y).1 (dualDXYPathTau hd x y).1

/-- The real dual current with prescribed cycle-character coordinates `q`.
It is the adjoint image of the inverse-Gram linear combination of the cycle
image basis. -/
noncomputable def dualDCoordinateCurrent {d : ℕ} (hd : 3 ≤ d) (B : Box d)
    (q : Fin (degreeOneCycleBasis B).1 → ℝ) : DualDCoClosed hd B := by
  let C := dualDExactOneComplex hd B
  let G := degreeOneCycleGramMatrix B
  let b := dualDImageCycleBasisForHodge hd B
  let a := G⁻¹.mulVec q
  let y : EuclideanSpace ℝ (DualDForm B (d - 1)) :=
    ∑ i, a i • (b i : EuclideanSpace ℝ (DualDForm B (d - 1)))
  refine ⟨C.d₁.adjoint y, ?_⟩
  apply LinearMap.mem_ker.mpr
  change C.d₀.adjoint (C.d₁.adjoint y) = 0
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  let z := C.d₀.adjoint (C.d₁.adjoint y)
  have hz : C.d₁ (C.d₀ z) = 0 := by
    have h := congrArg (fun f :
        EuclideanSpace ℝ (DualDForm B (d - 3)) →ₗ[ℝ]
          EuclideanSpace ℝ (DualDForm B (d - 1)) => f z)
      (dualDD₁_comp_D₀_zero (B := B) hd)
    change C.d₁ (C.d₀ z) = 0 at h
    exact h
  calc
    inner ℝ z z = inner ℝ (C.d₁.adjoint y) (C.d₀ z) := by
      rw [show z = C.d₀.adjoint (C.d₁.adjoint y) from rfl]
      exact LinearMap.adjoint_inner_left _ _ _
    _ = inner ℝ y (C.d₁ (C.d₀ z)) :=
      LinearMap.adjoint_inner_left _ _ _
    _ = 0 := by rw [hz]; simp [inner]

/-- The coordinate current is the unique Hodge representative whose lift
pairings are the prescribed cycle coordinates. -/
theorem dualDCoordinateCurrent_liftCoordinates {d : ℕ} (hd : 3 ≤ d)
    (B : Box d) (q : Fin (degreeOneCycleBasis B).1 → ℝ) :
    hodgeLiftCoordinates (dualDExactOneComplex hd B)
      (dualDImageCycleBasisForHodge hd B)
      (dualDCycleFillingLift ∘ degreeOneRealCycleBasisExplicit B)
      (dualDCoordinateCurrent hd B q) = q := by
  let C := dualDExactOneComplex hd B
  let G := degreeOneCycleGramMatrix B
  let b := dualDImageCycleBasisForHodge hd B
  let lift : Fin (degreeOneCycleBasis B).1 →
      EuclideanSpace ℝ (DualDForm B (d - 2)) :=
    dualDCycleFillingLift ∘ degreeOneRealCycleBasisExplicit B
  let a := G⁻¹.mulVec q
  let y : EuclideanSpace ℝ (DualDForm B (d - 1)) :=
    ∑ j, a j • (b j : EuclideanSpace ℝ (DualDForm B (d - 1)))
  have hlift (i : Fin (degreeOneCycleBasis B).1) :
      C.d₁ (lift i) = (b i : EuclideanSpace ℝ (DualDForm B (d - 1))) := by
    change dualDD₁ (dualDCycleFillingLift
        (degreeOneRealCycleBasisExplicit B i)) =
      (dualDImageCycleBasis hd B i : EuclideanSpace ℝ (DualDForm B (d - 1)))
    rw [dualDImageCycleBasis_apply]
    rfl
  have hgram : Matrix.gram ℝ (fun i =>
      (dualDImageCycleBasisForHodge hd B i :
        EuclideanSpace ℝ (DualDForm B (d - 1)))) = G :=
    dualDImageCycleGram_eq_cycleGram hd B
  have hentry (i j : Fin (degreeOneCycleBasis B).1) :
      inner ℝ (b i : EuclideanSpace ℝ (DualDForm B (d - 1)))
          (b j : EuclideanSpace ℝ (DualDForm B (d - 1))) = G i j := by
    have h := congrFun (congrFun hgram i) j
    simpa [Matrix.gram_apply, G, b] using h
  have hsymm (i j : Fin (degreeOneCycleBasis B).1) :
      G j i = G i j := by
    rw [← hentry j i, ← hentry i j, real_inner_comm]
  have hmatrix (i : Fin (degreeOneCycleBasis B).1) :
      inner ℝ y (b i : EuclideanSpace ℝ (DualDForm B (d - 1))) =
        (G.mulVec a) i := by
    rw [show y = ∑ j, a j •
      (b j : EuclideanSpace ℝ (DualDForm B (d - 1))) from rfl, sum_inner]
    simp only [real_inner_smul_left]
    rw [show (G.mulVec a) i = ∑ j, G i j * a j by
      simp [Matrix.mulVec, dotProduct]]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hentry j i, hsymm i j]
    ring
  have hGpos : G.PosDef := degreeOneCycleGramMatrix_posDef B
  let _ : Invertible G := hGpos.isUnit.invertible
  have hGq : G.mulVec a = q := by
    dsimp [a]
    calc
      G.mulVec (G⁻¹.mulVec q) = (G * G⁻¹).mulVec q := by
        rw [Matrix.mulVec_mulVec]
      _ = q := by rw [Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  funext i
  change inner ℝ
    ((dualDD₁ (B := B)).adjoint y) (lift i) = q i
  rw [LinearMap.adjoint_inner_left]
  change inner ℝ y (C.d₁ (lift i)) = q i
  rw [hlift i, hmatrix i]
  exact congrFun hGq i

end FroehlichSpencer.FS82.XY

end
