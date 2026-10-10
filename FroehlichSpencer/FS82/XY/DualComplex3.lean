/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.FiniteQuotientGaussian
public import FroehlichSpencer.FS82.Cubical.DualStokes
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex

/-!
# The 3D finite ground dual one-form complex and its quotient Gaussian

The finite carriers are all dual cells in the rectangular dual box; fields are
extended by zero outside the box.

The differential is the cubical dual
exterior difference, transported from the primal boundary by the orientation-
matched star.

Exactness at degree one follows by filling a positive-degree
primal 2-cycle with the generic cubical real filling operator.

Source: FS82 journal (4.13)--(4.25), Fröhlich–Spencer (1982).
-/

public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open scoped InnerProductSpace

noncomputable section
open Classical

abbrev Dual3Box := Box 3


abbrev Dual3Vertices (B : Dual3Box) :=
  {c : DualCell 3 B // dualCellDegree c = 0}

abbrev Dual3Links (B : Dual3Box) :=
  {c : DualCell 3 B // dualCellDegree c = 1}

abbrev Dual3Plaquettes (B : Dual3Box) :=
  {c : DualCell 3 B // dualCellDegree c = 2}

noncomputable instance dual3VerticesFintype {B : Dual3Box} :
    Fintype (Dual3Vertices B) := Fintype.ofFinite _

instance dual3VerticesDecidableEq {B : Dual3Box} :
    DecidableEq (Dual3Vertices B) := inferInstance

noncomputable instance dual3LinksFintype {B : Dual3Box} :
    Fintype (Dual3Links B) := Fintype.ofFinite _

instance dual3LinksDecidableEq {B : Dual3Box} :
    DecidableEq (Dual3Links B) := inferInstance

noncomputable instance dual3PlaquettesFintype {B : Dual3Box} :
    Fintype (Dual3Plaquettes B) := Fintype.ofFinite _

instance dual3PlaquettesDecidableEq {B : Dual3Box} :
    DecidableEq (Dual3Plaquettes B) := inferInstance

@[expose] def dual3VerticesEmbedding {B : Dual3Box} :
    Dual3Vertices B ↪ DualCell 3 B := Function.Embedding.subtype _

@[expose] def dual3LinksEmbedding {B : Dual3Box} :
    Dual3Links B ↪ DualCell 3 B := Function.Embedding.subtype _

@[expose] def dual3PlaquettesEmbedding {B : Dual3Box} :
    Dual3Plaquettes B ↪ DualCell 3 B := Function.Embedding.subtype _

@[expose] noncomputable def dual3EmbedSubtype {α : Type*} [Fintype α]
    [DecidableEq α] {B : Dual3Box} (f : α ↪ DualCell 3 B) :
    (α →₀ ℝ) →ₗ[ℝ] DualRealChain 3 B :=
  Finsupp.linearCombination ℝ (fun a => Finsupp.single (f a) 1)

@[simp] theorem dual3EmbedSubtype_apply_single {α : Type*} [Fintype α]
    [DecidableEq α] {B : Dual3Box} (f : α ↪ DualCell 3 B) (a : α) (r : ℝ) :
    dual3EmbedSubtype f (Finsupp.single a r) = Finsupp.single (f a) r := by
  simp [dual3EmbedSubtype, Finsupp.linearCombination_single]

@[expose] noncomputable def dual3CompressSubtype {α : Type*} [Fintype α]
    [DecidableEq α] {B : Dual3Box} (f : α ↪ DualCell 3 B) :
    DualRealChain 3 B →ₗ[ℝ] (α →₀ ℝ) where
  toFun q := Finsupp.comapDomain f q f.injective.injOn
  map_add' q r := Finsupp.comapDomain_add_of_injective f.injective q r
  map_smul' a q := by
    ext x
    simp [Finsupp.comapDomain_apply]


theorem dual3EmbedSubtype_eq_embDomain {α : Type*} [Fintype α]
    [DecidableEq α] {B : Dual3Box} (f : α ↪ DualCell 3 B) (q : α →₀ ℝ) :
    dual3EmbedSubtype f q = Finsupp.embDomain f q := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [dual3EmbedSubtype]
  | add q r hq hr =>
      rw [map_add, hq, hr]
      ext c
      simp [Finsupp.embDomain_apply]
  | single a r =>
      simp [dual3EmbedSubtype, Finsupp.linearCombination_single,
        Finsupp.embDomain_single]

@[simp] theorem dual3EmbedSubtype_apply_at_image {α : Type*} [Fintype α]
    [DecidableEq α] {B : Dual3Box} (f : α ↪ DualCell 3 B) (q : α →₀ ℝ) (a : α) :
    dual3EmbedSubtype f q (f a) = q a := by
  rw [dual3EmbedSubtype_eq_embDomain]
  simp [Finsupp.embDomain_apply]

theorem dual3EmbedCompress_eq_self_of_support {α : Type*} [Fintype α]
    [DecidableEq α] {B : Dual3Box} (f : α ↪ DualCell 3 B) (q : DualRealChain 3 B)
    (hq : (q.support : Set (DualCell 3 B)) ⊆ Set.range f) :
    dual3EmbedSubtype f (dual3CompressSubtype f q) = q := by
  rw [dual3EmbedSubtype_eq_embDomain]
  exact Finsupp.embDomain_comapDomain hq

theorem dual3EmbedSubtype_homogeneous {α : Type*} [Fintype α]
    [DecidableEq α] {B : Dual3Box} (f : α ↪ DualCell 3 B) (degree : ℕ)
    (hf : ∀ a, dualCellDegree (f a) = degree) (q : α →₀ ℝ) :
    dualRealHomogeneousSupport (dual3EmbedSubtype f q) degree := by
  rw [dual3EmbedSubtype_eq_embDomain]
  intro c hc
  rw [Finsupp.support_embDomain] at hc
  rcases Finset.mem_map.mp hc with ⟨a, ha, rfl⟩
  exact hf a

@[expose] noncomputable def dual3VerticesToChain {B : Dual3Box} :
    EuclideanSpace ℝ (Dual3Vertices B) →ₗ[ℝ] DualRealChain 3 B :=
  (dual3EmbedSubtype dual3VerticesEmbedding).comp euclideanToFinsupp

@[expose] noncomputable def dual3LinksToChain {B : Dual3Box} :
    EuclideanSpace ℝ (Dual3Links B) →ₗ[ℝ] DualRealChain 3 B :=
  (dual3EmbedSubtype dual3LinksEmbedding).comp euclideanToFinsupp

@[expose] noncomputable def dual3PlaquettesToChain {B : Dual3Box} :
    EuclideanSpace ℝ (Dual3Plaquettes B) →ₗ[ℝ] DualRealChain 3 B :=
  (dual3EmbedSubtype dual3PlaquettesEmbedding).comp euclideanToFinsupp

theorem dual3StarComplementaryDegree {B : Dual3Box} (c : Cell 3 B) :
    dualCellDegree (primalDualCellEquiv c) + cellDegree c = 3 := by
  have haxes : dualCellAxes (primalDualCellEquiv c) =
      Finset.univ \ cellAxes c := by
    ext i
    cases h : c i with
    | inl v =>
        simp only [dualCellAxes, cellAxes, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.mem_sdiff]
        simp [primalDualCellEquiv, h, coordIsEdge]
    | inr e =>
        simp only [dualCellAxes, cellAxes, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.mem_sdiff]
        simp [primalDualCellEquiv, h, coordIsEdge]
  have hcard := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (cellAxes c))
  simpa [dualCellDegree, cellDegree, haxes] using hcard

theorem dual3StarMap_homogeneousSupport {B : Dual3Box}
    (q : RealChain 3 B) (k : ℕ) (hq : realHomogeneousSupport q k) :
    dualRealHomogeneousSupport (starMap q) (3 - k) := by
  intro c hc
  have hmem : primalDualCellEquiv.symm c ∈ q.support := by
    simpa [starMap, Finsupp.equivMapDomain_apply] using hc
  have h := dual3StarComplementaryDegree (primalDualCellEquiv.symm c)
  simp only [Equiv.apply_symm_apply] at h
  rw [hq _ hmem] at h
  omega

theorem dual3StarMapInverse_homogeneousSupport {B : Dual3Box}
    (q : DualRealChain 3 B) (k : ℕ) (hq : dualRealHomogeneousSupport q k) :
    realHomogeneousSupport (starMapInverse q) (3 - k) := by
  intro c hc
  have hmem : primalDualCellEquiv c ∈ q.support := by
    simpa [starMapInverse, Finsupp.equivMapDomain_apply] using hc
  have h := dual3StarComplementaryDegree c
  rw [hq _ hmem] at h
  omega

theorem dual3ExteriorDifference_homogeneousSupport {B : Dual3Box}
    (q : DualRealChain 3 B) (k : ℕ) (hk : k < 3)
    (hq : dualRealHomogeneousSupport q k) :
    dualRealHomogeneousSupport (dualExteriorDifference q) (k + 1) := by
  have hs := dual3StarMapInverse_homogeneousSupport q k hq
  have hb := realBoundary_homogeneousSupport (starMapInverse q) (3 - k)
    (by omega) hs
  have hd := dual3StarMap_homogeneousSupport (realBoundary (starMapInverse q))
    (3 - k - 1) hb
  have hdeg : 3 - (3 - k - 1) = k + 1 := by omega
  rw [hdeg] at hd
  simpa [dualExteriorDifference] using hd

@[expose] noncomputable def dual3D₀ {B : Dual3Box} :
    EuclideanSpace ℝ (Dual3Vertices B) →ₗ[ℝ]
      EuclideanSpace ℝ (Dual3Links B) :=
  finsuppToEuclidean.comp
    ((dual3CompressSubtype dual3LinksEmbedding).comp
      (dualExteriorDifference.comp dual3VerticesToChain))

@[expose] noncomputable def dual3D₁ {B : Dual3Box} :
    EuclideanSpace ℝ (Dual3Links B) →ₗ[ℝ]
      EuclideanSpace ℝ (Dual3Plaquettes B) :=
  finsuppToEuclidean.comp
    ((dual3CompressSubtype dual3PlaquettesEmbedding).comp
      (dualExteriorDifference.comp dual3LinksToChain))

theorem dual3D₀_output_homogeneous {B : Dual3Box}
    (u : EuclideanSpace ℝ (Dual3Vertices B)) :
    dualRealHomogeneousSupport
      (dualExteriorDifference (dual3VerticesToChain u)) 1 := by
  exact dual3ExteriorDifference_homogeneousSupport _ 0 (by omega)
    (dual3EmbedSubtype_homogeneous dual3VerticesEmbedding 0
      (by intro a; exact a.2) (euclideanToFinsupp u))

theorem dual3D₀_embed_eq_derivative {B : Dual3Box}
    (u : EuclideanSpace ℝ (Dual3Vertices B)) :
    dual3LinksToChain (dual3D₀ u) =
      dualExteriorDifference (dual3VerticesToChain u) := by
  simp only [dual3LinksToChain, dual3D₀, LinearMap.comp_apply,
    euclideanToFinsupp_finsuppToEuclidean]
  apply dual3EmbedCompress_eq_self_of_support dual3LinksEmbedding
  intro c hc
  have hdeg : dualCellDegree c = 1 := dual3D₀_output_homogeneous u c hc
  exact ⟨⟨c, hdeg⟩, rfl⟩

theorem dual3D₁_output_homogeneous {B : Dual3Box}
    (u : EuclideanSpace ℝ (Dual3Links B)) :
    dualRealHomogeneousSupport
      (dualExteriorDifference (dual3LinksToChain u)) 2 := by
  exact dual3ExteriorDifference_homogeneousSupport _ 1 (by omega)
    (dual3EmbedSubtype_homogeneous dual3LinksEmbedding 1
      (by intro a; exact a.2) (euclideanToFinsupp u))

theorem dual3D₁_embed_eq_derivative {B : Dual3Box}
    (u : EuclideanSpace ℝ (Dual3Links B)) :
    dual3PlaquettesToChain (dual3D₁ u) =
      dualExteriorDifference (dual3LinksToChain u) := by
  simp only [dual3PlaquettesToChain, dual3D₁, LinearMap.comp_apply,
    euclideanToFinsupp_finsuppToEuclidean]
  apply dual3EmbedCompress_eq_self_of_support dual3PlaquettesEmbedding
  intro c hc
  have hdeg : dualCellDegree c = 2 := dual3D₁_output_homogeneous u c hc
  exact ⟨⟨c, hdeg⟩, rfl⟩

theorem dual3LinksToChain_injective {B : Dual3Box} :
    Function.Injective (@dual3LinksToChain B) := by
  intro x y h
  ext a
  have hv := congrArg (fun q : DualRealChain 3 B => q (dual3LinksEmbedding a)) h
  simpa [dual3LinksToChain, LinearMap.comp_apply, euclideanToFinsupp_apply] using hv

theorem dual3PlaquettesToChain_injective {B : Dual3Box} :
    Function.Injective (@dual3PlaquettesToChain B) := by
  intro x y h
  ext a
  have hv := congrArg (fun q : DualRealChain 3 B => q (dual3PlaquettesEmbedding a)) h
  simpa [dual3PlaquettesToChain, LinearMap.comp_apply,
    euclideanToFinsupp_apply] using hv

private theorem dual3RealBoundary_square_zero {B : Dual3Box} :
    (realBoundary (d := 3) (B := B)).comp
      (realBoundary (d := 3) (B := B)) = 0 := by
  change realifyLinearMap (boundary (d := 3) (B := B)) *
      realifyLinearMap (boundary (d := 3) (B := B)) = 0
  rw [← realifyLinearMap_mul, boundary_square_zero]
  apply LinearMap.ext
  intro q
  ext c
  change (Finsupp.linearCombination ℝ (fun x : Cell 3 B =>
    castIntegerChain ((0 : Chain 3 B →ₗ[ℤ] Chain 3 B) (basisChain x))) q) c = 0
  have hfun : (fun x : Cell 3 B => castIntegerChain
      ((0 : Chain 3 B →ₗ[ℤ] Chain 3 B) (basisChain x))) = 0 := by
    funext x
    simp [castIntegerChain]
  rw [hfun, Finsupp.linearCombination_zero]
  simp

private theorem dual3ExteriorDifference_square_zero {B : Dual3Box} :
    (dualExteriorDifference (d := 3) (B := B)).comp
      (dualExteriorDifference (d := 3) (B := B)) = 0 := by
  apply LinearMap.ext
  intro q
  change starMap (realBoundary (starMapInverse
      (starMap (realBoundary (starMapInverse q))))) = 0
  rw [starMapInverse_starMap]
  have h := congrArg (fun T : RealChain 3 B →ₗ[ℝ] RealChain 3 B =>
    T (starMapInverse q)) dual3RealBoundary_square_zero
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [h]
  simp

theorem dual3D₁_comp_D₀_zero {B : Dual3Box} :
    (dual3D₁ (B := B)).comp (dual3D₀ (B := B)) = 0 := by
  apply LinearMap.ext
  intro u
  apply dual3PlaquettesToChain_injective
  calc
    dual3PlaquettesToChain (dual3D₁ (dual3D₀ u)) =
        dualExteriorDifference (dual3LinksToChain (dual3D₀ u)) :=
      dual3D₁_embed_eq_derivative (dual3D₀ u)
    _ = dualExteriorDifference
        (dualExteriorDifference (dual3VerticesToChain u)) := by
      rw [dual3D₀_embed_eq_derivative]
    _ = dual3PlaquettesToChain
        (0 : EuclideanSpace ℝ (Dual3Plaquettes B)) := by
      have h := congrArg (fun T : DualRealChain 3 B →ₗ[ℝ]
        DualRealChain 3 B => T (dual3VerticesToChain u))
        dual3ExteriorDifference_square_zero
      simpa [LinearMap.comp_apply, dual3PlaquettesToChain] using h

theorem dual3D₀_exactOne {B : Dual3Box}
    (u : EuclideanSpace ℝ (Dual3Links B)) (hu : dual3D₁ u = 0) :
    u ∈ (dual3D₀ (B := B)).range := by
  let q : DualRealChain 3 B := dual3LinksToChain u
  have hclosed : dualExteriorDifference q = 0 := by
    calc
      dualExteriorDifference q = dual3PlaquettesToChain (dual3D₁ u) :=
        (dual3D₁_embed_eq_derivative u).symm
      _ = 0 := by rw [hu]; simp [dual3PlaquettesToChain]
  have hqdegree : dualRealHomogeneousSupport q 1 :=
    dual3EmbedSubtype_homogeneous dual3LinksEmbedding 1
      (by intro a; exact a.2) (euclideanToFinsupp u)
  let p : RealChain 3 B := starMapInverse q
  have hpdegree : realHomogeneousSupport p 2 := by
    exact dual3StarMapInverse_homogeneousSupport q 1 hqdegree
  have hstar : starMap p = q := by
    simpa [p] using starMap_starMapInverse q
  have hpcycle : realBoundary p = 0 := by
    have h := primalDualStar_boundary_identity p
    rw [hstar, hclosed] at h
    simpa using h.symm
  let anchor : Anchor 3 B := fun i => ⟨0, Nat.zero_lt_succ _⟩
  obtain ⟨hfill, hdegree⟩ :=
    real_positiveDegree_filling anchor p 2 (by omega) hpdegree hpcycle
  let η : RealChain 3 B := realFillingOperator anchor p
  have hηdegree : realHomogeneousSupport η 3 := by
    simpa [η] using hdegree
  have hηboundary : realBoundary η = p := by
    simpa [η] using hfill
  have hηdualdegree : dualRealHomogeneousSupport (starMap η) 0 := by
    have h := dual3StarMap_homogeneousSupport η 3 hηdegree
    simpa using h
  have hηsupport : ((starMap η).support : Set (DualCell 3 B)) ⊆
      Set.range dual3VerticesEmbedding := by
    intro c hc
    have hdeg := hηdualdegree c hc
    exact ⟨⟨c, hdeg⟩, rfl⟩
  let v : EuclideanSpace ℝ (Dual3Vertices B) :=
    finsuppToEuclidean (dual3CompressSubtype dual3VerticesEmbedding (starMap η))
  have hη : dual3VerticesToChain v = starMap η := by
    dsimp [dual3VerticesToChain, v]
    rw [euclideanToFinsupp_finsuppToEuclidean]
    exact dual3EmbedCompress_eq_self_of_support dual3VerticesEmbedding
      (starMap η) hηsupport
  have hfill' : dual3LinksToChain (dual3D₀ v) = q := by
    calc
      dual3LinksToChain (dual3D₀ v) =
          dualExteriorDifference (dual3VerticesToChain v) :=
        dual3D₀_embed_eq_derivative v
      _ = dualExteriorDifference (starMap η) := by rw [hη]
      _ = starMap (realBoundary η) :=
        primalDualStar_incidence_identity η
      _ = q := by rw [hηboundary, hstar]
  apply LinearMap.mem_range.mpr
  refine ⟨v, ?_⟩
  exact dual3LinksToChain_injective hfill'

@[expose] noncomputable def dual3ExactOneComplex (B : Dual3Box) :
    ExactOneComplex (Dual3Vertices B) (Dual3Links B) (Dual3Plaquettes B) where
  d₀ := dual3D₀
  d₁ := dual3D₁
  complex := dual3D₁_comp_D₀_zero
  exactOne := by
    intro u hu
    exact dual3D₀_exactOne u hu

@[expose] noncomputable def dual3HodgeInverse {B : Dual3Box} :
    coClosed (dual3ExactOneComplex B) →ₗ[ℝ]
      coClosed (dual3ExactOneComplex B) :=
  hodgeInverseOnCoClosed (dual3ExactOneComplex B)

theorem dual3HodgeInverse_spec {B : Dual3Box}
    (μ : coClosed (dual3ExactOneComplex B)) :
    hodgeOnCoClosed (dual3ExactOneComplex B) (dual3HodgeInverse μ) = μ :=
  hodgeOnCoClosed_hodgeInverse (dual3ExactOneComplex B) μ

@[expose] noncomputable def dual3CovarianceQuadratic {B : Dual3Box}
    (β : ℝ) (μ : coClosed (dual3ExactOneComplex B)) : ℝ :=
  inner ℝ (μ : EuclideanSpace ℝ (Dual3Links B))
    ((β • dual3HodgeInverse μ : coClosed (dual3ExactOneComplex B)) :
      EuclideanSpace ℝ (Dual3Links B))

theorem dual3CovarianceQuadratic_eq_hodge {B : Dual3Box}
    (β : ℝ) (μ : coClosed (dual3ExactOneComplex B)) :
    dual3CovarianceQuadratic β μ =
      β * quotientCovarianceQuadratic (dual3ExactOneComplex B) μ := by
  simp [dual3CovarianceQuadratic, quotientCovarianceQuadratic,
    dual3HodgeInverse, real_inner_smul_right]


abbrev Dual3GaugeQuotient (B : Dual3Box) :=
  FiniteGaugeQuotient (dual3ExactOneComplex B)

@[expose] noncomputable def dual3QuotientGaussian {B : Dual3Box}
    (β : ℝ) (hβ : 0 ≤ β) : MeasureTheory.Measure (Dual3GaugeQuotient B) :=
  finiteComplexQuotientGaussian (dual3ExactOneComplex B) β hβ


theorem dual3QuotientGaussian_characteristic {B : Dual3Box} {β : ℝ}
    (hβ : 0 ≤ β) (μ : coClosed (dual3ExactOneComplex B)) :
    MeasureTheory.charFun
      (MeasureTheory.Measure.map
        (finiteComplexQuotientTestFunctional (dual3ExactOneComplex B) μ)
        (dual3QuotientGaussian (B := B) β hβ)) 1 =
      Complex.exp (-↑(dual3CovarianceQuadratic β μ / 2)) := by
  simpa [dual3QuotientGaussian, dual3CovarianceQuadratic,
    dual3HodgeInverse, finiteComplexAmbientCovariance_coClosed_apply] using
    finiteComplexQuotientGaussian_charFunDual
      (dual3ExactOneComplex B) hβ μ


end

end FroehlichSpencer.FS82.XY

end
