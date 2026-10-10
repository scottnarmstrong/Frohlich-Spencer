/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.FiniteHodge
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex
public import FroehlichSpencer.FS82.Cubical.DualStokes

/-!
# Grounded dual exact-one complexes in every dimension at least three

For a rectangular box in dimension `d ≥ 3`, the dual forms of degrees
`d - 3`, `d - 2`, and `d - 1` form an exact-one complex at the middle degree.
The proof transfers a closed dual `(d - 2)`-chain through the cubical star to
a primal 2-cycle and fills it by the dimension-generic prism operator.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open scoped InnerProductSpace

noncomputable section
open Classical

/-- The finite dual cells of a fixed cubical form degree. -/
abbrev DualDForm {d : ℕ} (B : Box d) (k : ℕ) :=
  {c : DualCell d B // dualCellDegree c = k}

noncomputable instance dualDFormFintype {d : ℕ} {B : Box d} (k : ℕ) :
    Fintype (DualDForm B k) := Fintype.ofFinite _

instance dualDFormDecidableEq {d : ℕ} {B : Box d} (k : ℕ) :
    DecidableEq (DualDForm B k) := inferInstance

def dualDFormEmbedding {d : ℕ} {B : Box d} (k : ℕ) :
    DualDForm B k ↪ DualCell d B := Function.Embedding.subtype _

noncomputable def dualDEmbedSubtype {d : ℕ} {B : Box d}
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α ↪ DualCell d B) : (α →₀ ℝ) →ₗ[ℝ] DualRealChain d B :=
  Finsupp.linearCombination ℝ (fun a => Finsupp.single (f a) 1)

@[simp] theorem dualDEmbedSubtype_apply_single {d : ℕ} {B : Box d}
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α ↪ DualCell d B) (a : α) (r : ℝ) :
    dualDEmbedSubtype f (Finsupp.single a r) = Finsupp.single (f a) r := by
  simp [dualDEmbedSubtype, Finsupp.linearCombination_single]

theorem dualDEmbedSubtype_eq_embDomain {d : ℕ} {B : Box d}
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α ↪ DualCell d B) (q : α →₀ ℝ) :
    dualDEmbedSubtype f q = Finsupp.embDomain f q := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [dualDEmbedSubtype]
  | add q r hq hr =>
      rw [map_add, hq, hr]
      ext c
      simp [Finsupp.embDomain_apply]
  | single a r =>
      simp [dualDEmbedSubtype, Finsupp.linearCombination_single,
        Finsupp.embDomain_single]

@[simp] theorem dualDEmbedSubtype_apply_at_image {d : ℕ} {B : Box d}
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α ↪ DualCell d B) (q : α →₀ ℝ) (a : α) :
    dualDEmbedSubtype f q (f a) = q a := by
  rw [dualDEmbedSubtype_eq_embDomain]
  simp [Finsupp.embDomain_apply]

noncomputable def dualDCompressSubtype {d : ℕ} {B : Box d}
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α ↪ DualCell d B) : DualRealChain d B →ₗ[ℝ] (α →₀ ℝ) where
  toFun q := Finsupp.comapDomain f q f.injective.injOn
  map_add' q r := Finsupp.comapDomain_add_of_injective f.injective q r
  map_smul' a q := by
    ext x
    simp [Finsupp.comapDomain_apply]

@[simp] theorem dualDCompressSubtype_apply {d : ℕ} {B : Box d}
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α ↪ DualCell d B) (q : DualRealChain d B) (a : α) :
    dualDCompressSubtype f q a = q (f a) := by
  simp [dualDCompressSubtype, Finsupp.comapDomain_apply]

theorem dualDEmbedCompress_eq_self_of_support {d : ℕ} {B : Box d}
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α ↪ DualCell d B) (q : DualRealChain d B)
    (hq : (q.support : Set (DualCell d B)) ⊆ Set.range f) :
    dualDEmbedSubtype f (dualDCompressSubtype f q) = q := by
  rw [dualDEmbedSubtype_eq_embDomain]
  exact Finsupp.embDomain_comapDomain hq

theorem dualDEmbedSubtype_homogeneous {d : ℕ} {B : Box d}
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α ↪ DualCell d B) (degree : ℕ)
    (hf : ∀ a, dualCellDegree (f a) = degree) (q : α →₀ ℝ) :
    dualRealHomogeneousSupport (dualDEmbedSubtype f q) degree := by
  rw [dualDEmbedSubtype_eq_embDomain]
  intro c hc
  rw [Finsupp.support_embDomain] at hc
  rcases Finset.mem_map.mp hc with ⟨a, ha, rfl⟩
  exact hf a

noncomputable def dualDFormToChain {d : ℕ} {B : Box d} (k : ℕ) :
    EuclideanSpace ℝ (DualDForm B k) →ₗ[ℝ] DualRealChain d B :=
  (dualDEmbedSubtype (dualDFormEmbedding k)).comp euclideanToFinsupp

theorem dualDStarComplementaryDegree {d : ℕ} {B : Box d}
    (c : Cell d B) :
    dualCellDegree (primalDualCellEquiv c) + cellDegree c = d := by
  have haxes : dualCellAxes (primalDualCellEquiv c) = Finset.univ \ cellAxes c := by
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

theorem dualDStarMap_homogeneousSupport {d : ℕ} {B : Box d}
    (q : RealChain d B) (k : ℕ) (hq : realHomogeneousSupport q k) :
    dualRealHomogeneousSupport (starMap q) (d - k) := by
  intro c hc
  have hmem : primalDualCellEquiv.symm c ∈ q.support := by
    simpa [starMap, Finsupp.equivMapDomain_apply] using hc
  have h := dualDStarComplementaryDegree (primalDualCellEquiv.symm c)
  simp only [Equiv.apply_symm_apply] at h
  rw [hq _ hmem] at h
  omega

theorem dualDStarMapInverse_homogeneousSupport {d : ℕ} {B : Box d}
    (q : DualRealChain d B) (k : ℕ)
    (hq : dualRealHomogeneousSupport q k) :
    realHomogeneousSupport (starMapInverse q) (d - k) := by
  intro c hc
  have hmem : primalDualCellEquiv c ∈ q.support := by
    simpa [starMapInverse, Finsupp.equivMapDomain_apply] using hc
  have h := dualDStarComplementaryDegree c
  rw [hq _ hmem] at h
  omega

theorem dualDExteriorDifference_homogeneousSupport {d : ℕ} {B : Box d}
    (q : DualRealChain d B) (k : ℕ) (hk : k < d)
    (hq : dualRealHomogeneousSupport q k) :
    dualRealHomogeneousSupport (dualExteriorDifference q) (k + 1) := by
  have hs := dualDStarMapInverse_homogeneousSupport q k hq
  have hb := realBoundary_homogeneousSupport (starMapInverse q) (d - k)
    (by omega) hs
  have hd := dualDStarMap_homogeneousSupport
    (realBoundary (starMapInverse q)) (d - k - 1) hb
  have hdeg : d - (d - k - 1) = k + 1 := by omega
  rw [hdeg] at hd
  simpa [dualExteriorDifference] using hd

noncomputable def dualDD₀ {d : ℕ} {B : Box d} :
    EuclideanSpace ℝ (DualDForm B (d - 3)) →ₗ[ℝ]
      EuclideanSpace ℝ (DualDForm B (d - 2)) :=
  finsuppToEuclidean.comp
    ((dualDCompressSubtype (dualDFormEmbedding (d - 2))).comp
      (dualExteriorDifference.comp (dualDFormToChain (d - 3))))

noncomputable def dualDD₁ {d : ℕ} {B : Box d} :
    EuclideanSpace ℝ (DualDForm B (d - 2)) →ₗ[ℝ]
      EuclideanSpace ℝ (DualDForm B (d - 1)) :=
  finsuppToEuclidean.comp
    ((dualDCompressSubtype (dualDFormEmbedding (d - 1))).comp
      (dualExteriorDifference.comp (dualDFormToChain (d - 2))))

theorem dualDD₀_output_homogeneous {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (u : EuclideanSpace ℝ (DualDForm B (d - 3))) :
    dualRealHomogeneousSupport
      (dualExteriorDifference (dualDFormToChain (d - 3) u)) (d - 2) := by
  have hk : d - 3 < d := by omega
  have h := dualDExteriorDifference_homogeneousSupport
    (dualDFormToChain (d - 3) u) (d - 3) hk
    (dualDEmbedSubtype_homogeneous (dualDFormEmbedding (d - 3)) (d - 3)
      (by intro a; exact a.2) (euclideanToFinsupp u))
  have heq : d - 3 + 1 = d - 2 := by omega
  rw [heq] at h
  exact h

theorem dualDD₀_embed_eq_derivative {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (u : EuclideanSpace ℝ (DualDForm B (d - 3))) :
    dualDFormToChain (d - 2) (dualDD₀ u) =
      dualExteriorDifference (dualDFormToChain (d - 3) u) := by
  simp only [dualDFormToChain, dualDD₀, LinearMap.comp_apply,
    euclideanToFinsupp_finsuppToEuclidean]
  apply dualDEmbedCompress_eq_self_of_support (dualDFormEmbedding (d - 2))
  intro c hc
  have hdeg : dualCellDegree c = d - 2 :=
    dualDD₀_output_homogeneous hd u c hc
  exact ⟨⟨c, hdeg⟩, rfl⟩

theorem dualDD₁_output_homogeneous {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (u : EuclideanSpace ℝ (DualDForm B (d - 2))) :
    dualRealHomogeneousSupport
      (dualExteriorDifference (dualDFormToChain (d - 2) u)) (d - 1) := by
  have hk : d - 2 < d := by omega
  have h := dualDExteriorDifference_homogeneousSupport
    (dualDFormToChain (d - 2) u) (d - 2) hk
    (dualDEmbedSubtype_homogeneous (dualDFormEmbedding (d - 2)) (d - 2)
      (by intro a; exact a.2) (euclideanToFinsupp u))
  have heq : d - 2 + 1 = d - 1 := by omega
  rw [heq] at h
  exact h

theorem dualDD₁_embed_eq_derivative {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (u : EuclideanSpace ℝ (DualDForm B (d - 2))) :
    dualDFormToChain (d - 1) (dualDD₁ u) =
      dualExteriorDifference (dualDFormToChain (d - 2) u) := by
  simp only [dualDFormToChain, dualDD₁, LinearMap.comp_apply,
    euclideanToFinsupp_finsuppToEuclidean]
  apply dualDEmbedCompress_eq_self_of_support (dualDFormEmbedding (d - 1))
  intro c hc
  have hdeg : dualCellDegree c = d - 1 :=
    dualDD₁_output_homogeneous hd u c hc
  exact ⟨⟨c, hdeg⟩, rfl⟩

theorem dualDFormToChain_injective {d : ℕ} {B : Box d} (k : ℕ) :
    Function.Injective (dualDFormToChain (B := B) k) := by
  intro x y h
  ext a
  have hv := congrArg (fun q : DualRealChain d B =>
    q (dualDFormEmbedding k a)) h
  simpa [dualDFormToChain, LinearMap.comp_apply, euclideanToFinsupp_apply] using hv

private theorem dualDRealBoundary_square_zero {d : ℕ} {B : Box d} :
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

private theorem dualDExteriorDifference_square_zero {d : ℕ} {B : Box d} :
    (dualExteriorDifference (d := d) (B := B)).comp
      (dualExteriorDifference (d := d) (B := B)) = 0 := by
  apply LinearMap.ext
  intro q
  change starMap (realBoundary (starMapInverse
      (starMap (realBoundary (starMapInverse q))))) = 0
  rw [starMapInverse_starMap]
  have h := congrArg (fun T : RealChain d B →ₗ[ℝ] RealChain d B =>
    T (starMapInverse q)) dualDRealBoundary_square_zero
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [h]
  simp

theorem dualDD₁_comp_D₀_zero {d : ℕ} (hd : 3 ≤ d) {B : Box d} :
    (dualDD₁ (B := B)).comp (dualDD₀ (B := B)) = 0 := by
  apply LinearMap.ext
  intro u
  apply dualDFormToChain_injective (d - 1)
  calc
    dualDFormToChain (d - 1) (dualDD₁ (dualDD₀ u)) =
        dualExteriorDifference (dualDFormToChain (d - 2) (dualDD₀ u)) :=
      dualDD₁_embed_eq_derivative hd (dualDD₀ u)
    _ = dualExteriorDifference
        (dualExteriorDifference (dualDFormToChain (d - 3) u)) := by
      rw [dualDD₀_embed_eq_derivative hd u]
    _ = dualDFormToChain (d - 1) 0 := by
      have h := congrArg (fun T : DualRealChain d B →ₗ[ℝ]
          DualRealChain d B => T (dualDFormToChain (d - 3) u))
        dualDExteriorDifference_square_zero
      simpa [LinearMap.comp_apply, dualDFormToChain] using h

theorem dualDD₀_exactOne {d : ℕ} (hd : 3 ≤ d) {B : Box d}
    (u : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (hu : dualDD₁ u = 0) :
    u ∈ (dualDD₀ (B := B)).range := by
  let q : DualRealChain d B := dualDFormToChain (d - 2) u
  have hclosed : dualExteriorDifference q = 0 := by
    calc
      dualExteriorDifference q = dualDFormToChain (d - 1) (dualDD₁ u) :=
        (dualDD₁_embed_eq_derivative hd u).symm
      _ = 0 := by rw [hu]; simp [dualDFormToChain]
  have hqdegree : dualRealHomogeneousSupport q (d - 2) :=
    dualDEmbedSubtype_homogeneous (dualDFormEmbedding (d - 2)) (d - 2)
      (by intro a; exact a.2) (euclideanToFinsupp u)
  let p : RealChain d B := starMapInverse q
  have hpdegree : realHomogeneousSupport p 2 := by
    have h := dualDStarMapInverse_homogeneousSupport q (d - 2) hqdegree
    have hdeg : d - (d - 2) = 2 := by omega
    rw [hdeg] at h
    exact h
  have hstar : starMap p = q := by
    simpa [p] using starMap_starMapInverse q
  have hpcycle : realBoundary p = 0 := by
    have h := primalDualStar_boundary_identity p
    rw [hstar, hclosed] at h
    simpa using h.symm
  let anchor : Anchor d B := fun i => ⟨0, Nat.zero_lt_succ _⟩
  obtain ⟨hfill, hdegree⟩ :=
    real_positiveDegree_filling anchor p 2 (by omega) hpdegree hpcycle
  let η : RealChain d B := realFillingOperator anchor p
  have hηdegree : realHomogeneousSupport η 3 := by
    simpa [η] using hdegree
  have hηboundary : realBoundary η = p := by
    simpa [η] using hfill
  have hηdualdegree : dualRealHomogeneousSupport (starMap η) (d - 3) := by
    exact dualDStarMap_homogeneousSupport η 3 hηdegree
  have hηsupport : ((starMap η).support : Set (DualCell d B)) ⊆
      Set.range (dualDFormEmbedding (B := B) (d - 3)) := by
    intro c hc
    have hdeg := hηdualdegree c hc
    exact ⟨⟨c, hdeg⟩, rfl⟩
  let v : EuclideanSpace ℝ (DualDForm B (d - 3)) :=
    finsuppToEuclidean
      (dualDCompressSubtype (dualDFormEmbedding (B := B) (d - 3)) (starMap η))
  have hη : dualDFormToChain (d - 3) v = starMap η := by
    dsimp [dualDFormToChain, v]
    rw [euclideanToFinsupp_finsuppToEuclidean]
    exact dualDEmbedCompress_eq_self_of_support
      (dualDFormEmbedding (B := B) (d - 3)) (starMap η) hηsupport
  have hfill' : dualDFormToChain (d - 2) (dualDD₀ v) = q := by
    calc
      dualDFormToChain (d - 2) (dualDD₀ v) =
          dualExteriorDifference (dualDFormToChain (d - 3) v) :=
        dualDD₀_embed_eq_derivative hd v
      _ = dualExteriorDifference (starMap η) := by rw [hη]
      _ = starMap (realBoundary η) := primalDualStar_incidence_identity η
      _ = q := by rw [hηboundary, hstar]
  apply LinearMap.mem_range.mpr
  refine ⟨v, ?_⟩
  exact dualDFormToChain_injective (d - 2) hfill'

/-- The grounded dual exact-one complex in form degree `d - 2`. -/
noncomputable def dualDExactOneComplex {d : ℕ}
    (hd : 3 ≤ d) (B : Box d) :
    ExactOneComplex (DualDForm B (d - 3)) (DualDForm B (d - 2))
      (DualDForm B (d - 1)) where
  d₀ := dualDD₀
  d₁ := dualDD₁
  complex := dualDD₁_comp_D₀_zero hd
  exactOne := by
    intro u hu
    exact dualDD₀_exactOne hd u (LinearMap.mem_ker.mp hu)

end
end FroehlichSpencer.FS82.XY

end
