/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.DualStokes
public import FroehlichSpencer.FS82.Gaussian.FiniteHodge
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Source dual complex and finite Hodge inverse

The adapted finite dual complex is exact at degree one by the repository's
real cubical filling theorem.

The full-lattice halo operator is deliberately
not identified here: the `D₁†D₁ = Π_{Λ*} δd` identity belongs in
`FroehlichSpencer.FS82.Gaussian.SourceOperatorBridge.lean`, after .
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open scoped InnerProductSpace
open FroehlichSpencer.FS82.Cubical
abbrev SourceBox := Cubical.Box 4

private theorem g2d_homogeneousSupport_smul {d : ℕ} {B : Box d} (z : ℤ)
    {q : Chain d B} {k : ℕ} (hq : homogeneousSupport q k) :
    homogeneousSupport (z • q) k := by
  intro c hc
  apply hq
  rw [Finsupp.mem_support_iff] at hc ⊢
  intro hz
  apply hc
  simp [hz]

private theorem g2d_homogeneousSupport_basis {d : ℕ} {B : Box d}
    (c : Cell d B) : homogeneousSupport (basisChain c) (cellDegree c) := by
  intro x hx
  by_cases h : x = c
  · subst x
    rfl
  · simp [basisChain, h] at hx

private theorem g2d_homogeneousSupport_add {d : ℕ} {B : Box d}
    {q r : Chain d B} {k : ℕ}
    (hq : homogeneousSupport q k) (hr : homogeneousSupport r k) :
    homogeneousSupport (q + r) k := by
  intro c hc
  have hc' : c ∈ q.support ∪ r.support := Finsupp.support_add hc
  rcases Finset.mem_union.mp hc' with hq' | hr'
  · exact hq c hq'
  · exact hr c hr'

private theorem g2d_homogeneousSupport_finite_sum {d : ℕ} {B : Box d}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Chain d B) (k : ℕ)
    (hf : ∀ i ∈ s, homogeneousSupport (f i) k) :
    homogeneousSupport (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [homogeneousSupport]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply g2d_homogeneousSupport_add
      · exact hf i (Finset.mem_insert_self i s)
      · apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)

private theorem g2d_boundaryBasis_homogeneousSupport {d : ℕ} {B : Box d}
    (c : Cell d B) (hpos : 0 < cellDegree c) :
    homogeneousSupport (boundaryBasis c) (cellDegree c - 1) := by
  classical
  rw [boundaryBasis]
  apply g2d_homogeneousSupport_finite_sum
  intro i hi
  cases hci : c i with
  | inl v => simp [homogeneousSupport]
  | inr e =>
    have hmem : i ∈ cellAxes c := by
      simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
      change Sum.isRight (c i) = true
      rw [hci]
      rfl
    have hcard : ((cellAxes c).erase i).card + 1 = cellDegree c := by
      simpa [cellDegree] using Finset.card_erase_add_one hmem
    have hu : cellDegree (upperFace c i e) = cellDegree c - 1 := by
      rw [cellDegree, cellAxes_upperFace]
      omega
    have hl : cellDegree (lowerFace c i e) = cellDegree c - 1 := by
      rw [cellDegree, cellAxes_lowerFace]
      omega
    apply g2d_homogeneousSupport_smul
    intro x hx
    have hx' := Finsupp.support_sub hx
    rcases Finset.mem_union.mp hx' with hx' | hx'
    · have hb := g2d_homogeneousSupport_basis (upperFace c i e) x hx'
      rw [hu] at hb
      exact hb
    · have hb := g2d_homogeneousSupport_basis (lowerFace c i e) x hx'
      rw [hl] at hb
      exact hb

private theorem g2d_homogeneousSupport_linearCombination_lower
    {α ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] (outDegree : ι → ℕ) (inDegree : α → ℕ)
    (f : α → ι →₀ M) (q : α →₀ R) (k : ℕ)
    (hq : ∀ a ∈ q.support, inDegree a = k)
    (hf : ∀ a ∈ q.support, ∀ x, x ∈ (f a).support →
      outDegree x + 1 = inDegree a) :
    ∀ x ∈ (Finsupp.linearCombination R f q).support, outDegree x = k - 1 := by
  rw [Finsupp.linearCombination_apply]
  intro x hx
  have hsum := Finsupp.support_sum hx
  rcases Finset.mem_biUnion.mp hsum with ⟨a, ha, hx⟩
  have hx' : x ∈ (f a).support := by
    rw [Finsupp.mem_support_iff] at hx ⊢
    intro hz
    apply hx
    simp [hz]
  have hdeg := hf a ha x hx'
  rw [hq a ha] at hdeg
  omega

theorem realBoundary_homogeneousSupport {d : ℕ} {B : Box d}
    (q : RealChain d B) (k : ℕ) (hk : 0 < k)
    (hq : realHomogeneousSupport q k) :
    realHomogeneousSupport (realBoundary q) (k - 1) := by
  change ∀ c ∈ (Finsupp.linearCombination ℝ
    (fun c => castIntegerChain (boundary (basisChain c))) q).support,
      cellDegree c = k - 1
  refine g2d_homogeneousSupport_linearCombination_lower cellDegree cellDegree
    (fun c => castIntegerChain (boundary (basisChain c))) q k hq ?_
  intro c hc x hx
  have hcdegree := hq c hc
  have hcpos : 0 < cellDegree c := by rw [hcdegree]; exact hk
  have hboundaryBasis : boundary (basisChain c) = boundaryBasis c := by
    have hAxis (i : Fin d) : axisBoundary i (basisChain c) = axisBoundaryBasis c i := by
      simp [axisBoundary, basisChain, Finsupp.linearCombination_single]
    calc
      boundary (basisChain c) = ∑ i : Fin d, axisBoundary i (basisChain c) := by
        simp [boundary]
      _ = ∑ i : Fin d, axisBoundaryBasis c i := by simp_rw [hAxis]
      _ = boundaryBasis c := rfl
  have hbase : homogeneousSupport (boundary (basisChain c))
      (cellDegree c - 1) := by
    rw [hboundaryBasis]
    exact g2d_boundaryBasis_homogeneousSupport c hcpos
  have hcast : realHomogeneousSupport
      (castIntegerChain (boundary (basisChain c))) (cellDegree c - 1) := by
    intro x hx
    exact hbase x (Finsupp.support_mapRange hx)
  have hx' : x ∈ (castIntegerChain (boundary (basisChain c))).support := by
    simpa using hx
  have hxdegree := hcast x hx'
  rw [hcdegree] at hxdegree
  omega

@[expose] def dualRealHomogeneousSupport {d : ℕ} {B : Box d}
    (q : DualRealChain d B) (k : ℕ) : Prop :=
  ∀ c ∈ q.support, dualCellDegree c = k

theorem starMap_homogeneousSupport {B : Box 4} (q : RealChain 4 B)
    (k : ℕ) (hq : realHomogeneousSupport q k) :
    dualRealHomogeneousSupport (starMap q) (4 - k) := by
  intro c hc
  have hmem : primalDualCellEquiv.symm c ∈ q.support := by
    simpa [starMap, Finsupp.equivMapDomain_apply] using hc
  have h := star_complementary_degree (primalDualCellEquiv.symm c)
  rw [Equiv.apply_symm_apply] at h
  rw [hq _ hmem] at h
  omega

theorem starMapInverse_homogeneousSupport {B : Box 4}
    (q : DualRealChain 4 B) (k : ℕ) (hq : dualRealHomogeneousSupport q k) :
    realHomogeneousSupport (starMapInverse q) (4 - k) := by
  intro c hc
  have hmem : primalDualCellEquiv c ∈ q.support := by
    simpa [starMapInverse, Finsupp.equivMapDomain_apply] using hc
  have h := star_complementary_degree c
  rw [hq _ hmem] at h
  omega


@[expose] noncomputable def euclideanToFinsupp {α : Type*} [Fintype α] [DecidableEq α] :
    EuclideanSpace ℝ α →ₗ[ℝ] (α →₀ ℝ) where
  toFun x := (Finsupp.linearEquivFunOnFinite ℝ ℝ α).symm x.ofLp
  map_add' x y := by
    apply (Finsupp.linearEquivFunOnFinite ℝ ℝ α).injective
    simp only [map_add, LinearEquiv.apply_symm_apply, WithLp.ofLp_add]
  map_smul' a x := by
    apply (Finsupp.linearEquivFunOnFinite ℝ ℝ α).injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, WithLp.ofLp_smul,
      RingHom.id_apply]

@[simp] theorem euclideanToFinsupp_apply {α : Type*} [Fintype α] [DecidableEq α]
    (x : EuclideanSpace ℝ α) (a : α) : euclideanToFinsupp x a = x a := by
  simp [euclideanToFinsupp]

@[expose] noncomputable def finsuppToEuclidean {α : Type*} [Fintype α] [DecidableEq α] :
    (α →₀ ℝ) →ₗ[ℝ] EuclideanSpace ℝ α where
  toFun q := WithLp.toLp 2 (Finsupp.linearEquivFunOnFinite ℝ ℝ α q)
  map_add' q r := by
    ext a
    simp only [WithLp.ofLp_add, Pi.add_apply]
    simp [Finsupp.linearEquivFunOnFinite]
  map_smul' c q := by
    ext a
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp [Finsupp.linearEquivFunOnFinite]

@[simp] theorem finsuppToEuclidean_apply {α : Type*} [Fintype α] [DecidableEq α]
    (q : α →₀ ℝ) (a : α) : finsuppToEuclidean q a = q a := by
  change (Finsupp.linearEquivFunOnFinite ℝ ℝ α q) a = q a
  rfl

@[expose] noncomputable def embedDualSubtype {B : SourceBox} {α : Type*} [Fintype α]
    [DecidableEq α] (f : α ↪ Cubical.DualCell 4 B) :
    (α →₀ ℝ) →ₗ[ℝ] Cubical.DualRealChain 4 B :=
  Finsupp.linearCombination ℝ (fun a => Finsupp.single (f a) 1)

@[simp] theorem embedDualSubtype_apply_single {B : SourceBox} {α : Type*}
    [Fintype α] [DecidableEq α] (f : α ↪ Cubical.DualCell 4 B)
    (a : α) (r : ℝ) :
    embedDualSubtype f (Finsupp.single a r) = Finsupp.single (f a) r := by
  simp [embedDualSubtype, Finsupp.linearCombination_single]

noncomputable def compressDualSubtype {B : SourceBox} {α : Type*} [Fintype α]
    [DecidableEq α] (f : α ↪ Cubical.DualCell 4 B) :
    Cubical.DualRealChain 4 B →ₗ[ℝ] (α →₀ ℝ) where
  toFun q := Finsupp.comapDomain f q f.injective.injOn
  map_add' q r := Finsupp.comapDomain_add_of_injective f.injective q r
  map_smul' a q := by
    ext x
    simp [Finsupp.comapDomain_apply]

@[simp] theorem compressDualSubtype_apply {B : SourceBox} {α : Type*}
    [Fintype α] [DecidableEq α] (f : α ↪ Cubical.DualCell 4 B)
    (q : Cubical.DualRealChain 4 B) (a : α) :
    compressDualSubtype f q a = q (f a) := by
  simp [compressDualSubtype, Finsupp.comapDomain_apply]

abbrev SourceDualZeroCells (B : SourceBox) :=
  {c : Cubical.DualCell 4 B // Cubical.dualCellDegree c = 0}

abbrev SourceDualOneCells (B : SourceBox) := Cubical.LambdaStarLinks B
abbrev SourceDualTwoCells (B : SourceBox) :=
  {c : Cubical.DualCell 4 B // Cubical.dualCellDegree c = 2}

noncomputable instance sourceDualZeroFintype {B : SourceBox} :
    Fintype (SourceDualZeroCells B) := Fintype.ofFinite _

instance sourceDualZeroDecidableEq {B : SourceBox} :
    DecidableEq (SourceDualZeroCells B) := inferInstance

noncomputable instance sourceDualOneFintype {B : SourceBox} :
    Fintype (SourceDualOneCells B) := Fintype.ofFinite _

instance sourceDualOneDecidableEq {B : SourceBox} :
    DecidableEq (SourceDualOneCells B) := inferInstance

noncomputable instance sourceDualTwoFintype {B : SourceBox} :
    Fintype (SourceDualTwoCells B) := Fintype.ofFinite _

instance sourceDualTwoDecidableEq {B : SourceBox} :
    DecidableEq (SourceDualTwoCells B) := inferInstance

@[expose] def sourceDualZeroEmbedding {B : SourceBox} :
    SourceDualZeroCells B ↪ Cubical.DualCell 4 B := Function.Embedding.subtype _

@[expose] def sourceDualOneEmbedding {B : SourceBox} :
    SourceDualOneCells B ↪ Cubical.DualCell 4 B := Function.Embedding.subtype _

@[expose] def sourceDualTwoEmbedding {B : SourceBox} :
    SourceDualTwoCells B ↪ Cubical.DualCell 4 B := Function.Embedding.subtype _

theorem embedDualSubtype_eq_embDomain {B : SourceBox} {α : Type*} [Fintype α]
    [DecidableEq α] (f : α ↪ Cubical.DualCell 4 B) (q : α →₀ ℝ) :
    embedDualSubtype f q = Finsupp.embDomain f q := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [embedDualSubtype]
  | add q₁ q₂ h₁ h₂ =>
      rw [map_add]
      have hE : Finsupp.embDomain f (q₁ + q₂) =
          Finsupp.embDomain f q₁ + Finsupp.embDomain f q₂ := by
        ext c
        simp [Finsupp.embDomain_apply]
      rw [hE, h₁, h₂]
  | single a r =>
      simp [embedDualSubtype, Finsupp.linearCombination_single,
        Finsupp.embDomain_single]

@[simp] theorem embedDualSubtype_apply_at_image {B : SourceBox} {α : Type*}
    [Fintype α] [DecidableEq α] (f : α ↪ Cubical.DualCell 4 B)
    (q : α →₀ ℝ) (a : α) : embedDualSubtype f q (f a) = q a := by
  rw [embedDualSubtype_eq_embDomain]
  simp [Finsupp.embDomain_apply]

theorem embed_compress_eq_self_of_support {B : SourceBox} {α : Type*}
    [Fintype α] [DecidableEq α] (f : α ↪ Cubical.DualCell 4 B)
    (q : Cubical.DualRealChain 4 B)
    (hq : (q.support : Set (Cubical.DualCell 4 B)) ⊆ Set.range f) :
    embedDualSubtype f (compressDualSubtype f q) = q := by
  rw [embedDualSubtype_eq_embDomain]
  exact Finsupp.embDomain_comapDomain hq

theorem embedDualSubtype_homogeneous {B : SourceBox} {α : Type*}
    [Fintype α] [DecidableEq α] (f : α ↪ Cubical.DualCell 4 B)
    (degree : ℕ) (hf : ∀ a, Cubical.dualCellDegree (f a) = degree)
    (q : α →₀ ℝ) :
    dualRealHomogeneousSupport (embedDualSubtype f q) degree := by
  rw [embedDualSubtype_eq_embDomain]
  intro c hc
  rw [Finsupp.support_embDomain] at hc
  rcases Finset.mem_map.mp hc with ⟨a, ha, rfl⟩
  exact hf a

@[simp] theorem euclideanToFinsupp_finsuppToEuclidean {α : Type*}
    [Fintype α] [DecidableEq α] (q : α →₀ ℝ) :
    euclideanToFinsupp (finsuppToEuclidean q) = q := by
  ext a
  simp

@[simp] theorem finsuppToEuclidean_euclideanToFinsupp {α : Type*}
    [Fintype α] [DecidableEq α] (x : EuclideanSpace ℝ α) :
    finsuppToEuclidean (euclideanToFinsupp x) = x := by
  ext a
  simp

@[expose] noncomputable def sourceDualZeroToChain {B : SourceBox} :
    EuclideanSpace ℝ (SourceDualZeroCells B) →ₗ[ℝ] Cubical.DualRealChain 4 B :=
  (embedDualSubtype sourceDualZeroEmbedding).comp euclideanToFinsupp

@[expose] noncomputable def sourceDualOneToChain {B : SourceBox} :
    EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ] Cubical.DualRealChain 4 B :=
  (embedDualSubtype sourceDualOneEmbedding).comp euclideanToFinsupp

@[expose] noncomputable def sourceDualTwoToChain {B : SourceBox} :
    EuclideanSpace ℝ (SourceDualTwoCells B) →ₗ[ℝ] Cubical.DualRealChain 4 B :=
  (embedDualSubtype sourceDualTwoEmbedding).comp euclideanToFinsupp

@[expose] noncomputable def sourceDualD₀ {B : SourceBox} :
    EuclideanSpace ℝ (SourceDualZeroCells B) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualOneCells B) :=
  (finsuppToEuclidean).comp
    ((compressDualSubtype sourceDualOneEmbedding).comp
      (Cubical.dualExteriorDifference.comp sourceDualZeroToChain))

@[expose] noncomputable def sourceDualD₁ {B : SourceBox} :
    EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualTwoCells B) :=
  (finsuppToEuclidean).comp
    ((compressDualSubtype sourceDualTwoEmbedding).comp
      (Cubical.dualExteriorDifference.comp sourceDualOneToChain))

theorem dualExteriorDifference_homogeneousSupport {B : SourceBox}
    (q : Cubical.DualRealChain 4 B) (k : ℕ) (hk : k < 4)
    (hq : dualRealHomogeneousSupport q k) :
    dualRealHomogeneousSupport
      (Cubical.dualExteriorDifference q) (k + 1) := by
  have hs := starMapInverse_homogeneousSupport q k hq
  have hb := realBoundary_homogeneousSupport
    (Cubical.starMapInverse q) (4 - k) (by omega) hs
  have hd := starMap_homogeneousSupport
    (Cubical.realBoundary (Cubical.starMapInverse q)) (4 - k - 1) hb
  have hdeg : 4 - (4 - k - 1) = k + 1 := by omega
  rw [hdeg] at hd
  simpa [Cubical.dualExteriorDifference] using hd

theorem sourceDualD₀_output_homogeneous {B : SourceBox}
    (u : EuclideanSpace ℝ (SourceDualZeroCells B)) :
    dualRealHomogeneousSupport
      (Cubical.dualExteriorDifference (sourceDualZeroToChain u)) 1 := by
  exact dualExteriorDifference_homogeneousSupport _ 0 (by omega)
    (embedDualSubtype_homogeneous sourceDualZeroEmbedding 0
      (by intro a; exact a.2) (euclideanToFinsupp u))

theorem sourceDualD₀_embed_eq_derivative {B : SourceBox}
    (u : EuclideanSpace ℝ (SourceDualZeroCells B)) :
    sourceDualOneToChain (sourceDualD₀ u) =
      Cubical.dualExteriorDifference (sourceDualZeroToChain u) := by
  simp only [sourceDualOneToChain, sourceDualD₀, LinearMap.comp_apply,
    euclideanToFinsupp_finsuppToEuclidean]
  apply embed_compress_eq_self_of_support sourceDualOneEmbedding
  intro c hc
  have hdeg : Cubical.dualCellDegree c = 1 :=
    sourceDualD₀_output_homogeneous u c hc
  exact ⟨⟨c, hdeg⟩, rfl⟩

theorem realBoundary_square_zero {B : SourceBox} :
    (Cubical.realBoundary (d := 4) (B := B)).comp
      (Cubical.realBoundary (d := 4) (B := B)) = 0 := by
  change Cubical.realifyLinearMap (Cubical.boundary (d := 4) (B := B)) *
      Cubical.realifyLinearMap (Cubical.boundary (d := 4) (B := B)) = 0
  rw [← Cubical.realifyLinearMap_mul, Cubical.boundary_square_zero]
  apply LinearMap.ext
  intro q
  ext c
  change (Finsupp.linearCombination ℝ (fun x : Cubical.Cell 4 B =>
    Cubical.castIntegerChain
      ((0 : Cubical.Chain 4 B →ₗ[ℤ] Cubical.Chain 4 B)
        (Cubical.basisChain x))) q) c = 0
  have hfun : (fun x : Cubical.Cell 4 B => Cubical.castIntegerChain
      ((0 : Cubical.Chain 4 B →ₗ[ℤ] Cubical.Chain 4 B)
        (Cubical.basisChain x))) = 0 := by
    funext x
    simp [Cubical.castIntegerChain]
  rw [hfun, Finsupp.linearCombination_zero]
  simp

theorem dualExteriorDifference_square_zero {B : SourceBox} :
    (Cubical.dualExteriorDifference (d := 4) (B := B)).comp
      (Cubical.dualExteriorDifference (d := 4) (B := B)) = 0 := by
  apply LinearMap.ext
  intro q
  change Cubical.starMap (Cubical.realBoundary
      (Cubical.starMapInverse (Cubical.starMap (Cubical.realBoundary
        (Cubical.starMapInverse q))))) = 0
  rw [Cubical.starMapInverse_starMap]
  have h := congrArg (fun T : Cubical.RealChain 4 B →ₗ[ℝ]
      Cubical.RealChain 4 B => T (Cubical.starMapInverse q))
      realBoundary_square_zero
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [h]
  simp

theorem sourceDualD₁_output_homogeneous {B : SourceBox}
    (u : EuclideanSpace ℝ (SourceDualOneCells B)) :
    dualRealHomogeneousSupport
      (Cubical.dualExteriorDifference (sourceDualOneToChain u)) 2 := by
  exact dualExteriorDifference_homogeneousSupport _ 1 (by omega)
    (embedDualSubtype_homogeneous sourceDualOneEmbedding 1
      (by intro a; exact a.2) (euclideanToFinsupp u))

theorem sourceDualD₁_embed_eq_derivative {B : SourceBox}
    (u : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sourceDualTwoToChain (sourceDualD₁ u) =
      Cubical.dualExteriorDifference (sourceDualOneToChain u) := by
  simp only [sourceDualTwoToChain, sourceDualD₁, LinearMap.comp_apply,
    euclideanToFinsupp_finsuppToEuclidean]
  apply embed_compress_eq_self_of_support sourceDualTwoEmbedding
  intro c hc
  have hdeg : Cubical.dualCellDegree c = 2 :=
    sourceDualD₁_output_homogeneous u c hc
  exact ⟨⟨c, hdeg⟩, rfl⟩

theorem sourceDualOneToChain_injective {B : SourceBox} :
    Function.Injective (@sourceDualOneToChain B) := by
  intro x y h
  ext a
  have hv := congrArg (fun q : Cubical.DualRealChain 4 B =>
    q (sourceDualOneEmbedding a)) h
  simpa [sourceDualOneToChain, LinearMap.comp_apply] using hv

theorem sourceDualTwoToChain_injective {B : SourceBox} :
    Function.Injective (@sourceDualTwoToChain B) := by
  intro x y h
  ext a
  have hv := congrArg (fun q : Cubical.DualRealChain 4 B =>
    q (sourceDualTwoEmbedding a)) h
  simpa [sourceDualTwoToChain, LinearMap.comp_apply] using hv

theorem sourceDualD₁_comp_D₀_zero {B : SourceBox} :
    (sourceDualD₁ (B := B)).comp (sourceDualD₀ (B := B)) = 0 := by
  apply LinearMap.ext
  intro u
  apply sourceDualTwoToChain_injective
  calc
    sourceDualTwoToChain (sourceDualD₁ (sourceDualD₀ u)) =
        Cubical.dualExteriorDifference
          (sourceDualOneToChain (sourceDualD₀ u)) :=
      sourceDualD₁_embed_eq_derivative (sourceDualD₀ u)
    _ = Cubical.dualExteriorDifference
        (Cubical.dualExteriorDifference (sourceDualZeroToChain u)) := by
      rw [sourceDualD₀_embed_eq_derivative]
    _ = sourceDualTwoToChain (0 : EuclideanSpace ℝ (SourceDualTwoCells B)) := by
      have h := congrArg (fun T : Cubical.DualRealChain 4 B →ₗ[ℝ]
        Cubical.DualRealChain 4 B => T (sourceDualZeroToChain u))
        (dualExteriorDifference_square_zero (B := B))
      simpa [LinearMap.comp_apply, sourceDualTwoToChain] using h

private theorem sourceRealThreeForm_dualExactness {B : SourceBox}
    (anchor : Cubical.Anchor 4 B) (q : Cubical.RealChain 4 B)
    (hq : Cubical.realHomogeneousSupport q 3)
    (hcycle : Cubical.realBoundary q = 0) :
    ∃ η : Cubical.DualRealChain 4 B,
      Cubical.dualExteriorDifference η = Cubical.starMap q ∧
        Cubical.realHomogeneousSupport (Cubical.starMapInverse η) 4 ∧
        Cubical.realBoundary (Cubical.starMapInverse η) = q := by
  obtain ⟨hfill, hdegree⟩ :=
    Cubical.real_positiveDegree_filling anchor q 3 (by omega) hq hcycle
  refine ⟨Cubical.starMap (Cubical.realFillingOperator anchor q), ?_, ?_, ?_⟩
  · rw [Cubical.primalDualStar_incidence_identity, hfill]
  · simpa [Cubical.starMapInverse_starMap] using hdegree
  · simpa [Cubical.starMapInverse_starMap] using hfill

theorem sourceDualD₀_exactOne {B : SourceBox}
    (u : EuclideanSpace ℝ (SourceDualOneCells B))
    (hu : sourceDualD₁ u = 0) :
    u ∈ (sourceDualD₀ (B := B)).range := by
  let q : Cubical.DualRealChain 4 B := sourceDualOneToChain u
  have hclosed : Cubical.dualExteriorDifference q = 0 := by
    calc
      Cubical.dualExteriorDifference q = sourceDualTwoToChain (sourceDualD₁ u) :=
        (sourceDualD₁_embed_eq_derivative u).symm
      _ = 0 := by rw [hu]; simp [sourceDualTwoToChain]
  have hqdegree : dualRealHomogeneousSupport q 1 := by
    exact embedDualSubtype_homogeneous sourceDualOneEmbedding 1
      (by intro a; exact a.2) (euclideanToFinsupp u)
  let p : Cubical.RealChain 4 B := Cubical.starMapInverse q
  have hpdegree : Cubical.realHomogeneousSupport p 3 := by
    exact starMapInverse_homogeneousSupport q 1 hqdegree
  have hstar : Cubical.starMap p = q := by
    simpa [p] using Cubical.starMap_starMapInverse q
  have hpcycle : Cubical.realBoundary p = 0 := by
    have h := Cubical.primalDualStar_boundary_identity p
    rw [hstar, hclosed] at h
    simpa using h.symm
  let anchor : Cubical.Anchor 4 B := fun i => ⟨0, Nat.zero_lt_succ _⟩
  obtain ⟨η, hηderivative, hηdegree, _⟩ :=
    sourceRealThreeForm_dualExactness anchor p hpdegree hpcycle
  have hηdualdegree : dualRealHomogeneousSupport η 0 := by
    have h := starMap_homogeneousSupport
      (Cubical.starMapInverse η) 4 hηdegree
    simpa [Cubical.starMap_starMapInverse] using h
  have hηsupport : (η.support : Set (Cubical.DualCell 4 B)) ⊆
      Set.range sourceDualZeroEmbedding := by
    intro c hc
    have hdeg := hηdualdegree c hc
    exact ⟨⟨c, hdeg⟩, rfl⟩
  let v : EuclideanSpace ℝ (SourceDualZeroCells B) :=
    finsuppToEuclidean (compressDualSubtype sourceDualZeroEmbedding η)
  have hη : sourceDualZeroToChain v = η := by
    change embedDualSubtype sourceDualZeroEmbedding
      (euclideanToFinsupp (finsuppToEuclidean
        (compressDualSubtype sourceDualZeroEmbedding η))) = η
    rw [euclideanToFinsupp_finsuppToEuclidean]
    exact embed_compress_eq_self_of_support sourceDualZeroEmbedding η hηsupport
  have hfill : sourceDualOneToChain (sourceDualD₀ v) = q := by
    calc
      sourceDualOneToChain (sourceDualD₀ v) =
          Cubical.dualExteriorDifference (sourceDualZeroToChain v) :=
        sourceDualD₀_embed_eq_derivative v
      _ = Cubical.dualExteriorDifference η := by rw [hη]
      _ = Cubical.starMap p := hηderivative
      _ = q := hstar
  apply LinearMap.mem_range.mpr
  refine ⟨v, ?_⟩
  exact sourceDualOneToChain_injective hfill

theorem sourceDualD₁_kernel_eq_sourceDualD₀_range {B : SourceBox} :
    (sourceDualD₁ (B := B)).ker = (sourceDualD₀ (B := B)).range := by
  apply le_antisymm
  · intro u hu
    exact sourceDualD₀_exactOne u (LinearMap.mem_ker.mp hu)
  · intro u hu
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hu
    apply LinearMap.mem_ker.mpr
    have h := congrArg (fun T : EuclideanSpace ℝ (SourceDualZeroCells B) →ₗ[ℝ]
        EuclideanSpace ℝ (SourceDualTwoCells B) => T v)
        (sourceDualD₁_comp_D₀_zero (B := B))
    simpa [LinearMap.comp_apply] using h

@[expose] noncomputable def sourceDualFiniteOperator {B : SourceBox} :
    EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualOneCells B) :=
  (sourceDualD₁ (B := B)).adjoint.comp (sourceDualD₁ (B := B))


@[expose] noncomputable def sourceDualComplex (B : SourceBox) :
    ExactOneComplex
      (SourceDualZeroCells B) (SourceDualOneCells B) (SourceDualTwoCells B) where
  d₀ := sourceDualD₀
  d₁ := sourceDualD₁
  complex := sourceDualD₁_comp_D₀_zero
  exactOne := by
    intro u hu
    exact sourceDualD₀_exactOne u hu


end FroehlichSpencer.FS82.Gaussian
end
