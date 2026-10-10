/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.Core
public import FroehlichSpencer.FS82.Cubical.Contraction
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-!
# Cubical incidence and rectangular support

Oriented finite cells, incidence, zero extension, coordinate paths, and support primitives for rectangular boxes.

Source: FS82 journal (2.9)–(2.16), Fröhlich–Spencer (1982) and Lemma 1, lines 312–328.
-/

public section

namespace FroehlichSpencer.FS82.Cubical

noncomputable section
open Classical

@[expose] def latticeIsEdge (x : LatticeCoord) : Prop := x.isRight

@[expose] def latticeRankBefore {d : ℕ} (c : LatticeCell d) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun j : Fin d => j < i ∧ latticeIsEdge (c j)).card

@[expose] def latticeBasis {d : ℕ} (c : LatticeCell d) : LatticeChain d := Finsupp.single c 1

@[expose] def latticeEdgeCell {d : ℕ} (c : LatticeCell d) (i : Fin d) (t : ℤ) : LatticeCell d :=
  Function.update c i (Sum.inr t)

@[expose] def latticeVertexCell {d : ℕ} (c : LatticeCell d) (i : Fin d) (t : ℤ) : LatticeCell d :=
  Function.update c i (Sum.inl t)

@[expose] def latticeUpperFace {d : ℕ} (c : LatticeCell d) (i : Fin d) (t : ℤ) : LatticeCell d :=
  Function.update c i (Sum.inl (t + 1))

@[expose] def latticeLowerFace {d : ℕ} (c : LatticeCell d) (i : Fin d) (t : ℤ) : LatticeCell d :=
  Function.update c i (Sum.inl t)

@[expose] def latticeBoundaryBasis {d : ℕ} (c : LatticeCell d) : LatticeChain d :=
  ∑ i : Fin d, match c i with
    | Sum.inl _ => 0
    | Sum.inr t =>
        ((-1 : ℤ) ^ latticeRankBefore c i) •
          (latticeBasis (latticeUpperFace c i t) - latticeBasis (latticeLowerFace c i t))

@[expose] def latticeCoboundaryBasis {d : ℕ} (c : LatticeCell d) : LatticeChain d :=
  ∑ i : Fin d, match c i with
    | Sum.inr _ => 0
    | Sum.inl t =>
        ((-1 : ℤ) ^ latticeRankBefore c i) •
          (latticeBasis (latticeEdgeCell c i (t - 1)) - latticeBasis (latticeEdgeCell c i t))

@[expose] def latticeBoundary {d : ℕ} : LatticeChain d →ₗ[ℤ] LatticeChain d :=
  Finsupp.linearCombination ℤ latticeBoundaryBasis

@[expose] def latticeCoboundary {d : ℕ} : LatticeChain d →ₗ[ℤ] LatticeChain d :=
  Finsupp.linearCombination ℤ latticeCoboundaryBasis

/-- The full-lattice `δ d` on finitely supported integer forms. -/
@[expose] def latticeDeltaD {d : ℕ} : LatticeChain d →ₗ[ℤ] LatticeChain d :=
  latticeBoundary ∘ₗ latticeCoboundary

@[simp] theorem latticeBoundary_basis {d : ℕ} (c : LatticeCell d) :
    latticeBoundary (latticeBasis c) = latticeBoundaryBasis c := by
  simp [latticeBoundary, latticeBasis, Finsupp.linearCombination_single]

@[simp] theorem latticeCoboundary_basis {d : ℕ} (c : LatticeCell d) :
    latticeCoboundary (latticeBasis c) = latticeCoboundaryBasis c := by
  simp [latticeCoboundary, latticeBasis, Finsupp.linearCombination_single]

/-- The same full-lattice incidence stencil acting on real-valued forms. -/
abbrev RealLatticeChain (d : ℕ) := LatticeCell d →₀ ℝ

@[expose] def castLatticeChain {d : ℕ} (q : LatticeChain d) : RealLatticeChain d :=
  Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp) q

@[expose] def realifyLatticeLinearMap {d : ℕ} (T : LatticeChain d →ₗ[ℤ] LatticeChain d) :
    RealLatticeChain d →ₗ[ℝ] RealLatticeChain d :=
  Finsupp.linearCombination ℝ
    (fun c : LatticeCell d => castLatticeChain (T (latticeBasis c)))

@[expose] def realLatticeDeltaD {d : ℕ} : RealLatticeChain d →ₗ[ℝ] RealLatticeChain d :=
  realifyLatticeLinearMap latticeDeltaD

@[expose] def coordIsEdge {d : ℕ} {B : Box d} {i : Fin d} (x : Coord B i) : Prop := x.isRight

@[expose] def coordBase {d : ℕ} {B : Box d} {i : Fin d} (x : Coord B i) : ℕ :=
  Sum.elim (fun v => v.val) (fun e => e.val) x

@[expose] def cellRankBefore {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun j : Fin d => j < i ∧ coordIsEdge (c j)).card

@[expose] def cellAxes {d : ℕ} {B : Box d} (c : Cell d B) : Finset (Fin d) :=
  Finset.univ.filter fun i => coordIsEdge (c i)

@[expose] def vertexUpdate {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (v : Fin (B i + 1)) : Cell d B :=
  Function.update c i (Sum.inl v)

theorem vertexUpdate_commute {d : ℕ} {B : Box d} (c : Cell d B)
    {i j : Fin d} (hij : i ≠ j) (vi : Fin (B i + 1)) (vj : Fin (B j + 1)) :
    vertexUpdate (vertexUpdate c i vi) j vj =
      vertexUpdate (vertexUpdate c j vj) i vi := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [vertexUpdate, Function.update_of_ne hij]
  · by_cases hkj : k = j
    · subst k
      simp [vertexUpdate, Function.update_of_ne (Ne.symm hij)]
    · simp [vertexUpdate, Function.update_of_ne hki, Function.update_of_ne hkj]

@[expose] def lowerFace {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d) (e : Fin (B i)) : Cell d B :=
  vertexUpdate c i ⟨e.val, Nat.lt_succ_of_le e.isLt.le⟩

@[expose] def upperFace {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d) (e : Fin (B i)) : Cell d B :=
  vertexUpdate c i ⟨e.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt e.isLt)⟩

@[simp] theorem lowerFace_apply_of_ne {d : ℕ} {B : Box d} (c : Cell d B)
    (i k : Fin d) (e : Fin (B i)) (hki : k ≠ i) :
    lowerFace c i e k = c k := by
  simp [lowerFace, vertexUpdate, Function.update_of_ne hki]

@[simp] theorem upperFace_apply_of_ne {d : ℕ} {B : Box d} (c : Cell d B)
    (i k : Fin d) (e : Fin (B i)) (hki : k ≠ i) :
    upperFace c i e k = c k := by
  simp [upperFace, vertexUpdate, Function.update_of_ne hki]

theorem lowerFace_upperFace_commute {d : ℕ} {B : Box d} (c : Cell d B)
    {i j : Fin d} (hij : i ≠ j) (ei : Fin (B i)) (ej : Fin (B j)) :
    upperFace (upperFace c i ei) j ej = upperFace (upperFace c j ej) i ei := by
  change vertexUpdate (vertexUpdate c i _) j _ =
    vertexUpdate (vertexUpdate c j _) i _
  funext k
  by_cases hki : k = i
  · subst k
    simp [vertexUpdate, Function.update_of_ne hij]
  · by_cases hkj : k = j
    · subst k
      simp [vertexUpdate, Function.update_of_ne (Ne.symm hij)]
    · simp [vertexUpdate, Function.update_of_ne hki, Function.update_of_ne hkj]

abbrev axisRank {d : ℕ} (I : Finset (Fin d)) (i : Fin d) : ℕ :=
  Contraction.axisRank I i

theorem cellRankBefore_eq_axisRank {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d) :
    cellRankBefore c i = axisRank (cellAxes c) i := by
  simp [cellRankBefore, cellAxes, axisRank, Contraction.axisRank,
    Finset.filter_filter, and_comm]

theorem cellAxes_lowerFace {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (e : Fin (B i)) : cellAxes (lowerFace c i e) = (cellAxes c).erase i := by
  classical
  apply Finset.ext
  intro j
  simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases hji : j = i
  · subst j
    simp [lowerFace, vertexUpdate, coordIsEdge, Function.update_self]
  · simp [lowerFace, vertexUpdate, coordIsEdge, hji]

theorem cellAxes_upperFace {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (e : Fin (B i)) : cellAxes (upperFace c i e) = (cellAxes c).erase i := by
  classical
  apply Finset.ext
  intro j
  simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases hji : j = i
  · subst j
    simp [upperFace, vertexUpdate, coordIsEdge, Function.update_self]
  · simp [upperFace, vertexUpdate, coordIsEdge, hji]

@[simp] theorem cellRankBefore_lowerFace_eq_axisRank {d : ℕ} {B : Box d}
    (c : Cell d B) (i k : Fin d) (e : Fin (B i)) :
    cellRankBefore (lowerFace c i e) k = axisRank ((cellAxes c).erase i) k := by
  rw [cellRankBefore_eq_axisRank, cellAxes_lowerFace]

@[simp] theorem cellRankBefore_upperFace_eq_axisRank {d : ℕ} {B : Box d}
    (c : Cell d B) (i k : Fin d) (e : Fin (B i)) :
    cellRankBefore (upperFace c i e) k = axisRank ((cellAxes c).erase i) k := by
  rw [cellRankBefore_eq_axisRank, cellAxes_upperFace]

theorem cellSignSwap {d : ℕ} {B : Box d} (c : Cell d B)
    {i j : Fin d} (hij : i < j) (hi : i ∈ cellAxes c) (hj : j ∈ cellAxes c)
    (ei : Fin (B i)) (ej : Fin (B j)) :
    (-1 : ℤ) ^ cellRankBefore c i *
        (-1 : ℤ) ^ cellRankBefore (lowerFace c i ei) j =
      - ((-1 : ℤ) ^ cellRankBefore c j *
        (-1 : ℤ) ^ cellRankBefore (lowerFace c j ej) i) := by
  have hs := Contraction.cubical_sign_swap (cellAxes c) i j hij hi hj
  rw [cellRankBefore_eq_axisRank, cellRankBefore_eq_axisRank,
    cellRankBefore_eq_axisRank, cellRankBefore_eq_axisRank,
    cellAxes_lowerFace, cellAxes_lowerFace]
  simpa [axisRank] using hs

@[expose] def basisChain {d : ℕ} {B : Box d} (c : Cell d B) : Chain d B := Finsupp.single c 1

@[expose] def edgeCell {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d) (t : Fin (B i)) : Cell d B :=
  Function.update c i (Sum.inr t)

theorem cellAxes_edgeCell_eq_insert {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (e : Fin (B i)) :
    cellAxes (edgeCell c i e) = insert i (cellAxes c) := by
  apply Finset.ext
  intro j
  simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  by_cases hji : j = i
  · subst j
    change coordIsEdge (Function.update c i (Sum.inr e) i) ↔ _
    simp [coordIsEdge]
  · change coordIsEdge (Function.update c i (Sum.inr e) j) ↔ _
    rw [Function.update_of_ne hji]
    simp [hji]

@[expose] def embedCoord {d : ℕ} {B : Box d} (origin : Fin d → ℤ) (i : Fin d) :
    Coord B i ↪ LatticeCoord where
  toFun := fun x => match x with
    | Sum.inl v => Sum.inl (origin i + v.val)
    | Sum.inr e => Sum.inr (origin i + e.val)
  inj' := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        simp only [Sum.inl.injEq] at h
        have hv : (x.val : ℤ) = y.val := Int.add_left_cancel h
        exact congrArg Sum.inl (Fin.ext (by exact_mod_cast hv))
      | inr y => cases h
    | inr x =>
      cases y with
      | inl y => cases h
      | inr y =>
        simp only [Sum.inr.injEq] at h
        have hv : (x.val : ℤ) = y.val := Int.add_left_cancel h
        exact congrArg Sum.inr (Fin.ext (by exact_mod_cast hv))

@[expose] def boxCellEmbedding {d : ℕ} {B : Box d} (origin : Fin d → ℤ) :
    Cell d B ↪ LatticeCell d where
  toFun c i := embedCoord origin i (c i)
  inj' := by
    intro c₁ c₂ h
    funext i
    exact (embedCoord origin i).injective (congrFun h i)

@[expose] def zeroExtension {d : ℕ} {B : Box d} (origin : Fin d → ℤ) :
    Chain d B →ₗ[ℤ] LatticeChain d :=
  Finsupp.linearCombination ℤ (fun c : Cell d B => Finsupp.single (boxCellEmbedding origin c) 1)

theorem zeroExtension_eq_embDomain {d : ℕ} {B : Box d} (origin : Fin d → ℤ)
    (q : Chain d B) :
    zeroExtension (B := B) origin q = Finsupp.embDomain (boxCellEmbedding origin) q := by
  induction q using Finsupp.induction_linear with
  | zero => simp [zeroExtension]
  | add q₁ q₂ h₁ h₂ =>
      rw [map_add]
      have hE : Finsupp.embDomain (boxCellEmbedding origin) (q₁ + q₂) =
          Finsupp.embDomain (boxCellEmbedding origin) q₁ +
            Finsupp.embDomain (boxCellEmbedding origin) q₂ := by
        ext x
        simp [Finsupp.embDomain_apply]
      rw [hE, h₁, h₂]
  | single c z => simp [zeroExtension, Finsupp.embDomain_single]

theorem zeroExtension_support {d : ℕ} {B : Box d} (origin : Fin d → ℤ)
    (q : Chain d B) :
    (zeroExtension (B := B) origin q).support = q.support.map (boxCellEmbedding origin) := by
  rw [zeroExtension_eq_embDomain]
  exact Finsupp.support_embDomain _ _

theorem zeroExtension_vanishes_outside {d : ℕ} {B : Box d} (origin : Fin d → ℤ)
    (q : Chain d B) (c : LatticeCell d)
    (hc : c ∉ Set.range (boxCellEmbedding (B := B) origin)) :
    zeroExtension (B := B) origin q c = 0 := by
  rw [zeroExtension_eq_embDomain]
  exact Finsupp.embDomain_of_notMem_range _ _ _ hc

@[expose] def boxCompression {d : ℕ} {B : Box d} (origin : Fin d → ℤ) :
    LatticeChain d →ₗ[ℤ] Chain d B where
  toFun q := Finsupp.comapDomain (boxCellEmbedding origin) q
    ((boxCellEmbedding origin).injective.injOn)
  map_add' q₁ q₂ := Finsupp.comapDomain_add_of_injective
    (boxCellEmbedding origin).injective q₁ q₂
  map_smul' a q := by ext c; simp

theorem compress_extend_eq_id {d : ℕ} {B : Box d} (origin : Fin d → ℤ) :
    boxCompression (B := B) origin ∘ₗ zeroExtension (B := B) origin = LinearMap.id := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp [zeroExtension, boxCompression]
  | add q₁ q₂ h₁ h₂ =>
      rw [map_add, h₁, h₂]
      simp only [LinearMap.id_apply]
  | single c z =>
      simp [zeroExtension, boxCompression, Finsupp.linearCombination_single]

/-- Finite zero-Dirichlet operator: compress the full-lattice operator after zero extension. -/
@[expose] def finiteZeroExteriorOperator {d : ℕ} {B : Box d} (origin : Fin d → ℤ)
    (A : LatticeChain d →ₗ[ℤ] LatticeChain d) : Chain d B →ₗ[ℤ] Chain d B :=
  boxCompression (B := B) origin ∘ₗ A ∘ₗ zeroExtension (B := B) origin

theorem finiteZeroExteriorOperator_eq_compression {d : ℕ} {B : Box d}
    (origin : Fin d → ℤ) (A : LatticeChain d →ₗ[ℤ] LatticeChain d) :
    finiteZeroExteriorOperator origin A =
      boxCompression (B := B) origin ∘ₗ A ∘ₗ zeroExtension (B := B) origin := rfl

@[expose] def sourceBoxDeltaD {d : ℕ} {B : Box d} (origin : Fin d → ℤ) :
    Chain d B →ₗ[ℤ] Chain d B :=
  finiteZeroExteriorOperator origin latticeDeltaD

theorem sourceBoxDeltaD_is_compressed_full_operator {d : ℕ} {B : Box d}
    (origin : Fin d → ℤ) :
    sourceBoxDeltaD origin =
      boxCompression (B := B) origin ∘ₗ latticeDeltaD ∘ₗ zeroExtension (B := B) origin := rfl

@[expose] def boundaryBasis {d : ℕ} {B : Box d} (c : Cell d B) : Chain d B :=
  ∑ i : Fin d, match c i with
  | Sum.inl _ => 0
  | Sum.inr e =>
      ((-1 : ℤ) ^ cellRankBefore c i) •
        (basisChain (upperFace c i e) - basisChain (lowerFace c i e))

@[expose] def axisBoundaryBasis {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d) : Chain d B :=
  match c i with
  | Sum.inl _ => 0
  | Sum.inr e =>
      ((-1 : ℤ) ^ cellRankBefore c i) •
        (basisChain (upperFace c i e) - basisChain (lowerFace c i e))

@[expose] def axisBoundary {d : ℕ} {B : Box d} (i : Fin d) : Chain d B →ₗ[ℤ] Chain d B :=
  Finsupp.linearCombination ℤ (axisBoundaryBasis · i)

@[expose] def boundary {d : ℕ} {B : Box d} : Chain d B →ₗ[ℤ] Chain d B :=
  ∑ i : Fin d, axisBoundary i

@[expose] def extendBasisMap {d : ℕ} {B : Box d} (f : Cell d B → Chain d B) :
    Chain d B →ₗ[ℤ] Chain d B := Finsupp.linearCombination ℤ f

@[expose] def coordEdge {d : ℕ} {B : Box d} (i : Fin d) (t : ℕ) (ht : t < B i) : Coord B i :=
  Sum.inr ⟨t, ht⟩

@[expose] def coordVertex {d : ℕ} {B : Box d} (i : Fin d) (t : ℕ) (ht : t ≤ B i) : Coord B i :=
  Sum.inl ⟨t, Nat.lt_succ_of_le ht⟩

@[expose] def pathEdges {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (l r : ℕ) (hr : r ≤ B i) : Chain d B :=
  ∑ t : {t : ℕ // t ∈ Finset.Ico l r},
    basisChain (edgeCell c i ⟨t.val, by
      have ht := Finset.mem_Ico.mp t.property
      exact lt_of_lt_of_le ht.2 hr
    ⟩)

theorem finsupp_finset_sum_apply {ι α : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → α →₀ ℤ) (x : α) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.add_apply, ih]

theorem pathEdges_coefficientwiseBound {d : ℕ} {B : Box d} (c : Cell d B)
    (i : Fin d) (l r : ℕ) (hr : r ≤ B i) :
    ∀ x, (pathEdges c i l r hr x).natAbs ≤ 1 := by
  classical
  intro x
  unfold pathEdges
  let I := {t : ℕ // t ∈ Finset.Ico l r}
  let edgeAt : I → Cell d B := fun t => edgeCell c i ⟨t.val, by
    have ht := Finset.mem_Ico.mp t.property
    exact lt_of_lt_of_le ht.2 hr
  ⟩
  have hEval : (∑ t : I, basisChain (edgeAt t)) x =
      ∑ t : I, basisChain (edgeAt t) x := by
    have h := finsupp_finset_sum_apply (Finset.univ : Finset I)
      (fun t => basisChain (edgeAt t)) x
    exact h
  change ((∑ t : I, basisChain (edgeAt t)) x).natAbs ≤ 1
  rw [hEval]
  simp only [basisChain, Finsupp.single_apply]
  have hedgeAt : Function.Injective edgeAt := by
    intro s t h
    apply Subtype.ext
    have hi := congrFun h i
    simpa [edgeAt, edgeCell] using hi
  by_cases hex : ∃ t : I, x = edgeAt t
  · obtain ⟨t, ht⟩ := hex
    have hsum : (∑ s : I, if edgeAt s = x then (1 : ℤ) else 0) = 1 := by
      rw [Finset.sum_eq_single t]
      · simp [ht]
      · intro s hs hst
        have hnot : edgeAt s ≠ x := by
          intro hxs
          apply hst
          exact hedgeAt (hxs.trans ht)
        simp [hnot]
      · simp [I]
    rw [hsum]
    simp
  · have hsum : (∑ s : I, if edgeAt s = x then (1 : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hnot : edgeAt s ≠ x := by
        intro h
        exact hex ⟨s, h.symm⟩
      simp [hnot]
    rw [hsum]
    simp

@[expose] def pathEdgeTerm {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d) (t : ℕ) :
    Chain d B :=
  if ht : t < B i then basisChain (edgeCell c i ⟨t, ht⟩) else 0

theorem pathEdges_eq_Ico {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (l r : ℕ) (hr : r ≤ B i) :
    pathEdges c i l r hr =
      ∑ t ∈ Finset.Ico l r, pathEdgeTerm c i t := by
  unfold pathEdges
  calc
    (∑ t : {t : ℕ // t ∈ Finset.Ico l r},
        basisChain (edgeCell c i ⟨t.val, by
          have ht := Finset.mem_Ico.mp t.property
          exact lt_of_lt_of_le ht.2 hr
        ⟩)) =
      ∑ t : {t : ℕ // t ∈ Finset.Ico l r}, pathEdgeTerm c i t.val := by
        apply Finset.sum_congr rfl
        intro t ht
        have hb : t.val < B i := by
          have htr := (Finset.mem_Ico.mp t.property).2
          omega
        simp [pathEdgeTerm, hb]
    _ = ∑ t ∈ Finset.Ico l r, pathEdgeTerm c i t := by
        symm
        exact Finset.sum_subtype (Finset.Ico l r) (fun _ => Iff.rfl) (pathEdgeTerm c i)

theorem upperFace_edgeCell_commute {d : ℕ} {B : Box d} (c : Cell d B)
    (i j : Fin d) (hij : i ≠ j) (t : Fin (B i)) (e : Fin (B j)) :
    upperFace (edgeCell c i t) j e = edgeCell (upperFace c j e) i t := by
  change Function.update (Function.update c i (Sum.inr t)) j
      (Sum.inl ⟨e.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt e.isLt)⟩) =
    Function.update (Function.update c j
      (Sum.inl ⟨e.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt e.isLt)⟩)) i
      (Sum.inr t)
  exact Function.update_comm hij _ _ _

theorem lowerFace_edgeCell_commute {d : ℕ} {B : Box d} (c : Cell d B)
    (i j : Fin d) (hij : i ≠ j) (t : Fin (B i)) (e : Fin (B j)) :
    lowerFace (edgeCell c i t) j e = edgeCell (lowerFace c j e) i t := by
  change Function.update (Function.update c i (Sum.inr t)) j
      (Sum.inl ⟨e.val, Nat.lt_succ_of_le e.isLt.le⟩) =
    Function.update (Function.update c j
      (Sum.inl ⟨e.val, Nat.lt_succ_of_le e.isLt.le⟩)) i (Sum.inr t)
  exact Function.update_comm hij _ _ _

theorem pathEdges_succ_top {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (l r : ℕ) (hlr : l ≤ r) (hr : r + 1 ≤ B i) :
    pathEdges c i l (r + 1) hr =
      pathEdges c i l r (by omega) + basisChain (edgeCell c i ⟨r, by omega⟩) := by
  rw [pathEdges_eq_Ico, pathEdges_eq_Ico, Finset.sum_Ico_succ_top hlr]
  have hrlt : r < B i := by omega
  simp [pathEdgeTerm, dite_eq_left hrlt]

theorem pathEdges_succ_left {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (l r : ℕ) (hlr : l < r) (hr : r ≤ B i) :
    pathEdges c i l r hr =
      basisChain (edgeCell c i ⟨l, by omega⟩) + pathEdges c i (l + 1) r hr := by
  rw [pathEdges_eq_Ico, pathEdges_eq_Ico]
  have hIco : Finset.Ico l r = insert l (Finset.Ico (l + 1) r) := by
    ext t
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have hnot : l ∉ Finset.Ico (l + 1) r := by
    simp only [Finset.mem_Ico]
    omega
  rw [hIco, Finset.sum_insert hnot]
  have hlt : l < B i := lt_of_lt_of_le hlr hr
  simp [pathEdgeTerm, dite_eq_left hlt]

@[expose] def signedPathEdges {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (a b : ℕ) (ha : a ≤ B i) (hb : b ≤ B i) : Chain d B :=
  if _h : a ≤ b then pathEdges c i a b hb else -(pathEdges c i b a ha)

theorem signedPathEdges_coefficientwiseBound {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (a b : ℕ) (ha : a ≤ B i) (hb : b ≤ B i) :
    ∀ x, (signedPathEdges c i a b ha hb x).natAbs ≤ 1 := by
  by_cases h : a ≤ b
  · simpa [signedPathEdges, h] using
      (pathEdges_coefficientwiseBound c i a b hb)
  · intro x
    have hneg := pathEdges_coefficientwiseBound c i b a ha x
    simpa [signedPathEdges, h, Finsupp.neg_apply] using hneg

theorem signedPathEdges_succ {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (a t : ℕ) (ha : a ≤ B i) (ht : t < B i) :
    signedPathEdges c i a (t + 1) ha (Nat.succ_le_of_lt ht) -
      signedPathEdges c i a t ha (Nat.le_of_lt ht) =
        basisChain (edgeCell c i ⟨t, ht⟩) := by
  by_cases hat : a ≤ t
  · have hat1 : a ≤ t + 1 := by omega
    have htop : signedPathEdges c i a (t + 1) ha (Nat.succ_le_of_lt ht) =
        pathEdges c i a (t + 1) (Nat.succ_le_of_lt ht) := by
      simp [signedPathEdges, hat1]
    have hlow : signedPathEdges c i a t ha (Nat.le_of_lt ht) =
        pathEdges c i a t (Nat.le_of_lt ht) := by
      simp [signedPathEdges, hat]
    rw [htop, hlow, pathEdges_succ_top c i a t hat (Nat.succ_le_of_lt ht)]
    abel
  · have hta : t < a := by omega
    by_cases heq : a = t + 1
    · subst a
      have hrec := pathEdges_succ_left c i t (t + 1) (by omega)
        (Nat.succ_le_of_lt ht)
      have htop : signedPathEdges c i (t + 1) (t + 1) (by omega)
          (by omega) = pathEdges c i (t + 1) (t + 1) (by omega) := by
        simp [signedPathEdges]
      have hlow : signedPathEdges c i (t + 1) t (by omega) (Nat.le_of_lt ht) =
          -pathEdges c i t (t + 1) (by omega) := by
        simp [signedPathEdges, not_le_of_gt (show t < t + 1 by omega)]
      have hzero : pathEdges c i (t + 1) (t + 1) (by omega) = 0 := by
        rw [pathEdges_eq_Ico]
        simp
      rw [htop, hlow, hrec, hzero]
      abel
    · have hnext : t + 1 < a := by omega
      have hrec₀ := pathEdges_succ_left c i t a hta ha
      have hrec₁ := pathEdges_succ_left c i (t + 1) a hnext ha
      have htop : signedPathEdges c i a (t + 1) ha (Nat.succ_le_of_lt ht) =
          -pathEdges c i (t + 1) a ha := by
        simp [signedPathEdges, not_le_of_gt hnext]
      have hlow : signedPathEdges c i a t ha (Nat.le_of_lt ht) =
          -pathEdges c i t a ha := by
        simp [signedPathEdges, not_le_of_gt hta]
      rw [htop, hlow, hrec₀, hrec₁]
      abel

theorem cellRankBefore_edgeCell_self {d : ℕ} {B : Box d} (c : Cell d B)
    (i : Fin d) (e : Fin (B i)) :
    cellRankBefore (edgeCell c i e) i = cellRankBefore c i := by
  unfold cellRankBefore
  apply congrArg Finset.card
  ext j
  by_cases hji : j < i
  · have hne : j ≠ i := ne_of_lt hji
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [edgeCell, coordIsEdge, hji, Function.update_of_ne hne]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [edgeCell, coordIsEdge, hji]

@[expose] def vertexChainZeroExtension {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d)
    (t : ℕ) : Chain d B :=
  if ht : t ≤ B i then basisChain (vertexUpdate c i ⟨t, Nat.lt_succ_of_le ht⟩) else 0

@[expose] def anchorPathBasis {d : ℕ} {B : Box d} (anchor : Anchor d B)
    (c : Cell d B) (i : Fin d) : Chain d B :=
  match c i with
  | Sum.inr _ => 0
  | Sum.inl v =>
      if (anchor i).val ≤ v.val then
        ((-1 : ℤ) ^ cellRankBefore c i) •
          pathEdges c i (anchor i).val v.val (Nat.le_of_lt_succ v.isLt)
      else
        - (((-1 : ℤ) ^ cellRankBefore c i) •
          pathEdges c i v.val (anchor i).val (Nat.le_of_lt_succ (anchor i).isLt))

theorem anchorPathBasis_coefficientwiseBound {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (c : Cell d B) (i : Fin d) :
    ∀ x, (anchorPathBasis anchor c i x).natAbs ≤ 1 := by
  cases hci : c i with
  | inr e => intro x; simp [anchorPathBasis, hci]
  | inl v =>
    by_cases hav : (anchor i).val ≤ v.val
    · intro x
      have hsign : ((-1 : ℤ) ^ cellRankBefore c i).natAbs = 1 := by simp
      have hpath := pathEdges_coefficientwiseBound c i (anchor i).val v.val
        (Nat.le_of_lt_succ v.isLt) x
      simpa [anchorPathBasis, hci, hav, Finsupp.smul_apply,
        Int.natAbs_mul, hsign] using hpath
    · intro x
      have hsign : ((-1 : ℤ) ^ cellRankBefore c i).natAbs = 1 := by simp
      have hpath := pathEdges_coefficientwiseBound c i v.val (anchor i).val
        (Nat.le_of_lt_succ (anchor i).isLt) x
      simpa [anchorPathBasis, hci, hav, Finsupp.smul_apply,
        Int.natAbs_mul, hsign] using hpath

@[expose] def projectionBasis {d : ℕ} {B : Box d} (anchor : Anchor d B)
    (c : Cell d B) (i : Fin d) : Chain d B :=
  match c i with
  | Sum.inl _ => basisChain (Function.update c i (Sum.inl (anchor i)))
  | Sum.inr _ => 0

@[expose] def homotopy {d : ℕ} {B : Box d} (anchor : Anchor d B) (i : Fin d) :
    Chain d B →ₗ[ℤ] Chain d B := extendBasisMap (anchorPathBasis anchor · i)

@[expose] def projection {d : ℕ} {B : Box d} (anchor : Anchor d B) (i : Fin d) :
    Chain d B →ₗ[ℤ] Chain d B := extendBasisMap (projectionBasis anchor · i)

@[expose] def cellDegree {d : ℕ} {B : Box d} (c : Cell d B) : ℕ := (cellAxes c).card

@[expose] def cellCoordLower {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d) : ℕ :=
  coordBase (c i)

@[expose] def cellCoordUpper {d : ℕ} {B : Box d} (c : Cell d B) (i : Fin d) : ℕ :=
  coordBase (c i) + if coordIsEdge (c i) then 1 else 0

@[expose] def supportedInRect {d : ℕ} {B : Box d} (q : Chain d B)
    (lo hi : Fin d → ℕ) : Prop :=
  ∀ c ∈ q.support, ∀ i, lo i ≤ cellCoordLower c i ∧ cellCoordUpper c i ≤ hi i

@[expose] def chainL1 {d : ℕ} {B : Box d} (q : Chain d B) : ℕ :=
  ∑ c ∈ q.support, (q c).natAbs

@[expose] def coefficientwiseBound {d : ℕ} {B : Box d} (q : Chain d B) (M : ℕ) : Prop :=
  ∀ c, (q c).natAbs ≤ M

/-- The coefficientwise triangle estimate for a linear combination whose
basis images have coefficients in `{−1,0,1}`. -/
theorem linearCombination_coefficientwise_le_l1 {d : ℕ} {B : Box d}
    (f : Cell d B → Chain d B) (q : Chain d B)
    (hf : ∀ c x, (f c x).natAbs ≤ 1) :
    coefficientwiseBound (Finsupp.linearCombination ℤ f q) (chainL1 q) := by
  intro x
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, chainL1]
  have hsum : (∑ c ∈ q.support, q c • f c) x =
      ∑ c ∈ q.support, q c * f c x := by
    simp
  rw [hsum]
  change (∑ c ∈ q.support, q c * f c x).natAbs ≤
    ∑ c ∈ q.support, (q c).natAbs
  calc
    (∑ c ∈ q.support, q c * f c x).natAbs ≤
        ∑ c ∈ q.support, (q c * f c x).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ c ∈ q.support, (q c).natAbs := by
      apply Finset.sum_le_sum
      intro c hc
      calc
        (q c * f c x).natAbs = (q c).natAbs * (f c x).natAbs := by
          rw [Int.natAbs_mul]
        _ ≤ (q c).natAbs * 1 := Nat.mul_le_mul_left _ (hf c x)
        _ = (q c).natAbs := by simp

@[expose] def positiveDegreeSupport {d : ℕ} {B : Box d} (q : Chain d B) : Prop :=
  ∀ c ∈ q.support, 0 < cellDegree c

/-- A chain is homogeneous when all cells in its support have one dimension. -/
@[expose] def homogeneousSupport {d : ℕ} {B : Box d} (q : Chain d B) (k : ℕ) : Prop :=
  ∀ c ∈ q.support, cellDegree c = k

theorem homogeneousSupport_add {d : ℕ} {B : Box d} {q r : Chain d B} {k : ℕ}
    (hq : homogeneousSupport q k) (hr : homogeneousSupport r k) :
    homogeneousSupport (q + r) k := by
  intro c hc
  have hc' : c ∈ q.support ∪ r.support := Finsupp.support_add hc
  rcases Finset.mem_union.mp hc' with hq' | hr'
  · exact hq c hq'
  · exact hr c hr'

theorem homogeneousSupport_smul {d : ℕ} {B : Box d} (z : ℤ)
    {q : Chain d B} {k : ℕ} (hq : homogeneousSupport q k) :
    homogeneousSupport (z • q) k := by
  intro c hc
  apply hq
  rw [Finsupp.mem_support_iff] at hc ⊢
  intro hz
  apply hc
  simp [hz]

theorem homogeneousSupport_basis {d : ℕ} {B : Box d} (c : Cell d B) :
    homogeneousSupport (basisChain c) (cellDegree c) := by
  intro x hx
  by_cases h : x = c
  · subst x
    rfl
  · simp [basisChain, h] at hx

private theorem homogeneousSupport_finite_sum {d : ℕ} {B : Box d} {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Chain d B) (k : ℕ)
    (hf : ∀ i ∈ s, homogeneousSupport (f i) k) :
    homogeneousSupport (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [homogeneousSupport]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply homogeneousSupport_add
      · exact hf i (Finset.mem_insert_self i s)
      · apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)

private theorem cellDegree_edgeCell_of_vertex {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (e : Fin (B i))
    (hvertex : ¬ coordIsEdge (c i)) :
    cellDegree (edgeCell c i e) = cellDegree c + 1 := by
  have hi : i ∉ cellAxes c := by simp [cellAxes, hvertex]
  rw [cellDegree, cellAxes_edgeCell_eq_insert, Finset.card_insert_of_notMem hi]
  simp [cellDegree]

theorem homogeneousSupport_pathEdges {d : ℕ} {B : Box d} (c : Cell d B)
    (i : Fin d) (l r : ℕ) (hr : r ≤ B i)
    (hvertex : ¬ coordIsEdge (c i)) :
    homogeneousSupport (pathEdges c i l r hr) (cellDegree c + 1) := by
  classical
  unfold pathEdges
  change homogeneousSupport
    (∑ t ∈ (Finset.univ : Finset {t : ℕ // t ∈ Finset.Ico l r}),
      basisChain (edgeCell c i ⟨t.val, by
        have ht := Finset.mem_Ico.mp t.property
        exact lt_of_lt_of_le ht.2 hr
      ⟩)) (cellDegree c + 1)
  apply homogeneousSupport_finite_sum
  intro t ht
  simpa only [cellDegree_edgeCell_of_vertex c i _ hvertex] using
    (homogeneousSupport_basis (edgeCell c i ⟨t.val, by
    have ht' := Finset.mem_Ico.mp t.property
    exact lt_of_lt_of_le ht'.2 hr
  ⟩))

theorem homogeneousSupport_linearCombination_raise
    {α ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] (outDegree : ι → ℕ) (inDegree : α → ℕ)
    (f : α → ι →₀ M)
    (hf : ∀ a x, x ∈ (f a).support → outDegree x = inDegree a + 1)
    (q : α →₀ R) (k : ℕ)
    (hq : ∀ a ∈ q.support, inDegree a = k) :
    ∀ x ∈ (Finsupp.linearCombination R f q).support, outDegree x = k + 1 := by
  rw [Finsupp.linearCombination_apply]
  intro x hx
  have hsum := Finsupp.support_sum hx
  rcases Finset.mem_biUnion.mp hsum with ⟨a, ha, hx⟩
  have hx' : x ∈ (f a).support := by
    rw [Finsupp.mem_support_iff] at hx ⊢
    intro hz
    apply hx
    simp [hz]
  rw [hf a x hx', hq a ha]

theorem homogeneousSupport_linearCombination_same
    {α ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] (outDegree : ι → ℕ) (inDegree : α → ℕ)
    (f : α → ι →₀ M)
    (hf : ∀ a x, x ∈ (f a).support → outDegree x = inDegree a)
    (q : α →₀ R) (k : ℕ)
    (hq : ∀ a ∈ q.support, inDegree a = k) :
    ∀ x ∈ (Finsupp.linearCombination R f q).support, outDegree x = k := by
  rw [Finsupp.linearCombination_apply]
  intro x hx
  have hsum := Finsupp.support_sum hx
  rcases Finset.mem_biUnion.mp hsum with ⟨a, ha, hx⟩
  have hx' : x ∈ (f a).support := by
    rw [Finsupp.mem_support_iff] at hx ⊢
    intro hz
    apply hx
    simp [hz]
  rw [hf a x hx', hq a ha]

theorem supportedInRect_add {d : ℕ} {B : Box d} {q r : Chain d B}
    {lo hi : Fin d → ℕ} (hq : supportedInRect q lo hi)
    (hr : supportedInRect r lo hi) : supportedInRect (q + r) lo hi := by
  intro c hc i
  have hc' : c ∈ q.support ∪ r.support := Finsupp.support_add hc
  rcases Finset.mem_union.mp hc' with hq' | hr'
  · exact hq c hq' i
  · exact hr c hr' i

theorem supportedInRect_smul {d : ℕ} {B : Box d} (z : ℤ)
    {q : Chain d B} {lo hi : Fin d → ℕ} (hq : supportedInRect q lo hi) :
    supportedInRect (z • q) lo hi := by
  intro c hc i
  apply hq
  rw [Finsupp.mem_support_iff] at hc ⊢
  intro hz
  apply hc
  simp [hz]

private theorem supportedInRect_finite_sum {d : ℕ} {B : Box d} {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Chain d B) (lo hi : Fin d → ℕ)
    (hf : ∀ i ∈ s, supportedInRect (f i) lo hi) :
    supportedInRect (∑ i ∈ s, f i) lo hi := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [supportedInRect]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply supportedInRect_add
      · exact hf i (Finset.mem_insert_self i s)
      · apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)


theorem supportedInRect_basis_iff {d : ℕ} {B : Box d}
    (c : Cell d B) (lo hi : Fin d → ℕ) :
    supportedInRect (basisChain c) lo hi ↔
      ∀ i, lo i ≤ cellCoordLower c i ∧ cellCoordUpper c i ≤ hi i := by
  constructor
  · intro h i
    exact h c (by simp [basisChain]) i
  · intro h x hx i
    have hxc : x = c := by
      by_cases hxc : x = c
      · exact hxc
      · simp [basisChain, hxc] at hx
    subst x
    exact h i

private theorem supportedInRect_pathEdges {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (l r : ℕ) (hrB : r ≤ B i)
    (lo hi : Fin d → ℕ) (hc : supportedInRect (basisChain c) lo hi)
    (hlo : lo i ≤ l) (hhi : r ≤ hi i) :
    supportedInRect (pathEdges c i l r hrB) lo hi := by
  classical
  unfold pathEdges
  change supportedInRect
    (∑ t ∈ (Finset.univ : Finset {t : ℕ // t ∈ Finset.Ico l r}),
      basisChain (edgeCell c i ⟨t.val, by
        have ht := Finset.mem_Ico.mp t.property
        exact lt_of_lt_of_le ht.2 hrB
      ⟩)) lo hi
  apply supportedInRect_finite_sum
  intro t ht
  refine (supportedInRect_basis_iff
    (edgeCell c i ⟨t.val, by
      have ht' := Finset.mem_Ico.mp t.property
      exact lt_of_lt_of_le ht'.2 hrB
    ⟩) lo hi).2 ?_
  intro j
  have ht' := Finset.mem_Ico.mp t.property
  by_cases hji : j = i
  · subst j
    constructor
    · simpa [edgeCell, cellCoordLower, coordBase] using le_trans hlo ht'.1
    · have htupper : t.val + 1 ≤ r := Nat.succ_le_of_lt ht'.2
      simpa [edgeCell, cellCoordUpper, coordBase, coordIsEdge] using le_trans htupper hhi
  · simpa [edgeCell, cellCoordLower, cellCoordUpper, Function.update_of_ne hji] using
      (supportedInRect_basis_iff c lo hi).mp hc j

theorem supportedInRect_signedPathEdges {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (a b : ℕ)
    (haB : a ≤ B i) (hbB : b ≤ B i) (lo hi : Fin d → ℕ)
    (hc : supportedInRect (basisChain c) lo hi)
    (ha : lo i ≤ a ∧ a ≤ hi i) (hb : lo i ≤ b ∧ b ≤ hi i) :
    supportedInRect (signedPathEdges c i a b haB hbB) lo hi := by
  unfold signedPathEdges
  split_ifs with hab
  · exact supportedInRect_pathEdges c i a b hbB lo hi hc ha.1 hb.2
  · simpa using supportedInRect_smul (-1)
      (supportedInRect_pathEdges c i b a haB lo hi hc hb.1 ha.2)

theorem supportedInRect_linearCombination {d : ℕ} {B : Box d}
    (f : Cell d B → Chain d B) (lo hi : Fin d → ℕ)
    (hf : ∀ c, supportedInRect (basisChain c) lo hi →
      supportedInRect (f c) lo hi) (q : Chain d B)
    (hq : supportedInRect q lo hi) :
    supportedInRect (Finsupp.linearCombination ℤ f q) lo hi := by
  rw [Finsupp.linearCombination_apply]
  intro x hx i
  have hsum := Finsupp.support_sum hx
  rcases Finset.mem_biUnion.mp hsum with ⟨c, hc, hx⟩
  have hx' : x ∈ (f c).support := by
    rw [Finsupp.mem_support_iff] at hx ⊢
    intro hz
    apply hx
    simp [hz]
  exact hf c (supportedInRect_basis_iff c lo hi |>.2 (hq c hc)) x hx' i

private theorem cellAxes_vertexUpdate_of_vertex {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (v : Fin (B i + 1))
    (hvertex : ¬ coordIsEdge (c i)) :
    cellAxes (vertexUpdate c i v) = cellAxes c := by
  apply Finset.ext
  intro j
  simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hji : j = i
  · subst j
    simp [vertexUpdate, coordIsEdge]
    cases h : c i with
    | inl v => rfl
    | inr e => simp [coordIsEdge, h] at hvertex
  · change coordIsEdge (Function.update c i (Sum.inl v) j) ↔ coordIsEdge (c j)
    rw [Function.update_of_ne hji]

theorem homogeneousSupport_projectionBasis {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (c : Cell d B) (i : Fin d) :
    homogeneousSupport (projectionBasis anchor c i) (cellDegree c) := by
  cases hci : c i with
  | inr e => simp [projectionBasis, hci, homogeneousSupport]
  | inl v =>
      have hdeg : cellDegree (vertexUpdate c i (anchor i)) = cellDegree c := by
        unfold cellDegree
        rw [cellAxes_vertexUpdate_of_vertex c i _ (by simp [coordIsEdge, hci])]
      intro x hx
      have hx' : x ∈ (basisChain (vertexUpdate c i (anchor i))).support := by
        change x ∈ (basisChain (Function.update c i (Sum.inl (anchor i)))).support
        simpa [projectionBasis, hci] using hx
      have hdegree := homogeneousSupport_basis (vertexUpdate c i (anchor i)) x hx'
      rw [hdeg] at hdegree
      exact hdegree
end
end FroehlichSpencer.FS82.Cubical

end
