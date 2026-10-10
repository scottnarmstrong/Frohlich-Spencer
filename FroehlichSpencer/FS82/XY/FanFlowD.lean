/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.EndpointResidualD
public import FroehlichSpencer.FS82.XY.EndpointResidual
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Bounded endpoint flows in every dimension at least three

This module assembles finite three-dimensional double-cone flows on coordinate
slices of a cubical path.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open scoped BigOperators

noncomputable section
open Classical

variable {d : ℕ} (hd : 3 ≤ d) {B : Box d}

def xyDFin0 (h : 3 ≤ d) : Fin d :=
  ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) h⟩
def xyDFin1 (h : 3 ≤ d) : Fin d :=
  ⟨1, Nat.lt_of_succ_le (Nat.le_trans (by decide : 2 ≤ 3) h)⟩
def xyDFin2 (h : 3 ≤ d) : Fin d := ⟨2, Nat.lt_of_succ_le h⟩

/-- The first three coordinate directions used by a slice containing `i`.
The two `succAbove` directions are distinct and avoid `i`. -/
def xyDTripleAxis (hd : 3 ≤ d) (i : Fin d) : Fin 3 → Fin d :=
  if _ : i.val = 0 then
    Fin.cases i (fun j : Fin 2 => if j.val = 0 then xyDFin1 hd else xyDFin2 hd)
  else if _ : i.val = 1 then
    Fin.cases i (fun j : Fin 2 => if j.val = 0 then xyDFin0 hd else xyDFin2 hd)
  else
    Fin.cases i (fun j : Fin 2 => if j.val = 0 then xyDFin0 hd else xyDFin1 hd)

theorem xyDTripleAxis_zero (i : Fin d) : xyDTripleAxis hd i 0 = i := by
  unfold xyDTripleAxis
  split_ifs <;> rfl

theorem xyDTripleAxis_one (i : Fin d) :
    xyDTripleAxis hd i 1 ≠ i := by
  unfold xyDTripleAxis
  split_ifs with h0 h1
  · change xyDFin1 hd ≠ i
    intro h
    have hv := congrArg Fin.val h
    simp [xyDFin1] at hv
    omega
  · change xyDFin0 hd ≠ i
    intro h
    have hv := congrArg Fin.val h
    simp [xyDFin0] at hv
    omega
  · change xyDFin0 hd ≠ i
    intro h
    have hv := congrArg Fin.val h
    simp [xyDFin0] at hv
    omega

theorem xyDTripleAxis_two (i : Fin d) :
    xyDTripleAxis hd i 2 ≠ i := by
  unfold xyDTripleAxis
  split_ifs with h0 h1
  · change xyDFin2 hd ≠ i
    intro h
    have hv := congrArg Fin.val h
    simp [xyDFin2] at hv
    omega
  · change xyDFin2 hd ≠ i
    intro h
    have hv := congrArg Fin.val h
    simp [xyDFin2] at hv
    omega
  · change xyDFin1 hd ≠ i
    intro h
    have hv := congrArg Fin.val h
    simp [xyDFin1] at hv
    omega

theorem xyDTripleAxis_injective (i : Fin d) :
    Function.Injective (xyDTripleAxis hd i) := by
  have h1 := xyDTripleAxis_one (hd := hd) i
  have h2 := xyDTripleAxis_two (hd := hd) i
  have h01 : xyDTripleAxis hd i 0 ≠ xyDTripleAxis hd i 1 := by
    intro h
    apply h1
    simpa only [xyDTripleAxis_zero] using h.symm
  have h02 : xyDTripleAxis hd i 0 ≠ xyDTripleAxis hd i 2 := by
    intro h
    apply h2
    simpa only [xyDTripleAxis_zero] using h.symm
  have h12 : xyDTripleAxis hd i 1 ≠ xyDTripleAxis hd i 2 := by
    unfold xyDTripleAxis
    split_ifs with h0 h1
    · change xyDFin1 hd ≠ xyDFin2 hd
      intro h
      have hv := congrArg Fin.val h
      simp [xyDFin1, xyDFin2] at hv
    · change xyDFin0 hd ≠ xyDFin2 hd
      intro h
      have hv := congrArg Fin.val h
      simp [xyDFin0, xyDFin2] at hv
    · change xyDFin0 hd ≠ xyDFin1 hd
      intro h
      have hv := congrArg Fin.val h
      simp [xyDFin0, xyDFin1] at hv
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact Fin.ext rfl
  · exfalso
    apply h01
    simpa using hab
  · exfalso
    apply h02
    simpa using hab
  · exfalso
    apply h01
    simpa using hab.symm
  · exact Fin.ext rfl
  · exfalso
    apply h12
    simpa using hab
  · exfalso
    apply h02
    simpa using hab.symm
  · exfalso
    apply h12
    simpa using hab.symm
  · exact Fin.ext rfl

abbrev XYDVertex := (i : Fin d) → Fin (B i + 1)

/-- The three-dimensional cubical slice through the selected coordinate
directions. -/
abbrev xyDSliceBox (i : Fin d) : Box 3 :=
  fun k => B (xyDTripleAxis hd i k)

/-- Place a three-dimensional cell into the selected coordinate slice, fixing
all other coordinates at the vertex `base`. -/
def xyDSliceCell (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) : Cell d B :=
  Function.update
    (Function.update
      (Function.update (fun j => (Sum.inl (base j) : Coord B j))
        (xyDTripleAxis hd i 0) (c 0))
    (xyDTripleAxis hd i 1) (c 1))
    (xyDTripleAxis hd i 2) (c 2)

theorem xyDSliceCell_apply_zero (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) :
    xyDSliceCell (hd := hd) (B := B) i base c (xyDTripleAxis hd i 0) = c 0 := by
  change Function.update
      (Function.update
        (Function.update (fun j => (Sum.inl (base j) : Coord B j))
          (xyDTripleAxis hd i 0) (c 0))
        (xyDTripleAxis hd i 1) (c 1))
      (xyDTripleAxis hd i 2) (c 2) (xyDTripleAxis hd i 0) = c 0
  rw [Function.update_of_ne (by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2)
      ((xyDTripleAxis_injective (hd := hd) i) h))]
  rw [Function.update_of_ne (by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1)
      ((xyDTripleAxis_injective (hd := hd) i) h))]
  rw [Function.update_self]

theorem xyDSliceCell_apply_one (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) :
    xyDSliceCell (hd := hd) (B := B) i base c (xyDTripleAxis hd i 1) = c 1 := by
  change Function.update
      (Function.update
        (Function.update (fun j => (Sum.inl (base j) : Coord B j))
          (xyDTripleAxis hd i 0) (c 0))
        (xyDTripleAxis hd i 1) (c 1))
      (xyDTripleAxis hd i 2) (c 2) (xyDTripleAxis hd i 1) = c 1
  rw [Function.update_of_ne (by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2)
      ((xyDTripleAxis_injective (hd := hd) i) h))]
  rw [Function.update_self]

theorem xyDSliceCell_apply_two (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) :
    xyDSliceCell (hd := hd) (B := B) i base c (xyDTripleAxis hd i 2) = c 2 := by
  change Function.update
      (Function.update
        (Function.update (fun j => (Sum.inl (base j) : Coord B j))
          (xyDTripleAxis hd i 0) (c 0))
        (xyDTripleAxis hd i 1) (c 1))
      (xyDTripleAxis hd i 2) (c 2) (xyDTripleAxis hd i 2) = c 2
  rw [Function.update_self]

theorem xyDSliceCell_apply_axis (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) (k : Fin 3) :
    xyDSliceCell (hd := hd) (B := B) i base c (xyDTripleAxis hd i k) = c k := by
  fin_cases k
  · simpa using xyDSliceCell_apply_zero (hd := hd) (B := B) i base c
  · simpa using xyDSliceCell_apply_one (hd := hd) (B := B) i base c
  · simpa using xyDSliceCell_apply_two (hd := hd) (B := B) i base c

theorem xyDSliceCell_update_axis (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) (k : Fin 3)
    (v : Coord (xyDSliceBox (hd := hd) (B := B) i) k) :
    xyDSliceCell (hd := hd) (B := B) i base (Function.update c k v) =
      Function.update (xyDSliceCell (hd := hd) (B := B) i base c)
        (xyDTripleAxis hd i k) v := by
  have h01 : xyDTripleAxis hd i 0 ≠ xyDTripleAxis hd i 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1)
      ((xyDTripleAxis_injective (hd := hd) i) h)
  have h02 : xyDTripleAxis hd i 0 ≠ xyDTripleAxis hd i 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2)
      ((xyDTripleAxis_injective (hd := hd) i) h)
  have h12 : xyDTripleAxis hd i 1 ≠ xyDTripleAxis hd i 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2)
      ((xyDTripleAxis_injective (hd := hd) i) h)
  funext j
  by_cases hj0 : j = xyDTripleAxis hd i 0
  · subst j
    by_cases hk : k = 0
    · subst k
      rw [xyDSliceCell_apply_zero]
      simp
    · have hne : xyDTripleAxis hd i 0 ≠ xyDTripleAxis hd i k := by
        intro h
        apply hk
        exact (xyDTripleAxis_injective (hd := hd) i) h.symm
      rw [xyDSliceCell_apply_zero, Function.update_of_ne hne]
      rw [xyDSliceCell_apply_zero]
      exact Function.update_of_ne (Ne.symm hk) v c
  · by_cases hj1 : j = xyDTripleAxis hd i 1
    · subst j
      by_cases hk : k = 1
      · subst k
        rw [xyDSliceCell_apply_one]
        simp
      · have hne : xyDTripleAxis hd i 1 ≠ xyDTripleAxis hd i k := by
          intro h
          apply hk
          exact (xyDTripleAxis_injective (hd := hd) i) h.symm
        rw [xyDSliceCell_apply_one, Function.update_of_ne hne]
        rw [xyDSliceCell_apply_one]
        exact Function.update_of_ne (Ne.symm hk) v c
    · by_cases hj2 : j = xyDTripleAxis hd i 2
      · subst j
        by_cases hk : k = 2
        · subst k
          rw [xyDSliceCell_apply_two]
          simp
        · have hne : xyDTripleAxis hd i 2 ≠ xyDTripleAxis hd i k := by
            intro h
            apply hk
            exact (xyDTripleAxis_injective (hd := hd) i) h.symm
          rw [xyDSliceCell_apply_two, Function.update_of_ne hne]
          rw [xyDSliceCell_apply_two]
          exact Function.update_of_ne (Ne.symm hk) v c
      · have hjk : j ≠ xyDTripleAxis hd i k := by
          intro h
          fin_cases k
          · exact hj0 h
          · exact hj1 h
          · exact hj2 h
        simp [xyDSliceCell, Function.update_of_ne hj0,
          Function.update_of_ne hj1, Function.update_of_ne hj2,
          Function.update_of_ne hjk]

theorem xyDSliceCell_upperFace (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) (k : Fin 3)
    (e : Fin (xyDSliceBox (hd := hd) (B := B) i k)) :
    xyDSliceCell (hd := hd) (B := B) i base (upperFace c k e) =
      upperFace (xyDSliceCell (hd := hd) (B := B) i base c)
        (xyDTripleAxis hd i k) e := by
  simp only [upperFace, vertexUpdate]
  exact xyDSliceCell_update_axis (hd := hd) (B := B) i base c k _

theorem xyDSliceCell_lowerFace (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) (k : Fin 3)
    (e : Fin (xyDSliceBox (hd := hd) (B := B) i k)) :
    xyDSliceCell (hd := hd) (B := B) i base (lowerFace c k e) =
      lowerFace (xyDSliceCell (hd := hd) (B := B) i base c)
        (xyDTripleAxis hd i k) e := by
  simp only [lowerFace, vertexUpdate]
  exact xyDSliceCell_update_axis (hd := hd) (B := B) i base c k _

theorem xyDSliceCell_cellAxes (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) :
    cellAxes (xyDSliceCell (hd := hd) (B := B) i base c) =
      (cellAxes c).image (xyDTripleAxis hd i) := by
  classical
  ext j
  simp only [Finset.mem_image, cellAxes, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro hj
    by_cases hj0 : j = xyDTripleAxis hd i 0
    · subst j
      refine ⟨0, ?_, rfl⟩
      rw [← xyDSliceCell_apply_zero (hd := hd) (B := B) i base c]
      exact hj
    · by_cases hj1 : j = xyDTripleAxis hd i 1
      · subst j
        refine ⟨1, ?_, rfl⟩
        rw [← xyDSliceCell_apply_one (hd := hd) (B := B) i base c]
        exact hj
      · by_cases hj2 : j = xyDTripleAxis hd i 2
        · subst j
          refine ⟨2, ?_, rfl⟩
          rw [← xyDSliceCell_apply_two (hd := hd) (B := B) i base c]
          exact hj
        · simp [coordIsEdge, xyDSliceCell, Function.update_of_ne hj0,
            Function.update_of_ne hj1, Function.update_of_ne hj2] at hj
  · rintro ⟨k, hk, hkj⟩
    subst j
    rw [xyDSliceCell_apply_axis (hd := hd) (B := B) i base c k]
    exact hk

theorem xyDSliceCell_degree_one (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i))
    (hc : cellDegree c = 1) :
    cellDegree (xyDSliceCell (hd := hd) (B := B) i base c) = 1 := by
  change (cellAxes (xyDSliceCell (hd := hd) (B := B) i base c)).card = 1
  rw [xyDSliceCell_cellAxes (hd := hd) (B := B) i base c]
  rw [Finset.card_image_of_injective _ (xyDTripleAxis_injective (hd := hd) i)]
  exact hc

theorem xyDSliceCell_injective (i : Fin d) (base : XYDVertex (d := d) (B := B)) :
    Function.Injective (xyDSliceCell (hd := hd) (B := B) i base) := by
  have h01 : xyDTripleAxis hd i 0 ≠ xyDTripleAxis hd i 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1)
      ((xyDTripleAxis_injective (hd := hd) i) h)
  have h02 : xyDTripleAxis hd i 0 ≠ xyDTripleAxis hd i 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2)
      ((xyDTripleAxis_injective (hd := hd) i) h)
  have h12 : xyDTripleAxis hd i 1 ≠ xyDTripleAxis hd i 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2)
      ((xyDTripleAxis_injective (hd := hd) i) h)
  intro c c' h
  have h0 : c 0 = c' 0 := by
    have hk := congrFun h (xyDTripleAxis hd i 0)
    rw [xyDSliceCell_apply_zero (hd := hd) (B := B) i base c,
      xyDSliceCell_apply_zero (hd := hd) (B := B) i base c'] at hk
    exact hk
  have h1 : c 1 = c' 1 := by
    have hk := congrFun h (xyDTripleAxis hd i 1)
    rw [xyDSliceCell_apply_one (hd := hd) (B := B) i base c,
      xyDSliceCell_apply_one (hd := hd) (B := B) i base c'] at hk
    exact hk
  have h2 : c 2 = c' 2 := by
    have hk := congrFun h (xyDTripleAxis hd i 2)
    rw [xyDSliceCell_apply_two (hd := hd) (B := B) i base c,
      xyDSliceCell_apply_two (hd := hd) (B := B) i base c'] at hk
    exact hk
  funext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

def xyDSliceCellEmbedding (i : Fin d) (base : XYDVertex (d := d) (B := B)) :
    Cell 3 (xyDSliceBox (hd := hd) (B := B) i) ↪ Cell d B where
  toFun := xyDSliceCell (hd := hd) (B := B) i base
  inj' := xyDSliceCell_injective (hd := hd) (B := B) i base

/-- Push a real cubical chain into the selected coordinate slice. -/
noncomputable def xyDSliceChainMap (i : Fin d) (base : XYDVertex (d := d) (B := B)) :
    RealChain 3 (xyDSliceBox (hd := hd) (B := B) i) →ₗ[ℝ] RealChain d B :=
  Finsupp.linearCombination ℝ
    (fun c => Finsupp.single (xyDSliceCell (hd := hd) (B := B) i base c) 1)

theorem xyDSliceChainMap_eq_embDomain (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (q : RealChain 3 (xyDSliceBox (hd := hd) (B := B) i)) :
    xyDSliceChainMap (hd := hd) (B := B) i base q =
      Finsupp.embDomain (xyDSliceCellEmbedding (hd := hd) (B := B) i base) q := by
  induction q using Finsupp.induction_linear with
  | zero => simp [xyDSliceChainMap]
  | add q r hq hr =>
      rw [map_add, hq, hr]
      ext c
      simp [Finsupp.embDomain_apply]
  | single c r =>
      simp [xyDSliceChainMap, xyDSliceCellEmbedding,
        Finsupp.linearCombination_single, Finsupp.embDomain_single]

theorem xyDualDBondEnergy_eq_support_sum (q : RealChain d B)
    (hq : realHomogeneousSupport q 1) :
    xyDualDBondEnergy (d := d) (B := B) q =
      ∑ c ∈ q.support, q c ^ 2 := by
  classical
  have hzero : ∀ c : Cell d B, cellDegree c ≠ 1 → q c = 0 := by
    intro c hc
    by_contra hne
    exact hc (hq c (Finsupp.mem_support_iff.mpr hne))
  let p : Cell d B → Prop := fun c => cellDegree c = 1
  let genBond : Fintype {c : Cell d B // p c} := Subtype.fintype p
  let genOther : Fintype {c : Cell d B // ¬ p c} := Subtype.fintype _
  let allCells : Fintype (Cell d B) := inferInstance
  have hsplit := @Fintype.sum_subtype_add_sum_subtype ℝ (Cell d B)
    allCells _ p (fun c => q c ^ 2)
  have hcomplement :
      (@Finset.univ {c : Cell d B // ¬ p c} genOther).sum
          (fun c => q c.1 ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    simp [hzero c.1 c.2]
  have hbridge :
      (@Finset.univ {c : Cell d B // p c} genBond).sum
          (fun c => q c.1 ^ 2) =
        (@Finset.univ (XYBonds B) (xyBondsFintype (B := B))).sum
          (fun b => q b.1 ^ 2) := by
    exact @Equiv.sum_comp _ _ ℝ genBond (xyBondsFintype (B := B)) _
      (Equiv.refl _) (fun b => q b.1 ^ 2)
  have hsplit' :
      (@Finset.univ {c : Cell d B // p c} genBond).sum
          (fun c => q c.1 ^ 2) +
        (@Finset.univ {c : Cell d B // ¬ p c} genOther).sum
          (fun c => q c.1 ^ 2) =
        (@Finset.univ (Cell d B) allCells).sum (fun c => q c ^ 2) := by
    exact hsplit
  unfold xyDualDBondEnergy
  calc
    (@Finset.univ (XYBonds B) (xyBondsFintype (B := B))).sum
        (fun c => q c.1 ^ 2) =
        (@Finset.univ {c : Cell d B // p c} genBond).sum
          (fun c => q c.1 ^ 2) := hbridge.symm
    _ = (@Finset.univ (Cell d B) allCells).sum (fun c => q c ^ 2) := by
      rw [← hsplit']
      rw [hcomplement, add_zero]
    _ = ∑ c ∈ q.support, q c ^ 2 := by
      symm
      exact @Finsupp.sum_fintype (Cell d B) ℝ ℝ _ _ allCells q
        (fun (_ : Cell d B) (a : ℝ) => a ^ 2) (by intro c; simp)

theorem xyDualDBondEnergy_embDomain (i : Fin d)
    (e : Cell 3 (xyDSliceBox (hd := hd) (B := B) i) ↪ Cell d B)
    (he : ∀ c, cellDegree c = 1 → cellDegree (e c) = 1)
    (q : RealChain 3 (xyDSliceBox (hd := hd) (B := B) i))
    (hq : realHomogeneousSupport q 1) :
    xyDualDBondEnergy (d := d) (B := B) (Finsupp.embDomain e q) =
      xyDualDBondEnergy (d := 3) (B := xyDSliceBox (hd := hd) (B := B) i) q := by
  have hq' : realHomogeneousSupport (Finsupp.embDomain e q) 1 := by
    intro c hc
    rw [Finsupp.support_embDomain] at hc
    rcases Finset.mem_map.mp hc with ⟨c', hc', rfl⟩
    exact he c' (hq c' hc')
  rw [xyDualDBondEnergy_eq_support_sum (d := d) (B := B) _ hq']
  rw [xyDualDBondEnergy_eq_support_sum (d := 3)
    (B := xyDSliceBox (hd := hd) (B := B) i) q hq]
  calc
    (∑ c ∈ (Finsupp.embDomain e q).support,
        (Finsupp.embDomain e q) c ^ 2) =
        (Finsupp.embDomain e q).sum (fun (_ : Cell d B) (a : ℝ) => a ^ 2) := rfl
    _ = q.sum (fun (_ : Cell 3 (xyDSliceBox (hd := hd) (B := B) i))
        (a : ℝ) => a ^ 2) := by rw [Finsupp.sum_embDomain]
    _ = ∑ c ∈ q.support, q c ^ 2 := rfl

theorem cellDegree_one_axis (c : Cell d B) (hc : cellDegree c = 1) :
    ∃ (k : Fin d) (e : Fin (B k)), c k = Sum.inr e ∧
      ∀ j, j ≠ k → ¬ coordIsEdge (c j) := by
  have hcard : (cellAxes c).card = 1 := hc
  obtain ⟨k, haxes⟩ := Finset.card_eq_one.mp hcard
  have hk : coordIsEdge (c k) := by
    have : k ∈ cellAxes c := by rw [haxes]; simp
    simpa [cellAxes] using this
  cases hcoord : c k with
  | inl v => simp [coordIsEdge, hcoord] at hk
  | inr e =>
      refine ⟨k, e, hcoord, ?_⟩
      intro j hj hedge
      have hmem : j ∈ cellAxes c := by simpa [cellAxes] using hedge
      rw [haxes] at hmem
      simp at hmem
      exact hj hmem

theorem xyDSliceChainMap_single (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) (r : ℝ) :
    xyDSliceChainMap (hd := hd) (B := B) i base (Finsupp.single c r) =
      Finsupp.single (xyDSliceCell (hd := hd) (B := B) i base c) r := by
  rw [xyDSliceChainMap_eq_embDomain]
  simp [xyDSliceCellEmbedding]

theorem boundary_basis_of_single_edge (c : Cell d B) (k : Fin d) (e : Fin (B k))
    (hc : c k = Sum.inr e)
    (hother : ∀ j, j ≠ k → ¬ coordIsEdge (c j)) :
    boundary (basisChain c) =
      basisChain (upperFace c k e) - basisChain (lowerFace c k e) := by
  classical
  have hrank : cellRankBefore c k = 0 := by
    have hempty :
        (Finset.univ.filter fun j : Fin d => j < k ∧ coordIsEdge (c j)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j hj
      rintro ⟨hjk, hedge⟩
      exact hother j (ne_of_lt hjk) hedge
    simp [cellRankBefore, hempty]
  rw [boundary_basis]
  unfold boundaryBasis
  rw [Finset.sum_eq_single k]
  · rw [hc, hrank]
    simp
  · intro j hj hjk
    have hno := hother j hjk
    cases hcoord : c j with
    | inl v => simp
    | inr f => exact (hno (by simp [coordIsEdge, hcoord])).elim
  · simp

theorem realBoundary_single_of_single_edge (c : Cell d B) (k : Fin d)
    (e : Fin (B k)) (hc : c k = Sum.inr e)
    (hother : ∀ j, j ≠ k → ¬ coordIsEdge (c j)) :
    realBoundary (Finsupp.single c (1 : ℝ)) =
      Finsupp.single (upperFace c k e) 1 - Finsupp.single (lowerFace c k e) 1 := by
  rw [realBoundary, realifyLinearMap_single,
    boundary_basis_of_single_edge c k e hc hother]
  rw [castIntegerChain_sub, castIntegerChain_basis, castIntegerChain_basis]
  simp

theorem xyDSliceBoundary_single (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (c : Cell 3 (xyDSliceBox (hd := hd) (B := B) i)) (hc : cellDegree c = 1) :
    realBoundary (Finsupp.single (xyDSliceCell (hd := hd) (B := B) i base c) (1 : ℝ)) =
      xyDSliceChainMap (hd := hd) (B := B) i base (realBoundary (Finsupp.single c 1)) := by
  obtain ⟨k, e, hcoord, hother⟩ := cellDegree_one_axis c hc
  have htargetCoord :
      xyDSliceCell (hd := hd) (B := B) i base c (xyDTripleAxis hd i k) = Sum.inr e := by
    rw [xyDSliceCell_apply_axis]
    exact hcoord
  have htargetOther : ∀ j, j ≠ xyDTripleAxis hd i k →
      ¬ coordIsEdge (xyDSliceCell (hd := hd) (B := B) i base c j) := by
    intro j hj hedge
    have hjaxes : j ∈ cellAxes (xyDSliceCell (hd := hd) (B := B) i base c) := by
      simpa [cellAxes] using hedge
    rw [xyDSliceCell_cellAxes] at hjaxes
    rcases Finset.mem_image.mp hjaxes with ⟨l, hl, hlj⟩
    have hle : l = k := by
      by_contra hne
      exact hother l hne (by simpa [cellAxes] using hl)
    subst l
    exact hj hlj.symm
  rw [realBoundary_single_of_single_edge (d := d) (B := B)
    (xyDSliceCell (hd := hd) (B := B) i base c) (xyDTripleAxis hd i k)
    e htargetCoord htargetOther]
  rw [realBoundary_single_of_single_edge (d := 3)
    (B := xyDSliceBox (hd := hd) (B := B) i) c k e hcoord hother]
  rw [map_sub,
    xyDSliceChainMap_single, xyDSliceChainMap_single,
    xyDSliceCell_upperFace, xyDSliceCell_lowerFace]

theorem realChain_eq_sum_bondSingles (q : RealChain d B)
    (hq : realHomogeneousSupport q 1) :
    q = ∑ b : XYBonds B, Finsupp.single b.1 (q b.1) := by
  classical
  ext c
  by_cases hc : cellDegree c = 1
  · let b₀ : XYBonds B := ⟨c, hc⟩
    have hsum :
        (∑ b : XYBonds B, Finsupp.single b.1 (q b.1)) c = q c := by
      rw [Finsupp.finsetSum_apply]
      calc
        (∑ b : XYBonds B, (Finsupp.single b.1 (q b.1)) c) =
            (Finsupp.single b₀.1 (q b₀.1)) c := by
              apply Fintype.sum_eq_single b₀
              intro b hne
              have hcell : b.1 ≠ c := by
                intro heq
                apply hne
                exact Subtype.ext heq
              simp [hcell]
        _ = q c := by simp [b₀]
    exact hsum.symm
  · have hqc : q c = 0 := by
      by_contra hne
      exact hc (hq c (Finsupp.mem_support_iff.mpr hne))
    rw [hqc]
    symm
    rw [Finsupp.finsetSum_apply]
    apply Fintype.sum_eq_zero
    intro b
    have hne : b.1 ≠ c := by
      intro heq
      subst c
      exact hc b.2
    simp [hne]

theorem xyDSliceChainMap_realBoundary (i : Fin d) (base : XYDVertex (d := d) (B := B))
    (q : RealChain 3 (xyDSliceBox (hd := hd) (B := B) i))
    (hq : realHomogeneousSupport q 1) :
    realBoundary (xyDSliceChainMap (hd := hd) (B := B) i base q) =
      xyDSliceChainMap (hd := hd) (B := B) i base (realBoundary q) := by
  classical
  rw [realChain_eq_sum_bondSingles q hq]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hsingle : Finsupp.single b.1 (q b.1) =
      (q b.1) • Finsupp.single b.1 (1 : ℝ) := by
    ext c
    by_cases hc : c = b.1 <;> simp [hc]
  rw [hsingle]
  simp only [map_smul]
  rw [xyDSliceChainMap_single,
    xyDSliceBoundary_single (hd := hd) (B := B) i base b.1 b.2]

theorem xyDualDEndpointResidualEnergy_eq_xyDual3ResidualEnergy
    {B3 : Box 3} (x y : XYSites B3) :
    xyDualDEndpointResidualEnergy (d := 3) (B := B3) (hd := by omega) x y =
      xyDual3ResidualEnergy x y := by
  rw [xyDual3ResidualEnergy_eq_loopFieldResidual_inner]
  rfl


theorem xyDThreeDimensionalFlow_exists {B3 : Box 3} (x y : XYSites B3)
    (hCube : ∀ i j : Fin 3, B3 i = B3 j) :
    ∃ J : RealChain 3 B3,
      realHomogeneousSupport J 1 ∧
      realBoundary J = castIntegerChain (xyEndpointSource x y) ∧
      xyDualDBondEnergy J ≤ 72 := by
  obtain ⟨J, hJ, hboundary, henergy⟩ :=
    exists_xyDualDEndpointResidualMinimizingFlow (d := 3) (B := B3)
      (hd := by omega) x y
  refine ⟨J, hJ, hboundary, ?_⟩
  calc
    xyDualDBondEnergy J =
        xyDualDEndpointResidualEnergy (d := 3) (B := B3) (hd := by omega) x y :=
      henergy
    _ = xyDual3ResidualEnergy x y :=
      xyDualDEndpointResidualEnergy_eq_xyDual3ResidualEnergy (d := 3)
        (B3 := B3) x y
    _ ≤ 72 := xyDual3EndpointResidualEnergy_le_uniform x y hCube

theorem xyDSite_noEdge (x : XYSites B) (j : Fin d) :
    ¬ coordIsEdge (x.1 j) := by
  intro hj
  have hmem : j ∈ cellAxes x.1 := by simpa [cellAxes] using hj
  have hpos : 0 < cellDegree x.1 := Finset.card_pos.mpr ⟨j, hmem⟩
  omega

def xyDSiteCoord (x : XYSites B) (j : Fin d) : Fin (B j + 1) :=
  (x.1 j).elim id (fun _ => 0)

theorem xyDSiteCoord_spec (x : XYSites B) (j : Fin d) :
    x.1 j = Sum.inl (xyDSiteCoord (d := d) (B := B) x j) := by
  cases h : x.1 j with
  | inl v => simp [xyDSiteCoord, h]
  | inr e => exact (xyDSite_noEdge (d := d) (B := B) x j (by simp [coordIsEdge, h])).elim

def xyDVertexCell (v : XYDVertex (d := d) (B := B)) : Cell d B :=
  fun j => Sum.inl (v j)

def xyDWaypointVertex (x y : XYSites B) (n : ℕ) : XYDVertex (d := d) (B := B) :=
  fun j => if j.val < n then xyDSiteCoord (d := d) (B := B) y j
    else xyDSiteCoord (d := d) (B := B) x j

def xyDWaypointCell (x y : XYSites B) (n : ℕ) : Cell d B :=
  fun j => Sum.inl (if j.val < n then xyDSiteCoord (d := d) (B := B) y j
    else xyDSiteCoord (d := d) (B := B) x j)

theorem xyDWaypointCell_eq_vertexCell (x y : XYSites B) (n : ℕ) :
    xyDWaypointCell (d := d) (B := B) x y n =
      xyDVertexCell (d := d) (B := B) (xyDWaypointVertex (d := d) (B := B) x y n) := rfl

def xyDWaypoint (x y : XYSites B) (n : ℕ) : XYSites B :=
  ⟨xyDWaypointCell (d := d) (B := B) x y n, by
    simp [cellDegree, cellAxes, coordIsEdge, xyDWaypointCell]
  ⟩

theorem xyDWaypointCell_zero (x y : XYSites B) :
    xyDWaypointCell (d := d) (B := B) x y 0 = x.1 := by
  funext j
  simp [xyDWaypointCell, xyDSiteCoord_spec]

theorem xyDWaypointCell_large (x y : XYSites B) :
    xyDWaypointCell (d := d) (B := B) x y d = y.1 := by
  funext j
  have hjd : j.val < d := j.isLt
  simp [xyDWaypointCell, hjd, xyDSiteCoord_spec]


def xyDSliceSiteOfVertex (i : Fin d) (v : XYDVertex (d := d) (B := B)) :
    XYSites (xyDSliceBox (hd := hd) (B := B) i) :=
  ⟨fun k => Sum.inl (v (xyDTripleAxis hd i k)), by
    simp [cellDegree, cellAxes, coordIsEdge]
  ⟩

theorem xyDSliceCell_vertex_eq (i : Fin d) (base v : XYDVertex (d := d) (B := B))
    (hout : ∀ j, j ∉ Set.range (xyDTripleAxis hd i) → v j = base j) :
    xyDSliceCell (hd := hd) (B := B) i base
      (xyDSliceSiteOfVertex (hd := hd) (B := B) i v).1 = xyDVertexCell v := by
  funext j
  by_cases hj0 : j = xyDTripleAxis hd i 0
  · subst j
    rw [xyDSliceCell_apply_zero]
    simp [xyDSliceSiteOfVertex, xyDVertexCell]
  · by_cases hj1 : j = xyDTripleAxis hd i 1
    · subst j
      rw [xyDSliceCell_apply_one]
      simp [xyDSliceSiteOfVertex, xyDVertexCell]
    · by_cases hj2 : j = xyDTripleAxis hd i 2
      · subst j
        rw [xyDSliceCell_apply_two]
        simp [xyDSliceSiteOfVertex, xyDVertexCell]
      · have hjrange : j ∉ Set.range (xyDTripleAxis hd i) := by
          rintro ⟨k, hkj⟩
          fin_cases k
          · exact hj0 hkj.symm
          · exact hj1 hkj.symm
          · exact hj2 hkj.symm
        simp [xyDSliceCell, Function.update_of_ne hj0,
          Function.update_of_ne hj1, Function.update_of_ne hj2,
          xyDVertexCell, hout j hjrange]

theorem xyDWaypointVertex_succ (x y : XYSites B) (i : Fin d) :
    xyDWaypointVertex (d := d) (B := B) x y (i.val + 1) =
      Function.update (xyDWaypointVertex (d := d) (B := B) x y i.val) i
        (xyDSiteCoord (d := d) (B := B) y i) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [xyDWaypointVertex, Function.update_self]
  · by_cases hlt : j.val < i.val
    · have hlt' : j.val < i.val + 1 := by omega
      simp [xyDWaypointVertex, hlt, hlt', Function.update_of_ne hji]
    · have hnot : ¬ j.val < i.val + 1 := by
        intro hlt'
        have heq : j.val = i.val := by omega
        exact hji (Fin.ext heq)
      simp [xyDWaypointVertex, hlt, hnot, Function.update_of_ne hji]

theorem xyDSegmentFlow_exists (hd : 3 ≤ d) (i : Fin d) (x y : XYSites B)
    (hCube : ∀ j k : Fin d, B j = B k) :
    ∃ J : RealChain d B,
      realHomogeneousSupport J 1 ∧
      realBoundary J = castIntegerChain
        (xyEndpointSource (xyDWaypoint (d := d) (B := B) x y i.val)
          (xyDWaypoint (d := d) (B := B) x y (i.val + 1))) ∧
      xyDualDBondEnergy (d := d) (B := B) J ≤ 72 := by
  let v0 := xyDWaypointVertex (d := d) (B := B) x y i.val
  let v1 := xyDWaypointVertex (d := d) (B := B) x y (i.val + 1)
  let base := v0
  let p := xyDSliceSiteOfVertex (hd := hd) (B := B) i v0
  let q := xyDSliceSiteOfVertex (hd := hd) (B := B) i v1
  have hCube3 : ∀ j k : Fin 3, xyDSliceBox (hd := hd) (B := B) i j =
      xyDSliceBox (hd := hd) (B := B) i k := by
    intro j k
    exact hCube (xyDTripleAxis hd i j) (xyDTripleAxis hd i k)
  obtain ⟨J3, hJ3, hboundary3, henergy3⟩ :=
    xyDThreeDimensionalFlow_exists (B3 := xyDSliceBox (hd := hd) (B := B) i)
      p q hCube3
  let J := Finsupp.embDomain
    (xyDSliceCellEmbedding (hd := hd) (B := B) i base) J3
  have hJ : realHomogeneousSupport J 1 := by
    rw [show J = Finsupp.embDomain
      (xyDSliceCellEmbedding (hd := hd) (B := B) i base) J3 by rfl]
    intro c hc
    rw [Finsupp.support_embDomain] at hc
    rcases Finset.mem_map.mp hc with ⟨c3, hc3, rfl⟩
    exact xyDSliceCell_degree_one (hd := hd) (B := B) i base c3 (hJ3 c3 hc3)
  have hout0 : ∀ j, j ∉ Set.range (xyDTripleAxis hd i) → v0 j = base j := by
    intro j hj
    rfl
  have hmap0 : xyDSliceCell (hd := hd) (B := B) i base p.1 = xyDVertexCell v0 :=
    xyDSliceCell_vertex_eq (hd := hd) (B := B) i base v0 hout0
  have hout1 : ∀ j, j ∉ Set.range (xyDTripleAxis hd i) → v1 j = base j := by
    intro j hj
    have hji : j ≠ i := by
      intro hji
      apply hj
      refine ⟨0, ?_⟩
      simpa [xyDTripleAxis_zero] using hji.symm
    have hv1 : v1 = Function.update v0 i (xyDSiteCoord (d := d) (B := B) y i) := by
      dsimp [v0, v1]
      exact xyDWaypointVertex_succ (d := d) (B := B) x y i
    rw [hv1]
    exact Function.update_of_ne hji (xyDSiteCoord (d := d) (B := B) y i) v0
  have hw0 : (xyDWaypoint (d := d) (B := B) x y i.val).1 = xyDVertexCell v0 := by
    change xyDWaypointCell (d := d) (B := B) x y i.val = xyDVertexCell v0
    rw [xyDWaypointCell_eq_vertexCell]
  have hw1 : (xyDWaypoint (d := d) (B := B) x y (i.val + 1)).1 = xyDVertexCell v1 := by
    change xyDWaypointCell (d := d) (B := B) x y (i.val + 1) = xyDVertexCell v1
    rw [xyDWaypointCell_eq_vertexCell]
  have hmap1 : xyDSliceCell (hd := hd) (B := B) i base q.1 = xyDVertexCell v1 :=
    xyDSliceCell_vertex_eq (hd := hd) (B := B) i base v1 hout1
  have hsource : xyDSliceChainMap (hd := hd) (B := B) i base
      (castIntegerChain (xyEndpointSource p q)) =
      castIntegerChain (xyEndpointSource
        (xyDWaypoint (d := d) (B := B) x y i.val)
        (xyDWaypoint (d := d) (B := B) x y (i.val + 1))) := by
    rw [xyEndpointSource, castIntegerChain_sub, castIntegerChain_basis,
      castIntegerChain_basis, map_sub, xyDSliceChainMap_single,
      xyDSliceChainMap_single, hmap0, hmap1]
    rw [← hw0, ← hw1]
    rw [xyEndpointSource, castIntegerChain_sub, castIntegerChain_basis,
      castIntegerChain_basis]
  have hboundary : realBoundary J = castIntegerChain
      (xyEndpointSource (xyDWaypoint (d := d) (B := B) x y i.val)
        (xyDWaypoint (d := d) (B := B) x y (i.val + 1))) := by
    rw [show J = xyDSliceChainMap (hd := hd) (B := B) i base J3 by
      rw [xyDSliceChainMap_eq_embDomain]]
    rw [xyDSliceChainMap_realBoundary (hd := hd) (B := B) i base J3 hJ3,
      hboundary3, hsource]
  have henergy : xyDualDBondEnergy (d := d) (B := B) J =
      xyDualDBondEnergy (d := 3) (B := xyDSliceBox (hd := hd) (B := B) i) J3 := by
    rw [show J = Finsupp.embDomain
      (xyDSliceCellEmbedding (hd := hd) (B := B) i base) J3 by rfl]
    exact xyDualDBondEnergy_embDomain (hd := hd) (B := B)
      (i := i) (e := xyDSliceCellEmbedding (hd := hd) (B := B) i base)
      (he := fun c hc => xyDSliceCell_degree_one (hd := hd) (B := B) i base c hc)
      J3 hJ3
  exact ⟨J, hJ, hboundary, by rw [henergy]; exact henergy3⟩

theorem xyDualDEndpointResidualEnergy_le_uniform_cube (hd : 3 ≤ d)
    (hCube : ∀ i j : Fin d, B i = B j) (x y : XYSites B) :
    xyDualDEndpointResidualEnergy (hd := hd) x y ≤ 72 * (d : ℝ) ^ 2 := by
  classical
  have hsegments (i : Fin d) :
      ∃ J : RealChain d B,
        realHomogeneousSupport J 1 ∧
        realBoundary J = castIntegerChain
          (xyEndpointSource (xyDWaypoint (d := d) (B := B) x y i.val)
            (xyDWaypoint (d := d) (B := B) x y (i.val + 1))) ∧
        xyDualDBondEnergy (d := d) (B := B) J ≤ 72 :=
    xyDSegmentFlow_exists (d := d) (B := B) hd i x y hCube
  let Jseg : Fin d → RealChain d B := fun i => Classical.choose (hsegments i)
  have hJseg (i : Fin d) :
      realHomogeneousSupport (Jseg i) 1 ∧
      realBoundary (Jseg i) = castIntegerChain
        (xyEndpointSource (xyDWaypoint (d := d) (B := B) x y i.val)
          (xyDWaypoint (d := d) (B := B) x y (i.val + 1))) ∧
      xyDualDBondEnergy (d := d) (B := B) (Jseg i) ≤ 72 :=
    Classical.choose_spec (hsegments i)
  let Jtotal : RealChain d B := ∑ i : Fin d, Jseg i
  have hJtotal : realHomogeneousSupport Jtotal 1 := by
    intro c hc
    rw [show Jtotal = ∑ i : Fin d, Jseg i by rfl] at hc
    have hmem := Finsupp.support_finsetSum (s := Finset.univ) (f := Jseg) hc
    rcases Finset.mem_biUnion.mp hmem with ⟨i, hi, hci⟩
    exact (hJseg i).1 c hci
  have hsource_sum :
      (∑ i : Fin d, castIntegerChain
        (xyEndpointSource (xyDWaypoint (d := d) (B := B) x y i.val)
          (xyDWaypoint (d := d) (B := B) x y (i.val + 1)))) =
        castIntegerChain (xyEndpointSource x y) := by
    let f : ℕ → RealChain d B := fun n =>
      Finsupp.single (xyDWaypoint (d := d) (B := B) x y n).1 (1 : ℝ)
    have hterm (i : Fin d) :
        castIntegerChain
            (xyEndpointSource (xyDWaypoint (d := d) (B := B) x y i.val)
              (xyDWaypoint (d := d) (B := B) x y (i.val + 1))) =
          f i.val - f (i.val + 1) := by
      simp [f, xyEndpointSource, castIntegerChain_sub, castIntegerChain_basis]
    have hw0 : (xyDWaypoint (d := d) (B := B) x y 0).1 = x.1 := by
      change xyDWaypointCell (d := d) (B := B) x y 0 = x.1
      exact xyDWaypointCell_zero x y
    have hwlast : (xyDWaypoint (d := d) (B := B) x y d).1 = y.1 := by
      change xyDWaypointCell (d := d) (B := B) x y d = y.1
      exact xyDWaypointCell_large x y
    have hzero : f 0 = Finsupp.single x.1 (1 : ℝ) := by simp [f, hw0]
    have hlast : f d = Finsupp.single y.1 (1 : ℝ) := by simp [f, hwlast]
    calc
      _ = ∑ i : Fin d, (f i.val - f (i.val + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i
      _ = ∑ n ∈ Finset.range d, (f n - f (n + 1)) :=
        Fin.sum_univ_eq_sum_range (fun n => f n - f (n + 1)) d
      _ = f 0 - f d := Finset.sum_range_sub' f d
      _ = castIntegerChain (xyEndpointSource x y) := by
        rw [hzero, hlast, xyEndpointSource, castIntegerChain_sub,
          castIntegerChain_basis, castIntegerChain_basis]
  have hboundary : realBoundary Jtotal = castIntegerChain (xyEndpointSource x y) := by
    rw [show Jtotal = ∑ i : Fin d, Jseg i by rfl, map_sum]
    calc
      (∑ i : Fin d, realBoundary (Jseg i)) =
          ∑ i : Fin d, castIntegerChain
            (xyEndpointSource (xyDWaypoint (d := d) (B := B) x y i.val)
              (xyDWaypoint (d := d) (B := B) x y (i.val + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hJseg i).2.1
      _ = castIntegerChain (xyEndpointSource x y) := hsource_sum
  have henergy_total : xyDualDBondEnergy (d := d) (B := B) Jtotal ≤
      72 * (d : ℝ) ^ 2 := by
    have hpoint (b : XYBonds B) :
        (∑ i : Fin d, Jseg i b.1) ^ 2 ≤ (d : ℝ) *
          ∑ i : Fin d, (Jseg i b.1) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin d => Jseg i b.1)
      simpa using h
    unfold xyDualDBondEnergy
    calc
      (∑ b : XYBonds B, Jtotal b.1 ^ 2) ≤
          ∑ b : XYBonds B, (d : ℝ) * ∑ i : Fin d, (Jseg i b.1) ^ 2 := by
            apply Finset.sum_le_sum
            intro b hb
            simpa [Jtotal, Finsupp.finsetSum_apply] using hpoint b
      _ = (d : ℝ) * ∑ i : Fin d, xyDualDBondEnergy (d := d) (B := B) (Jseg i) := by
            calc
              (∑ b : XYBonds B, (d : ℝ) * ∑ i : Fin d, (Jseg i b.1) ^ 2) =
                  ∑ b : XYBonds B, ∑ i : Fin d, (d : ℝ) * (Jseg i b.1) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro b hb
                    rw [Finset.mul_sum]
              _ = ∑ i : Fin d, ∑ b : XYBonds B, (d : ℝ) * (Jseg i b.1) ^ 2 :=
                    Finset.sum_comm
              _ = ∑ i : Fin d, (d : ℝ) * ∑ b : XYBonds B, (Jseg i b.1) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [Finset.mul_sum]
              _ = (d : ℝ) * ∑ i : Fin d,
                    xyDualDBondEnergy (d := d) (B := B) (Jseg i) := by
                    rw [Finset.mul_sum]
                    simp [xyDualDBondEnergy]
      _ ≤ (d : ℝ) * ∑ i : Fin d, (72 : ℝ) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum
              intro i hi
              exact (hJseg i).2.2
            · positivity
      _ = 72 * (d : ℝ) ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
        ring_nf
  have hflow := xyDualDEndpointResidualEnergy_le_of_bondFlow
    (d := d) (hd := hd) (B := B) x y Jtotal hJtotal hboundary
  exact hflow.trans henergy_total

end
end FroehlichSpencer.FS82.XY

end
