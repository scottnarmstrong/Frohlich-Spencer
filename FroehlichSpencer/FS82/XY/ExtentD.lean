/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.RelativeFillingD
public import FroehlichSpencer.FS82.Currents.ActivityLineage

/-!
# local relative fillings of currents of small extent, in every dimension

The dimension-generic form of `XY/Extent3.lean`.

A good lineage of the expansion, for a collision
relation that moves base points by at most one in every coordinate, has a connected set of active
cells, so the base points of its `L` cells differ by at most `L − 1` in every coordinate.

A
co-closed integer current whose base points have pairwise extent `D` with `D < B k` in every
direction touches at most one of the two boundary faces of each direction.

It therefore has a
relative filling that is supported within coordinate distance `D + 1` of any of its cells and is
bounded by its `ℓ¹` norm.

* `cellBase`: the base point of a dual cell; windows of cells are counted by `card_window_le`
  (at most `2 ^ d (R + R' + 1) ^ d` cells).
* `cellBaseNear`: base points at `ℓ^∞` distance at most one.
* `good_active_extent`: the extent of a good lineage.
* `exists_relativeFilling_of_extent`: the local relative filling.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents

variable {d : ℕ} {B : Box d}

/-! ## Base points -/

/-- The base point of a dual cell: `v + 1` at a dual vertex `v`, `u` at a dual interval `u`. -/
def cellBase (c : DualCell d B) (k : Fin d) : ℕ :=
  match c k with
  | Sum.inl v => v.val + 1
  | Sum.inr u => u.val

theorem cellCoordLower_bumpCell (c : DualCell d B) (k : Fin d) :
    cellCoordLower (bumpCell c) k = cellBase c k := by
  unfold cellCoordLower cellBase
  cases hc : c k with
  | inl v => simp [bumpCell_inl hc, coordBase]
  | inr u => simp [bumpCell_inr hc, coordBase]

theorem cellCoordUpper_bumpCell_le (c : DualCell d B) (k : Fin d) :
    cellCoordUpper (bumpCell c) k ≤ cellBase c k + 1 := by
  unfold cellCoordUpper
  have h := cellCoordLower_bumpCell c k
  unfold cellCoordLower at h
  rw [h]
  split_ifs <;> omega

theorem cellBase_le_cellCoordUpper (c : DualCell d B) (k : Fin d) :
    cellBase c k ≤ cellCoordUpper (bumpCell c) k := by
  rw [← cellCoordLower_bumpCell]
  unfold cellCoordLower cellCoordUpper
  omega

theorem cellBase_le (c : DualCell d B) (k : Fin d) : cellBase c k ≤ B k := by
  unfold cellBase
  cases hc : c k with
  | inl v => exact v.isLt
  | inr u => exact Nat.lt_succ_iff.mp u.isLt

theorem dualCell_ext_of_pattern_base {c c' : DualCell d B}
    (hp : ∀ k, (c k).isRight = (c' k).isRight) (hb : ∀ k, cellBase c k = cellBase c' k) :
    c = c' := by
  funext k
  have hpk := hp k
  have hbk := hb k
  unfold cellBase at hbk
  cases hc : c k with
  | inl v =>
    cases hc' : c' k with
    | inl w =>
      rw [hc, hc'] at hbk
      exact congrArg Sum.inl (Fin.ext (by simpa using hbk))
    | inr u => simp [hc, hc'] at hpk
  | inr u =>
    cases hc' : c' k with
    | inl w => simp [hc, hc'] at hpk
    | inr u' =>
      rw [hc, hc'] at hbk
      exact congrArg Sum.inr (Fin.ext hbk)

/-- The code of a dual cell in a window: its pattern of interval directions and its offsets. -/
noncomputable def windowCode (a : Fin d → ℕ) (R n : ℕ) (hn : 0 < n) (c : DualCell d B) :
    (Fin d → Bool) × (Fin d → Fin n) :=
  (fun k => (c k).isRight, fun k => ⟨(cellBase c k + R - a k) % n, Nat.mod_lt _ hn⟩)

open Classical in
/-- **Cells in a coordinate window.** -/
theorem card_window_le {α : Type*} [Fintype α] (f : α → DualCell d B)
    (hf : Function.Injective f) (a : Fin d → ℕ) (R R' : ℕ) :
    (Finset.univ.filter fun x : α =>
      ∀ k, a k ≤ cellBase (f x) k + R ∧ cellBase (f x) k ≤ a k + R').card ≤
      2 ^ d * (R + R' + 1) ^ d := by
  have hcard : Fintype.card ((Fin d → Bool) × (Fin d → Fin (R + R' + 1))) =
      2 ^ d * (R + R' + 1) ^ d := by
    simp [Fintype.card_prod]
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun x => windowCode a R (R + R' + 1) (Nat.succ_pos _) (f x))
    (fun _ _ => Finset.mem_univ _) ?_
  intro x hx x' hx' hcode
  have hwx := (Finset.mem_filter.mp hx).2
  have hwx' := (Finset.mem_filter.mp hx').2
  apply hf
  refine dualCell_ext_of_pattern_base (fun k => congrFun (congrArg Prod.fst hcode) k) fun k => ?_
  have hk := congrArg Fin.val (congrFun (congrArg Prod.snd hcode) k)
  simp only [windowCode] at hk
  have h1 := hwx k
  have h2 := hwx' k
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hk
  omega

/-! ## The extent of a good lineage -/

/-- Two dual cells are base-near when their base points differ by at most one in every
coordinate. Cells with a common face or a common coface are base-near. -/
def cellBaseNear (c c' : DualCell d B) : Prop :=
  ∀ k, cellBase c k ≤ cellBase c' k + 1 ∧ cellBase c' k ≤ cellBase c k + 1

theorem cellBaseNear_refl (c : DualCell d B) : cellBaseNear c c :=
  fun _ => ⟨Nat.le_succ _, Nat.le_succ _⟩

theorem cellBaseNear_symm {c c' : DualCell d B} (h : cellBaseNear c c') : cellBaseNear c' c :=
  fun k => ⟨(h k).2, (h k).1⟩

theorem good_active_extent {n : ℕ} {near : DualDForm B n → DualDForm B n → Prop}
    (hnear : ∀ e f, near e f → cellBaseNear e.1 f.1)
    {h : ActivityLineage (DualDForm B n)} (hg : ActivityLineage.Good near h) :
    ∀ e ∈ h.active, ∀ f ∈ h.active, ∀ k,
      cellBase e.1 k + 1 ≤ cellBase f.1 k + h.active.card := by
  induction hg with
  | leaf e =>
    intro e' he' f hf k
    simp only [ActivityLineage.active, Finset.mem_singleton] at he' hf
    subst he'
    subst hf
    simp [ActivityLineage.active]
  | @add l r hl hr hdisj hbridge ihl ihr
  | @sub l r hl hr hdisj hbridge ihl ihr =>
    have hactiveDisj : Disjoint l.active r.active := by
      apply Finset.disjoint_left.mpr
      intro e heL heR
      exact (Finset.disjoint_left.mp hdisj) (l.active_subset_all heL) (r.active_subset_all heR)
    have hcard : (l.active ∪ r.active).card = l.active.card + r.active.card :=
      Finset.card_union_of_disjoint hactiveDisj
    obtain ⟨u, hu, v, hv, huv⟩ := hbridge
    have hbase := hnear u v huv
    intro e he f hf k
    simp only [ActivityLineage.active, Finset.mem_union] at he hf ⊢
    rw [hcard]
    have hk := hbase k
    rcases he with heL | heR <;> rcases hf with hfL | hfR
    · have := ihl e heL f hfL k
      omega
    · have h1 := ihl e heL u hu k
      have h2 := ihr v hv f hfR k
      omega
    · have h1 := ihr e heR v hv k
      have h2 := ihl u hu f hfL k
      omega
    · have := ihr e heR f hfR k
      omega
  | @keepLeft l r hl hr hdisj hbridge ihl ihr =>
    simpa [ActivityLineage.active] using ihl
  | @keepRight l r hl hr hdisj hbridge ihl ihr =>
    simpa [ActivityLineage.active] using ihr

/-! ## The local relative filling -/

/-- **The local relative filling of a co-closed current of small extent.** -/
theorem exists_relativeFilling_of_extent (hd : 3 ≤ d) (J : DualDForm B (d - 2) → ℤ)
    (hJ : currentVector J ∈ coClosed (dualDExactOneComplex hd B)) (e₀ : DualDForm B (d - 2))
    (he₀ : J e₀ ≠ 0) (D : ℕ)
    (hext : ∀ e f, J e ≠ 0 → J f ≠ 0 → ∀ k, cellBase e.1 k ≤ cellBase f.1 k + D)
    (hD : ∀ k, D < B k) :
    ∃ F : DualDForm B (d - 1) → ℤ,
      (dualDExactOneComplex hd B).d₁.adjoint (WithLp.toLp 2 fun p => ((F p : ℤ) : ℝ)) =
        currentVector J ∧
      (∀ p, F p ≠ 0 → ∀ k, cellBase e₀.1 k ≤ cellBase p.1 k + D ∧
        cellBase p.1 k ≤ cellBase e₀.1 k + (D + 1)) ∧
      (∀ p, (F p).natAbs ≤ ∑ e : DualDForm B (d - 2), (J e).natAbs) := by
  classical
  let low : Fin d → Prop := fun k =>
    ∃ e : DualDForm B (d - 2), J e ≠ 0 ∧ ∃ u : Fin (B k + 1), e.1 k = Sum.inr u ∧ u.val = 0
  let high : Fin d → Prop := fun k =>
    ∃ e : DualDForm B (d - 2), J e ≠ 0 ∧ ∃ u : Fin (B k + 1), e.1 k = Sum.inr u ∧ u.val = B k
  have hbase_inr : ∀ (e : DualDForm B (d - 2)) (k : Fin d) (u : Fin (B k + 1)),
      e.1 k = Sum.inr u → cellBase e.1 k = u.val := by
    intro e k u hu
    simp only [cellBase, hu]
  let anchor : Anchor d (bumpedBoxD B) := fun k =>
    if low k then ⟨0, Nat.succ_pos _⟩
    else if high k then ⟨B k + 1, Nat.lt_succ_self _⟩
    else ⟨cellBase e₀.1 k, Nat.lt_succ_of_le (Nat.le_succ_of_le (cellBase_le e₀.1 k))⟩
  have hnotboth : ∀ k, high k → ¬ low k := by
    rintro k ⟨e, he, u, hu, huv⟩ ⟨e', he', u', hu', huv'⟩
    have h := hext e e' he he' k
    rw [hbase_inr e k u hu, hbase_inr e' k u' hu'] at h
    have := hD k
    omega
  have hanch : AnchorAtBoundary anchor J := by
    intro e he i u hu
    constructor
    · intro h0
      have hlow : low i := ⟨e, he, u, hu, h0⟩
      simp only [anchor, hlow, ↓reduceIte]
    · intro hB
      have hhigh : high i := ⟨e, he, u, hu, hB⟩
      have hnl := hnotboth i hhigh
      simp only [anchor, hnl, hhigh, ↓reduceIte]
  let lo : Fin d → ℕ := fun k => cellBase e₀.1 k - D
  let hi : Fin d → ℕ := fun k => cellBase e₀.1 k + (D + 1)
  have hrect : ∀ e : DualDForm B (d - 2), J e ≠ 0 → ∀ i,
      lo i ≤ cellCoordLower (bumpCell e.1) i ∧ cellCoordUpper (bumpCell e.1) i ≤ hi i := by
    intro e he i
    have h1 := hext e₀ e he₀ he i
    have h2 := hext e e₀ he he₀ i
    have h3 := cellCoordUpper_bumpCell_le e.1 i
    rw [cellCoordLower_bumpCell]
    simp only [lo, hi]
    omega
  have hanchor : ∀ j, lo j ≤ (anchor j).val ∧ (anchor j).val ≤ hi j := by
    intro j
    have hle := cellBase_le e₀.1 j
    by_cases hl : low j
    · obtain ⟨e, he, u, hu, hu0⟩ := hl
      have h := hext e₀ e he₀ he j
      rw [hbase_inr e j u hu] at h
      have hl' : low j := ⟨e, he, u, hu, hu0⟩
      simp only [anchor, lo, hi, hl', ↓reduceIte]
      omega
    · by_cases hh : high j
      · obtain ⟨e, he, u, hu, huB⟩ := hh
        have h := hext e e₀ he he₀ j
        rw [hbase_inr e j u hu] at h
        have hh' : high j := ⟨e, he, u, hu, huB⟩
        simp only [anchor, lo, hi, hl, hh', ↓reduceIte]
        omega
      · simp only [anchor, lo, hi, hl, hh, ↓reduceIte]
        omega
  refine ⟨relativeFilling anchor J, relativeFilling_spec hd anchor J hJ hanch, ?_,
    relativeFilling_natAbs_le anchor J⟩
  intro p hp k
  have h := relativeFilling_support anchor J lo hi hrect hanchor hp k
  rw [cellCoordLower_bumpCell] at h
  have h2 := cellBase_le_cellCoordUpper p.1 k
  simp only [lo, hi] at h
  omega

end FroehlichSpencer.FS82.XY.DualD

end
