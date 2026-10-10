/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.XYCurrent
public import FroehlichSpencer.BKT.Bridge.SquareCarriers
import Mathlib.Algebra.BigOperators.Fin

/-!
# Integer cohomology of the periodic square torus

This module constructs and uniquely identifies the two winding numbers and pinned dual height of
an integer divergence-free torus current. It also fixes a coordinate path current for a two-point
source and proves the corresponding affine decomposition.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Lattice2D

namespace FroehlichSpencer.BKT.Rotator.Periodic

private theorem sum_torusEdge {L : ℕ} [NeZero L] (f : TorusEdge L → ℤ) :
    (∑ e : TorusEdge L, f e) = ∑ p : TorusVertex L, (f (p, true) + f (p, false)) := by
  calc
    _ = ∑ p : TorusVertex L, ∑ d : Bool, f (p, d) := Fintype.sum_prod_type f
    _ = _ := by simp only [Fintype.sum_bool]

private theorem step_eq_prev {L : ℕ} [NeZero L] (d : Bool) (p v : TorusVertex L) :
    torusStep L d p = v ↔ p = if d then (v.1, v.2 - 1) else (v.1 - 1, v.2) := by
  cases d
  · change (p.1 + 1, p.2) = v ↔ p = (v.1 - 1, v.2)
    constructor
    · intro h
      rcases Prod.mk.inj h with ⟨h₁, h₂⟩
      ext
      · calc p.1 = p.1 + 1 - 1 := by abel
          _ = v.1 - 1 := by rw [h₁]
      · exact h₂
    · intro h
      have h₁ : p.1 = v.1 - 1 := by simpa using congrArg Prod.fst h
      have h₂ : p.2 = v.2 := by simpa using congrArg Prod.snd h
      ext
      · calc p.1 + 1 = (v.1 - 1) + 1 := by rw [h₁]
          _ = v.1 := sub_add_cancel _ _
      · exact h₂
  · change (p.1, p.2 + 1) = v ↔ p = (v.1, v.2 - 1)
    constructor
    · intro h
      rcases Prod.mk.inj h with ⟨h₁, h₂⟩
      ext
      · exact h₁
      · calc p.2 = p.2 + 1 - 1 := by abel
          _ = v.2 - 1 := by rw [h₂]
    · intro h
      have h₁ : p.1 = v.1 := by simpa using congrArg Prod.fst h
      have h₂ : p.2 = v.2 - 1 := by simpa using congrArg Prod.snd h
      ext
      · exact h₁
      · calc p.2 + 1 = (v.2 - 1) + 1 := by rw [h₂]
          _ = v.2 := sub_add_cancel _ _

theorem torusCurrentDivergence_formula {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) q v =
      q (v, false) + q (v, true) - q ((v.1 - 1, v.2), false) - q ((v.1, v.2 - 1), true) := by
  classical
  unfold currentDivergence
  have hout : (∑ e : TorusEdge L, if (torusGraph L hL).src e = v then q e else 0) =
      q (v, true) + q (v, false) := by
    change (∑ e : TorusEdge L, if e.1 = v then q e else 0) = _
    rw [sum_torusEdge, Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_ite_eq']
  have hin : (∑ e : TorusEdge L, if (torusGraph L hL).tgt e = v then q e else 0) =
      q ((v.1 - 1, v.2), false) + q ((v.1, v.2 - 1), true) := by
    change (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then q e else 0) = _
    rw [sum_torusEdge]
    simp_rw [step_eq_prev]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_ite_eq']
    ring
  rw [hout, hin]
  ring


/-- The dual height coboundary as an integer current on positively oriented torus edges. -/
def torusDualGradient {L : ℕ} [NeZero L] (h : TorusVertex L → ℤ) : TorusEdge L → ℤ
  | (p, false) => h p - h (p.1, p.2 - 1)
  | (p, true) => h (p.1 - 1, p.2) - h p

/-- A pair of integer period representatives, supported on the two fundamental cuts. -/
def torusHarmonicCurrent {L : ℕ} [NeZero L] (w : ℤ × ℤ) : TorusEdge L → ℤ
  | (p, false) => if p.2 = 0 then w.1 else 0
  | (p, true) => if p.1 = 0 then w.2 else 0

/-- The horizontal fundamental period of an oriented torus current. -/
def torusWindingX {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ) : ℤ :=
  ∑ y : ZMod L, q ((0, y), false)

/-- The vertical fundamental period of an oriented torus current. -/
def torusWindingY {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ) : ℤ :=
  ∑ x : ZMod L, q ((x, 0), true)


/-- The horizontal cycle sum at a fixed first coordinate. -/
def torusHorizontalPeriod {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ) (x : ZMod L) : ℤ :=
  ∑ y : ZMod L, q ((x, y), false)

/-- The vertical cycle sum at a fixed second coordinate. -/
def torusVerticalPeriod {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ) (y : ZMod L) : ℤ :=
  ∑ x : ZMod L, q ((x, y), true)

private theorem sum_shift_prev {L : ℕ} [NeZero L] (f : ZMod L → ℤ) :
    (∑ x : ZMod L, f (x - 1)) = ∑ x : ZMod L, f x := by
  simpa [sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L)) f)

private theorem sum_shift_next {L : ℕ} [NeZero L] (f : ZMod L → ℤ) :
    (∑ x : ZMod L, f (x + 1)) = ∑ x : ZMod L, f x := by
  simpa using (Equiv.sum_comp (Equiv.addRight (1 : ZMod L)) f)

theorem torusHorizontalPeriod_succ {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (x : ZMod L)
    (hdiv : ∀ v, currentDivergence (torusGraph L hL) q v = 0) :
    torusHorizontalPeriod q (x + 1) = torusHorizontalPeriod q x := by
  have hpoint (y : ZMod L) :
      q ((x + 1, y), false) - q ((x, y), false) =
        q ((x + 1, y - 1), true) - q ((x + 1, y), true) := by
    have h := hdiv (x + 1, y)
    rw [torusCurrentDivergence_formula, add_sub_cancel_right] at h
    linarith
  have hsum :
      (∑ y : ZMod L, (q ((x + 1, y), false) - q ((x, y), false))) =
      ∑ y : ZMod L, (q ((x + 1, y - 1), true) - q ((x + 1, y), true)) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hpoint y
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  have hshift : (∑ y : ZMod L, q ((x + 1, y - 1), true)) =
      ∑ y : ZMod L, q ((x + 1, y), true) := by
    exact sum_shift_prev (fun y => q ((x + 1, y), true))
  rw [hshift] at hsum
  unfold torusHorizontalPeriod
  linarith

theorem torusVerticalPeriod_succ {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (y : ZMod L)
    (hdiv : ∀ v, currentDivergence (torusGraph L hL) q v = 0) :
    torusVerticalPeriod q (y + 1) = torusVerticalPeriod q y := by
  have hpoint (x : ZMod L) :
      q ((x, y + 1), true) - q ((x, y), true) =
        q ((x - 1, y + 1), false) - q ((x, y + 1), false) := by
    have h := hdiv (x, y + 1)
    rw [torusCurrentDivergence_formula, add_sub_cancel_right] at h
    linarith
  have hsum :
      (∑ x : ZMod L, (q ((x, y + 1), true) - q ((x, y), true))) =
      ∑ x : ZMod L, (q ((x - 1, y + 1), false) - q ((x, y + 1), false)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hpoint x
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  have hshift : (∑ x : ZMod L, q ((x - 1, y + 1), false)) =
      ∑ x : ZMod L, q ((x, y + 1), false) := by
    exact sum_shift_prev (fun x => q ((x, y + 1), false))
  rw [hshift] at hsum
  unfold torusVerticalPeriod
  linarith

private theorem torusHorizontalPeriod_const {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (x : ZMod L)
    (hdiv : ∀ v, currentDivergence (torusGraph L hL) q v = 0) :
    torusHorizontalPeriod q x = torusHorizontalPeriod q 0 := by
  have hnat : ∀ n : ℕ,
      torusHorizontalPeriod q (n : ZMod L) = torusHorizontalPeriod q 0 := by
    intro n
    induction n with
    | zero => simp [torusHorizontalPeriod]
    | succ n ih =>
      rw [Nat.cast_succ, torusHorizontalPeriod_succ hL q (n : ZMod L) hdiv, ih]
  simpa [torusHorizontalPeriod, ZMod.natCast_zmod_val] using hnat x.val

private theorem torusVerticalPeriod_const {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (y : ZMod L)
    (hdiv : ∀ v, currentDivergence (torusGraph L hL) q v = 0) :
    torusVerticalPeriod q y = torusVerticalPeriod q 0 := by
  have hnat : ∀ n : ℕ,
      torusVerticalPeriod q (n : ZMod L) = torusVerticalPeriod q 0 := by
    intro n
    induction n with
    | zero => simp [torusVerticalPeriod]
    | succ n ih =>
      rw [Nat.cast_succ, torusVerticalPeriod_succ hL q (n : ZMod L) hdiv, ih]
  simpa [torusVerticalPeriod, ZMod.natCast_zmod_val] using hnat y.val


/-- The current sum along the first `n` positive horizontal steps. -/
def torusHorizontalPathSum {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ)
    (x : ZMod L) (n : ℕ) : ℤ :=
  ∑ k : Fin n, (q ((x, ((k.val + 1 : ℕ) : ZMod L)), false))

/-- The current sum along the first `n` positive vertical steps. -/
def torusVerticalPathSum {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ)
    (n : ℕ) (y : ZMod L) : ℤ :=
  ∑ k : Fin n, (q ((((k.val + 1 : ℕ) : ZMod L), y), true))

/-- The pinned integer height obtained by integrating a zero-period cycle along coordinate paths. -/
def torusPathHeight {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ) (p : TorusVertex L) : ℤ :=
  torusHorizontalPathSum q 0 p.2.val - torusVerticalPathSum q p.1.val p.2

theorem torusPathHeight_root {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ) :
    torusPathHeight q (0, 0) = 0 := by
  simp [torusPathHeight, torusHorizontalPathSum, torusVerticalPathSum]

private theorem zmod_one_val {L : ℕ} [NeZero L] (hL : 2 < L) :
    (1 : ZMod L).val = 1 := by
  exact @ZMod.val_one L ⟨by omega⟩

theorem torusVerticalPathSum_succ {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ)
    (n : ℕ) (j : ZMod L) :
    torusVerticalPathSum q (n + 1) j = torusVerticalPathSum q n j +
      q ((((n + 1 : ℕ) : ZMod L), j), true) := by
  simp [torusVerticalPathSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem torusHorizontalPathSum_succ {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ)
    (i : ZMod L) (n : ℕ) :
    torusHorizontalPathSum q i (n + 1) = torusHorizontalPathSum q i n +
      q ((i, ((n + 1 : ℕ) : ZMod L)), false) := by
  simp [torusHorizontalPathSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem torusPathHeight_vertical_nonzero {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (i j : ZMod L) (hi : 0 < i.val) :
    torusPathHeight q (i - 1, j) - torusPathHeight q (i, j) = q ((i, j), true) := by
  have hval : (i - 1).val = i.val - 1 := by
    rw [ZMod.val_sub (by rw [zmod_one_val hL]; omega), zmod_one_val hL]
  have hsucc : i.val - 1 + 1 = i.val := Nat.sub_add_cancel (by omega)
  have hcast : ((i.val - 1 + 1 : ℕ) : ZMod L) = i := by
    rw [hsucc]
    exact ZMod.natCast_zmod_val i
  have hsum : torusVerticalPathSum q i.val j =
      torusVerticalPathSum q (i.val - 1) j + q ((i, j), true) := by
    calc
      torusVerticalPathSum q i.val j = torusVerticalPathSum q (i.val - 1 + 1) j := by rw [hsucc]
      _ = torusVerticalPathSum q (i.val - 1) j + q (((i.val - 1 + 1 : ℕ), j), true) :=
        torusVerticalPathSum_succ q (i.val - 1) j
      _ = _ := by rw [hcast]
  unfold torusPathHeight
  rw [hval, hsum]
  ring

theorem torusPathHeight_horizontal_base_nonzero {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (j : ZMod L) (hj : 0 < j.val) :
    torusPathHeight q (0, j) - torusPathHeight q (0, j - 1) = q ((0, j), false) := by
  have hval : (j - 1).val = j.val - 1 := by
    rw [ZMod.val_sub (by rw [zmod_one_val hL]; omega), zmod_one_val hL]
  have hsucc : j.val - 1 + 1 = j.val := Nat.sub_add_cancel (by omega)
  have hcast : ((j.val - 1 + 1 : ℕ) : ZMod L) = j := by
    rw [hsucc]
    exact ZMod.natCast_zmod_val j
  have hsum : torusHorizontalPathSum q 0 j.val =
      torusHorizontalPathSum q 0 (j.val - 1) + q ((0, j), false) := by
    calc
      torusHorizontalPathSum q 0 j.val = torusHorizontalPathSum q 0 (j.val - 1 + 1) := by rw [hsucc]
      _ = torusHorizontalPathSum q 0 (j.val - 1) +
          q ((0, (j.val - 1 + 1 : ℕ)), false) := torusHorizontalPathSum_succ q 0 (j.val - 1)
      _ = _ := by rw [hcast]
  have hz1 : torusVerticalPathSum q 0 j = 0 := by simp [torusVerticalPathSum]
  have hz2 : torusVerticalPathSum q 0 (j - 1) = 0 := by simp [torusVerticalPathSum]
  simp only [torusPathHeight, ZMod.val_zero]
  rw [hval, hsum, hz1, hz2]
  ring

private theorem finEquiv_succ_cast {n : ℕ} (i : Fin n) :
    ZMod.finEquiv (n + 1) i.succ = ((i.val + 1 : ℕ) : ZMod (n + 1)) := by
  have hv : (ZMod.finEquiv (n + 1) i.succ).val = i.val + 1 := by
    change i.succ.val = i.val + 1
    exact Fin.val_succ i
  calc
    ZMod.finEquiv (n + 1) i.succ =
        ((ZMod.finEquiv (n + 1) i.succ).val : ZMod (n + 1)) :=
      (ZMod.natCast_zmod_val _).symm
    _ = ((i.val + 1 : ℕ) : ZMod (n + 1)) := by rw [hv]

theorem torusHorizontalPeriod_eq_root_add_path {L : ℕ} [NeZero L]
    (q : TorusEdge L → ℤ) (x : ZMod L) :
    torusHorizontalPeriod q x = q ((x, 0), false) + torusHorizontalPathSum q x (L - 1) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hsum : torusHorizontalPeriod (L := n + 1) q x =
        ∑ i : Fin (n + 1), q ((x, ZMod.finEquiv (n + 1) i), false) := by
      unfold torusHorizontalPeriod
      exact (Equiv.sum_comp (ZMod.finEquiv (n + 1)).toEquiv
        (fun y => q ((x, y), false))).symm
    have hroot : ZMod.finEquiv (n + 1) (0 : Fin (n + 1)) = 0 := rfl
    have htail :
        (∑ i : Fin n, q ((x, ZMod.finEquiv (n + 1) i.succ), false)) =
          torusHorizontalPathSum q x n := by
      unfold torusHorizontalPathSum
      apply Finset.sum_congr rfl
      intro i hi
      rw [finEquiv_succ_cast]
    calc
      torusHorizontalPeriod q x =
          q ((x, ZMod.finEquiv (n + 1) 0), false) +
            ∑ i : Fin n, q ((x, ZMod.finEquiv (n + 1) i.succ), false) := by
        rw [hsum, Fin.sum_univ_succ]
      _ = q ((x, 0), false) + torusHorizontalPathSum q x n := by rw [hroot, htail]
      _ = _ := by simp

theorem torusVerticalPeriod_eq_root_add_path {L : ℕ} [NeZero L]
    (q : TorusEdge L → ℤ) (y : ZMod L) :
    torusVerticalPeriod q y = q ((0, y), true) + torusVerticalPathSum q (L - 1) y := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hsum : torusVerticalPeriod (L := n + 1) q y =
        ∑ i : Fin (n + 1), q ((ZMod.finEquiv (n + 1) i, y), true) := by
      unfold torusVerticalPeriod
      exact (Equiv.sum_comp (ZMod.finEquiv (n + 1)).toEquiv
        (fun x => q ((x, y), true))).symm
    have hroot : ZMod.finEquiv (n + 1) (0 : Fin (n + 1)) = 0 := rfl
    have htail :
        (∑ i : Fin n, q ((ZMod.finEquiv (n + 1) i.succ, y), true)) =
          torusVerticalPathSum q n y := by
      unfold torusVerticalPathSum
      apply Finset.sum_congr rfl
      intro i hi
      rw [finEquiv_succ_cast]
    calc
      torusVerticalPeriod q y =
          q ((ZMod.finEquiv (n + 1) 0, y), true) +
            ∑ i : Fin n, q ((ZMod.finEquiv (n + 1) i.succ, y), true) := by
        rw [hsum, Fin.sum_univ_succ]
      _ = q ((0, y), true) + torusVerticalPathSum q n y := by rw [hroot, htail]
      _ = _ := by simp

theorem torusPathHeight_horizontal_base_zero {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (hperiod : torusHorizontalPeriod q 0 = 0) :
    torusPathHeight q (0, 0) - torusPathHeight q (0, -1) = q ((0, 0), false) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hper := torusHorizontalPeriod_eq_root_add_path (L := n + 1) q 0
    have hper' : 0 = q ((0, 0), false) + torusHorizontalPathSum q 0 n := by
      simpa using hperiod.symm.trans hper
    have hpath : torusPathHeight q (0, -1) = torusHorizontalPathSum q 0 n := by
      simp [torusPathHeight, torusVerticalPathSum, ZMod.val_neg_one]
    rw [torusPathHeight_root, hpath]
    linarith

theorem torusPathHeight_vertical_base_zero {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (j : ZMod L) (hperiod : torusVerticalPeriod q j = 0) :
    torusPathHeight q (-1, j) - torusPathHeight q (0, j) = q ((0, j), true) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hper := torusVerticalPeriod_eq_root_add_path (L := n + 1) q j
    have hper' : 0 = q ((0, j), true) + torusVerticalPathSum q n j := by
      simpa using hperiod.symm.trans hper
    have hleft : torusPathHeight q (-1, j) =
        torusHorizontalPathSum q 0 j.val - torusVerticalPathSum q n j := by
      simp [torusPathHeight, ZMod.val_neg_one]
    have hright : torusPathHeight q (0, j) = torusHorizontalPathSum q 0 j.val := by
      simp [torusPathHeight, torusVerticalPathSum]
    rw [hleft, hright]
    linarith

private theorem torusPathHeight_vertical_current {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (i j : ZMod L) (hperiod : torusVerticalPeriod q j = 0) :
    torusPathHeight q (i - 1, j) - torusPathHeight q (i, j) = q ((i, j), true) := by
  by_cases hi : i = 0
  · subst i
    simpa using torusPathHeight_vertical_base_zero hL q j hperiod
  · exact torusPathHeight_vertical_nonzero hL q i j (ZMod.val_pos.mpr hi)

private theorem torusPathHeight_horizontal_current {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (i j : ZMod L)
    (hdiv : ∀ v, currentDivergence (torusGraph L hL) q v = 0)
    (hperiod : torusHorizontalPeriod q 0 = 0)
    (hperiodV : ∀ y, torusVerticalPeriod q y = 0) :
    q ((i, j), false) = torusPathHeight q (i, j) - torusPathHeight q (i, j - 1) := by
  have hbase (y : ZMod L) :
      q ((0, y), false) = torusPathHeight q (0, y) - torusPathHeight q (0, y - 1) := by
    by_cases hy : y = 0
    · subst y
      simpa using (torusPathHeight_horizontal_base_zero hL q hperiod).symm
    · exact (torusPathHeight_horizontal_base_nonzero hL q y (ZMod.val_pos.mpr hy)).symm
  have hnat : ∀ k : ℕ, k < L → ∀ y : ZMod L,
      q ((((k : ℕ) : ZMod L), y), false) =
        torusPathHeight q (((k : ℕ) : ZMod L), y) -
          torusPathHeight q (((k : ℕ) : ZMod L), y - 1) := by
    intro k
    induction k with
    | zero =>
      intro hk y
      simpa using hbase y
    | succ k ih =>
      intro hk y
      have hk' : k < L := by omega
      have hprev := ih hk' y
      let x : ZMod L := ((k + 1 : ℕ) : ZMod L)
      have hcoord : x - 1 = (k : ℕ) := by
        dsimp [x]
        rw [Nat.cast_succ]
        abel
      have hdivx := hdiv (x, y)
      rw [torusCurrentDivergence_formula, hcoord] at hdivx
      have hv := torusPathHeight_vertical_current hL q x y (hperiodV y)
      have hv' := torusPathHeight_vertical_current hL q x (y - 1) (hperiodV (y - 1))
      rw [hcoord] at hv hv'
      have hnew : q ((x, y), false) =
          torusPathHeight q (x, y) - torusPathHeight q (x, y - 1) := by
        linarith
      simpa [x] using hnew
  have hresult := hnat i.val i.val_lt j
  rw [ZMod.natCast_zmod_val i] at hresult
  exact hresult

theorem torusPathHeight_eq_torusDualGradient_of_cycle_zeroPeriods {L : ℕ} [NeZero L]
    (hL : 2 < L) (q : TorusEdge L → ℤ)
    (hdiv : ∀ v, currentDivergence (torusGraph L hL) q v = 0)
    (hwindX : torusWindingX q = 0) (hwindY : torusWindingY q = 0) :
    q = torusDualGradient (torusPathHeight q) := by
  have hperiodX : torusHorizontalPeriod q 0 = 0 := by
    simpa [torusHorizontalPeriod, torusWindingX] using hwindX
  have hperiodY : torusVerticalPeriod q 0 = 0 := by
    simpa [torusVerticalPeriod, torusWindingY] using hwindY
  have hperiodV : ∀ y, torusVerticalPeriod q y = 0 := by
    intro y
    rw [torusVerticalPeriod_const hL q y hdiv]
    exact hperiodY
  funext e
  rcases e with ⟨p, d⟩
  cases d
  · exact torusPathHeight_horizontal_current hL q p.1 p.2 hdiv hperiodX hperiodV
  · simpa [torusDualGradient] using
      (torusPathHeight_vertical_current hL q p.1 p.2 (hperiodV p.2)).symm

private theorem torusDualGradient_injective_pinned {L : ℕ} [NeZero L] (_hL : 2 < L)
    (f g : TorusVertex L → ℤ) (hf : f (0, 0) = 0) (hg : g (0, 0) = 0)
    (hfg : torusDualGradient f = torusDualGradient g) : f = g := by
  have hleft (x y : ZMod L) :
      f (x - 1, y) - g (x - 1, y) = f (x, y) - g (x, y) := by
    have h := congrFun hfg ((x, y), true)
    change f (x - 1, y) - f (x, y) = g (x - 1, y) - g (x, y) at h
    linarith
  have hdown (x y : ZMod L) :
      f (x, y - 1) - g (x, y - 1) = f (x, y) - g (x, y) := by
    have h := congrFun hfg ((x, y), false)
    change f (x, y) - f (x, y - 1) = g (x, y) - g (x, y - 1) at h
    linarith
  have hx : ∀ k : ℕ, k < L → ∀ y : ZMod L,
      f ((k : ℕ), y) - g ((k : ℕ), y) = f (0, y) - g (0, y) := by
    intro k
    induction k with
    | zero => intro hk y; simp
    | succ k ih =>
      intro hk y
      have hk' : k < L := by omega
      let x : ZMod L := ((k + 1 : ℕ) : ZMod L)
      have hcoord : x - 1 = (k : ℕ) := by
        dsimp [x]
        rw [Nat.cast_succ]
        abel
      have h := hleft x y
      rw [hcoord] at h
      calc
        f ((k + 1 : ℕ), y) - g ((k + 1 : ℕ), y) =
            f ((k : ℕ), y) - g ((k : ℕ), y) := by simpa [x] using h.symm
        _ = f (0, y) - g (0, y) := ih hk' y
  have hxy (x y : ZMod L) : f (x, y) - g (x, y) = f (0, 0) - g (0, 0) := by
    have hx' := hx x.val x.val_lt y
    rw [ZMod.natCast_zmod_val x] at hx'
    have hy : ∀ k : ℕ, k < L →
        f (0, ((k : ℕ) : ZMod L)) - g (0, ((k : ℕ) : ZMod L)) =
          f (0, 0) - g (0, 0) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hk' : k < L := by omega
        let y := ((k + 1 : ℕ) : ZMod L)
        have hcoord : y - 1 = (k : ℕ) := by
          dsimp [y]
          rw [Nat.cast_succ]
          abel
        have h := hdown 0 y
        rw [hcoord] at h
        calc
          f (0, (k + 1 : ℕ)) - g (0, (k + 1 : ℕ)) =
              f (0, (k : ℕ)) - g (0, (k : ℕ)) := by simpa [y] using h.symm
          _ = f (0, 0) - g (0, 0) := ih hk'
    have hy' := hy y.val y.val_lt
    rw [ZMod.natCast_zmod_val y] at hy'
    calc
      f (x, y) - g (x, y) = f (0, y) - g (0, y) := hx'
      _ = f (0, 0) - g (0, 0) := hy'
  funext p
  have hp := hxy p.1 p.2
  rw [hf, hg, sub_self] at hp
  linarith

theorem torusDualGradient_divergence_zero {L : ℕ} [NeZero L] (hL : 2 < L)
    (h : TorusVertex L → ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (torusDualGradient h) v = 0 := by
  rw [torusCurrentDivergence_formula]
  simp only [torusDualGradient]
  ring

theorem torusHarmonicCurrent_divergence_zero {L : ℕ} [NeZero L] (hL : 2 < L)
    (w : ℤ × ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (torusHarmonicCurrent w) v = 0 := by
  rw [torusCurrentDivergence_formula]
  simp only [torusHarmonicCurrent]
  ring

private theorem sum_sub_prev_zero {L : ℕ} [NeZero L] (f : ZMod L → ℤ) :
    (∑ x : ZMod L, f x) - ∑ x : ZMod L, f (x - 1) = 0 := by
  have hshift : (∑ x : ZMod L, f (x - 1)) = ∑ x : ZMod L, f x := by
    simpa [sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L)) f)
  rw [hshift]
  ring

private theorem sum_sub_next_zero {L : ℕ} [NeZero L] (f : ZMod L → ℤ) :
    (∑ x : ZMod L, f x) - ∑ x : ZMod L, f (x + 1) = 0 := by
  have hshift : (∑ x : ZMod L, f (x + 1)) = ∑ x : ZMod L, f x := by
    simpa using (Equiv.sum_comp (Equiv.addRight (1 : ZMod L)) f)
  rw [hshift]
  ring

theorem torusDualGradient_torusWindingX_zero {L : ℕ} [NeZero L] (h : TorusVertex L → ℤ) :
    torusWindingX (torusDualGradient h) = 0 := by
  unfold torusWindingX
  simp only [torusDualGradient]
  rw [Finset.sum_sub_distrib]
  exact sum_sub_prev_zero (fun y => h (0, y))

theorem torusDualGradient_torusWindingY_zero {L : ℕ} [NeZero L] (h : TorusVertex L → ℤ) :
    torusWindingY (torusDualGradient h) = 0 := by
  unfold torusWindingY
  simp only [torusDualGradient]
  rw [Finset.sum_sub_distrib]
  have h := sum_sub_prev_zero (fun x => h (x, 0))
  linarith

theorem torusHarmonicCurrent_torusWindingX {L : ℕ} [NeZero L] (w : ℤ × ℤ) :
    torusWindingX (L := L) (torusHarmonicCurrent (L := L) w) = w.1 := by
  classical
  simp [torusWindingX, torusHarmonicCurrent]

theorem torusHarmonicCurrent_torusWindingY {L : ℕ} [NeZero L] (w : ℤ × ℤ) :
    torusWindingY (L := L) (torusHarmonicCurrent (L := L) w) = w.2 := by
  classical
  simp [torusWindingY, torusHarmonicCurrent]


private theorem torusWindingX_add {L : ℕ} [NeZero L] (q r : TorusEdge L → ℤ) :
    torusWindingX (q + r) = torusWindingX q + torusWindingX r := by
  simp [torusWindingX, Finset.sum_add_distrib]

private theorem torusWindingY_add {L : ℕ} [NeZero L] (q r : TorusEdge L → ℤ) :
    torusWindingY (q + r) = torusWindingY q + torusWindingY r := by
  simp [torusWindingY, Finset.sum_add_distrib]

private theorem torusWindingX_neg {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ) :
    torusWindingX (-q) = - torusWindingX q := by
  simp [torusWindingX]

private theorem torusWindingY_neg {L : ℕ} [NeZero L] (q : TorusEdge L → ℤ) :
    torusWindingY (-q) = - torusWindingY q := by
  simp [torusWindingY]

private theorem torusWindingX_sub {L : ℕ} [NeZero L] (q r : TorusEdge L → ℤ) :
    torusWindingX (q - r) = torusWindingX q - torusWindingX r := by
  simp [sub_eq_add_neg, torusWindingX_add, torusWindingX_neg]

private theorem torusWindingY_sub {L : ℕ} [NeZero L] (q r : TorusEdge L → ℤ) :
    torusWindingY (q - r) = torusWindingY q - torusWindingY r := by
  simp [sub_eq_add_neg, torusWindingY_add, torusWindingY_neg]

private theorem divergence_sub_zero {L : ℕ} [NeZero L] (hL : 2 < L)
    (q r : TorusEdge L → ℤ) (v : TorusVertex L)
    (hq : currentDivergence (torusGraph L hL) q v = 0)
    (hr : currentDivergence (torusGraph L hL) r v = 0) :
    currentDivergence (torusGraph L hL) (q - r) v = 0 := by
  have hq' := hq
  have hr' := hr
  rw [torusCurrentDivergence_formula] at hq'
  rw [torusCurrentDivergence_formula] at hr'
  rw [torusCurrentDivergence_formula]
  simp only [Pi.sub_apply]
  linear_combination hq' - hr'

/-- Every divergence-free torus current is a pinned height gradient plus its two cut-period representatives. -/
theorem torusCycle_decomposition_exists {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ)
    (hdiv : ∀ v, currentDivergence (torusGraph L hL) q v = 0) :
    ∃ h : TorusVertex L → ℤ, ∃ w : ℤ × ℤ,
      h (0, 0) = 0 ∧ q = torusDualGradient h + torusHarmonicCurrent w := by
  let w : ℤ × ℤ := (torusWindingX q, torusWindingY q)
  let r : TorusEdge L → ℤ := q - torusHarmonicCurrent w
  have hdivr : ∀ v, currentDivergence (torusGraph L hL) r v = 0 := by
    intro v
    apply divergence_sub_zero hL q (torusHarmonicCurrent w) v (hdiv v)
    exact torusHarmonicCurrent_divergence_zero hL w v
  have hwindx : torusWindingX r = 0 := by
    dsimp [r, w]
    rw [torusWindingX_sub, torusHarmonicCurrent_torusWindingX]
    ring
  have hwindy : torusWindingY r = 0 := by
    dsimp [r, w]
    rw [torusWindingY_sub, torusHarmonicCurrent_torusWindingY]
    ring
  refine ⟨torusPathHeight r, w, ?_, ?_⟩
  · exact torusPathHeight_root r
  · have hr := torusPathHeight_eq_torusDualGradient_of_cycle_zeroPeriods hL r hdivr hwindx hwindy
    have hdecomp : r = torusDualGradient (torusPathHeight r) := hr
    funext e
    have he := congrFun hdecomp e
    have he' : q e - torusHarmonicCurrent w e = torusDualGradient (torusPathHeight r) e := by
      simpa [r] using he
    change q e = torusDualGradient (torusPathHeight r) e + torusHarmonicCurrent w e
    omega


/-- The pinned height and integer winding pair in a torus cycle decomposition are unique. -/
theorem torusCycle_decomposition_unique {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (h₁ h₂ : TorusVertex L → ℤ) (w₁ w₂ : ℤ × ℤ)
    (hh₁ : h₁ (0, 0) = 0) (hh₂ : h₂ (0, 0) = 0)
    (hq₁ : q = torusDualGradient h₁ + torusHarmonicCurrent w₁)
    (hq₂ : q = torusDualGradient h₂ + torusHarmonicCurrent w₂) :
    h₁ = h₂ ∧ w₁ = w₂ := by
  have hwx₁ : torusWindingX q = w₁.1 := by
    rw [hq₁, torusWindingX_add, torusDualGradient_torusWindingX_zero, torusHarmonicCurrent_torusWindingX]
    ring
  have hwx₂ : torusWindingX q = w₂.1 := by
    rw [hq₂, torusWindingX_add, torusDualGradient_torusWindingX_zero, torusHarmonicCurrent_torusWindingX]
    ring
  have hwy₁ : torusWindingY q = w₁.2 := by
    rw [hq₁, torusWindingY_add, torusDualGradient_torusWindingY_zero, torusHarmonicCurrent_torusWindingY]
    ring
  have hwy₂ : torusWindingY q = w₂.2 := by
    rw [hq₂, torusWindingY_add, torusDualGradient_torusWindingY_zero, torusHarmonicCurrent_torusWindingY]
    ring
  have hwind : w₁ = w₂ := by
    apply Prod.ext <;> omega
  subst w₂
  have hgrad : torusDualGradient h₁ = torusDualGradient h₂ := by
    funext e
    have he₁ := congrFun hq₁ e
    have he₂ := congrFun hq₂ e
    change q e = torusDualGradient h₁ e + torusHarmonicCurrent w₁ e at he₁
    change q e = torusDualGradient h₂ e + torusHarmonicCurrent w₁ e at he₂
    omega
  exact ⟨torusDualGradient_injective_pinned hL h₁ h₂ hh₁ hh₂ hgrad, rfl⟩

/-- A current with marked divergence is its fixed path current plus a unique cycle sector. -/
theorem torusSourceCycle_decomposition_exists {L : ℕ} [NeZero L] (hL : 2 < L)
    (q γ : TorusEdge L → ℤ) (χ : TorusVertex L → ℤ)
    (hq : ∀ v, currentDivergence (torusGraph L hL) q v = χ v)
    (hγ : ∀ v, currentDivergence (torusGraph L hL) γ v = χ v) :
    ∃ h : TorusVertex L → ℤ, ∃ w : ℤ × ℤ,
      h (0, 0) = 0 ∧ q = γ + (torusDualGradient h + torusHarmonicCurrent w) := by
  let d : TorusEdge L → ℤ := q - γ
  have hdiv : ∀ v, currentDivergence (torusGraph L hL) d v = 0 := by
    intro v
    have hq' := hq v
    have hγ' := hγ v
    rw [torusCurrentDivergence_formula] at hq' hγ'
    change currentDivergence (torusGraph L hL) (q - γ) v = 0
    rw [torusCurrentDivergence_formula]
    simp only [Pi.sub_apply]
    linear_combination hq' - hγ'
  obtain ⟨h, w, hp, hdecomp⟩ := torusCycle_decomposition_exists hL d hdiv
  refine ⟨h, w, hp, ?_⟩
  funext e
  have he := congrFun hdecomp e
  change q e = γ e + (torusDualGradient h e + torusHarmonicCurrent w e)
  dsimp [d] at he
  omega

/-- The pinned height and winding pair are unique after subtracting the fixed source path. -/
theorem torusSourceCycle_decomposition_unique {L : ℕ} [NeZero L] (hL : 2 < L)
    (q γ : TorusEdge L → ℤ) (h₁ h₂ : TorusVertex L → ℤ) (w₁ w₂ : ℤ × ℤ)
    (hh₁ : h₁ (0, 0) = 0) (hh₂ : h₂ (0, 0) = 0)
    (hq₁ : q = γ + (torusDualGradient h₁ + torusHarmonicCurrent w₁))
    (hq₂ : q = γ + (torusDualGradient h₂ + torusHarmonicCurrent w₂)) :
    h₁ = h₂ ∧ w₁ = w₂ := by
  have hcancel : q - γ = torusDualGradient h₁ + torusHarmonicCurrent w₁ := by
    funext e
    have he := congrFun hq₁ e
    change q e = γ e + (torusDualGradient h₁ e + torusHarmonicCurrent w₁ e) at he
    simp only [Pi.sub_apply, Pi.add_apply]
    linarith
  have hcancel₂ : q - γ = torusDualGradient h₂ + torusHarmonicCurrent w₂ := by
    funext e
    have he := congrFun hq₂ e
    change q e = γ e + (torusDualGradient h₂ e + torusHarmonicCurrent w₂ e) at he
    simp only [Pi.sub_apply, Pi.add_apply]
    linarith
  exact torusCycle_decomposition_unique hL (q - γ) h₁ h₂ w₁ w₂ hh₁ hh₂ hcancel hcancel₂


private theorem currentDivergence_add {L : ℕ} [NeZero L] (hL : 2 < L)
    (q r : TorusEdge L → ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (q + r) v =
      currentDivergence (torusGraph L hL) q v + currentDivergence (torusGraph L hL) r v := by
  classical
  unfold currentDivergence
  change ((∑ e : TorusEdge L, if e.1 = v then q e + r e else 0) -
      (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then q e + r e else 0)) =
    ((∑ e : TorusEdge L, if e.1 = v then q e else 0) -
      (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then q e else 0)) +
    ((∑ e : TorusEdge L, if e.1 = v then r e else 0) -
      (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then r e else 0))
  have hsrc : (∑ e, if e.1 = v then q e + r e else 0) =
      (∑ e, if e.1 = v then q e else 0) +
        ∑ e, if e.1 = v then r e else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hs : e.1 = v <;> simp [hs]
  have htgt : (∑ e, if torusStep L e.2 e.1 = v then q e + r e else 0) =
      (∑ e, if torusStep L e.2 e.1 = v then q e else 0) +
        ∑ e, if torusStep L e.2 e.1 = v then r e else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases ht : torusStep L e.2 e.1 = v <;> simp [ht]
  rw [hsrc, htgt]
  ring

private theorem currentDivergence_neg {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (-q) v =
      -currentDivergence (torusGraph L hL) q v := by
  have hadd := currentDivergence_add hL q (-q) v
  have hcancel : q + (-q) = (0 : TorusEdge L → ℤ) := by
    funext e
    simp
  rw [hcancel] at hadd
  have hzero : currentDivergence (torusGraph L hL) (0 : TorusEdge L → ℤ) v = 0 := by
    unfold currentDivergence
    change ((∑ e : TorusEdge L, if e.1 = v then (0 : ℤ) else 0) -
      (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then (0 : ℤ) else 0)) = 0
    simp
  rw [hzero] at hadd
  linarith

private theorem currentDivergence_sub {L : ℕ} [NeZero L] (hL : 2 < L)
    (q r : TorusEdge L → ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (q - r) v =
      currentDivergence (torusGraph L hL) q v - currentDivergence (torusGraph L hL) r v := by
  rw [sub_eq_add_neg, currentDivergence_add, currentDivergence_neg]
  ring

private theorem currentDivergence_zsmul {L : ℕ} [NeZero L] (hL : 2 < L)
    (k : ℤ) (q : TorusEdge L → ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (k • q) v =
      k * currentDivergence (torusGraph L hL) q v := by
  change currentDivergence (torusGraph L hL) (fun e => k * q e) v = _
  unfold currentDivergence
  change ((∑ e : TorusEdge L, if e.1 = v then k * q e else 0) -
      (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then k * q e else 0)) =
    k * ((∑ e : TorusEdge L, if e.1 = v then q e else 0) -
      (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then q e else 0))
  have hsrc : (∑ e, if e.1 = v then k * q e else 0) =
      k * ∑ e, if e.1 = v then q e else 0 := by
    calc
      _ = ∑ e, k * (if e.1 = v then q e else 0) := by
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> simp
      _ = _ := by rw [Finset.mul_sum]
  have htgt : (∑ e, if torusStep L e.2 e.1 = v then k * q e else 0) =
      k * ∑ e, if torusStep L e.2 e.1 = v then q e else 0 := by
    calc
      _ = ∑ e, k * (if torusStep L e.2 e.1 = v then q e else 0) := by
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> simp
      _ = _ := by rw [Finset.mul_sum]
  rw [hsrc, htgt]
  ring

/-- The unit current supported on one oriented edge. -/
def torusSingleCurrent {L : ℕ} [NeZero L] (e₀ : TorusEdge L) : TorusEdge L → ℤ :=
  fun e => if e = e₀ then 1 else 0

theorem currentDivergence_torusSingleCurrent {L : ℕ} [NeZero L] (hL : 2 < L)
    (e₀ : TorusEdge L) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (torusSingleCurrent e₀) v =
      (if (torusGraph L hL).src e₀ = v then (1 : ℤ) else 0) -
        (if (torusGraph L hL).tgt e₀ = v then (1 : ℤ) else 0) := by
  classical
  unfold currentDivergence torusSingleCurrent
  have hsrc : (∑ e, if e.1 = v then (if e = e₀ then (1 : ℤ) else 0) else 0) =
      if e₀.1 = v then (1 : ℤ) else 0 := by
    calc
      _ = ∑ e, if e = e₀ then (if e.1 = v then (1 : ℤ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases he₀ : e = e₀ <;> simp [he₀]
      _ = _ := by simp
  have htgt : (∑ e, if torusStep L e.2 e.1 = v then (if e = e₀ then (1 : ℤ) else 0) else 0) =
      if torusStep L e₀.2 e₀.1 = v then (1 : ℤ) else 0 := by
    calc
      _ = ∑ e, if e = e₀ then
          (if torusStep L e.2 e.1 = v then (1 : ℤ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases he₀ : e = e₀ <;> simp [he₀]
      _ = _ := by simp
  change ((∑ e : TorusEdge L, if e.1 = v then (if e = e₀ then (1 : ℤ) else 0) else 0) -
      (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then
        (if e = e₀ then (1 : ℤ) else 0) else 0)) =
    (if e₀.1 = v then (1 : ℤ) else 0) - (if torusStep L e₀.2 e₀.1 = v then (1 : ℤ) else 0)
  calc
    _ = (if e₀.1 = v then (1 : ℤ) else 0) -
        (if torusStep L e₀.2 e₀.1 = v then (1 : ℤ) else 0) :=
      congrArg₂ (fun a b : ℤ => a - b) hsrc htgt
    _ = _ := rfl

/-- The current along a finite positive horizontal path. -/
def torusHorizontalPathCurrent {L : ℕ} [NeZero L] (x y : ZMod L) :
    ℕ → TorusEdge L → ℤ
  | 0 => 0
  | n + 1 => torusHorizontalPathCurrent x y n +
      torusSingleCurrent ((x + (n : ZMod L), y), false)

/-- The current along a finite positive vertical path. -/
def torusVerticalPathCurrent {L : ℕ} [NeZero L] (x y : ZMod L) :
    ℕ → TorusEdge L → ℤ
  | 0 => 0
  | n + 1 => torusVerticalPathCurrent x y n +
      torusSingleCurrent ((x, y + (n : ZMod L)), true)

/-- The horizontal path current has positive divergence at its start and negative divergence at its endpoint. -/
theorem torusHorizontalPathCurrent_divergence {L : ℕ} [NeZero L] (hL : 2 < L)
    (x y : ZMod L) (n : ℕ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (torusHorizontalPathCurrent x y n) v =
      (if v = (x, y) then 1 else 0) - (if v = (x + (n : ZMod L), y) then 1 else 0) := by
  induction n with
  | zero =>
    change currentDivergence (torusGraph L hL) (0 : TorusEdge L → ℤ) v = _
    have hzero : currentDivergence (torusGraph L hL) (0 : TorusEdge L → ℤ) v = 0 := by
      unfold currentDivergence
      change ((∑ e : TorusEdge L, if e.1 = v then (0 : ℤ) else 0) -
        (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then (0 : ℤ) else 0)) = 0
      simp
    rw [hzero]
    simp
  | succ n ih =>
    rw [torusHorizontalPathCurrent, currentDivergence_add, ih,
      currentDivergence_torusSingleCurrent]
    simp only [torusGraph_src, torusGraph_tgt, torusStep, Bool.false_eq_true, ↓reduceIte]
    have hs : x + (n : ZMod L) + 1 = x + ((n + 1 : ℕ) : ZMod L) := by
      rw [Nat.cast_succ]
      ring
    rw [hs]
    simp only [eq_comm]
    ring

/-- The vertical path current has positive divergence at its start and negative divergence at its endpoint. -/
theorem torusVerticalPathCurrent_divergence {L : ℕ} [NeZero L] (hL : 2 < L)
    (x y : ZMod L) (n : ℕ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (torusVerticalPathCurrent x y n) v =
      (if v = (x, y) then 1 else 0) - (if v = (x, y + (n : ZMod L)) then 1 else 0) := by
  induction n with
  | zero =>
    change currentDivergence (torusGraph L hL) (0 : TorusEdge L → ℤ) v = _
    have hzero : currentDivergence (torusGraph L hL) (0 : TorusEdge L → ℤ) v = 0 := by
      unfold currentDivergence
      change ((∑ e : TorusEdge L, if e.1 = v then (0 : ℤ) else 0) -
        (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then (0 : ℤ) else 0)) = 0
      simp
    rw [hzero]
    simp
  | succ n ih =>
    rw [torusVerticalPathCurrent, currentDivergence_add, ih,
      currentDivergence_torusSingleCurrent]
    simp only [torusGraph_src, torusGraph_tgt, torusStep, ↓reduceIte]
    have hs : y + (n : ZMod L) + 1 = y + ((n + 1 : ℕ) : ZMod L) := by
      rw [Nat.cast_succ]
      ring
    rw [hs]
    simp only [eq_comm]
    ring

/-- A fixed coordinate path current from the origin to a torus vertex. -/
def torusRootPathCurrent {L : ℕ} [NeZero L] (p : TorusVertex L) : TorusEdge L → ℤ :=
  torusHorizontalPathCurrent 0 0 p.1.val + torusVerticalPathCurrent p.1 0 p.2.val

/-- The root path current has divergence equal to the origin-to-vertex dipole. -/
theorem torusRootPathCurrent_divergence {L : ℕ} [NeZero L] (hL : 2 < L)
    (p v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (torusRootPathCurrent p) v =
      (if v = (0, 0) then 1 else 0) - (if v = p then 1 else 0) := by
  rw [torusRootPathCurrent, currentDivergence_add,
    torusHorizontalPathCurrent_divergence, torusVerticalPathCurrent_divergence]
  have hx : (p.1.val : ZMod L) = p.1 := ZMod.natCast_zmod_val p.1
  have hy : (p.2.val : ZMod L) = p.2 := ZMod.natCast_zmod_val p.2
  simp only [hx, hy, zero_add]
  ring

/-- A fixed integer-multiple path current with the marked two-point divergence. -/
def torusSourcePathCurrent {L : ℕ} [NeZero L] (a x : TorusVertex L) (ξ : ℤ) :
    TorusEdge L → ℤ := ξ • (torusRootPathCurrent x - torusRootPathCurrent a)

private theorem torusSourcePathCurrent_divergence_dipole {L : ℕ} [NeZero L]
    (hL : 2 < L) (a x : TorusVertex L) (ξ : ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (torusSourcePathCurrent a x ξ) v =
      (if v = a then ξ else 0) - (if v = x then ξ else 0) := by
  unfold torusSourcePathCurrent
  rw [currentDivergence_zsmul, currentDivergence_sub]
  rw [torusRootPathCurrent_divergence, torusRootPathCurrent_divergence]
  by_cases hva : v = a
  · subst v
    by_cases hax : a = x
    · subst x
      simp
    · simp [hax]
  · by_cases hvx : v = x
    · have hxa : x ≠ a := fun h => hva (hvx.trans h)
      simp [hvx, hxa]
    · simp [hva, hvx]

/-- The fixed source path current realizes the two-point frequency on the torus. -/
theorem torusSourcePathCurrent_divergence {L : ℕ} [NeZero L] (hL : 2 < L)
    (a x : TorusVertex L) (ξ : ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (torusSourcePathCurrent a x ξ) v =
      rotatorTwoPointFrequency a x ξ v := by
  rw [torusSourcePathCurrent_divergence_dipole]
  simp only [rotatorTwoPointFrequency]
  have hx : (if v = x then -ξ else 0) = -(if v = x then ξ else 0) := by
    by_cases h : v = x <;> simp [h]
  rw [hx]
  ring


/-- Whether a graph isomorphism preserves the chosen orientation of an edge. -/
def currentSameOrientation {V E W F : Type*}
    {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (e : E) : Prop :=
  H.src (I.edges e) = I.vertices (G.src e) ∧
    H.tgt (I.edges e) = I.vertices (G.tgt e)

/-- Pull an integer current back along a multigraph isomorphism, changing sign on reversed edges. -/
noncomputable def currentPullback {V E W F : Type*}
    {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (q : F → ℤ) : E → ℤ := by
  classical
  exact fun e =>
    if currentSameOrientation I e then q (I.edges e) else -q (I.edges e)

private def currentEdgeDivergence {V E : Type*} [DecidableEq V]
    (G : Multigraph V E) (q : E → ℤ) (v : V) (e : E) : ℤ :=
  (if G.src e = v then q e else 0) - (if G.tgt e = v then q e else 0)

private theorem currentDivergence_eq_edgeSum {V E : Type*} [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (q : E → ℤ) (v : V) :
    currentDivergence G q v = ∑ e, currentEdgeDivergence G q v e := by
  classical
  unfold currentDivergence currentEdgeDivergence
  rw [← Finset.sum_sub_distrib]

private theorem currentEdgeDivergence_pullback {V E W F : Type*}
    [DecidableEq V] [DecidableEq W]
    {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (q : F → ℤ) (v : V) (e : E) :
    currentEdgeDivergence G (currentPullback I q) v e =
      currentEdgeDivergence H q (I.vertices v) (I.edges e) := by
  classical
  by_cases hs : currentSameOrientation I e
  · have hsame := hs
    dsimp [currentSameOrientation] at hsame
    rcases I.endpoints e with he | he
    · simp [currentEdgeDivergence, currentPullback, currentSameOrientation, hsame]
    · have hvertex : I.vertices (G.src e) = I.vertices (G.tgt e) :=
        hsame.1.symm.trans he.1
      have hloop : G.src e = G.tgt e := I.vertices.injective hvertex
      exact (G.src_ne_tgt e hloop).elim
  · rcases I.endpoints e with he | he
    · exact (hs he).elim
    · have hnot : ¬ currentSameOrientation I e := by
        intro hsame
        dsimp [currentSameOrientation] at hsame
        have hvertex : I.vertices (G.src e) = I.vertices (G.tgt e) :=
          hsame.1.symm.trans he.1
        exact G.src_ne_tgt e (I.vertices.injective hvertex)
      have hrevFalse : ¬ (G.tgt e = G.src e ∧ G.src e = G.tgt e) := by
        rintro ⟨_, h₂⟩
        exact G.src_ne_tgt e h₂
      have hsrc : I.vertices (G.src e) = I.vertices v ↔ G.src e = v :=
        I.vertices.injective.eq_iff
      have htgt : I.vertices (G.tgt e) = I.vertices v ↔ G.tgt e = v :=
        I.vertices.injective.eq_iff
      simp [currentEdgeDivergence, currentPullback, currentSameOrientation,
        he.1, he.2, hsrc, htgt, hrevFalse]
      have hsrcNeg : (if G.src e = v then -q (I.edges e) else 0) =
          -(if G.src e = v then q (I.edges e) else 0) := by
        by_cases h : G.src e = v <;> simp [h]
      have htgtNeg : (if G.tgt e = v then -q (I.edges e) else 0) =
          -(if G.tgt e = v then q (I.edges e) else 0) := by
        by_cases h : G.tgt e = v <;> simp [h]
      rw [hsrcNeg, htgtNeg]
      ring

private theorem currentDivergence_pullback {V E W F : Type*}
    [Fintype E] [Fintype F] [DecidableEq V] [DecidableEq W]
    {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (q : F → ℤ) (v : V) :
    currentDivergence G (currentPullback I q) v =
      currentDivergence H q (I.vertices v) := by
  classical
  calc
    currentDivergence G (currentPullback I q) v =
        ∑ e, currentEdgeDivergence G (currentPullback I q) v e :=
      currentDivergence_eq_edgeSum G _ _
    _ = ∑ e, currentEdgeDivergence H q (I.vertices v) (I.edges e) := by
      apply Finset.sum_congr rfl
      intro e he
      exact currentEdgeDivergence_pullback I q v e
    _ = ∑ f, currentEdgeDivergence H q (I.vertices v) f :=
      Equiv.sum_comp I.edges _
    _ = currentDivergence H q (I.vertices v) :=
      (currentDivergence_eq_edgeSum H _ _).symm

/--
Transport a square-periodic current to the right/up torus orientation, applying the sign change
when the sorted edge orientation is opposite.
-/
noncomputable def torusCurrentOfSquare {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : Bond L → ℤ) : TorusEdge L → ℤ :=
  currentPullback (torusGraphToSquarePeriodicIso hL) q

/--
Transport a right/up torus current back to the sorted-edge carrier with its orientation
sign restored.
-/
noncomputable def squareCurrentOfTorus {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) : Bond L → ℤ :=
  currentPullback (squarePeriodicTorusIsomorphism hL) q

/-- The signed transport preserves current divergence at corresponding vertices. -/
theorem torusCurrentOfSquare_divergence {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : Bond L → ℤ) (p : TorusVertex L) :
    currentDivergence (torusGraph L hL) (torusCurrentOfSquare hL q) p =
      currentDivergence (graph L) q ((squareTorusVertexEquiv L).symm p) := by
  simpa [torusCurrentOfSquare, torusGraphToSquarePeriodicIso, graph,
    squarePeriodic] using
    (currentDivergence_pullback (torusGraphToSquarePeriodicIso hL) q p)

/-- The signed reverse transport preserves current divergence at corresponding vertices. -/
theorem squareCurrentOfTorus_divergence {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : TorusEdge L → ℤ) (v : Site L) :
    currentDivergence (graph L) (squareCurrentOfTorus hL q) v =
      currentDivergence (torusGraph L hL) q (squareTorusVertexEquiv L v) := by
  simpa [squareCurrentOfTorus, squarePeriodicTorusIsomorphism, graph,
    squarePeriodic] using
    (currentDivergence_pullback (squarePeriodicTorusIsomorphism hL) q v)


private theorem currentOrientation_roundtrip {L : ℕ} [NeZero L] (hL : 2 < L)
    (t : TorusEdge L) :
    currentSameOrientation (torusGraphToSquarePeriodicIso hL) t ↔
      currentSameOrientation (squarePeriodicTorusIsomorphism hL)
        ((torusGraphToSquarePeriodicIso hL).edges t) := by
  let I := torusGraphToSquarePeriodicIso hL
  let J := squarePeriodicTorusIsomorphism hL
  have hedges : J.edges (I.edges t) = t :=
    squarePeriodicEdgeToTorus_edgeOfTorus hL t
  have hverts (v : TorusVertex L) : J.vertices (I.vertices v) = v := by
    change squareTorusVertexEquiv L ((squareTorusVertexEquiv L).symm v) = v
    exact Equiv.apply_symm_apply _ _
  have hi := I.endpoints t
  have hj := J.endpoints (I.edges t)
  simp only [hedges] at hj
  rcases hi with hi | hi
  · rcases hj with hj | hj
    · change ((squarePeriodic L).src (I.edges t) =
          I.vertices ((torusGraph L hL).src t) ∧
        (squarePeriodic L).tgt (I.edges t) = I.vertices ((torusGraph L hL).tgt t)) ↔
        ((torusGraph L hL).src (J.edges (I.edges t)) =
          J.vertices ((squarePeriodic L).src (I.edges t)) ∧
        (torusGraph L hL).tgt (J.edges (I.edges t)) =
          J.vertices ((squarePeriodic L).tgt (I.edges t)))
      constructor
      · intro _
        simpa only [hedges] using hj
      · intro _
        simpa only [hedges] using hi
    · have hloop : (torusGraph L hL).src t = (torusGraph L hL).tgt t := by
        calc
          _ = J.vertices ((squarePeriodic L).tgt (I.edges t)) := hj.1
          _ = J.vertices (I.vertices ((torusGraph L hL).tgt t)) := by rw [hi.2]
          _ = _ := hverts _
      exact (torusGraph L hL).src_ne_tgt t hloop |>.elim
  · rcases hj with hj | hj
    · have hloop : (torusGraph L hL).src t = (torusGraph L hL).tgt t := by
        calc
          _ = J.vertices ((squarePeriodic L).src (I.edges t)) := hj.1
          _ = J.vertices (I.vertices ((torusGraph L hL).tgt t)) := by rw [hi.1]
          _ = _ := hverts _
      exact (torusGraph L hL).src_ne_tgt t hloop |>.elim
    · constructor
      · intro hsame
        dsimp [currentSameOrientation] at hsame
        have hvertex : I.vertices ((torusGraph L hL).src t) =
            I.vertices ((torusGraph L hL).tgt t) := by
          calc
            _ = (squarePeriodic L).src (I.edges t) := hsame.1.symm
            _ = I.vertices ((torusGraph L hL).tgt t) := hi.1
        exact (torusGraph L hL).src_ne_tgt t (I.vertices.injective hvertex) |>.elim
      · intro hsame
        have hsame₁ := hsame.1
        change (torusGraph L hL).src (J.edges (I.edges t)) =
          J.vertices ((squarePeriodic L).src (I.edges t)) at hsame₁
        rw [hedges] at hsame₁
        have hloop : (torusGraph L hL).src t = (torusGraph L hL).tgt t := by
          calc
            _ = J.vertices ((squarePeriodic L).src (I.edges t)) := hsame₁
            _ = J.vertices (I.vertices ((torusGraph L hL).tgt t)) := by rw [hi.1]
            _ = _ := hverts _
        exact (torusGraph L hL).src_ne_tgt t hloop |>.elim

/-- The two signed current transports are inverse on right/up torus currents. -/
theorem torusCurrentOfSquare_squareCurrentOfTorus {L : ℕ} [NeZero L]
    (hL : 2 < L) (q : TorusEdge L → ℤ) :
    torusCurrentOfSquare hL (squareCurrentOfTorus hL q) = q := by
  classical
  let I := torusGraphToSquarePeriodicIso hL
  let J := squarePeriodicTorusIsomorphism hL
  funext t
  have hedges : J.edges (I.edges t) = t := squarePeriodicEdgeToTorus_edgeOfTorus hL t
  have hrel : currentSameOrientation I t ↔ currentSameOrientation J (I.edges t) := by
    simpa [I, J] using currentOrientation_roundtrip hL t
  change (if currentSameOrientation I t then
      (if currentSameOrientation J (I.edges t) then q (J.edges (I.edges t)) else -q (J.edges (I.edges t)))
    else -(if currentSameOrientation J (I.edges t) then q (J.edges (I.edges t)) else -q (J.edges (I.edges t)))) = q t
  by_cases hs : currentSameOrientation I t
  · have hs' := hrel.mp hs
    simp [hs, hs', hedges]
  · have hs' : ¬ currentSameOrientation J (I.edges t) := fun h => hs (hrel.mpr h)
    simp [hs, hs', hedges]

/--
The two signed current transports are inverse on  periodic-square currents.
-/
theorem squareCurrentOfTorus_torusCurrentOfSquare {L : ℕ} [NeZero L]
    (hL : 2 < L) (q : Bond L → ℤ) :
    squareCurrentOfTorus hL (torusCurrentOfSquare hL q) = q := by
  classical
  let I := torusGraphToSquarePeriodicIso hL
  let J := squarePeriodicTorusIsomorphism hL
  funext e
  have hedges : I.edges (J.edges e) = e := squarePeriodicEdgeOfTorus_edgeToTorus hL e
  have hrel : currentSameOrientation J e ↔ currentSameOrientation I (J.edges e) := by
    have h := currentOrientation_roundtrip hL (J.edges e)
    simpa [I, J, hedges] using h.symm
  change (if currentSameOrientation J e then
      (if currentSameOrientation I (J.edges e) then q (I.edges (J.edges e)) else -q (I.edges (J.edges e)))
    else -(if currentSameOrientation I (J.edges e) then q (I.edges (J.edges e)) else -q (I.edges (J.edges e)))) = q e
  by_cases hs : currentSameOrientation J e
  · have hs' := hrel.mp hs
    simp [hs, hs', hedges]
  · have hs' : ¬ currentSameOrientation I (J.edges e) := fun h => hs (hrel.mpr h)
    simp [hs, hs', hedges]


/--
The torus current map sends divergence-free -square currents to divergence-free torus
currents, preserving the full integer current under the inverse map.
-/
theorem torusCycle_decomposition_exists_from_square {L : ℕ} [NeZero L]
    (hL : 2 < L) (q : Bond L → ℤ)
    (hdiv : ∀ v, currentDivergence (graph L) q v = 0) :
    ∃ h : TorusVertex L → ℤ, ∃ w : ℤ × ℤ,
      h (0, 0) = 0 ∧
        torusCurrentOfSquare hL q = torusDualGradient h + torusHarmonicCurrent w := by
  have hdivT : ∀ p, currentDivergence (torusGraph L hL)
      (torusCurrentOfSquare hL q) p = 0 := by
    intro p
    rw [torusCurrentOfSquare_divergence]
    exact hdiv ((squareTorusVertexEquiv L).symm p)
  exact torusCycle_decomposition_exists hL (torusCurrentOfSquare hL q) hdivT

/--
A divergence-free -square current has a unique transported pinned height and winding
pair.
-/
theorem torusCycle_decomposition_unique_from_square {L : ℕ} [NeZero L]
    (hL : 2 < L) (q : Bond L → ℤ)
    (h₁ h₂ : TorusVertex L → ℤ) (w₁ w₂ : ℤ × ℤ)
    (hh₁ : h₁ (0, 0) = 0) (hh₂ : h₂ (0, 0) = 0)
    (hq₁ : torusCurrentOfSquare hL q = torusDualGradient h₁ + torusHarmonicCurrent w₁)
    (hq₂ : torusCurrentOfSquare hL q = torusDualGradient h₂ + torusHarmonicCurrent w₂) :
    h₁ = h₂ ∧ w₁ = w₂ :=
  torusCycle_decomposition_unique hL (torusCurrentOfSquare hL q)
    h₁ h₂ w₁ w₂ hh₁ hh₂ hq₁ hq₂

/-- Integer point-character frequencies are preserved by a bijection of vertex carriers. -/
theorem rotatorTwoPointFrequency_equiv {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (a x : V) (ξ : ℤ) (v : W) :
    rotatorTwoPointFrequency a x ξ (e.symm v) =
      rotatorTwoPointFrequency (e a) (e x) ξ v := by
  have ha : e.symm v = a ↔ v = e a := by
    constructor
    · intro h
      calc
        v = e (e.symm v) := by simp
        _ = e a := by rw [h]
    · intro h
      apply e.injective
      simpa using h
  have hx : e.symm v = x ↔ v = e x := by
    constructor
    · intro h
      calc
        v = e (e.symm v) := by simp
        _ = e x := by rw [h]
    · intro h
      apply e.injective
      simpa using h
  simp only [rotatorTwoPointFrequency, ha, hx]

/--
A fixed source path current on the periodic square, transported from the canonical
coordinate path on the right/up torus.
-/
noncomputable def squareSourcePathCurrent {L : ℕ} [NeZero L] (hL : 2 < L)
    (a x : Site L) (ξ : ℤ) : Bond L → ℤ :=
  squareCurrentOfTorus hL
    (torusSourcePathCurrent (squareTorusVertexEquiv L a)
      (squareTorusVertexEquiv L x) ξ)

/--
The -square source path has the divergence imposed by the two-point character.
-/
theorem squareSourcePathCurrent_divergence {L : ℕ} [NeZero L] (hL : 2 < L)
    (a x : Site L) (ξ : ℤ) (v : Site L) :
    currentDivergence (graph L) (squareSourcePathCurrent hL a x ξ) v =
      rotatorTwoPointFrequency a x ξ v := by
  rw [squareSourcePathCurrent, squareCurrentOfTorus_divergence,
    torusSourcePathCurrent_divergence]
  simpa using (rotatorTwoPointFrequency_equiv (squareTorusVertexEquiv L)
    a x ξ (squareTorusVertexEquiv L v)).symm

/--
A -square current with the marked endpoint divergence is its fixed source path plus one
pinned height gradient and a unique pair of winding representatives, after signed transport.
-/
theorem torusSourceCycle_decomposition_exists_from_square {L : ℕ} [NeZero L]
    (hL : 2 < L) (q : Bond L → ℤ) (a x : Site L) (ξ : ℤ)
    (hq : ∀ v, currentDivergence (graph L) q v =
      rotatorTwoPointFrequency a x ξ v) :
    ∃ h : TorusVertex L → ℤ, ∃ w : ℤ × ℤ,
      h (0, 0) = 0 ∧
        torusCurrentOfSquare hL q =
          torusCurrentOfSquare hL (squareSourcePathCurrent hL a x ξ) +
            (torusDualGradient h + torusHarmonicCurrent w) := by
  let aT := squareTorusVertexEquiv L a
  let xT := squareTorusVertexEquiv L x
  have hqT : ∀ p, currentDivergence (torusGraph L hL)
      (torusCurrentOfSquare hL q) p =
        rotatorTwoPointFrequency aT xT ξ p := by
    intro p
    rw [torusCurrentOfSquare_divergence]
    calc
      currentDivergence (graph L) q ((squareTorusVertexEquiv L).symm p) =
          rotatorTwoPointFrequency a x ξ ((squareTorusVertexEquiv L).symm p) :=
        hq ((squareTorusVertexEquiv L).symm p)
      _ = rotatorTwoPointFrequency aT xT ξ p :=
        rotatorTwoPointFrequency_equiv (squareTorusVertexEquiv L) a x ξ p
  have hγT : ∀ p, currentDivergence (torusGraph L hL)
      (torusSourcePathCurrent aT xT ξ) p =
        rotatorTwoPointFrequency aT xT ξ p := by
    intro p
    exact torusSourcePathCurrent_divergence hL aT xT ξ p
  obtain ⟨h, w, hh, hdecomp⟩ := torusSourceCycle_decomposition_exists hL
    (torusCurrentOfSquare hL q) (torusSourcePathCurrent aT xT ξ)
    (rotatorTwoPointFrequency aT xT ξ) hqT hγT
  have hsource : torusCurrentOfSquare hL (squareSourcePathCurrent hL a x ξ) =
      torusSourcePathCurrent aT xT ξ := by
    rw [squareSourcePathCurrent]
    exact torusCurrentOfSquare_squareCurrentOfTorus hL _
  refine ⟨h, w, hh, ?_⟩
  rw [hdecomp, hsource]

/--
The pinned height and winding pair of a marked -square current are unique after its fixed
source path is subtracted.
-/
theorem torusSourceCycle_decomposition_unique_from_square {L : ℕ} [NeZero L]
    (hL : 2 < L) (q : Bond L → ℤ) (a x : Site L) (ξ : ℤ)
    (h₁ h₂ : TorusVertex L → ℤ) (w₁ w₂ : ℤ × ℤ)
    (hh₁ : h₁ (0, 0) = 0) (hh₂ : h₂ (0, 0) = 0)
    (hq₁ : torusCurrentOfSquare hL q =
      torusCurrentOfSquare hL (squareSourcePathCurrent hL a x ξ) +
        (torusDualGradient h₁ + torusHarmonicCurrent w₁))
    (hq₂ : torusCurrentOfSquare hL q =
      torusCurrentOfSquare hL (squareSourcePathCurrent hL a x ξ) +
        (torusDualGradient h₂ + torusHarmonicCurrent w₂)) :
    h₁ = h₂ ∧ w₁ = w₂ :=
  torusSourceCycle_decomposition_unique hL
    (torusCurrentOfSquare hL q)
    (torusCurrentOfSquare hL (squareSourcePathCurrent hL a x ξ))
    h₁ h₂ w₁ w₂ hh₁ hh₂ hq₁ hq₂


/-!
## Winding-sector current sums

The sector fibers retain the -square current carrier.

Their winding labels are computed
after signed transport to the right/up torus; for marked currents we subtract the fixed coordinate
source path first.
-/

/-- The pinned integer heights on the dual torus. -/
def periodicPinnedHeights (L : ℕ) [NeZero L] :=
  {h : TorusVertex L → ℤ // h (0, 0) = 0}

/--
A pinned height and winding pair, transported to the periodic-square carrier.
-/
noncomputable def periodicTwistedHeightCurrent {L : ℕ} [NeZero L] (hL : 2 < L)
    (w : ℤ × ℤ) (h : periodicPinnedHeights L) : Bond L → ℤ :=
  squareCurrentOfTorus hL
    (torusDualGradient h.1 + torusHarmonicCurrent w)

/--
The zero-divergence predicate on  periodic-square currents.
-/
def periodicNeutralCurrentPredicate {L : ℕ} (q : Bond L → ℤ) : Prop :=
  ∀ v, currentDivergence (graph L) q v = 0

/--
The set of neutral  periodic-square integer currents.
-/
def periodicNeutralCurrents {L : ℕ} (_hL : 2 < L) :=
  {q : Bond L → ℤ // periodicNeutralCurrentPredicate (L := L) q}

/--
The winding pair of a neutral -square current.
-/
noncomputable def periodicNeutralCurrentWinding {L : ℕ} [NeZero L] (hL : 2 < L)
    (q : periodicNeutralCurrents (L := L) hL) : ℤ × ℤ :=
  (torusWindingX (torusCurrentOfSquare hL q.1),
    torusWindingY (torusCurrentOfSquare hL q.1))

/-- The neutral-current fiber with prescribed winding pair. -/
def periodicNeutralCurrentSector {L : ℕ} [NeZero L] (hL : 2 < L) (w : ℤ × ℤ) :=
  {q : periodicNeutralCurrents (L := L) hL // periodicNeutralCurrentWinding hL q = w}

/--
The marked-divergence predicate on  periodic-square currents.
-/
def periodicMarkedCurrentPredicate {L : ℕ} (q : Bond L → ℤ)
    (a x : Site L) (ξ : ℤ) : Prop :=
  ∀ v, currentDivergence (graph L) q v = rotatorTwoPointFrequency a x ξ v

/-- The winding pair of a marked current relative to the fixed coordinate source path. -/
noncomputable def periodicMarkedCurrentWinding {L : ℕ} [NeZero L] (hL : 2 < L)
    (a x : Site L) (ξ : ℤ) (q : Bond L → ℤ) : ℤ × ℤ :=
  let qT := torusCurrentOfSquare hL q
  let γT := torusSourcePathCurrent (squareTorusVertexEquiv L a)
    (squareTorusVertexEquiv L x) ξ
  (torusWindingX (qT - γT), torusWindingY (qT - γT))

/-- A marked current sector, with winding measured after subtracting its fixed source path. -/
def periodicMarkedCurrentSector {L : ℕ} [NeZero L] (hL : 2 < L)
    (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ) :=
  {q : Bond L → ℤ // periodicMarkedCurrentPredicate q a x ξ ∧
    periodicMarkedCurrentWinding hL a x ξ q = w}

/-- Marked currents before they are partitioned by their relative winding. -/
def periodicMarkedCurrents {L : ℕ} (a x : Site L) (ξ : ℤ) :=
  {q : Bond L → ℤ // periodicMarkedCurrentPredicate q a x ξ}

/-- Winding of a marked current viewed in the marked-current subtype. -/
noncomputable def periodicMarkedCurrentsWinding {L : ℕ} [NeZero L]
    (hL : 2 < L) (a x : Site L) (ξ : ℤ)
    (q : periodicMarkedCurrents (L := L) a x ξ) : ℤ × ℤ :=
  periodicMarkedCurrentWinding hL a x ξ q.1

/-- The marked-current fiber description of a winding sector. -/
def periodicMarkedCurrentsFiber {L : ℕ} [NeZero L] (hL : 2 < L)
    (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ) :=
  {q : periodicMarkedCurrents (L := L) a x ξ // periodicMarkedCurrentsWinding hL a x ξ q = w}

/-- The nonnegative real weight of a neutral winding sector. -/
noncomputable def periodicNeutralSectorWeight {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (w : ℤ × ℤ) : ℝ :=
  ∑' q : periodicNeutralCurrentSector hL w, rotatorCurrentWeight (rotatorIReal β) q.1.1

/-- The nonnegative real weight of a marked winding sector. -/
noncomputable def periodicMarkedSectorWeight {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ) : ℝ :=
  ∑' q : periodicMarkedCurrentSector hL a x ξ w, rotatorCurrentWeight (rotatorIReal β) q.1

private theorem periodicCurrentWeight_summable {L : ℕ} (β : ℝ)
    (hI : Summable (rotatorI β)) :
    Summable (fun q : Bond L → ℤ => |rotatorCurrentWeight (rotatorIReal β) q|) := by
  have h := Villain.summable_norm_prod_currents (E := Bond L)
    (fun _ m => rotatorI β m) (fun _ => hI.norm)
  apply h.congr
  intro q
  rw [rotatorCurrentWeight]
  rw [show (∏ e : Bond L, rotatorI β (q e)) =
      ((∏ e : Bond L, rotatorIReal β (q e) : ℝ) : ℂ) by
        simp [rotatorI_eq_realCast]]
  rw [Complex.norm_real, Real.norm_eq_abs]

universe u v

private theorem tsum_subtype_fiberwise {α : Type u} {β : Type v}
    (P : α → Prop) (f : α → β) (g : α → ℂ)
    (h : Summable (fun a : {x // P x} => g a.1)) :
    (∑' a : {x // P x}, g a.1) =
      ∑' b : β, ∑' a : {x : {x // P x} // f x.1 = b}, g a.1 := by
  let F : β → Type u := fun b => {x : {x // P x} // f x.1 = b}
  let e := Equiv.sigmaFiberEquiv (fun a : {x // P x} => f a.1)
  have hs : Summable (fun s : Σ b, F b => g (e s).1) :=
    h.comp_injective e.injective
  calc
    (∑' a : {x // P x}, g a.1) = ∑' s : Σ b, F b, g (e s).1 :=
      (Equiv.tsum_eq e (fun a : {x // P x} => g a.1)).symm
    _ = ∑' b : β, ∑' a : F b, g a.1 := by
      simpa [F, e, Equiv.sigmaFiberEquiv] using hs.tsum_sigma

private theorem tsum_fiberwise {α : Type u} {β : Type v}
    (f : α → β) (g : α → ℂ) (h : Summable g) :
    (∑' a : α, g a) = ∑' b : β, ∑' a : {x : α // f x = b}, g a.1 := by
  let F : β → Type u := fun b => {x : α // f x = b}
  let e := Equiv.sigmaFiberEquiv f
  have hs : Summable (fun s : Σ b, F b => g (e s)) := h.comp_injective e.injective
  calc
    (∑' a : α, g a) = ∑' s : Σ b, F b, g (e s) :=
      (Equiv.tsum_eq e g).symm
    _ = ∑' b : β, ∑' a : F b, g a.1 := by
      simpa [F, e, Equiv.sigmaFiberEquiv] using hs.tsum_sigma

theorem torusDivergence_add_formula {L : ℕ} [NeZero L] (hL : 2 < L)
    (q r : TorusEdge L → ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (q + r) v =
      currentDivergence (torusGraph L hL) q v + currentDivergence (torusGraph L hL) r v := by
  rw [torusCurrentDivergence_formula]
  simp only [Pi.add_apply]
  rw [torusCurrentDivergence_formula, torusCurrentDivergence_formula]
  ring

theorem torusDivergence_sub_formula {L : ℕ} [NeZero L] (hL : 2 < L)
    (q r : TorusEdge L → ℤ) (v : TorusVertex L) :
    currentDivergence (torusGraph L hL) (q - r) v =
      currentDivergence (torusGraph L hL) q v - currentDivergence (torusGraph L hL) r v := by
  rw [torusCurrentDivergence_formula]
  simp only [Pi.sub_apply]
  rw [torusCurrentDivergence_formula, torusCurrentDivergence_formula]
  ring

theorem torusWindingX_add_sector {L : ℕ} [NeZero L] (q r : TorusEdge L → ℤ) :
    torusWindingX (q + r) = torusWindingX q + torusWindingX r := by
  simp [torusWindingX, Finset.sum_add_distrib]

theorem torusWindingY_add_sector {L : ℕ} [NeZero L] (q r : TorusEdge L → ℤ) :
    torusWindingY (q + r) = torusWindingY q + torusWindingY r := by
  simp [torusWindingY, Finset.sum_add_distrib]

theorem torusWindingX_sub_sector {L : ℕ} [NeZero L] (q r : TorusEdge L → ℤ) :
    torusWindingX (q - r) = torusWindingX q - torusWindingX r := by
  simp [torusWindingX, Finset.sum_sub_distrib]

theorem torusWindingY_sub_sector {L : ℕ} [NeZero L] (q r : TorusEdge L → ℤ) :
    torusWindingY (q - r) = torusWindingY q - torusWindingY r := by
  simp [torusWindingY, Finset.sum_sub_distrib]

/-- A pinned height and winding pair define a neutral square current in the corresponding sector.
-/
noncomputable def periodicNeutralSectorCurrent {L : ℕ} [NeZero L] (hL : 2 < L)
    (w : ℤ × ℤ) (h : periodicPinnedHeights L) : periodicNeutralCurrentSector hL w := by
  classical
  let q := periodicTwistedHeightCurrent hL w h
  have hdiv : periodicNeutralCurrentPredicate (L := L) q := by
    intro v
    change currentDivergence (graph L)
      (squareCurrentOfTorus hL (torusDualGradient h.1 + torusHarmonicCurrent w)) v = 0
    rw [squareCurrentOfTorus_divergence, torusDivergence_add_formula,
      torusDualGradient_divergence_zero, torusHarmonicCurrent_divergence_zero]
    ring
  have hwind : periodicNeutralCurrentWinding hL ⟨q, hdiv⟩ = w := by
    apply Prod.ext
    · change torusWindingX (torusCurrentOfSquare hL
        (squareCurrentOfTorus hL
          (torusDualGradient h.1 + torusHarmonicCurrent w))) = w.1
      rw [torusCurrentOfSquare_squareCurrentOfTorus]
      rw [torusWindingX_add_sector, torusDualGradient_torusWindingX_zero,
        torusHarmonicCurrent_torusWindingX]
      ring
    · change torusWindingY (torusCurrentOfSquare hL
        (squareCurrentOfTorus hL
          (torusDualGradient h.1 + torusHarmonicCurrent w))) = w.2
      rw [torusCurrentOfSquare_squareCurrentOfTorus]
      rw [torusWindingY_add_sector, torusDualGradient_torusWindingY_zero,
        torusHarmonicCurrent_torusWindingY]
      ring
  exact ⟨⟨q, hdiv⟩, hwind⟩

/-- The unique pinned height corresponding to a current in a fixed neutral winding sector. -/
noncomputable def periodicNeutralSectorHeight {L : ℕ} [NeZero L] (hL : 2 < L)
    (w : ℤ × ℤ) (q : periodicNeutralCurrentSector hL w) : periodicPinnedHeights L :=
  ⟨torusPathHeight
    (torusCurrentOfSquare hL q.1.1 - torusHarmonicCurrent w),
    torusPathHeight_root _⟩

/-- Each neutral winding sector is in bijection with pinned twisted heights. -/
noncomputable def periodicNeutralSectorEquiv {L : ℕ} [NeZero L] (hL : 2 < L)
    (w : ℤ × ℤ) : periodicPinnedHeights L ≃ periodicNeutralCurrentSector hL w where
  toFun := periodicNeutralSectorCurrent hL w
  invFun := periodicNeutralSectorHeight hL w
  left_inv := by
    intro h
    apply Subtype.ext
    apply torusDualGradient_injective_pinned hL
    · exact (periodicNeutralSectorHeight hL w
        (periodicNeutralSectorCurrent hL w h)).2
    · exact h.2
    have hq : torusCurrentOfSquare hL
        (periodicNeutralSectorCurrent hL w h).1.1 =
        torusDualGradient h.1 + torusHarmonicCurrent w := by
      change torusCurrentOfSquare hL
        (squareCurrentOfTorus hL
          (torusDualGradient h.1 + torusHarmonicCurrent w)) = _
      rw [torusCurrentOfSquare_squareCurrentOfTorus]
    have hr : torusCurrentOfSquare hL
        (periodicNeutralSectorCurrent hL w h).1.1 - torusHarmonicCurrent w =
        torusDualGradient h.1 := by
      funext e
      have he := congrFun hq e
      simp only [Pi.sub_apply, Pi.add_apply] at *
      linarith
    have hgrad : torusDualGradient
        (torusPathHeight (torusCurrentOfSquare hL
          (periodicNeutralSectorCurrent hL w h).1.1 - torusHarmonicCurrent w)) =
        torusDualGradient h.1 := by
      rw [hr]
      symm
      apply torusPathHeight_eq_torusDualGradient_of_cycle_zeroPeriods hL
      · exact torusDualGradient_divergence_zero hL h.1
      · exact torusDualGradient_torusWindingX_zero h.1
      · exact torusDualGradient_torusWindingY_zero h.1
    exact hgrad
  right_inv := by
    intro q
    apply Subtype.ext
    have hqTdiv : ∀ v, currentDivergence (torusGraph L hL)
        (torusCurrentOfSquare hL q.1.1) v = 0 := by
      intro v
      rw [torusCurrentOfSquare_divergence]
      exact q.1.2 ((squareTorusVertexEquiv L).symm v)
    have hrdiv : ∀ v, currentDivergence (torusGraph L hL)
        (torusCurrentOfSquare hL q.1.1 - torusHarmonicCurrent w) v = 0 := by
      intro v
      rw [torusDivergence_sub_formula, hqTdiv v,
        torusHarmonicCurrent_divergence_zero, sub_zero]
    have hrwindX : torusWindingX
        (torusCurrentOfSquare hL q.1.1 - torusHarmonicCurrent w) = 0 := by
      rw [torusWindingX_sub]
      have hw := congrArg Prod.fst q.2
      change torusWindingX (torusCurrentOfSquare hL q.1.1) = w.1 at hw
      rw [torusHarmonicCurrent_torusWindingX]
      omega
    have hrwindY : torusWindingY
        (torusCurrentOfSquare hL q.1.1 - torusHarmonicCurrent w) = 0 := by
      rw [torusWindingY_sub]
      have hw := congrArg Prod.snd q.2
      change torusWindingY (torusCurrentOfSquare hL q.1.1) = w.2 at hw
      rw [torusHarmonicCurrent_torusWindingY]
      omega
    have hr := torusPathHeight_eq_torusDualGradient_of_cycle_zeroPeriods hL
      (torusCurrentOfSquare hL q.1.1 - torusHarmonicCurrent w) hrdiv hrwindX hrwindY
    have hdecomp : torusCurrentOfSquare hL q.1.1 =
        torusDualGradient (periodicNeutralSectorHeight hL w q).1 +
          torusHarmonicCurrent w := by
      funext e
      have he := congrFun hr e
      change torusCurrentOfSquare hL q.1.1 e =
        torusDualGradient
          (torusPathHeight (torusCurrentOfSquare hL q.1.1 - torusHarmonicCurrent w)) e +
          torusHarmonicCurrent w e
      simp only [Pi.sub_apply] at he
      linarith
    have hback := squareCurrentOfTorus_torusCurrentOfSquare hL q.1.1
    apply Subtype.ext
    funext e
    have he := congrFun hback e
    change squareCurrentOfTorus hL
      (torusDualGradient (periodicNeutralSectorHeight hL w q).1 +
        torusHarmonicCurrent w) e = q.1.1 e
    rw [← hdecomp]
    exact he

/-- The marked-current winding fiber is equivalent to the conjunction-based marked sector carrier.
-/
def periodicMarkedCurrentsFiberEquiv {L : ℕ} [NeZero L]
    (hL : 2 < L) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ) :
    periodicMarkedCurrentsFiber hL a x ξ w ≃ periodicMarkedCurrentSector hL a x ξ w where
  toFun q := ⟨q.1.1, q.1.2, q.2⟩
  invFun q := ⟨⟨q.1, q.2.1⟩, q.2.2⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro q
    apply Subtype.ext
    rfl

/-- Absolute summability of sector sums follows from absolute summability on the whole current
carrier. -/
private theorem periodicFiberAbsSummable {α : Type u} {β : Type v}
    (P : α → Prop) (f : α → β) (g : {x // P x} → ℝ)
    (h : Summable (fun x : {x // P x} => |g x|)) :
    Summable (fun b : β => ∑' x : {y : {x // P x} // f y.1 = b}, |g x.1|) := by
  let F : β → Type u := fun b => {y : {x // P x} // f y.1 = b}
  let e := Equiv.sigmaFiberEquiv (fun x : {x // P x} => f x.1)
  have hs : Summable (fun s : Σ b, F b => |g (e s)|) :=
    h.comp_injective e.injective
  have hparts := (summable_sigma_of_nonneg (fun s => abs_nonneg (g (e s)))).mp hs
  simpa [F, e, Equiv.sigmaFiberEquiv] using hparts.2

private theorem tsum_subtype_fiberwise_real {α : Type u} {β : Type v}
    (P : α → Prop) (f : α → β) (g : {x // P x} → ℝ)
    (h : Summable (fun a : {x // P x} => g a)) :
    (∑' a : {x // P x}, g a) =
      ∑' b : β, ∑' a : {x : {x // P x} // f x.1 = b}, g a.1 := by
  let F : β → Type u := fun b => {x : {x // P x} // f x.1 = b}
  let e := Equiv.sigmaFiberEquiv (fun a : {x // P x} => f a.1)
  have hs : Summable (fun s : Σ b, F b => g (e s)) :=
    h.comp_injective e.injective
  calc
    (∑' a : {x // P x}, g a) = ∑' s : Σ b, F b, g (e s) :=
      (Equiv.tsum_eq e (fun a : {x // P x} => g a)).symm
    _ = ∑' b : β, ∑' a : F b, g a.1 := by
      simpa [F, e, Equiv.sigmaFiberEquiv] using hs.tsum_sigma

/-- The neutral current sector sum is the partition function of pinned twisted heights. -/
noncomputable def periodicNeutralHeightSectorWeight {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (w : ℤ × ℤ) : ℝ :=
  ∑' h : periodicPinnedHeights L,
    rotatorCurrentWeight (rotatorIReal β) (periodicTwistedHeightCurrent hL w h)

/-- The sector current sum agrees exactly with its twisted-height partition function. -/
theorem periodicNeutralSectorWeight_eq_twistedHeight {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (w : ℤ × ℤ) :
    periodicNeutralSectorWeight hL β w = periodicNeutralHeightSectorWeight hL β w := by
  unfold periodicNeutralSectorWeight periodicNeutralHeightSectorWeight
  exact (Equiv.tsum_eq (periodicNeutralSectorEquiv hL w)
    (fun q : periodicNeutralCurrentSector hL w =>
      rotatorCurrentWeight (rotatorIReal β) q.1.1)).symm

/-- Every neutral twisted-height sector has strictly positive weight for positive inverse
temperature. -/
theorem periodicNeutralSectorWeight_pos {L : ℕ} [NeZero L]
    (hL : 2 < L) {β : ℝ} (hβ : 0 < β) (w : ℤ × ℤ)
    (hI : Summable (rotatorI β)) : 0 < periodicNeutralSectorWeight hL β w := by
  classical
  have hweight := periodicCurrentWeight_summable (L := L) β hI
  let F := periodicNeutralCurrentSector hL w
  have hF : Summable (fun q : F => |rotatorCurrentWeight (rotatorIReal β) q.1.1|) := by
    apply hweight.comp_injective
    intro q r h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hsum : Summable (fun q : F => rotatorCurrentWeight (rotatorIReal β) q.1.1) :=
    hF.of_norm
  have hcoef : ∀ m : ℤ, 0 < rotatorIReal β m := by
    intro m
    have hp := rotatorI_re_pos hβ m
    rw [rotatorI_eq_realCast] at hp
    exact hp
  let q₀ := periodicNeutralSectorCurrent hL w
    ⟨fun _ => 0, by simp⟩
  have hq₀ : 0 < rotatorCurrentWeight (rotatorIReal β) q₀.1.1 := by
    unfold rotatorCurrentWeight
    exact Finset.prod_pos fun e he => hcoef _
  refine Summable.tsum_pos hsum ?_ q₀ hq₀
  intro q
  unfold rotatorCurrentWeight
  exact Finset.prod_nonneg fun e he => (hcoef (q.1.1 e)).le

/-- Every edge-current weight is strictly positive at positive inverse temperature. -/
theorem periodicCurrentWeight_pos {L : ℕ} [NeZero L]
    (β : ℝ) (hβ : 0 < β) (q : Bond L → ℤ) :
    0 < rotatorCurrentWeight (rotatorIReal β) q := by
  have hcoef : ∀ m : ℤ, 0 < rotatorIReal β m := by
    intro m
    have hp := rotatorI_re_pos hβ m
    rw [rotatorI_eq_realCast] at hp
    exact hp
  unfold rotatorCurrentWeight
  exact Finset.prod_pos fun e he => hcoef (q e)

/-- Every edge-current weight is nonnegative at positive inverse temperature. -/
theorem periodicCurrentWeight_nonneg {L : ℕ} [NeZero L] (β : ℝ) (hβ : 0 < β)
    (q : Bond L → ℤ) : 0 ≤ rotatorCurrentWeight (rotatorIReal β) q :=
  (periodicCurrentWeight_pos (L := L) β hβ q).le

/-- The real winding-sector partition weights are summable, and hence absolutely summable. -/
theorem periodicNeutralSectorWeights_summable {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (hβ : 0 < β) (hI : Summable (rotatorI β)) :
    Summable (fun w : ℤ × ℤ => periodicNeutralSectorWeight hL β w) := by
  classical
  have habs := periodicCurrentWeight_summable (L := L) β hI
  have hcurrent : Summable (fun q : Bond L → ℤ =>
      rotatorCurrentWeight (rotatorIReal β) q) := by
    apply habs.congr
    intro q
    exact abs_of_nonneg (periodicCurrentWeight_nonneg β hβ q)
  have hneutral : Summable (fun q : periodicNeutralCurrents hL =>
      rotatorCurrentWeight (rotatorIReal β) q.1) := by
    change Summable (fun q : {q : Bond L → ℤ // periodicNeutralCurrentPredicate q} =>
      rotatorCurrentWeight (rotatorIReal β) q.1)
    exact hcurrent.subtype (fun q : Bond L → ℤ => periodicNeutralCurrentPredicate q)
  let F : (ℤ × ℤ) → Type _ := fun w => periodicNeutralCurrentSector hL w
  let e := Equiv.sigmaFiberEquiv (fun q : periodicNeutralCurrents hL =>
    periodicNeutralCurrentWinding hL q)
  have hs : Summable (fun s : Σ w, F w =>
      rotatorCurrentWeight (rotatorIReal β) (e s).1) :=
    hneutral.comp_injective e.injective
  have hparts := (summable_sigma_of_nonneg
    (fun s => periodicCurrentWeight_nonneg β hβ (e s).1)).mp hs
  have houter := hparts.2
  change Summable (fun w : ℤ × ℤ => ∑' q : F w,
    rotatorCurrentWeight (rotatorIReal β) (e ⟨w, q⟩).1) at houter
  simpa only [F, e, Equiv.sigmaFiberEquiv_apply, periodicNeutralSectorWeight] using houter

/-- The summand selecting divergence-free currents in the all-current partition series. -/
noncomputable def periodicNeutralCurrentSeriesTerm {L : ℕ}
    (β : ℝ) (q : Bond L → ℤ) : ℂ :=
  by
    classical
    exact if q ∈ Set.ofPred (periodicNeutralCurrentPredicate (L := L)) then
      (rotatorCurrentWeight (rotatorIReal β) q : ℂ) else 0

/-- The neutral all-current sum, grouped exactly by the two integer torus windings. -/
theorem periodicNeutralCurrentSeries_winding {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (hI : Summable (rotatorI β)) :
    (∑' q : Bond L → ℤ, periodicNeutralCurrentSeriesTerm β q) =
      ∑' w : ℤ × ℤ, (periodicNeutralSectorWeight hL β w : ℂ) := by
  classical
  let P := periodicNeutralCurrentPredicate (L := L)
  let g₀ := fun q : Bond L → ℤ =>
    (rotatorCurrentWeight (rotatorIReal β) q : ℂ)
  let N := periodicNeutralCurrents hL
  let f := periodicNeutralCurrentWinding hL
  let g := fun q : N =>
    (rotatorCurrentWeight (rotatorIReal β) q.1 : ℂ)
  have hweight := periodicCurrentWeight_summable (L := L) β hI
  have hsub : Summable g := by
    have ha := hweight.subtype (fun q : Bond L → ℤ => P q)
    have hn : Summable (fun q : {q : Bond L → ℤ // P q} => ‖g q‖) := by
      apply ha.congr
      intro q
      simp [g, Complex.norm_real, Real.norm_eq_abs]
    exact hn.of_norm
  calc
    _ = ∑' q : N, g q := by
      symm
      change (∑' q : ↥(Set.ofPred P), g₀ q.1) =
        ∑' q : Bond L → ℤ, periodicNeutralCurrentSeriesTerm β q
      rw [tsum_subtype (Set.ofPred P) g₀]
      apply tsum_congr
      intro q
      rfl
    _ = ∑' w : ℤ × ℤ, ∑' q : {q : N // f q = w}, g q.1 :=
      tsum_fiberwise f g hsub
    _ = ∑' w : ℤ × ℤ, (periodicNeutralSectorWeight hL β w : ℂ) := by
      apply tsum_congr
      intro w
      change (∑' q : periodicNeutralCurrentSector hL w,
        (rotatorCurrentWeight (rotatorIReal β) q.1.1 : ℂ)) = _
      rw [periodicNeutralSectorWeight, Complex.ofReal_tsum]

/-- The marked twisted current formed from the fixed source path, a pinned height, and a winding
representative. -/
noncomputable def periodicMarkedTwistedHeightCurrent {L : ℕ} [NeZero L]
    (hL : 2 < L) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ)
    (h : periodicPinnedHeights L) : Bond L → ℤ :=
  squareCurrentOfTorus hL
    (torusSourcePathCurrent (squareTorusVertexEquiv L a) (squareTorusVertexEquiv L x) ξ +
      (torusDualGradient h.1 + torusHarmonicCurrent w))

/-- The marked twisted-height sector sum, with the same fixed source path as the current fiber. -/
noncomputable def periodicMarkedHeightSectorWeight {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ) : ℝ :=
  ∑' h : periodicPinnedHeights L,
    rotatorCurrentWeight (rotatorIReal β)
      (periodicMarkedTwistedHeightCurrent hL a x ξ w h)

/-- A pinned height and winding give a marked square current in the corresponding source sector.
-/
noncomputable def periodicMarkedSectorCurrent {L : ℕ} [NeZero L]
    (hL : 2 < L) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ)
    (h : periodicPinnedHeights L) : periodicMarkedCurrentSector hL a x ξ w := by
  classical
  let γ := torusSourcePathCurrent (squareTorusVertexEquiv L a)
    (squareTorusVertexEquiv L x) ξ
  let η := torusDualGradient h.1 + torusHarmonicCurrent w
  let q := squareCurrentOfTorus hL (γ + η)
  have hfreq (v : Site L) :
      currentDivergence (torusGraph L hL) γ (squareTorusVertexEquiv L v) =
        rotatorTwoPointFrequency a x ξ v := by
    rw [torusSourcePathCurrent_divergence]
    simpa using (rotatorTwoPointFrequency_equiv (squareTorusVertexEquiv L)
      a x ξ (squareTorusVertexEquiv L v)).symm
  have hdiv : periodicMarkedCurrentPredicate q a x ξ := by
    intro v
    change currentDivergence (graph L)
      (squareCurrentOfTorus hL (γ + η)) v = rotatorTwoPointFrequency a x ξ v
    rw [squareCurrentOfTorus_divergence, torusDivergence_add_formula,
      torusDivergence_add_formula]
    rw [hfreq, torusDualGradient_divergence_zero,
      torusHarmonicCurrent_divergence_zero]
    ring
  have hback : torusCurrentOfSquare hL q = γ + η := by
    change torusCurrentOfSquare hL (squareCurrentOfTorus hL (γ + η)) = γ + η
    exact torusCurrentOfSquare_squareCurrentOfTorus hL (γ + η)
  have hdiff : torusCurrentOfSquare hL q - γ = η := by
    funext e
    have he := congrFun hback e
    change torusCurrentOfSquare hL q e = γ e + η e at he
    change torusCurrentOfSquare hL q e - γ e = η e
    linarith
  have hwind : periodicMarkedCurrentWinding hL a x ξ q = w := by
    apply Prod.ext
    · change torusWindingX (torusCurrentOfSquare hL q - γ) = w.1
      rw [hdiff, torusWindingX_add_sector,
        torusDualGradient_torusWindingX_zero, torusHarmonicCurrent_torusWindingX]
      ring
    · change torusWindingY (torusCurrentOfSquare hL q - γ) = w.2
      rw [hdiff, torusWindingY_add_sector,
        torusDualGradient_torusWindingY_zero, torusHarmonicCurrent_torusWindingY]
      ring
  exact ⟨q, hdiv, hwind⟩

/-- The pinned height of a marked current after its fixed source path and winding are removed. -/
noncomputable def periodicMarkedSectorHeight {L : ℕ} [NeZero L]
    (hL : 2 < L) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ)
    (q : periodicMarkedCurrentSector hL a x ξ w) : periodicPinnedHeights L :=
  ⟨torusPathHeight
    (torusCurrentOfSquare hL q.1 -
      torusSourcePathCurrent (squareTorusVertexEquiv L a) (squareTorusVertexEquiv L x) ξ -
      torusHarmonicCurrent w),
    torusPathHeight_root _⟩

/-- Every marked winding sector is in bijection with pinned twisted heights. -/
noncomputable def periodicMarkedSectorEquiv {L : ℕ} [NeZero L]
    (hL : 2 < L) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ) :
    periodicPinnedHeights L ≃ periodicMarkedCurrentSector hL a x ξ w where
  toFun := periodicMarkedSectorCurrent hL a x ξ w
  invFun := periodicMarkedSectorHeight hL a x ξ w
  left_inv := by
    intro h
    apply Subtype.ext
    apply torusDualGradient_injective_pinned hL
    · exact (periodicMarkedSectorHeight hL a x ξ w
        (periodicMarkedSectorCurrent hL a x ξ w h)).2
    · exact h.2
    let γ := torusSourcePathCurrent (squareTorusVertexEquiv L a)
      (squareTorusVertexEquiv L x) ξ
    have hq : torusCurrentOfSquare hL
        (periodicMarkedSectorCurrent hL a x ξ w h).1 =
        γ + (torusDualGradient h.1 + torusHarmonicCurrent w) := by
      change torusCurrentOfSquare hL
        (squareCurrentOfTorus hL (γ +
          (torusDualGradient h.1 + torusHarmonicCurrent w))) = _
      rw [torusCurrentOfSquare_squareCurrentOfTorus]
    have hr : torusCurrentOfSquare hL
        (periodicMarkedSectorCurrent hL a x ξ w h).1 - γ -
          torusHarmonicCurrent w = torusDualGradient h.1 := by
      funext e
      have he := congrFun hq e
      change torusCurrentOfSquare hL
        (periodicMarkedSectorCurrent hL a x ξ w h).1 e =
          γ e + (torusDualGradient h.1 e + torusHarmonicCurrent w e) at he
      change torusCurrentOfSquare hL
        (periodicMarkedSectorCurrent hL a x ξ w h).1 e - γ e -
          torusHarmonicCurrent w e = torusDualGradient h.1 e
      linarith
    have hgrad : torusDualGradient
        (torusPathHeight (torusCurrentOfSquare hL
          (periodicMarkedSectorCurrent hL a x ξ w h).1 - γ -
            torusHarmonicCurrent w)) = torusDualGradient h.1 := by
      rw [hr]
      symm
      apply torusPathHeight_eq_torusDualGradient_of_cycle_zeroPeriods hL
      · exact torusDualGradient_divergence_zero hL h.1
      · exact torusDualGradient_torusWindingX_zero h.1
      · exact torusDualGradient_torusWindingY_zero h.1
    exact hgrad
  right_inv := by
    intro q
    apply Subtype.ext
    let γ := torusSourcePathCurrent (squareTorusVertexEquiv L a)
      (squareTorusVertexEquiv L x) ξ
    have qTdiv : ∀ v, currentDivergence (torusGraph L hL)
        (torusCurrentOfSquare hL q.1) v =
          currentDivergence (torusGraph L hL) γ v := by
      intro v
      have hfreq := q.2.1 ((squareTorusVertexEquiv L).symm v)
      calc
        currentDivergence (torusGraph L hL) (torusCurrentOfSquare hL q.1) v =
            currentDivergence (graph L) q.1 ((squareTorusVertexEquiv L).symm v) :=
          torusCurrentOfSquare_divergence hL q.1 v
        _ = rotatorTwoPointFrequency a x ξ ((squareTorusVertexEquiv L).symm v) := hfreq
        _ = rotatorTwoPointFrequency (squareTorusVertexEquiv L a)
            (squareTorusVertexEquiv L x) ξ v :=
          rotatorTwoPointFrequency_equiv (squareTorusVertexEquiv L) a x ξ v
        _ = currentDivergence (torusGraph L hL) γ v :=
          by simpa [γ] using (torusSourcePathCurrent_divergence hL
            (squareTorusVertexEquiv L a) (squareTorusVertexEquiv L x) ξ v).symm
    have hdiffdiv : ∀ v, currentDivergence (torusGraph L hL)
        (torusCurrentOfSquare hL q.1 - γ) v = 0 := by
      intro v
      rw [torusDivergence_sub_formula, qTdiv, sub_self]
    have hw := q.2.2
    dsimp [periodicMarkedCurrentWinding] at hw
    have hw' : (torusWindingX (torusCurrentOfSquare hL q.1 - γ),
        torusWindingY (torusCurrentOfSquare hL q.1 - γ)) = w := by
      simpa [γ] using hw
    have hrwindX : torusWindingX
        (torusCurrentOfSquare hL q.1 - γ - torusHarmonicCurrent w) = 0 := by
      rw [torusWindingX_sub_sector, torusHarmonicCurrent_torusWindingX]
      have hwx := congrArg Prod.fst hw'
      change torusWindingX (torusCurrentOfSquare hL q.1 - γ) = w.1 at hwx
      rw [hwx]
      ring
    have hrwindY : torusWindingY
        (torusCurrentOfSquare hL q.1 - γ - torusHarmonicCurrent w) = 0 := by
      rw [torusWindingY_sub_sector, torusHarmonicCurrent_torusWindingY]
      have hwy := congrArg Prod.snd hw'
      change torusWindingY (torusCurrentOfSquare hL q.1 - γ) = w.2 at hwy
      rw [hwy]
      ring
    have hrdiv : ∀ v, currentDivergence (torusGraph L hL)
        (torusCurrentOfSquare hL q.1 - γ - torusHarmonicCurrent w) v = 0 := by
      intro v
      rw [torusDivergence_sub_formula, hdiffdiv v,
        torusHarmonicCurrent_divergence_zero, sub_zero]
    have hr := torusPathHeight_eq_torusDualGradient_of_cycle_zeroPeriods hL
      (torusCurrentOfSquare hL q.1 - γ - torusHarmonicCurrent w)
      hrdiv hrwindX hrwindY
    have hdecomp : torusCurrentOfSquare hL q.1 =
        γ + (torusDualGradient (periodicMarkedSectorHeight hL a x ξ w q).1 +
          torusHarmonicCurrent w) := by
      funext e
      have he := congrFun hr e
      change torusCurrentOfSquare hL q.1 e - γ e - torusHarmonicCurrent w e =
        torusDualGradient
          (torusPathHeight (torusCurrentOfSquare hL q.1 - γ - torusHarmonicCurrent w)) e at he
      change torusCurrentOfSquare hL q.1 e = γ e +
        (torusDualGradient
          (torusPathHeight (torusCurrentOfSquare hL q.1 - γ - torusHarmonicCurrent w)) e +
          torusHarmonicCurrent w e)
      linear_combination he
    have hback := squareCurrentOfTorus_torusCurrentOfSquare hL q.1
    funext e
    have he := congrFun hback e
    change squareCurrentOfTorus hL
      (γ + (torusDualGradient (periodicMarkedSectorHeight hL a x ξ w q).1 +
        torusHarmonicCurrent w)) e = q.1 e
    rw [← hdecomp]
    exact he


/-- The marked sector sum agrees exactly with its fixed-path twisted-height partition function. -/
theorem periodicMarkedSectorWeight_eq_twistedHeight {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ) :
    periodicMarkedSectorWeight hL β a x ξ w =
      periodicMarkedHeightSectorWeight hL β a x ξ w := by
  unfold periodicMarkedSectorWeight periodicMarkedHeightSectorWeight
  exact (Equiv.tsum_eq (periodicMarkedSectorEquiv hL a x ξ w)
    (fun q : periodicMarkedCurrentSector hL a x ξ w =>
      rotatorCurrentWeight (rotatorIReal β) q.1)).symm

/-- Every marked twisted-height sector has strictly positive weight for positive inverse
temperature. -/
theorem periodicMarkedSectorWeight_pos {L : ℕ} [NeZero L]
    (hL : 2 < L) {β : ℝ} (hβ : 0 < β) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ)
    (hI : Summable (rotatorI β)) : 0 < periodicMarkedSectorWeight hL β a x ξ w := by
  classical
  have hweight := periodicCurrentWeight_summable (L := L) β hI
  let F := periodicMarkedCurrentSector hL a x ξ w
  have hF : Summable (fun q : F => |rotatorCurrentWeight (rotatorIReal β) q.1|) := by
    apply hweight.comp_injective
    intro q r h
    exact Subtype.ext h
  have hsum : Summable (fun q : F => rotatorCurrentWeight (rotatorIReal β) q.1) :=
    hF.of_norm
  let h₀ : periodicPinnedHeights L := ⟨fun _ => 0, by simp⟩
  let q₀ := periodicMarkedSectorCurrent hL a x ξ w h₀
  have hq₀ : 0 < rotatorCurrentWeight (rotatorIReal β) q₀.1 :=
    periodicCurrentWeight_pos β hβ q₀.1
  refine Summable.tsum_pos hsum ?_ q₀ hq₀
  intro q
  exact periodicCurrentWeight_nonneg β hβ q.1

/-- The real marked winding-sector weights are summable. -/
theorem periodicMarkedSectorWeights_summable {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (hβ : 0 < β) (a x : Site L) (ξ : ℤ)
    (hI : Summable (rotatorI β)) :
    Summable (fun w : ℤ × ℤ => periodicMarkedSectorWeight hL β a x ξ w) := by
  classical
  have habs := periodicCurrentWeight_summable (L := L) β hI
  have hcurrent : Summable (fun q : Bond L → ℤ =>
      rotatorCurrentWeight (rotatorIReal β) q) := by
    apply habs.congr
    intro q
    exact abs_of_nonneg (periodicCurrentWeight_nonneg β hβ q)
  have hmarked : Summable (fun q : periodicMarkedCurrents a x ξ =>
      rotatorCurrentWeight (rotatorIReal β) q.1) := by
    change Summable (fun q : {q : Bond L → ℤ // periodicMarkedCurrentPredicate q a x ξ} =>
      rotatorCurrentWeight (rotatorIReal β) q.1)
    exact hcurrent.subtype (fun q : Bond L → ℤ => periodicMarkedCurrentPredicate q a x ξ)
  let F : (ℤ × ℤ) → Type _ := fun w => periodicMarkedCurrentsFiber hL a x ξ w
  let e := Equiv.sigmaFiberEquiv (fun q : periodicMarkedCurrents a x ξ =>
    periodicMarkedCurrentsWinding hL a x ξ q)
  have hs : Summable (fun s : Σ w, F w =>
      rotatorCurrentWeight (rotatorIReal β) (e s).1) :=
    hmarked.comp_injective e.injective
  have hparts := (summable_sigma_of_nonneg
    (fun s => periodicCurrentWeight_nonneg β hβ (e s).1)).mp hs
  have houter : Summable (fun w : ℤ × ℤ =>
      ∑' q : F w, rotatorCurrentWeight (rotatorIReal β) (e ⟨w, q⟩).1) := hparts.2
  have houter' : Summable (fun w : ℤ × ℤ =>
      ∑' q : periodicMarkedCurrentsFiber hL a x ξ w,
        rotatorCurrentWeight (rotatorIReal β) q.1.1) := by
    apply houter.congr
    intro w
    apply tsum_congr
    intro q
    rfl
  apply houter'.congr
  intro w
  unfold periodicMarkedSectorWeight
  exact Equiv.tsum_eq (periodicMarkedCurrentsFiberEquiv hL a x ξ w)
    (fun q : periodicMarkedCurrentSector hL a x ξ w =>
      rotatorCurrentWeight (rotatorIReal β) q.1)

/-- The summand selecting a prescribed marked divergence in the all-current series. -/
noncomputable def periodicMarkedCurrentSeriesTerm {L : ℕ}
    (β : ℝ) (a x : Site L) (ξ : ℤ) (q : Bond L → ℤ) : ℂ := by
  classical
  exact if q ∈ Set.ofPred (fun j : Bond L → ℤ =>
      periodicMarkedCurrentPredicate j a x ξ) then
    (rotatorCurrentWeight (rotatorIReal β) q : ℂ) else 0

/-- The marked all-current sum, grouped exactly by relative winding after the fixed source path is
subtracted. -/
theorem periodicMarkedCurrentSeries_winding {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (a x : Site L) (ξ : ℤ) (hI : Summable (rotatorI β)) :
    (∑' q : Bond L → ℤ, periodicMarkedCurrentSeriesTerm β a x ξ q) =
      ∑' w : ℤ × ℤ, (periodicMarkedSectorWeight hL β a x ξ w : ℂ) := by
  classical
  let P := fun q : Bond L → ℤ => periodicMarkedCurrentPredicate q a x ξ
  let g₀ := fun q : Bond L → ℤ =>
    (rotatorCurrentWeight (rotatorIReal β) q : ℂ)
  let N := periodicMarkedCurrents a x ξ
  let f := periodicMarkedCurrentsWinding hL a x ξ
  let g := fun q : N => (rotatorCurrentWeight (rotatorIReal β) q.1 : ℂ)
  have hweight := periodicCurrentWeight_summable (L := L) β hI
  have hsub : Summable g := by
    have ha := hweight.subtype (fun q : Bond L → ℤ => P q)
    have hn : Summable (fun q : {q : Bond L → ℤ // P q} => ‖g q‖) := by
      apply ha.congr
      intro q
      simp [g, Complex.norm_real, Real.norm_eq_abs]
    exact hn.of_norm
  calc
    _ = ∑' q : N, g q := by
      symm
      change (∑' q : ↥(Set.ofPred P), g₀ q.1) =
        ∑' q : Bond L → ℤ, periodicMarkedCurrentSeriesTerm β a x ξ q
      rw [tsum_subtype (Set.ofPred P) g₀]
      apply tsum_congr
      intro q
      rfl
    _ = ∑' w : ℤ × ℤ, ∑' q : {q : N // f q = w}, g q.1 :=
      tsum_fiberwise f g hsub
    _ = ∑' w : ℤ × ℤ, (periodicMarkedSectorWeight hL β a x ξ w : ℂ) := by
      apply tsum_congr
      intro w
      change (∑' q : periodicMarkedCurrentsFiber hL a x ξ w,
          (rotatorCurrentWeight (rotatorIReal β) q.1.1 : ℂ)) = _
      calc
        _ = ∑' q : periodicMarkedCurrentSector hL a x ξ w,
            (rotatorCurrentWeight (rotatorIReal β) q.1 : ℂ) :=
          Equiv.tsum_eq (periodicMarkedCurrentsFiberEquiv hL a x ξ w)
            (fun q : periodicMarkedCurrentSector hL a x ξ w =>
              (rotatorCurrentWeight (rotatorIReal β) q.1 : ℂ))
        _ = _ := by
          rw [periodicMarkedSectorWeight, Complex.ofReal_tsum]

/-- Absolute convergence of the neutral winding-sector partition series. -/
theorem periodicNeutralSectorWeights_absSummable {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (hβ : 0 < β) (hI : Summable (rotatorI β)) :
    Summable (fun w : ℤ × ℤ => |periodicNeutralSectorWeight hL β w|) := by
  apply (periodicNeutralSectorWeights_summable hL β hβ hI).congr
  intro w
  exact (abs_of_nonneg (periodicNeutralSectorWeight_pos hL hβ w hI).le).symm

/-- Absolute convergence of the marked winding-sector numerator series. -/
theorem periodicMarkedSectorWeights_absSummable {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (hβ : 0 < β) (a x : Site L) (ξ : ℤ)
    (hI : Summable (rotatorI β)) :
    Summable (fun w : ℤ × ℤ => |periodicMarkedSectorWeight hL β a x ξ w|) := by
  apply (periodicMarkedSectorWeights_summable hL β hβ a x ξ hI).congr
  intro w
  exact (abs_of_nonneg (periodicMarkedSectorWeight_pos hL hβ a x ξ w hI).le).symm

/-- Exact partition identity, written as a sum of pinned twisted-height sectors. -/
theorem partitionIntegral_windingSectorIdentity {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (hI : Summable (rotatorI β)) :
    (partitionIntegral L β : ℂ) =
      (∑' w : ℤ × ℤ, (periodicNeutralSectorWeight hL β w : ℂ)) *
        (2 * Real.pi : ℂ) ^ Fintype.card (Site L) := by
  rw [partitionIntegral_currentIdentity (L := L) β hI]
  apply congrArg (fun z : ℂ => z * (2 * Real.pi : ℂ) ^ Fintype.card (Site L))
  calc
    _ = ∑' q : Bond L → ℤ, periodicNeutralCurrentSeriesTerm β q := by
      apply tsum_congr
      intro q
      simp [periodicNeutralCurrentSeriesTerm, Set.mem_ofPred_eq,
        periodicNeutralCurrentPredicate]
    _ = _ := periodicNeutralCurrentSeries_winding hL β hI

/-- Exact marked-character identity, with fixed-path twisted-height sectors and the original
raw-angle volume factor. -/
theorem markedIntegral_windingSectorIdentity {L : ℕ} [NeZero L]
    (hL : 2 < L) (β : ℝ) (a x : Site L) (ξ : ℤ) (hI : Summable (rotatorI β)) :
    markedIntegral L β a x ξ =
      (∑' w : ℤ × ℤ, (periodicMarkedSectorWeight hL β a x ξ w : ℂ)) *
        (2 * Real.pi : ℂ) ^ Fintype.card (Site L) := by
  rw [markedIntegral_currentIdentity (L := L) β hI a x ξ]
  apply congrArg (fun z : ℂ => z * (2 * Real.pi : ℂ) ^ Fintype.card (Site L))
  calc
    _ = ∑' q : Bond L → ℤ, periodicMarkedCurrentSeriesTerm β a x ξ q := by
      apply tsum_congr
      intro q
      simp [periodicMarkedCurrentSeriesTerm, Set.mem_ofPred_eq,
        periodicMarkedCurrentPredicate]
    _ = _ := periodicMarkedCurrentSeries_winding hL β a x ξ hI

end FroehlichSpencer.BKT.Rotator.Periodic

end
