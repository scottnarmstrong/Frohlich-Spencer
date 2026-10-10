/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.DualCarrier
public import FroehlichSpencer.BKT.Lattice2D.C64

/-!
# Periodic logarithmic harmonic fields

The real torus cycle decomposition and the Green flow give a periodic analogue of the explicit
free-box harmonic field used in Theorem C.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open Multigraph

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {L : ℕ} [NeZero L]

/-- Real divergence on the right/up torus, in the current convention. -/
def torusRealDivergence (q : TorusEdge L → ℝ) (v : TorusVertex L) : ℝ :=
  q (v, false) + q (v, true) - q ((v.1 - 1, v.2), false) - q ((v.1, v.2 - 1), true)

/-- Horizontal flux through a vertical torus cut. -/
def torusRealHorizontalPeriod (q : TorusEdge L → ℝ) (x : ZMod L) : ℝ :=
  ∑ y : ZMod L, q ((x, y), false)

/-- Vertical flux through a horizontal torus cut. -/
def torusRealVerticalPeriod (q : TorusEdge L → ℝ) (y : ZMod L) : ℝ :=
  ∑ x : ZMod L, q ((x, y), true)

/-- The real current along the first `n` positive horizontal steps. -/
def torusRealHorizontalPathSum (q : TorusEdge L → ℝ) (x : ZMod L) (n : ℕ) : ℝ :=
  ∑ k : Fin n, q ((x, ((k.val + 1 : ℕ) : ZMod L)), false)

/-- The real current along the first `n` positive vertical steps. -/
def torusRealVerticalPathSum (q : TorusEdge L → ℝ) (n : ℕ) (y : ZMod L) : ℝ :=
  ∑ k : Fin n, q ((((k.val + 1 : ℕ) : ZMod L), y), true)

/-- The real height obtained by integrating a zero-period cycle along coordinate paths. -/
def torusRealPathHeight (q : TorusEdge L → ℝ) (p : TorusVertex L) : ℝ :=
  torusRealHorizontalPathSum q 0 p.2.val - torusRealVerticalPathSum q p.1.val p.2

private theorem sum_shift_prev_real (f : ZMod L → ℝ) :
    (∑ x : ZMod L, f (x - 1)) = ∑ x : ZMod L, f x := by
  simpa [sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L)) f)

/-- A real divergence-free cycle has constant horizontal flux across cuts. -/
theorem torusRealHorizontalPeriod_succ (_hL : 2 < L) (q : TorusEdge L → ℝ) (x : ZMod L)
    (hdiv : ∀ v, torusRealDivergence q v = 0) :
    torusRealHorizontalPeriod q (x + 1) = torusRealHorizontalPeriod q x := by
  have hpoint (y : ZMod L) :
      q ((x + 1, y), false) - q ((x, y), false) =
        q ((x + 1, y - 1), true) - q ((x + 1, y), true) := by
    have h := hdiv (x + 1, y)
    simp only [torusRealDivergence] at h
    have hcoord : x + 1 - 1 = x := by abel
    rw [hcoord] at h
    linarith
  have hsum :
      (∑ y : ZMod L, (q ((x + 1, y), false) - q ((x, y), false))) =
        ∑ y : ZMod L, (q ((x + 1, y - 1), true) - q ((x + 1, y), true)) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hpoint y
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  have hshift : (∑ y : ZMod L, q ((x + 1, y - 1), true)) =
      ∑ y : ZMod L, q ((x + 1, y), true) :=
    sum_shift_prev_real (fun y => q ((x + 1, y), true))
  rw [hshift] at hsum
  unfold torusRealHorizontalPeriod
  linarith

/-- A real divergence-free cycle has constant vertical flux across cuts. -/
theorem torusRealVerticalPeriod_succ (_hL : 2 < L) (q : TorusEdge L → ℝ) (y : ZMod L)
    (hdiv : ∀ v, torusRealDivergence q v = 0) :
    torusRealVerticalPeriod q (y + 1) = torusRealVerticalPeriod q y := by
  have hpoint (x : ZMod L) :
      q ((x, y + 1), true) - q ((x, y), true) =
        q ((x - 1, y + 1), false) - q ((x, y + 1), false) := by
    have h := hdiv (x, y + 1)
    simp only [torusRealDivergence] at h
    have hcoord : y + 1 - 1 = y := by abel
    rw [hcoord] at h
    linarith
  have hsum :
      (∑ x : ZMod L, (q ((x, y + 1), true) - q ((x, y), true))) =
        ∑ x : ZMod L, (q ((x - 1, y + 1), false) - q ((x, y + 1), false)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hpoint x
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  have hshift : (∑ x : ZMod L, q ((x - 1, y + 1), false)) =
      ∑ x : ZMod L, q ((x, y + 1), false) :=
    sum_shift_prev_real (fun x => q ((x, y + 1), false))
  rw [hshift] at hsum
  unfold torusRealVerticalPeriod
  linarith

private theorem torusRealHorizontalPeriod_const (hL : 2 < L) (q : TorusEdge L → ℝ)
    (x : ZMod L) (hdiv : ∀ v, torusRealDivergence q v = 0) :
    torusRealHorizontalPeriod q x = torusRealHorizontalPeriod q 0 := by
  have hnat : ∀ n : ℕ, torusRealHorizontalPeriod q (n : ZMod L) =
      torusRealHorizontalPeriod q 0 := by
    intro n
    induction n with
    | zero => simp [torusRealHorizontalPeriod]
    | succ n ih => rw [Nat.cast_succ, torusRealHorizontalPeriod_succ hL q _ hdiv, ih]
  simpa [torusRealHorizontalPeriod, ZMod.natCast_zmod_val] using hnat x.val

private theorem torusRealVerticalPeriod_const (hL : 2 < L) (q : TorusEdge L → ℝ)
    (y : ZMod L) (hdiv : ∀ v, torusRealDivergence q v = 0) :
    torusRealVerticalPeriod q y = torusRealVerticalPeriod q 0 := by
  have hnat : ∀ n : ℕ, torusRealVerticalPeriod q (n : ZMod L) =
      torusRealVerticalPeriod q 0 := by
    intro n
    induction n with
    | zero => simp [torusRealVerticalPeriod]
    | succ n ih => rw [Nat.cast_succ, torusRealVerticalPeriod_succ hL q _ hdiv, ih]
  simpa [torusRealVerticalPeriod, ZMod.natCast_zmod_val] using hnat y.val

private theorem finEquiv_succ_cast_real {n : ℕ} (i : Fin n) :
    ZMod.finEquiv (n + 1) i.succ = ((i.val + 1 : ℕ) : ZMod (n + 1)) := by
  have hv : (ZMod.finEquiv (n + 1) i.succ).val = i.val + 1 := by
    change i.succ.val = i.val + 1
    exact Fin.val_succ i
  calc
    ZMod.finEquiv (n + 1) i.succ =
        ((ZMod.finEquiv (n + 1) i.succ).val : ZMod (n + 1)) :=
      (ZMod.natCast_zmod_val _).symm
    _ = ((i.val + 1 : ℕ) : ZMod (n + 1)) := by rw [hv]

private theorem torusRealHorizontalPeriod_eq_root_add_path (q : TorusEdge L → ℝ)
    (x : ZMod L) :
    torusRealHorizontalPeriod q x = q ((x, 0), false) +
      torusRealHorizontalPathSum q x (L - 1) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hsum : torusRealHorizontalPeriod (L := n + 1) q x =
        ∑ i : Fin (n + 1), q ((x, ZMod.finEquiv (n + 1) i), false) := by
      unfold torusRealHorizontalPeriod
      exact (Equiv.sum_comp (ZMod.finEquiv (n + 1)).toEquiv
        (fun y => q ((x, y), false))).symm
    have hroot : ZMod.finEquiv (n + 1) (0 : Fin (n + 1)) = 0 := rfl
    have htail :
        (∑ i : Fin n, q ((x, ZMod.finEquiv (n + 1) i.succ), false)) =
          torusRealHorizontalPathSum q x n := by
      unfold torusRealHorizontalPathSum
      apply Finset.sum_congr rfl
      intro i hi
      rw [finEquiv_succ_cast_real]
    calc
      torusRealHorizontalPeriod q x =
          q ((x, ZMod.finEquiv (n + 1) 0), false) +
            ∑ i : Fin n, q ((x, ZMod.finEquiv (n + 1) i.succ), false) := by
        rw [hsum, Fin.sum_univ_succ]
      _ = q ((x, 0), false) + torusRealHorizontalPathSum q x n := by rw [hroot, htail]
      _ = _ := by simp

private theorem torusRealVerticalPeriod_eq_root_add_path (q : TorusEdge L → ℝ)
    (y : ZMod L) :
    torusRealVerticalPeriod q y = q ((0, y), true) +
      torusRealVerticalPathSum q (L - 1) y := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hsum : torusRealVerticalPeriod (L := n + 1) q y =
        ∑ i : Fin (n + 1), q ((ZMod.finEquiv (n + 1) i, y), true) := by
      unfold torusRealVerticalPeriod
      exact (Equiv.sum_comp (ZMod.finEquiv (n + 1)).toEquiv
        (fun x => q ((x, y), true))).symm
    have hroot : ZMod.finEquiv (n + 1) (0 : Fin (n + 1)) = 0 := rfl
    have htail :
        (∑ i : Fin n, q ((ZMod.finEquiv (n + 1) i.succ, y), true)) =
          torusRealVerticalPathSum q n y := by
      unfold torusRealVerticalPathSum
      apply Finset.sum_congr rfl
      intro i hi
      rw [finEquiv_succ_cast_real]
    calc
      torusRealVerticalPeriod q y =
          q ((ZMod.finEquiv (n + 1) 0, y), true) +
            ∑ i : Fin n, q ((ZMod.finEquiv (n + 1) i.succ, y), true) := by
        rw [hsum, Fin.sum_univ_succ]
      _ = q ((0, y), true) + torusRealVerticalPathSum q n y := by rw [hroot, htail]
      _ = _ := by simp

omit [NeZero L] in
theorem torusRealVerticalPathSum_succ (q : TorusEdge L → ℝ) (n : ℕ) (j : ZMod L) :
    torusRealVerticalPathSum q (n + 1) j = torusRealVerticalPathSum q n j +
      q ((((n + 1 : ℕ) : ZMod L), j), true) := by
  simp [torusRealVerticalPathSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

omit [NeZero L] in
theorem torusRealHorizontalPathSum_succ (q : TorusEdge L → ℝ) (i : ZMod L) (n : ℕ) :
    torusRealHorizontalPathSum q i (n + 1) = torusRealHorizontalPathSum q i n +
      q ((i, ((n + 1 : ℕ) : ZMod L)), false) := by
  simp [torusRealHorizontalPathSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

omit [NeZero L] in
private theorem zmod_one_val_real (hL : 2 < L) : (1 : ZMod L).val = 1 := by
  exact @ZMod.val_one L ⟨by omega⟩

omit [NeZero L] in
theorem torusRealPathHeight_root (q : TorusEdge L → ℝ) : torusRealPathHeight q (0, 0) = 0 := by
  simp [torusRealPathHeight, torusRealHorizontalPathSum, torusRealVerticalPathSum]

theorem torusRealPathHeight_vertical_nonzero (hL : 2 < L) (q : TorusEdge L → ℝ)
    (i j : ZMod L) (hi : 0 < i.val) :
    torusRealPathHeight q (i - 1, j) - torusRealPathHeight q (i, j) = q ((i, j), true) := by
  have hval : (i - 1).val = i.val - 1 := by
    rw [ZMod.val_sub (by rw [zmod_one_val_real hL]; omega), zmod_one_val_real hL]
  have hsucc : i.val - 1 + 1 = i.val := Nat.sub_add_cancel (by omega)
  have hcast : ((i.val - 1 + 1 : ℕ) : ZMod L) = i := by
    rw [hsucc]
    exact ZMod.natCast_zmod_val i
  have hsum : torusRealVerticalPathSum q i.val j =
      torusRealVerticalPathSum q (i.val - 1) j + q ((i, j), true) := by
    calc
      torusRealVerticalPathSum q i.val j =
          torusRealVerticalPathSum q (i.val - 1 + 1) j := by rw [hsucc]
      _ = torusRealVerticalPathSum q (i.val - 1) j +
          q (((i.val - 1 + 1 : ℕ), j), true) :=
        torusRealVerticalPathSum_succ q (i.val - 1) j
      _ = _ := by rw [hcast]
  unfold torusRealPathHeight
  rw [hval, hsum]
  ring

theorem torusRealPathHeight_horizontal_base_nonzero (hL : 2 < L)
    (q : TorusEdge L → ℝ) (j : ZMod L) (hj : 0 < j.val) :
    torusRealPathHeight q (0, j) - torusRealPathHeight q (0, j - 1) = q ((0, j), false) := by
  have hval : (j - 1).val = j.val - 1 := by
    rw [ZMod.val_sub (by rw [zmod_one_val_real hL]; omega), zmod_one_val_real hL]
  have hsucc : j.val - 1 + 1 = j.val := Nat.sub_add_cancel (by omega)
  have hcast : ((j.val - 1 + 1 : ℕ) : ZMod L) = j := by
    rw [hsucc]
    exact ZMod.natCast_zmod_val j
  have hsum : torusRealHorizontalPathSum q 0 j.val =
      torusRealHorizontalPathSum q 0 (j.val - 1) + q ((0, j), false) := by
    calc
      torusRealHorizontalPathSum q 0 j.val =
          torusRealHorizontalPathSum q 0 (j.val - 1 + 1) := by rw [hsucc]
      _ = torusRealHorizontalPathSum q 0 (j.val - 1) +
          q ((0, (j.val - 1 + 1 : ℕ)), false) :=
        torusRealHorizontalPathSum_succ q 0 (j.val - 1)
      _ = _ := by rw [hcast]
  have hz1 : torusRealVerticalPathSum q 0 j = 0 := by
    simp [torusRealVerticalPathSum]
  have hz2 : torusRealVerticalPathSum q 0 (j - 1) = 0 := by
    simp [torusRealVerticalPathSum]
  simp only [torusRealPathHeight, ZMod.val_zero]
  rw [hval, hsum, hz1, hz2]
  ring

private theorem torusRealPathHeight_horizontal_base_zero (hL : 2 < L)
    (q : TorusEdge L → ℝ) (hperiod : torusRealHorizontalPeriod q 0 = 0) :
    torusRealPathHeight q (0, 0) - torusRealPathHeight q (0, -1) =
      q ((0, 0), false) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hper := torusRealHorizontalPeriod_eq_root_add_path (L := n + 1) q 0
    have hper' : 0 = q ((0, 0), false) + torusRealHorizontalPathSum q 0 n := by
      simpa using hperiod.symm.trans hper
    have hpath : torusRealPathHeight q (0, -1) =
        torusRealHorizontalPathSum q 0 n := by
      simp [torusRealPathHeight, torusRealVerticalPathSum, ZMod.val_neg_one]
    rw [torusRealPathHeight_root, hpath]
    linarith

private theorem torusRealPathHeight_vertical_base_zero (hL : 2 < L)
    (q : TorusEdge L → ℝ) (j : ZMod L) (hperiod : torusRealVerticalPeriod q j = 0) :
    torusRealPathHeight q (-1, j) - torusRealPathHeight q (0, j) =
      q ((0, j), true) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hper := torusRealVerticalPeriod_eq_root_add_path (L := n + 1) q j
    have hper' : 0 = q ((0, j), true) + torusRealVerticalPathSum q n j := by
      simpa using hperiod.symm.trans hper
    have hleft : torusRealPathHeight q (-1, j) =
        torusRealHorizontalPathSum q 0 j.val - torusRealVerticalPathSum q n j := by
      simp [torusRealPathHeight, ZMod.val_neg_one]
    have hright : torusRealPathHeight q (0, j) =
        torusRealHorizontalPathSum q 0 j.val := by
      simp [torusRealPathHeight, torusRealVerticalPathSum]
    rw [hleft, hright]
    linarith

private theorem torusRealPathHeight_vertical_current (hL : 2 < L)
    (q : TorusEdge L → ℝ) (i j : ZMod L) (hperiod : torusRealVerticalPeriod q j = 0) :
    torusRealPathHeight q (i - 1, j) - torusRealPathHeight q (i, j) =
      q ((i, j), true) := by
  by_cases hi : i = 0
  · subst i
    simpa using torusRealPathHeight_vertical_base_zero hL q j hperiod
  · exact torusRealPathHeight_vertical_nonzero hL q i j (ZMod.val_pos.mpr hi)

private theorem torusRealPathHeight_horizontal_current (hL : 2 < L)
    (q : TorusEdge L → ℝ) (i j : ZMod L)
    (hdiv : ∀ v, torusRealDivergence q v = 0)
    (hperiod : torusRealHorizontalPeriod q 0 = 0)
    (hperiodV : ∀ y, torusRealVerticalPeriod q y = 0) :
    q ((i, j), false) = torusRealPathHeight q (i, j) -
      torusRealPathHeight q (i, j - 1) := by
  have hbase (y : ZMod L) : q ((0, y), false) =
      torusRealPathHeight q (0, y) - torusRealPathHeight q (0, y - 1) := by
    by_cases hy : y = 0
    · subst y
      simpa using (torusRealPathHeight_horizontal_base_zero hL q hperiod).symm
    · exact (torusRealPathHeight_horizontal_base_nonzero hL q y
        (ZMod.val_pos.mpr hy)).symm
  have hnat : ∀ k : ℕ, k < L → ∀ y : ZMod L,
      q ((((k : ℕ) : ZMod L), y), false) =
        torusRealPathHeight q (((k : ℕ) : ZMod L), y) -
          torusRealPathHeight q (((k : ℕ) : ZMod L), y - 1) := by
    intro k
    induction k with
    | zero => intro hk y; simpa using hbase y
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
      simp only [torusRealDivergence] at hdivx
      rw [hcoord] at hdivx
      have hv := torusRealPathHeight_vertical_current hL q x y (hperiodV y)
      have hv' := torusRealPathHeight_vertical_current hL q x (y - 1) (hperiodV (y - 1))
      rw [hcoord] at hv hv'
      rw [hprev] at hdivx
      have hnew : q ((x, y), false) =
          torusRealPathHeight q (x, y) - torusRealPathHeight q (x, y - 1) := by
        linarith
      simpa [x] using hnew
  have hresult := hnat i.val i.val_lt j
  rw [ZMod.natCast_zmod_val i] at hresult
  exact hresult

/-- A divergence-free real torus current with zero periods is a dual gradient. -/
theorem torusRealCycle_eq_dualGradient (hL : 2 < L) (q : TorusEdge L → ℝ)
    (hdiv : ∀ v, torusRealDivergence q v = 0)
    (hwindX : torusRealHorizontalPeriod q 0 = 0)
    (hwindY : torusRealVerticalPeriod q 0 = 0) :
    q = torusDualGradientReal (torusRealPathHeight q) := by
  have hperiodX : torusRealHorizontalPeriod q 0 = 0 := hwindX
  have hperiodY : torusRealVerticalPeriod q 0 = 0 := hwindY
  have hperiodV : ∀ y, torusRealVerticalPeriod q y = 0 := by
    intro y
    rw [torusRealVerticalPeriod_const hL q y hdiv]
    exact hperiodY
  funext e
  rcases e with ⟨p, d⟩
  cases d
  · exact torusRealPathHeight_horizontal_current hL q p.1 p.2 hdiv hperiodX hperiodV
  · simpa [torusDualGradientReal] using
      (torusRealPathHeight_vertical_current hL q p.1 p.2 (hperiodV p.2)).symm

/-- Swap the two torus coordinates. -/
def torusCoordinateSwapEquiv : TorusVertex L ≃ TorusVertex L where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The corresponding swap of oriented edges. -/
def torusEdgeSwapEquiv : TorusEdge L ≃ TorusEdge L where
  toFun e := ((e.1.2, e.1.1), !e.2)
  invFun e := ((e.1.2, e.1.1), !e.2)
  left_inv e := by cases e with | mk p d => cases p; cases d <;> rfl
  right_inv e := by cases e with | mk p d => cases p; cases d <;> rfl

/-- Coordinate transposition is an automorphism of the right/up torus graph. -/
def torusCoordinateSwapIso (hL : 2 < L) :
    Multigraph.Isomorphism (torusGraph L hL) (torusGraph L hL) where
  vertices := torusCoordinateSwapEquiv
  edges := torusEdgeSwapEquiv
  endpoints e := by
    rcases e with ⟨⟨x, y⟩, d⟩
    cases d <;> simp [torusCoordinateSwapEquiv, torusEdgeSwapEquiv,
      torusGraph, torusStep]

private theorem greenBilinear_coordinateSwap (hL : 2 < L)
    (p q : TorusVertex L) :
    greenBilinear (torusGraph L hL) (torusGraph_connected L hL)
      (dipole (p.2, p.1) (q.2, q.1)) (dipole (p.2, p.1) (q.2, q.1)) =
    greenBilinear (torusGraph L hL) (torusGraph_connected L hL)
      (dipole p q) (dipole p q) := by
  let I := torusCoordinateSwapIso hL
  have hpush : I.pushField (dipole p q) = dipole (p.2, p.1) (q.2, q.1) := by
    funext v
    have hs (a b : TorusVertex L) : (a.2, a.1) = b ↔ a = (b.2, b.1) := by
      rcases a with ⟨a₁, a₂⟩
      rcases b with ⟨b₁, b₂⟩
      simp only [Prod.mk.injEq]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩
    simp [dipole, Multigraph.Isomorphism.pushField, I,
      torusCoordinateSwapIso, torusCoordinateSwapEquiv, hs]
  calc
    _ = greenBilinear (torusGraph L hL) (torusGraph_connected L hL)
        (I.pushField (dipole p q)) (I.pushField (dipole p q)) := by rw [hpush]
    _ = _ := by
      unfold greenBilinear
      rw [← I.greenOp_transport (torusGraph_connected L hL) (dipole p q)]
      exact I.pairing_transport (dipole p q) (-((torusGraph L hL).greenOp
        (torusGraph_connected L hL) (dipole p q)))

/-- The vertical axis version of the C6.4 Green energy estimate. -/
theorem torusGreenBilinear_vertical_dipole_log_upper_bound (hL : 2 < L)
    (p : TorusVertex L) (m : ℕ) (hm : m ≤ L) :
    greenBilinear (torusGraph L hL) (torusGraph_connected L hL)
      (dipole p (p + (0, (m : ZMod L)))) (dipole p (p + (0, (m : ZMod L)))) ≤
      82 * Real.log (((torusCyclicAxisDistance L m) + 1 : ℕ) : ℝ) := by
  have h := torusGreenBilinear_horizontal_dipole_log_upper_bound hL
    (torusGraph_connected L hL) (p.2, p.1) m hm
  have hswap := greenBilinear_coordinateSwap hL p (p + (0, (m : ZMod L)))
  rw [← hswap]
  have hadd : ((p.2, p.1) + ((m : ZMod L), 0)) =
      ((p + (0, (m : ZMod L))).2, (p + (0, (m : ZMod L))).1) := by
    ext <;> simp
  simpa [hadd] using h

/-- Any torus dipole has Green energy bounded by a logarithm of the sum of its cyclic coordinate
distances. -/
theorem torusGreenBilinear_dipole_torusRadius_log_upper_bound (hL : 2 < L)
    (p q : TorusVertex L) :
    greenBilinear (torusGraph L hL) (torusGraph_connected L hL) (dipole p q) (dipole p q) ≤
      328 * Real.log (((torusRadius p q) + 1 : ℕ) : ℝ) := by
  let dx := (q.1 - p.1).val
  let dy := (q.2 - p.2).val
  let r : TorusVertex L := (q.1, p.2)
  have hdx : q.1 = p.1 + (dx : ZMod L) := by
    dsimp only [dx]
    have hval : ((q.1 - p.1).val : ZMod L) = q.1 - p.1 :=
      ZMod.natCast_zmod_val _
    calc
      q.1 = p.1 + (q.1 - p.1) := by abel
      _ = p.1 + ((q.1 - p.1).val : ZMod L) := congrArg (p.1 + ·) hval.symm
  have hdy : q.2 = p.2 + (dy : ZMod L) := by
    dsimp only [dy]
    have hval : ((q.2 - p.2).val : ZMod L) = q.2 - p.2 :=
      ZMod.natCast_zmod_val _
    calc
      q.2 = p.2 + (q.2 - p.2) := by abel
      _ = p.2 + ((q.2 - p.2).val : ZMod L) := congrArg (p.2 + ·) hval.symm
  have hdecomp : dipole p q = dipole p r + dipole r q := by
    funext v
    simp [dipole, r]
  let f : TorusVertex L → ℝ := dipole p r
  let g : TorusVertex L → ℝ := dipole r q
  let R := torusRadius p q
  let K : ℝ := 82 * Real.log (((R + 1 : ℕ) : ℝ))
  have hRpos : 0 < ((R + 1 : ℕ) : ℝ) := by positivity
  have hcycX : torusCyclicAxisDistance L dx ≤ R := by
    dsimp [R, torusRadius, torusCoordDistance, dx]
    exact Nat.le_add_right _ _
  have hcycY : torusCyclicAxisDistance L dy ≤ R := by
    dsimp [R, torusRadius, torusCoordDistance, dy]
    exact Nat.le_add_left _ _
  have hlogX : Real.log (((torusCyclicAxisDistance L dx + 1 : ℕ) : ℝ)) ≤
      Real.log (((R + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hcycX 1
  have hlogY : Real.log (((torusCyclicAxisDistance L dy + 1 : ℕ) : ℝ)) ≤
      Real.log (((R + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hcycY 1
  have hf : ∑ v, f v = 0 := by dsimp [f]; exact sum_dipole_eq_zero _ _
  have hg : ∑ v, g v = 0 := by dsimp [g]; exact sum_dipole_eq_zero _ _
  have hfx : greenBilinear (torusGraph L hL) (torusGraph_connected L hL) f f ≤ K := by
    have hm' : dx ≤ L := by dsimp [dx]; exact Nat.le_of_lt (q.1 - p.1).val_lt
    have h := torusGreenBilinear_horizontal_dipole_log_upper_bound hL
      (torusGraph_connected L hL) p dx hm'
    have hr : p + ((dx : ZMod L), 0) = r := by
      ext <;> simp [r, hdx]
    simpa [f, hr, K, R] using
      le_trans h (mul_le_mul_of_nonneg_left hlogX (by norm_num : (0 : ℝ) ≤ 82))
  have hgy : greenBilinear (torusGraph L hL) (torusGraph_connected L hL) g g ≤ K := by
    have hm' : dy ≤ L := by dsimp [dy]; exact Nat.le_of_lt (q.2 - p.2).val_lt
    have h := torusGreenBilinear_vertical_dipole_log_upper_bound hL r dy
      hm'
    have hr : r + (0, (dy : ZMod L)) = q := by
      ext <;> simp [r, hdy]
    simpa [g, hr, K, R] using
      le_trans h (mul_le_mul_of_nonneg_left hlogY (by norm_num : (0 : ℝ) ≤ 82))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfg := torusGreenBilinear_abs_le_of_quadratic_bounds hL
    (torusGraph_connected L hL) f g hf hg K hK hfx hgy
  have hexpand := greenBilinear_sub_self (torusGraph L hL)
    (torusGraph_connected L hL) f (-g)
  have hsum : greenBilinear (torusGraph L hL) (torusGraph_connected L hL)
      (f + g) (f + g) ≤ 4 * K := by
    have hcross : |greenBilinear (torusGraph L hL) (torusGraph_connected L hL) f g| ≤ K := hfg
    rw [show f + g = f - -g by ext v; simp]
    rw [hexpand]
    have hneg : greenBilinear (torusGraph L hL) (torusGraph_connected L hL) (-g) (-g) =
        greenBilinear (torusGraph L hL) (torusGraph_connected L hL) g g := by
      let G := torusGraph L hL
      let hG := torusGraph_connected L hL
      have hmap (u : TorusVertex L → ℝ) : G.greenOp hG (-u) = -G.greenOp hG u :=
        (G.greenOp hG).map_neg u
      have hpneg (u v : TorusVertex L → ℝ) : pairing (-u) v = -pairing u v := by
        rw [pairing_comm, pairing_neg_right, pairing_comm]
      unfold greenBilinear
      rw [hmap]
      simp only [neg_neg]
      rw [hpneg, pairing_neg_right]
    have hcross1 : greenBilinear (torusGraph L hL) (torusGraph_connected L hL) f (-g) =
        -greenBilinear (torusGraph L hL) (torusGraph_connected L hL) f g := by
      let G := torusGraph L hL
      let hG := torusGraph_connected L hL
      have hmap (u : TorusVertex L → ℝ) : G.greenOp hG (-u) = -G.greenOp hG u :=
        (G.greenOp hG).map_neg u
      unfold greenBilinear
      rw [hmap]
      simp only [neg_neg, pairing_neg_right, neg_neg]
      rfl
    have hcross2 : greenBilinear (torusGraph L hL) (torusGraph_connected L hL) (-g) f =
        -greenBilinear (torusGraph L hL) (torusGraph_connected L hL) f g := by
      rw [greenBilinear_symm, hcross1]
    rw [hneg, hcross1, hcross2]
    have hc := abs_le.mp hcross
    nlinarith [hfx, hgy, hc.1, hc.2]
  rw [hdecomp]
  calc
    greenBilinear (torusGraph L hL) (torusGraph_connected L hL)
        (dipole p r + dipole r q) (dipole p r + dipole r q) ≤ 4 * K := by
      simpa [f, g] using hsum
    _ = 328 * Real.log (((torusRadius p q + 1 : ℕ) : ℝ)) := by
      dsimp [K, R]
      ring

end FroehlichSpencer.BKT.Rotator.Periodic

end
