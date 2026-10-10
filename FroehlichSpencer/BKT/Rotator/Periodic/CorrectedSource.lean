/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.HarmonicCorrection
public import FroehlichSpencer.BKT.Villain.CurrentExpansion

/-!
# Logarithmic energy of the corrected periodic source

The fixed source path is corrected by the periodic Green potential. The real Hodge decomposition
retains its two path periods as harmonic currents; both periods are bounded independently of the
torus side.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Periodic
open FroehlichSpencer.BKT.Villain
open Multigraph

namespace FroehlichSpencer.BKT.Rotator.Periodic

noncomputable section

variable {L : ℕ} [NeZero L]

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The real divergence of an integer current is the cast of its oriented divergence. -/
theorem torusRealDivergence_intCast (hL : 2 < L) (j : TorusEdge L → ℤ)
    (v : TorusVertex L) :
    torusRealDivergence (fun e => (j e : ℝ)) v =
      (currentDivergence (torusGraph L hL) j v : ℝ) := by
  rw [torusRealDivergence, torusCurrentDivergence_formula]
  push_cast
  rfl

private def realCurrentDivergence (G : Multigraph V E)
    (q : E → ℝ) (v : V) : ℝ :=
  (∑ e, if G.src e = v then q e else 0) -
    ∑ e, if G.tgt e = v then q e else 0

omit [Fintype V] in
private theorem realCurrentDivergence_grad
    (G : Multigraph V E) (u : V → ℝ) (v : V) :
    realCurrentDivergence G (fun e => G.grad u e) v = -G.laplacian u v := by
  classical
  unfold realCurrentDivergence Multigraph.laplacian Multigraph.grad
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : G.src e = v
  · have ht : G.tgt e ≠ v := by
      intro ht
      exact G.src_ne_tgt e (hs.trans ht.symm)
    simp [hs, ht]
  · by_cases ht : G.tgt e = v
    · simp [hs, ht]
    · simp [hs, ht]

private theorem torusRealDivergence_eq_realCurrent (hL : 2 < L)
    (q : TorusEdge L → ℝ) (v : TorusVertex L) :
    torusRealDivergence q v = realCurrentDivergence (torusGraph L hL) q v := by
  classical
  have hsum (f : TorusEdge L → ℝ) :
      (∑ e : TorusEdge L, f e) = ∑ p : TorusVertex L, (f (p, true) + f (p, false)) := by
    calc
      _ = ∑ p : TorusVertex L, ∑ d : Bool, f (p, d) := Fintype.sum_prod_type f
      _ = _ := by simp only [Fintype.sum_bool]
  have hout : (∑ e : TorusEdge L, if (torusGraph L hL).src e = v then q e else 0) =
      q (v, true) + q (v, false) := by
    change (∑ e : TorusEdge L, if e.1 = v then q e else 0) = _
    rw [hsum, Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_ite_eq']
  have hin : (∑ e : TorusEdge L, if (torusGraph L hL).tgt e = v then q e else 0) =
      q ((v.1 - 1, v.2), false) + q ((v.1, v.2 - 1), true) := by
    change (∑ e : TorusEdge L, if torusStep L e.2 e.1 = v then q e else 0) = _
    rw [hsum]
    simp_rw [show torusStep L true = fun p => (p.1, p.2 + 1) by rfl,
      show torusStep L false = fun p => (p.1 + 1, p.2) by rfl]
    have hs : ∀ p : TorusVertex L,
        (p.1, p.2 + 1) = v ↔ p = (v.1, v.2 - 1) := by
      intro p
      constructor
      · intro h
        have h' := congrArg (fun z : TorusVertex L => (z.1, z.2 - 1)) h
        simpa using h'
      · rintro rfl
        ext <;> simp
    have hv : ∀ p : TorusVertex L,
        (p.1 + 1, p.2) = v ↔ p = (v.1 - 1, v.2) := by
      intro p
      constructor
      · intro h
        have h' := congrArg (fun z : TorusVertex L => (z.1 - 1, z.2)) h
        simpa using h'
      · rintro rfl
        ext <;> simp
    rw [Finset.sum_add_distrib]
    simp_rw [hs, hv]
    simp [Finset.mem_univ]
    ring
  change q (v, false) + q (v, true) - q ((v.1 - 1, v.2), false) -
      q ((v.1, v.2 - 1), true) = _
  unfold realCurrentDivergence
  rw [hout, hin]
  ring

/-- The real divergence of the graph gradient is its Laplacian. -/
theorem torusRealDivergence_grad (hL : 2 < L) (u : TorusVertex L → ℝ)
    (v : TorusVertex L) :
    torusRealDivergence (fun e => (torusGraph L hL).grad u e) v =
      -(torusGraph L hL).laplacian u v := by
  rw [torusRealDivergence_eq_realCurrent, realCurrentDivergence_grad]

private theorem horizontalPath_rootCut (n : ℕ) (hn : n ≤ L) (y : ZMod L) :
    torusHorizontalPathCurrent 0 0 n ((0, y), false) =
      if y = 0 ∧ 0 < n then 1 else 0 := by
  induction n with
  | zero => simp [torusHorizontalPathCurrent]
  | succ n ih =>
      have hnL : n < L := by omega
      have hcast : ((n : ℕ) : ZMod L) = 0 ↔ n = 0 := by
        constructor
        · intro hz
          have hdvd : L ∣ n := (ZMod.natCast_eq_zero_iff n L).mp hz
          rcases n with _ | n
          · rfl
          · have hpos : 0 < n + 1 := by omega
            have hLle : L ≤ n + 1 := Nat.le_of_dvd hpos hdvd
            omega
        · rintro rfl
          simp
      change torusHorizontalPathCurrent 0 0 n ((0, y), false) +
        torusSingleCurrent ((0 + (n : ZMod L), 0), false) ((0, y), false) = _
      rw [ih (by omega)]
      have hsingle : torusSingleCurrent ((0 + (n : ZMod L), 0), false)
          ((0, y), false) = if y = 0 ∧ n = 0 then 1 else 0 := by
        by_cases hn0 : n = 0
        · subst n
          simp [torusSingleCurrent]
        · have hcastne : (n : ZMod L) ≠ 0 := fun hz => hn0 (hcast.mp hz)
          have hcastne' : (0 : ZMod L) ≠ (n : ZMod L) := Ne.symm hcastne
          simp [torusSingleCurrent, hcastne', hn0]
      rw [hsingle]
      by_cases hy : y = 0 <;> by_cases hn0 : n = 0 <;> simp [hy, hn0]

private theorem verticalPath_rootCut (x₀ : ZMod L) (n : ℕ) (hn : n ≤ L)
    (x : ZMod L) :
    torusVerticalPathCurrent x₀ 0 n ((x, 0), true) =
      if x = x₀ ∧ 0 < n then 1 else 0 := by
  induction n with
  | zero => simp [torusVerticalPathCurrent]
  | succ n ih =>
      have hnL : n < L := by omega
      have hcast : ((n : ℕ) : ZMod L) = 0 ↔ n = 0 := by
        constructor
        · intro hz
          have hdvd : L ∣ n := (ZMod.natCast_eq_zero_iff n L).mp hz
          rcases n with _ | n
          · rfl
          · have hpos : 0 < n + 1 := by omega
            have hLle : L ≤ n + 1 := Nat.le_of_dvd hpos hdvd
            omega
        · rintro rfl
          simp
      change torusVerticalPathCurrent x₀ 0 n ((x, 0), true) +
        torusSingleCurrent ((x₀, 0 + (n : ZMod L)), true) ((x, 0), true) = _
      rw [ih (by omega)]
      have hsingle : torusSingleCurrent ((x₀, 0 + (n : ZMod L)), true)
          ((x, 0), true) = if x = x₀ ∧ n = 0 then 1 else 0 := by
        by_cases hn0 : n = 0
        · subst n
          simp [torusSingleCurrent]
        · have hcastne : (n : ZMod L) ≠ 0 := fun hz => hn0 (hcast.mp hz)
          have hcastne' : (0 : ZMod L) ≠ (n : ZMod L) := Ne.symm hcastne
          simp [torusSingleCurrent, hcastne', hn0]
      rw [hsingle]
      by_cases hx : x = x₀ <;> by_cases hn0 : n = 0 <;> simp [hx, hn0]

private theorem verticalPath_false (x y : ZMod L) (n : ℕ) (a b : ZMod L) :
    torusVerticalPathCurrent x y n ((a, b), false) = 0 := by
  induction n with
  | zero => simp [torusVerticalPathCurrent]
  | succ n ih => simp [torusVerticalPathCurrent, torusSingleCurrent, ih]

private theorem horizontalPath_true (x y : ZMod L) (n : ℕ) (a b : ZMod L) :
    torusHorizontalPathCurrent x y n ((a, b), true) = 0 := by
  induction n with
  | zero => simp [torusHorizontalPathCurrent]
  | succ n ih => simp [torusHorizontalPathCurrent, torusSingleCurrent, ih]

/-- The horizontal period of a coordinate root path at the root cut is zero or one. -/
theorem torusRootPathCurrent_horizontalPeriod_root (p : TorusVertex L) :
    torusHorizontalPeriod (torusRootPathCurrent p) 0 =
      if p.1.val = 0 then 0 else 1 := by
  classical
  simp only [torusHorizontalPeriod, torusRootPathCurrent]
  simp_rw [Pi.add_apply,
    horizontalPath_rootCut p.1.val (Nat.le_of_lt (ZMod.val_lt p.1)),
    verticalPath_false]
  by_cases hp : 0 < p.1.val
  · have hne : p.1 ≠ 0 := by
      intro h
      rw [h] at hp
      norm_num at hp
    simp [hp, hne]
  · have hz : p.1.val = 0 := Nat.eq_zero_of_not_pos hp
    simp [hz]

/-- The vertical period of a coordinate root path at the root cut is zero or one. -/
theorem torusRootPathCurrent_verticalPeriod_root (p : TorusVertex L) :
    torusVerticalPeriod (torusRootPathCurrent p) 0 =
      if p.2.val = 0 then 0 else 1 := by
  classical
  simp only [torusVerticalPeriod, torusRootPathCurrent]
  simp_rw [Pi.add_apply,
    verticalPath_rootCut p.1 p.2.val (Nat.le_of_lt (ZMod.val_lt p.2)),
    horizontalPath_true]
  by_cases hp : 0 < p.2.val
  · have hne : p.2 ≠ 0 := by
      intro h
      rw [h] at hp
      norm_num at hp
    simp [hp, hne]
  · have hz : p.2.val = 0 := Nat.eq_zero_of_not_pos hp
    simp [hz]


/-- Casting an integer current to real preserves horizontal periods. -/
theorem torusRealHorizontalPeriod_intCast (q : TorusEdge L → ℤ) (x : ZMod L) :
    torusRealHorizontalPeriod (fun e => (q e : ℝ)) x =
      (torusHorizontalPeriod q x : ℝ) := by
  unfold torusRealHorizontalPeriod torusHorizontalPeriod
  push_cast
  rfl

/-- Casting an integer current to real preserves vertical periods. -/
theorem torusRealVerticalPeriod_intCast (q : TorusEdge L → ℤ) (y : ZMod L) :
    torusRealVerticalPeriod (fun e => (q e : ℝ)) y =
      (torusVerticalPeriod q y : ℝ) := by
  unfold torusRealVerticalPeriod torusVerticalPeriod
  push_cast
  rfl

private def torusTranslateX : TorusVertex L ≃ TorusVertex L where
  toFun p := (p.1 + 1, p.2)
  invFun p := (p.1 - 1, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private def torusTranslateY : TorusVertex L ≃ TorusVertex L where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- Summing all horizontal cut periods of a graph gradient gives zero. -/
theorem sum_torusRealHorizontalPeriod_grad_zero (hL : 2 < L)
    (u : TorusVertex L → ℝ) :
    (∑ x : ZMod L,
      torusRealHorizontalPeriod (fun e => (torusGraph L hL).grad u e) x) = 0 := by
  change (∑ x : ZMod L, ∑ y : ZMod L, (u (x, y) - u (x + 1, y))) = 0
  have hshift : (∑ p : TorusVertex L, u (torusTranslateX p)) = ∑ p, u p := by
    exact (Equiv.sum_comp torusTranslateX u)
  calc
    (∑ x : ZMod L, ∑ y : ZMod L, (u (x, y) - u (x + 1, y))) =
        ∑ p : TorusVertex L, (u p - u (torusTranslateX p)) := by
          exact (Fintype.sum_prod_type
            (fun p : TorusVertex L => u p - u (torusTranslateX p))).symm
    _ = (∑ p : TorusVertex L, u p) - ∑ p, u (torusTranslateX p) := by
      exact Finset.sum_sub_distrib _ _
    _ = 0 := by rw [hshift]; ring

/-- Summing all vertical cut periods of a graph gradient gives zero. -/
theorem sum_torusRealVerticalPeriod_grad_zero (hL : 2 < L)
    (u : TorusVertex L → ℝ) :
    (∑ y : ZMod L,
      torusRealVerticalPeriod (fun e => (torusGraph L hL).grad u e) y) = 0 := by
  change (∑ y : ZMod L, ∑ x : ZMod L, (u (x, y) - u (x, y + 1))) = 0
  have hshift : (∑ p : TorusVertex L, u (torusTranslateY p)) = ∑ p, u p := by
    exact (Equiv.sum_comp torusTranslateY u)
  calc
    (∑ y : ZMod L, ∑ x : ZMod L, (u (x, y) - u (x, y + 1))) =
        ∑ p : TorusVertex L, (u p - u (torusTranslateY p)) := by
          rw [Finset.sum_comm]
          exact (Fintype.sum_prod_type
            (fun p : TorusVertex L => u p - u (torusTranslateY p))).symm
    _ = (∑ p : TorusVertex L, u p) - ∑ p, u (torusTranslateY p) := by
      exact Finset.sum_sub_distrib _ _
    _ = 0 := by rw [hshift]; ring


private theorem torusHorizontalPathCurrent_sum_false (x y : ZMod L) (n : ℕ) :
    (∑ v : TorusVertex L,
      torusHorizontalPathCurrent x y n (v, false)) = n := by
  induction n with
  | zero => simp [torusHorizontalPathCurrent]
  | succ n ih =>
      change (∑ v : TorusVertex L, (
        torusHorizontalPathCurrent x y n (v, false) +
          torusSingleCurrent ((x + (n : ZMod L), y), false) (v, false))) = n + 1
      rw [Finset.sum_add_distrib, ih]
      have hsingle : (∑ v : TorusVertex L,
          torusSingleCurrent ((x + (n : ZMod L), y), false) (v, false)) = 1 := by
        simp [torusSingleCurrent]
      rw [hsingle]

private theorem torusVerticalPathCurrent_sum_true (x y : ZMod L) (n : ℕ) :
    (∑ v : TorusVertex L,
      torusVerticalPathCurrent x y n (v, true)) = n := by
  induction n with
  | zero => simp [torusVerticalPathCurrent]
  | succ n ih =>
      change (∑ v : TorusVertex L, (
        torusVerticalPathCurrent x y n (v, true) +
          torusSingleCurrent ((x, y + (n : ZMod L)), true) (v, true))) = n + 1
      rw [Finset.sum_add_distrib, ih]
      have hsingle : (∑ v : TorusVertex L,
          torusSingleCurrent ((x, y + (n : ZMod L)), true) (v, true)) = 1 := by
        simp [torusSingleCurrent]
      rw [hsingle]

private theorem torusRealHorizontalPeriod_sum (q : TorusEdge L → ℝ) :
    (∑ x : ZMod L, torusRealHorizontalPeriod q x) =
      ∑ v : TorusVertex L, q (v, false) := by
  unfold torusRealHorizontalPeriod
  exact (Fintype.sum_prod_type (fun v : TorusVertex L => q (v, false))).symm

private theorem torusRealVerticalPeriod_sum (q : TorusEdge L → ℝ) :
    (∑ y : ZMod L, torusRealVerticalPeriod q y) =
      ∑ v : TorusVertex L, q (v, true) := by
  unfold torusRealVerticalPeriod
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type (fun v : TorusVertex L => q (v, true))).symm

private theorem torusRootPathCurrent_sum_false (p : TorusVertex L) :
    (∑ v : TorusVertex L, torusRootPathCurrent p (v, false)) = p.1.val := by
  change (∑ v : TorusVertex L, (
    torusHorizontalPathCurrent 0 0 p.1.val (v, false) +
      torusVerticalPathCurrent p.1 0 p.2.val (v, false))) = p.1.val
  have hzero (v : TorusVertex L) :
      torusVerticalPathCurrent p.1 0 p.2.val (v, false) = 0 := by
    rcases v with ⟨a, b⟩
    exact verticalPath_false p.1 0 p.2.val a b
  simp_rw [hzero, add_zero]
  exact torusHorizontalPathCurrent_sum_false 0 0 p.1.val

private theorem torusRootPathCurrent_sum_true (p : TorusVertex L) :
    (∑ v : TorusVertex L, torusRootPathCurrent p (v, true)) = p.2.val := by
  change (∑ v : TorusVertex L, (
    torusHorizontalPathCurrent 0 0 p.1.val (v, true) +
      torusVerticalPathCurrent p.1 0 p.2.val (v, true))) = p.2.val
  have hzero (v : TorusVertex L) :
      torusHorizontalPathCurrent 0 0 p.1.val (v, true) = 0 := by
    rcases v with ⟨a, b⟩
    exact horizontalPath_true 0 0 p.1.val a b
  simp_rw [hzero, zero_add]
  exact torusVerticalPathCurrent_sum_true p.1 0 p.2.val

private theorem sum_const_zmod_real (c : ℝ) :
    (∑ _ : ZMod L, c) = (L : ℝ) * c := by
  calc
    (∑ _ : ZMod L, c) = ∑ _ : Fin L, c := by
      exact (Equiv.sum_comp (ZMod.finEquiv L).toEquiv (fun _ : ZMod L => c)).symm
    _ = (L : ℝ) * c := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]


private theorem periodicCorrectedSource_harmonicPeriods_bound (hL : 2 < L)
    (a x : TorusVertex L) (ξ : ℤ) (u σ : TorusVertex L → ℝ) (p q : ℝ)
    (hdiv : ∀ v, torusRealDivergence (fun e =>
      ((torusSourcePathCurrent a x ξ e : ℤ) : ℝ)) v =
        torusRealDivergence (fun e => (torusGraph L hL).grad u e) v)
    (hdecomp : ∀ e, (torusSourcePathCurrent a x ξ e : ℝ) +
      (torusDualGraph hL).grad σ e = (torusGraph L hL).grad u e +
        torusRealUniformHarmonicCurrent p q e) :
    p ^ 2 + q ^ 2 ≤ 2 * (ξ : ℝ) ^ 2 := by
  let G := torusGraph L hL
  let j : TorusEdge L → ℝ := fun e => (torusSourcePathCurrent a x ξ e : ℝ)
  have hcycle : ∀ v,
      torusRealDivergence (j - fun e => G.grad u e) v = 0 := by
    intro v
    have hsub : torusRealDivergence (j - fun e => G.grad u e) v =
        torusRealDivergence j v - torusRealDivergence (fun e => G.grad u e) v := by
      simp [torusRealDivergence, Pi.sub_apply]
      ring
    rw [hsub, hdiv v]
    ring
  have hconstX : ∀ z : ZMod L,
      torusRealHorizontalPeriod (j - fun e => G.grad u e) z =
        torusRealHorizontalPeriod (j - fun e => G.grad u e) 0 := by
    intro z
    have hnat : ∀ n : ℕ,
        torusRealHorizontalPeriod (j - fun e => G.grad u e) (n : ZMod L) =
          torusRealHorizontalPeriod (j - fun e => G.grad u e) 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Nat.cast_succ,
            torusRealHorizontalPeriod_succ hL (j - fun e => G.grad u e)
              (n : ZMod L) hcycle, ih]
    simpa [ZMod.natCast_zmod_val] using hnat z.val
  have hconstY : ∀ z : ZMod L,
      torusRealVerticalPeriod (j - fun e => G.grad u e) z =
        torusRealVerticalPeriod (j - fun e => G.grad u e) 0 := by
    intro z
    have hnat : ∀ n : ℕ,
        torusRealVerticalPeriod (j - fun e => G.grad u e) (n : ZMod L) =
          torusRealVerticalPeriod (j - fun e => G.grad u e) 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Nat.cast_succ,
            torusRealVerticalPeriod_succ hL (j - fun e => G.grad u e)
              (n : ZMod L) hcycle, ih]
    simpa [ZMod.natCast_zmod_val] using hnat z.val
  have hdualX : torusRealHorizontalPeriod
      (fun e => (torusDualGraph hL).grad σ e) 0 = 0 := by
    unfold torusRealHorizontalPeriod
    simp_rw [torusDualGraph_grad_eq_torusDualGradientReal, torusDualGradientReal]
    rw [Finset.sum_sub_distrib]
    have hshift : (∑ y : ZMod L, σ ((0 : ZMod L), y - 1)) =
        ∑ y : ZMod L, σ ((0 : ZMod L), y) := by
      simpa [Equiv.addRight, sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun y : ZMod L => σ ((0 : ZMod L), y)))
    rw [hshift, sub_self]
  have hdualY : torusRealVerticalPeriod
      (fun e => (torusDualGraph hL).grad σ e) 0 = 0 := by
    unfold torusRealVerticalPeriod
    simp_rw [torusDualGraph_grad_eq_torusDualGradientReal, torusDualGradientReal]
    rw [Finset.sum_sub_distrib]
    have hshift : (∑ y : ZMod L, σ (y - 1, (0 : ZMod L))) =
        ∑ y : ZMod L, σ (y, (0 : ZMod L)) := by
      simpa [Equiv.addRight, sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun y : ZMod L => σ (y, (0 : ZMod L))))
    rw [hshift, sub_self]
  have hsubX (z : ZMod L) :
      torusRealHorizontalPeriod (j - fun e => G.grad u e) z =
        torusRealHorizontalPeriod j z -
          torusRealHorizontalPeriod (fun e => G.grad u e) z := by
    unfold torusRealHorizontalPeriod
    simp only [Pi.sub_apply]
    exact Finset.sum_sub_distrib _ _
  have hsubY (z : ZMod L) :
      torusRealVerticalPeriod (j - fun e => G.grad u e) z =
        torusRealVerticalPeriod j z -
          torusRealVerticalPeriod (fun e => G.grad u e) z := by
    unfold torusRealVerticalPeriod
    simp only [Pi.sub_apply]
    exact Finset.sum_sub_distrib _ _
  have hcycleEq : j - (fun e => G.grad u e) =
      (fun e => torusRealUniformHarmonicCurrent p q e -
        (torusDualGraph hL).grad σ e) := by
    funext e
    have he := hdecomp e
    change j e - G.grad u e =
      torusRealUniformHarmonicCurrent p q e - (torusDualGraph hL).grad σ e
    linarith
  have hpEq : torusRealHorizontalPeriod (j - fun e => G.grad u e) 0 = p := by
    rw [hcycleEq]
    have hsub : torusRealHorizontalPeriod
        (fun e => torusRealUniformHarmonicCurrent p q e -
          (torusDualGraph hL).grad σ e) (0 : ZMod L) =
        torusRealHorizontalPeriod (torusRealUniformHarmonicCurrent p q) (0 : ZMod L) -
          torusRealHorizontalPeriod (fun e => (torusDualGraph hL).grad σ e) (0 : ZMod L) := by
      unfold torusRealHorizontalPeriod
      exact Finset.sum_sub_distrib _ _
    rw [hsub, torusRealUniformHarmonicCurrent_horizontalPeriod (L := L), hdualX, sub_zero]
  have hqEq : torusRealVerticalPeriod (j - fun e => G.grad u e) 0 = q := by
    rw [hcycleEq]
    have hsub : torusRealVerticalPeriod
        (fun e => torusRealUniformHarmonicCurrent p q e -
          (torusDualGraph hL).grad σ e) (0 : ZMod L) =
        torusRealVerticalPeriod (torusRealUniformHarmonicCurrent p q) (0 : ZMod L) -
          torusRealVerticalPeriod (fun e => (torusDualGraph hL).grad σ e) (0 : ZMod L) := by
      unfold torusRealVerticalPeriod
      exact Finset.sum_sub_distrib _ _
    rw [hsub, torusRealUniformHarmonicCurrent_verticalPeriod (L := L), hdualY, sub_zero]
  have hconstSumX :
      (∑ z : ZMod L, torusRealHorizontalPeriod (j - fun e => G.grad u e) z) =
        (L : ℝ) * p := by
    calc
      _ = ∑ z : ZMod L,
          torusRealHorizontalPeriod (j - fun e => G.grad u e) 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hconstX z
      _ = (L : ℝ) * torusRealHorizontalPeriod (j - fun e => G.grad u e) 0 :=
            sum_const_zmod_real _
      _ = (L : ℝ) * p := by rw [hpEq]
  have hconstSumY :
      (∑ z : ZMod L, torusRealVerticalPeriod (j - fun e => G.grad u e) z) =
        (L : ℝ) * q := by
    calc
      _ = ∑ z : ZMod L,
          torusRealVerticalPeriod (j - fun e => G.grad u e) 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hconstY z
      _ = (L : ℝ) * torusRealVerticalPeriod (j - fun e => G.grad u e) 0 :=
            sum_const_zmod_real _
      _ = (L : ℝ) * q := by rw [hqEq]
  have hjpoint (e : TorusEdge L) :
      j e = (ξ : ℝ) *
        ((torusRootPathCurrent x e : ℤ) - torusRootPathCurrent a e : ℤ) := by
    simp [j, torusSourcePathCurrent]
  have hrootCastX (z : TorusVertex L) :
      (∑ v : TorusVertex L, (torusRootPathCurrent z (v, false) : ℤ) : ℝ) =
        (z.1.val : ℝ) := by
    exact_mod_cast torusRootPathCurrent_sum_false z
  have hrootCastY (z : TorusVertex L) :
      (∑ v : TorusVertex L, (torusRootPathCurrent z (v, true) : ℤ) : ℝ) =
        (z.2.val : ℝ) := by
    exact_mod_cast torusRootPathCurrent_sum_true z
  have hsumJX :
      (∑ z : ZMod L, torusRealHorizontalPeriod j z) =
        (ξ : ℝ) * ((x.1.val : ℝ) - (a.1.val : ℝ)) := by
    rw [torusRealHorizontalPeriod_sum]
    calc
      _ = ∑ v : TorusVertex L, (ξ : ℝ) *
          (((torusRootPathCurrent x (v, false) : ℤ) -
            torusRootPathCurrent a (v, false) : ℤ) : ℝ) := by
              apply Finset.sum_congr rfl
              intro v hv
              exact hjpoint (v, false)
      _ = (ξ : ℝ) * ((∑ v : TorusVertex L,
          (torusRootPathCurrent x (v, false) : ℤ) : ℝ) -
          (∑ v : TorusVertex L,
          (torusRootPathCurrent a (v, false) : ℤ) : ℝ)) := by
            rw [← Finset.mul_sum]
            congr 1
            simp_rw [Int.cast_sub]
            exact Finset.sum_sub_distrib _ _
      _ = _ := by rw [hrootCastX x, hrootCastX a]
  have hsumJY :
      (∑ z : ZMod L, torusRealVerticalPeriod j z) =
        (ξ : ℝ) * ((x.2.val : ℝ) - (a.2.val : ℝ)) := by
    rw [torusRealVerticalPeriod_sum]
    calc
      _ = ∑ v : TorusVertex L, (ξ : ℝ) *
          (((torusRootPathCurrent x (v, true) : ℤ) -
            torusRootPathCurrent a (v, true) : ℤ) : ℝ) := by
              apply Finset.sum_congr rfl
              intro v hv
              exact hjpoint (v, true)
      _ = (ξ : ℝ) * ((∑ v : TorusVertex L,
          (torusRootPathCurrent x (v, true) : ℤ) : ℝ) -
          (∑ v : TorusVertex L,
          (torusRootPathCurrent a (v, true) : ℤ) : ℝ)) := by
            rw [← Finset.mul_sum]
            congr 1
            simp_rw [Int.cast_sub]
            exact Finset.sum_sub_distrib _ _
      _ = _ := by rw [hrootCastY x, hrootCastY a]
  have hcycleSumX :
      (∑ z : ZMod L, torusRealHorizontalPeriod (j - fun e => G.grad u e) z) =
        (ξ : ℝ) * ((x.1.val : ℝ) - (a.1.val : ℝ)) := by
    calc
      _ = ∑ z : ZMod L,
          (torusRealHorizontalPeriod j z -
            torusRealHorizontalPeriod (fun e => G.grad u e) z) := by
              apply Finset.sum_congr rfl
              intro z hz
              exact hsubX z
      _ = (∑ z : ZMod L, torusRealHorizontalPeriod j z) -
          ∑ z : ZMod L, torusRealHorizontalPeriod (fun e => G.grad u e) z :=
            Finset.sum_sub_distrib _ _
      _ = _ := by rw [hsumJX, sum_torusRealHorizontalPeriod_grad_zero hL u, sub_zero]
  have hcycleSumY :
      (∑ z : ZMod L, torusRealVerticalPeriod (j - fun e => G.grad u e) z) =
        (ξ : ℝ) * ((x.2.val : ℝ) - (a.2.val : ℝ)) := by
    calc
      _ = ∑ z : ZMod L,
          (torusRealVerticalPeriod j z -
            torusRealVerticalPeriod (fun e => G.grad u e) z) := by
              apply Finset.sum_congr rfl
              intro z hz
              exact hsubY z
      _ = (∑ z : ZMod L, torusRealVerticalPeriod j z) -
          ∑ z : ZMod L, torusRealVerticalPeriod (fun e => G.grad u e) z :=
            Finset.sum_sub_distrib _ _
      _ = _ := by rw [hsumJY, sum_torusRealVerticalPeriod_grad_zero hL u, sub_zero]
  have hformulaX :
      (L : ℝ) * p = (ξ : ℝ) * ((x.1.val : ℝ) - (a.1.val : ℝ)) := by
    rw [← hconstSumX]
    exact hcycleSumX
  have hformulaY :
      (L : ℝ) * q = (ξ : ℝ) * ((x.2.val : ℝ) - (a.2.val : ℝ)) := by
    rw [← hconstSumY]
    exact hcycleSumY
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hLne : (L : ℝ) ≠ 0 := hLreal.ne'
  have hdx : |(x.1.val : ℝ) - (a.1.val : ℝ)| ≤ (L : ℝ) := by
    rw [abs_le]
    have hxL : (x.1.val : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (ZMod.val_lt x.1))
    have haL : (a.1.val : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (ZMod.val_lt a.1))
    have hx0 : 0 ≤ (x.1.val : ℝ) := by positivity
    have ha0 : 0 ≤ (a.1.val : ℝ) := by positivity
    constructor <;> linarith
  have hdy : |(x.2.val : ℝ) - (a.2.val : ℝ)| ≤ (L : ℝ) := by
    rw [abs_le]
    have hxL : (x.2.val : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (ZMod.val_lt x.2))
    have haL : (a.2.val : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (ZMod.val_lt a.2))
    have hx0 : 0 ≤ (x.2.val : ℝ) := by positivity
    have ha0 : 0 ≤ (a.2.val : ℝ) := by positivity
    constructor <;> linarith
  have hpval : p = (ξ : ℝ) * ((x.1.val : ℝ) - (a.1.val : ℝ)) / (L : ℝ) := by
    apply (eq_div_iff hLne).2
    nlinarith [hformulaX]
  have hqval : q = (ξ : ℝ) * ((x.2.val : ℝ) - (a.2.val : ℝ)) / (L : ℝ) := by
    apply (eq_div_iff hLne).2
    nlinarith [hformulaY]
  have hpAbs : |p| ≤ |(ξ : ℝ)| := by
    rw [hpval, abs_div, abs_of_pos hLreal, abs_mul]
    exact (div_le_iff₀ hLreal).2 (mul_le_mul_of_nonneg_left hdx (abs_nonneg _))
  have hqAbs : |q| ≤ |(ξ : ℝ)| := by
    rw [hqval, abs_div, abs_of_pos hLreal, abs_mul]
    exact (div_le_iff₀ hLreal).2 (mul_le_mul_of_nonneg_left hdy (abs_nonneg _))
  have hpbound : p ^ 2 ≤ (ξ : ℝ) ^ 2 := by
    rw [← sq_abs p, ← sq_abs (ξ : ℝ)]
    calc
      |p| ^ 2 = |p| * |p| := by ring
      _ ≤ |(ξ : ℝ)| * |(ξ : ℝ)| :=
        mul_self_le_mul_self (abs_nonneg _) hpAbs
      _ = |(ξ : ℝ)| ^ 2 := by ring
  have hqbound : q ^ 2 ≤ (ξ : ℝ) ^ 2 := by
    rw [← sq_abs q, ← sq_abs (ξ : ℝ)]
    calc
      |q| ^ 2 = |q| * |q| := by ring
      _ ≤ |(ξ : ℝ)| * |(ξ : ℝ)| :=
        mul_self_le_mul_self (abs_nonneg _) hqAbs
      _ = |(ξ : ℝ)| ^ 2 := by ring
  linarith [hpbound, hqbound]

/-- The source path corrected by the periodic Green field and its two harmonic periods has
uniformly logarithmic energy. The constant is independent of the torus side. -/
theorem exists_periodicCorrectedSource_energy (hL : 2 < L)
    (a x : TorusVertex L) (ξ : ℤ) :
    ∃ σ : TorusVertex L → ℝ,
      σ (0, 0) = 0 ∧
      (∑ e : TorusEdge L,
        (((torusSourcePathCurrent a x ξ e : ℤ) : ℝ) +
          (torusDualGraph hL).grad σ e) ^ 2) ≤
        350 * (ξ : ℝ) ^ 2 *
          (1 + Real.log (((torusRadius a x + 1 : ℕ) : ℝ))) := by
  let G := torusGraph L hL
  let hG := torusGraph_connected L hL
  let f : TorusVertex L → ℝ := fun v => (ξ : ℝ) * dipole a x v
  let u : TorusVertex L → ℝ := -G.greenOp hG f
  let j : TorusEdge L → ℝ := fun e => (torusSourcePathCurrent a x ξ e : ℝ)
  have hf : ∑ v, f v = 0 := by
    simp only [f]
    rw [← Finset.mul_sum, sum_dipole_eq_zero, mul_zero]
  have hsource (v : TorusVertex L) : torusRealDivergence j v = f v := by
    rw [torusRealDivergence_intCast hL,
      torusSourcePathCurrent_divergence hL]
    simp [f, dipole, rotatorTwoPointFrequency]; split_ifs <;> ring
  have hgreenLap := G.laplacian_greenOp_of_sum_eq_zero hG f hf
  have hnegLap (g : TorusVertex L → ℝ) : G.laplacian (-g) = -G.laplacian g := by
    funext v
    unfold Multigraph.laplacian
    simp only [Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hs : G.src e = v <;> by_cases ht : G.tgt e = v <;>
      simp [hs, ht, neg_sub] <;> ring_nf
  have huLap : G.laplacian u = -f := by
    rw [show u = -G.greenOp hG f by rfl, hnegLap, hgreenLap]
  have hdiv : ∀ v, torusRealDivergence j v =
      torusRealDivergence (fun e => G.grad u e) v := by
    intro v
    rw [hsource v, torusRealDivergence_grad hL]
    have hv := congrFun huLap v
    rw [hv]
    simp
  obtain ⟨σ, p, q, hroot, hdecomp, hcorrectedEnergy⟩ :=
    exists_periodicHarmonicCorrection_energy hL j u hdiv
  have henergyGreen : G.energy u = greenBilinear G hG f f := by
    have hnegE : G.energy (-G.greenOp hG f) = G.energy (G.greenOp hG f) := by
      unfold Multigraph.energy
      apply Finset.sum_congr rfl
      intro e he
      have hgrad : G.grad (-G.greenOp hG f) e =
          -(G.grad (G.greenOp hG f) e) := by
        simp only [Multigraph.grad, Pi.neg_apply]
        ring
      rw [hgrad, neg_sq]
    rw [show u = -G.greenOp hG f by rfl, hnegE,
      G.energy_eq_neg_pairing_laplacian, hgreenLap]
    unfold greenBilinear
    rw [pairing_comm]
    exact (pairing_neg_right f (G.greenOp hG f)).symm
  have hscale : greenBilinear G hG f f =
      (ξ : ℝ) ^ 2 * greenBilinear G hG (dipole a x) (dipole a x) := by
    have hfscale : f = (ξ : ℝ) • dipole a x := by
      funext v
      simp [f, smul_eq_mul]
    rw [hfscale]
    unfold greenBilinear Multigraph.pairing
    rw [LinearMap.map_smul]
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    calc
      _ = ∑ v, (ξ : ℝ) ^ 2 *
          (dipole a x v * (-(G.greenOp hG (dipole a x)) v)) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring_nf
      _ = (ξ : ℝ) ^ 2 *
          (∑ v, dipole a x v * (-(G.greenOp hG (dipole a x)) v)) := by
            rw [Finset.mul_sum]
      _ = _ := by ring
  have hpqbound := periodicCorrectedSource_harmonicPeriods_bound hL a x ξ u σ p q
    hdiv hdecomp
  have hbase := torusGreenBilinear_dipole_torusRadius_log_upper_bound hL a x
  have hlog : 0 ≤ Real.log (((torusRadius a x + 1 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hR : 1 ≤ (torusRadius a x + 1 : ℕ) := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast hR
  have hξsq : 0 ≤ (ξ : ℝ) ^ 2 := sq_nonneg _
  have hgreenBound : G.energy u ≤
      328 * (ξ : ℝ) ^ 2 * Real.log (((torusRadius a x + 1 : ℕ) : ℝ)) := by
    rw [henergyGreen, hscale]
    calc
      _ ≤ (ξ : ℝ) ^ 2 * (328 * Real.log (((torusRadius a x + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
      _ = _ := by ring
  have henergyBound : G.energy u + p ^ 2 + q ^ 2 ≤
      328 * (ξ : ℝ) ^ 2 * Real.log (((torusRadius a x + 1 : ℕ) : ℝ)) +
        2 * (ξ : ℝ) ^ 2 := by
    nlinarith [hgreenBound, hpqbound]
  refine ⟨σ, hroot, ?_⟩
  calc
    _ = ∑ e : TorusEdge L, (j e + (torusDualGraph hL).grad σ e) ^ 2 := by
      rfl
    _ = G.energy u + p ^ 2 + q ^ 2 := hcorrectedEnergy
    _ ≤ 328 * (ξ : ℝ) ^ 2 * Real.log (((torusRadius a x + 1 : ℕ) : ℝ)) +
        2 * (ξ : ℝ) ^ 2 := henergyBound
    _ ≤ 350 * (ξ : ℝ) ^ 2 *
        (1 + Real.log (((torusRadius a x + 1 : ℕ) : ℝ))) := by
      nlinarith [mul_nonneg hξsq hlog]

end

end FroehlichSpencer.BKT.Rotator.Periodic
