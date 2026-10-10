/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.EnsembleBound
public import Mathlib.Algebra.Order.Chebyshev

/-!
# the attenuation and the Jensen error budget for unit link shifts

When every plaquette shift `η_{i,p}` has absolute value at most one, each current shifts at most
`n_i` plaquettes, and no plaquette is shifted by two currents:

* `attenuation_le`: `A_i ≤ exp(β (cosh 1 − 1) n_i − (ρ_i, a_i))`, the bound (3.35);
* `error_budget_le`: the Jensen error of (3.49) is at most
  `72 Σ_i z_i (2π d_i)² + (6β(e−1) + 72β²(e−1)²) Z Σ_p (2π ε_p)²` whenever `z_i (1 + n_i) ≤ Z`.

The first term is the phase part `|ε(μ_ϱ)|²` of `k_ϱ(ε)²` in (3.45), and the second the part
  `β L(ϱ) max |ε_p|`, summed with the disjointness of the shifted plaquettes instead of a maximum.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.ZN.Torus

noncomputable section

variable {E P ι : Type*} [Fintype E] [Fintype P] [Fintype ι]

theorem exp_abs_sub_one_le {η : ℝ} (hη : |η| ≤ 1) : Real.exp |η| - 1 ≤ Real.exp 1 - 1 := by
  have := Real.exp_le_exp.mpr hη
  linarith

theorem cosh_sub_one_le {η : ℝ} (hη : |η| ≤ 1) : Real.cosh η - 1 ≤ Real.cosh 1 - 1 := by
  have h : Real.cosh η ≤ Real.cosh 1 := by
    rw [Real.cosh_le_cosh]
    simpa using hη
  linarith

/-- **The attenuation bound** (FS82 (3.35)). -/
theorem attenuation_le [DecidableEq P] {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (ρ : E → ℤ)
    (a : E → ℝ) (n : ℕ) (hη : ∀ p, |plaqShift c a p| ≤ 1)
    (hcard : (Finset.univ.filter fun p => plaqShift c a p ≠ 0).card ≤ n) :
    attenuation β c ρ a ≤
      Real.exp (β * (Real.cosh 1 - 1) * n - ∑ x, (ρ x : ℝ) * a x) := by
  unfold attenuation
  rw [← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc1 : 0 ≤ Real.cosh 1 - 1 := by linarith [Real.one_le_cosh (1 : ℝ)]
  have hterm : ∀ p, β * (Real.cosh (plaqShift c a p) - 1) ≤
      if plaqShift c a p ≠ 0 then β * (Real.cosh 1 - 1) else 0 := by
    intro p
    by_cases hp : plaqShift c a p = 0
    · simp [hp]
    · rw [ite_eq_left hp]
      exact mul_le_mul_of_nonneg_left (cosh_sub_one_le (hη p)) hβ
  have hsum : ∑ p, β * (Real.cosh (plaqShift c a p) - 1) ≤ β * (Real.cosh 1 - 1) * n := by
    calc ∑ p, β * (Real.cosh (plaqShift c a p) - 1)
        ≤ ∑ p, if plaqShift c a p ≠ 0 then β * (Real.cosh 1 - 1) else 0 :=
          Finset.sum_le_sum fun p _ => hterm p
      _ = ((Finset.univ.filter fun p => plaqShift c a p ≠ 0).card : ℝ) *
            (β * (Real.cosh 1 - 1)) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * (β * (Real.cosh 1 - 1)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg hβ hc1)
      _ = _ := by ring
  linarith

theorem shiftK2_le [DecidableEq P] {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (a : E → ℝ)
    (ε : P → ℝ) (hη : ∀ p, |plaqShift c a p| ≤ 1) :
    shiftK2 β c a ε ≤ β * (Real.exp 1 - 1) *
      ∑ p ∈ Finset.univ.filter (fun p => plaqShift c a p ≠ 0), (2 * Real.pi * ε p) ^ 2 := by
  unfold shiftK2
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : plaqShift c a p = 0
  · simp [hp]
  · rw [ite_eq_left hp]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_abs_sub_one_le (hη p)) hβ) (sq_nonneg _)

theorem shiftK1_sq_le [DecidableEq P] {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (a : E → ℝ)
    (ε : P → ℝ) (δ : ℝ) (n : ℕ) (hη : ∀ p, |plaqShift c a p| ≤ 1)
    (hcard : (Finset.univ.filter fun p => plaqShift c a p ≠ 0).card ≤ n) :
    shiftK1 β c a ε δ ^ 2 ≤ 2 * (2 * Real.pi * δ) ^ 2 +
      2 * (β * (Real.exp 1 - 1)) ^ 2 * n *
        ∑ p ∈ Finset.univ.filter (fun p => plaqShift c a p ≠ 0), (2 * Real.pi * ε p) ^ 2 := by
  have hpi := Real.pi_pos
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  set F := Finset.univ.filter (fun p => plaqShift c a p ≠ 0) with hF
  have hsum : ∑ p, β * (Real.exp |plaqShift c a p| - 1) * (2 * Real.pi * |ε p|) ≤
      β * (Real.exp 1 - 1) * ∑ p ∈ F, |2 * Real.pi * ε p| := by
    rw [Finset.mul_sum, hF, Finset.sum_filter]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hp : plaqShift c a p = 0
    · simp [hp]
    · rw [ite_eq_left hp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (exp_abs_sub_one_le (hη p)) hβ) (by positivity)
  have hcs : (∑ p ∈ F, |2 * Real.pi * ε p|) ^ 2 ≤
      (n : ℝ) * ∑ p ∈ F, (2 * Real.pi * ε p) ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := F) (f := fun p => |2 * Real.pi * ε p|)
    simp only [sq_abs] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ?_)
    exact Finset.sum_nonneg fun p _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ p ∈ F, |2 * Real.pi * ε p| := Finset.sum_nonneg fun p _ => abs_nonneg _
  have hK1 : shiftK1 β c a ε δ ≤ 2 * Real.pi * |δ| +
      β * (Real.exp 1 - 1) * ∑ p ∈ F, |2 * Real.pi * ε p| := by
    unfold shiftK1
    linarith
  have hK10 : 0 ≤ shiftK1 β c a ε δ := by
    unfold shiftK1
    have : 0 ≤ ∑ p, β * (Real.exp |plaqShift c a p| - 1) * (2 * Real.pi * |ε p|) :=
      Finset.sum_nonneg fun p _ => mul_nonneg (mul_nonneg hβ (exp_abs_sub_one_nonneg _))
        (by positivity)
    have h2 : 0 ≤ 2 * Real.pi * |δ| := by positivity
    linarith
  have hx : (2 * Real.pi * |δ|) ^ 2 = (2 * Real.pi * δ) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
    ring
  calc shiftK1 β c a ε δ ^ 2
      ≤ (2 * Real.pi * |δ| + β * (Real.exp 1 - 1) * ∑ p ∈ F, |2 * Real.pi * ε p|) ^ 2 :=
        pow_le_pow_left₀ hK10 hK1 2
    _ ≤ 2 * (2 * Real.pi * |δ|) ^ 2 +
        2 * (β * (Real.exp 1 - 1) * ∑ p ∈ F, |2 * Real.pi * ε p|) ^ 2 := by
        nlinarith [sq_nonneg (2 * Real.pi * |δ| -
          β * (Real.exp 1 - 1) * ∑ p ∈ F, |2 * Real.pi * ε p|)]
    _ ≤ _ := by
        rw [hx, mul_pow]
        have hb : 0 ≤ (β * (Real.exp 1 - 1)) ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hcs hb]

/-- **The Jensen error budget.** -/
theorem error_budget_le [DecidableEq P] [DecidableEq ι] {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ)
    (ε : P → ℝ) (z : ι → ℝ) (hz0 : ∀ i, 0 ≤ z i) (a : ι → E → ℝ) (d : ι → ℝ) (n : ι → ℕ)
    (hη : ∀ i p, |plaqShift c (a i) p| ≤ 1)
    (hplaq : ∀ p i j, i ≠ j → plaqShift c (a i) p = 0 ∨ plaqShift c (a j) p = 0)
    (hcard : ∀ i, (Finset.univ.filter fun p => plaqShift c (a i) p ≠ 0).card ≤ n i)
    (Z : ℝ) (hZ0 : 0 ≤ Z) (hZ : ∀ i, z i * (1 + n i) ≤ Z) :
    ∑ i, 3 * z i * (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (d i) ^ 2) ≤
      72 * ∑ i, z i * (2 * Real.pi * d i) ^ 2 +
        (6 * β * (Real.exp 1 - 1) + 72 * β ^ 2 * (Real.exp 1 - 1) ^ 2) * Z *
          ∑ p, (2 * Real.pi * ε p) ^ 2 := by
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  set c₁ := 6 * β * (Real.exp 1 - 1) + 72 * β ^ 2 * (Real.exp 1 - 1) ^ 2 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set U : ι → ℝ := fun i =>
    ∑ p ∈ Finset.univ.filter (fun p => plaqShift c (a i) p ≠ 0), (2 * Real.pi * ε p) ^ 2 with hU
  have hU0 : ∀ i, 0 ≤ U i := fun i => Finset.sum_nonneg fun p _ => sq_nonneg _
  have hterm : ∀ i, 3 * z i * (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (d i) ^ 2) ≤
      72 * (z i * (2 * Real.pi * d i) ^ 2) + c₁ * Z * U i := by
    intro i
    have h2 := shiftK2_le hβ c (a i) ε (hη i)
    have h1 := shiftK1_sq_le hβ c (a i) ε (d i) (n i) (hη i) (hcard i)
    have hn0 : (0 : ℝ) ≤ n i := Nat.cast_nonneg _
    have hzle : z i ≤ Z := by nlinarith [hZ i, mul_nonneg (hz0 i) hn0]
    have hznle : z i * n i ≤ Z := by nlinarith [hZ i, hz0 i]
    have hA : 3 * z i * (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (d i) ^ 2) ≤
        3 * z i * (2 * (β * (Real.exp 1 - 1) * U i) +
          12 * (2 * (2 * Real.pi * d i) ^ 2 +
            2 * (β * (Real.exp 1 - 1)) ^ 2 * n i * U i)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith [hz0 i])
      linarith
    refine hA.trans ?_
    have hb1 : 0 ≤ β * (Real.exp 1 - 1) * U i := mul_nonneg (mul_nonneg hβ he1) (hU0 i)
    have hb2 : 0 ≤ (β * (Real.exp 1 - 1)) ^ 2 * U i := mul_nonneg (sq_nonneg _) (hU0 i)
    have e1 := mul_le_mul_of_nonneg_right hzle hb1
    have e2 := mul_le_mul_of_nonneg_right hznle hb2
    have hexp : 3 * z i * (2 * (β * (Real.exp 1 - 1) * U i) +
          12 * (2 * (2 * Real.pi * d i) ^ 2 +
            2 * (β * (Real.exp 1 - 1)) ^ 2 * n i * U i)) =
        72 * (z i * (2 * Real.pi * d i) ^ 2) + 6 * (z i * (β * (Real.exp 1 - 1) * U i)) +
          72 * (z i * n i * ((β * (Real.exp 1 - 1)) ^ 2 * U i)) := by ring
    have hrhs : c₁ * Z * U i = 6 * (Z * (β * (Real.exp 1 - 1) * U i)) +
        72 * (Z * ((β * (Real.exp 1 - 1)) ^ 2 * U i)) := by
      rw [hc₁]
      ring
    rw [hexp, hrhs]
    linarith
  have hdisj : ∑ i, U i ≤ ∑ p, (2 * Real.pi * ε p) ^ 2 := by
    have hswap : ∑ i, U i =
        ∑ p, ∑ i, if plaqShift c (a i) p ≠ 0 then (2 * Real.pi * ε p) ^ 2 else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hU]
      beta_reduce
      rw [Finset.sum_filter]
    rw [hswap]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hall : ∀ i, plaqShift c (a i) p = 0
    · simp only [hall, ne_eq, not_true_eq_false, ite_false, Finset.sum_const_zero]
      exact sq_nonneg _
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      rw [Finset.sum_eq_single i₀]
      · rw [ite_eq_left hi₀]
      · intro j _ hj
        have h0 : plaqShift c (a j) p = 0 := (hplaq p j i₀ hj).resolve_right hi₀
        simp [h0]
      · intro h
        exact absurd (Finset.mem_univ i₀) h
  calc ∑ i, 3 * z i * (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (d i) ^ 2)
      ≤ ∑ i, (72 * (z i * (2 * Real.pi * d i) ^ 2) + c₁ * Z * U i) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 72 * ∑ i, z i * (2 * Real.pi * d i) ^ 2 + c₁ * Z * ∑ i, U i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        linarith [mul_le_mul_of_nonneg_left hdisj (mul_nonneg hc₁0 hZ0)]

end

end FroehlichSpencer.FS82.ZN.Torus

end
