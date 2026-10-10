/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The β threshold in KP Claim 3.2

KP Claim 3.2, p. 15–16 (Kharash–Peled, first version):
"using (1.14) and setting `0 < β₂ < β₀` to be small enough".

We show the T1.6 damping `exp(-(c₁/β)(u + log₂(d+1)))`
beats `K (d+1)³ u²` uniformly in `d ≥ 1`, `u ≥ 2` once `β < β₂`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- `u² ≤ exp u` for `u ≥ 2`. -/
lemma sq_le_exp_of_two_le {u : ℝ} (hu : 2 ≤ u) : u ^ 2 ≤ Real.exp u := by
  have h := Real.sum_le_exp_of_nonneg (n := 4) (by linarith : 0 ≤ u)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [sq_nonneg (u - 2), mul_nonneg (by linarith : 0 ≤ u) (sq_nonneg (u - 2))]

/-- `(d+1)³ ≤ exp (3 w)` for `w = logb 2 (d+1)`, `d ≥ 1`. -/
lemma cube_le_exp_logb {d : ℝ} (hd : 1 ≤ d) :
    (d + 1) ^ 3 ≤ Real.exp (3 * Real.logb 2 (d + 1)) := by
  have hpos : 0 < d + 1 := by linarith
  have hl : Real.log (d + 1) ≤ Real.logb 2 (d + 1) := by
    have h2 : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num)
      linarith
    have hw : 0 ≤ Real.log (d + 1) := Real.log_nonneg (by linarith)
    rw [Real.logb]
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    nlinarith
  have : (d + 1) ^ 3 = Real.exp (3 * Real.log (d + 1)) := by
    rw [show 3 * Real.log (d + 1) = ((3 : ℕ) : ℝ) * Real.log (d + 1) by norm_num,
      Real.exp_nat_mul, Real.exp_log hpos]
  rw [this]
  exact Real.exp_le_exp.2 (by linarith)

/-- The damping estimate for `t ≥ 4`. -/
lemma claim32_damping (K t d u : ℝ) (hK : 0 < K) (ht : 4 ≤ t) (hd : 1 ≤ d) (hu : 2 ≤ u) :
    K * (d + 1) ^ 3 * u ^ 2 * Real.exp (-t * (u + Real.logb 2 (d + 1)))
      ≤ K * Real.exp (-3 * (t - 3)) := by
  have hw : 1 ≤ Real.logb 2 (d + 1) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  set w := Real.logb 2 (d + 1)
  have h1 := cube_le_exp_logb hd
  have h2 := sq_le_exp_of_two_le hu
  have h3 : (d + 1) ^ 3 * u ^ 2 ≤ Real.exp (3 * w + u) := by
    rw [Real.exp_add]
    exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
  have h4 : (d + 1) ^ 3 * u ^ 2 * Real.exp (-t * (u + w)) ≤ Real.exp (-3 * (t - 3)) := by
    calc _ ≤ Real.exp (3 * w + u) * Real.exp (-t * (u + w)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp (3 * w + u + -t * (u + w)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)
  calc K * (d + 1) ^ 3 * u ^ 2 * Real.exp (-t * (u + w))
      = K * ((d + 1) ^ 3 * u ^ 2 * Real.exp (-t * (u + w))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 hK.le

/-- Abstract final step: `K t exp(-3(t-3)) ≤ c₁` for `t` large. -/
lemma claim32_tail (K c₁ t : ℝ) (hK : 0 < K) (hc₁ : 0 < c₁) (ht : 0 < t)
    (hlog : (1 / 2) * Real.log (K * Real.exp 9 / c₁) < t) :
    K * Real.exp (-3 * (t - 3)) * t ≤ c₁ := by
  have hA : Real.log (K * Real.exp 9 / c₁) < 2 * t := by linarith
  have hB : K * Real.exp 9 / c₁ < Real.exp (2 * t) := by
    have := Real.exp_lt_exp.2 hA
    rwa [Real.exp_log (by positivity)] at this
  have ht' : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hE : Real.exp (-3 * (t - 3)) = Real.exp 9 * Real.exp (-t) * Real.exp (-(2 * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h5 : Real.exp (-t) * t ≤ 1 := by
    have := mul_le_mul_of_nonneg_left ht' (Real.exp_pos (-t)).le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have h6 : Real.exp 9 * Real.exp (-(2 * t)) * K ≤ c₁ := by
    rw [Real.exp_neg]
    have hp := Real.exp_pos (2 * t)
    rw [div_lt_iff₀ hc₁] at hB
    have : Real.exp 9 * (Real.exp (2 * t))⁻¹ * K = Real.exp 9 * K / Real.exp (2 * t) := by
      field_simp
    rw [this, div_le_iff₀ hp]
    nlinarith
  have hx := Real.exp_pos 9
  have hy := Real.exp_pos (-(2 * t))
  calc K * Real.exp (-3 * (t - 3)) * t
      = (Real.exp 9 * Real.exp (-(2 * t)) * K) * (Real.exp (-t) * t) := by rw [hE]; ring
    _ ≤ c₁ * 1 := mul_le_mul h6 h5 (by positivity) hc₁.le
    _ = c₁ := mul_one _

/-- The β threshold in KP Claim 3.2: for `β` small, the T1.6 damping `exp(-(c₁/β)(u + log₂(d+1)))`
beats the polynomial `K (d+1)³ u²` uniformly in `d ≥ 1`, `u ≥ 2`. -/
theorem exists_claim32_threshold (K c₁ : ℝ) (hK : 0 < K) (hc₁ : 0 < c₁) :
    ∃ β₂ : ℝ, 0 < β₂ ∧ ∀ β : ℝ, 0 < β → β < β₂ → ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      K * (d + 1) ^ 3 * u ^ 2 * Real.exp (-(c₁ / β) * (u + Real.logb 2 (d + 1))) ≤ β := by
  set M := max 4 ((1 / 2) * Real.log (K * Real.exp 9 / c₁)) with hM
  have hM4 : 4 ≤ M := le_max_left _ _
  have hMpos : 0 < M := by linarith
  refine ⟨c₁ / M, div_pos hc₁ hMpos, fun β hβ hlt d u hd hu => ?_⟩
  have hbt : M < c₁ / β := by
    rw [lt_div_iff₀ hβ]
    rw [lt_div_iff₀ hMpos] at hlt
    linarith
  set t := c₁ / β with htdef
  have htpos : 0 < t := by linarith
  have hβ' : β = c₁ / t := by rw [htdef]; field_simp
  have h1 := claim32_damping K t d u hK (by linarith) hd hu
  have h2 := claim32_tail K c₁ t hK hc₁ htpos
    (lt_of_le_of_lt (le_max_right _ _) hbt)
  refine h1.trans ?_
  rw [hβ', le_div_iff₀ htpos]
  exact h2

end FroehlichSpencer.BKT

end
