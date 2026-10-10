/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Energy.CostEnvelope
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# An admissible logarithmic scale choice for the SOS cost (the SOS activity estimate)

The
rooted-layer activity theorem (`abs_rootedActivityD_le`) needs an amplitude `amp`, a cutoff `k₀` and
a rate `b` with:

* `amp·K₁ ≤ W`;
* `100·4^{k₀}·costMajorant κ κ (amp·K₁) ≤ amp/2`;
* `amp ≤ 1/(2κK₀)`;
* `amp ≤ 2^{γk₀}/K₁`;
* `b ≤ amp/8 − a₁`;
* `b ≤ amp/(8D₁) − D₂ − a₂`.

`exists_sosScaleChoice`: for any layer constants (`α > 1`, `D₁, K₀, K₁ > 0`) and any `C > 0` there
are `r > 0` and `T₀` such that for every `T ≥ T₀` the choice `amp = T/(8πK₁)`,
`k₀ = ⌈log₂T / γ⌉ + 1`, `b = rT` is admissible.

Here `γ = 1 − 1/α`.

The exponential branch of the
cost is `e^{2π amp K₁} = e^{T/4}`, beaten by `κ ∝ e^{−2T/3}`, and `4^{k₀} ≤ 16 T^{2/γ}` is
polynomial in `T`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Layer

open Filter Topology
open FroehlichSpencer.BKT.Generic

/-- The SOS cutoff `k₀ = ⌈log₂ T / γ⌉ + 1`. -/
def sosCutoff (γ T : ℝ) : ℕ := ⌈Real.logb 2 T / γ⌉₊ + 1

theorem one_le_sosCutoff (γ T : ℝ) : 1 ≤ sosCutoff γ T := by
  unfold sosCutoff; omega

theorem le_two_rpow_sosCutoff {γ T : ℝ} (hγ : 0 < γ) (hT : 1 ≤ T) :
    T ≤ (2 : ℝ) ^ (γ * (sosCutoff γ T : ℝ)) := by
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.logb 2 T := Real.logb_nonneg (by norm_num) hT
  have hceil : Real.logb 2 T / γ ≤ ⌈Real.logb 2 T / γ⌉₊ := Nat.le_ceil _
  have hk : Real.logb 2 T ≤ γ * (sosCutoff γ T : ℝ) := by
    unfold sosCutoff
    push_cast
    rw [div_le_iff₀ hγ] at hceil
    nlinarith
  calc T = (2 : ℝ) ^ Real.logb 2 T := (Real.rpow_logb (by norm_num) (by norm_num) hT0).symm
    _ ≤ (2 : ℝ) ^ (γ * (sosCutoff γ T : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hk

theorem four_pow_sosCutoff_le {γ T : ℝ} (hγ : 0 < γ) (hT : 1 ≤ T) :
    (4 : ℝ) ^ sosCutoff γ T ≤ 16 * T ^ (2 / γ) := by
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.logb 2 T := Real.logb_nonneg (by norm_num) hT
  have hceil : (⌈Real.logb 2 T / γ⌉₊ : ℝ) < Real.logb 2 T / γ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hlog hγ.le)
  have hk : (sosCutoff γ T : ℝ) ≤ Real.logb 2 T / γ + 2 := by
    unfold sosCutoff; push_cast; linarith
  calc (4 : ℝ) ^ sosCutoff γ T = (2 : ℝ) ^ (2 * (sosCutoff γ T : ℝ)) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_two, Real.rpow_natCast]; norm_num
    _ ≤ (2 : ℝ) ^ (2 * (Real.logb 2 T / γ + 2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 16 * T ^ (2 / γ) := by
        rw [show 2 * (Real.logb 2 T / γ + 2) = Real.logb 2 T * (2 / γ) + 4 by ring,
          Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num),
          Real.rpow_logb (by norm_num) (by norm_num) hT0]
        norm_num
        ring

theorem sos_width_le {T K₁ : ℝ} (hT : 0 ≤ T) (hK₁ : 0 < K₁) :
    T / (8 * Real.pi * K₁) * K₁ ≤ Real.pi * Real.exp (T / 3) := by
  have hpi2 := Real.two_le_pi
  have h1 : 1 + T / 3 ≤ Real.exp (T / 3) := by
    have := Real.add_one_le_exp (T / 3); linarith
  have e1 : T / (8 * Real.pi * K₁) * K₁ = T / (8 * Real.pi) := by field_simp
  rw [e1, div_le_iff₀ (by positivity)]
  have hpp : 4 ≤ Real.pi * Real.pi := by nlinarith
  have e2 : Real.pi * Real.exp (T / 3) * (8 * Real.pi) =
      8 * (Real.pi * Real.pi) * Real.exp (T / 3) := by ring
  rw [e2]
  have he0 : 0 ≤ Real.exp (T / 3) := (Real.exp_pos _).le
  nlinarith

theorem div_eight_pi_le {T : ℝ} (hT : 0 ≤ T) : T / (8 * Real.pi) ≤ T := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.two_le_pi]

/-- The cost majorant at `amp·K₁ = T/(8π)` and `κ = C e^{−2T/3}`. -/
theorem sos_costMajorant_le {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) :
    costMajorant (C * Real.exp (-2 * T / 3)) (C * Real.exp (-2 * T / 3)) (T / (8 * Real.pi)) ≤
      C * (T ^ (2 : ℝ) * Real.exp (-(5 / 12) * T) + Real.exp (-(5 / 12) * T)) := by
  unfold costMajorant
  have hexp4 : Real.exp (2 * Real.pi * (T / (8 * Real.pi))) = Real.exp (T / 4) := by
    congr 1; field_simp; ring
  have he1 : Real.exp (-2 * T / 3) * Real.exp (T / 4) = Real.exp (-(5 / 12) * T) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp (-2 * T / 3) ≤ Real.exp (-(5 / 12) * T) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsq : (T / (8 * Real.pi)) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by positivity)
    (div_eight_pi_le hT) 2
  rw [hexp4, Real.rpow_two]
  set E := Real.exp (-2 * T / 3)
  set E' := Real.exp (-(5 / 12) * T)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have h1 : C * E * (T / (8 * Real.pi)) ^ 2 ≤ C * (T ^ 2 * E') := by
    calc C * E * (T / (8 * Real.pi)) ^ 2 ≤ C * E * T ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hC hE)
      _ = C * (T ^ 2 * E) := by ring
      _ ≤ C * (T ^ 2 * E') := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left he2 (sq_nonneg T)) hC
  have h2 : C * E * Real.exp (T / 4) = C * E' := by rw [mul_assoc, he1]
  linarith

/-- The exponential-cost condition from two small polynomial-exponential quantities. -/
theorem sos_expCost_le {T C K₁ γ ε₀ : ℝ} (hT : 1 ≤ T) (hC : 0 < C) (hK₁ : 0 < K₁) (hγ : 0 < γ)
    (hε₀ : ε₀ = 1 / (16 * Real.pi * K₁) / (3200 * C))
    (hP1 : T ^ (2 / γ + 2) * Real.exp (-(5 / 12) * T) < ε₀)
    (hP2 : T ^ (2 / γ) * Real.exp (-(5 / 12) * T) < ε₀) :
    100 * 4 ^ sosCutoff γ T * costMajorant (C * Real.exp (-2 * T / 3))
      (C * Real.exp (-2 * T / 3)) (T / (8 * Real.pi * K₁) * K₁) ≤ T / (8 * Real.pi * K₁) / 2 := by
  have hT0 : 0 < T := by linarith
  have hk4 := four_pow_sosCutoff_le hγ hT
  have hampK : T / (8 * Real.pi * K₁) * K₁ = T / (8 * Real.pi) := by field_simp
  rw [hampK]
  have hmaj := sos_costMajorant_le hT0.le hC.le
  have hmaj0 := costMajorant_nonneg (mul_nonneg hC.le (Real.exp_pos (-2 * T / 3)).le)
    (mul_nonneg hC.le (Real.exp_pos (-2 * T / 3)).le) (T / (8 * Real.pi))
  set E' := Real.exp (-(5 / 12) * T)
  set P := T ^ (2 / γ)
  have hP0 : 0 ≤ P := by positivity
  have hTpow : P * T ^ (2 : ℝ) = T ^ (2 / γ + 2) := (Real.rpow_add hT0 _ _).symm
  have hA : P * (T ^ (2 : ℝ) * E') < ε₀ := by rw [← mul_assoc, hTpow]; exact hP1
  have hε₀eq : 3200 * C * ε₀ = 1 / (16 * Real.pi * K₁) := by rw [hε₀]; field_simp
  have hamp1 : 1 / (16 * Real.pi * K₁) ≤ T / (8 * Real.pi * K₁) / 2 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk : 0 ≤ 16 * Real.pi * K₁ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hT hk]
  set M := costMajorant (C * Real.exp (-2 * T / 3)) (C * Real.exp (-2 * T / 3))
    (T / (8 * Real.pi))
  have hstep1 : 100 * 4 ^ sosCutoff γ T * M ≤ 100 * (16 * P) * M :=
    mul_le_mul_of_nonneg_right (by linarith) hmaj0
  have hstep2 : 100 * (16 * P) * M ≤ 1600 * C * (P * (T ^ (2 : ℝ) * E') + P * E') := by
    have := mul_le_mul_of_nonneg_left hmaj (show (0 : ℝ) ≤ 100 * (16 * P) by positivity)
    have e : 100 * (16 * P) * (C * (T ^ (2 : ℝ) * E' + E')) =
      1600 * C * (P * (T ^ (2 : ℝ) * E') + P * E') := by ring
    linarith
  have hstep3 : 1600 * C * (P * (T ^ (2 : ℝ) * E') + P * E') ≤ 3200 * C * ε₀ := by
    have : P * (T ^ (2 : ℝ) * E') + P * E' ≤ 2 * ε₀ := by linarith
    nlinarith
  linarith

theorem sos_quadBase_le {T C K₀ c : ℝ} (hC : 0 < C) (hK₀ : 0 < K₀) (hc : 0 < c)
    (hQ : T ^ (1 : ℝ) * Real.exp (-(2 / 3) * T) < 1 / (2 * C * K₀ * c)) :
    c * T ≤ 1 / (2 * (C * Real.exp (-2 * T / 3)) * K₀) := by
  have he : Real.exp (-2 * T / 3) = Real.exp (-(2 / 3) * T) := by congr 1; ring
  rw [he]
  rw [Real.rpow_one] at hQ
  set E := Real.exp (-(2 / 3) * T)
  have hE : 0 < E := Real.exp_pos _
  have hpos : 0 < 2 * C * K₀ * c := by positivity
  rw [lt_div_iff₀ hpos] at hQ
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem sos_rateMass_le {T c Mx a₁ : ℝ} (hc : 0 < c) (hMx : 1 ≤ Mx) (hT : 0 < T)
    (hR : 32 * |a₁| / (3 * c) ≤ T) : c / (32 * Mx) * T ≤ c * T / 8 - a₁ := by
  have h1 : c / (32 * Mx) * T ≤ c * T / 32 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos hc hT]
  rw [div_le_iff₀ (by positivity)] at hR
  have := le_abs_self a₁
  linarith

theorem sos_rateArea_le {T c Mx D₁ D₂ a₂ : ℝ} (hc : 0 < c) (hD₁ : 0 < D₁) (hMx : 1 ≤ Mx)
    (hMxD : D₁ ≤ Mx) (hT : 0 < T) (hR : 32 * Mx * (|D₂| + |a₂|) / (3 * c) ≤ T) :
    c / (32 * Mx) * T ≤ c * T / (8 * D₁) - D₂ - a₂ := by
  have hMx0 : 0 < Mx := by linarith
  have h1 : c * T / (8 * Mx) ≤ c * T / (8 * D₁) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  rw [div_le_iff₀ (by positivity)] at hR
  have hD := le_abs_self D₂
  have ha := le_abs_self a₂
  have e1 : c / (32 * Mx) * T = c * T / (32 * Mx) := by ring
  have e2 : c * T / (8 * Mx) = 4 * (c * T / (32 * Mx)) := by field_simp; ring
  have h3 : |D₂| + |a₂| ≤ 3 * (c * T / (32 * Mx)) := by
    rw [show 3 * (c * T / (32 * Mx)) = 3 * c * T / (32 * Mx) by ring, le_div_iff₀ (by positivity)]
    linarith
  rw [e1]
  linarith

/-- **An admissible logarithmic scale choice for the SOS cost.** -/
theorem exists_sosScaleChoice {D₁ D₂ α K₀ K₁ a₁ a₂ C : ℝ} (hα : 1 < α) (hD₁ : 0 < D₁)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hC : 0 < C) :
    ∃ r T₀ : ℝ, 0 < r ∧ 1 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
      0 ≤ T / (8 * Real.pi * K₁) ∧
      T / (8 * Real.pi * K₁) * K₁ ≤ Real.pi * Real.exp (T / 3) ∧
      1 ≤ sosCutoff (gradExponent α) T ∧
      100 * 4 ^ sosCutoff (gradExponent α) T * costMajorant (C * Real.exp (-2 * T / 3))
        (C * Real.exp (-2 * T / 3)) (T / (8 * Real.pi * K₁) * K₁) ≤ T / (8 * Real.pi * K₁) / 2 ∧
      T / (8 * Real.pi * K₁) ≤ 1 / (2 * (C * Real.exp (-2 * T / 3)) * K₀) ∧
      T / (8 * Real.pi * K₁) ≤
        (2 : ℝ) ^ (gradExponent α * (sosCutoff (gradExponent α) T : ℝ)) / K₁ ∧
      0 ≤ r * T ∧ r * T ≤ T / (8 * Real.pi * K₁) / 8 - a₁ ∧
      r * T ≤ T / (8 * Real.pi * K₁) / (8 * D₁) - D₂ - a₂ := by
  have hγ : 0 < gradExponent α := gradExponent_pos hα
  set c := 1 / (8 * Real.pi * K₁) with hc
  have hc0 : 0 < c := by positivity
  have hampc : ∀ T : ℝ, T / (8 * Real.pi * K₁) = c * T := fun T => by rw [hc]; ring
  set Mx := max 1 D₁ with hMx
  have hMx1 : 1 ≤ Mx := le_max_left _ _
  have hMxD : D₁ ≤ Mx := le_max_right _ _
  set ε₀ := 1 / (16 * Real.pi * K₁) / (3200 * C) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hpoly : ∀ s : ℝ, ∀ᶠ T in atTop, T ^ s * Real.exp (-(5 / 12) * T) < ε₀ :=
    fun s => (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s (5 / 12) (by norm_num)).eventually
      (gt_mem_nhds hε₀pos)
  have hq : ∀ᶠ T in atTop, T ^ (1 : ℝ) * Real.exp (-(2 / 3) * T) < 1 / (2 * C * K₀ * c) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 / 3) (by norm_num)).eventually
      (gt_mem_nhds (by positivity))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (1 : ℝ)).and
    ((hpoly (2 / gradExponent α + 2)).and ((hpoly (2 / gradExponent α)).and (hq.and
      ((eventually_ge_atTop (32 * |a₁| / (3 * c))).and
        (eventually_ge_atTop (32 * Mx * (|D₂| + |a₂|) / (3 * c))))))))
  refine ⟨c / (32 * Mx), max T₀ 1, by positivity, le_max_right _ _, fun T hT => ?_⟩
  obtain ⟨hT1, hP1, hP2, hQ, hR1, hR2⟩ := hT₀ T (le_trans (le_max_left _ _) hT)
  have hT0 : 0 < T := by linarith
  refine ⟨by positivity, sos_width_le hT0.le hK₁, one_le_sosCutoff _ _,
    sos_expCost_le hT1 hC hK₁ hγ hε₀ hP1 hP2, ?_, ?_, by positivity, ?_, ?_⟩
  · rw [hampc]; exact sos_quadBase_le hC hK₀ hc0 hQ
  · rw [le_div_iff₀ hK₁, show T / (8 * Real.pi * K₁) * K₁ = T / (8 * Real.pi) by field_simp]
    exact (div_eight_pi_le hT0.le).trans (le_two_rpow_sosCutoff hγ hT1)
  · rw [hampc]; exact sos_rateMass_le hc0 hMx1 hT0 hR1
  · rw [hampc]
    exact sos_rateArea_le hc0 hD₁ hMx1 hMxD hT0 hR2

end FroehlichSpencer.BKT.SOS.Layer

end
