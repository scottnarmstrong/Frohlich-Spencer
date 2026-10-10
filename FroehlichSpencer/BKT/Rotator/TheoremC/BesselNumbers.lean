/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Energy.CostEnvelope
public import FroehlichSpencer.BKT.Generic.Moment.Aggregate
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The numbers of the T1.5-NG assembly for the Bessel weight

For a charge layer with constants `D₁, D₂, α, K₀, K₁`, an
edge-volume constant `Kv`, an overlap constant `Kov` and an entropy rate `a₁, a₂`, all the
amplitude and decay conditions of the exponential-moment assembly hold for every large `β`
with the explicit choices

* the amplitude `λ_β = log β / (4π K₁)` (`besselAmplitude`), so `λ_β K₁ = log β/(4π)` and
  `e^{2π λ_β K₁} = √β`;
* the scale cutoff `k₀ = ⌈log₂(λ_β K₁ + 2)/γ⌉ + 1` with `γ = 1 − 1/α` (`besselScaleCutoff`), so
  `2^{γ k₀} ≥ λ_β K₁ + 2` while `4^{k₀} ≤ 16 (λ_β K₁ + 2)^{2/γ}` is polylogarithmic in `β`;
* the decay rate `b_β = min(λ_β/8 − a₁, λ_β/(8 D₁) − D₂ − a₂)`, which tends to `∞`;
* the packing threshold `ε_β = C′ e^{−b_β}` (`exists_touching_threshold`), which tends to `0`.

This is `exists_besselNumbers`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

open Filter Topology
open FroehlichSpencer.BKT.Generic

/-- The scale cutoff `k₀ = ⌈log₂(x + 2)/γ⌉ + 1` for the amplitude edge bound `x = λ K₁`. -/
def besselScaleCutoff (γ x : ℝ) : ℕ :=
  ⌈Real.logb 2 (x + 2) / γ⌉₊ + 1

theorem le_two_rpow_besselScaleCutoff {γ x : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x) :
    x + 2 ≤ (2 : ℝ) ^ (γ * (besselScaleCutoff γ x : ℝ)) := by
  have hpos : 0 < x + 2 := by linarith
  have hs : Real.logb 2 (x + 2) / γ ≤ (besselScaleCutoff γ x : ℝ) := by
    unfold besselScaleCutoff
    push_cast
    linarith [Nat.le_ceil (Real.logb 2 (x + 2) / γ)]
  have he : Real.logb 2 (x + 2) ≤ γ * (besselScaleCutoff γ x : ℝ) := by
    rw [div_le_iff₀ hγ] at hs
    linarith
  calc x + 2 = (2 : ℝ) ^ Real.logb 2 (x + 2) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
    _ ≤ (2 : ℝ) ^ (γ * (besselScaleCutoff γ x : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) he

theorem four_pow_besselScaleCutoff_le {γ x : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x) :
    (4 : ℝ) ^ besselScaleCutoff γ x ≤ 16 * (x + 2) ^ (2 / γ) := by
  have hpos : 0 < x + 2 := by linarith
  have hs0 : 0 ≤ Real.logb 2 (x + 2) / γ :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by linarith)) hγ.le
  have hk : (besselScaleCutoff γ x : ℝ) ≤ Real.logb 2 (x + 2) / γ + 2 := by
    unfold besselScaleCutoff
    push_cast
    linarith [Nat.ceil_lt_add_one (R := ℝ) hs0]
  have h4 : (4 : ℝ) ^ besselScaleCutoff γ x =
      (2 : ℝ) ^ (2 * (besselScaleCutoff γ x : ℝ)) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_two, Real.rpow_natCast]
    norm_num
  have h16 : (2 : ℝ) ^ (4 : ℝ) = 16 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h4]
  calc (2 : ℝ) ^ (2 * (besselScaleCutoff γ x : ℝ))
      ≤ (2 : ℝ) ^ (Real.logb 2 (x + 2) * (2 / γ) + 4) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          have : Real.logb 2 (x + 2) * (2 / γ) = 2 * (Real.logb 2 (x + 2) / γ) := by ring
          linarith)
    _ = 16 * (x + 2) ^ (2 / γ) := by
        rw [Real.rpow_add (by norm_num), h16, Real.rpow_mul (by norm_num),
          Real.rpow_logb (by norm_num) (by norm_num) hpos, mul_comm]

/-- **The Bessel numbers.** See the module docstring. -/
theorem exists_besselNumbers {D₁ D₂ α K₀ K₁ Kv a₁ a₂ C : ℝ} (Kov : ℕ) (hα : 1 < α)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) (hKv : 0 ≤ Kv) (hC : 0 < C) :
    ∃ (β₀ : ℝ) (amp b ε : ℝ → ℝ) (k₀ : ℝ → ℕ), 1 ≤ β₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ β : ℝ, β₀ ≤ β →
        0 ≤ amp β ∧ amp β * K₁ ≤ Real.pi * β ∧ 1 ≤ k₀ β ∧
        100 * 4 ^ k₀ β * Generic.costMajorant (C / β) (C / β) (amp β * K₁) ≤ amp β / 2 ∧
        amp β ≤ 1 / (2 * (C / β) * K₀) ∧
        amp β ≤ (2 : ℝ) ^ (Generic.gradExponent α * k₀ β) / K₁ ∧
        (∀ u : ℝ, |u| ≤ max (amp β * K₁) 1 → C / β * Real.exp |u| ≤ 1) ∧
        Real.log 8 / 2 ≤ b β ∧ b β ≤ amp β / 8 - a₁ ∧ b β ≤ amp β / (8 * D₁) - D₂ - a₂ ∧
        0 ≤ ε β ∧
        ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
          (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
            Real.exp (-b β * (u + Real.logb 2 (d + 1))) ≤ ε β := by
  have hγ : 0 < gradExponent α := gradExponent_pos hα
  have hpi := Real.two_le_pi
  obtain ⟨Cth, b₀, hCth, -, hth⟩ :=
    exists_touching_threshold ((Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) / 2) (by positivity) 4 4
  -- the choices
  let amp : ℝ → ℝ := fun β => besselAmplitude K₁ β
  let b : ℝ → ℝ := fun β => min (amp β / 8 - a₁) (amp β / (8 * D₁) - D₂ - a₂)
  let ε : ℝ → ℝ := fun β => Cth * Real.exp (-b β)
  let k₀ : ℝ → ℕ := fun β => besselScaleCutoff (gradExponent α) (amp β * K₁)
  have hampK : ∀ β, amp β * K₁ = Real.log β / (4 * Real.pi) := fun β => by
    simp only [amp, besselAmplitude]
    field_simp
  have hamp_t : Tendsto amp atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by positivity)
  have hb_t : Tendsto b atTop atTop := by
    refine tendsto_atTop.2 fun M => ?_
    filter_upwards [hamp_t.eventually_ge_atTop (8 * (M + a₁)),
      hamp_t.eventually_ge_atTop (8 * D₁ * (M + D₂ + a₂))] with β h1 h2
    refine le_min ?_ ?_
    · linarith
    · have : M + D₂ + a₂ ≤ amp β / (8 * D₁) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
  -- the eventual inequalities
  have hc : (0 : ℝ) < 1 / (6400 * C * K₁) := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 / gradExponent α)
    (by norm_num : (0 : ℝ) < 1 / 2)).bound hc
  have hc' : (0 : ℝ) < 2 * Real.pi * K₁ / (C * K₀) := by positivity
  have hlo' := Real.isLittleO_log_id_atTop.bound hc'
  have hev : ∀ᶠ β : ℝ in atTop,
      0 ≤ amp β ∧ amp β * K₁ ≤ Real.pi * β ∧ 1 ≤ k₀ β ∧
        100 * 4 ^ k₀ β * Generic.costMajorant (C / β) (C / β) (amp β * K₁) ≤ amp β / 2 ∧
        amp β ≤ 1 / (2 * (C / β) * K₀) ∧
        amp β ≤ (2 : ℝ) ^ (Generic.gradExponent α * k₀ β) / K₁ ∧
        (∀ u : ℝ, |u| ≤ max (amp β * K₁) 1 → C / β * Real.exp |u| ≤ 1) ∧
        Real.log 8 / 2 ≤ b β ∧ b β ≤ amp β / 8 - a₁ ∧ b β ≤ amp β / (8 * D₁) - D₂ - a₂ ∧
        0 ≤ ε β ∧
        ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
          (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
            Real.exp (-b β * (u + Real.logb 2 (d + 1))) ≤ ε β := by
    filter_upwards [eventually_ge_atTop (Real.exp (4 * Real.pi)),
      eventually_ge_atTop ((C * Real.exp 1) ^ 2), hlo, hlo',
      hb_t.eventually_ge_atTop (max (Real.log 8 / 2) b₀)] with β hβe hβC hβlo hβlo' hβb
    -- basic facts
    have hβ1 : 1 ≤ β := le_trans (Real.one_le_exp (by positivity)) hβe
    have hβ0 : 0 < β := by linarith
    have hlogβ : 4 * Real.pi ≤ Real.log β := by
      rw [← Real.log_exp (4 * Real.pi)]
      exact Real.log_le_log (Real.exp_pos _) hβe
    have hlog0 : 0 ≤ Real.log β := by linarith
    set x := amp β * K₁ with hxdef
    have hx : x = Real.log β / (4 * Real.pi) := hampK β
    have hx1 : 1 ≤ x := by
      rw [hx, le_div_iff₀ (by positivity)]
      linarith
    have hx0 : 0 ≤ x := by linarith
    have hamp_eq : amp β = x / K₁ := by
      rw [hxdef]
      field_simp
    have hamp0 : 0 ≤ amp β := by rw [hamp_eq]; positivity
    have hsq : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
    have hss : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
    have hbb := le_max_left (Real.log 8 / 2) b₀
    have hbb₀ := le_max_right (Real.log 8 / 2) b₀
    refine ⟨hamp0, ?_, Nat.le_add_left 1 _, ?_, ?_, ?_, ?_, hbb.trans hβb, min_le_left _ _,
      min_le_right _ _, mul_nonneg hCth (Real.exp_pos _).le, ?_⟩
    · -- the amplitude stays in the strip
      rw [hx, div_le_iff₀ (by positivity)]
      have h1 := Real.log_le_sub_one_of_pos hβ0
      have hpp : 4 ≤ Real.pi * Real.pi := by nlinarith
      have h2 : 16 * β ≤ Real.pi * β * (4 * Real.pi) := by
        have : Real.pi * β * (4 * Real.pi) = 4 * (Real.pi * Real.pi) * β := by ring
        rw [this]
        nlinarith
      linarith
    · -- the exponential branch: `100 · 4^{k₀} · B(λK₁) ≤ λ/2`
      have hcm := costMajorant_bessel_le hC.le hβ1 hK₁
      have hcm0 : 0 ≤ costMajorant (C / β) (C / β) (amp β * K₁) :=
        costMajorant_nonneg (by positivity) (by positivity) _
      have h4 := four_pow_besselScaleCutoff_le hγ hx0
      have hx2 : x + 2 ≤ Real.log β := by
        rw [hx]
        have : Real.log β / (4 * Real.pi) ≤ Real.log β / 4 :=
          div_le_div_of_nonneg_left hlog0 (by norm_num) (by linarith)
        linarith
      have hr : (x + 2) ^ (2 / gradExponent α) ≤ Real.log β ^ (2 / gradExponent α) :=
        Real.rpow_le_rpow (by linarith) hx2 (by positivity)
      have hlo2 : Real.log β ^ (2 / gradExponent α) ≤ 1 / (6400 * C * K₁) * Real.sqrt β := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _),
          Real.norm_of_nonneg (Real.rpow_nonneg hβ0.le _)] at hβlo
        rwa [Real.sqrt_eq_rpow]
      have h4' : (4 : ℝ) ^ k₀ β ≤ 16 * (1 / (6400 * C * K₁) * Real.sqrt β) :=
        h4.trans (mul_le_mul_of_nonneg_left (hr.trans hlo2) (by norm_num))
      calc 100 * 4 ^ k₀ β * costMajorant (C / β) (C / β) (amp β * K₁)
          ≤ 100 * (16 * (1 / (6400 * C * K₁) * Real.sqrt β)) * (2 * C / Real.sqrt β) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h4' (by norm_num)) hcm hcm0 (by positivity)
        _ = 1 / (2 * K₁) := by field_simp; ring
        _ ≤ amp β / 2 := by
            rw [hamp_eq, div_div, mul_comm K₁ 2]
            exact div_le_div_of_nonneg_right hx1 (by positivity)
    · -- the quadratic branch
      have hle : Real.log β ≤ 2 * Real.pi * K₁ / (C * K₀) * β := by
        simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_pos hβ0] using hβlo'
      have heq : 1 / (2 * (C / β) * K₀) = 2 * Real.pi * K₁ / (C * K₀) * β / (4 * Real.pi * K₁) := by
        field_simp
        ring
      rw [heq]
      exact div_le_div_of_nonneg_right hle (by positivity)
    · -- the scale cutoff
      have h2 := le_two_rpow_besselScaleCutoff hγ hx0
      rw [hamp_eq]
      exact div_le_div_of_nonneg_right (by linarith) hK₁.le
    · -- the logarithmic-derivative bound `M ≤ 1`
      intro u hu
      have hu' : |u| ≤ x + 1 := hu.trans (max_le (by linarith) (by linarith))
      have hex : Real.exp x ≤ Real.sqrt β := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hβ0]
        refine Real.exp_le_exp.mpr ?_
        rw [hx]
        have : Real.log β / (4 * Real.pi) ≤ Real.log β / 2 :=
          div_le_div_of_nonneg_left hlog0 (by norm_num) (by linarith)
        linarith
      have hCe : C * Real.exp 1 ≤ Real.sqrt β := by
        have := Real.sqrt_le_sqrt hβC
        rwa [Real.sqrt_sq (by positivity)] at this
      calc C / β * Real.exp |u| ≤ C / β * (Real.exp x * Real.exp 1) := by
            rw [← Real.exp_add]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu') (by positivity)
        _ ≤ C / β * (Real.sqrt β * Real.exp 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hex (Real.exp_pos _).le)
              (by positivity)
        _ = C * Real.exp 1 / Real.sqrt β := by
            rw [eq_div_iff hsq.ne', show C / β * (Real.sqrt β * Real.exp 1) * Real.sqrt β =
              C * Real.exp 1 * (Real.sqrt β * Real.sqrt β) / β by ring, hss, mul_div_assoc,
              div_self hβ0.ne', mul_one]
        _ ≤ 1 := by rw [div_le_one hsq]; exact hCe
    · -- the packing threshold
      intro d u hd hu
      have h := hth (b β) (hbb₀.trans hβb) d u hd hu
      calc (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
            Real.exp (-b β * (u + Real.logb 2 (d + 1)))
          = 2 * ((Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) / 2) * (d + 1) ^ (4 + 1) * u ^ 4 *
            Real.exp (-b β * (u + Real.logb 2 (d + 1))) := by ring
        _ ≤ ε β := h
  obtain ⟨β₁, hβ₁⟩ := eventually_atTop.mp hev
  refine ⟨max β₁ 1, amp, b, ε, k₀, le_max_right _ _, ?_,
    fun β hβ => hβ₁ β ((le_max_left _ _).trans hβ)⟩
  have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hb_t).const_mul Cth
  rw [mul_zero] at this
  exact this

end FroehlichSpencer.BKT.Rotator.TheoremC

end
