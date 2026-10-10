/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Roughening.Weight
public import FroehlichSpencer.BKT.SOS.Layer.Rate
public import FroehlichSpencer.BKT.Generic.Moment.Aggregate

/-!
# The numbers of the SOS argument at `β = e^{−T}` (the dipole tilt construction: condition (★))

For the layer constants of the Appendix D pinned layer, all the numerical hypotheses of the SOS
moment bound (`sosMoment_ge_of_layer`) hold for every large `T = log(1/β)`:

* the SOS activity estimate scale choice `amp = T/(8πK₁)`, `k₀ = ⌈log₂T/γ⌉ + 1`, `b = rT`
  (`Layer.exists_sosScaleChoice`);
* the logarithmic-derivative bound `C e^{−2T/3} e^{|u|} ≤ 1` for `|u| ≤ max(T/8π, 1)`;
* the curvature `κ_c = (C + 1) e^{−2T/3}`;
* the packing threshold `ε_p = C_p e^{−rT}` and the endpoint threshold
  `ε_end = max(amp K₁, 1)² C_e e^{−rT}` (`exists_touching_threshold`);
* **(★)**: with `C₁ = κ_c + 4ε_p`, `C₁(T) → 0` and `128 C₁ ε_end ≤ 1`. In FS81's notation
  `c(β) = C₁` and `Λ_end = ε_end · ‖∇g‖²`, so `c(β) Λ_end(β)/R → 0`: the endpoint loss is a
  vanishing fraction of the gain.

`exists_sosNumbers`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Roughening

open Filter Topology
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.SOS.Star (interpolationCostConstant)
open FroehlichSpencer.BKT.SOS.Layer

theorem hasCurvatureBound_mono {w : ℂ → ℂ} {κ κ' : ℝ} (h : HasCurvatureBound w κ)
    (hκ : κ ≤ κ') : HasCurvatureBound w κ' := fun t s => by
  have h1 := h t s
  have h2 : κ * s ^ 2 ≤ κ' * s ^ 2 := mul_le_mul_of_nonneg_right hκ (sq_nonneg s)
  linarith

theorem exp_neg_rpow_two_thirds (T : ℝ) :
    Real.exp (-T) ^ (2 / 3 : ℝ) = Real.exp (-2 * T / 3) := by
  rw [← Real.exp_mul]; ring_nf

theorem sosWidthψ_exp_neg (T : ℝ) : sosWidthψ (Real.exp (-T)) = Real.pi * Real.exp (T / 3) := by
  unfold sosWidthψ
  rw [← Real.exp_mul]
  ring_nf

/-- `C x^s e^{−bx} → 0`, in the form used for the thresholds. -/
theorem tendsto_mul_rpow_mul_exp_neg (C s b : ℝ) (hb : 0 < b) :
    Tendsto (fun T : ℝ => C * (T ^ s * Real.exp (-b * T))) atTop (𝓝 0) := by
  simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).const_mul C

/-- **The numbers of the SOS argument.** For the layer constants there are `T₀ ≥ 1` and a
function `C₁ → 0` such that for every `T ≥ T₀` all the numerical hypotheses of
`sosMoment_ge_of_layer` hold at `β = e^{−T}` with `κ_c + 4ε_p = C₁(T)` and
`128 C₁(T) ε_end ≤ 1`. -/
theorem exists_sosNumbers {D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ} (Kov : ℕ) (hα : 1 < α)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) (hKv : 0 ≤ Kv) :
    ∃ (T₀ : ℝ) (C₁ : ℝ → ℝ), 1 ≤ T₀ ∧ Tendsto C₁ atTop (𝓝 0) ∧ ∀ T, T₀ ≤ T →
      0 < C₁ T ∧ ∃ (M : ℝ → ℝ) (κc amp b εp εe : ℝ) (k₀ : ℕ),
        HasLogDerivBounds (sosWeightψ (Real.exp (-T))) (sosWidthψ (Real.exp (-T))) M ∧
        HasCurvatureBound (sosWeightψ (Real.exp (-T))) κc ∧ 0 ≤ amp ∧
        amp * K₁ ≤ sosWidthψ (Real.exp (-T)) ∧ 1 ≤ k₀ ∧
        100 * 4 ^ k₀ * costMajorant (interpolationCostConstant * Real.exp (-T) ^ (2 / 3 : ℝ))
          (interpolationCostConstant * Real.exp (-T) ^ (2 / 3 : ℝ)) (amp * K₁) ≤ amp / 2 ∧
        amp ≤ 1 / (2 * (interpolationCostConstant * Real.exp (-T) ^ (2 / 3 : ℝ)) * K₀) ∧
        amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁ ∧
        (∀ u : ℝ, |u| ≤ max (amp * K₁) 1 → M u ≤ 1) ∧
        Real.log 8 / 2 ≤ b ∧ b ≤ amp / 8 - a₁ ∧ b ≤ amp / (8 * D₁) - D₂ - a₂ ∧
        (∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
          (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
            Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ εp) ∧
        (∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
          (Kov : ℝ) * (Kv * max (amp * K₁) 1 ^ 2) * (d + 1) ^ (2 + 1) * u ^ 0 *
            Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ εe) ∧
        κc + 4 * εp = C₁ T ∧ 128 * C₁ T * εe ≤ 1 := by
  obtain ⟨r, T₁, hr, hT₁, hscale⟩ := exists_sosScaleChoice (D₂ := D₂) (a₁ := a₁) (a₂ := a₂) hα
    hD₁ hK₀ hK₁ interpolationCostConstant_pos
  obtain ⟨CL, hCL, hlogB⟩ := exists_sosWeightψ_logDeriv
  obtain ⟨CK, hCK, hcurvB⟩ := exists_sosWeightψ_curvature
  obtain ⟨Cp, bp, hCp, hbp, hthP⟩ :=
    exists_touching_threshold ((Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) / 2) (by positivity) 4 4
  obtain ⟨Ce, be, hCe, hbe, hthE⟩ :=
    exists_touching_threshold ((Kov : ℝ) * Kv / 2) (by positivity) 2 0
  set C₁ : ℝ → ℝ := fun T => (CK + 1) * Real.exp (-2 * T / 3) + 4 * (Cp * Real.exp (-(r * T)))
    with hC₁
  have hpi := Real.two_le_pi
  -- the limit of `C₁`
  have hC₁lim : Tendsto C₁ atTop (𝓝 0) := by
    have h1 := tendsto_mul_rpow_mul_exp_neg (CK + 1) 0 (2 / 3) (by norm_num)
    have h2 := tendsto_mul_rpow_mul_exp_neg (4 * Cp) 0 r hr
    have h := h1.add h2
    rw [add_zero] at h
    refine h.congr' (eventually_atTop.mpr ⟨0, fun T _ => ?_⟩)
    have e1 : Real.exp (-(2 / 3) * T) = Real.exp (-2 * T / 3) := by ring_nf
    have e2 : Real.exp (-r * T) = Real.exp (-(r * T)) := by ring_nf
    simp only [Real.rpow_zero, one_mul, hC₁, e1, e2]
    ring
  -- the eventual inequalities
  set c' : ℝ := 2 / 3 - 1 / (8 * Real.pi) with hc'
  have hc'pos : 0 < c' := by
    rw [hc']
    have : 1 / (8 * Real.pi) < 2 / 3 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hEM := (tendsto_mul_rpow_mul_exp_neg (CL * Real.exp 1) 0 c' hc'pos).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hEP := (tendsto_mul_rpow_mul_exp_neg (128 * (CK + 1 + 4 * Cp) * Ce * 4) 2 r hr).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (max T₁ 1)).and
    ((eventually_ge_atTop (Real.log 8 / 2 / r)).and ((eventually_ge_atTop (bp / r)).and
      ((eventually_ge_atTop (be / r)).and (hEM.and hEP)))))
  refine ⟨max T₀ 1, C₁, le_max_right _ _, hC₁lim, fun T hT => ?_⟩
  obtain ⟨hTT₁, hT8, hTp, hTe, hM1, hP1⟩ := hT₀ T (le_trans (le_max_left _ _) hT)
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hTT₁
  have hT0 : 0 < T := by linarith
  have hTs : T₁ ≤ T := le_trans (le_max_left _ _) hTT₁
  set β := Real.exp (-T) with hβdef
  have hβ : 0 < β := Real.exp_pos _
  have hβ1 : β ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hβ23 : β ^ (2 / 3 : ℝ) = Real.exp (-2 * T / 3) := exp_neg_rpow_two_thirds T
  obtain ⟨hamp, hampW, hk₀, hexp, hquad₁, hquad₂, hb0, hb₁, hb₂⟩ := hscale T hTs
  set amp := T / (8 * Real.pi * K₁) with hampdef
  have hampK : amp * K₁ = T / (8 * Real.pi) := by rw [hampdef]; field_simp
  have hrT : 0 ≤ r * T := by positivity
  set Mw := max (amp * K₁) 1 with hMw
  have hMw1 : 1 ≤ Mw := le_max_right _ _
  have hMwT : Mw ≤ 2 * T := by
    rw [hMw, hampK]
    refine max_le ?_ (by linarith)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨by rw [hC₁]; positivity, fun u => CL * β ^ (2 / 3 : ℝ) * Real.exp |u|,
    (CK + 1) * β ^ (2 / 3 : ℝ), amp, r * T, Cp * Real.exp (-(r * T)),
    Mw ^ 2 * (Ce * Real.exp (-(r * T))), sosCutoff (gradExponent α) T,
    hlogB β hβ hβ1, ?_, hamp, ?_, hk₀, ?_, ?_, hquad₂, ?_, ?_, hb₁, hb₂, ?_, ?_, ?_, ?_⟩
  · exact hasCurvatureBound_mono (hcurvB β hβ hβ1)
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hβ.le _))
  · rw [sosWidthψ_exp_neg]; exact hampW
  · rw [hβ23]; exact hexp
  · rw [hβ23]; exact hquad₁
  · -- the log-derivative bound below the amplitude
    intro u hu
    rw [hβ23]
    have hu' : |u| ≤ T / (8 * Real.pi) + 1 := by
      rw [← hampK]; exact hu.trans (max_le (by linarith) (by
        have : 0 ≤ amp * K₁ := by rw [hampK]; positivity
        linarith))
    have h := hM1
    simp only [Real.rpow_zero, one_mul] at h
    calc CL * Real.exp (-2 * T / 3) * Real.exp |u|
        ≤ CL * Real.exp (-2 * T / 3) * Real.exp (T / (8 * Real.pi) + 1) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu') (by positivity)
      _ = CL * Real.exp 1 * Real.exp (-c' * T) := by
          rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add, hc']
          congr 2
          ring
      _ ≤ 1 := h.le
  · -- `b = rT ≥ log 8 / 2`
    have := (div_le_iff₀ hr).mp hT8
    linarith
  · -- the packing threshold
    intro d u hd hu
    have h := hthP (r * T) (by have := (div_le_iff₀ hr).mp hTp; linarith) d u hd hu
    have h2 : 2 * ((Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) / 2) =
        (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) := by ring
    rw [h2] at h
    exact h
  · -- the endpoint threshold
    intro d u hd hu
    have h := hthE (r * T) (by have := (div_le_iff₀ hr).mp hTe; linarith) d u hd hu
    have h2 : (Kov : ℝ) * (Kv * Mw ^ 2) * (d + 1) ^ (2 + 1) * u ^ 0 *
        Real.exp (-(r * T) * (u + Real.logb 2 (d + 1))) =
        Mw ^ 2 * (2 * ((Kov : ℝ) * Kv / 2) * (d + 1) ^ (2 + 1) * u ^ 0 *
          Real.exp (-(r * T) * (u + Real.logb 2 (d + 1)))) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
  · rw [hC₁, hβ23]
  · -- (★): `128 C₁ ε_end ≤ 1`
    have hC₁le : C₁ T ≤ CK + 1 + 4 * Cp := by
      rw [hC₁]
      have e1 : Real.exp (-2 * T / 3) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have e2 : Real.exp (-(r * T)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have := mul_le_mul_of_nonneg_left e1 (by linarith : (0 : ℝ) ≤ CK + 1)
      have := mul_le_mul_of_nonneg_left e2 hCp
      linarith
    have hC₁0 : 0 ≤ C₁ T := by rw [hC₁]; positivity
    have hMw2 : Mw ^ 2 ≤ 4 * T ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      nlinarith
    have hP1' : 128 * (CK + 1 + 4 * Cp) * Ce * 4 * (T ^ (2 : ℝ) * Real.exp (-r * T)) < 1 := by
      simpa [mul_assoc] using hP1
    have hexpeq : Real.exp (-(r * T)) = Real.exp (-r * T) := by ring_nf
    rw [hexpeq]
    have hE0 : 0 ≤ Ce * Real.exp (-r * T) := by positivity
    calc 128 * C₁ T * (Mw ^ 2 * (Ce * Real.exp (-r * T)))
        ≤ 128 * (CK + 1 + 4 * Cp) * (4 * T ^ (2 : ℝ) * (Ce * Real.exp (-r * T))) := by
          gcongr
      _ = 128 * (CK + 1 + 4 * Cp) * Ce * 4 * (T ^ (2 : ℝ) * Real.exp (-r * T)) := by ring
      _ ≤ 1 := hP1'.le

end FroehlichSpencer.BKT.SOS.Roughening

end
