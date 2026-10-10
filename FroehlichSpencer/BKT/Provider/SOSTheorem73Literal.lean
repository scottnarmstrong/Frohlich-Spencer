/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.SOSLiteral
public import FroehlichSpencer.BKT.Surface.SOSLiteralLimit
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.sos_theorem73_literal`

-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open FroehlichSpencer.BKT FroehlichSpencer.BKT.SOS.Literal
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site)
open FroehlichSpencer.BKT.SOS.Roughening (pinnedGrad pinnedField)
open FroehlichSpencer.BKT.Bridge.SOSLiteral


theorem sos_theorem73_literal :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1), β ≤ β₀ → 0 < β' β ∧
        ∀ (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (hw : w ∈ A),
          (∃ ν : Measure (A → ℤ), IsSOSLiteralLimit β hβ hβ1 A w hw ν) ∧
          ∀ ν : Measure (A → ℤ), IsSOSLiteralLimit β hβ hβ1 A w hw ν →
            IsProbabilityMeasure ν ∧ ∀ (v v' : ℤ × ℤ) (hv : v ∈ A) (hv' : v' ∈ A),
              let r : ℝ := Real.sqrt (((v.1 - v'.1 : ℤ) : ℝ) ^ 2 + ((v.2 - v'.2 : ℤ) : ℝ) ^ 2)
              (∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + r))) ≤
                ∫⁻ d, ENNReal.ofReal (Real.exp (ε * ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ))) ∂ν) ∧
              ENNReal.ofReal (Real.log (1 + r) / β' β) ≤
                ∫⁻ d, ENNReal.ofReal (((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ^ 2) ∂ν ∧
              ∫⁻ d, ENNReal.ofReal (((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ^ 2) ∂ν < ⊤ := by
  obtain ⟨β₀, β', hβ₀, -, hlim, h⟩ := literal_theorem73_limit
  have htwo : Tendsto (fun j : ℕ => 2 * j) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun _a ha => by omega⟩
  refine ⟨β₀, hβ₀, fun β => 16 * β' β, by simpa using hlim.const_mul 16,
    fun β hβ hβ1 hββ₀ => ?_⟩
  obtain ⟨hβ', hA⟩ := h β hβ hββ₀
  refine ⟨by positivity, fun A w hw => ?_⟩
  obtain ⟨hex, hall⟩ := hA A w hw
  obtain ⟨M, hM⟩ := exists_box A
  refine ⟨?_, fun ν hν => ?_⟩
  · -- a limit point exists
    obtain ⟨φs, ν, hφs, hconv⟩ := hex (fun j => 2 * j) htwo
    refine ⟨ν, φs, hφs.tendsto_atTop, fun d => ?_⟩
    have hK : ∀ k ≥ M, A ⊆ planeBox (φs k) := fun k hk => hM _ (hk.trans (hφs.id_le k))
    have : Nonempty {k // A ⊆ planeBox (φs k)} := ⟨⟨M, hK M le_rfl⟩⟩
    refine Tendsto.congr (fun k => ?_) ((hconv d).comp (tendsto_val_subtype hK))
    simp only [Function.comp_apply]
    rw [sosLiteralDiffLaw_eq_diffLaw hβ hβ1 hw _ k.2]
  · -- every limit point
    obtain ⟨Rs, hRs, hconv⟩ := hν
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hRs.eventually_ge_atTop M)
    have hK' : ∀ k ≥ K, A ⊆ planeBox (Rs k) := fun k hk => hM _ (hK k hk)
    have : Nonempty {k // A ⊆ planeBox (Rs k)} := ⟨⟨K, hK' K le_rfl⟩⟩
    have hint : ∀ d, Tendsto (fun j => diffLaw β A w (2 * Rs j) {d}) atTop (𝓝 (ν {d})) :=
      fun d => tendsto_of_tendsto_subtype hK' (Tendsto.congr (fun k => by
        rw [sosLiteralDiffLaw_eq_diffLaw hβ hβ1 hw _ k.2]) (hconv d))
    obtain ⟨hprob, hbounds⟩ := hall (fun j => 2 * Rs j) ν (htwo.comp hRs) hint
    refine ⟨hprob, fun v v' hv hv' => ?_⟩
    obtain ⟨hmom, hvar, hfin⟩ := hbounds v v' hv hv'
    have hlog := log_euclid_le v v'
    have hℓ0 : 0 ≤ Real.log (1 + (planeLinf v v' : ℝ)) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (planeLinf v v'); linarith)
    refine ⟨fun ε => le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) (hmom ε),
      le_trans (ENNReal.ofReal_le_ofReal ?_) hvar, hfin⟩
    · have hε : 0 ≤ ε ^ 2 / (16 * β' β) := by positivity
      calc ε ^ 2 / (16 * β' β) *
            Real.log (1 + Real.sqrt (((v.1 - v'.1 : ℤ) : ℝ) ^ 2 + ((v.2 - v'.2 : ℤ) : ℝ) ^ 2))
          ≤ ε ^ 2 / (16 * β' β) * (2 * Real.log (1 + (planeLinf v v' : ℝ))) :=
            mul_le_mul_of_nonneg_left hlog hε
        _ = ε ^ 2 / (8 * β' β) * Real.log (1 + (planeLinf v v' : ℝ)) := by field_simp; ring
    · rw [div_le_div_iff₀ (by positivity) hβ']
      nlinarith

end FroehlichSpencer.BKT.Provider

end
