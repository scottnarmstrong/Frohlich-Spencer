/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.SOSDirichlet
public import FroehlichSpencer.BKT.Surface.SOSDirichletLaw
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.sos_theorem73_dirichlet`

-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site siteBoundaryDepth euclideanSiteDistance)
open FroehlichSpencer.BKT.SOS.Roughening (sosHeightWeight sosHeightWeight_pos sosPartition
  sosVariance pinnedGrad pinnedField linfDist)
open FroehlichSpencer.BKT.Bridge.SOSDirichlet


theorem sos_theorem73_dirichlet :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' (𝓝[>] 0) (𝓝 0) ∧ ∃ L₀ : ℕ,
      ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → 0 < β' β ∧
        ∀ L : ℕ, L₀ ≤ L → ∀ u v : Fin L × Fin L,
          let r : ℝ := min
            (Real.sqrt ((((u.1 : ℕ) : ℝ) - v.1) ^ 2 + (((u.2 : ℕ) : ℝ) - v.2) ^ 2))
            ((min (min ((u.1 : ℕ) + 1) (L - u.1)) (min ((u.2 : ℕ) + 1) (L - u.2)) : ℕ) : ℝ)
          (∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + r))) ≤
            ∫⁻ n, ENNReal.ofReal (Real.exp (ε * ((n u : ℝ) - n v))) ∂sosDirichletLaw L β hβ) ∧
          ENNReal.ofReal (Real.log (1 + r) / β' β) ≤
            ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ ∧
          ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ < ⊤ := by
  obtain ⟨β₀, β'', L₀, hβ₀, hlim, hmain⟩ := SOS.Source.sos_theorem73_all_eps
  refine ⟨β₀, hβ₀, fun β => 2 * β'' β, by simpa using hlim.const_mul 2, L₀.val, fun β hβ hββ₀ =>
    ⟨by have := (hmain β hβ hββ₀).1; positivity, fun L hL₀ u v => ?_⟩⟩
  have hL : 1 < L := lt_of_lt_of_le L₀.property hL₀
  have hβ'' : 0 < β'' β := (hmain β hβ hββ₀).1
  obtain ⟨hmom, hvar⟩ := (hmain β hβ hββ₀).2 L hL₀ u v
  rw [depth_eq, euclid_eq, sosDirichletLaw_eq_sosLaw hL hβ]
  set ℓ := Real.log (1 + ((min (linfDist u v) (siteBoundaryDepth u) : ℕ) : ℝ)) with hℓ
  have hr : Real.log (1 + min (euclideanSiteDistance u v) (siteBoundaryDepth u : ℝ)) ≤ 2 * ℓ := by
    rw [hℓ, Nat.cast_min]
    exact log_min_le (Real.sqrt_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (euclid_le_two_linf u v)
  have hℓ0 : 0 ≤ ℓ := by
    have := Nat.cast_nonneg (α := ℝ) (min (linfDist u v) (siteBoundaryDepth u))
    exact Real.log_nonneg (by linarith)
  have hint := SOS.Source.sosVarianceIntegral_integrable hL hβ u v
  have hsq : ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂SOS.Source.sosLaw hL β hβ =
      ENNReal.ofReal (SOS.Source.sosVarianceIntegral hL hβ u v) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)).symm
  refine ⟨fun ε => ?_, ?_, ?_⟩
  · refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) (hmom ε)
    have hε : 0 ≤ ε ^ 2 / (2 * β'' β) := by positivity
    calc ε ^ 2 / (2 * β'' β) *
          Real.log (1 + min (euclideanSiteDistance u v) (siteBoundaryDepth u : ℝ))
        ≤ ε ^ 2 / (2 * β'' β) * (2 * ℓ) := mul_le_mul_of_nonneg_left hr hε
      _ = ε ^ 2 / β'' β * ℓ := by field_simp
  · rw [hsq]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ hvar)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [hsq]; exact ENNReal.ofReal_lt_top

end FroehlichSpencer.BKT.Provider

end
