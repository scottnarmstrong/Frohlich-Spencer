/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockLaw
public import FroehlichSpencer.BKT.Ginibre.Models
import Mathlib.Tactic

/-!
`clockLaw n hn β Λ` (FS81 (7.1)–(7.2), source) is the internal pair-Gibbs measure
with the clock site measure for every real `β` (`clockLaw_eq_pairGibbs`), and the internal
`(clockModel n hn β hβ).gibbs Λ` for `β ≥ 0` (`clockLaw_eq_gibbs`).

Its two-point functions converge
along the net of finite regions to the Ginibre free limit (`tendsto_clockTwoPoint`).

These lemmas
prove the gates `isProbabilityMeasure_clockLaw` and `existsUnique_tendsto_clockTwoPoint` (providers
in `BKT/Provider/`).
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ClockLaw

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Rotator.Ginibre

/-- The free bond weights of the clock (and rotator) state, for every real `β`. -/
def clockBondWeight (β : ℝ) (Λ : Finset (ℤ × ℤ)) (b : Λ × Λ) : ℝ → ℝ :=
  if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then expCosWeight β else fun _ => 1

theorem isBondWeight_clockBondWeight (β : ℝ) (Λ : Finset (ℤ × ℤ)) (b : Λ × Λ) :
    IsBondWeight (clockBondWeight β Λ b) := by
  unfold clockBondWeight
  split_ifs
  exacts [isBondWeight_expCos β, isBondWeight_one]

theorem clock_density_eq (β : ℝ) (Λ : Finset (ℤ × ℤ)) (θ : Λ → ℝ) :
    (∏ b ∈ (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)),
        ENNReal.ofReal (Real.exp (β * Real.cos (θ b.1 - θ b.2)))) =
      ENNReal.ofReal (pairWeight (bondFrequency Λ) (clockBondWeight β Λ) θ) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun b _ => (Real.exp_pos _).le), pairWeight,
    Finset.prod_filter]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [phase_bondFrequency, clockBondWeight]
  unfold LatticeStep
  by_cases h : (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) <;>
    simp [h, expCosWeight]

theorem clockLaw_eq_pairGibbs (n : ℕ) (hn : 0 < n) (β : ℝ) (Λ : Finset (ℤ × ℤ)) :
    clockLaw n hn β Λ = pairGibbs (clockMeasure n) (bondFrequency Λ) (clockBondWeight β Λ) := by
  have hw := isBondWeight_clockBondWeight β Λ
  have hν := clockMeasure_univ_ne_zero hn
  have hZ := pairPartition_pos (d := bondFrequency Λ) hν hw
  have hdens : (fun θ : Λ → ℝ => ∏ b ∈ (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)),
        ENNReal.ofReal (Real.exp (β * Real.cos (θ b.1 - θ b.2)))) =
      fun θ => ENNReal.ofReal (pairWeight (bondFrequency Λ) (clockBondWeight β Λ) θ) :=
    funext (clock_density_eq β Λ)
  have hraw : (Measure.pi fun _ : Λ => ∑ k : Fin n, Measure.dirac (2 * Real.pi * (k : ℝ) / n)) =
      siteProduct (clockMeasure n) Λ := rfl
  have hmass : ((siteProduct (clockMeasure n) Λ).withDensity fun θ =>
      ENNReal.ofReal (pairWeight (bondFrequency Λ) (clockBondWeight β Λ) θ)) Set.univ =
      ENNReal.ofReal (pairPartition (clockMeasure n) (bondFrequency Λ) (clockBondWeight β Λ)) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, pairPartition,
      ofReal_integral_eq_lintegral_ofReal (integrable_pairWeight hw)
        (ae_of_all _ fun θ => (pairWeight_pos hw θ).le)]
  unfold clockLaw pairGibbs
  simp only [hdens, hraw]
  rw [hmass]
  ext s hs
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs, withDensity_apply _ hs,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hZ).ne')]
  refine lintegral_congr fun θ => ?_
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]

theorem clockLaw_eq_gibbs (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (Λ : Finset (ℤ × ℤ)) :
    clockLaw n hn β Λ = (clockModel n hn β hβ).gibbs Λ := by
  rw [clockLaw_eq_pairGibbs n hn]
  rfl

theorem clockTwoPoint_eq (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (j ℓ : ℤ × ℤ)
    (Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ}) :
    (∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩)) ∂clockLaw n hn β Λ.1) =
      (clockModel n hn β hβ).twoPoint ξ Λ.1 j ℓ := by
  rw [clockLaw_eq_gibbs n hn β hβ, FreeModel.twoPoint]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [latticeAngle, dite_eq_left Λ.2.1, dite_eq_left Λ.2.2]

theorem tendsto_clockTwoPoint (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (j ℓ : ℤ × ℤ) :
    Tendsto (fun Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} =>
      ∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩)) ∂clockLaw n hn β Λ.1)
      atTop (𝓝 ((clockModel n hn β hβ).twoPointLimit ξ j ℓ)) := by
  set M := clockModel n hn β hβ
  simp only [clockTwoPoint_eq n hn β hβ]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨L, hL, hL₀⟩ := (((M.tendsto_twoPointLimit ξ j ℓ).eventually
      (lt_mem_nhds ha)).and (eventually_ge_atTop (max (boxRadius j) (boxRadius ℓ)))).exists
    have hj : j ∈ freeBox L := mem_freeBox_of_boxRadius_le ((le_max_left _ _).trans hL₀)
    have hl : ℓ ∈ freeBox L := mem_freeBox_of_boxRadius_le ((le_max_right _ _).trans hL₀)
    filter_upwards [eventually_ge_atTop (⟨freeBox L, hj, hl⟩ :
        {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ})] with Λ hΛ
    exact hL.trans_le (M.twoPoint_mono_domain ξ hΛ hj hl)
  · exact Eventually.of_forall fun Λ => (M.twoPoint_le_twoPointLimit ξ Λ.2.1 Λ.2.2).trans_lt ha

end FroehlichSpencer.BKT.Bridge.ClockLaw

end
