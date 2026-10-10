/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.FreeVillainLaw
public import FroehlichSpencer.BKT.Bridge.VillainMeasure
import Mathlib.Tactic

/-!
The `freeVillainLaw β hβ Λ` ) is the normalized
`withDensity` of the bond density `freeVillainDensity` over the angle box (`freeVillainLaw_eq`, by
`rfl`).

Its total mass is in `(0, ∞)` (`freeVillainMass_pos_lt_top`): each bond factor is
`ENNReal.ofReal (villainWeight β t)` (`villainFactor_eq_ofReal_weight`), bounded above uniformly by
the Fourier bound (`villainWeight_fourier_bound`) and below, on the angle box `[-π, π)^Λ`, by the
zero-winding term `e^{-(β/2)(2π)²}`.

The gate `isProbabilityMeasure_freeVillainLaw` is proved in
`BKT/Provider/`; the D2 bridge `Bridge/FreeVillainDisorder.lean` uses `freeBonds` and
`freeVillainDensity`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.FreeVillainLaw

open FroehlichSpencer.BKT

/-- The bonds of `freeVillainLaw`: the nearest-neighbour pairs of `Λ`, each once. -/
def freeBonds (Λ : Finset (ℤ × ℤ)) : Finset (Λ × Λ) :=
  (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
    (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1))

/-- The density of `freeVillainLaw`. -/
def freeVillainDensity (β : ℝ) (Λ : Finset (ℤ × ℤ)) (θ : Λ → ℝ) : ℝ≥0∞ :=
  ∏ b ∈ freeBonds Λ,
    ∑' m : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) * (θ b.1 - θ b.2 + 2 * Real.pi * m) ^ 2))

/-- The reference measure of `freeVillainLaw`. -/
def freeVillainBase (Λ : Finset (ℤ × ℤ)) : Measure (Λ → ℝ) :=
  Measure.pi fun _ : Λ => volume.restrict (Set.Ico (-Real.pi) Real.pi)

theorem freeVillainLaw_eq (β : ℝ) (hβ : 0 < β) (Λ : Finset (ℤ × ℤ)) :
    freeVillainLaw β hβ Λ =
      ((freeVillainBase Λ).withDensity (freeVillainDensity β Λ) Set.univ)⁻¹ •
        (freeVillainBase Λ).withDensity (freeVillainDensity β Λ) := rfl

/-- The angle box `[-π, π)^Λ`. -/
def angleBox (Λ : Finset (ℤ × ℤ)) : Set (Λ → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ico (-Real.pi) Real.pi

theorem freeVillainDensity_le (β : ℝ) (hβ : 0 < β) (Λ : Finset (ℤ × ℤ)) (θ : Λ → ℝ) :
    freeVillainDensity β Λ θ ≤
      ∏ _b ∈ freeBonds Λ, ENNReal.ofReal (villainFourierBound β) := by
  unfold freeVillainDensity
  refine Finset.prod_le_prod₀ (fun _ _ => zero_le) fun b _ => ?_
  rw [villainFactor_eq_ofReal_weight β hβ]
  exact ENNReal.ofReal_le_ofReal (villainWeight_fourier_bound β hβ _)

theorem freeVillainDensity_lower_on_box (β : ℝ) (hβ : 0 < β) (Λ : Finset (ℤ × ℤ)) (θ : Λ → ℝ)
    (hθ : θ ∈ angleBox Λ) :
    ∏ _b ∈ freeBonds Λ, ENNReal.ofReal (Real.exp (-(β / 2) * (2 * Real.pi) ^ 2)) ≤
      freeVillainDensity β Λ θ := by
  have hangle (j : Λ) : |θ j| ≤ Real.pi := by
    have hj := (Set.mem_pi.mp hθ) j (Set.mem_univ j)
    exact abs_le.mpr ⟨hj.1, hj.2.le⟩
  unfold freeVillainDensity
  refine Finset.prod_le_prod₀ (fun _ _ => zero_le) fun b _ => ?_
  have habs : |θ b.1 - θ b.2| ≤ 2 * Real.pi := by
    calc |θ b.1 - θ b.2| ≤ |θ b.1| + |θ b.2| := abs_sub _ _
      _ ≤ Real.pi + Real.pi := add_le_add (hangle _) (hangle _)
      _ = 2 * Real.pi := by ring
  have hsq : (θ b.1 - θ b.2) ^ 2 ≤ (2 * Real.pi) ^ 2 := by
    have : 0 ≤ 2 * Real.pi := by positivity
    nlinarith [sq_abs (θ b.1 - θ b.2), abs_nonneg (θ b.1 - θ b.2)]
  have hexp : Real.exp (-(β / 2) * (2 * Real.pi) ^ 2) ≤
      Real.exp (-(β / 2) * (θ b.1 - θ b.2) ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsq (by linarith))
  calc ENNReal.ofReal (Real.exp (-(β / 2) * (2 * Real.pi) ^ 2))
      ≤ ENNReal.ofReal (Real.exp (-(β / 2) * (θ b.1 - θ b.2 + 2 * Real.pi * (0 : ℤ)) ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal; simpa using hexp
    _ ≤ _ := ENNReal.le_tsum (f := fun m : ℤ => ENNReal.ofReal (Real.exp (-(β / 2) *
          (θ b.1 - θ b.2 + 2 * Real.pi * m) ^ 2))) 0

theorem freeVillainBase_angleBox_pos (Λ : Finset (ℤ × ℤ)) : 0 < freeVillainBase Λ (angleBox Λ) := by
  unfold freeVillainBase angleBox
  rw [Measure.pi_pi]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [Measure.restrict_apply measurableSet_Ico, Set.inter_self, Real.volume_Ico]
  exact (ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])).ne'

theorem freeVillainBase_univ_lt_top (Λ : Finset (ℤ × ℤ)) : freeVillainBase Λ Set.univ < ∞ := by
  unfold freeVillainBase
  rw [← Set.pi_univ, Measure.pi_pi]
  exact ENNReal.prod_lt_top fun j _ => by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top

theorem freeVillainMass_pos_lt_top (β : ℝ) (hβ : 0 < β) (Λ : Finset (ℤ × ℤ)) :
    0 < (freeVillainBase Λ).withDensity (freeVillainDensity β Λ) Set.univ ∧
      (freeVillainBase Λ).withDensity (freeVillainDensity β Λ) Set.univ < ∞ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  constructor
  · set d : ℝ≥0∞ := ∏ _b ∈ freeBonds Λ, ENNReal.ofReal (Real.exp (-(β / 2) * (2 * Real.pi) ^ 2))
    have hdpos : 0 < d := by
      apply pos_iff_ne_zero.mpr
      exact Finset.prod_ne_zero_iff.mpr fun _ _ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hSmeas : MeasurableSet (angleBox Λ) :=
      (measurableSet_pi Set.countable_univ).mpr (Or.inl fun _ _ => measurableSet_Ico)
    have hlint : d * freeVillainBase Λ (angleBox Λ) ≤
        ∫⁻ θ, freeVillainDensity β Λ θ ∂freeVillainBase Λ := by
      calc d * freeVillainBase Λ (angleBox Λ) =
            ∫⁻ θ, (angleBox Λ).indicator (fun _ => d) θ ∂freeVillainBase Λ := by
            rw [lintegral_indicator_const hSmeas]
        _ ≤ _ := lintegral_mono fun θ => by
            by_cases hθ : θ ∈ angleBox Λ
            · simpa only [Set.indicator, hθ, ↓reduceIte, d] using
                freeVillainDensity_lower_on_box β hβ Λ θ hθ
            · simp only [Set.indicator, hθ, ↓reduceIte, zero_le]
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr
      (mul_ne_zero hdpos.ne' (freeVillainBase_angleBox_pos Λ).ne')) hlint
  · set M : ℝ≥0∞ := ∏ _b ∈ freeBonds Λ, ENNReal.ofReal (villainFourierBound β)
    have hMtop : M < ∞ := ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
    calc ∫⁻ θ, freeVillainDensity β Λ θ ∂freeVillainBase Λ ≤ ∫⁻ _, M ∂freeVillainBase Λ :=
          lintegral_mono fun θ => freeVillainDensity_le β hβ Λ θ
      _ = M * freeVillainBase Λ Set.univ := lintegral_const M
      _ < ∞ := ENNReal.mul_lt_top hMtop (freeVillainBase_univ_lt_top Λ)

end FroehlichSpencer.BKT.Bridge.FreeVillainLaw

end
