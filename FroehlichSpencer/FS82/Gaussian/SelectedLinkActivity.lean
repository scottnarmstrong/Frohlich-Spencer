/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-!
# selected-link scalar bounds

Finite-sum activity attenuation and the real-tilt Gaussian phase.
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Gaussian.SelectedLinkActivity

/-- A weighted selected-link energy bound implies the source's `1/216` decay. -/
theorem selectedLinkEnergy_at_least_one216
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Finset ι) (β : ℝ) (ρ : ι → ℝ) (n : ι → ℕ)
    (hβ : 0 ≤ β) (hTS : T ⊆ S)
    (hnpos : ∀ b ∈ T, 0 < n b) (hnle : ∀ b ∈ T, n b ≤ 6)
    (hcapture : (∑ b ∈ S, ρ b ^ 2) / 18 ≤ ∑ b ∈ T, ρ b ^ 2) :
    Real.exp (-((β / 2) * ∑ b ∈ T, ρ b ^ 2 / (n b : ℝ))) ≤
      Real.exp (-((β / 216) * ∑ b ∈ S, ρ b ^ 2)) := by
  apply Real.exp_le_exp.mpr
  have hlocal : ∀ b ∈ T, ρ b ^ 2 / 6 ≤ ρ b ^ 2 / (n b : ℝ) := by
    intro b hb
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6)
      (by exact_mod_cast (hnpos b hb))]
    have hn := hnle b hb
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn)
      (sq_nonneg (ρ b))
  have hsum := Finset.sum_le_sum hlocal
  have hscaled : (∑ b ∈ T, ρ b ^ 2) / 6 ≤
      ∑ b ∈ T, ρ b ^ 2 / (n b : ℝ) := by
    simpa [Finset.sum_div] using hsum
  have hsub : ∑ b ∈ T, ρ b ^ 2 ≤ ∑ b ∈ S, ρ b ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hTS
    intro b hbS hbT
    exact sq_nonneg (ρ b)
  have htarget : (∑ b ∈ S, ρ b ^ 2) / 108 ≤
      ∑ b ∈ T, ρ b ^ 2 / (n b : ℝ) := by
    have hcap := hcapture
    have hscaledCapture : (∑ b ∈ S, ρ b ^ 2) / 108 ≤
        (∑ b ∈ T, ρ b ^ 2) / 6 := by linarith
    linarith
  have hmul := mul_le_mul_of_nonneg_left htarget
    (div_nonneg hβ (by norm_num : (0 : ℝ) ≤ 2))
  have hscaledTarget : (β / 216) * (∑ b ∈ S, ρ b ^ 2) ≤
      (β / 2) * ∑ b ∈ T, ρ b ^ 2 / (n b : ℝ) := by
    nlinarith [hmul]
  linarith

/-- The extra phase and scalar factor produced when a real tilt meets a selected
Gaussian coordinate. This is the completed-square identity behind the `t`-dependent
version of Lemma 3. -/
theorem tiltedGaussianExponent_factor (a q t v : ℝ) :
    Complex.exp (((t * a : ℂ) + Complex.I * (q : ℂ)) ^ 2 * (v : ℂ) / 2) =
      Complex.exp ((t * a : ℂ) ^ 2 * (v : ℂ) / 2) *
        Complex.exp (-((q : ℂ) ^ 2) * (v : ℂ) / 2) *
          Complex.exp (Complex.I * (q : ℂ) * (t * a : ℂ) * (v : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring_nf
  simp only [Complex.I_sq]
  ring


/-- The selected Gaussian attenuation is bounded by the source's uniform
`1/216` decay after inserting the activity coefficient. -/
theorem renormalizedActivity_le_one216
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Finset ι) (β K : ℝ) (ρ : ι → ℝ) (n : ι → ℕ)
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (hTS : T ⊆ S)
    (hnpos : ∀ b ∈ T, 0 < n b) (hnle : ∀ b ∈ T, n b ≤ 6)
    (hcapture : (∑ b ∈ S, ρ b ^ 2) / 18 ≤ ∑ b ∈ T, ρ b ^ 2) :
    K * Real.exp (-((β / 2) * ∑ b ∈ T, ρ b ^ 2 / (n b : ℝ))) ≤
      K * Real.exp (-((β / 216) * ∑ b ∈ S, ρ b ^ 2)) := by
  exact mul_le_mul_of_nonneg_left
    (selectedLinkEnergy_at_least_one216 S T β ρ n hβ hTS hnpos hnle hcapture) hK


end FroehlichSpencer.FS82.Gaussian.SelectedLinkActivity

end
