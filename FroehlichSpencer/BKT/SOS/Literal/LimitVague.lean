/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitUniform

/-!
# Vague limits on a countable discrete space (the comb-inserted SOS construction)

On a countable space with measurable singletons a measure is the sum of its point masses, and
vague convergence `μ_j ⇀ ν` is the pointwise convergence `μ_j{a} → ν{a}`.

* `lintegral_le_of_tendsto_singleton` (Fatou): a uniform upper bound on `∫ g dμ_j` passes to `ν`.
* `le_lintegral_of_tendsto_singleton`: a lower bound on `∫ g dμ_j` passes to `ν` **provided the
  tails of `g` are uniformly small** (`Σ_{a∉F} g(a) μ_j{a} ≤ η`). This is the uniform
  integrability that a lower bound needs: a vague limit can lose mass at infinity.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

omit [Countable α] [MeasurableSingletonClass α] in
theorem tendsto_sum_singleton {μ : ℕ → Measure α} {ν : Measure α}
    (hconv : ∀ a, Tendsto (fun j => μ j {a}) atTop (𝓝 (ν {a}))) (g : α → ℝ≥0∞)
    (hg : ∀ a, g a ≠ ⊤) (s : Finset α) :
    Tendsto (fun j => ∑ a ∈ s, g a * μ j {a}) atTop (𝓝 (∑ a ∈ s, g a * ν {a})) :=
  tendsto_finsetSum s fun a _ => ENNReal.Tendsto.const_mul (hconv a) (Or.inr (hg a))

/-- **Fatou**: a uniform upper bound passes to the vague limit. -/
theorem lintegral_le_of_tendsto_singleton {μ : ℕ → Measure α} {ν : Measure α}
    (hconv : ∀ a, Tendsto (fun j => μ j {a}) atTop (𝓝 (ν {a}))) (g : α → ℝ≥0∞)
    (hg : ∀ a, g a ≠ ⊤) {B : ℝ≥0∞} (hB : ∀ᶠ j in atTop, ∫⁻ a, g a ∂μ j ≤ B) :
    ∫⁻ a, g a ∂ν ≤ B := by
  rw [lintegral_countable', ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => le_of_tendsto (tendsto_sum_singleton hconv g hg s) ?_
  filter_upwards [hB] with j hj
  rw [lintegral_countable'] at hj
  exact (ENNReal.sum_le_tsum s).trans hj

omit [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] in
theorem tsum_split_finset (f : α → ℝ≥0∞) (F : Finset α) :
    ∑' a, f a = ∑ a ∈ F, f a + ∑' a, (↑F : Set α)ᶜ.indicator f a := by
  classical
  have h1 : ∀ a, f a = (↑F : Set α).indicator f a + (↑F : Set α)ᶜ.indicator f a := fun a => by
    by_cases ha : a ∈ F <;> simp [Set.indicator, ha]
  rw [tsum_congr h1, ENNReal.tsum_add]
  congr 1
  rw [tsum_eq_sum (s := F) fun a ha => by simp [Set.indicator, ha]]
  exact Finset.sum_congr rfl fun a ha => by simp [Set.indicator, ha]

/-- **Lower bounds pass to the vague limit under uniform integrability.** -/
theorem le_lintegral_of_tendsto_singleton {μ : ℕ → Measure α} {ν : Measure α}
    (hconv : ∀ a, Tendsto (fun j => μ j {a}) atTop (𝓝 (ν {a}))) (g : α → ℝ≥0∞)
    (hg : ∀ a, g a ≠ ⊤)
    (htail : ∀ η : ℝ≥0∞, 0 < η → ∃ F : Finset α, ∀ᶠ j in atTop,
      ∑' a, (↑F : Set α)ᶜ.indicator g a * μ j {a} ≤ η)
    {B : ℝ≥0∞} (hB : ∀ᶠ j in atTop, B ≤ ∫⁻ a, g a ∂μ j) : B ≤ ∫⁻ a, g a ∂ν := by
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  obtain ⟨F, hF⟩ := htail η (by exact_mod_cast hη)
  have hsplit : ∀ j, ∫⁻ a, g a ∂μ j = ∑ a ∈ F, g a * μ j {a} +
      ∑' a, (↑F : Set α)ᶜ.indicator g a * μ j {a} := fun j => by
    rw [lintegral_countable', tsum_split_finset (fun a => g a * μ j {a}) F]
    congr 1
    refine tsum_congr fun a => ?_
    by_cases ha : a ∈ (↑F : Set α) <;> simp [Set.indicator, ha]
  have hlim := (tendsto_sum_singleton hconv g hg F).add_const (η : ℝ≥0∞)
  have hle : B ≤ ∑ a ∈ F, g a * ν {a} + η := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [hB, hF] with j hj hj'
    rw [hsplit] at hj
    exact hj.trans (add_le_add le_rfl hj')
  refine hle.trans (add_le_add ?_ le_rfl)
  rw [lintegral_countable']
  exact ENNReal.sum_le_tsum F

end FroehlichSpencer.BKT.SOS.Literal

end
