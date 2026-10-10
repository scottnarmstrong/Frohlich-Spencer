/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeLaw.Defs

/-!
# The rooted edge density is even almost everywhere (generic core)

For an even strip
weight the rooted density `∏_e w(∇φ(e)) · 𝟙_{[-π, π)}(φ(v))` is invariant under `φ ↦ −φ` except
on the null set `φ(v) = ±π`, where the half-open root window is not symmetric
(`edgeDensity_neg_ae`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory

variable {V : Type*} [Fintype V] {E : Type*} [Fintype E]

/-- The rooted edge density is even off the null set `φ(v) = ±π`. -/
theorem edgeDensity_neg_ae (G : Multigraph V E) {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
    (hw : IsStripWeight w W c) (v : V) :
    ∀ᵐ φ : V → ℝ, edgeDensity G w v (-φ) = edgeDensity G w v φ := by
  have hnull : ∀ x : ℝ, (volume : Measure (V → ℝ)) {φ | φ v = x} = 0 := fun x => by
    rw [volume_pi]; exact Measure.pi_hyperplane (fun _ : V => (volume : Measure ℝ)) v x
  have h1 := measure_eq_zero_iff_ae_notMem.mp (hnull Real.pi)
  have h2 := measure_eq_zero_iff_ae_notMem.mp (hnull (-Real.pi))
  filter_upwards [h1, h2] with φ hφ1' hφ2'
  have hφ1 : φ v ≠ Real.pi := hφ1'
  have hφ2 : φ v ≠ -Real.pi := hφ2'
  unfold edgeDensity
  congr 1
  · refine Finset.prod_congr rfl fun e _ => ?_
    have hg : G.grad (-φ) e = -G.grad φ e := by
      simp only [Multigraph.grad, Pi.neg_apply]; ring
    rw [hg, Complex.ofReal_neg, hw.even _ (by simpa using hw.width_nonneg)]
  · have hiff : -φ v ∈ Set.Ico (-Real.pi) Real.pi ↔ φ v ∈ Set.Ico (-Real.pi) Real.pi := by
      simp only [Set.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, lt_of_le_of_ne (by linarith) hφ1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, lt_of_le_of_ne (by linarith) (fun h => hφ2 (by linarith))⟩
    simp only [Pi.neg_apply]
    by_cases h : φ v ∈ Set.Ico (-Real.pi) Real.pi
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h), Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.mp h'))]

end FroehlichSpencer.BKT.Generic

end
