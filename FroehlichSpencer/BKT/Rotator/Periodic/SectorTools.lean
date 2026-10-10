/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.Offset

/-!
# Basic tools for paired winding sectors

Two elementary ingredients recur in a winding-sector proof. Opposite edge offsets give an
inversion-even sum of rooted densities, and a uniform lower bound on every sector ratio passes to
the ratio of the positive sector sums. This module proves those facts without claiming a torus
current decomposition or a sector estimate.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace FroehlichSpencer.BKT.Generic

variable {V E : Type} [Fintype V] [Fintype E]

/-- Inversion changes a fixed edge offset to its negative, away from the two root-window endpoints.
-/
theorem offsetEdgeDensity_neg_eq_negOffset_ae (G : Multigraph V E) {w : ℂ → ℂ} {W : ℝ}
    {c : ℝ → ℝ} (hw : IsStripWeight w W c) (θ : E → ℝ) (v : V) :
    ∀ᵐ φ : V → ℝ,
      offsetEdgeDensity G w θ v (-φ) = offsetEdgeDensity G w (-θ) v φ := by
  have hnull : ∀ x : ℝ, (volume : Measure (V → ℝ)) {φ | φ v = x} = 0 := fun x => by
    rw [volume_pi]
    exact Measure.pi_hyperplane (fun _ : V => (volume : Measure ℝ)) v x
  have h1 := measure_eq_zero_iff_ae_notMem.mp (hnull Real.pi)
  have h2 := measure_eq_zero_iff_ae_notMem.mp (hnull (-Real.pi))
  filter_upwards [h1, h2] with φ hφ1' hφ2'
  have hφ1 : φ v ≠ Real.pi := hφ1'
  have hφ2 : φ v ≠ -Real.pi := hφ2'
  unfold offsetEdgeDensity
  congr 1
  · refine Finset.prod_congr rfl fun e _ => ?_
    have hg : G.grad (-φ) e + θ e = -(G.grad φ e + (-θ e)) := by
      simp only [Multigraph.grad, Pi.neg_apply]
      ring
    rw [hg, Complex.ofReal_neg, hw.even _ (by simpa using hw.width_nonneg)]
    simp only [Pi.neg_apply]
  · have hiff : -φ v ∈ Set.Ico (-Real.pi) Real.pi ↔ φ v ∈ Set.Ico (-Real.pi) Real.pi := by
      simp only [Set.mem_Ico]
      constructor
      · rintro ⟨h1', h2'⟩
        exact ⟨by linarith, lt_of_le_of_ne (by linarith) hφ1⟩
      · rintro ⟨h1', h2'⟩
        exact ⟨by linarith, lt_of_le_of_ne (by linarith) (fun h => hφ2 (by linarith))⟩
    simp only [Pi.neg_apply]
    by_cases h : φ v ∈ Set.Ico (-Real.pi) Real.pi
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h), Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.mp h'))]

/-- The sum of the two opposite-offset rooted densities is even almost everywhere. -/
theorem oppositeOffsetPair_even_ae (G : Multigraph V E) {w : ℂ → ℂ} {W : ℝ}
    {c : ℝ → ℝ} (hw : IsStripWeight w W c) (θ : E → ℝ) (v : V) :
    ∀ᵐ φ : V → ℝ,
      offsetEdgeDensity G w θ v (-φ) + offsetEdgeDensity G w (-θ) v (-φ) =
        offsetEdgeDensity G w θ v φ + offsetEdgeDensity G w (-θ) v φ := by
  filter_upwards [offsetEdgeDensity_neg_eq_negOffset_ae G hw θ v,
    offsetEdgeDensity_neg_eq_negOffset_ae G hw (-θ) v] with φ hθ hneg
  rw [hθ, hneg]
  ring_nf

end FroehlichSpencer.BKT.Generic

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {ι : Type*}

/-- A pointwise sector comparison sums to the same comparison for absolutely convergent sector
series. This is the positive-sums step in passing a common sector-ratio bound to the full ratio.
-/
theorem sectorSums_lowerBound (Z N : ι → ℝ) {r : ℝ}
    (hZ : Summable Z) (hN : Summable N)
    (hsector : ∀ i, r * Z i ≤ N i) :
    r * (∑' i, Z i) ≤ ∑' i, N i := by
  calc
    r * (∑' i, Z i) = ∑' i, r * Z i := (hZ.tsum_mul_left r).symm
    _ ≤ ∑' i, N i := (hZ.mul_left r).tsum_le_tsum hsector hN

/-- If the total denominator sector weight is positive, a uniform sector comparison bounds the
ratio of the total marked and unmarked weights below by the same constant.
-/
theorem sectorRatio_lowerBound (Z N : ι → ℝ) {r : ℝ}
    (hZ : Summable Z) (hN : Summable N)
    (hden : 0 < ∑' i, Z i) (hsector : ∀ i, r * Z i ≤ N i) :
    r ≤ (∑' i, N i) / (∑' i, Z i) := by
  apply (le_div_iff₀ hden).2
  exact sectorSums_lowerBound Z N hZ hN hsector

end FroehlichSpencer.BKT.Rotator.Periodic

end
