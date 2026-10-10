/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.PlaneRotatorLaw
public import FroehlichSpencer.BKT.Rotator.Ginibre.FreeLimit
public import Mathlib.Probability.Notation
import Mathlib.Tactic

/-!
`planeRotatorLaw β Λ` (FS81 (1.26), source) is the internal
`Ginibre.freeRotatorMeasure β Λ` (`planeRotatorLaw_eq_freeRotatorMeasure`), and its two-point
functions converge along the net of finite regions to the Ginibre free limit
(`tendsto_planeRotatorTwoPoint`).

These lemmas prove the gates
`isProbabilityMeasure_planeRotatorLaw` and `existsUnique_tendsto_planeRotatorTwoPoint` (providers in
`BKT/Provider/`).
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.PlaneRotatorLaw

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Rotator FroehlichSpencer.BKT.Rotator.Ginibre

theorem planeRotator_density_eq (β : ℝ) (Λ : Finset (ℤ × ℤ)) (θ : Λ → ℝ) :
    (∏ b ∈ (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)),
        ENNReal.ofReal (Real.exp (β * Real.cos (θ b.1 - θ b.2)))) =
      ENNReal.ofReal (cosineWeight (bondFrequency Λ) (freeCoupling β Λ) θ) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun b _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [cosineEnergy, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [phase_bondFrequency, freeCoupling]
  unfold LatticeStep
  by_cases h : (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) <;>
    simp [h]

theorem planeRotatorLaw_eq_freeRotatorMeasure (β : ℝ) (Λ : Finset (ℤ × ℤ)) :
    planeRotatorLaw β Λ = freeRotatorMeasure β Λ := by
  set d := bondFrequency Λ
  set J := freeCoupling β Λ
  have hZ := cosinePartition_pos d J
  have hdens : (fun θ : Λ → ℝ => ∏ b ∈ (Finset.univ : Finset (Λ × Λ)).filter (fun b : Λ × Λ =>
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨ (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)),
        ENNReal.ofReal (Real.exp (β * Real.cos (θ b.1 - θ b.2)))) =
      fun θ => ENNReal.ofReal (cosineWeight d J θ) :=
    funext (planeRotator_density_eq β Λ)
  have hraw : (Measure.pi fun _ : Λ => volume.restrict (Set.Ico (-Real.pi) Real.pi)) =
      rotatorRawAngleMeasure Λ := rfl
  have hmass : ((rotatorRawAngleMeasure Λ).withDensity
      fun θ => ENNReal.ofReal (cosineWeight d J θ)) Set.univ = ENNReal.ofReal (cosinePartition d J) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, cosinePartition,
      ofReal_integral_eq_lintegral_ofReal (integrable_cosineWeight d J)
        (ae_of_all _ fun θ => (cosineWeight_pos d J θ).le)]
  unfold planeRotatorLaw freeRotatorMeasure cosineGibbs
  simp only [hdens, hraw]
  rw [hmass]
  ext s hs
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs, withDensity_apply _ hs,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hZ).ne')]
  refine lintegral_congr fun θ => ?_
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]

/-- The regions containing `j` and `ℓ` are directed under inclusion. -/
theorem atTop_neBot_regions (j ℓ : ℤ × ℤ) :
    (atTop : Filter {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ}).NeBot := by
  have : Nonempty {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} :=
    ⟨⟨{j, ℓ}, by simp, by simp⟩⟩
  have : IsDirected {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} (· ≤ ·) :=
    ⟨fun a b => ⟨⟨a.1 ∪ b.1, Finset.mem_union_left _ a.2.1, Finset.mem_union_left _ a.2.2⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩⟩
  exact atTop_neBot

theorem twoPoint_eq (β : ℝ) (ξ : ℤ) (j ℓ : ℤ × ℤ)
    (Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ}) :
    (∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩))
        ∂planeRotatorLaw β Λ.1) = freeTwoPoint β ξ Λ.1 j ℓ := by
  rw [planeRotatorLaw_eq_freeRotatorMeasure, freeTwoPoint]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [latticeAngle, dite_eq_left Λ.2.1, dite_eq_left Λ.2.2]

theorem tendsto_planeRotatorTwoPoint (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (j ℓ : ℤ × ℤ) :
    Tendsto (fun Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} =>
      ∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩))
        ∂planeRotatorLaw β Λ.1) atTop (𝓝 (freeTwoPointLimit β hβ ξ j ℓ)) := by
  simp only [twoPoint_eq]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨L, hL, hL₀⟩ := (((tendsto_freeTwoPointLimit hβ ξ j ℓ).eventually
      (lt_mem_nhds ha)).and (eventually_ge_atTop (max (boxRadius j) (boxRadius ℓ)))).exists
    have hj : j ∈ freeBox L := mem_freeBox_of_boxRadius_le ((le_max_left _ _).trans hL₀)
    have hl : ℓ ∈ freeBox L := mem_freeBox_of_boxRadius_le ((le_max_right _ _).trans hL₀)
    filter_upwards [eventually_ge_atTop (⟨freeBox L, hj, hl⟩ :
        {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ})] with Λ hΛ
    exact hL.trans_le (freeTwoPoint_mono_domain hβ ξ hΛ hj hl)
  · exact Eventually.of_forall fun Λ =>
      (freeTwoPoint_le_freeTwoPointLimit hβ ξ Λ.2.1 Λ.2.2).trans_lt ha

end FroehlichSpencer.BKT.Bridge.PlaneRotatorLaw

end
