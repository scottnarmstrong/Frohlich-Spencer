/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.FreeVillainDisorder
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.Gauge
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedEstimate
import Mathlib.Tactic


@[expose] public section

open MeasureTheory

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.FreeVillainDisorderGauge

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.VillainDisorder.Dirichlet FroehlichSpencer.BKT.Villain.TheoremC
open FroehlichSpencer.BKT.Bridge.FreeVillainDisorder


theorem unpinnedBoxVillainLaw_eq (R : ℕ) (β : ℝ) (hβ : 0 < β) :
    unpinnedBoxVillainLaw R β = villainGraphGibbs (graph' R) β := by
  have hw : ∀ e : RotatorInternalBond (sideLength R),
      IsBondWeight ((fun _ => villainWeight β) e) := fun _ => isBondWeight_villain hβ
  have hZ := pairPartition_pos (ν := circleMeasure) (d := multigraphFrequency (graph' R))
    circleMeasure_univ_ne_zero hw
  have hdens : boxDensity R β = fun θ =>
      ENNReal.ofReal
        (pairWeight (multigraphFrequency (graph' R)) (fun _ => villainWeight β) θ) := by
    funext θ
    unfold boxDensity pairWeight
    rw [ENNReal.ofReal_prod_of_nonneg fun e _ => (VillainWeight.villainWeight_pos hβ _).le]
    simp_rw [phase_multigraphFrequency]
  have hraw : boxBase R = siteProduct circleMeasure (FreeVillainDisorder.Site R) := rfl
  have hmass : ((siteProduct circleMeasure (FreeVillainDisorder.Site R)).withDensity fun θ =>
      ENNReal.ofReal (pairWeight (multigraphFrequency (graph' R)) (fun _ => villainWeight β) θ))
        Set.univ =
      ENNReal.ofReal (pairPartition circleMeasure (multigraphFrequency (graph' R))
        (fun _ => villainWeight β)) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, pairPartition,
      ofReal_integral_eq_lintegral_ofReal (integrable_pairWeight hw)
        (ae_of_all _ fun θ => (pairWeight_pos hw θ).le)]
  unfold unpinnedBoxVillainLaw villainGraphGibbs pairGibbs
  rw [hdens, hraw, hmass]
  ext s hs
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs, withDensity_apply _ hs,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hZ).ne')]
  refine lintegral_congr fun θ => ?_
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]


theorem gaugeInput_of_VD5 : GaugeInput := by
  intro R n hn β hβ ξ
  rw [unpinnedBoxVillainLaw_eq R β hβ]
  exact fullVillainShiftRatio_integral_eq_rooted (graph' R) (dirichletRoot R) β hβ _


theorem freeVillain_disorderLimit_upper_bound_of_D2 (hD2 : RootedDirichletFejerGlobalInput) :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      (∃ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D) ∧
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D →
        ∀ n : ℕ, D n ≤ A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) :=
  freeVillain_disorderLimit_upper_bound_of_inputs hD2 gaugeInput_of_VD5


theorem freeVillain_disorderLimit_upper_bound_of_marked (hE : RootedFejerMarkedExtension) :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      (∃ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D) ∧
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D →
        ∀ n : ℕ, D n ≤ A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) :=
  freeVillain_disorderLimit_upper_bound_of_D2 (rootedDirichletFejerEstimate_of_markedExtension hE)

end FroehlichSpencer.BKT.Bridge.FreeVillainDisorderGauge

end
