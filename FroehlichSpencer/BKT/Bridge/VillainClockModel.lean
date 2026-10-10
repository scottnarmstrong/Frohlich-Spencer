/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.VillainClockModel
public import FroehlichSpencer.BKT.Clock.VillainClock.Model
public import FroehlichSpencer.BKT.Clock.VillainClock.DualGinibre
public import FroehlichSpencer.BKT.Clock.VillainClock.DisorderCarrier
public import FroehlichSpencer.BKT.Clock.VillainClock.DisorderExhaustion
public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBox
@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.VillainClock
open FroehlichSpencer.BKT.Clock.Compact (integral_siteProduct_clockMeasure)

namespace FroehlichSpencer.BKT.Bridge.VillainClockModel

theorem villainClockModel_eq_gibbs (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β)
    (Λ : Finset (ℤ × ℤ)) :
    villainClockModel N hN β hβ Λ =
      (Clock.VillainClock.model N hN β hβ).gibbs Λ := by
  unfold villainClockModel Clock.VillainClock.model Ginibre.FreeModel.gibbs
    Ginibre.pairGibbs Ginibre.pairPartition Ginibre.siteProduct
  simp only [Ginibre.clockMeasure]
  have hweight (θ : Λ → ℝ) :
      (∏ b : Λ × Λ,
        (if (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨
            (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) then
          (fun x : ℝ => ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * m) ^ 2))
        else fun _ => 1) (θ b.1 - θ b.2)) =
      Ginibre.pairWeight (Rotator.Ginibre.bondFrequency Λ)
        ((Clock.VillainClock.model N hN β hβ).bondWeight Λ) θ := by
    simp only [Ginibre.pairWeight, Ginibre.FreeModel.bondWeight,
      Rotator.Ginibre.phase_bondFrequency]
    refine Finset.prod_congr rfl ?_
    intro b hb
    by_cases hs : (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨
        (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1)
    · simp [hs, Rotator.Ginibre.LatticeStep, Clock.VillainClock.model, villainWeight]
    · simp [hs, Rotator.Ginibre.LatticeStep]
  have hweightFun :
      (fun θ : Λ → ℝ =>
        ∏ b : Λ × Λ,
          (if (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨
              (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) then
            (fun x : ℝ => ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * m) ^ 2))
          else fun _ => 1) (θ b.1 - θ b.2)) =
      (fun θ => Ginibre.pairWeight (Rotator.Ginibre.bondFrequency Λ)
        ((Clock.VillainClock.model N hN β hβ).bondWeight Λ) θ) := by
    funext θ
    exact hweight θ
  congr 1
  funext θ
  apply congrArg ENNReal.ofReal
  congr 1
  · exact hweight θ
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall hweight

theorem villainClockLaw_integral_eq_sum (N K : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β)
    (F : (squareBoxZ K → ℝ) → ℝ) :
    ∫ θ, F θ ∂(model N hN β hβ).gibbs (squareBoxZ K) =
      (∑ s : RotatorSpinSite K → Fin N,
          F (fun z => clockAngle N (s ((squareBoxEquiv K).symm z))) *
            configurationWeight (rotatorFreeGraph K) β N s) /
        ∑ s : RotatorSpinSite K → Fin N, configurationWeight (rotatorFreeGraph K) β N s := by
  classical
  have hν : (model N hN β hβ).ν = clockMeasure N := rfl
  rw [Ginibre.FreeModel.gibbs, Ginibre.integral_pairGibbs
    (model N hN β hβ).mass_ne_zero
    ((model N hN β hβ).isBondWeight_bondWeight (squareBoxZ K)),
    Ginibre.pairPartition, hν, integral_siteProduct_clockMeasure,
    integral_siteProduct_clockMeasure]
  have he' : ∀ (k : squareBoxZ K → Fin N) (p : RotatorSpinSite K),
      (Equiv.arrowCongr (squareBoxEquiv K).symm (Equiv.refl (Fin N))) k p =
        k (squareBoxEquiv K p) := fun k p => rfl
  congr 1
  · refine Fintype.sum_equiv
      (Equiv.arrowCongr (squareBoxEquiv K).symm (Equiv.refl (Fin N))) _ _ fun k => ?_
    rw [villainClockModel_pairWeight_squareBox N K hN hβ]
    simp only [configurationWeight, angleField, clockAngle, he']
    congr 1
    simp only [Equiv.apply_symm_apply]
  · refine Fintype.sum_equiv
      (Equiv.arrowCongr (squareBoxEquiv K).symm (Equiv.refl (Fin N))) _ _ fun k => ?_
    rw [villainClockModel_pairWeight_squareBox N K hN hβ]
    simp only [configurationWeight, angleField, clockAngle, he']

end FroehlichSpencer.BKT.Bridge.VillainClockModel

end
