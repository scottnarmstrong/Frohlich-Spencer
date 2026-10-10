/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.VillainClockDisorderLimit
public import FroehlichSpencer.BKT.Bridge.VillainClockModel
public import FroehlichSpencer.BKT.Clock.VillainClock.DualGinibre
public import FroehlichSpencer.BKT.Clock.VillainClock.DisorderCarrier
public import FroehlichSpencer.BKT.Clock.VillainClock.DisorderExhaustion
public import FroehlichSpencer.BKT.Clock.Compact.FejerLimit
public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBox

@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.VillainClock
open FroehlichSpencer.BKT.Clock.Compact (integral_siteProduct_clockMeasure)
open FroehlichSpencer.BKT.Bridge.VillainClockModel

namespace FroehlichSpencer.BKT.Bridge.VillainClockDisorder

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

private def disorderBoxLower {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (m : Fin r) :
    RotatorSpinSite (2 * L) :=
  (⟨L + m.val + 1, by have hm := m.isLt; omega⟩, ⟨L, by omega⟩)

private def disorderBoxUpper {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (m : Fin r) :
    RotatorSpinSite (2 * L) :=
  (⟨L + m.val + 1, by have hm := m.isLt; omega⟩, ⟨L + 1, by omega⟩)

theorem villainClockDisorderObservable_eq_freeSquareDisorderObservable
    (N L r : ℕ) (β ξ : ℝ) (hβ : 0 < β) (s : RotatorSpinSite (2 * L) → Fin N)
    (hL : 0 < L) (hr : r ≤ L) :
    let Λ := squareBoxZ (2 * L)
    villainClockDisorderObservable β hβ ξ L r Λ
      (fun m => by
        have hm := m.isLt
        dsimp [Λ, squareBoxZ]
        constructor <;> simp only [Finset.mem_product, Finset.mem_Icc] <;> omega)
      (fun z => clockAngle N (s ((squareBoxEquiv (2 * L)).symm z))) =
      freeSquareDisorderObservable N β ξ s hL hr := by
  classical
  intro Λ
  let lower : Fin r → ℤ × ℤ := fun m =>
    ((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ))
  let upper : Fin r → ℤ × ℤ := fun m =>
    ((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ) + 1)
  have hsites (m : Fin r) : lower m ∈ Λ ∧ upper m ∈ Λ := by
    have hm := m.isLt
    dsimp [Λ, lower, upper, squareBoxZ]
    constructor <;> simp only [Finset.mem_product, Finset.mem_Icc] <;> omega
  have hlow (m : Fin r) :
      (⟨lower m, (hsites m).1⟩ : squareBoxZ (2 * L)) =
        squareBoxEquiv (2 * L) (disorderSeamLower hL hr m) := by
    apply Subtype.ext
    rw [squareBoxEquiv_apply_coe]
    simp [lower, disorderSeamLower, siteToZ]
  have hupp (m : Fin r) :
      (⟨upper m, (hsites m).2⟩ : squareBoxZ (2 * L)) =
        squareBoxEquiv (2 * L) (disorderSeamUpper hL hr m) := by
    apply Subtype.ext
    rw [squareBoxEquiv_apply_coe]
    simp [upper, disorderSeamUpper, siteToZ]
  have hlowθ (m : Fin r) :
      (fun z => clockAngle N (s ((squareBoxEquiv (2 * L)).symm z)))
          ⟨lower m, (hsites m).1⟩ = clockAngle N (s (disorderSeamLower hL hr m)) := by
    rw [hlow]
    simp
  have huppθ (m : Fin r) :
      (fun z => clockAngle N (s ((squareBoxEquiv (2 * L)).symm z)))
          ⟨upper m, (hsites m).2⟩ = clockAngle N (s (disorderSeamUpper hL hr m)) := by
    rw [hupp]
    simp
  unfold villainClockDisorderObservable freeSquareDisorderObservable freeSquareDisorderFactor
  apply Finset.prod_congr rfl
  intro m hm
  rw [hlowθ, huppθ]
  rfl

theorem villainClockDisorderExpectation_eq_freeSquareDisorderExpectation
    (N L r : ℕ) (β ξ : ℝ) (hN : 0 < N) (hβ : 0 < β)
    (hL : 0 < L) (hr : r ≤ L) :
    villainClockDisorderExpectation N hN β hβ ξ L r hL hr =
      freeSquareDisorderExpectation N β ξ hβ hN hL hr := by
  classical
  let Λ := squareBoxZ (2 * L)
  let lower : Fin r → ℤ × ℤ := fun m =>
    ((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ))
  let upper : Fin r → ℤ × ℤ := fun m =>
    ((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ) + 1)
  have hsites (m : Fin r) : lower m ∈ Λ ∧ upper m ∈ Λ := by
    have hm := m.isLt
    dsimp [Λ, lower, upper, squareBoxZ]
    constructor <;> simp only [Finset.mem_product, Finset.mem_Icc] <;> omega
  have hobs (s : RotatorSpinSite (2 * L) → Fin N) :
      villainClockDisorderObservable β hβ ξ L r Λ hsites
        (fun z => clockAngle N (s ((squareBoxEquiv (2 * L)).symm z))) =
        freeSquareDisorderObservable N β ξ s hL hr := by
    simpa [Λ, lower, upper] using
      (villainClockDisorderObservable_eq_freeSquareDisorderObservable
        N L r β ξ hβ s hL hr)
  unfold villainClockDisorderExpectation
  change ∫ θ, villainClockDisorderObservable β hβ ξ L r Λ hsites θ ∂
      villainClockModel N hN β hβ Λ =
    freeSquareDisorderExpectation N β ξ hβ hN hL hr
  rw [villainClockModel_eq_gibbs]
  rw [villainClockLaw_integral_eq_sum N (2 * L) hN β hβ
    (fun θ => villainClockDisorderObservable β hβ ξ L r Λ hsites θ)]
  unfold freeSquareDisorderExpectation freeSquarePartitionFunction freeSquareConfigurationWeight
  congr 1

theorem isVillainClockDisorderExhaustingLimitPoint_iff
    (N r : ℕ) (β ξ c : ℝ) (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) :
    IsVillainClockDisorderExhaustingLimitPoint N r β ξ c hβ hN hr ↔
      IsFreeSquareDisorderExhaustingLimitPoint N r β ξ c hβ hN hr := by
  unfold IsVillainClockDisorderExhaustingLimitPoint IsFreeSquareDisorderExhaustingLimitPoint
  constructor
  · rintro ⟨s, hs, hst, hlim⟩
    refine ⟨s, hs, hst, ?_⟩
    have hfun :
        (fun t => villainClockDisorderExpectation N hN β hβ ξ (r + s t) r
          (by omega) (by omega)) =
        (fun t => freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr (s t)) := by
      funext t
      simpa [freeSquareDisorderExpectationExhaustion] using
        (villainClockDisorderExpectation_eq_freeSquareDisorderExpectation
          N (r + s t) r β ξ hN hβ (by omega) (by omega))
    rw [hfun] at hlim
    exact hlim
  · rintro ⟨s, hs, hst, hlim⟩
    refine ⟨s, hs, hst, ?_⟩
    have hfun :
        (fun t => villainClockDisorderExpectation N hN β hβ ξ (r + s t) r
          (by omega) (by omega)) =
        (fun t => freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr (s t)) := by
      funext t
      simpa [freeSquareDisorderExpectationExhaustion] using
        (villainClockDisorderExpectation_eq_freeSquareDisorderExpectation
          N (r + s t) r β ξ hN hβ (by omega) (by omega))
    rw [hfun]
    exact hlim


end FroehlichSpencer.BKT.Bridge.VillainClockDisorder

end
