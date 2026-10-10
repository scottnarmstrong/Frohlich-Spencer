/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.SquarePeriodic
public import FroehlichSpencer.BKT.Rotator.XYDualityFourier
public import FroehlichSpencer.BKT.Rotator.CosineFourierSummable

/-!
# Fourier-current identities on the periodic XY torus

The finite torus uses the `squarePeriodic` carrier.

This module records the full current
sum, before any decomposition into height and winding sectors.

In particular the normalization
from raw angle integration is explicit: it is `(2π)^{|V_L|}` for both the partition function and
the marked character numerator.
-/

@[expose] public section

open Complex MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Villain
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {L : ℕ}

/-- The spin sites of the periodic torus of side `L`. -/
abbrev Site (L : ℕ) := Fin L × Fin L

/-- The positively oriented edge carrier of the periodic torus of side `L`. -/
abbrev Bond (L : ℕ) := SquarePeriodicEdge L

/-- The periodic torus graph with the source orientation fixed by `squarePeriodic`. -/
def graph (L : ℕ) : Multigraph (Site L) (Bond L) := squarePeriodic L

/-- Real angle representatives at the periodic spin sites. -/
abbrev Angles (L : ℕ) := Site L → ℝ

/-- The XY Boltzmann density on the periodic torus, with one factor per unoriented bond. -/
def spinDensity (L : ℕ) (β : ℝ) (θ : Angles L) : ℝ :=
  ∏ e : Bond L, Real.exp (β * Real.cos
    (θ ((graph L).src e) - θ ((graph L).tgt e)))

/-- Raw integration of the periodic XY density over `[-π,π)` at each site. -/
def partitionIntegral (L : ℕ) (β : ℝ) : ℝ :=
  ∫ θ : Angles L, spinDensity L β θ ∂rotatorRawAngleMeasure (Site L)

/-- The integer spin character on the periodic torus. -/
def spinCharacter (L : ℕ) (a x : Site L) (ξ : ℤ) (θ : Angles L) : ℂ :=
  Complex.exp (Complex.I * (ξ : ℂ) * ((θ a - θ x : ℝ) : ℂ))

/-- The raw marked numerator for a periodic two-point character. -/
def markedIntegral (L : ℕ) (β : ℝ) (a x : Site L) (ξ : ℤ) : ℂ :=
  ∫ θ : Angles L, (spinDensity L β θ : ℂ) * spinCharacter L a x ξ θ
    ∂rotatorRawAngleMeasure (Site L)

private theorem bondFourierExpansion (β t : ℝ) :
    rotatorBondReal β t = ∑' m : ℤ,
      rotatorI β m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)) := by
  simpa [rotatorBondReal] using (hasSum_rotatorI_mul_exp β t).tsum_eq.symm

private theorem bondFourierExpansion_negativePhase (β t : ℝ) :
    rotatorBondReal β t = ∑' m : ℤ,
      rotatorI β m * Complex.exp (-Complex.I * (m : ℂ) * (t : ℂ)) :=
  rotatorI_negativePhase_expansion β t (fun s => bondFourierExpansion β s)

private theorem phaseProduct_eq_divergence (q : Bond L → ℤ) (θ : Angles L) :
    (∏ e : Bond L, Complex.exp (-Complex.I * (q e : ℂ) *
      (((θ ((graph L).src e) - θ ((graph L).tgt e)) : ℝ) : ℂ))) =
      ∏ v : Site L, Complex.exp (Complex.I *
        (-(currentDivergence (graph L) q v : ℂ)) * (θ v : ℂ)) := by
  classical
  have hpair := Villain.currentDivergence_pairing (graph L) q (fun v => (θ v : ℂ))
  have hsum :
      ∑ e : Bond L, -Complex.I * (q e : ℂ) *
          (((θ ((graph L).src e) - θ ((graph L).tgt e)) : ℝ) : ℂ) =
        ∑ v : Site L, Complex.I * (-(currentDivergence (graph L) q v : ℂ)) *
          (θ v : ℂ) := by
    calc
      _ = ∑ e : Bond L, (-Complex.I) * ((q e : ℂ) *
          ((θ ((graph L).src e) : ℂ) - (θ ((graph L).tgt e) : ℂ))) := by
            apply Finset.sum_congr rfl
            intro e he
            simp only [Complex.ofReal_sub]
            ring
      _ = -Complex.I * ∑ e : Bond L, (q e : ℂ) *
          ((θ ((graph L).src e) : ℂ) - (θ ((graph L).tgt e) : ℂ)) := by
            rw [Finset.mul_sum]
      _ = -Complex.I * ∑ v : Site L,
          (currentDivergence (graph L) q v : ℂ) * (θ v : ℂ) := by
            rw [hpair]
      _ = ∑ v : Site L, (-Complex.I) *
          ((currentDivergence (graph L) q v : ℂ) * (θ v : ℂ)) := by
            rw [Finset.mul_sum]
      _ = ∑ v : Site L, Complex.I *
          (-(currentDivergence (graph L) q v : ℂ)) * (θ v : ℂ) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
  calc
    _ = Complex.exp (∑ e : Bond L, -Complex.I * (q e : ℂ) *
        (((θ ((graph L).src e) - θ ((graph L).tgt e)) : ℝ) : ℂ)) := by
          rw [← Complex.exp_sum]
    _ = Complex.exp (∑ v : Site L, Complex.I *
        (-(currentDivergence (graph L) q v : ℂ)) * (θ v : ℂ)) := by rw [hsum]
    _ = _ := by rw [Complex.exp_sum]

private theorem phase_norm (m : ℤ) (t : ℝ) :
    ‖Complex.exp (-Complex.I * (m : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hreal : (-Complex.I * (m : ℂ) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hreal, Real.exp_zero]

/-- The periodic XY density has its absolutely convergent full integer-current expansion. -/
theorem spinDensity_currentSeries (β : ℝ) (hI : Summable (rotatorI β))
    (θ : Angles L) :
    (spinDensity L β θ : ℂ) =
      ∑' q : Bond L → ℤ,
        rotatorCurrentFourierTerm (graph L) (rotatorIReal β) q (fun _ => 0) θ := by
  classical
  let a (e : Bond L) (m : ℤ) : ℂ :=
    rotatorI β m * Complex.exp (-Complex.I * (m : ℂ) *
      (((θ ((graph L).src e) - θ ((graph L).tgt e)) : ℝ) : ℂ))
  have ha : ∀ e : Bond L, Summable (fun m : ℤ => ‖a e m‖) := by
    intro e
    have h := hI.norm
    apply h.congr
    intro m
    simp only [a, Complex.norm_mul, phase_norm, mul_one]
  have hprod := Villain.tsum_prod_currents a ha
  calc
    (spinDensity L β θ : ℂ) =
        ∏ e : Bond L, rotatorBondReal β
          (θ ((graph L).src e) - θ ((graph L).tgt e)) := by
            unfold spinDensity rotatorBondReal
            simp [Complex.ofReal_prod, Complex.ofReal_exp]
    _ = ∏ e : Bond L, ∑' m : ℤ, a e m := by
          apply Finset.prod_congr rfl
          intro e he
          simpa [a] using (bondFourierExpansion_negativePhase β
            (θ ((graph L).src e) - θ ((graph L).tgt e)))
    _ = ∑' q : Bond L → ℤ, ∏ e, a e (q e) := hprod
    _ = ∑' q : Bond L → ℤ,
          rotatorCurrentFourierTerm (graph L) (rotatorIReal β) q (fun _ => 0) θ := by
          apply tsum_congr
          intro q
          rw [rotatorCurrentFourierTerm]
          have hcoeff : ∏ e : Bond L, rotatorI β (q e) =
              (rotatorCurrentWeight (rotatorIReal β) q : ℂ) := by
            simp [rotatorCurrentWeight, rotatorI_eq_realCast]
          rw [show (∏ e : Bond L, a e (q e)) =
              (∏ e : Bond L, rotatorI β (q e)) *
                ∏ e : Bond L, Complex.exp (-Complex.I * (q e : ℂ) *
                  (((θ ((graph L).src e) - (θ ((graph L).tgt e))) : ℝ) : ℂ)) by
                    simp [a, Finset.prod_mul_distrib]]
          rw [hcoeff, phaseProduct_eq_divergence]
          simp

private theorem currentWeight_summable (β : ℝ) (hI : Summable (rotatorI β)) :
    Summable (fun q : Bond L → ℤ =>
      |rotatorCurrentWeight (rotatorIReal β) q|) := by
  have h := Villain.summable_norm_prod_currents (E := Bond L)
    (fun _ m => rotatorI β m) (fun _ => hI.norm)
  apply h.congr
  intro q
  rw [rotatorCurrentWeight]
  rw [show (∏ e : Bond L, rotatorI β (q e)) =
      ((∏ e : Bond L, rotatorIReal β (q e) : ℝ) : ℂ) by
        simp [rotatorI_eq_realCast]]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- Exact torus partition current identity, including the raw angle-volume factor. -/
theorem partitionIntegral_currentIdentity (β : ℝ) (hI : Summable (rotatorI β)) :
    (partitionIntegral L β : ℂ) =
      (∑' q : Bond L → ℤ,
        if ∀ v, currentDivergence (graph L) q v = 0 then
          (rotatorCurrentWeight (rotatorIReal β) q : ℂ) else 0) *
        (2 * Real.pi : ℂ) ^ Fintype.card (Site L) := by
  let μ := rotatorRawAngleMeasure (Site L)
  have hweight := currentWeight_summable (L := L) β hI
  calc
    (partitionIntegral L β : ℂ) =
        ∫ θ : Angles L, (spinDensity L β θ : ℂ) ∂μ := by
          exact (integral_ofReal (f := spinDensity L β) (μ := μ)).symm
    _ = ∫ θ : Angles L,
          ∑' q : Bond L → ℤ,
            rotatorCurrentFourierTerm (graph L) (rotatorIReal β) q (fun _ => 0) θ ∂μ := by
          apply integral_congr_ae
          filter_upwards with θ
          exact spinDensity_currentSeries (L := L) β hI θ
    _ = _ := by
          simpa [μ] using rotatorPartitionCurrentSeries_integral
            (graph L) (rotatorIReal β) hweight

private theorem frequency_sum (a x : Site L) (ξ : ℤ) (θ : Angles L) :
    ∑ v : Site L, (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ) =
      (ξ : ℂ) * (θ a : ℂ) - (ξ : ℂ) * (θ x : ℂ) := by
  classical
  unfold rotatorTwoPointFrequency
  simp only [Int.cast_add]
  calc
    _ = ∑ v : Site L,
        (↑(if v = a then ξ else 0) * (θ v : ℂ) +
          ↑(if v = x then -ξ else 0) * (θ v : ℂ)) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
    _ = (ξ : ℂ) * (θ a : ℂ) + (-ξ : ℂ) * (θ x : ℂ) := by
            rw [Finset.sum_add_distrib]
            simp
    _ = _ := by ring

private theorem spinCharacter_vertexProduct (a x : Site L) (ξ : ℤ) (θ : Angles L) :
    spinCharacter L a x ξ θ =
      ∏ v : Site L, Complex.exp (Complex.I *
        (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ)) := by
  have harg :
      ∑ v : Site L, Complex.I * (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ) =
        Complex.I * (ξ : ℂ) * ((θ a - θ x : ℝ) : ℂ) := by
    calc
      _ = Complex.I * ∑ v : Site L,
          (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = _ := by rw [frequency_sum]; simp only [Complex.ofReal_sub]; ring
  unfold spinCharacter
  rw [← harg, Complex.exp_sum]

private theorem currentTerm_mul_character (β : ℝ) (q : Bond L → ℤ)
    (a x : Site L) (ξ : ℤ) (θ : Angles L) :
    rotatorCurrentFourierTerm (graph L) (rotatorIReal β) q (fun _ => 0) θ *
        spinCharacter L a x ξ θ =
      rotatorCurrentFourierTerm (graph L) (rotatorIReal β) q
        (rotatorTwoPointFrequency a x ξ) θ := by
  have hprod :
      (∏ v : Site L, Complex.exp (Complex.I *
        ((-currentDivergence (graph L) q v : ℤ) : ℂ) * (θ v : ℂ))) *
        (∏ v : Site L, Complex.exp (Complex.I *
          (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ))) =
      ∏ v : Site L, Complex.exp (Complex.I *
        ((-currentDivergence (graph L) q v + rotatorTwoPointFrequency a x ξ v : ℤ) : ℂ) *
          (θ v : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [rotatorCurrentFourierTerm, add_zero]
  rw [spinCharacter_vertexProduct]
  calc
    ((rotatorCurrentWeight (rotatorIReal β) q : ℂ) *
        ∏ v : Site L, Complex.exp (Complex.I *
          ((-currentDivergence (graph L) q v : ℤ) : ℂ) * (θ v : ℂ))) *
        ∏ v : Site L, Complex.exp (Complex.I *
          (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ)) =
      (rotatorCurrentWeight (rotatorIReal β) q : ℂ) *
        ((∏ v : Site L, Complex.exp (Complex.I *
          ((-currentDivergence (graph L) q v : ℤ) : ℂ) * (θ v : ℂ))) *
          ∏ v : Site L, Complex.exp (Complex.I *
            (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ))) := by ring
    _ = (rotatorCurrentWeight (rotatorIReal β) q : ℂ) *
        ∏ v : Site L, Complex.exp (Complex.I *
          ((-currentDivergence (graph L) q v + rotatorTwoPointFrequency a x ξ v : ℤ) : ℂ) *
            (θ v : ℂ)) := by
          exact congrArg (fun z : ℂ => (rotatorCurrentWeight (rotatorIReal β) q : ℂ) * z) hprod

/-- The density multiplied by a character has the full current series with the corresponding
vertex-frequency constraint. -/
theorem markedDensity_currentSeries (β : ℝ) (hI : Summable (rotatorI β))
    (a x : Site L) (ξ : ℤ) (θ : Angles L) :
    (spinDensity L β θ : ℂ) * spinCharacter L a x ξ θ =
      ∑' q : Bond L → ℤ,
        rotatorCurrentFourierTerm (graph L) (rotatorIReal β) q
          (rotatorTwoPointFrequency a x ξ) θ := by
  rw [spinDensity_currentSeries (L := L) β hI θ, ← tsum_mul_right]
  apply tsum_congr
  intro q
  exact currentTerm_mul_character β q a x ξ θ

/-- Exact torus marked-current identity. The condition is `div q = δ_a - δ_x`, and the raw angle
normalization is the same `(2π)^{|V_L|}` as for the partition function. -/
theorem markedIntegral_currentIdentity (β : ℝ) (hI : Summable (rotatorI β))
    (a x : Site L) (ξ : ℤ) :
    markedIntegral L β a x ξ =
      (∑' q : Bond L → ℤ,
        if ∀ v, currentDivergence (graph L) q v = rotatorTwoPointFrequency a x ξ v then
          (rotatorCurrentWeight (rotatorIReal β) q : ℂ) else 0) *
        (2 * Real.pi : ℂ) ^ Fintype.card (Site L) := by
  let χ := rotatorTwoPointFrequency a x ξ
  have hweight := currentWeight_summable (L := L) β hI
  have hfreq (q : Bond L → ℤ) :
      (fun v => -currentDivergence (graph L) q v + χ v) = 0 ↔
        ∀ v, currentDivergence (graph L) q v = χ v := by
    constructor
    · intro h v
      have hv := congrFun h v
      change -currentDivergence (graph L) q v + χ v = 0 at hv
      omega
    · intro h
      funext v
      change -currentDivergence (graph L) q v + χ v = 0
      have hv := h v
      omega
  calc
    markedIntegral L β a x ξ =
        ∫ θ : Angles L,
          ∑' q : Bond L → ℤ,
            rotatorCurrentFourierTerm (graph L) (rotatorIReal β) q χ θ ∂
              rotatorRawAngleMeasure (Site L) := by
          unfold markedIntegral
          apply integral_congr_ae
          filter_upwards with θ
          simpa [χ] using markedDensity_currentSeries (L := L) β hI a x ξ θ
    _ = _ := by
          simpa only [χ, hfreq] using rotatorCurrentSeries_integral
            (graph L) (rotatorIReal β) χ hweight

end FroehlichSpencer.BKT.Rotator.Periodic

end
