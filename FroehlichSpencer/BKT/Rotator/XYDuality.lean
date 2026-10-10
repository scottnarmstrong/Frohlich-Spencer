/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.FreeBoxBijection
public import FroehlichSpencer.BKT.Rotator.InternalLaw
public import FroehlichSpencer.BKT.Rotator.CosineFourierSummable
public import FroehlichSpencer.BKT.Villain.CurrentSum
public import FroehlichSpencer.BKT.Villain.Expansion

/-!
# Fourier-current and height identities for the internal XY box

The Fourier coefficient summability and pointwise expansion are explicit hypotheses on the main
identities, so those identities remain usable independently of the separate coefficient proof.
-/

@[expose] public section

open Complex MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator.BesselInterp
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Villain
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- The real representative of the circle-integral Fourier coefficient. -/
def rotatorIReal (b : ℝ) (m : ℤ) : ℝ := besselCoeffRe b m

theorem rotatorI_eq_realCast (b : ℝ) (m : ℤ) :
    rotatorI b m = (rotatorIReal b m : ℂ) := by
  exact rotatorI_eq_ofReal b m

/-- Reindexing the pointwise cosine expansion gives its negative-phase convention. -/
theorem rotatorI_negativePhase_expansion (b t : ℝ)
    (hFourier : ∀ t : ℝ,
      rotatorBondReal b t = ∑' m : ℤ,
        rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))) :
    rotatorBondReal b t = ∑' m : ℤ,
      rotatorI b m * Complex.exp (-Complex.I * (m : ℂ) * (t : ℂ)) := by
  rw [hFourier t]
  calc
    (∑' m : ℤ, rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))) =
        ∑' m : ℤ, rotatorI b (-m) *
          Complex.exp (Complex.I * ((-m : ℤ) : ℂ) * (t : ℂ)) := by
      simpa [Equiv.neg] using ((Equiv.neg ℤ).tsum_eq
        (fun n : ℤ => rotatorI b n * Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)))).symm
    _ = ∑' m : ℤ, rotatorI b m *
          Complex.exp (-Complex.I * (m : ℂ) * (t : ℂ)) := by
      apply tsum_congr
      intro m
      rw [rotatorI_even b m]
      congr 1
      apply congrArg Complex.exp
      simp only [Int.cast_neg]
      ring

/-- The product of negative edge phases is the vertex character with frequency minus divergence.
This is the unpinned-angle version, so no root coordinate is discarded. -/
theorem rotatorCurrentEdgePhase_prod (q : RotatorInternalBond L → ℤ)
    (θ : RotatorAngleConfiguration L) :
    (∏ e : RotatorInternalBond L,
      Complex.exp (-Complex.I * (q e : ℂ) *
        (((θ ((rotatorFreeGraph L).src e) - θ ((rotatorFreeGraph L).tgt e)) : ℝ) : ℂ))) =
      ∏ v : RotatorSpinSite L,
        Complex.exp (Complex.I * (-(rotatorCurrentDivergence q v : ℂ)) *
          (θ v : ℂ)) := by
  classical
  let G := rotatorFreeGraph L
  have hpair := Villain.currentDivergence_pairing G q (fun v => (θ v : ℂ))
  have hsum :
      ∑ e : RotatorInternalBond L,
        -Complex.I * (q e : ℂ) *
          (((θ (G.src e) - θ (G.tgt e)) : ℝ) : ℂ) =
        ∑ v : RotatorSpinSite L,
          Complex.I * (-(rotatorCurrentDivergence q v : ℂ)) * (θ v : ℂ) := by
    calc
      _ = ∑ e : RotatorInternalBond L,
          (-Complex.I) * ((q e : ℂ) *
            ((θ (G.src e) : ℂ) - (θ (G.tgt e) : ℂ))) := by
            apply Finset.sum_congr rfl
            intro e he
            simp only [Complex.ofReal_sub]
            ring
      _ = -Complex.I * ∑ e : RotatorInternalBond L,
          (q e : ℂ) * ((θ (G.src e) : ℂ) - (θ (G.tgt e) : ℂ)) := by
            rw [Finset.mul_sum]
      _ = -Complex.I * ∑ v : RotatorSpinSite L,
          (rotatorCurrentDivergence q v : ℂ) * (θ v : ℂ) := by
            rw [hpair]
            rfl
      _ = ∑ v : RotatorSpinSite L,
          (-Complex.I) * ((rotatorCurrentDivergence q v : ℂ) * (θ v : ℂ)) := by
            rw [Finset.mul_sum]
      _ = ∑ v : RotatorSpinSite L,
          Complex.I * (-(rotatorCurrentDivergence q v : ℂ)) * (θ v : ℂ) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
  calc
    _ = Complex.exp (∑ e : RotatorInternalBond L,
        -Complex.I * (q e : ℂ) *
          (((θ (G.src e) - θ (G.tgt e)) : ℝ) : ℂ)) := by
        rw [← Complex.exp_sum]
    _ = Complex.exp (∑ v : RotatorSpinSite L,
        Complex.I * (-(rotatorCurrentDivergence q v : ℂ)) * (θ v : ℂ)) := by
        rw [hsum]
    _ = ∏ v : RotatorSpinSite L,
        Complex.exp (Complex.I * (-(rotatorCurrentDivergence q v : ℂ)) *
          (θ v : ℂ)) := by
        rw [Complex.exp_sum]

private theorem rotatorFourierPhase_norm (m : ℤ) (t : ℝ) :
    ‖Complex.exp (-Complex.I * (m : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (-Complex.I * (m : ℂ) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- Absolute summability of the edge-current coefficients follows from summability of the
one-edge rotator coefficients and finiteness of the free-box bond carrier. -/
theorem rotatorCurrentCoefficient_summable (b : ℝ) (hI : Summable (rotatorI b)) :
    Summable (fun q : RotatorInternalBond L → ℤ =>
      ‖∏ e, rotatorI b (q e)‖) := by
  classical
  exact Villain.summable_norm_prod_currents
    (fun _ m => rotatorI b m) (fun _ => hI.norm)

/-- Absolute summability of the real current weights used by the raw orthogonality theorem. -/
theorem rotatorCurrentWeight_summable (b : ℝ) (hI : Summable (rotatorI b)) :
    Summable (fun q : RotatorInternalBond L → ℤ =>
      |rotatorCurrentWeight (rotatorIReal b) q|) := by
  have hcoeff := rotatorCurrentCoefficient_summable (L := L) b hI
  apply hcoeff.congr
  intro q
  rw [rotatorCurrentWeight]
  rw [show (∏ e : RotatorInternalBond L, rotatorI b (q e)) =
      ((∏ e : RotatorInternalBond L, rotatorIReal b (q e) : ℝ) : ℂ) by
        simp [rotatorI_eq_realCast]]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- The actual internal XY density, cast to `ℂ`, is its absolutely convergent full current series.
The only analytic hypotheses are the summable one-edge coefficients and their pointwise expansion.
-/
theorem rotatorSpinDensity_currentSeries (b : ℝ)
    (hI : Summable (rotatorI b))
    (hFourier : ∀ t : ℝ,
      rotatorBondReal b t = ∑' m : ℤ,
        rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)))
    (θ : RotatorAngleConfiguration L) :
    (rotatorSpinDensity L b θ : ℂ) =
      ∑' q : RotatorInternalBond L → ℤ,
        rotatorCurrentFourierTerm (rotatorFreeGraph L) (rotatorIReal b) q
          (fun _ => 0) θ := by
  classical
  let a (e : RotatorInternalBond L) (m : ℤ) : ℂ :=
    rotatorI b m * Complex.exp (-Complex.I * (m : ℂ) *
      (((θ ((rotatorFreeGraph L).src e) - θ ((rotatorFreeGraph L).tgt e)) : ℝ) : ℂ))
  have ha : ∀ e : RotatorInternalBond L, Summable (fun m : ℤ => ‖a e m‖) := by
    intro e
    have h := hI.norm
    apply h.congr
    intro m
    simp only [a, Complex.norm_mul, rotatorFourierPhase_norm, mul_one]
  have hprod := Villain.tsum_prod_currents a ha
  calc
    (rotatorSpinDensity L b θ : ℂ) =
        ∏ e : RotatorInternalBond L,
          rotatorBondReal b
            (θ ((rotatorFreeGraph L).src e) - θ ((rotatorFreeGraph L).tgt e)) := by
        unfold rotatorSpinDensity rotatorBondDensity rotatorBondReal
        simp [Complex.ofReal_prod, Complex.ofReal_exp]
    _ = ∏ e : RotatorInternalBond L, ∑' m : ℤ, a e m := by
        apply Finset.prod_congr rfl
        intro e he
        exact rotatorI_negativePhase_expansion b
          (θ ((rotatorFreeGraph L).src e) - θ ((rotatorFreeGraph L).tgt e)) hFourier
    _ = ∑' q : RotatorInternalBond L → ℤ, ∏ e, a e (q e) := hprod
    _ = ∑' q : RotatorInternalBond L → ℤ,
          rotatorCurrentFourierTerm (rotatorFreeGraph L) (rotatorIReal b) q
            (fun _ => 0) θ := by
        apply tsum_congr
        intro q
        rw [rotatorCurrentFourierTerm]
        have hcoeff :
            ∏ e : RotatorInternalBond L, rotatorI b (q e) =
              (rotatorCurrentWeight (rotatorIReal b) q : ℂ) := by
          simp [rotatorCurrentWeight, rotatorI_eq_realCast]
        rw [show (∏ e : RotatorInternalBond L, a e (q e)) =
            (∏ e : RotatorInternalBond L, rotatorI b (q e)) *
              ∏ e : RotatorInternalBond L,
                Complex.exp (-Complex.I * (q e : ℂ) *
                  (((θ ((rotatorFreeGraph L).src e) -
                    θ ((rotatorFreeGraph L).tgt e)) : ℝ) : ℂ)) by
              simp [a, Finset.prod_mul_distrib]]
        rw [hcoeff, rotatorCurrentEdgePhase_prod]
        simp [rotatorCurrentDivergence]


def rotatorHeightPartitionFactor (L : ℕ) (b : ℝ) : ℂ :=
  ∑' h : RotatorFaceHeight L,
    ∏ e : RotatorInternalBond L,
      rotatorI b (rotatorFaceHeightCurrent h e)

/-- The height partition factor equals the neutral-current coefficient sum. -/
theorem rotatorNeutralCurrent_tsum_eq_heightPartition (b : ℝ) :
    (∑' q : RotatorNeutralCurrent L,
      (rotatorCurrentWeight (rotatorIReal b) q.1 : ℂ)) =
      rotatorHeightPartitionFactor L b := by
  let e : RotatorFaceHeight L ≃ RotatorNeutralCurrent L :=
    (rotatorNeutralCurrentHeightEquiv L).symm
  calc
    (∑' q : RotatorNeutralCurrent L,
        (rotatorCurrentWeight (rotatorIReal b) q.1 : ℂ)) =
        ∑' h : RotatorFaceHeight L,
          (rotatorCurrentWeight (rotatorIReal b) (e h).1 : ℂ) :=
      (Equiv.tsum_eq e
        (fun q : RotatorNeutralCurrent L =>
          (rotatorCurrentWeight (rotatorIReal b) q.1 : ℂ))).symm
    _ = rotatorHeightPartitionFactor L b := by
      apply tsum_congr
      intro h
      have eh : (e h).1 = rotatorFaceHeightCurrent h := by rfl
      rw [rotatorCurrentWeight]
      rw [eh]
      simp [rotatorI_eq_realCast]

/-- The all-current neutral filter is the subtype sum over admissible currents. -/
theorem rotatorNeutralFilter_tsum_eq_subtype (b : ℝ) :
    (∑' q : RotatorInternalBond L → ℤ,
      if ∀ v, rotatorCurrentDivergence q v = 0 then
        (rotatorCurrentWeight (rotatorIReal b) q : ℂ) else 0) =
      ∑' q : RotatorNeutralCurrent L,
        (rotatorCurrentWeight (rotatorIReal b) q.1 : ℂ) := by
  classical
  let P : (RotatorInternalBond L → ℤ) → Prop :=
    fun q => ∀ v, rotatorCurrentDivergence q v = 0
  let f : (RotatorInternalBond L → ℤ) → ℂ :=
    fun q => (rotatorCurrentWeight (rotatorIReal b) q : ℂ)
  have hsub :
      (∑' q : {q : RotatorInternalBond L → ℤ // P q}, f q.1) =
        ∑' q : RotatorInternalBond L → ℤ, {q | P q}.indicator f q :=
    tsum_subtype {q | P q} f
  calc
    (∑' q : RotatorInternalBond L → ℤ,
        if ∀ v, rotatorCurrentDivergence q v = 0 then
          (rotatorCurrentWeight (rotatorIReal b) q : ℂ) else 0) =
        ∑' q : RotatorInternalBond L → ℤ, {q | P q}.indicator f q := by
          apply tsum_congr
          intro q
          simp [P, f, Set.indicator]
    _ = ∑' q : {q : RotatorInternalBond L → ℤ // P q}, f q.1 := hsub.symm

/-- The partition integral has the exact raw factor (2π)^|V| times the pinned-height partition
factor. The hypotheses show the one-edge Fourier input explicitly. -/
theorem rotatorPartitionIntegralInternal_eq_heightFactor (b : ℝ)
    (hI : Summable (rotatorI b))
    (hFourier : ∀ t : ℝ,
      rotatorBondReal b t = ∑' m : ℤ,
        rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))) :
    (rotatorPartitionIntegralInternal L b : ℂ) =
      (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) *
        rotatorHeightPartitionFactor L b := by
  let μ := rotatorRawAngleMeasure (RotatorSpinSite L)
  have hweight := rotatorCurrentWeight_summable (L := L) b hI
  have hseries (θ : RotatorAngleConfiguration L) :=
    rotatorSpinDensity_currentSeries b hI hFourier θ
  calc
    (rotatorPartitionIntegralInternal L b : ℂ) =
        ∫ θ : RotatorAngleConfiguration L, (rotatorSpinDensity L b θ : ℂ) ∂μ := by
          exact (integral_ofReal (f := rotatorSpinDensity L b)
            (μ := rotatorRawAngleMeasure (RotatorSpinSite L))).symm
    _ = ∫ θ : RotatorAngleConfiguration L,
          ∑' q : RotatorInternalBond L → ℤ,
            rotatorCurrentFourierTerm (rotatorFreeGraph L) (rotatorIReal b) q
              (fun _ => 0) θ ∂μ := by
          apply integral_congr_ae
          filter_upwards with θ
          exact hseries θ
    _ = (∑' q : RotatorInternalBond L → ℤ,
          if ∀ v, rotatorCurrentDivergence q v = 0 then
            (rotatorCurrentWeight (rotatorIReal b) q : ℂ) else 0) *
          (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) := by
          simpa [μ, rotatorFreeGraph, rotatorCurrentDivergence] using
            rotatorPartitionCurrentSeries_integral (rotatorFreeGraph L)
              (rotatorIReal b) hweight
    _ = (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) *
          rotatorHeightPartitionFactor L b := by
          rw [rotatorNeutralFilter_tsum_eq_subtype (L := L) b,
            rotatorNeutralCurrent_tsum_eq_heightPartition (L := L) b]
          ring

/-- The complex height partition factor is real. -/
theorem rotatorHeightPartitionFactor_im_zero (b : ℝ)
    (hI : Summable (rotatorI b))
    (hFourier : ∀ t : ℝ,
      rotatorBondReal b t = ∑' m : ℤ,
        rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))) :
    (rotatorHeightPartitionFactor L b).im = 0 := by
  have hid := rotatorPartitionIntegralInternal_eq_heightFactor (L := L) b hI hFourier
  have hfactorC : (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) =
      (↑((2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L)) : ℂ) := by
    have hb : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [hb, ← Complex.ofReal_pow]
  have hfactor : 0 < (2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L) := by positivity
  have hid' : (rotatorPartitionIntegralInternal L b : ℂ) =
      (↑((2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L)) : ℂ) *
        rotatorHeightPartitionFactor L b := by
    rw [hfactorC] at hid
    exact hid
  have him' := congrArg Complex.im hid'
  have hmul :
      (2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L) *
        (rotatorHeightPartitionFactor L b).im = 0 := by
    have hprod := him'.symm
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hprod
    rw [Complex.ofReal_im] at hprod
    simpa only [zero_mul, add_zero] using hprod
  rcases mul_eq_zero.mp hmul with hzero | himzero
  · exact (ne_of_gt hfactor hzero).elim
  · exact himzero

/-- Strict positivity of the pinned-height partition factor, inherited from the positive internal
XY partition integral and its exact raw normalization. -/
theorem rotatorHeightPartitionFactor_re_pos (b : ℝ)
    (hI : Summable (rotatorI b))
    (hFourier : ∀ t : ℝ,
      rotatorBondReal b t = ∑' m : ℤ,
        rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))) :
    0 < (rotatorHeightPartitionFactor L b).re := by
  have hid := rotatorPartitionIntegralInternal_eq_heightFactor (L := L) b hI hFourier
  have hraw := rotatorPartitionIntegralInternal_pos L b
  have hfactor : 0 < (2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L) := by positivity
  have hfactorC : (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) =
      (↑((2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L)) : ℂ) := by
    have hb : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [hb, ← Complex.ofReal_pow]
  have hid' : (rotatorPartitionIntegralInternal L b : ℂ) =
      (↑((2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L)) : ℂ) *
        rotatorHeightPartitionFactor L b := by
    rw [hfactorC] at hid
    exact hid
  have hre := congrArg Complex.re hid'
  have himzero := rotatorHeightPartitionFactor_im_zero (L := L) b hI hFourier
  rw [Complex.ofReal_re] at hre
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hre
  simp only [zero_mul, sub_zero, himzero] at hre
  have hreal :
      rotatorPartitionIntegralInternal L b =
        (2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L) *
          (rotatorHeightPartitionFactor L b).re := by
    exact hre
  rw [hreal] at hraw
  nlinarith

/-- The pinned-height partition factor with a fixed source current inserted. -/
def rotatorHeightMarkedFactor (L : ℕ) (b : ℝ)
    (j : RotatorInternalBond L → ℤ) : ℂ :=
  ∑' h : RotatorFaceHeight L,
    ∏ e : RotatorInternalBond L,
      rotatorI b (rotatorFaceHeightCurrent h e + j e)

private theorem rotatorTwoPointFrequency_sum (a x : RotatorSpinSite L) (ξ : ℤ)
    (θ : RotatorAngleConfiguration L) :
    ∑ v : RotatorSpinSite L,
        (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ) =
      (ξ : ℂ) * (θ a : ℂ) - (ξ : ℂ) * (θ x : ℂ) := by
  classical
  unfold rotatorTwoPointFrequency
  simp only [Int.cast_add]
  calc
    _ = ∑ v : RotatorSpinSite L,
        (↑(if v = a then ξ else 0) * (θ v : ℂ) +
          ↑(if v = x then -ξ else 0) * (θ v : ℂ)) := by
          apply Finset.sum_congr rfl
          intro v hv
          ring
    _ = (ξ : ℂ) * (θ a : ℂ) + (-ξ : ℂ) * (θ x : ℂ) := by
          rw [Finset.sum_add_distrib]
          simp
    _ = (ξ : ℂ) * (θ a : ℂ) - (ξ : ℂ) * (θ x : ℂ) := by ring

/-- The inserted spin character is the vertex-frequency product used by current orthogonality. -/
private theorem rotatorSpinCharacter_vertexProduct (a x : RotatorSpinSite L) (ξ : ℤ)
    (θ : RotatorAngleConfiguration L) :
    rotatorSpinCharacter L a x ξ θ =
      ∏ v : RotatorSpinSite L,
        Complex.exp (Complex.I * (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ)) := by
  have harg :
      ∑ v : RotatorSpinSite L,
        Complex.I * (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ) =
      Complex.I * (ξ : ℂ) * ((θ a - θ x : ℝ) : ℂ) := by
    calc
      _ = ∑ v : RotatorSpinSite L,
          Complex.I * ((rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ)) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = Complex.I * ∑ v : RotatorSpinSite L,
          (rotatorTwoPointFrequency a x ξ v : ℂ) * (θ v : ℂ) := by
            rw [← Finset.mul_sum]
      _ = Complex.I * ((ξ : ℂ) * (θ a : ℂ) - (ξ : ℂ) * (θ x : ℂ)) := by
            rw [rotatorTwoPointFrequency_sum]
      _ = Complex.I * (ξ : ℂ) * ((θ a - θ x : ℝ) : ℂ) := by
            simp only [Complex.ofReal_sub]
            ring
  unfold rotatorSpinCharacter
  rw [← harg, Complex.exp_sum]

/-- Adding the vertex frequency of the spin character shifts each current phase term. -/
private theorem rotatorCurrentFourierTerm_mul_spinCharacter (b : ℝ)
    (q : RotatorInternalBond L → ℤ) (a x : RotatorSpinSite L) (ξ : ℤ)
    (θ : RotatorAngleConfiguration L) :
    rotatorCurrentFourierTerm (rotatorFreeGraph L) (rotatorIReal b) q
        (fun _ => 0) θ * rotatorSpinCharacter L a x ξ θ =
      rotatorCurrentFourierTerm (rotatorFreeGraph L) (rotatorIReal b) q
        (rotatorTwoPointFrequency a x ξ) θ := by
  have hprod :
      (∏ v : RotatorSpinSite L,
        Complex.exp (Complex.I * ((-rotatorCurrentDivergence q v : ℤ) : ℂ) *
          (θ v : ℂ))) *
        (∏ v : RotatorSpinSite L,
          Complex.exp (Complex.I * (rotatorTwoPointFrequency a x ξ v : ℂ) *
            (θ v : ℂ))) =
      ∏ v : RotatorSpinSite L,
        Complex.exp (Complex.I *
          ((-rotatorCurrentDivergence q v + rotatorTwoPointFrequency a x ξ v : ℤ) : ℂ) *
          (θ v : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [rotatorCurrentFourierTerm, add_zero]
  rw [rotatorSpinCharacter_vertexProduct]
  have hprod' :
      (∏ v : RotatorSpinSite L,
        Complex.exp (Complex.I *
          ((-currentDivergence (rotatorFreeGraph L) q v : ℤ) : ℂ) * (θ v : ℂ))) *
        (∏ v : RotatorSpinSite L,
          Complex.exp (Complex.I * (rotatorTwoPointFrequency a x ξ v : ℂ) *
            (θ v : ℂ))) =
      ∏ v : RotatorSpinSite L,
        Complex.exp (Complex.I *
          ((-currentDivergence (rotatorFreeGraph L) q v +
            rotatorTwoPointFrequency a x ξ v : ℤ) : ℂ) * (θ v : ℂ)) := by
    simpa [rotatorCurrentDivergence] using hprod
  calc
    ((rotatorCurrentWeight (rotatorIReal b) q : ℂ) *
        ∏ v : RotatorSpinSite L,
          Complex.exp (Complex.I *
            ((-currentDivergence (rotatorFreeGraph L) q v : ℤ) : ℂ) *
            (θ v : ℂ))) *
        ∏ v : RotatorSpinSite L,
          Complex.exp (Complex.I * (rotatorTwoPointFrequency a x ξ v : ℂ) *
            (θ v : ℂ)) =
      (rotatorCurrentWeight (rotatorIReal b) q : ℂ) *
        ((∏ v : RotatorSpinSite L,
          Complex.exp (Complex.I *
            ((-currentDivergence (rotatorFreeGraph L) q v : ℤ) : ℂ) *
            (θ v : ℂ))) *
          ∏ v : RotatorSpinSite L,
            Complex.exp (Complex.I * (rotatorTwoPointFrequency a x ξ v : ℂ) *
              (θ v : ℂ))) := by ring
    _ = (rotatorCurrentWeight (rotatorIReal b) q : ℂ) *
          ∏ v : RotatorSpinSite L,
            Complex.exp (Complex.I *
              ((-currentDivergence (rotatorFreeGraph L) q v +
                rotatorTwoPointFrequency a x ξ v : ℤ) : ℂ) * (θ v : ℂ)) := by
          exact congrArg (fun z : ℂ => (rotatorCurrentWeight (rotatorIReal b) q : ℂ) * z)
            hprod'

/-- The density times its marked spin character has the absolutely convergent source-current
series. -/
theorem rotatorSpinDensity_mulCharacter_currentSeries (b : ℝ)
    (hI : Summable (rotatorI b))
    (hFourier : ∀ t : ℝ,
      rotatorBondReal b t = ∑' m : ℤ,
        rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)))
    (a x : RotatorSpinSite L) (ξ : ℤ) (θ : RotatorAngleConfiguration L) :
    (rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ =
      ∑' q : RotatorInternalBond L → ℤ,
        rotatorCurrentFourierTerm (rotatorFreeGraph L) (rotatorIReal b) q
          (rotatorTwoPointFrequency a x ξ) θ := by
  rw [rotatorSpinDensity_currentSeries b hI hFourier θ]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro q
  exact rotatorCurrentFourierTerm_mul_spinCharacter b q a x ξ θ

/-- Reindexing source currents by the path shift and then by the planar height bijection gives
the marked pinned-height factor. -/
theorem rotatorSourceCurrentFactor_eq_heightMarked (b : ℝ)
    (χ : RotatorSpinSite L → ℤ) (j : RotatorInternalBond L → ℤ)
    (hj : ∀ v, rotatorCurrentDivergence j v = χ v) :
    (∑' q : RotatorInternalBond L → ℤ,
      if ∀ v, rotatorCurrentDivergence q v = χ v then
        (rotatorCurrentWeight (rotatorIReal b) q : ℂ) else 0) =
      rotatorHeightMarkedFactor L b j := by
  classical
  let P : (RotatorInternalBond L → ℤ) → Prop :=
    fun q => ∀ v, rotatorCurrentDivergence q v = χ v
  let f : (RotatorInternalBond L → ℤ) → ℂ :=
    fun q => (rotatorCurrentWeight (rotatorIReal b) q : ℂ)
  let e : RotatorFaceHeight L ≃ {q : RotatorInternalBond L → ℤ // P q} :=
    (rotatorNeutralCurrentHeightEquiv L).symm.trans
      (rotatorCurrentShiftEquiv (rotatorFreeGraph L) χ j (by
        simpa [rotatorCurrentDivergence] using hj))
  have hsub :
      (∑' q : {q : RotatorInternalBond L → ℤ // P q}, f q.1) =
        ∑' q : RotatorInternalBond L → ℤ, {q | P q}.indicator f q :=
    tsum_subtype {q | P q} f
  calc
    (∑' q : RotatorInternalBond L → ℤ,
      if ∀ v, rotatorCurrentDivergence q v = χ v then
        (rotatorCurrentWeight (rotatorIReal b) q : ℂ) else 0) =
        ∑' q : RotatorInternalBond L → ℤ, {q | P q}.indicator f q := by
          apply tsum_congr
          intro q
          simp [P, f, Set.indicator]
    _ = ∑' q : {q : RotatorInternalBond L → ℤ // P q}, f q.1 := hsub.symm
    _ = ∑' h : RotatorFaceHeight L, f (e h).1 :=
          (Equiv.tsum_eq e (fun q : {q : RotatorInternalBond L → ℤ // P q} => f q.1)).symm
    _ = rotatorHeightMarkedFactor L b j := by
          apply tsum_congr
          intro h
          have eh : (e h).1 = fun edge => rotatorFaceHeightCurrent h edge + j edge := by
            rfl
          dsimp only [f]
          rw [rotatorCurrentWeight, eh]
          simp [rotatorI_eq_realCast]

/-- The raw marked integral selects source currents and equals the same `(2π)^|V|` factor times
the shifted pinned-height series. -/
theorem rotatorMarkedDensityIntegral_eq_heightMarkedFactor (b : ℝ)
    (hI : Summable (rotatorI b))
    (hFourier : ∀ t : ℝ,
      rotatorBondReal b t = ∑' m : ℤ,
        rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)))
    (a x : RotatorSpinSite L) (ξ : ℤ) (j : RotatorInternalBond L → ℤ)
    (hj : ∀ v, rotatorCurrentDivergence j v = rotatorTwoPointFrequency a x ξ v) :
    (∫ θ : RotatorAngleConfiguration L,
      (rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ
        ∂rotatorRawAngleMeasure (RotatorSpinSite L)) =
      (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) *
        rotatorHeightMarkedFactor L b j := by
  classical
  let χ := rotatorTwoPointFrequency a x ξ
  have hweight := rotatorCurrentWeight_summable (L := L) b hI
  have hfreq (q : RotatorInternalBond L → ℤ) :
      (fun v => -currentDivergence (rotatorFreeGraph L) q v + χ v) = 0 ↔
        ∀ v, rotatorCurrentDivergence q v = χ v := by
    constructor
    · intro h v
      have hvRaw := congrFun h v
      change -rotatorCurrentDivergence q v + χ v = 0 at hvRaw
      have hv : -rotatorCurrentDivergence q v + χ v = 0 := hvRaw
      omega
    · intro h
      funext v
      change -rotatorCurrentDivergence q v + χ v = 0
      have hv := h v
      omega
  calc
    (∫ θ : RotatorAngleConfiguration L,
      (rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ
        ∂rotatorRawAngleMeasure (RotatorSpinSite L)) =
        ∫ θ : RotatorAngleConfiguration L,
          ∑' q : RotatorInternalBond L → ℤ,
            rotatorCurrentFourierTerm (rotatorFreeGraph L) (rotatorIReal b) q χ θ
          ∂rotatorRawAngleMeasure (RotatorSpinSite L) := by
            apply integral_congr_ae
            filter_upwards with θ
            exact rotatorSpinDensity_mulCharacter_currentSeries b hI hFourier a x ξ θ
    _ = (∑' q : RotatorInternalBond L → ℤ,
          if ∀ v, rotatorCurrentDivergence q v = χ v then
            (rotatorCurrentWeight (rotatorIReal b) q : ℂ) else 0) *
          (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) := by
            simpa only [χ, hfreq] using
              rotatorCurrentSeries_integral (rotatorFreeGraph L) (rotatorIReal b)
                (rotatorTwoPointFrequency a x ξ) hweight
    _ = (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) *
          rotatorHeightMarkedFactor L b j := by
            rw [rotatorSourceCurrentFactor_eq_heightMarked (L := L) b χ j
              (by simpa [χ] using hj)]
            ring

/-- The directed straight source path along row one, with `+ξ` on its rightward bonds. -/
def rotatorStraightSourceCurrent (n : ℕ) (ξ : ℤ) :
    RotatorInternalBond L → ℤ
  | .inl e => if e.2.val = 1 ∧ e.1.1.val < n then ξ else 0
  | .inr _ => 0

/-- The row-one source path has divergence `+ξ` at its left endpoint and `-ξ` at its right
endpoint, in the source orientation of the free-box graph. -/
theorem rotatorStraightSourceCurrent_divergence (n : ℕ) (ξ : ℤ)
    (hn : 2 ≤ n) (hnL : n ≤ L) (v : RotatorSpinSite L) :
    rotatorCurrentDivergence (rotatorStraightSourceCurrent (L := L) n ξ) v =
      rotatorTwoPointFrequency
        ((⟨0, by omega⟩ : Fin (L + 1)), (⟨1, by omega⟩ : Fin (L + 1)))
        ((⟨n, by omega⟩ : Fin (L + 1)), (⟨1, by omega⟩ : Fin (L + 1))) ξ v := by
  rcases v with ⟨x, y⟩
  let a : RotatorSpinSite L :=
    ((⟨0, by omega⟩ : Fin (L + 1)), (⟨1, by omega⟩ : Fin (L + 1)))
  let z : RotatorSpinSite L :=
    ((⟨n, by omega⟩ : Fin (L + 1)), (⟨1, by omega⟩ : Fin (L + 1)))
  have hstart : (x, y) = a ↔ x.val = 0 ∧ y.val = 1 := by
    constructor
    · intro h
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      exact ⟨congrArg Fin.val hx, congrArg Fin.val hy⟩
    · rintro ⟨hx, hy⟩
      apply Prod.ext
      · apply Fin.ext
        exact hx
      · apply Fin.ext
        exact hy
  have hend : (x, y) = z ↔ x.val = n ∧ y.val = 1 := by
    constructor
    · intro h
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      exact ⟨congrArg Fin.val hx, congrArg Fin.val hy⟩
    · rintro ⟨hx, hy⟩
      apply Prod.ext
      · apply Fin.ext
        exact hx
      · apply Fin.ext
        exact hy
  have hfreq : rotatorTwoPointFrequency a z ξ (x, y) =
      (if x.val = 0 ∧ y.val = 1 then ξ else 0) +
        if x.val = n ∧ y.val = 1 then -ξ else 0 := by
    simp only [rotatorTwoPointFrequency, a, z, hstart, hend]
  have hH (i : Fin L) (k : Fin (L + 1)) :
      rotatorHorizontalCurrent (rotatorStraightSourceCurrent (L := L) n ξ) i k =
        if k.val = 1 ∧ i.val < n then ξ else 0 := by
    simp [rotatorHorizontalCurrent, rotatorStraightSourceCurrent,
      horizontalDualEdgeData]
    rfl
  have hV (i : Fin (L + 1)) (k : Fin L) :
      rotatorVerticalCurrent (rotatorStraightSourceCurrent (L := L) n ξ) i k = 0 := by
    simp [rotatorVerticalCurrent, rotatorStraightSourceCurrent]
  simp_rw [rotatorCurrentDivergence_formula, hH, hV]
  rw [hfreq]
  by_cases hy : y.val = 1
  · by_cases hx0 : x.val = 0
    · have h0L : x.val < L := by omega
      have hnpos : 0 < n := by omega
      have hLpos : 0 < L := by omega
      simp [hx0, hy, hnpos, hLpos]
      omega
    · by_cases hxn : x.val = n
      · have hnpos : 0 < n := by omega
        simp [hxn, hy, hnpos]
        omega
      · by_cases hxL : x.val = L
        · have hprev : ¬ x.val - 1 < n := by omega
          have hnpos : 0 < n := by omega
          have hLpos : 0 < L := by omega
          have hprevL : ¬ L - 1 < n := by simpa [hxL] using hprev
          have hLn : L ≠ n := by omega
          simp [hy, hxL, hprevL, hLpos, hLn]
          omega
        · have hxlo : 0 < x.val := by omega
          have hxhi : x.val < L := by have hxlt := x.isLt; omega
          rcases lt_or_gt_of_ne hxn with hlt | hgt
          · have hprev : x.val - 1 < n := by omega
            simp [hx0, hxn, hy, hxlo, hxhi, hlt, hprev]
          · have hout : ¬ x.val < n := by omega
            have hprev : ¬ x.val - 1 < n := by omega
            simp [hx0, hxn, hy, hxlo, hxhi, hout, hprev]
  · simp [hy]

/-- The normalized marked two-point function under the actual free-box internal rotator law is the
ratio of the shifted pinned-height factor to the unmarked one. -/
theorem rotatorMeasureInternal_character_integral_eq_heightRatio (b : ℝ)
    (hI : Summable (rotatorI b))
    (hFourier : ∀ t : ℝ,
      rotatorBondReal b t = ∑' m : ℤ,
        rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)))
    (a x : RotatorSpinSite L) (ξ : ℤ) (j : RotatorInternalBond L → ℤ)
    (hj : ∀ v, rotatorCurrentDivergence j v = rotatorTwoPointFrequency a x ξ v) :
    (∫ θ, rotatorSpinCharacter L a x ξ θ ∂rotatorMeasureInternal L b) =
      rotatorHeightMarkedFactor L b j / rotatorHeightPartitionFactor L b := by
  have hZ := rotatorPartitionIntegralInternal_pos L b
  have hpart := rotatorPartitionIntegralInternal_eq_heightFactor (L := L) b hI hFourier
  have hmarked := rotatorMarkedDensityIntegral_eq_heightMarkedFactor (L := L) b hI hFourier
    a x ξ j hj
  have hfactorR : 0 < (2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L) := by
    positivity
  have hfactorC : (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) =
      (↑((2 * Real.pi : ℝ) ^ Fintype.card (RotatorSpinSite L)) : ℂ) := by
    have hb : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [hb, ← Complex.ofReal_pow]
  have hfactorNe : (2 * Real.pi : ℂ) ^ Fintype.card (RotatorSpinSite L) ≠ 0 := by
    rw [hfactorC]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hfactorR)
  have hheightPos := rotatorHeightPartitionFactor_re_pos (L := L) b hI hFourier
  have hheightNe : rotatorHeightPartitionFactor L b ≠ 0 := by
    intro hzero
    have hre : (rotatorHeightPartitionFactor L b).re = 0 := by rw [hzero]; rfl
    exact (ne_of_gt hheightPos) hre
  have hZc : (rotatorPartitionIntegralInternal L b : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hZ.ne'
  have hscale (θ : RotatorAngleConfiguration L) :
      ((rotatorSpinDensity L b θ / rotatorPartitionIntegralInternal L b : ℝ) : ℂ) *
        rotatorSpinCharacter L a x ξ θ =
      (rotatorPartitionIntegralInternal L b : ℂ)⁻¹ *
        ((rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ) := by
    rw [Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr hZ.ne']
  calc
    (∫ θ, rotatorSpinCharacter L a x ξ θ ∂rotatorMeasureInternal L b) =
        ∫ θ : RotatorAngleConfiguration L,
          ((rotatorSpinDensity L b θ / rotatorPartitionIntegralInternal L b : ℝ) : ℂ) *
            rotatorSpinCharacter L a x ξ θ
          ∂rotatorRawAngleMeasure (RotatorSpinSite L) :=
      rotatorMeasureInternal_character_integral L b a x ξ
    _ = (rotatorPartitionIntegralInternal L b : ℂ)⁻¹ *
          ∫ θ : RotatorAngleConfiguration L,
            (rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ
            ∂rotatorRawAngleMeasure (RotatorSpinSite L) := by
          rw [show (fun θ : RotatorAngleConfiguration L =>
              ((rotatorSpinDensity L b θ / rotatorPartitionIntegralInternal L b : ℝ) : ℂ) *
                rotatorSpinCharacter L a x ξ θ) =
              fun θ => (rotatorPartitionIntegralInternal L b : ℂ)⁻¹ *
                ((rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ) from
                funext hscale]
          rw [integral_const_mul]
    _ = rotatorHeightMarkedFactor L b j /
          rotatorHeightPartitionFactor L b := by
          rw [hmarked, hpart]
          field_simp [hZc, hfactorNe, hheightNe]

/-- Every rightward spin bond of the straight row path carries the positive source current `ξ`. -/
theorem rotatorStraightSourceCurrent_onRow (n : ℕ) (ξ : ℤ)
    (_hn : 2 ≤ n) (_hnL : n ≤ L) (i : Fin L) (hi : i.val < n) :
    rotatorStraightSourceCurrent (L := L) n ξ
      (.inl (horizontalDualEdgeData i ⟨1, by omega⟩)) = ξ := by
  simp [rotatorStraightSourceCurrent, horizontalDualEdgeData, hi]

/-- The row-one marked height edge is exactly the `+ξ` shifted factor of FS81 (1.36), in the
source orientation: the dual endpoints are the upper and lower faces respectively. -/
theorem rotatorStraightMarkedEdgeFactor (n : ℕ) (ξ : ℤ)
    (hn : 2 ≤ n) (hnL : n ≤ L) (i : Fin L) (hi : i.val < n)
    (h : RotatorFaceHeight L) :
    rotatorFaceHeightCurrent h (.inl (horizontalDualEdgeData i ⟨1, by omega⟩)) +
        rotatorStraightSourceCurrent (L := L) n ξ
          (.inl (horizontalDualEdgeData i ⟨1, by omega⟩)) =
    h.1 (some (i, (⟨1, by omega⟩ : Fin L))) -
        h.1 (some (i, (⟨0, by omega⟩ : Fin L))) + ξ := by
  let e : RotatorInternalBond L := .inl (horizontalDualEdgeData i ⟨1, by omega⟩)
  have hrow : 1 < L := by omega
  have hsrc : (rotatorDualGraph L).src e = some (i, (⟨1, by omega⟩ : Fin L)) := by
    simp [e, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, horizontalPrimalSrc,
      horizontalFaceX, horizontalDualEdgeData, hrow]
  have htgt : (rotatorDualGraph L).tgt e = some (i, (⟨0, by omega⟩ : Fin L)) := by
    simp [e, rotatorDualGraph, wiredBoxGraph, wiredBoxTgt, horizontalPrimalTgt,
      horizontalFaceX, horizontalDualEdgeData]
  rw [rotatorFaceHeightCurrent, hsrc, htgt, rotatorStraightSourceCurrent_onRow n ξ hn hnL i hi]

/-- The normalized free-box two-point function for the explicit straight row path equals its
`+ξ` pinned-height series divided by the unmarked pinned-height partition factor. -/
theorem rotatorMeasureInternal_straightTwoPoint_eq_heightRatio (b : ℝ)
    (hI : Summable (rotatorI b))
    (hFourier : ∀ t : ℝ,
      rotatorBondReal b t = ∑' m : ℤ,
        rotatorI b m * Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)))
    (n : ℕ) (ξ : ℤ) (hn : 2 ≤ n) (hnL : n ≤ L) :
    (∫ θ, rotatorSpinCharacter L
      ((⟨0, by omega⟩ : Fin (L + 1)), (⟨1, by omega⟩ : Fin (L + 1)))
      ((⟨n, by omega⟩ : Fin (L + 1)), (⟨1, by omega⟩ : Fin (L + 1))) ξ θ
      ∂rotatorMeasureInternal L b) =
      rotatorHeightMarkedFactor L b (rotatorStraightSourceCurrent (L := L) n ξ) /
        rotatorHeightPartitionFactor L b := by
  exact rotatorMeasureInternal_character_integral_eq_heightRatio (L := L) b hI hFourier
    _ _ ξ (rotatorStraightSourceCurrent (L := L) n ξ)
    (rotatorStraightSourceCurrent_divergence (L := L) n ξ hn hnL)


end FroehlichSpencer.BKT.Rotator
end
