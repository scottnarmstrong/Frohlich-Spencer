/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.AssignmentPattern
public import FroehlichSpencer.FS82.XY.BranchGaussian
public import FroehlichSpencer.FS82.XY.Poisson3

/-!
# the per-assignment moment as a gauge-averaged integral

For a real tilt `w` the dual Poisson summand factors as

`dualQuadraticExp A w k = e^{π⟨w, A⁻¹w⟩} · e^{i⟨s_w, j⟩} · e^{−π⟨k, A⁻¹k⟩}`,

with the real link field `s_w = −2π A⁻¹ w` on the chords.

So the tilt is a translation of the link
field by `s_w`, FS82 (4.33)–(4.35).

Together with the fibre bijection this gives

`gaugeAssignmentMoment T A τ t z q = e^{π⟨w, A⁻¹w⟩} ∫ ∏_e (1 + z cos((φ_e + s_w(e)) (q_e + 1)))`,

the integral being over the gauge-averaged chord Gaussian, FS82 (4.29)–(4.30) for one mode
assignment.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.GaugeAverage

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The real tilt vector of a chord test function. -/
noncomputable def tiltVector (T : RootedTreeGauge V E) (τ : T.Chord → ℝ) (t : ℝ) :
    T.Chord → ℝ := fun c => t * τ c / (2 * Real.pi)

/-- The link translation of a real tilt, in radians. -/
noncomputable def tiltShift (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (w : T.Chord → ℝ) : E → ℝ :=
  T.extendChord fun c => -(2 * Real.pi) * (A⁻¹.mulVec w) c

/-- The Gaussian constant of a real tilt. -/
noncomputable def tiltConstant (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (w : T.Chord → ℝ) : ℝ := Real.exp (Real.pi * chordBilinear T A w w)

theorem tiltConstant_pos (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (w : T.Chord → ℝ) : 0 < tiltConstant T A w := Real.exp_pos _

theorem linkPairing_tiltShift (T : RootedTreeGauge V E) {A : Matrix T.Chord T.Chord ℝ}
    (hA : A.PosDef) (w : T.Chord → ℝ) (j : E → ℤ) :
    linkPairing (tiltShift T A w) j =
      -(2 * Real.pi) * chordBilinear T A w (chordVector T j) := by
  unfold linkPairing tiltShift
  rw [sum_extendChord_mul T _ fun e => (j e : ℝ), chordBilinear_comm T hA]
  unfold chordBilinear chordVector
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dualQuadraticExp_tilt (T : RootedTreeGauge V E) {A : Matrix T.Chord T.Chord ℝ}
    (hA : A.PosDef) (w : T.Chord → ℝ) (j : E → ℤ) :
    dualQuadraticExp A (fun c => (w c : ℂ)) (T.restrictChord j) =
      (tiltConstant T A w : ℂ) *
        (Complex.exp (Complex.I * (linkPairing (tiltShift T A w) j : ℝ)) *
          Complex.exp (-(Real.pi * chordQuadratic T A j : ℝ))) := by
  have hreal := xyDual3DualQuadraticExp_real A w (T.restrictChord j)
  simp only [xyDual3ComplexBilinear_eq_dotProduct] at hreal
  have hk : (fun i : T.Chord => ((T.restrictChord j i : ℤ) : ℝ)) = chordVector T j := rfl
  rw [hk] at hreal
  have hsymm : dotProduct (chordVector T j) (A⁻¹.mulVec w) =
      dotProduct w (A⁻¹.mulVec (chordVector T j)) := chordBilinear_comm T hA (chordVector T j) w
  rw [hsymm] at hreal
  rw [hreal, linkPairing_tiltShift T hA, chordQuadratic_eq_chordBilinear]
  unfold tiltConstant chordBilinear
  rw [Complex.ofReal_exp, mul_assoc]
  congr 1
  · congr 1
    push_cast
    ring
  · rw [mul_comm]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring

/-- The per-assignment moment as a sum over sign patterns. -/
theorem gaugeAssignmentMoment_eq_patternSum (T : RootedTreeGauge V E)
    {A : Matrix T.Chord T.Chord ℝ} (hA : A.PosDef) (τ : T.Chord → ℝ) (t : ℝ)
    (z : ℕ → ℝ) (q : E → ℕ) (hz : ∀ n, 0 < z (positiveMode n)) :
    gaugeAssignmentMoment T A τ t z q =
      ∑ σ : E → Sign, (∏ e, signCoeff (z (positiveMode (q e))) (σ e)) *
        ((tiltConstant T A (tiltVector T τ t) : ℂ) *
          (Complex.exp (Complex.I *
              (linkPairing (tiltShift T A (tiltVector T τ t)) (patternCurrent q σ) : ℝ)) *
            characterValue T A (patternCurrent q σ))) := by
  unfold gaugeAssignmentMoment
  refine gaugeAssignmentFiberSum_eq_patternSum T q z hz
    (fun j => dualQuadraticExp A (realTiltParameter τ t) (T.restrictChord j))
    (fun j => (tiltConstant T A (tiltVector T τ t) : ℂ) *
      (Complex.exp (Complex.I * (linkPairing (tiltShift T A (tiltVector T τ t)) j : ℝ)) *
        characterValue T A j)) ?_ ?_
  · intro j hj
    rw [characterValue_of_coClosed T A hj]
    exact dualQuadraticExp_tilt T hA (tiltVector T τ t) j
  · intro j hj
    rw [characterValue_of_not_coClosed T A hj, mul_zero, mul_zero]

/-- The single-link current of a mode assignment. -/
def assignmentCurrent (q : E → ℕ) (e : E) : E → ℤ := Pi.single e ((q e + 1 : ℕ) : ℤ)

omit [Fintype V] [DecidableEq V] in
theorem linkPairing_assignmentCurrent (φ : E → ℝ) (q : E → ℕ) (e : E) :
    linkPairing φ (assignmentCurrent q e) = φ e * ((q e + 1 : ℕ) : ℝ) := by
  unfold linkPairing assignmentCurrent
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ he'
    simp [he']
  · simp

omit [Fintype V] [DecidableEq V] in
theorem signedSum_assignmentCurrent (q : E → ℕ) (σ : E → Sign) :
    signedSum (assignmentCurrent q) σ = patternCurrent q σ := by
  funext e
  unfold signedSum assignmentCurrent patternCurrent
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ he'
    simp [he'.symm]
  · simp

/-- **The per-assignment moment as a gauge-averaged integral.** -/
theorem gaugeAssignmentMoment_eq_integral (T : RootedTreeGauge V E)
    {A : Matrix T.Chord T.Chord ℝ} (hA : A.PosDef) (τ : T.Chord → ℝ) (t : ℝ)
    (z : ℕ → ℝ) (q : E → ℕ) (hz : ∀ n, 0 < z (positiveMode n)) :
    gaugeAssignmentMoment T A τ t z q =
      (tiltConstant T A (tiltVector T τ t) : ℂ) *
        ((∫ ω, ∏ e, (1 + z (positiveMode (q e)) *
            Real.cos ((gaugeField T ω e + tiltShift T A (tiltVector T τ t) e) *
              ((q e + 1 : ℕ) : ℝ))) ∂gaugeMeasure T A : ℝ) : ℂ) := by
  set s := tiltShift T A (tiltVector T τ t) with hs
  have hint := integral_cosineProduct T hA (fun e => z (positiveMode (q e)))
    (fun e => s e * ((q e + 1 : ℕ) : ℝ)) (assignmentCurrent q)
  have hfun : (fun ω : EuclideanSpace ℝ T.Chord × (V → ℝ) =>
      ∏ e, (1 + z (positiveMode (q e)) *
        Real.cos (linkPairing (gaugeField T ω) (assignmentCurrent q e) +
          s e * ((q e + 1 : ℕ) : ℝ)))) =
      fun ω => ∏ e, (1 + z (positiveMode (q e)) *
        Real.cos ((gaugeField T ω e + s e) * ((q e + 1 : ℕ) : ℝ))) := by
    funext ω
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [linkPairing_assignmentCurrent, add_mul]
  rw [hfun] at hint
  rw [hint, gaugeAssignmentMoment_eq_patternSum T hA τ t z q hz, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [signedSum_assignmentCurrent]
  have hw : signWeight (fun e => z (positiveMode (q e)))
      (fun e => s e * ((q e + 1 : ℕ) : ℝ)) σ =
      (∏ e, signCoeff (z (positiveMode (q e))) (σ e)) *
        Complex.exp (Complex.I * (linkPairing s (patternCurrent q σ) : ℝ)) := by
    unfold signWeight
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum]
    congr 4
    unfold linkPairing patternCurrent
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [signValue_eq_signZ]
    push_cast
    ring
  rw [hw]
  ring

end FroehlichSpencer.FS82.XY.GaugeAverage

end
