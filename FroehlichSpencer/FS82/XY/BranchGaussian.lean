/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.CosineGaussian

/-!
# the renormalized branch identity

`branch_integral_eq_gaussian`: for co-closed integer currents `J i` and gains `g i` such that
`branchCovariance T A J g` is positive semidefinite, the gauge-averaged integral of
`∏ (1 + K_i cos(⟨J_i, φ⟩ + θ_i))` equals the integral of `∏ (1 + K_i e^{−g_i/2} cos(y_i + θ_i))`
against the centred Gaussian with that covariance.

`branchCovariance_posSemidef` reduces the
semidefiniteness to the local lower bound `∑ s_i² g_i ≤ 2π ⟨k_s, A⁻¹ k_s⟩`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.GaugeAverage

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real chord vector of an integer link current. -/
def chordVector (T : RootedTreeGauge V E) (j : E → ℤ) : T.Chord → ℝ := fun c => (j c.1 : ℝ)

/-- The chord bilinear form `⟨x, A⁻¹ y⟩`. -/
noncomputable def chordBilinear (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (x y : T.Chord → ℝ) : ℝ := dotProduct x (A⁻¹.mulVec y)

theorem chordQuadratic_eq_chordBilinear (T : RootedTreeGauge V E)
    (A : Matrix T.Chord T.Chord ℝ) (j : E → ℤ) :
    chordQuadratic T A j = chordBilinear T A (chordVector T j) (chordVector T j) := rfl

theorem chordBilinear_comm (T : RootedTreeGauge V E) {A : Matrix T.Chord T.Chord ℝ}
    (hA : A.PosDef) (x y : T.Chord → ℝ) :
    chordBilinear T A x y = chordBilinear T A y x := by
  unfold chordBilinear
  have hsymm : A⁻¹.transpose = A⁻¹ := by
    have h := hA.inv.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]

omit [Fintype V] [Fintype E] [DecidableEq ι] in
theorem chordVector_signedSum (T : RootedTreeGauge V E) (J : ι → E → ℤ) (σ : ι → Sign) :
    chordVector T (signedSum J σ) = ∑ i, signValue (σ i) • chordVector T (J i) := by
  funext c
  simp [chordVector, signedSum, signValue_eq_signZ, Finset.sum_apply]

omit [DecidableEq ι] in
theorem chordBilinear_sum_sum (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (s : ι → ℝ) (k : ι → T.Chord → ℝ) :
    chordBilinear T A (∑ i, s i • k i) (∑ i, s i • k i) =
      ∑ i, ∑ j, s i * s j * chordBilinear T A (k i) (k j) := by
  unfold chordBilinear
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The covariance of the renormalized angles of a family with gains `g`. -/
noncomputable def branchCovariance (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (J : ι → E → ℤ) (g : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => 2 * Real.pi * chordBilinear T A (chordVector T (J i)) (chordVector T (J j)) -
    if i = j then g i else 0

theorem branchCovariance_quadratic (T : RootedTreeGauge V E) (A : Matrix T.Chord T.Chord ℝ)
    (J : ι → E → ℤ) (g : ι → ℝ) (s : ι → ℝ) :
    dotProduct s ((branchCovariance T A J g).mulVec s) =
      2 * Real.pi * chordBilinear T A (∑ i, s i • chordVector T (J i))
        (∑ i, s i • chordVector T (J i)) - ∑ i, s i ^ 2 * g i := by
  rw [chordBilinear_sum_sum]
  simp only [dotProduct, Matrix.mulVec, branchCovariance, sub_mul, Finset.sum_sub_distrib,
    mul_sub, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- The local lower bound on the chord quadratic form makes the branch covariance positive
semidefinite. -/
theorem branchCovariance_posSemidef (T : RootedTreeGauge V E) {A : Matrix T.Chord T.Chord ℝ}
    (hA : A.PosDef) (J : ι → E → ℤ) (g : ι → ℝ)
    (hg : ∀ s : ι → ℝ, ∑ i, s i ^ 2 * g i ≤
      2 * Real.pi * chordBilinear T A (∑ i, s i • chordVector T (J i))
        (∑ i, s i • chordVector T (J i))) :
    (branchCovariance T A J g).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun s => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, branchCovariance]
    rw [chordBilinear_comm T hA]
    by_cases hij : i = j
    · subst hij
      rfl
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [hij, hji]
  · rw [star_trivial, branchCovariance_quadratic]
    linarith [hg s]

omit [Fintype V] [DecidableEq ι] in
theorem coClosed_signedSum (T : RootedTreeGauge V E) (J : ι → E → ℤ) (σ : ι → Sign)
    (hJ : ∀ i, RootedTreeGauge.CoClosed T (J i)) :
    RootedTreeGauge.CoClosed T (signedSum J σ) := by
  classical
  intro v hv
  have h1 : ∀ (P : E → Prop) [DecidablePred P],
      (∑ e, if P e then signedSum J σ e else 0) =
        ∑ i, signZ (σ i) * ∑ e, if P e then J i e else 0 := by
    intro P _
    simp only [signedSum, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs
    · rfl
    · simp
  unfold RootedTreeGauge.divergence
  rw [h1, h1, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← mul_sub]
  have := hJ i v hv
  unfold RootedTreeGauge.divergence at this
  rw [this, mul_zero]

omit [DecidableEq ι] in
theorem signWeight_renormalized (K θ g : ι → ℝ) (σ : ι → Sign) :
    signWeight (fun i => K i * Real.exp (-(g i / 2))) θ σ =
      signWeight K θ σ *
        Complex.exp (-((∑ i, signValue (σ i) ^ 2 * g i : ℝ) : ℂ) / 2) := by
  unfold signWeight
  rw [Complex.ofReal_sum, ← Finset.sum_neg_distrib, Finset.sum_div, Complex.exp_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize σ i = ε
  fin_cases ε
  · simp [signCoeff, signValue]
  · simp [signCoeff, signValue, neg_div]
    ring
  · simp [signCoeff, signValue, neg_div]
    ring

/-- **The renormalized branch identity.** -/
theorem branch_integral_eq_gaussian (T : RootedTreeGauge V E) {A : Matrix T.Chord T.Chord ℝ}
    (hA : A.PosDef) (K θ g : ι → ℝ) (J : ι → E → ℤ)
    (hJ : ∀ i, RootedTreeGauge.CoClosed T (J i))
    (hR : (branchCovariance T A J g).PosSemidef) :
    ∫ ω, ∏ i, (1 + K i * Real.cos (linkPairing (gaugeField T ω) (J i) + θ i))
        ∂gaugeMeasure T A =
      ∫ y : EuclideanSpace ℝ ι,
        ∏ i, (1 + (K i * Real.exp (-(g i / 2))) * Real.cos (y i + θ i))
          ∂multivariateGaussian 0 (branchCovariance T A J g) := by
  apply Complex.ofReal_injective
  rw [integral_cosineProduct T hA, integral_cosineProduct_gaussian hR]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [characterValue_of_coClosed T A (coClosed_signedSum T J σ hJ), signWeight_renormalized,
    mul_assoc, ← Complex.exp_add]
  congr 2
  have hq : signQuadratic (branchCovariance T A J g) σ =
      2 * Real.pi * chordQuadratic T A (signedSum J σ) -
        ∑ i, signValue (σ i) ^ 2 * g i := by
    unfold signQuadratic
    rw [branchCovariance_quadratic, chordQuadratic_eq_chordBilinear, chordVector_signedSum]
  rw [hq]
  push_cast
  ring

end FroehlichSpencer.FS82.XY.GaugeAverage

end
