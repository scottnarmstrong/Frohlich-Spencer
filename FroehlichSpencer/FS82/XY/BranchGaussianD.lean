/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.GaugeFieldD
public import FroehlichSpencer.FS82.XY.BranchGaussian

/-!
# renormalization of a family of closed currents, without a chart

The chart-free form of `XY/BranchGaussian.lean`.

For closed integer currents `J_i` (for the
integer divergence matrix `D`) and gains `g_i` with

`∑ s_i² g_i ≤ ⟨∑ s_i J_i, S ∑ s_i J_i⟩` for all real `s`,

the matrix `R_ij = ⟨J_i, S J_j⟩ − δ_ij g_i` is positive semidefinite, and the gauge-averaged
integral of `∏ (1 + K_i cos(⟨J_i, φ⟩ + θ_i))` is the `N(0, R)` integral of
`∏ (1 + K_i e^{−g_i/2} cos(y_i + θ_i))`: both are the same sum over sign patterns.

This is the
renormalization of the activities, FS82 (4.30)–(4.33).

* `bilinearD`, `branchCovarianceD`, `branchCovarianceD_posSemidef`.
* `closedD_signedSum`.
* `branch_integral_eq_gaussianD`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.XY.GaugeAverage
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real vector of an integer current, as a function. -/
def realCurrent (j : E → ℤ) : E → ℝ := fun e => (j e : ℝ)

/-- The bilinear form `⟨x, S y⟩`. -/
noncomputable def bilinearD (S : Matrix E E ℝ) (x y : E → ℝ) : ℝ := dotProduct x (S.mulVec y)

omit [DecidableEq E] in
theorem quadraticD_eq_bilinearD (S : Matrix E E ℝ) (j : E → ℤ) :
    quadraticD S j = bilinearD S (realCurrent j) (realCurrent j) := rfl

omit [DecidableEq E] in
theorem bilinearD_comm {S : Matrix E E ℝ} (hS : S.PosSemidef) (x y : E → ℝ) :
    bilinearD S x y = bilinearD S y x := by
  unfold bilinearD
  have hsymm : S.transpose = S := by
    have h := hS.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]

omit [Fintype E] [DecidableEq E] [DecidableEq ι] in
theorem realCurrent_signedSum (J : ι → E → ℤ) (σ : ι → Sign) :
    realCurrent (signedSum J σ) = ∑ i, signValue (σ i) • realCurrent (J i) := by
  funext e
  simp [realCurrent, signedSum, signValue_eq_signZ, Finset.sum_apply]

omit [DecidableEq E] [DecidableEq ι] in
theorem bilinearD_sum_sum (S : Matrix E E ℝ) (s : ι → ℝ) (k : ι → E → ℝ) :
    bilinearD S (∑ i, s i • k i) (∑ i, s i • k i) =
      ∑ i, ∑ j, s i * s j * bilinearD S (k i) (k j) := by
  unfold bilinearD
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The covariance of the renormalized angles of a family with gains `g`. -/
noncomputable def branchCovarianceD (S : Matrix E E ℝ) (J : ι → E → ℤ) (g : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => bilinearD S (realCurrent (J i)) (realCurrent (J j)) - if i = j then g i else 0

omit [DecidableEq E] in
theorem branchCovarianceD_quadratic (S : Matrix E E ℝ) (J : ι → E → ℤ) (g : ι → ℝ)
    (s : ι → ℝ) :
    dotProduct s ((branchCovarianceD S J g).mulVec s) =
      bilinearD S (∑ i, s i • realCurrent (J i)) (∑ i, s i • realCurrent (J i)) -
        ∑ i, s i ^ 2 * g i := by
  rw [bilinearD_sum_sum]
  simp only [dotProduct, Matrix.mulVec, branchCovarianceD, sub_mul, Finset.sum_sub_distrib,
    mul_sub, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring

omit [DecidableEq E] in
/-- The lower bound on the quadratic form makes the branch covariance positive semidefinite. -/
theorem branchCovarianceD_posSemidef {S : Matrix E E ℝ} (hS : S.PosSemidef) (J : ι → E → ℤ)
    (g : ι → ℝ)
    (hg : ∀ s : ι → ℝ, ∑ i, s i ^ 2 * g i ≤
      bilinearD S (∑ i, s i • realCurrent (J i)) (∑ i, s i • realCurrent (J i))) :
    (branchCovarianceD S J g).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun s => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, branchCovarianceD]
    rw [bilinearD_comm hS]
    by_cases hij : i = j
    · subst hij
      rfl
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [hij, hji]
  · rw [star_trivial, branchCovarianceD_quadratic]
    linarith [hg s]

omit [Fintype V] [DecidableEq E] [DecidableEq ι] in
/-- Signed sums of closed currents are closed. -/
theorem closedD_signedSum (D : V → E → ℤ) (J : ι → E → ℤ) (σ : ι → Sign)
    (hJ : ∀ i, ClosedD D (J i)) : ClosedD D (signedSum J σ) := by
  intro v
  have h : divergenceD D (signedSum J σ) v = ∑ i, signZ (σ i) * divergenceD D (J i) v := by
    unfold divergenceD signedSum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => by ring
  rw [h]
  exact Finset.sum_eq_zero fun i _ => by rw [hJ i v, mul_zero]

/-- **The renormalized branch identity.** -/
theorem branch_integral_eq_gaussianD (D : V → E → ℤ) {S : Matrix E E ℝ} (hS : S.PosSemidef)
    (K θ g : ι → ℝ) (J : ι → E → ℤ) (hJ : ∀ i, ClosedD D (J i))
    (hR : (branchCovarianceD S J g).PosSemidef) :
    ∫ ω, ∏ i, (1 + K i * Real.cos (linkPairing (gaugeFieldD D ω) (J i) + θ i))
        ∂gaugeMeasureD V S =
      ∫ y : EuclideanSpace ℝ ι,
        ∏ i, (1 + (K i * Real.exp (-(g i / 2))) * Real.cos (y i + θ i))
          ∂multivariateGaussian 0 (branchCovarianceD S J g) := by
  apply Complex.ofReal_injective
  rw [integral_cosineProductD D hS, integral_cosineProduct_gaussian hR]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [characterValueD_of_closed D S (closedD_signedSum D J σ hJ), signWeight_renormalized,
    mul_assoc, ← Complex.exp_add]
  congr 2
  have hq : signQuadratic (branchCovarianceD S J g) σ =
      quadraticD S (signedSum J σ) - ∑ i, signValue (σ i) ^ 2 * g i := by
    unfold signQuadratic
    rw [branchCovarianceD_quadratic, quadraticD_eq_bilinearD, realCurrent_signedSum]
  rw [hq]
  push_cast
  ring

end FroehlichSpencer.FS82.XY.DualD

end
