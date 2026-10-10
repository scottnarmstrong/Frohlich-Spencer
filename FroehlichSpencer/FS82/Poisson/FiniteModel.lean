module

public import FroehlichSpencer.FS82.Poisson.TiltedPoisson
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open Complex Matrix
open scoped BigOperators

namespace FroehlichSpencer.FS82.Poisson

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dual zero-shift Gaussian weight in chord coordinates. -/
def dualGaussianWeight (A : Matrix ι ι ℝ) (k : ι → ℤ) : ℝ :=
  Real.exp (-Real.pi * ∑ i, ∑ j,
    (k i : ℝ) * A⁻¹ i j * (k j : ℝ))

/-- The zero-shift dual normalizer `Ξ` in the finite chord model. -/
def xi (A : Matrix ι ι ℝ) : ℝ :=
  ∑' k : ι → ℤ, dualGaussianWeight A k

/-- The real tilt as a Fourier parameter in the normalization used by the
finite-dimensional Poisson theorem. -/
def realTiltParameter (τ : ι → ℝ) (t : ℝ) : ι → ℂ :=
  fun i => ((t * τ i / (2 * Real.pi) : ℝ) : ℂ)

/-- The (unnormalized) tested chord-lattice sum. -/
def testedPrimalTerm (A : Matrix ι ι ℝ) (τ : ι → ℝ) (t : ℝ)
    (n : ι → ℤ) : ℂ :=
  cexp (-(Real.pi : ℂ) *
    (∑ i, ∑ j, (n i : ℂ) * (A i j : ℂ) * (n j : ℂ)) +
      t * ∑ i, (τ i : ℂ) * (n i : ℂ))

/-- The source-normalized tested expectation on the gauge-fixed lattice. -/
def testedExpectation (A : Matrix ι ι ℝ) (τ : ι → ℝ) (t : ℝ) : ℂ :=
  (∑' n : ι → ℤ, testedPrimalTerm A τ t n) /
    (∑' n : ι → ℤ, testedPrimalTerm A τ 0 n)

omit [DecidableEq ι] in
private theorem testedPrimalTerm_eq (A : Matrix ι ι ℝ) (τ : ι → ℝ) (t : ℝ)
    (n : ι → ℤ) :
    testedPrimalTerm A τ t n =
      primalQuadraticExp A (realTiltParameter τ t) n := by
  unfold testedPrimalTerm primalQuadraticExp realTiltParameter
  apply congrArg cexp
  congr 1
  calc
    (t : ℂ) * ∑ i, (τ i : ℂ) * (n i : ℂ) =
        ∑ i, (t : ℂ) * ((τ i : ℂ) * (n i : ℂ)) := by rw [Finset.mul_sum]
    _ = ∑ i, (2 * Real.pi : ℂ) *
        (((t * τ i / (2 * Real.pi) : ℝ) : ℂ) * (n i : ℂ)) := by
      apply Fintype.sum_congr
      intro i
      push_cast
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp [hpi]
    _ = (2 * Real.pi : ℂ) *
        ∑ i, (((t * τ i / (2 * Real.pi) : ℝ) : ℂ) * (n i : ℂ)) :=
          (Finset.mul_sum ..).symm

theorem dualGaussianWeight_eq (A : Matrix ι ι ℝ) (k : ι → ℤ) :
    dualQuadraticExp A 0 k = (dualGaussianWeight A k : ℂ) := by
  unfold dualQuadraticExp dualGaussianWeight
  have hterm (i j : ι) :
      (0 - I * (k i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) *
          (0 - I * (k j : ℂ)) =
        -(((k i : ℝ) * A⁻¹ i j * (k j : ℝ) : ℝ) : ℂ) := by
    simp only [zero_sub]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hquad :
      (∑ i, ∑ j, (0 - I * (k i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) *
          (0 - I * (k j : ℂ))) =
        -((∑ i, ∑ j, (k i : ℝ) * A⁻¹ i j * (k j : ℝ) : ℝ) : ℂ) := by
    calc
      _ = ∑ i, ∑ j, -(((k i : ℝ) * A⁻¹ i j * (k j : ℝ) : ℝ) : ℂ) := by
        apply Fintype.sum_congr
        intro i
        apply Fintype.sum_congr
        intro j
        exact hterm i j
      _ = _ := by
        simp
  change cexp ((Real.pi : ℂ) *
      ∑ i, ∑ j, (0 - I * (k i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) *
        (0 - I * (k j : ℂ))) =
    ((Real.exp (-Real.pi * ∑ i, ∑ j,
      (k i : ℝ) * A⁻¹ i j * (k j : ℝ)) : ℝ) : ℂ)
  rw [Complex.ofReal_exp]
  apply congrArg cexp
  rw [hquad]
  push_cast
  ring

private theorem summable_dualGaussianWeight (A : Matrix ι ι ℝ)
    (hA : A.PosDef) : Summable (dualGaussianWeight A) := by
  have hdual := summable_dual_quadratic_exp A hA (0 : ι → ℂ)
  refine hdual.norm.congr ?_
  intro k
  calc
    ‖dualQuadraticExp A 0 k‖ = ‖(dualGaussianWeight A k : ℂ)‖ :=
      congrArg norm (dualGaussianWeight_eq A k)
    _ = dualGaussianWeight A k := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (Real.exp_pos _).le

/-- The real dual Gaussian sums to a strictly positive normalizer. -/
theorem xi_pos (A : Matrix ι ι ℝ) (hA : A.PosDef) : 0 < xi A := by
  unfold xi
  exact (summable_dualGaussianWeight A hA).tsum_pos
    (fun k => (Real.exp_pos _).le) (0 : ι → ℤ) (by simp [dualGaussianWeight])

theorem xi_complex_eq (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (xi A : ℂ) = ∑' k : ι → ℤ, dualQuadraticExp A 0 k := by
  have hs := summable_dualGaussianWeight A hA
  have hreal := hs.hasSum
  have hcomplex := (Complex.hasSum_ofReal).mpr hreal
  calc
    (xi A : ℂ) = (∑' k : ι → ℤ, dualGaussianWeight A k : ℝ) := rfl
    _ = ∑' k : ι → ℤ, (dualGaussianWeight A k : ℂ) := hcomplex.tsum_eq.symm
    _ = ∑' k : ι → ℤ, dualQuadraticExp A 0 k :=
      tsum_congr fun k => (dualGaussianWeight_eq A k).symm

/-- The tested Poisson ratio for a positive-definite finite chord matrix.
The chord energy is normalized as `π ⟨n,A n⟩`; taking
`A = K_CC / (2πβ)` gives the source weight
`exp(-⟨n,K_CC n⟩/(2β) + t⟨τ,n⟩)`. -/
theorem tested_poisson_ratio (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (τ : ι → ℝ) (t : ℝ) :
    testedExpectation A τ t =
      (∑' k : ι → ℤ, dualQuadraticExp A (realTiltParameter τ t) k) /
        (xi A : ℂ) := by
  let w := realTiltParameter τ t
  let c : ℂ := ((Real.sqrt A.det : ℝ) : ℂ)⁻¹
  have hc : c ≠ 0 := by
    have hdet : 0 < A.det := hA.det_pos
    have hsqrt : (Real.sqrt A.det : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hdet)
    exact inv_ne_zero hsqrt
  have hnum := tsum_cexp_neg_quadratic_pi A hA w
  have hden := tsum_cexp_neg_quadratic_pi A hA (0 : ι → ℂ)
  have hXi := xi_complex_eq A hA
  have hnum' :
      (∑' n : ι → ℤ, testedPrimalTerm A τ t n) =
        c * ∑' k : ι → ℤ, dualQuadraticExp A w k := by
    calc
      _ = ∑' n : ι → ℤ, primalQuadraticExp A w n :=
        tsum_congr fun n => testedPrimalTerm_eq A τ t n
      _ = _ := by simpa [c, w, primalQuadraticExp, dualQuadraticExp] using hnum
  have hzero : realTiltParameter τ 0 = 0 := by
    funext i
    simp [realTiltParameter]
  have hden' :
      (∑' n : ι → ℤ, testedPrimalTerm A τ 0 n) =
        c * ∑' k : ι → ℤ, dualQuadraticExp A 0 k := by
    calc
      _ = ∑' n : ι → ℤ, primalQuadraticExp A 0 n := by
        refine tsum_congr fun n => ?_
        simpa only [hzero] using testedPrimalTerm_eq A τ 0 n
      _ = _ := by simpa [c, primalQuadraticExp, dualQuadraticExp] using hden
  unfold testedExpectation
  rw [hnum', hden']
  calc
    c * (∑' k : ι → ℤ, dualQuadraticExp A w k) /
        (c * ∑' k : ι → ℤ, dualQuadraticExp A 0 k) =
        (∑' k : ι → ℤ, dualQuadraticExp A w k) /
          (∑' k : ι → ℤ, dualQuadraticExp A 0 k) := by
            field_simp [hc]
    _ = (∑' k : ι → ℤ, dualQuadraticExp A w k) / (xi A : ℂ) := by
      rw [← hXi]

end
end FroehlichSpencer.FS82.Poisson
