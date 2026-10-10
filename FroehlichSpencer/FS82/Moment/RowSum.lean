module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic
public import FroehlichSpencer.FS82.Moment.Coercivity

@[expose] public section

open scoped InnerProductSpace

namespace FroehlichSpencer.FS82.Moment.Coercivity

noncomputable def matrixOperator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap.comp
    (((Matrix.toLin' A).toContinuousLinearMap).comp
      (EuclideanSpace.equiv ι ℝ).toContinuousLinearMap)

theorem matrixOperator_apply_equiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace.equiv ι ℝ (matrixOperator A x) =
      A.mulVec (EuclideanSpace.equiv ι ℝ x) := by
  change EuclideanSpace.equiv ι ℝ
      ((EuclideanSpace.equiv ι ℝ).symm
        (A.mulVec (EuclideanSpace.equiv ι ℝ x))) = _
  exact (EuclideanSpace.equiv ι ℝ).apply_symm_apply _

theorem matrixOperator_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    matrixOperator A x i =
      A.mulVec (EuclideanSpace.equiv ι ℝ x) i := by
  have h := congrFun (matrixOperator_apply_equiv A x) i
  simpa [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using h

theorem matrixOperator_inner_double_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    inner ℝ (matrixOperator A x) y =
      ∑ i, ∑ j, A i j *
        (EuclideanSpace.equiv ι ℝ x) j * (EuclideanSpace.equiv ι ℝ y) i := by
  rw [PiLp.inner_apply]
  simp_rw [matrixOperator_apply, Real.inner_apply,
    Matrix.mulVec_apply_eq_sum, Finset.sum_mul]
  simp [EuclideanSpace.equiv]

/-- A symmetric real matrix defines a self-adjoint operator on the Euclidean
coordinate space. -/
theorem matrixOperator_selfAdjoint_of_symmetric
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hsymm : ∀ i j, A i j = A j i)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (matrixOperator A x) y = inner ℝ x (matrixOperator A y) := by
  calc
    inner ℝ (matrixOperator A x) y =
        ∑ i, ∑ j, A i j * (EuclideanSpace.equiv ι ℝ x) j *
          (EuclideanSpace.equiv ι ℝ y) i := matrixOperator_inner_double_sum A x y
    _ = ∑ i, ∑ j, A i j * (EuclideanSpace.equiv ι ℝ y) j *
          (EuclideanSpace.equiv ι ℝ x) i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsymm]
      ring
    _ = inner ℝ x (matrixOperator A y) := by
      simpa [real_inner_comm] using
        (matrixOperator_inner_double_sum A y x).symm


/--
This constructs the finite-volume Hodge
preimage rather than adding it as an assumption.
-/
theorem exists_preimage_of_coclosed
    {F E : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (d : F →ₗ[ℝ] E) (K : E →ₗ[ℝ] E)
    (hKsym : K.IsSymmetric) (hker : K.ker = d.range)
    (j : E) (hcoclosed : d.adjoint j = 0) :
    ∃ v, K v = j := by
  have hjorth : j ∈ K.kerᗮ := by
    rw [hker, LinearMap.orthogonal_range]
    exact LinearMap.mem_ker.mpr hcoclosed
  have hjrange : j ∈ K.range := by
    rw [LinearMap.orthogonal_ker, hKsym.adjoint_eq] at hjorth
    exact hjorth
  exact LinearMap.mem_range.mp hjrange

/-- Abstract quotient coercivity. With `ker K = range d`, co-closedness
constructs a pseudoinverse representative. A row-sum estimate supplies the
operator norm bound, and the selected-mode mass is bounded by the squared
norm of the physically scaled current. -/
theorem hCoercive_from_kernel_and_row_bound
    {F E : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (d : F →ₗ[ℝ] E) (K : E →ₗ[ℝ] E)
    (hKsym : K.IsSymmetric)
    (hKpos : ∀ x, 0 ≤ inner ℝ x (K x))
    (hker : K.ker = d.range)
    (R beta selected : ℝ) (hR : 0 < R) (hbeta : 0 ≤ beta)
    (hOp : ‖K.toContinuousLinearMap‖ ≤ R)
    (j : E) (hcoclosed : d.adjoint j = 0)
    (hSelected : (2 * Real.pi)^2 * selected ≤ ‖j‖^2) :
    ∃ v, K v = j ∧
      (beta * (2 * Real.pi)^2 / (2 * R)) * selected ≤
        (beta / 2) * inner ℝ j v := by
  obtain ⟨v, hv⟩ := exists_preimage_of_coclosed d K hKsym hker j hcoclosed
  refine ⟨v, hv, ?_⟩
  have hInv := inverse_quadratic_lower_bound K.toContinuousLinearMap
    (fun x y => hKsym x y) hKpos R hR hOp j v (by simpa using hv)
  have hscale := mul_le_mul_of_nonneg_left hSelected (by positivity :
    0 ≤ beta / (2 * R))
  have hinv := mul_le_mul_of_nonneg_left hInv (by positivity : 0 ≤ beta / 2)
  have hratio : (beta / (2 * R)) * (R * inner ℝ j v) =
      (beta / 2) * inner ℝ j v := by
    field_simp [ne_of_gt hR]
  calc
    (beta * (2 * Real.pi)^2 / (2 * R)) * selected =
        (beta / (2 * R)) * ((2 * Real.pi)^2 * selected) := by ring
    _ ≤ (beta / (2 * R)) * ‖j‖^2 := hscale
    _ ≤ (beta / (2 * R)) * (R * inner ℝ j v) := by
      calc
        (beta / (2 * R)) * ‖j‖^2 =
            (beta / 2) * (‖j‖^2 / R) := by
              field_simp [ne_of_gt hR]
        _ ≤ (beta / 2) * inner ℝ j v := hinv
        _ = (beta / (2 * R)) * (R * inner ℝ j v) := hratio.symm
    _ = (beta / 2) * inner ℝ j v := hratio


end FroehlichSpencer.FS82.Moment.Coercivity
