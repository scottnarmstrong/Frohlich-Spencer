/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.FiniteHodge

/-!
# Variational characterization of finite quotient covariance

The source finite Hodge inverse is the attained variational maximum of the
linear source term minus the curl energy.
-/

public section

namespace FroehlichSpencer.FS82.Infinite

open FroehlichSpencer.FS82.Gaussian
open scoped InnerProductSpace

variable {V E P : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]

/-- The source quadratic objective on all finite edge fields. -/
@[expose] noncomputable def finiteVariationalObjective
    (C : ExactOneComplex V E P) (x : coClosed C)
    (φ : EuclideanSpace ℝ E) : ℝ :=
  2 * inner ℝ (x : EuclideanSpace ℝ E) φ - ‖C.d₁ φ‖ ^ 2

/-- The finite quotient covariance is the attained supremum over all edge
fields, not just co-closed fields. Exactness at degree one and the orthogonality
of `x` to `range d₀` remove the exact part of a field. -/
theorem quotientCovarianceQuadratic_isGreatest_variational
    (C : ExactOneComplex V E P) (x : coClosed C) :
    IsGreatest
      {r : ℝ | ∃ φ : EuclideanSpace ℝ E,
        finiteVariationalObjective C x φ = r}
      (quotientCovarianceQuadratic C x) := by
  let u : EuclideanSpace ℝ E := hodgeInverseOnCoClosed C x
  have hu : C.d₁.adjoint (C.d₁ u) = (x : EuclideanSpace ℝ E) := by
    have h := congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C x)
    change formLaplacian C (hodgeInverseOnCoClosed C x : EuclideanSpace ℝ E) =
      (x : EuclideanSpace ℝ E) at h
    simpa [formLaplacian, u, LinearMap.comp_apply] using h
  have hq : quotientCovarianceQuadratic C x = ‖C.d₁ u‖ ^ 2 := by
    rw [quotientCovarianceQuadratic]
    calc
      inner ℝ (x : EuclideanSpace ℝ E)
          (hodgeInverseOnCoClosed C x : EuclideanSpace ℝ E)
          = inner ℝ (C.d₁.adjoint (C.d₁ u)) u := by rw [hu]
      _ = inner ℝ (C.d₁ u) (C.d₁ u) := by
        exact LinearMap.adjoint_inner_left C.d₁ u (C.d₁ u)
      _ = ‖C.d₁ u‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  refine ⟨?_, ?_⟩
  · refine ⟨u, ?_⟩
    dsimp [finiteVariationalObjective]
    rw [hq]
    rw [show inner ℝ (x : EuclideanSpace ℝ E) u = ‖C.d₁ u‖ ^ 2 by
      calc
        inner ℝ (x : EuclideanSpace ℝ E) u =
            inner ℝ (C.d₁.adjoint (C.d₁ u)) u := by rw [hu]
        _ = inner ℝ (C.d₁ u) (C.d₁ u) :=
          LinearMap.adjoint_inner_left C.d₁ u (C.d₁ u)
        _ = ‖C.d₁ u‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]]
    ring
  · rintro r ⟨φ, rfl⟩
    dsimp [finiteVariationalObjective]
    rw [hq]
    have hinner : inner ℝ (x : EuclideanSpace ℝ E) φ =
        inner ℝ (C.d₁ u) (C.d₁ φ) := by
      calc
        inner ℝ (x : EuclideanSpace ℝ E) φ =
            inner ℝ (C.d₁.adjoint (C.d₁ u)) φ := by rw [hu]
        _ = inner ℝ (C.d₁ u) (C.d₁ φ) :=
          LinearMap.adjoint_inner_left C.d₁ φ (C.d₁ u)
    rw [hinner]
    have hnonneg : 0 ≤ ‖C.d₁ u - C.d₁ φ‖ ^ 2 := sq_nonneg _
    nlinarith [norm_sub_sq_real (C.d₁ u) (C.d₁ φ)]

end FroehlichSpencer.FS82.Infinite

end
