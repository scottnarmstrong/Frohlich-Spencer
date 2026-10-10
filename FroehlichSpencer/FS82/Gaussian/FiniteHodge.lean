/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Ring

/-!
# Generic finite Hodge inverse

A finite real cochain complex with exactness at degree one has an invertible
form Laplacian on its co-closed subspace. The source dual complex instantiates
this result in `SourceDualComplex.lean`.
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open scoped InnerProductSpace
structure ExactOneComplex (V E P : Type*)
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P] where
  d₀ : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ E
  d₁ : EuclideanSpace ℝ E →ₗ[ℝ] EuclideanSpace ℝ P
  complex : d₁.comp d₀ = 0
  exactOne : d₁.ker ≤ d₀.range

variable {V E P : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]

/-- The source co-closed subspace: kernel of the adjoint of the vertex
coboundary. -/
@[expose] noncomputable def coClosed (C : ExactOneComplex V E P) : Submodule ℝ (EuclideanSpace ℝ E) :=
  C.d₀.adjoint.ker

/-- The form Laplacian `δd` on edge cochains. -/
@[expose] noncomputable def formLaplacian (C : ExactOneComplex V E P) :
    EuclideanSpace ℝ E →ₗ[ℝ] EuclideanSpace ℝ E :=
  C.d₁.adjoint.comp C.d₁

/-- `δd` preserves the co-closed subspace when `d₁ d₀ = 0`. -/
theorem formLaplacian_mem_coClosed (C : ExactOneComplex V E P)
    (x : EuclideanSpace ℝ E) :
    formLaplacian C x ∈ coClosed C := by
  apply LinearMap.mem_ker.mpr
  have hcomp : C.d₀.adjoint.comp C.d₁.adjoint = 0 := by
    rw [← LinearMap.adjoint_comp, C.complex]
    simp
  change ((C.d₀.adjoint.comp C.d₁.adjoint).comp C.d₁) x = 0
  rw [hcomp]
  simp

/-- The finite source Hodge operator, restricted to co-closed 1-forms. -/
@[expose] noncomputable def hodgeOnCoClosed (C : ExactOneComplex V E P) :
    coClosed C →ₗ[ℝ] coClosed C :=
  ((formLaplacian C).codRestrict (coClosed C)
    (formLaplacian_mem_coClosed C)).comp (coClosed C).subtype

/-- Exactness at degree one removes all harmonic 1-forms: the restricted
form Hodge operator has trivial kernel. -/
theorem hodgeOnCoClosed_injective (C : ExactOneComplex V E P) :
    Function.Injective (hodgeOnCoClosed C) := by
  intro x y hxy
  apply Subtype.ext
  let w : EuclideanSpace ℝ E := (x : EuclideanSpace ℝ E) - y
  have hL : formLaplacian C w = 0 := by
    have hval := congrArg (fun z : coClosed C => (z : EuclideanSpace ℝ E)) hxy
    change formLaplacian C (x : EuclideanSpace ℝ E) =
      formLaplacian C (y : EuclideanSpace ℝ E) at hval
    dsimp [w]
    rw [map_sub, hval, sub_self]
  have hcurl : C.d₁ w = 0 := by
    have hmem : w ∈ (formLaplacian C).ker := LinearMap.mem_ker.mpr hL
    rw [formLaplacian, LinearMap.ker_adjoint_comp_self] at hmem
    exact LinearMap.mem_ker.mp hmem
  have hfill : w ∈ C.d₀.range := C.exactOne (LinearMap.mem_ker.mpr hcurl)
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hfill
  have hx0 : C.d₀.adjoint (x : EuclideanSpace ℝ E) = 0 :=
    LinearMap.mem_ker.mp x.property
  have hy0 : C.d₀.adjoint (y : EuclideanSpace ℝ E) = 0 :=
    LinearMap.mem_ker.mp y.property
  have hw0 : C.d₀.adjoint w = 0 := by
    dsimp [w]
    rw [map_sub, hx0, hy0, sub_self]
  have horth : inner ℝ w w = 0 := by
    calc
      inner ℝ w w = inner ℝ (C.d₀ u) w := by rw [hu]
      _ = inner ℝ u (C.d₀.adjoint w) :=
        (LinearMap.adjoint_inner_right C.d₀ u w).symm
      _ = 0 := by rw [hw0]; simp
  have hwzero : w = 0 := inner_self_eq_zero.mp horth
  dsimp [w] at hwzero
  exact sub_eq_zero.mp hwzero

/-- On any finite exact-one complex, every co-closed source has a unique
co-closed solution of the finite Hodge equation. -/
theorem existsUnique_hodge_solution (C : ExactOneComplex V E P)
    (f : coClosed C) : ∃! x : coClosed C, hodgeOnCoClosed C x = f := by
  have hsurj : Function.Surjective (hodgeOnCoClosed C) :=
    (LinearMap.injective_iff_surjective.mp (hodgeOnCoClosed_injective C))
  obtain ⟨x, hx⟩ := hsurj f
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hodgeOnCoClosed_injective C (hy.trans hx.symm)


@[expose] noncomputable def hodgeInverseOnCoClosed (C : ExactOneComplex V E P) :
    coClosed C →ₗ[ℝ] coClosed C :=
  (LinearEquiv.ofInjectiveEndo (hodgeOnCoClosed C)
    (hodgeOnCoClosed_injective C)).symm.toLinearMap

@[simp] theorem hodgeOnCoClosed_hodgeInverse
    (C : ExactOneComplex V E P) (x : coClosed C) :
    hodgeOnCoClosed C (hodgeInverseOnCoClosed C x) = x := by
  change (LinearEquiv.ofInjectiveEndo (hodgeOnCoClosed C)
      (hodgeOnCoClosed_injective C))
    ((LinearEquiv.ofInjectiveEndo (hodgeOnCoClosed C)
      (hodgeOnCoClosed_injective C)).symm x) = x
  exact (LinearEquiv.ofInjectiveEndo (hodgeOnCoClosed C)
    (hodgeOnCoClosed_injective C)).apply_symm_apply x

/-- The inverse Hodge operator is self-adjoint on co-closed forms. This
statement is generic in the finite exact complex; the source-star orientation
does not enter its proof. -/
theorem hodgeInverseOnCoClosed_symmetric (C : ExactOneComplex V E P)
    (x y : coClosed C) :
    inner ℝ (hodgeInverseOnCoClosed C x : EuclideanSpace ℝ E)
        (y : EuclideanSpace ℝ E) =
      inner ℝ (x : EuclideanSpace ℝ E)
        (hodgeInverseOnCoClosed C y : EuclideanSpace ℝ E) := by
  let H := hodgeOnCoClosed C
  let V := hodgeInverseOnCoClosed C
  have hHsym (u v : coClosed C) :
      inner ℝ (H u : EuclideanSpace ℝ E) (v : EuclideanSpace ℝ E) =
        inner ℝ (u : EuclideanSpace ℝ E) (H v : EuclideanSpace ℝ E) := by
    change inner ℝ (formLaplacian C (u : EuclideanSpace ℝ E))
        (v : EuclideanSpace ℝ E) =
      inner ℝ (u : EuclideanSpace ℝ E)
        (formLaplacian C (v : EuclideanSpace ℝ E))
    calc
      inner ℝ (formLaplacian C (u : EuclideanSpace ℝ E))
          (v : EuclideanSpace ℝ E) =
        inner ℝ (v : EuclideanSpace ℝ E)
          (formLaplacian C (u : EuclideanSpace ℝ E)) := real_inner_comm _ _
      _ = inner ℝ (C.d₁ (v : EuclideanSpace ℝ E))
          (C.d₁ (u : EuclideanSpace ℝ E)) := by
        rw [formLaplacian]
        exact LinearMap.adjoint_inner_right C.d₁
          (v : EuclideanSpace ℝ E) (C.d₁ (u : EuclideanSpace ℝ E))
      _ = inner ℝ (C.d₁ (u : EuclideanSpace ℝ E))
          (C.d₁ (v : EuclideanSpace ℝ E)) := real_inner_comm _ _
      _ = inner ℝ (u : EuclideanSpace ℝ E)
          (formLaplacian C (v : EuclideanSpace ℝ E)) := by
        rw [formLaplacian]
        exact (LinearMap.adjoint_inner_right C.d₁
          (u : EuclideanSpace ℝ E) (C.d₁ (v : EuclideanSpace ℝ E))).symm
  have hVx : H (V x) = x := hodgeOnCoClosed_hodgeInverse C x
  have hVy : H (V y) = y := hodgeOnCoClosed_hodgeInverse C y
  calc
    inner ℝ (V x : EuclideanSpace ℝ E) (y : EuclideanSpace ℝ E) =
        inner ℝ (V x : EuclideanSpace ℝ E) (H (V y) : EuclideanSpace ℝ E) := by
      rw [hVy]
    _ = inner ℝ (H (V x) : EuclideanSpace ℝ E)
        (V y : EuclideanSpace ℝ E) := (hHsym (V x) (V y)).symm
    _ = inner ℝ (x : EuclideanSpace ℝ E)
        (V y : EuclideanSpace ℝ E) := by rw [hVx]

theorem formLaplacian_inner_nonneg (C : ExactOneComplex V E P)
    (x : EuclideanSpace ℝ E) :
    0 ≤ inner ℝ (formLaplacian C x) x := by
  calc
    0 ≤ inner ℝ (C.d₁ x) (C.d₁ x) := real_inner_self_nonneg
    _ = inner ℝ x (formLaplacian C x) := by
      rw [formLaplacian]
      exact (LinearMap.adjoint_inner_right C.d₁ x (C.d₁ x)).symm
    _ = inner ℝ (formLaplacian C x) x := real_inner_comm _ _

/-- The covariance quadratic form on co-closed tests, before the factor `β`.
Exactness makes the inverse well-defined; positivity follows from the
sum-of-squares identity for `d₁† d₁`. -/
@[expose] noncomputable def quotientCovarianceQuadratic
    (C : ExactOneComplex V E P) (x : coClosed C) : ℝ :=
  inner ℝ (x : EuclideanSpace ℝ E)
    (hodgeInverseOnCoClosed C x : EuclideanSpace ℝ E)

theorem quotientCovarianceQuadratic_nonneg
    (C : ExactOneComplex V E P) (x : coClosed C) :
    0 ≤ quotientCovarianceQuadratic C x := by
  have hInv := hodgeOnCoClosed_hodgeInverse C x
  have hval : formLaplacian C
      (hodgeInverseOnCoClosed C x : EuclideanSpace ℝ E) = x := by
    exact congrArg Subtype.val hInv
  rw [quotientCovarianceQuadratic, ← hval]
  exact formLaplacian_inner_nonneg C
    (hodgeInverseOnCoClosed C x : EuclideanSpace ℝ E)


end FroehlichSpencer.FS82.Gaussian
end
