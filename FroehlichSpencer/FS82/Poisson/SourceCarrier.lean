/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.DualComplex
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex

/-!
This module binds the finite Poisson link carrier and compressed stencil to
the physical `Λ*` carrier.

Its co-closed space and Hodge inverse use lattice-oriented complex, including the C2 orientation twist.

The Hodge
operator is the compressed physical `Π_{Λ*} δd` stencil.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open FroehlichSpencer.FS82

variable {B : Cubical.Box 4}


/-- The physical Hodge operator on `Λ*` fields. -/
noncomputable def sourcePoissonHodge (origin : Fin 4 → ℤ) :
    EuclideanSpace ℝ (Gaussian.SourceDualOneCells B) →ₗ[ℝ]
      EuclideanSpace ℝ (Gaussian.SourceDualOneCells B) :=
  Gaussian.formLaplacian (Gaussian.latticeExactOneComplex (B := B) origin)


/-- The physical Hodge operator is the literal compressed `Π_{Λ*} δd`
stencil. This is the C2 bridge from the star-oriented source complex. -/
theorem sourcePoissonHodge_eq_stencil (origin : Fin 4 → ℤ) :
    sourcePoissonHodge (B := B) origin =
      Gaussian.latticeStencilOperator (B := B) origin :=
  Gaussian.latticeFormLaplacian_eq_stencil (B := B) origin


end FroehlichSpencer.FS82.Poisson
