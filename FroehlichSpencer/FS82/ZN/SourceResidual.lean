/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.CubeLoopField
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex
public import FroehlichSpencer.FS82.Wilson.LatticeCurl

/-!
# The source §3 plaquette field and its residual on centred cubes

FS82 (3.22) assigns `2π ξ/N` to each primal plaquette whose dual lies in the
0–1 disorder sheet and zero elsewhere.

Under the C1 embedding, the dual
plaquettes are exactly the 2–3 cells selected by the indicator in
`cubeSheet_apply`.

The field below is written in the source star orientation of C4, so its unit
sheet is `cubeSheet`.

The C2 coordinate orientation on these 2–3 cells has
sign `-1` (`latticeCellOrientationSign_plaquette₂₃`); the coordinate-oriented
field and residual are recorded separately below.

Its perimeter
bound is for centred cubes with `N_box ≥ max(L,T)+1`, and is a finite-box
result; it does not identify the unscripted infinite-volume inverse in (3.25).
-/

public section

namespace FroehlichSpencer.FS82.ZN

open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Moment.SourceConstructor

/--
The literal finite-box field of FS82 (3.22), on source-star-oriented dual
plaquettes: `2π ξ/N` on the cells whose primal plaquette dual lies in the
0–1 sheet, and zero elsewhere.

The modulus is named `q` to distinguish it
from the cube radius `N_box`.
-/
@[expose] noncomputable def cubeSourcePlaquetteField
    (ξ q L T N_box : ℕ) : EuclideanSpace ℝ (SourceDualTwoCells (cube N_box)) :=
  (2 * Real.pi * (ξ : ℝ) / (q : ℝ)) • cubeSheet L T N_box


theorem cubeSourcePlaquetteField_eq_twist_smul_cubeSheet
    (ξ q L T N_box : ℕ) :
    cubeSourcePlaquetteField ξ q L T N_box =
      (2 * Real.pi * (ξ : ℝ) / (q : ℝ)) • cubeSheet L T N_box := rfl


/--
The box radius is a separate
parameter from the twist modulus.

This is the component of the source residual in the chosen orientation.
-/
@[expose] noncomputable def cubeSourceResidual
    (ξ q L T N_box : ℕ) : EuclideanSpace ℝ (SourceDualTwoCells (cube N_box)) :=
  loopFieldResidual (sourceLatticeComplex (B := cube N_box))
    (cubeSourcePlaquetteField ξ q L T N_box)


/-- Projection residuals are homogeneous in the input field. -/
theorem loopFieldResidual_smul (B : Box 4) (a : ℝ)
    (σ : EuclideanSpace ℝ (SourceDualTwoCells B)) :
    loopFieldResidual (sourceLatticeComplex (B := B)) (a • σ) =
      a • loopFieldResidual (sourceLatticeComplex (B := B)) σ := by
  simp only [loopFieldResidual, map_smul, smul_sub]


theorem cubeSourceResidual_eq_scaled_loopFieldResidual
    (ξ q L T N_box : ℕ) :
    cubeSourceResidual ξ q L T N_box =
      (2 * Real.pi * (ξ : ℝ) / (q : ℝ)) •
        loopFieldResidual (sourceLatticeComplex (B := cube N_box))
          (cubeSheet L T N_box) := by
  rw [cubeSourceResidual, cubeSourcePlaquetteField_eq_twist_smul_cubeSheet,
    loopFieldResidual_smul]


private theorem norm_sq_smul (a : ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : E) : ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/--
The source residual has the the source residual estimate perimeter upper bound on centred cubes:
`‖ε‖² ≤ 24π² (ξ/q)² (L+T)` whenever `N_box ≥ max(L,T)+1`.
-/
theorem cubeSourceResidual_normSq_le
    {ξ q L T N_box : ℕ} (_hξ : 1 ≤ ξ) (_hξq : ξ < q)
    (hbox : max L T + 1 ≤ N_box) :
    ‖cubeSourceResidual ξ q L T N_box‖ ^ 2 ≤
      24 * Real.pi ^ 2 * ((ξ : ℝ) / (q : ℝ)) ^ 2 * ((L : ℝ) + T) := by
  rw [cubeSourceResidual_eq_scaled_loopFieldResidual]
  calc
    ‖(2 * Real.pi * (ξ : ℝ) / (q : ℝ)) •
        loopFieldResidual (sourceLatticeComplex (B := cube N_box))
          (cubeSheet L T N_box)‖ ^ 2
      = (2 * Real.pi * (ξ : ℝ) / (q : ℝ)) ^ 2 *
          ‖loopFieldResidual (sourceLatticeComplex (B := cube N_box))
            (cubeSheet L T N_box)‖ ^ 2 := norm_sq_smul _ _
    _ ≤ (2 * Real.pi * (ξ : ℝ) / (q : ℝ)) ^ 2 *
          (6 * ((L : ℝ) + T)) :=
        mul_le_mul_of_nonneg_left (cube_loopField_normSq_le hbox) (sq_nonneg _)
    _ = 24 * Real.pi ^ 2 * ((ξ : ℝ) / (q : ℝ)) ^ 2 * ((L : ℝ) + T) := by ring


end FroehlichSpencer.FS82.ZN

end
