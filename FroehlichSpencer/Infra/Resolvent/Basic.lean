/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Generic resolvent algebra

This module develops finite-dimensional matrix resolvent tools motivated by
Fröhlich–Spencer, *Absence of diffusion in the Anderson tight binding model
for large disorder or low energy* (1983), equations (2.10)–(2.13), pp. 159–160.
All declarations here are generic algebra for finite matrices; the paper
specific Hamiltonians and lattice are not defined here.
The spectral parameter convention throughout is `H - z • (1 : Matrix ι ι ℂ)`.
-/

public section

namespace FroehlichSpencer

open scoped Matrix.Norms.L2Operator

/-- The first resolvent identity in a ring, in the order used by the
finite-volume resolvent formula. -/
theorem ringInverse_resolvent_identity {R : Type*} [Ring R] (A A₀ : R)
    (hA : IsUnit A) (hA₀ : IsUnit A₀) :
    Ring.inverse A = Ring.inverse A₀ - Ring.inverse A₀ * (A - A₀) * Ring.inverse A := by
  calc
    Ring.inverse A = Ring.inverse A₀ * A₀ * Ring.inverse A := by
      rw [Ring.inverse_mul_cancel A₀ hA₀, one_mul]
    _ = Ring.inverse A₀ - Ring.inverse A₀ * (A - A₀) * Ring.inverse A := by
      calc
        Ring.inverse A₀ * A₀ * Ring.inverse A =
            Ring.inverse A₀ -
              (Ring.inverse A₀ - Ring.inverse A₀ * A₀ * Ring.inverse A) := by simp
        _ = Ring.inverse A₀ -
              (Ring.inverse A₀ * (A * Ring.inverse A) -
                Ring.inverse A₀ * A₀ * Ring.inverse A) := by
          rw [Ring.mul_inverse_cancel A hA]
          simp
        _ = _ := by noncomm_ring

/-- The mirrored first resolvent identity. -/
theorem ringInverse_resolvent_identity_mirror {R : Type*} [Ring R] (A A₀ : R)
    (hA : IsUnit A) (hA₀ : IsUnit A₀) :
    Ring.inverse A = Ring.inverse A₀ - Ring.inverse A * (A - A₀) * Ring.inverse A₀ := by
  calc
    Ring.inverse A = Ring.inverse A * A₀ * Ring.inverse A₀ := by
      calc
        Ring.inverse A = Ring.inverse A * (A₀ * Ring.inverse A₀) := by
          rw [Ring.mul_inverse_cancel A₀ hA₀, mul_one]
        _ = _ := by rw [mul_assoc]
    _ = Ring.inverse A₀ - Ring.inverse A * (A - A₀) * Ring.inverse A₀ := by
      calc
        Ring.inverse A * A₀ * Ring.inverse A₀ =
            Ring.inverse A₀ -
              (Ring.inverse A₀ - Ring.inverse A * A₀ * Ring.inverse A₀) := by simp
        _ = Ring.inverse A₀ -
              (Ring.inverse A * (A * Ring.inverse A₀) -
                Ring.inverse A * A₀ * Ring.inverse A₀) := by
          rw [← mul_assoc (Ring.inverse A) A (Ring.inverse A₀),
            Ring.inverse_mul_cancel A hA]
          simp
        _ = _ := by noncomm_ring

/-- Every matrix entry is bounded by the `L²` operator norm. -/
theorem Matrix.norm_entry_le_l2_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  let e : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j (1 : ℂ))
  have hcoord : ‖A i j‖ ≤ ‖T e‖ := by
    have h := PiLp.norm_apply_le (T e) i
    simpa [T, e, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one] using h
  calc
    ‖A i j‖ ≤ ‖T e‖ := hcoord
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = ‖A‖ := by simp [T, e, Matrix.l2_opNorm_toEuclideanCLM]

end FroehlichSpencer
