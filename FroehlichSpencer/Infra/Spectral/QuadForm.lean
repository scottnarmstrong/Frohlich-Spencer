/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Quadratic forms of matrices on plain vectors

Basic facts about `(star u ⬝ᵥ (A *ᵥ u)).re` for `A : Matrix ι ι ℂ` and `u : ι → ℂ`, including the
bound by the L² operator norm and the Rayleigh quotient at an eigenvector of a Hermitian matrix.
Nothing here is specific to Fröhlich–Spencer (1983).
-/

@[expose] public section

open Matrix Finset
open scoped Matrix.Norms.L2Operator

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι]

theorem re_star_dotProduct_self_eq_sum_norm_sq (u : ι → ℂ) :
    (star u ⬝ᵥ u).re = ∑ i, ‖u i‖ ^ 2 := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

theorem re_star_dotProduct_self_nonneg (u : ι → ℂ) : 0 ≤ (star u ⬝ᵥ u).re := by
  rw [re_star_dotProduct_self_eq_sum_norm_sq]
  exact sum_nonneg fun i _ => sq_nonneg _

theorem re_star_dotProduct_self_pos {u : ι → ℂ} (hu : u ≠ 0) : 0 < (star u ⬝ᵥ u).re := by
  rw [re_star_dotProduct_self_eq_sum_norm_sq]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hu
  exact sum_pos' (fun i _ => sq_nonneg _)
    ⟨j, mem_univ _, pow_pos (norm_pos_iff.mpr hj) 2⟩

theorem norm_toLp_sq (u : ι → ℂ) : ‖WithLp.toLp 2 u‖ ^ 2 = (star u ⬝ᵥ u).re := by
  rw [re_star_dotProduct_self_eq_sum_norm_sq, EuclideanSpace.norm_sq_eq]

theorem re_star_dotProduct_add_mulVec (A B : Matrix ι ι ℂ) (u : ι → ℂ) :
    (star u ⬝ᵥ ((A + B) *ᵥ u)).re = (star u ⬝ᵥ (A *ᵥ u)).re + (star u ⬝ᵥ (B *ᵥ u)).re := by
  rw [add_mulVec, dotProduct_add, Complex.add_re]

theorem re_star_dotProduct_sub_mulVec (A B : Matrix ι ι ℂ) (u : ι → ℂ) :
    (star u ⬝ᵥ ((A - B) *ᵥ u)).re = (star u ⬝ᵥ (A *ᵥ u)).re - (star u ⬝ᵥ (B *ᵥ u)).re := by
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re]

variable [DecidableEq ι]

theorem re_star_dotProduct_smul_one_mulVec (t : ℝ) (u : ι → ℂ) :
    (star u ⬝ᵥ ((t • (1 : Matrix ι ι ℂ)) *ᵥ u)).re = t * (star u ⬝ᵥ u).re := by
  have : (t • (1 : Matrix ι ι ℂ)) *ᵥ u = (t : ℂ) • u := by
    ext i
    simp [mulVec, dotProduct, Matrix.one_apply, Finset.sum_ite_eq]
  rw [this, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem re_star_dotProduct_diagonal_mulVec (v : ι → ℝ) (u : ι → ℂ) :
    (star u ⬝ᵥ (diagonal (fun i => (v i : ℂ)) *ᵥ u)).re = ∑ i, v i * ‖u i‖ ^ 2 := by
  simp only [mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The quadratic form is bounded by the L² operator norm. -/
theorem abs_re_star_dotProduct_mulVec_le (A : Matrix ι ι ℂ) (u : ι → ℂ) :
    |(star u ⬝ᵥ (A *ᵥ u)).re| ≤ ‖A‖ * (star u ⬝ᵥ u).re := by
  have h1 := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h2 : |(star u ⬝ᵥ (A *ᵥ u)).re| ≤ ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 (A *ᵥ u)‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    have := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 u) (WithLp.toLp 2 (A *ᵥ u))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa [dotProduct_comm] using this
  rw [← norm_toLp_sq]
  calc _ ≤ _ := h2
    _ ≤ ‖WithLp.toLp 2 u‖ * (‖A‖ * ‖WithLp.toLp 2 u‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := by ring

/-- Rayleigh quotient at an eigenvector. -/
theorem re_star_dotProduct_mulVec_eigenvectorBasis {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (i : ι) :
    (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ (H *ᵥ ⇑(hH.eigenvectorBasis i))).re = hH.eigenvalues i :=
  (hH.eigenvalues_eq i).symm

theorem abs_eigenvalues_le_norm {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (i : ι) :
    |hH.eigenvalues i| ≤ ‖H‖ := by
  have h := abs_re_star_dotProduct_mulVec_le H ⇑(hH.eigenvectorBasis i)
  rw [re_star_dotProduct_mulVec_eigenvectorBasis hH i, ← norm_toLp_sq] at h
  simpa using h

end FroehlichSpencer.Infra
