/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Count
public import FroehlichSpencer.Infra.Spectral.QuadForm
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Location of the spectrum of a diagonal perturbation

For `A : Matrix ι ι ℂ` and a real potential `v : ι → ℝ`, the eigenvalues of the Hermitian matrix
`A + diagonal v` lie in `[a - ‖A‖, b + ‖A‖]` when `v` takes values in `[a, b]` (operator-norm
form), and each lies within the Gershgorin row-sum radius of some `v k + Re (A k k)`.

Counting
corollaries: no eigenvalue `≤ E` above the potential level `E + ‖A‖`, and all eigenvalues `≤ E`
below the level `E - ‖A‖`.

This is the first-order spectral location used in
Fröhlich–Spencer (1983), Fröhlich–Spencer (1983); nothing here is lattice specific.
-/

@[expose] public section

open Matrix Finset
open scoped Matrix.Norms.L2Operator

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem re_star_dotProduct_self_eigenvectorBasis {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (i : ι) :
    (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i)).re = 1 := by
  rw [← norm_toLp_sq]
  simp

/-- Spectrum of a diagonal perturbation, operator-norm form. -/
theorem eigenvalues_mem_Icc_of_diagonal_add (A : Matrix ι ι ℂ) (v : ι → ℝ) {a b : ℝ}
    (hv : ∀ i, v i ∈ Set.Icc a b) (hH : (A + diagonal (fun i => (v i : ℂ))).IsHermitian)
    (i : ι) : hH.eigenvalues i ∈ Set.Icc (a - ‖A‖) (b + ‖A‖) := by
  set u : ι → ℂ := ⇑(hH.eigenvectorBasis i) with hu
  have hnorm : (star u ⬝ᵥ u).re = 1 := re_star_dotProduct_self_eigenvectorBasis hH i
  have heig := re_star_dotProduct_mulVec_eigenvectorBasis hH i
  rw [← hu, re_star_dotProduct_add_mulVec, re_star_dotProduct_diagonal_mulVec] at heig
  have hA := abs_re_star_dotProduct_mulVec_le A u
  rw [hnorm, mul_one] at hA
  have hsq : ∑ j, ‖u j‖ ^ 2 = 1 := by
    rw [← re_star_dotProduct_self_eq_sum_norm_sq]; exact hnorm
  have hlo : a ≤ ∑ j, v j * ‖u j‖ ^ 2 := by
    calc a = ∑ j, a * ‖u j‖ ^ 2 := by rw [← mul_sum, hsq, mul_one]
      _ ≤ _ := sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hv j).1 (sq_nonneg _)
  have hhi : ∑ j, v j * ‖u j‖ ^ 2 ≤ b := by
    calc _ ≤ ∑ j, b * ‖u j‖ ^ 2 :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hv j).2 (sq_nonneg _)
      _ = b := by rw [← mul_sum, hsq, mul_one]
  have := abs_le.mp hA
  rw [← heig]
  constructor <;> linarith [this.1, this.2]

/-- Gershgorin for Hermitian matrices, real form. -/
theorem exists_abs_eigenvalues_sub_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (i : ι) :
    ∃ k, |hH.eigenvalues i - (H k k).re| ≤ ∑ j ∈ Finset.univ.erase k, ‖H k j‖ := by
  have hev : Module.End.HasEigenvalue (Matrix.toLin' H) (hH.eigenvalues i : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⇑(hH.eigenvectorBasis i)) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      have := hH.mulVec_eigenvectorBasis i
      rw [this, ← Complex.coe_smul]
    · intro h
      have := re_star_dotProduct_self_eigenvectorBasis hH i
      rw [h] at this
      simp at this
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
  refine ⟨k, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have h1 : (hH.eigenvalues i : ℂ) - H k k = ((hH.eigenvalues i - (H k k).re : ℝ) : ℂ) := by
    have hk' : ((H k k).re : ℂ) = H k k := hH.coe_re_apply_self k
    rw [Complex.ofReal_sub, hk']
  rwa [h1, Complex.norm_real, Real.norm_eq_abs] at hk

theorem exists_abs_eigenvalues_sub_diagonal_add_le (A : Matrix ι ι ℂ) (v : ι → ℝ)
    (hH : (A + diagonal (fun i => (v i : ℂ))).IsHermitian) (i : ι) :
    ∃ k, |hH.eigenvalues i - (v k + (A k k).re)| ≤ ∑ j ∈ Finset.univ.erase k, ‖A k j‖ := by
  obtain ⟨k, hk⟩ := exists_abs_eigenvalues_sub_le hH i
  refine ⟨k, ?_⟩
  have h1 : ((A + diagonal (fun i => (v i : ℂ))) k k).re = v k + (A k k).re := by
    simp [add_comm]
  have h2 : ∑ j ∈ Finset.univ.erase k, ‖(A + diagonal (fun i => (v i : ℂ))) k j‖
      = ∑ j ∈ Finset.univ.erase k, ‖A k j‖ := by
    refine sum_congr rfl fun j hj => ?_
    have hjk : k ≠ j := fun h => (mem_erase.mp hj).1 h.symm
    simp [diagonal_apply_ne _ hjk]
  rwa [h1, h2] at hk

/-- No eigenvalue `≤ E` when the potential is everywhere above `E + ‖A‖`. -/
theorem eigenvalueCount_eq_zero_of_diagonal_add (A : Matrix ι ι ℂ) (v : ι → ℝ)
    (hH : (A + diagonal (fun i => (v i : ℂ))).IsHermitian) {E : ℝ} (hv : ∀ i, E + ‖A‖ < v i) :
    eigenvalueCount hH E = 0 := by
  rw [eigenvalueCount, card_eq_zero, filter_eq_empty_iff]
  intro i _
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨i, mem_univ _⟩
  have hlt : E + ‖A‖ < univ.inf' hne v := (lt_inf'_iff hne).mpr fun j _ => hv j
  have := (eigenvalues_mem_Icc_of_diagonal_add A v (a := univ.inf' hne v) (b := univ.sup' hne v)
    (fun j => ⟨inf'_le _ (mem_univ j), le_sup' _ (mem_univ j)⟩) hH i).1
  rw [not_le]
  linarith

/-- Every eigenvalue is `≤ E` when the potential is everywhere below `E - ‖A‖`. -/
theorem eigenvalueCount_eq_card_of_diagonal_add (A : Matrix ι ι ℂ) (v : ι → ℝ)
    (hH : (A + diagonal (fun i => (v i : ℂ))).IsHermitian) {E : ℝ} (hv : ∀ i, v i ≤ E - ‖A‖) :
    eigenvalueCount hH E = Fintype.card ι := by
  rw [eigenvalueCount, filter_true_of_mem, card_univ]
  intro i _
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨i, mem_univ _⟩
  have := (eigenvalues_mem_Icc_of_diagonal_add A v (a := univ.inf' hne v) (b := E - ‖A‖)
    (fun j => ⟨inf'_le _ (mem_univ j), hv j⟩) hH i).2
  linarith

/-- Gershgorin form of the previous fact: a nonzero count forces a low site. -/
theorem exists_le_of_eigenvalueCount_pos (A : Matrix ι ι ℂ) (v : ι → ℝ)
    (hH : (A + diagonal (fun i => (v i : ℂ))).IsHermitian) {E : ℝ}
    (hpos : 0 < eigenvalueCount hH E) :
    ∃ k, v k + (A k k).re - ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ E := by
  obtain ⟨i, hi⟩ := card_pos.mp hpos
  have hi' : hH.eigenvalues i ≤ E := by simpa using hi
  obtain ⟨k, hk⟩ := exists_abs_eigenvalues_sub_diagonal_add_le A v hH i
  exact ⟨k, by linarith [(abs_le.mp hk).1]⟩

end FroehlichSpencer.Infra
