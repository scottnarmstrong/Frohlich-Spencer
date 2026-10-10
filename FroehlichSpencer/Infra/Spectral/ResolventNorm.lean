/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Regularity
public import FroehlichSpencer.Infra.Resolvent
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Matrix.Order

/-!
# Resolvent norm equals inverse spectral distance

For a Hermitian matrix `H`, `H - z • 1` is invertible iff `z` is not an eigenvalue, and the
L² operator norm of its inverse is the reciprocal of the distance from `z` to the spectrum.

This links the resolvent bound `‖G‖ ≤ e^{√d}` of Fröhlich–Spencer (1983) with the spectral
condition `dist(spec H, E) ≥ e^{-√d}` (Condition A(c), Fröhlich–Spencer (1983)).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- Spectral factorization of the shifted matrix. -/
theorem sub_smul_one_eq_unitary_diagonal (hH : H.IsHermitian) (z : ℂ) :
    H - z • (1 : Matrix ι ι ℂ) =
      (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
        Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ) - z) *
        star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
  let Uu := hH.eigenvectorUnitary
  let eig : ι → ℂ := fun i => (hH.eigenvalues i : ℂ)
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) Uu
  have hs : H = φ (Matrix.diagonal eig) := by
    simpa [φ, eig, Function.comp_def] using hH.spectral_theorem
  have hscalar : φ (z • (1 : Matrix ι ι ℂ)) = z • (1 : Matrix ι ι ℂ) := by
    simp [φ]
  have hdiag : Matrix.diagonal eig - z • (1 : Matrix ι ι ℂ) =
      Matrix.diagonal (fun i => eig i - z) := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  calc
    H - z • (1 : Matrix ι ι ℂ) = φ (Matrix.diagonal eig) - φ (z • (1 : Matrix ι ι ℂ)) := by
      rw [hscalar, ← hs]
    _ = φ (Matrix.diagonal (fun i => eig i - z)) := by rw [← map_sub, hdiag]
    _ = _ := by
      change ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) Uu) _ = _
      rw [Unitary.conjStarAlgAut_apply]

theorem isUnit_sub_smul_one_iff (hH : H.IsHermitian) (z : ℂ) :
    IsUnit (H - z • (1 : Matrix ι ι ℂ)) ↔ ∀ i, (hH.eigenvalues i : ℂ) ≠ z := by
  let Uu := hH.eigenvectorUnitary
  have hU : IsUnit (Uu : Matrix ι ι ℂ) := (Unitary.toUnits Uu).isUnit
  have hUs : IsUnit (star (Uu : Matrix ι ι ℂ)) := (Unitary.toUnits (star Uu)).isUnit
  have hD : IsUnit (H - z • (1 : Matrix ι ι ℂ)) ↔
      IsUnit (Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ) - z)) := by
    rw [sub_smul_one_eq_unitary_diagonal hH z]
    constructor
    · intro h
      have h2 : Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ) - z) =
          star (Uu : Matrix ι ι ℂ) * ((Uu : Matrix ι ι ℂ) *
            Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ) - z) *
            star (Uu : Matrix ι ι ℂ)) * (Uu : Matrix ι ι ℂ) := by
        have h1 : star (Uu : Matrix ι ι ℂ) * (Uu : Matrix ι ι ℂ) = 1 := by simp [Uu]
        calc _ = (star (Uu : Matrix ι ι ℂ) * (Uu : Matrix ι ι ℂ)) *
              Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ) - z) *
              (star (Uu : Matrix ι ι ℂ) * (Uu : Matrix ι ι ℂ)) := by rw [h1]; simp
          _ = _ := by noncomm_ring
      rw [h2]
      exact (hUs.mul h).mul hU
    · intro h
      exact (hU.mul h).mul hUs
  rw [hD, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  simp only [isUnit_iff_ne_zero, ne_eq, sub_eq_zero]

/-- Inverse of the shifted matrix when `z` is not an eigenvalue. -/
theorem inv_sub_smul_one_eq (hH : H.IsHermitian) (z : ℂ) (hz : ∀ i, (hH.eigenvalues i : ℂ) ≠ z) :
    (H - z • (1 : Matrix ι ι ℂ))⁻¹ =
      (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
        Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹) *
        star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
  let Uu := hH.eigenvectorUnitary
  have hval : ∀ i, (hH.eigenvalues i : ℂ) - z ≠ 0 := fun i => sub_ne_zero.mpr (hz i)
  have hdl : Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ) - z) *
      Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹) = 1 := by
    simp [Matrix.diagonal_mul_diagonal, hval]
  have hUs : star (Uu : Matrix ι ι ℂ) * (Uu : Matrix ι ι ℂ) = 1 := by simp [Uu]
  have hUs' : (Uu : Matrix ι ι ℂ) * star (Uu : Matrix ι ι ℂ) = 1 := by simp [Uu]
  apply Matrix.inv_eq_right_inv
  rw [sub_smul_one_eq_unitary_diagonal hH z]
  calc _ = (Uu : Matrix ι ι ℂ) * (Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ) - z) *
        (star (Uu : Matrix ι ι ℂ) * (Uu : Matrix ι ι ℂ)) *
        Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹)) *
        star (Uu : Matrix ι ι ℂ) := by noncomm_ring
    _ = 1 := by
      rw [hUs, mul_one, hdl, mul_one, hUs']

/-- The resolvent norm is the reciprocal of the distance from `z` to the spectrum. The content is
the case where `z` is not an eigenvalue (then `H - z • 1` is invertible, `isUnit_sub_smul_one_iff`).
When `z` is an eigenvalue both sides are `0`, only because of Lean's conventions `A⁻¹ = 0` for
singular `A` and `1 / 0 = 0`. -/
theorem norm_inv_sub_smul_one_eq [Nonempty ι] (hH : H.IsHermitian) (z : ℂ) :
    ‖(H - z • (1 : Matrix ι ι ℂ))⁻¹‖ =
      1 / Finset.univ.inf' Finset.univ_nonempty (fun i => ‖(hH.eigenvalues i : ℂ) - z‖) := by
  set m := Finset.univ.inf' Finset.univ_nonempty (fun i => ‖(hH.eigenvalues i : ℂ) - z‖)
    with hm
  by_cases h : ∀ i, (hH.eigenvalues i : ℂ) ≠ z
  · have hmle : ∀ i, m ≤ ‖(hH.eigenvalues i : ℂ) - z‖ := fun i =>
      Finset.inf'_le _ (Finset.mem_univ i)
    have hmpos : 0 < m := by
      rw [hm, Finset.lt_inf'_iff]
      intro i _
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (h i))
    let Uu := hH.eigenvectorUnitary
    rw [inv_sub_smul_one_eq hH z h]
    have hn : ‖(Uu : Matrix ι ι ℂ) *
        Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹) *
        star (Uu : Matrix ι ι ℂ)‖ =
        ‖Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹)‖ := by
      rw [mul_assoc]
      calc _ = ‖Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹) *
            star (Uu : Matrix ι ι ℂ)‖ := CStarRing.norm_coe_unitary_mul Uu _
        _ = _ := CStarRing.norm_mul_coe_unitary _ (star Uu)
    rw [hn, Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      rw [norm_inv, one_div]
      exact inv_anti₀ hmpos (hmle i)
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι))
        (fun i => ‖(hH.eigenvalues i : ℂ) - z‖)
      have := norm_le_pi_norm (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹) i
      rw [norm_inv, ← hi] at this
      simpa only [one_div] using this
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hnu : ¬ IsUnit (H - z • (1 : Matrix ι ι ℂ)) := by
      rw [isUnit_sub_smul_one_iff hH z]
      push Not
      exact ⟨i, hi⟩
    have hm0 : m = 0 := by
      apply le_antisymm
      · calc m ≤ ‖(hH.eigenvalues i : ℂ) - z‖ := Finset.inf'_le _ (Finset.mem_univ i)
          _ = 0 := by rw [hi, sub_self, norm_zero]
      · rw [hm]
        exact Finset.le_inf' _ _ fun j _ => norm_nonneg _
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [Matrix.isUnit_iff_isUnit_det] at hnu),
      norm_zero, hm0, div_zero]

theorem isUnit_sub_smul_one_iff_pos [Nonempty ι] (hH : H.IsHermitian) (E : ℝ) :
    IsUnit (H - (E : ℂ) • (1 : Matrix ι ι ℂ)) ↔
      0 < Finset.univ.inf' Finset.univ_nonempty (fun i => |hH.eigenvalues i - E|) := by
  rw [isUnit_sub_smul_one_iff hH, Finset.lt_inf'_iff]
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_univ, true_implies, abs_pos, ne_eq, sub_eq_zero]
  exact_mod_cast Iff.rfl

/-- Real-energy form of `norm_inv_sub_smul_one_eq`: `‖(H - E • 1)⁻¹‖ = 1 / min_i |λ_i - E|`.
Substantive when the minimum is positive (`isUnit_sub_smul_one_iff_pos`); if `E` is an eigenvalue
both sides are `0` by the junk conventions `A⁻¹ = 0`, `1 / 0 = 0`. For a gap statement that
carries invertibility explicitly, use `le_inf'_abs_eigenvalues_sub_iff_norm_inv_le`. -/
theorem norm_inv_sub_real_smul_one_eq [Nonempty ι] (hH : H.IsHermitian) (E : ℝ) :
    ‖(H - (E : ℂ) • (1 : Matrix ι ι ℂ))⁻¹‖ =
      1 / Finset.univ.inf' Finset.univ_nonempty (fun i => |hH.eigenvalues i - E|) := by
  rw [norm_inv_sub_smul_one_eq hH]
  congr 2
  funext i
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Entrywise resolvent bound by the reciprocal spectral distance (both sides `0` in the
junk-valued case where `z` is an eigenvalue). -/
theorem norm_inv_sub_smul_one_apply_le [Nonempty ι] (hH : H.IsHermitian) (z : ℂ) (i j : ι) :
    ‖(H - z • (1 : Matrix ι ι ℂ))⁻¹ i j‖ ≤
      1 / Finset.univ.inf' Finset.univ_nonempty (fun i => ‖(hH.eigenvalues i : ℂ) - z‖) :=
  (FroehlichSpencer.Matrix.norm_entry_le_l2_opNorm _ i j).trans
    (norm_inv_sub_smul_one_eq hH z).le

theorem le_inf'_abs_eigenvalues_sub_iff_norm_inv_le [Nonempty ι] (hH : H.IsHermitian) (E : ℝ)
    {κ : ℝ} (hκ : 0 < κ) :
    κ ≤ Finset.univ.inf' Finset.univ_nonempty (fun i => |hH.eigenvalues i - E|) ↔
      IsUnit (H - (E : ℂ) • (1 : Matrix ι ι ℂ)) ∧
        ‖(H - (E : ℂ) • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ 1 / κ := by
  rw [norm_inv_sub_real_smul_one_eq hH, isUnit_sub_smul_one_iff_pos hH]
  set m := Finset.univ.inf' Finset.univ_nonempty (fun i => |hH.eigenvalues i - E|)
  constructor
  · intro h
    exact ⟨hκ.trans_le h, one_div_le_one_div_of_le hκ h⟩
  · rintro ⟨hm, h⟩
    exact (one_div_le_one_div hm hκ).mp h

theorem forall_mem_spectrum_le_abs_sub_iff [Nonempty ι] (hH : H.IsHermitian) (E κ : ℝ) :
    (∀ x ∈ spectrum ℝ H, κ ≤ |x - E|) ↔
      κ ≤ Finset.univ.inf' Finset.univ_nonempty (fun i => |hH.eigenvalues i - E|) := by
  rw [forall_mem_spectrum_iff hH (fun x => κ ≤ |x - E|), le_inf'_abs_eigenvalues_sub_iff hH]

end FroehlichSpencer.Infra
