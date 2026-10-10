/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.MinMax
public import FroehlichSpencer.Infra.Spectral.Sorted
public import FroehlichSpencer.Infra.Spectral.QuadForm
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Shift invariance and Loewner monotonicity of eigenvalue counts

Shift invariance `N(E, H + t) = N(E - t, H)` (Fröhlich–Spencer (1983), Appendix C uses
`N(E, v) = N(0, v - E)`) and monotonicity of the counting functions and sorted eigenvalues under
positive semidefinite perturbations; in particular raising a diagonal potential lowers the counts.
-/

@[expose] public section

open Matrix Finset ComplexOrder

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}

theorem eigenvalueCount_add_smul_one (hH : H.IsHermitian) (t : ℝ)
    (hHt : (H + t • (1 : Matrix ι ι ℂ)).IsHermitian) (E : ℝ) :
    eigenvalueCount hHt E = eigenvalueCount hH (E - t) := by
  refine (isGreatest_eigenvalueCount hHt E).unique ?_
  have hset : {d | ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = d ∧
      ∀ u ∈ V, (star u ⬝ᵥ ((H + t • (1 : Matrix ι ι ℂ)) *ᵥ u)).re ≤ E * (star u ⬝ᵥ u).re} =
      {d | ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = d ∧
      ∀ u ∈ V, (star u ⬝ᵥ (H *ᵥ u)).re ≤ (E - t) * (star u ⬝ᵥ u).re} := by
    ext d
    refine exists_congr fun V => and_congr_right fun _ => forall₂_congr fun u _ => ?_
    rw [re_star_dotProduct_add_mulVec, re_star_dotProduct_smul_one_mulVec]
    constructor <;> intro h <;> linarith only [h]
  rw [hset]
  exact isGreatest_eigenvalueCount hH (E - t)

theorem eigenvalueCountLT_add_smul_one (hH : H.IsHermitian) (t : ℝ)
    (hHt : (H + t • (1 : Matrix ι ι ℂ)).IsHermitian) (E : ℝ) :
    eigenvalueCountLT hHt E = eigenvalueCountLT hH (E - t) := by
  refine (isGreatest_eigenvalueCountLT hHt E).unique ?_
  have hset : {d | ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = d ∧
      ∀ u ∈ V, u ≠ 0 →
        (star u ⬝ᵥ ((H + t • (1 : Matrix ι ι ℂ)) *ᵥ u)).re < E * (star u ⬝ᵥ u).re} =
      {d | ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = d ∧
      ∀ u ∈ V, u ≠ 0 → (star u ⬝ᵥ (H *ᵥ u)).re < (E - t) * (star u ⬝ᵥ u).re} := by
    ext d
    refine exists_congr fun V => and_congr_right fun _ =>
      forall₂_congr fun u _ => forall_congr' fun _ => ?_
    rw [re_star_dotProduct_add_mulVec, re_star_dotProduct_smul_one_mulVec]
    constructor <;> intro h <;> linarith only [h]
  rw [hset]
  exact isGreatest_eigenvalueCountLT hH (E - t)

theorem eigenvaluesAsc_add_smul_one (hH : H.IsHermitian) (t : ℝ)
    (hHt : (H + t • (1 : Matrix ι ι ℂ)).IsHermitian) (k : Fin (Fintype.card ι)) :
    eigenvaluesAsc hHt k = eigenvaluesAsc hH k + t := by
  refine le_antisymm ?_ ?_
  · refine eigenvaluesAsc_le_add_of_eigenvalueCount_le hHt hH t (fun E => ?_) k
    rw [eigenvalueCount_add_smul_one hH t hHt, add_sub_cancel_right]
  · have h := eigenvaluesAsc_le_add_of_eigenvalueCount_le hH hHt (-t) (fun E => by
      rw [eigenvalueCount_add_smul_one hH t hHt, sub_eq_add_neg]) k
    linarith only [h]

/--
The relation `N(E, v) = N(0, v - E)` used in FS83 Appendix C (Fröhlich–Spencer (1983),
line 1820, after (C.3)), for a diagonal potential added to any matrix.
-/
theorem eigenvalueCount_add_diagonal_eq (A : Matrix ι ι ℂ) (v : ι → ℝ) (E : ℝ)
    (hv : (A + diagonal (fun i => (v i : ℂ))).IsHermitian)
    (hvE : (A + diagonal (fun i => ((v i - E : ℝ) : ℂ))).IsHermitian) :
    eigenvalueCount hv E = eigenvalueCount hvE 0 := by
  have hmat : A + diagonal (fun i => ((v i - E : ℝ) : ℂ)) =
      (A + diagonal (fun i => (v i : ℂ))) + (-E) • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.smul_apply, sub_eq_add_neg]
      ring
    · simp [hij]
  have h2 : ((A + diagonal (fun i => (v i : ℂ))) + (-E) • (1 : Matrix ι ι ℂ)).IsHermitian :=
    hmat ▸ hvE
  rw [eigenvalueCount_congr hvE h2 hmat, eigenvalueCount_add_smul_one hv (-E) h2 0]
  simp

theorem eigenvalueCount_le_of_posSemidef (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (h : (H' - H).PosSemidef) (E : ℝ) :
    eigenvalueCount hH' E ≤ eigenvalueCount hH E := by
  rw [← finrank_spectralSubspace_Iic hH' E]
  refine finrank_le_eigenvalueCount hH _ fun u hu => ?_
  have h1 := re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic hH' hu
  have h2 : 0 ≤ (star u ⬝ᵥ ((H' - H) *ᵥ u)).re := by
    have := h.re_dotProduct_nonneg u
    simpa [RCLike.re_to_complex] using this
  rw [re_star_dotProduct_sub_mulVec] at h2
  linarith only [h1, h2]

theorem eigenvalueCountLT_le_of_posSemidef (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (h : (H' - H).PosSemidef) (E : ℝ) :
    eigenvalueCountLT hH' E ≤ eigenvalueCountLT hH E := by
  rw [← finrank_spectralSubspace_Iio hH' E]
  refine finrank_le_eigenvalueCountLT hH _ fun u hu hu0 => ?_
  have h1 := re_star_dotProduct_mulVec_lt_of_mem_spectralSubspace_Iio hH' hu hu0
  have h2 : 0 ≤ (star u ⬝ᵥ ((H' - H) *ᵥ u)).re := by
    have := h.re_dotProduct_nonneg u
    simpa [RCLike.re_to_complex] using this
  rw [re_star_dotProduct_sub_mulVec] at h2
  linarith only [h1, h2]

theorem eigenvaluesAsc_le_of_posSemidef (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (h : (H' - H).PosSemidef) (k : Fin (Fintype.card ι)) :
    eigenvaluesAsc hH k ≤ eigenvaluesAsc hH' k :=
  eigenvaluesAsc_le_of_eigenvalueCount_le hH hH' (eigenvalueCount_le_of_posSemidef hH hH' h) k

omit [Fintype ι] in
theorem posSemidef_add_diagonal_sub (A : Matrix ι ι ℂ) {v w : ι → ℝ} (hvw : v ≤ w) :
    ((A + diagonal (fun i => (w i : ℂ))) - (A + diagonal (fun i => (v i : ℂ)))).PosSemidef := by
  have : (A + diagonal (fun i => (w i : ℂ))) - (A + diagonal (fun i => (v i : ℂ))) =
      diagonal (fun i => ((w i - v i : ℝ) : ℂ)) := by
    rw [add_sub_add_left_eq_sub]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [this]
  refine Matrix.PosSemidef.diagonal fun i => ?_
  simpa using hvw i

/-- Raising a diagonal potential pointwise lowers the counts. -/
theorem eigenvalueCount_add_diagonal_antitone (A : Matrix ι ι ℂ) {v w : ι → ℝ} (hvw : v ≤ w)
    (hv : (A + diagonal (fun i => (v i : ℂ))).IsHermitian)
    (hw : (A + diagonal (fun i => (w i : ℂ))).IsHermitian) (E : ℝ) :
    eigenvalueCount hw E ≤ eigenvalueCount hv E :=
  eigenvalueCount_le_of_posSemidef hv hw (posSemidef_add_diagonal_sub A hvw) E

theorem eigenvalueCountLT_add_diagonal_antitone (A : Matrix ι ι ℂ) {v w : ι → ℝ}
    (hvw : v ≤ w) (hv : (A + diagonal (fun i => (v i : ℂ))).IsHermitian)
    (hw : (A + diagonal (fun i => (w i : ℂ))).IsHermitian) (E : ℝ) :
    eigenvalueCountLT hw E ≤ eigenvalueCountLT hv E :=
  eigenvalueCountLT_le_of_posSemidef hv hw (posSemidef_add_diagonal_sub A hvw) E

end FroehlichSpencer.Infra
