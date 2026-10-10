/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.MinMax

/-!
# Canonical characterization of the spectral subspace and the eigenvalue count

`spectralSubspace` and `eigenvalueCount` are defined through Mathlib's choice of eigenbasis. Here
we show they are canonical: the spectral subspace is the sum of the eigenspaces of `H` for
eigenvalues in `S`; the count is the number of roots (with multiplicity) of the characteristic
polynomial in `(-∞, E]`, and the sum of the geometric multiplicities of the eigenvalues `≤ E`.
-/

@[expose] public section

open Matrix Finset

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)

theorem mem_eigenspace_toLin'_iff (μ : ℂ) (u : ι → ℂ) :
    u ∈ Module.End.eigenspace (Matrix.toLin' H) μ ↔ H *ᵥ u = μ • u := by
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

/-- The spectral subspace is the sum of the eigenspaces for eigenvalues in `S`; in particular it
does not depend on the choice of eigenbasis. -/
theorem spectralSubspace_eq_iSup_eigenspace (S : Set ℝ) :
    spectralSubspace hH S = ⨆ μ ∈ S, Module.End.eigenspace (Matrix.toLin' H) (μ : ℂ) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    have hle : Module.End.eigenspace (Matrix.toLin' H) (hH.eigenvalues i : ℂ) ≤
        ⨆ μ ∈ S, Module.End.eigenspace (Matrix.toLin' H) (μ : ℂ) :=
      le_iSup₂_of_le (f := fun (μ : ℝ) (_ : μ ∈ S) =>
        Module.End.eigenspace (Matrix.toLin' H) (μ : ℂ)) (hH.eigenvalues i) hi le_rfl
    refine hle ?_
    rw [mem_eigenspace_toLin'_iff, hH.mulVec_eigenvectorBasis,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  · refine iSup₂_le fun μ hμ u hu => ?_
    rw [mem_eigenspace_toLin'_iff] at hu
    rw [mem_spectralSubspace_iff hH]
    intro i hi
    have h1 := inner_eigenvectorBasis_mulVec hH u i
    rw [hu, WithLp.toLp_smul, inner_smul_right] at h1
    have hne : (hH.eigenvalues i : ℂ) ≠ (μ : ℂ) := by
      intro h
      exact hi (by rw [Complex.ofReal_inj.mp h]; exact hμ)
    rw [hH.eigenvectorBasis.repr_apply_apply]
    have h2 : ((hH.eigenvalues i : ℂ) - μ) *
        inner ℂ (hH.eigenvectorBasis i) (WithLp.toLp 2 u) = 0 := by
      rw [sub_mul]; exact sub_eq_zero.mpr h1.symm
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

theorem eigenvalueCount_eq_card_roots (E : ℝ) :
    eigenvalueCount hH E = Multiset.card (H.charpoly.roots.filter fun z => z.re ≤ E) := by
  rw [hH.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map]
  simp [eigenvalueCount, Finset.card_def, Finset.filter_val]

theorem eigenvalueCountLT_eq_card_roots (E : ℝ) :
    eigenvalueCountLT hH E = Multiset.card (H.charpoly.roots.filter fun z => z.re < E) := by
  rw [hH.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map]
  simp [eigenvalueCountLT, Finset.card_def, Finset.filter_val]

/-- Multiplicity of an eigenvalue in Mathlib's list = dimension of the eigenspace. -/
theorem card_eigenvalues_eq_finrank_eigenspace (μ : ℝ) :
    #{i | hH.eigenvalues i = μ} =
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' H) (μ : ℂ)) := by
  classical
  have h := spectralSubspace_eq_iSup_eigenspace hH {μ}
  rw [_root_.iSup_singleton] at h
  rw [← h, finrank_spectralSubspace hH {μ}]
  simp

/-- The count is the sum of the geometric multiplicities of the eigenvalues `≤ E`. -/
theorem eigenvalueCount_eq_sum_finrank_eigenspace (E : ℝ) :
    eigenvalueCount hH E = ∑ μ ∈ (Finset.univ.image hH.eigenvalues).filter (· ≤ E),
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' H) (μ : ℂ)) := by
  classical
  unfold eigenvalueCount
  rw [Finset.card_eq_sum_card_image hH.eigenvalues]
  have himg : (Finset.univ.filter fun i => hH.eigenvalues i ≤ E).image hH.eigenvalues =
      (Finset.univ.image hH.eigenvalues).filter (· ≤ E) := by
    ext μ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, rfl⟩, hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩; exact ⟨i, hi, rfl⟩
  rw [himg]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [← card_eigenvalues_eq_finrank_eigenspace hH]
  have hμE := (Finset.mem_filter.mp hμ).2
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hμE, h⟩

end FroehlichSpencer.Infra
