/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Eigenvalue counting for finite Hermitian matrices

For a Hermitian matrix `H : Matrix ι ι ℂ` over a finite index type, `eigenvalueCount hH E` is the
number of eigenvalues of `H` that are `≤ E`, counted with multiplicity, and `eigenvalueCountLT hH E`
the number that are `< E`.

The spectral subspace `spectralSubspace hH S` is the span of the
eigenvectors whose eigenvalue lies in `S : Set ℝ`.

The counting function is the object `N_Λ(E, v)` of Fröhlich–Spencer (1983), defined after (1.9)
and used in Appendix C (Fröhlich–Spencer (1983)), but nothing here is specific to that
setting: the index type and the matrix are arbitrary.

All definitions use Mathlib's `Matrix.IsHermitian.eigenvalues` and
`Matrix.IsHermitian.eigenvectorBasis`; by proof irrelevance they depend on `H` only
(`eigenvalueCount_congr`).
-/

@[expose] public section

open Matrix Finset

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}

/-- The number of eigenvalues of a Hermitian matrix that are `≤ E`, counted with multiplicity. -/
noncomputable def eigenvalueCount (hH : H.IsHermitian) (E : ℝ) : ℕ :=
  #{i | hH.eigenvalues i ≤ E}

/-- The number of eigenvalues of a Hermitian matrix that are `< E`, counted with multiplicity. -/
noncomputable def eigenvalueCountLT (hH : H.IsHermitian) (E : ℝ) : ℕ :=
  #{i | hH.eigenvalues i < E}

/-- The span of the eigenvectors (from `Matrix.IsHermitian.eigenvectorBasis`) whose eigenvalue
lies in `S`. -/
noncomputable def spectralSubspace (hH : H.IsHermitian) (S : Set ℝ) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ ((fun i => ⇑(hH.eigenvectorBasis i)) '' {i | hH.eigenvalues i ∈ S})

/-- The fixed relabelling `ι ≃ Fin (card ι)` under which Mathlib's `eigenvalues` (indexed by `ι`)
become the increasing list `eigenvaluesAsc`. It depends on `ι` only, not on the matrix. -/
noncomputable def ascIndex (ι : Type*) [Fintype ι] : ι ≃ Fin (Fintype.card ι) :=
  (Fintype.equivOfCardEq (Fintype.card_fin _)).symm.trans Fin.revPerm

/-- The eigenvalues of a Hermitian matrix in increasing order: `eigenvaluesAsc hH k` is the
`(k + 1)`-st smallest eigenvalue, counted with multiplicity. (Mathlib's `eigenvalues₀` lists them
in decreasing order.) -/
noncomputable def eigenvaluesAsc (hH : H.IsHermitian) (k : Fin (Fintype.card ι)) : ℝ :=
  hH.eigenvalues₀ k.rev

theorem eigenvalueCount_congr (hH : H.IsHermitian) (hH' : H'.IsHermitian) (h : H = H') (E : ℝ) :
    eigenvalueCount hH E = eigenvalueCount hH' E := by
  subst h; rfl

theorem eigenvalueCountLT_congr (hH : H.IsHermitian) (hH' : H'.IsHermitian) (h : H = H')
    (E : ℝ) : eigenvalueCountLT hH E = eigenvalueCountLT hH' E := by
  subst h; rfl

theorem spectralSubspace_congr (hH : H.IsHermitian) (hH' : H'.IsHermitian) (h : H = H')
    (S : Set ℝ) : spectralSubspace hH S = spectralSubspace hH' S := by
  subst h; rfl

theorem eigenvaluesAsc_congr (hH : H.IsHermitian) (hH' : H'.IsHermitian) (h : H = H') :
    eigenvaluesAsc hH = eigenvaluesAsc hH' := by
  subst h; rfl

variable (hH : H.IsHermitian)

theorem eigenvalues_eq_eigenvaluesAsc_ascIndex (i : ι) :
    hH.eigenvalues i = eigenvaluesAsc hH (ascIndex ι i) := by
  simp [eigenvaluesAsc, ascIndex, IsHermitian.eigenvalues]

theorem eigenvaluesAsc_monotone : Monotone (eigenvaluesAsc hH) := fun _ _ hkl =>
  hH.eigenvalues₀_antitone (Fin.rev_le_rev.mpr hkl)

theorem eigenvalueCount_le_card (E : ℝ) : eigenvalueCount hH E ≤ Fintype.card ι :=
  card_filter_le _ _

theorem eigenvalueCountLT_le_card (E : ℝ) : eigenvalueCountLT hH E ≤ Fintype.card ι :=
  card_filter_le _ _

theorem eigenvalueCount_mono : Monotone (eigenvalueCount hH) := fun _ _ hEE' =>
  card_le_card fun _ => by simp only [mem_filter, mem_univ, true_and]; exact fun h => h.trans hEE'

theorem eigenvalueCountLT_mono : Monotone (eigenvalueCountLT hH) := fun _ _ hEE' =>
  card_le_card fun _ => by
    simp only [mem_filter, mem_univ, true_and]; exact fun h => h.trans_le hEE'

theorem eigenvalueCountLT_le_eigenvalueCount (E : ℝ) :
    eigenvalueCountLT hH E ≤ eigenvalueCount hH E :=
  card_le_card fun _ => by simp only [mem_filter, mem_univ, true_and]; exact le_of_lt

theorem eigenvalueCount_le_eigenvalueCountLT_of_lt {E E' : ℝ} (hEE' : E < E') :
    eigenvalueCount hH E ≤ eigenvalueCountLT hH E' :=
  card_le_card fun _ => by
    simp only [mem_filter, mem_univ, true_and]; exact fun h => h.trans_lt hEE'

/-- The eigenvalues in `[a, b]` are those counted by `eigenvalueCount hH b` but not by
`eigenvalueCountLT hH a`. -/
theorem eigenvalueCountLT_add_card_Icc {a b : ℝ} (hab : a ≤ b) :
    eigenvalueCountLT hH a + #{i | hH.eigenvalues i ∈ Set.Icc a b} = eigenvalueCount hH b := by
  rw [eigenvalueCountLT, eigenvalueCount, ← card_union_of_disjoint]
  · congr 1
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and, Set.mem_Icc]
    constructor
    · rintro (h | h)
      · exact h.le.trans hab
      · exact h.2
    · intro h
      by_cases hi : hH.eigenvalues i < a
      · exact Or.inl hi
      · exact Or.inr ⟨not_lt.mp hi, h⟩
  · rw [disjoint_filter]
    intro i _ h h'
    exact (not_le.mpr h) h'.1

/-- If some eigenvalue lies in `[a, b]`, then the count jumps by at least one across `[a, b]`. -/
theorem eigenvalueCountLT_lt_eigenvalueCount {a b : ℝ} {i : ι}
    (hi : hH.eigenvalues i ∈ Set.Icc a b) :
    eigenvalueCountLT hH a < eigenvalueCount hH b := by
  rw [← eigenvalueCountLT_add_card_Icc hH (hi.1.trans hi.2)]
  refine Nat.lt_add_of_pos_right (card_pos.mpr ⟨i, ?_⟩)
  simpa using hi

end FroehlichSpencer.Infra
