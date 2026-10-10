/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.MinMax
public import FroehlichSpencer.Infra.Spectral.Sorted
public import FroehlichSpencer.Infra.Spectral.QuadForm

/-!
# Courant–Fischer, Weyl's inequality and continuity of eigenvalues

For a Hermitian matrix over an arbitrary finite index type we prove the min-max and max-min
characterizations of the `k`-th smallest eigenvalue, Weyl's perturbation inequality in the L²
operator norm (in counting form and for sorted eigenvalues), and continuity of each sorted
eigenvalue along a continuous family of Hermitian matrices.
-/

@[expose] public section

open Matrix Finset
open scoped Matrix.Norms.L2Operator

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}

omit [Fintype ι] [DecidableEq ι] in
/-- A subspace of a finite-dimensional space contains a subspace of any smaller dimension. -/
theorem exists_le_finrank_eq {W : Submodule ℂ (ι → ℂ)} {n : ℕ} (hn : n ≤ Module.finrank ℂ W) :
    ∃ V ≤ W, Module.finrank ℂ V = n := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hn
  refine ⟨Submodule.span ℂ (Set.range fun j => (f j : ι → ℂ)), ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact (f j).2
  · have hli : LinearIndependent ℂ fun j => (f j : ι → ℂ) := hf.map' W.subtype W.ker_subtype
    rw [finrank_span_eq_card hli]
    simp

/-- Courant–Fischer (min-max): the `k`-th smallest eigenvalue is the least `E` such that the
form is `≤ E` on some `(k+1)`-dimensional subspace. -/
theorem isLeast_eigenvaluesAsc (hH : H.IsHermitian) (k : Fin (Fintype.card ι)) :
    IsLeast {E | ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = k + 1 ∧
      ∀ u ∈ V, (star u ⬝ᵥ (H *ᵥ u)).re ≤ E * (star u ⬝ᵥ u).re} (eigenvaluesAsc hH k) := by
  refine ⟨?_, ?_⟩
  · have h := lt_eigenvalueCount_eigenvaluesAsc hH k
    rw [← finrank_spectralSubspace_Iic hH] at h
    obtain ⟨V, hVW, hV⟩ := exists_le_finrank_eq h
    exact ⟨V, hV, fun u hu =>
      re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic hH (hVW hu)⟩
  · rintro E ⟨V, hV, hVE⟩
    have := finrank_le_eigenvalueCount hH V hVE
    exact (eigenvaluesAsc_le_iff hH k E).mpr (by omega)

/-- Courant–Fischer (max-min): the `k`-th smallest eigenvalue is the greatest `E` such that the
form is `≥ E` on some `(card ι - k)`-dimensional subspace. -/
theorem isGreatest_eigenvaluesAsc (hH : H.IsHermitian) (k : Fin (Fintype.card ι)) :
    IsGreatest {E | ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = Fintype.card ι - k ∧
      ∀ u ∈ V, E * (star u ⬝ᵥ u).re ≤ (star u ⬝ᵥ (H *ᵥ u)).re} (eigenvaluesAsc hH k) := by
  refine ⟨?_, ?_⟩
  · have h1 := finrank_spectralSubspace_Ici_add hH (eigenvaluesAsc hH k)
    have h2 := eigenvalueCountLT_eigenvaluesAsc_le hH k
    obtain ⟨V, hVW, hV⟩ := exists_le_finrank_eq
      (W := spectralSubspace hH (Set.Ici (eigenvaluesAsc hH k)))
      (n := Fintype.card ι - k) (by omega)
    exact ⟨V, hV, fun u hu =>
      le_re_star_dotProduct_mulVec_of_mem_spectralSubspace_Ici hH (hVW hu)⟩
  · rintro E ⟨V, hV, hVE⟩
    have := finrank_add_eigenvalueCountLT_le hH V hVE
    have hk := k.2
    exact (le_eigenvaluesAsc_iff hH k E).mpr (by omega)

/-- Counting form of Weyl's inequality. -/
theorem eigenvalueCount_le_eigenvalueCount_add_norm (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) (E : ℝ) :
    eigenvalueCount hH' E ≤ eigenvalueCount hH (E + ‖H - H'‖) := by
  rw [← finrank_spectralSubspace_Iic hH']
  refine finrank_le_eigenvalueCount hH _ fun u hu => ?_
  have h1 := re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic hH' hu
  have h2 := abs_re_star_dotProduct_mulVec_le (H - H') u
  have h3 := re_star_dotProduct_sub_mulVec H H' u
  have h4 := (abs_le.mp h2).2
  linarith only [h1, h3, h4]

theorem eigenvaluesAsc_le_eigenvaluesAsc_add_norm (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (k : Fin (Fintype.card ι)) :
    eigenvaluesAsc hH k ≤ eigenvaluesAsc hH' k + ‖H - H'‖ :=
  eigenvaluesAsc_le_add_of_eigenvalueCount_le hH hH' _
    (eigenvalueCount_le_eigenvalueCount_add_norm hH hH') k

/-- **Weyl's inequality.** -/
theorem abs_eigenvaluesAsc_sub_le (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (k : Fin (Fintype.card ι)) :
    |eigenvaluesAsc hH k - eigenvaluesAsc hH' k| ≤ ‖H - H'‖ := by
  have h1 := eigenvaluesAsc_le_eigenvaluesAsc_add_norm hH hH' k
  have h2 := eigenvaluesAsc_le_eigenvaluesAsc_add_norm hH' hH k
  rw [norm_sub_rev] at h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

/-- Weyl's inequality for Mathlib's `ι`-indexed eigenvalues (the relabelling `ascIndex ι`
does not depend on the matrix). -/
theorem abs_eigenvalues_sub_le (hH : H.IsHermitian) (hH' : H'.IsHermitian) (i : ι) :
    |hH.eigenvalues i - hH'.eigenvalues i| ≤ ‖H - H'‖ := by
  rw [eigenvalues_eq_eigenvaluesAsc_ascIndex hH i, eigenvalues_eq_eigenvaluesAsc_ascIndex hH' i]
  exact abs_eigenvaluesAsc_sub_le hH hH' _

/-- Each sorted eigenvalue is continuous along a continuous family of Hermitian matrices. -/
theorem continuous_eigenvaluesAsc {X : Type*} [TopologicalSpace X] {A : X → Matrix ι ι ℂ}
    (hA : Continuous A) (hAH : ∀ x, (A x).IsHermitian) (k : Fin (Fintype.card ι)) :
    Continuous fun x => eigenvaluesAsc (hAH x) k := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  have hn : Filter.Tendsto (fun x => ‖A x - A x₀‖) (nhds x₀) (nhds 0) := by
    have hc : Continuous fun x => ‖A x - A x₀‖ :=
      (hA.sub (continuous_const (y := A x₀))).norm
    simpa using hc.tendsto x₀
  refine squeeze_zero (fun _ => dist_nonneg) (fun x => ?_) hn
  rw [Real.dist_eq]
  exact abs_eigenvaluesAsc_sub_le (hAH x) (hAH x₀) k

theorem continuous_eigenvalues {X : Type*} [TopologicalSpace X] {A : X → Matrix ι ι ℂ}
    (hA : Continuous A) (hAH : ∀ x, (A x).IsHermitian) (i : ι) :
    Continuous fun x => (hAH x).eigenvalues i := by
  have : (fun x => (hAH x).eigenvalues i) =
      fun x => eigenvaluesAsc (hAH x) (ascIndex ι i) :=
    funext fun x => eigenvalues_eq_eigenvaluesAsc_ascIndex (hAH x) i
  rw [this]
  exact continuous_eigenvaluesAsc hA hAH _

end FroehlichSpencer.Infra
