/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Interlacing
public import FroehlichSpencer.Infra.Spectral.Canonical
public import FroehlichSpencer.Infra.Spectral.Regularity
public import FroehlichSpencer.Infra.Spectral.Sorted
public import FroehlichSpencer.Infra.Resolvent

/-!
# Principal submatrices and Dirichlet decoupling

For a Hermitian matrix `H` on a finite index type and a subset `B`, the principal submatrix
`H_B := H.submatrix (↑) (↑)` satisfies Cauchy interlacing, in counting and sorted form
(`λ_k(H) ≤ λ_k(H_B) ≤ λ_{k + |Bᶜ|}(H)`).

The decoupled matrix `decouple B H` (cross entries
between `B` and `Bᶜ` removed) changes eigenvalue counts by at most the rank of the coupling,
which is at most the number of boundary sites; its spectrum is, with multiplicity, the union
of the spectra of `H_B` and `H_Bᶜ`.

Motivated by the decoupling of blocks by Dirichlet
conditions in Fröhlich–Spencer (1983), (2.10)–(2.13), Fröhlich–Spencer (1983).
-/

@[expose] public section

open Matrix Finset

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
  (B : Set ι) [DecidablePred (· ∈ B)]

/-- Extension by zero from `B` to `ι`. -/
private def extZero (u : B → ℂ) : ι → ℂ := fun i => if h : i ∈ B then u ⟨i, h⟩ else 0

omit [Fintype ι] [DecidableEq ι] in
private theorem extZero_apply_mem (u : B → ℂ) (i : B) : extZero B u i = u i := by
  simp [extZero]

omit [Fintype ι] [DecidableEq ι] in
private theorem extZero_apply_notMem (u : B → ℂ) {i : ι} (hi : i ∉ B) : extZero B u i = 0 := by
  simp [extZero, hi]

/-- Extension by zero as a linear map. -/
private def extZeroLin : (B → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun := extZero B
  map_add' u v := by
    ext i
    by_cases hi : i ∈ B <;> simp [extZero, hi]
  map_smul' c u := by
    ext i
    by_cases hi : i ∈ B <;> simp [extZero, hi]

omit [Fintype ι] [DecidableEq ι] in
private theorem extZeroLin_apply (u : B → ℂ) : extZeroLin B u = extZero B u := rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem extZeroLin_injective : Function.Injective (extZeroLin B (ι := ι)) := by
  intro u v h
  ext i
  have := congrFun h i
  simpa only [extZeroLin_apply, extZero_apply_mem] using this

omit [DecidableEq ι] in
private theorem sum_extZero_mul (u : B → ℂ) (w : ι → ℂ) :
    ∑ i, extZero B u i * w i = ∑ i : B, u i * w i := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ B)]
  have h2 : ∑ i : {x // ¬ x ∈ B}, extZero B u i * w i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [extZero_apply_notMem B u i.2, zero_mul]
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun i _ => by rw [extZero_apply_mem]

omit [DecidableEq ι] in
private theorem star_extZero_dotProduct (u : B → ℂ) (w : ι → ℂ) :
    star (extZero B u) ⬝ᵥ w = star u ⬝ᵥ (fun i : B => w i) := by
  have h : star (extZero B u) = extZero B (star u) := by
    ext i
    by_cases hi : i ∈ B <;> simp [extZero, hi]
  rw [h]
  exact sum_extZero_mul B (star u) w

omit [DecidableEq ι] in
private theorem mulVec_extZero_apply (H : Matrix ι ι ℂ) (u : B → ℂ) (i : B) :
    (H *ᵥ extZero B u) i = ((H.submatrix ((↑) : B → ι) (↑)) *ᵥ u) i := by
  simp only [mulVec, dotProduct, submatrix_apply]
  have := sum_extZero_mul B u (fun j => H i j)
  simp only [mul_comm] at this ⊢
  exact this

omit [DecidableEq ι] in
private theorem re_quad_extZero (H : Matrix ι ι ℂ) (u : B → ℂ) :
    (star (extZero B u) ⬝ᵥ H *ᵥ extZero B u).re =
      (star u ⬝ᵥ (H.submatrix ((↑) : B → ι) (↑)) *ᵥ u).re := by
  rw [star_extZero_dotProduct]
  congr 3
  funext i
  exact mulVec_extZero_apply B H u i

omit [DecidableEq ι] in
private theorem re_norm_extZero (u : B → ℂ) :
    (star (extZero B u) ⬝ᵥ extZero B u).re = (star u ⬝ᵥ u).re := by
  rw [star_extZero_dotProduct]
  congr 3
  funext i
  exact extZero_apply_mem B u i

omit [DecidableEq ι] in
private theorem finrank_comap_extZeroLin_add (V : Submodule ℂ (ι → ℂ)) :
    Module.finrank ℂ V ≤
      Module.finrank ℂ (V.comap (extZeroLin B)) + Fintype.card (Bᶜ : Set ι) := by
  have hinj := extZeroLin_injective B (ι := ι)
  have h1 : Module.finrank ℂ (V.comap (extZeroLin B)) =
      Module.finrank ℂ (V ⊓ LinearMap.range (extZeroLin B) : Submodule ℂ (ι → ℂ)) := by
    rw [inf_comm, ← Submodule.map_comap_eq]
    exact (Submodule.equivMapOfInjective (extZeroLin B) hinj (V.comap (extZeroLin B))).finrank_eq
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq V (LinearMap.range (extZeroLin B))
  have h3 : Module.finrank ℂ (LinearMap.range (extZeroLin B)) = Fintype.card B := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  have h4 : Module.finrank ℂ ↥(V ⊔ LinearMap.range (extZeroLin B)) ≤ Fintype.card ι := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      Submodule.finrank_le (V ⊔ LinearMap.range (extZeroLin B))
  have h5 : Fintype.card B + Fintype.card (Bᶜ : Set ι) = Fintype.card ι := by
    rw [Fintype.card_compl_set]
    have : Fintype.card B ≤ Fintype.card ι := Fintype.card_subtype_le _
    omega
  omega

/-- Cauchy interlacing, counting form: compressing removes eigenvalues below `E`. -/
theorem eigenvalueCount_submatrix_le (hH : H.IsHermitian) (E : ℝ) :
    eigenvalueCount (hH.submatrix ((↑) : B → ι)) E ≤ eigenvalueCount hH E := by
  have hinj := extZeroLin_injective B (ι := ι)
  set V := spectralSubspace (hH.submatrix ((↑) : B → ι)) (Set.Iic E)
  have h1 : Module.finrank ℂ (V.map (extZeroLin B)) = Module.finrank ℂ V :=
    (Submodule.equivMapOfInjective (extZeroLin B) hinj V).finrank_eq.symm
  rw [← finrank_spectralSubspace_Iic, ← h1]
  apply finrank_le_eigenvalueCount hH
  rintro _ ⟨v, hv, rfl⟩
  have := re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic _ hv
  rw [extZeroLin_apply, re_quad_extZero, re_norm_extZero]
  exact this

theorem eigenvalueCount_le_eigenvalueCount_submatrix_add (hH : H.IsHermitian) (E : ℝ) :
    eigenvalueCount hH E ≤
      eigenvalueCount (hH.submatrix ((↑) : B → ι)) E + Fintype.card (Bᶜ : Set ι) := by
  have h1 := finrank_comap_extZeroLin_add B (spectralSubspace hH (Set.Iic E))
  rw [finrank_spectralSubspace_Iic] at h1
  have h2 : Module.finrank ℂ ((spectralSubspace hH (Set.Iic E)).comap (extZeroLin B)) ≤
      eigenvalueCount (hH.submatrix ((↑) : B → ι)) E := by
    apply finrank_le_eigenvalueCount (hH.submatrix ((↑) : B → ι))
    intro v hv
    have := re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic hH
      (Submodule.mem_comap.mp hv)
    rw [extZeroLin_apply, re_quad_extZero, re_norm_extZero] at this
    exact this
  omega

theorem eigenvalueCountLT_submatrix_le (hH : H.IsHermitian) (E : ℝ) :
    eigenvalueCountLT (hH.submatrix ((↑) : B → ι)) E ≤ eigenvalueCountLT hH E := by
  have hinj := extZeroLin_injective B (ι := ι)
  set V := spectralSubspace (hH.submatrix ((↑) : B → ι)) (Set.Iio E)
  have h1 : Module.finrank ℂ (V.map (extZeroLin B)) = Module.finrank ℂ V :=
    (Submodule.equivMapOfInjective (extZeroLin B) hinj V).finrank_eq.symm
  rw [← finrank_spectralSubspace_Iio, ← h1]
  apply finrank_le_eigenvalueCountLT hH
  rintro _ ⟨v, hv, rfl⟩ hne
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hne (map_zero _)
  have := re_star_dotProduct_mulVec_lt_of_mem_spectralSubspace_Iio _ hv hv0
  rw [extZeroLin_apply, re_quad_extZero, re_norm_extZero]
  exact this

theorem eigenvalueCountLT_le_eigenvalueCountLT_submatrix_add (hH : H.IsHermitian) (E : ℝ) :
    eigenvalueCountLT hH E ≤
      eigenvalueCountLT (hH.submatrix ((↑) : B → ι)) E + Fintype.card (Bᶜ : Set ι) := by
  have h1 := finrank_comap_extZeroLin_add B (spectralSubspace hH (Set.Iio E))
  rw [finrank_spectralSubspace_Iio] at h1
  have h2 : Module.finrank ℂ ((spectralSubspace hH (Set.Iio E)).comap (extZeroLin B)) ≤
      eigenvalueCountLT (hH.submatrix ((↑) : B → ι)) E := by
    apply finrank_le_eigenvalueCountLT (hH.submatrix ((↑) : B → ι))
    intro v hv hv0
    have hne : extZeroLin B v ≠ 0 := fun h =>
      hv0 (extZeroLin_injective B (h.trans (map_zero _).symm))
    have := re_star_dotProduct_mulVec_lt_of_mem_spectralSubspace_Iio hH
      (Submodule.mem_comap.mp hv) hne
    rw [extZeroLin_apply, re_quad_extZero, re_norm_extZero] at this
    exact this
  omega

/-- Cauchy interlacing, sorted form. -/
theorem eigenvaluesAsc_le_eigenvaluesAsc_submatrix (hH : H.IsHermitian)
    {k : Fin (Fintype.card ι)} {l : Fin (Fintype.card B)} (hkl : (k : ℕ) ≤ l) :
    eigenvaluesAsc hH k ≤ eigenvaluesAsc (hH.submatrix ((↑) : B → ι)) l := by
  have h1 := lt_eigenvalueCount_eigenvaluesAsc (hH.submatrix ((↑) : B → ι)) l
  have h2 := eigenvalueCount_submatrix_le B hH
    (eigenvaluesAsc (hH.submatrix ((↑) : B → ι)) l)
  rw [eigenvaluesAsc_le_iff]
  omega

theorem eigenvaluesAsc_submatrix_le_eigenvaluesAsc (hH : H.IsHermitian)
    {l : Fin (Fintype.card B)} {k : Fin (Fintype.card ι)}
    (hlk : (l : ℕ) + Fintype.card (Bᶜ : Set ι) ≤ k) :
    eigenvaluesAsc (hH.submatrix ((↑) : B → ι)) l ≤ eigenvaluesAsc hH k := by
  have h1 := lt_eigenvalueCount_eigenvaluesAsc hH k
  have h2 := eigenvalueCount_le_eigenvalueCount_submatrix_add B hH (eigenvaluesAsc hH k)
  rw [eigenvaluesAsc_le_iff]
  omega

omit [Fintype ι] [DecidableEq ι] in
private theorem coupling_apply_eq (H : Matrix ι ι ℂ) (i j : ι) :
    FroehlichSpencer.Matrix.coupling B H i j = if (i ∈ B ↔ j ∉ B) then H i j else 0 := by
  by_cases hi : i ∈ B <;> by_cases hj : j ∈ B <;>
    simp [FroehlichSpencer.Matrix.coupling_apply, FroehlichSpencer.Matrix.decouple_apply, hi, hj]

open Classical in
/-- The coupling has rank at most the number of boundary sites. -/
theorem rank_coupling_le (H : Matrix ι ι ℂ) :
    (FroehlichSpencer.Matrix.coupling B H).rank ≤ #{i | ∃ j, (i ∈ B ↔ j ∉ B) ∧ H i j ≠ 0} := by
  set S : Finset ι := {i | ∃ j, (i ∈ B ↔ j ∉ B) ∧ H i j ≠ 0} with hS
  set d : ι → ℂ := fun i => if i ∈ S then 1 else 0 with hd
  have h1 : FroehlichSpencer.Matrix.coupling B H =
      Matrix.diagonal d * FroehlichSpencer.Matrix.coupling B H := by
    ext i j
    rw [Matrix.diagonal_mul, coupling_apply_eq]
    by_cases hij : (i ∈ B ↔ j ∉ B)
    · have hiS : i ∈ S ∨ H i j = 0 := by
        by_cases h0 : H i j = 0
        · exact Or.inr h0
        · refine Or.inl ?_
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, hij, h0⟩
      rcases hiS with hiS | h0
      · simp [hd, hiS]
      · simp [hd, h0]
    · simp [hij]
  calc (FroehlichSpencer.Matrix.coupling B H).rank
      = (Matrix.diagonal d * FroehlichSpencer.Matrix.coupling B H).rank := by rw [← h1]
    _ ≤ (Matrix.diagonal d).rank := Matrix.rank_mul_le_left _ _
    _ = Fintype.card {i // d i ≠ 0} := _root_.Matrix.rank_diagonal d
    _ = #S := by
      rw [Fintype.card_subtype]
      congr 1
      ext i
      simp [hd]

open Classical in
/-- … and at most twice the number of coupled pairs. -/
theorem rank_coupling_le_two_mul (hH : H.IsHermitian) :
    (FroehlichSpencer.Matrix.coupling B H).rank ≤
      2 * #{p : ι × ι | p.1 ∈ B ∧ p.2 ∉ B ∧ H p.1 p.2 ≠ 0} := by
  set P : Finset (ι × ι) := {p | p.1 ∈ B ∧ p.2 ∉ B ∧ H p.1 p.2 ≠ 0} with hP
  have hsub : ({i | ∃ j, (i ∈ B ↔ j ∉ B) ∧ H i j ≠ 0} : Finset ι) ⊆
      P.image Prod.fst ∪ P.image Prod.snd := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hij, hne⟩ := hi
    simp only [Finset.mem_union, Finset.mem_image, hP, Finset.mem_filter, Finset.mem_univ,
      true_and, Prod.exists, exists_and_right, exists_eq_right]
    by_cases hi : i ∈ B
    · exact Or.inl ⟨j, hi, hij.mp hi, hne⟩
    · have hj : j ∈ B := by
        by_contra hj
        exact hi (hij.mpr hj)
      refine Or.inr ⟨j, hj, hi, ?_⟩
      rw [← hH.apply j i]
      exact star_ne_zero.mpr hne
  calc (FroehlichSpencer.Matrix.coupling B H).rank
      ≤ #{i | ∃ j, (i ∈ B ↔ j ∉ B) ∧ H i j ≠ 0} := rank_coupling_le B H
    _ ≤ #(P.image Prod.fst ∪ P.image Prod.snd) := Finset.card_le_card hsub
    _ ≤ #(P.image Prod.fst) + #(P.image Prod.snd) := Finset.card_union_le _ _
    _ ≤ #P + #P := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * #P := by ring

theorem eigenvalueCount_decouple_le (hH : H.IsHermitian) (E : ℝ) :
    eigenvalueCount (FroehlichSpencer.Matrix.decouple_isHermitian B hH) E ≤
        eigenvalueCount hH E + (FroehlichSpencer.Matrix.coupling B H).rank ∧
      eigenvalueCount hH E ≤
        eigenvalueCount (FroehlichSpencer.Matrix.decouple_isHermitian B hH) E +
          (FroehlichSpencer.Matrix.coupling B H).rank := by
  have hr : (FroehlichSpencer.Matrix.decouple B H - H).rank ≤
      (FroehlichSpencer.Matrix.coupling B H).rank :=
    (rank_sub_comm _ _).le
  exact (eigenvalueCount_le_add_of_rank_le hH (FroehlichSpencer.Matrix.decouple_isHermitian B hH)
    hr E).symm

private theorem charpoly_decouple (H : Matrix ι ι ℂ) :
    (FroehlichSpencer.Matrix.decouple B H).charpoly =
      (H.submatrix ((↑) : B → ι) (↑)).charpoly *
        (H.submatrix ((↑) : (Bᶜ : Set ι) → ι) (↑)).charpoly := by
  rw [FroehlichSpencer.Matrix.decouple_eq_reindex_fromBlocks, Matrix.charpoly_reindex,
    Matrix.charpoly_fromBlocks_zero₁₂]

/-- The decoupled spectrum is the union, with multiplicity, of the two block spectra. -/
theorem eigenvalues_multiset_decouple (hH : H.IsHermitian) :
    Multiset.map (FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues
        Finset.univ.val =
      Multiset.map (hH.submatrix ((↑) : B → ι)).eigenvalues Finset.univ.val +
        Multiset.map (hH.submatrix ((↑) : (Bᶜ : Set ι) → ι)).eigenvalues Finset.univ.val := by
  have hD := FroehlichSpencer.Matrix.decouple_isHermitian B hH
  have hA := hH.submatrix ((↑) : B → ι)
  have hC := hH.submatrix ((↑) : (Bᶜ : Set ι) → ι)
  have hmonoA : (H.submatrix ((↑) : B → ι) (↑)).charpoly.Monic := Matrix.charpoly_monic _
  have hmonoC : (H.submatrix ((↑) : (Bᶜ : Set ι) → ι) (↑)).charpoly.Monic :=
    Matrix.charpoly_monic _
  have hroots := Polynomial.roots_mul (hmonoA.mul hmonoC).ne_zero
  rw [← charpoly_decouple, hD.roots_charpoly_eq_eigenvalues, hA.roots_charpoly_eq_eigenvalues,
    hC.roots_charpoly_eq_eigenvalues] at hroots
  apply Multiset.map_injective Complex.ofReal_injective
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  exact hroots

private theorem eigenvalueCount_eq_card_filter_map {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ ℂ} (hA : A.IsHermitian) (E : ℝ) :
    eigenvalueCount hA E =
      Multiset.card (Multiset.filter (· ≤ E) (Multiset.map hA.eigenvalues Finset.univ.val)) := by
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

private theorem eigenvalueCountLT_eq_card_filter_map {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ ℂ} (hA : A.IsHermitian) (E : ℝ) :
    eigenvalueCountLT hA E =
      Multiset.card (Multiset.filter (· < E) (Multiset.map hA.eigenvalues Finset.univ.val)) := by
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

theorem eigenvalueCount_decouple (hH : H.IsHermitian) (E : ℝ) :
    eigenvalueCount (FroehlichSpencer.Matrix.decouple_isHermitian B hH) E =
      eigenvalueCount (hH.submatrix ((↑) : B → ι)) E +
        eigenvalueCount (hH.submatrix ((↑) : (Bᶜ : Set ι) → ι)) E := by
  rw [eigenvalueCount_eq_card_filter_map, eigenvalueCount_eq_card_filter_map,
    eigenvalueCount_eq_card_filter_map, eigenvalues_multiset_decouple B hH, Multiset.filter_add,
    Multiset.card_add]

theorem eigenvalueCountLT_decouple (hH : H.IsHermitian) (E : ℝ) :
    eigenvalueCountLT (FroehlichSpencer.Matrix.decouple_isHermitian B hH) E =
      eigenvalueCountLT (hH.submatrix ((↑) : B → ι)) E +
        eigenvalueCountLT (hH.submatrix ((↑) : (Bᶜ : Set ι) → ι)) E := by
  rw [eigenvalueCountLT_eq_card_filter_map, eigenvalueCountLT_eq_card_filter_map,
    eigenvalueCountLT_eq_card_filter_map, eigenvalues_multiset_decouple B hH, Multiset.filter_add,
    Multiset.card_add]

theorem forall_eigenvalues_decouple_iff (hH : H.IsHermitian) (p : ℝ → Prop) :
    (∀ i, p ((FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues i)) ↔
      (∀ i, p ((hH.submatrix ((↑) : B → ι)).eigenvalues i)) ∧
        ∀ i, p ((hH.submatrix ((↑) : (Bᶜ : Set ι) → ι)).eigenvalues i) := by
  have key : ∀ {κ : Type _} [Fintype κ] (f : κ → ℝ),
      (∀ i, p (f i)) ↔ ∀ x ∈ Multiset.map f Finset.univ.val, p x := by
    intro κ _ f
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
      forall_exists_index, forall_apply_eq_imp_iff]
  rw [key, key, key, eigenvalues_multiset_decouple B hH]
  simp only [Multiset.mem_add]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · exact h2 x hx

/-- The spectral distance of the decoupled matrix is the minimum of the block ones. -/
theorem inf'_abs_eigenvalues_decouple_sub [Nonempty ι] [Nonempty B] [Nonempty (Bᶜ : Set ι)]
    (hH : H.IsHermitian) (E : ℝ) :
    Finset.univ.inf' Finset.univ_nonempty
        (fun i => |(FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues i - E|) =
      min (Finset.univ.inf' Finset.univ_nonempty
          (fun i => |(hH.submatrix ((↑) : B → ι)).eigenvalues i - E|))
        (Finset.univ.inf' Finset.univ_nonempty
          (fun i => |(hH.submatrix ((↑) : (Bᶜ : Set ι) → ι)).eigenvalues i - E|)) := by
  have hmem : ∀ i, (∃ j, (hH.submatrix ((↑) : B → ι)).eigenvalues j =
        (FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues i) ∨
      ∃ j, (hH.submatrix ((↑) : (Bᶜ : Set ι) → ι)).eigenvalues j =
        (FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues i := by
    intro i
    have : (FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues i ∈
        Multiset.map (FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues
          Finset.univ.val := Multiset.mem_map_of_mem _ (Finset.mem_univ _)
    rw [eigenvalues_multiset_decouple B hH, Multiset.mem_add] at this
    simpa only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] using this
  have hmemB : ∀ j, ∃ i, (FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues i =
      (hH.submatrix ((↑) : B → ι)).eigenvalues j := by
    intro j
    have : (hH.submatrix ((↑) : B → ι)).eigenvalues j ∈
        Multiset.map (FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues
          Finset.univ.val := by
      rw [eigenvalues_multiset_decouple B hH, Multiset.mem_add]
      exact Or.inl (Multiset.mem_map_of_mem _ (Finset.mem_univ _))
    simpa only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] using this
  have hmemC : ∀ j, ∃ i, (FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues i =
      (hH.submatrix ((↑) : (Bᶜ : Set ι) → ι)).eigenvalues j := by
    intro j
    have : (hH.submatrix ((↑) : (Bᶜ : Set ι) → ι)).eigenvalues j ∈
        Multiset.map (FroehlichSpencer.Matrix.decouple_isHermitian B hH).eigenvalues
          Finset.univ.val := by
      rw [eigenvalues_multiset_decouple B hH, Multiset.mem_add]
      exact Or.inr (Multiset.mem_map_of_mem _ (Finset.mem_univ _))
    simpa only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] using this
  apply le_antisymm
  · refine le_min ?_ ?_
    · rw [Finset.le_inf'_iff]
      intro j _
      obtain ⟨i, hi⟩ := hmemB j
      refine (Finset.inf'_le _ (Finset.mem_univ i)).trans ?_
      rw [hi]
    · rw [Finset.le_inf'_iff]
      intro j _
      obtain ⟨i, hi⟩ := hmemC j
      refine (Finset.inf'_le _ (Finset.mem_univ i)).trans ?_
      rw [hi]
  · rw [Finset.le_inf'_iff]
    intro i _
    rcases hmem i with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine min_le_of_left_le ((Finset.inf'_le _ (Finset.mem_univ j)).trans ?_)
      rw [hj]
    · refine min_le_of_right_le ((Finset.inf'_le _ (Finset.mem_univ j)).trans ?_)
      rw [hj]

end FroehlichSpencer.Infra
