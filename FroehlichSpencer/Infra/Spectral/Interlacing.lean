/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Monotonicity

/-!
# Finite-rank interlacing of eigenvalue counts

A perturbation of rank `≤ r` changes the eigenvalue counts by at most `r`; for a one-site
diagonal change the counts differ by at most one and move monotonically (Fröhlich–Spencer (1983),
Appendix C, Fröhlich–Spencer (1983) line 1821: "the eigenvalues … are interlaced, hence
`0 ≤ δ_j N ≤ 1`", with `δ_j N` defined in (C.3)).

`eigenvalueCount_update_le` is that statement for
an arbitrary matrix plus a diagonal potential.
-/

@[expose] public section

open Matrix Finset ComplexOrder

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}

omit [DecidableEq ι] in
theorem finrank_ker_mulVecLin_add_rank (A : Matrix ι ι ℂ) :
    Module.finrank ℂ (LinearMap.ker A.mulVecLin) + A.rank = Fintype.card ι := by
  have := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at this
  unfold Matrix.rank
  omega

theorem eigenvalueCount_le_add_rank (hH : H.IsHermitian) (hH' : H'.IsHermitian) (E : ℝ) :
    eigenvalueCount hH E ≤ eigenvalueCount hH' E + (H' - H).rank := by
  set K := LinearMap.ker (H' - H).mulVecLin with hK
  have h1 : Module.finrank ℂ K + (H' - H).rank = Fintype.card ι :=
    finrank_ker_mulVecLin_add_rank (H' - H)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (spectralSubspace hH (Set.Iic E)) K
  have h3 : Module.finrank ℂ ↥(spectralSubspace hH (Set.Iic E) ⊔ K) ≤ Fintype.card ι := by
    simpa using Submodule.finrank_le (spectralSubspace hH (Set.Iic E) ⊔ K)
  have h4 := finrank_spectralSubspace_Iic hH E
  have h5 : Module.finrank ℂ ↥(spectralSubspace hH (Set.Iic E) ⊓ K) ≤ eigenvalueCount hH' E := by
    refine finrank_le_eigenvalueCount hH' _ fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := hu
    have hk : (H' - H) *ᵥ u = 0 := hu2
    rw [sub_mulVec, sub_eq_zero] at hk
    rw [hk]
    exact re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic hH hu1
  omega

theorem eigenvalueCountLT_le_add_rank (hH : H.IsHermitian) (hH' : H'.IsHermitian) (E : ℝ) :
    eigenvalueCountLT hH E ≤ eigenvalueCountLT hH' E + (H' - H).rank := by
  set K := LinearMap.ker (H' - H).mulVecLin with hK
  have h1 : Module.finrank ℂ K + (H' - H).rank = Fintype.card ι :=
    finrank_ker_mulVecLin_add_rank (H' - H)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (spectralSubspace hH (Set.Iio E)) K
  have h3 : Module.finrank ℂ ↥(spectralSubspace hH (Set.Iio E) ⊔ K) ≤ Fintype.card ι := by
    simpa using Submodule.finrank_le (spectralSubspace hH (Set.Iio E) ⊔ K)
  have h4 := finrank_spectralSubspace_Iio hH E
  have h5 : Module.finrank ℂ ↥(spectralSubspace hH (Set.Iio E) ⊓ K) ≤ eigenvalueCountLT hH' E := by
    refine finrank_le_eigenvalueCountLT hH' _ fun u hu hu0 => ?_
    obtain ⟨hu1, hu2⟩ := hu
    have hk : (H' - H) *ᵥ u = 0 := hu2
    rw [sub_mulVec, sub_eq_zero] at hk
    rw [hk]
    exact re_star_dotProduct_mulVec_lt_of_mem_spectralSubspace_Iio hH hu1 hu0
  omega

theorem rank_sub_comm (A B : Matrix ι ι ℂ) : (A - B).rank = (B - A).rank := by
  rw [← neg_sub]
  unfold Matrix.rank
  have : (-(B - A)).mulVecLin = -(B - A).mulVecLin := by
    ext u i
    simp
  rw [this, LinearMap.range_neg]

theorem eigenvalueCount_le_add_of_rank_le (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    {r : ℕ} (hr : (H' - H).rank ≤ r) (E : ℝ) :
    eigenvalueCount hH E ≤ eigenvalueCount hH' E + r ∧
      eigenvalueCount hH' E ≤ eigenvalueCount hH E + r := by
  have h1 := eigenvalueCount_le_add_rank hH hH' E
  have h2 := eigenvalueCount_le_add_rank hH' hH E
  rw [rank_sub_comm] at h2
  omega

theorem eigenvalueCountLT_le_add_of_rank_le (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    {r : ℕ} (hr : (H' - H).rank ≤ r) (E : ℝ) :
    eigenvalueCountLT hH E ≤ eigenvalueCountLT hH' E + r ∧
      eigenvalueCountLT hH' E ≤ eigenvalueCountLT hH E + r := by
  have h1 := eigenvalueCountLT_le_add_rank hH hH' E
  have h2 := eigenvalueCountLT_le_add_rank hH' hH E
  rw [rank_sub_comm] at h2
  omega

/-- Interlacing of sorted eigenvalues under a perturbation of rank `≤ r`. -/
theorem eigenvaluesAsc_le_of_rank_le (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    {r : ℕ} (hr : (H' - H).rank ≤ r) {k l : Fin (Fintype.card ι)} (hkl : (k : ℕ) + r ≤ l) :
    eigenvaluesAsc hH' k ≤ eigenvaluesAsc hH l := by
  rw [eigenvaluesAsc_le_iff]
  have h1 := lt_eigenvalueCount_eigenvaluesAsc hH l
  have h2 := (eigenvalueCount_le_add_of_rank_le hH hH' hr (eigenvaluesAsc hH l)).1
  omega

theorem rank_smul_single_le_one (j : ι) (t : ℝ) :
    (t • Matrix.single j j (1 : ℂ) : Matrix ι ι ℂ).rank ≤ 1 := by
  have : (t • Matrix.single j j (1 : ℂ) : Matrix ι ι ℂ) =
      vecMulVec (Pi.single j (t : ℂ)) (Pi.single j (1 : ℂ)) := by
    ext a b
    simp only [Matrix.smul_apply, Matrix.single_apply, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp_all [Complex.real_smul]
  rw [this]
  exact (Matrix.rank_vecMulVec_le _ _).trans (by simp)

theorem eigenvalueCount_le_add_smul_single_add_one (hH : H.IsHermitian) (j : ι) (t : ℝ)
    (hHt : (H + t • Matrix.single j j (1 : ℂ)).IsHermitian) (E : ℝ) :
    eigenvalueCount hH E ≤ eigenvalueCount hHt E + 1 ∧
      eigenvalueCount hHt E ≤ eigenvalueCount hH E + 1 :=
  eigenvalueCount_le_add_of_rank_le hH hHt
    (by rw [add_sub_cancel_left]; exact rank_smul_single_le_one j t) E

omit [Fintype ι] in
theorem posSemidef_smul_single {t : ℝ} (ht : 0 ≤ t) (j : ι) :
    (t • Matrix.single j j (1 : ℂ) : Matrix ι ι ℂ).PosSemidef := by
  have : (t • Matrix.single j j (1 : ℂ) : Matrix ι ι ℂ) =
      diagonal (fun i => ((if i = j then t else 0 : ℝ) : ℂ)) := by
    ext a b
    simp only [Matrix.smul_apply, Matrix.single_apply, diagonal_apply]
    split_ifs <;> simp_all [Complex.real_smul]
    all_goals grind
  rw [this]
  refine Matrix.PosSemidef.diagonal fun i => ?_
  by_cases hi : i = j <;> simp [hi, ht]

theorem eigenvalueCount_add_smul_single_le (hH : H.IsHermitian) (j : ι) {t : ℝ} (ht : 0 ≤ t)
    (hHt : (H + t • Matrix.single j j (1 : ℂ)).IsHermitian) (E : ℝ) :
    eigenvalueCount hHt E ≤ eigenvalueCount hH E ∧
      eigenvalueCount hH E ≤ eigenvalueCount hHt E + 1 := by
  refine ⟨eigenvalueCount_le_of_posSemidef hH hHt ?_ E,
    (eigenvalueCount_le_add_smul_single_add_one hH j t hHt E).1⟩
  rw [add_sub_cancel_left]
  exact posSemidef_smul_single ht j

omit [Fintype ι] in
theorem diagonal_update_eq_add (A : Matrix ι ι ℂ) (v : ι → ℝ) (j : ι) (s t : ℝ) :
    A + diagonal (fun i => (Function.update v j t i : ℂ)) =
      (A + diagonal (fun i => (Function.update v j s i : ℂ))) +
        (t - s) • Matrix.single j j (1 : ℂ) := by
  rw [add_assoc]
  congr 1
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, diagonal_apply,
    Function.update_apply]
  split_ifs
  · simp only [Complex.real_smul, mul_one]; push_cast; ring
  · exfalso; grind
  · exfalso; grind
  · simp
  · exfalso; grind
  · simp

theorem eigenvalueCount_update_le (A : Matrix ι ι ℂ) (v : ι → ℝ) (j : ι) {s t : ℝ} (hst : s ≤ t)
    (hs : (A + diagonal (fun i => (Function.update v j s i : ℂ))).IsHermitian)
    (ht : (A + diagonal (fun i => (Function.update v j t i : ℂ))).IsHermitian) (E : ℝ) :
    eigenvalueCount ht E ≤ eigenvalueCount hs E ∧
      eigenvalueCount hs E ≤ eigenvalueCount ht E + 1 := by
  have heq := diagonal_update_eq_add A v j s t
  have ht' : ((A + diagonal (fun i => (Function.update v j s i : ℂ))) +
      (t - s) • Matrix.single j j (1 : ℂ)).IsHermitian := heq ▸ ht
  rw [eigenvalueCount_congr ht ht' heq E]
  exact eigenvalueCount_add_smul_single_le hs j (sub_nonneg.mpr hst) ht' E

theorem eigenvalueCountLT_update_le (A : Matrix ι ι ℂ) (v : ι → ℝ) (j : ι) {s t : ℝ}
    (hst : s ≤ t)
    (hs : (A + diagonal (fun i => (Function.update v j s i : ℂ))).IsHermitian)
    (ht : (A + diagonal (fun i => (Function.update v j t i : ℂ))).IsHermitian) (E : ℝ) :
    eigenvalueCountLT ht E ≤ eigenvalueCountLT hs E ∧
      eigenvalueCountLT hs E ≤ eigenvalueCountLT ht E + 1 := by
  have heq := diagonal_update_eq_add A v j s t
  have ht' : ((A + diagonal (fun i => (Function.update v j s i : ℂ))) +
      (t - s) • Matrix.single j j (1 : ℂ)).IsHermitian := heq ▸ ht
  rw [eigenvalueCountLT_congr ht ht' heq E]
  refine ⟨eigenvalueCountLT_le_of_posSemidef hs ht' ?_ E,
    (eigenvalueCountLT_le_add_of_rank_le hs ht' (r := 1) ?_ E).1⟩
  · rw [add_sub_cancel_left]
    exact posSemidef_smul_single (sub_nonneg.mpr hst) j
  · rw [add_sub_cancel_left]
    exact rank_smul_single_le_one j _

end FroehlichSpencer.Infra
