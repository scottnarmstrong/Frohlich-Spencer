/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Count

/-!
# Spectral subspaces and the min-max characterization of eigenvalue counts

For a Hermitian matrix `H` over a finite index type we expand the quadratic form
`u ↦ (star u ⬝ᵥ (H *ᵥ u)).re` in the eigenbasis, identify the dimension of the spectral subspace
`spectralSubspace hH S` with the number of eigenvalues in `S`, and deduce the Courant–Fischer
min-max principle in counting form: `eigenvalueCount hH E` is the largest dimension of a subspace on
which the form is `≤ E` times the squared norm (and similarly for the strict count).

The counting function is the one of Fröhlich–Spencer (1983) (Fröhlich–Spencer (1983)),
but nothing here is specific to that setting.
-/

@[expose] public section

open Matrix Finset

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)

theorem inner_eigenvectorBasis_mulVec (u : ι → ℂ) (i : ι) :
    inner ℂ (hH.eigenvectorBasis i) (WithLp.toLp 2 (H *ᵥ u)) =
      (hH.eigenvalues i : ℂ) * inner ℂ (hH.eigenvectorBasis i) (WithLp.toLp 2 u) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm, dotProduct_comm (WithLp.ofLp (WithLp.toLp 2 u)), WithLp.ofLp_toLp,
    WithLp.ofLp_toLp, Matrix.dotProduct_mulVec]
  have h1 : star (WithLp.ofLp (hH.eigenvectorBasis i)) ᵥ* H =
      (hH.eigenvalues i : ℂ) • star (WithLp.ofLp (hH.eigenvectorBasis i)) := by
    have := congrArg star (hH.mulVec_eigenvectorBasis i)
    rw [Matrix.star_mulVec, hH.eq] at this
    rw [this]
    simp [star_smul]
  rw [h1, smul_dotProduct]
  rfl

theorem star_dotProduct_mulVec_eq_sum_repr (u : ι → ℂ) :
    star u ⬝ᵥ (H *ᵥ u) =
      ∑ i, (hH.eigenvalues i : ℂ) * (‖hH.eigenvectorBasis.repr (WithLp.toLp 2 u) i‖ ^ 2 : ℝ) := by
  have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 u) (WithLp.toLp 2 (H *ᵥ u))
  have h2 : inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 (H *ᵥ u)) = star u ⬝ᵥ (H *ᵥ u) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [← h2, ← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvectorBasis_mulVec hH, hH.eigenvectorBasis.repr_apply_apply, ← inner_conj_symm,
    Complex.ofReal_pow, ← Complex.conj_mul' ]
  simp only [starRingEnd_apply]
  ring

theorem star_dotProduct_self_eq_sum_repr (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ i, ‖hH.eigenvectorBasis.repr (WithLp.toLp 2 u) i‖ ^ 2 : ℝ) : ℂ) := by
  have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 u) (WithLp.toLp 2 u)
  have h2 : inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 u) = star u ⬝ᵥ u := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [← h2, ← h, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hH.eigenvectorBasis.repr_apply_apply, ← inner_conj_symm, Complex.ofReal_pow,
    ← Complex.conj_mul']

/-- Spectral expansion of the quadratic form. -/
theorem re_star_dotProduct_mulVec_eq_sum_repr (u : ι → ℂ) :
    (star u ⬝ᵥ (H *ᵥ u)).re =
      ∑ i, hH.eigenvalues i * ‖hH.eigenvectorBasis.repr (WithLp.toLp 2 u) i‖ ^ 2 := by
  rw [star_dotProduct_mulVec_eq_sum_repr hH, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

theorem re_star_dotProduct_self_eq_sum_repr (u : ι → ℂ) :
    (star u ⬝ᵥ u).re = ∑ i, ‖hH.eigenvectorBasis.repr (WithLp.toLp 2 u) i‖ ^ 2 := by
  rw [star_dotProduct_self_eq_sum_repr hH, Complex.ofReal_re]

/-- Membership in a spectral subspace: the coefficients outside `S` vanish. -/
theorem mem_spectralSubspace_iff (S : Set ℝ) (u : ι → ℂ) :
    u ∈ spectralSubspace hH S ↔
      ∀ i, hH.eigenvalues i ∉ S → hH.eigenvectorBasis.repr (WithLp.toLp 2 u) i = 0 := by
  let K : Submodule ℂ (ι → ℂ) :=
    { carrier := {u | ∀ i, hH.eigenvalues i ∉ S →
        hH.eigenvectorBasis.repr (WithLp.toLp 2 u) i = 0}
      add_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
      zero_mem' := fun i _ => by simp
      smul_mem' := fun c a ha i hi => by simp [ha i hi] }
  constructor
  · intro hu
    have hle : spectralSubspace hH S ≤ K := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, hj, rfl⟩ i hi
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have : WithLp.toLp 2 (⇑(hH.eigenvectorBasis j)) = hH.eigenvectorBasis j := rfl
      show hH.eigenvectorBasis.repr (WithLp.toLp 2 (⇑(hH.eigenvectorBasis j))) i = 0
      rw [this, OrthonormalBasis.repr_self]
      simp [hij]
    exact hle hu
  · intro hu
    have hsum :
        u = ∑ i, hH.eigenvectorBasis.repr (WithLp.toLp 2 u) i • ⇑(hH.eigenvectorBasis i) := by
      have := congrArg WithLp.ofLp (hH.eigenvectorBasis.sum_repr (WithLp.toLp 2 u))
      simpa using this.symm
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : hH.eigenvalues i ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · have := hu i hi
      simp [this]

theorem finrank_spectralSubspace (S : Set ℝ) [DecidablePred (· ∈ S)] :
    Module.finrank ℂ (spectralSubspace hH S) = #{i | hH.eigenvalues i ∈ S} := by
  let e : EuclideanSpace ℂ ι →ₗ[ℂ] (ι → ℂ) := (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
  have hli : LinearIndependent ℂ (fun j : {i // hH.eigenvalues i ∈ S} =>
      (⇑(hH.eigenvectorBasis j) : ι → ℂ)) := by
    have h1 := hH.eigenvectorBasis.orthonormal.linearIndependent.comp
      (Subtype.val : {i // hH.eigenvalues i ∈ S} → ι) Subtype.val_injective
    exact h1.map' e (LinearEquiv.ker _)
  have hspan : spectralSubspace hH S = Submodule.span ℂ (Set.range
      (fun j : {i // hH.eigenvalues i ∈ S} => (⇑(hH.eigenvectorBasis j) : ι → ℂ))) := by
    unfold spectralSubspace
    rw [Set.image_eq_range]
    rfl
  rw [hspan, finrank_span_eq_card hli, Fintype.card_subtype]

theorem finrank_spectralSubspace_Iic (E : ℝ) :
    Module.finrank ℂ (spectralSubspace hH (Set.Iic E)) = eigenvalueCount hH E := by
  classical
  rw [finrank_spectralSubspace]
  rfl

theorem finrank_spectralSubspace_Iio (E : ℝ) :
    Module.finrank ℂ (spectralSubspace hH (Set.Iio E)) = eigenvalueCountLT hH E := by
  classical
  rw [finrank_spectralSubspace]
  rfl

theorem exists_repr_ne_zero {u : ι → ℂ} (hu0 : u ≠ 0) :
    ∃ i, hH.eigenvectorBasis.repr (WithLp.toLp 2 u) i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hu0
  have : hH.eigenvectorBasis.repr (WithLp.toLp 2 u) = 0 := by
    ext i
    simpa using hcon i
  have h2 := (hH.eigenvectorBasis.repr.map_eq_zero_iff).mp this
  simpa using congrArg WithLp.ofLp h2

theorem re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic {E : ℝ} {u : ι → ℂ}
    (hu : u ∈ spectralSubspace hH (Set.Iic E)) :
    (star u ⬝ᵥ (H *ᵥ u)).re ≤ E * (star u ⬝ᵥ u).re := by
  rw [re_star_dotProduct_mulVec_eq_sum_repr hH, re_star_dotProduct_self_eq_sum_repr hH,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : hH.eigenvalues i ≤ E
  · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  · have := (mem_spectralSubspace_iff hH _ u).mp hu i hi
    simp [this]

theorem re_star_dotProduct_mulVec_lt_of_mem_spectralSubspace_Iio {E : ℝ} {u : ι → ℂ}
    (hu : u ∈ spectralSubspace hH (Set.Iio E)) (hu0 : u ≠ 0) :
    (star u ⬝ᵥ (H *ᵥ u)).re < E * (star u ⬝ᵥ u).re := by
  rw [re_star_dotProduct_mulVec_eq_sum_repr hH, re_star_dotProduct_self_eq_sum_repr hH,
    Finset.mul_sum]
  obtain ⟨j, hj⟩ := exists_repr_ne_zero hH hu0
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · by_cases hi : hH.eigenvalues i < E
    · exact mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)
    · have := (mem_spectralSubspace_iff hH _ u).mp hu i hi
      simp [this]
  · have hjE : hH.eigenvalues j < E := by
      by_contra h
      exact hj ((mem_spectralSubspace_iff hH _ u).mp hu j h)
    exact mul_lt_mul_of_pos_right hjE (by positivity)

theorem le_re_star_dotProduct_mulVec_of_mem_spectralSubspace_Ici {E : ℝ} {u : ι → ℂ}
    (hu : u ∈ spectralSubspace hH (Set.Ici E)) :
    E * (star u ⬝ᵥ u).re ≤ (star u ⬝ᵥ (H *ᵥ u)).re := by
  rw [re_star_dotProduct_mulVec_eq_sum_repr hH, re_star_dotProduct_self_eq_sum_repr hH,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : E ≤ hH.eigenvalues i
  · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  · have := (mem_spectralSubspace_iff hH _ u).mp hu i hi
    simp [this]

theorem lt_re_star_dotProduct_mulVec_of_mem_spectralSubspace_Ioi {E : ℝ} {u : ι → ℂ}
    (hu : u ∈ spectralSubspace hH (Set.Ioi E)) (hu0 : u ≠ 0) :
    E * (star u ⬝ᵥ u).re < (star u ⬝ᵥ (H *ᵥ u)).re := by
  rw [re_star_dotProduct_mulVec_eq_sum_repr hH, re_star_dotProduct_self_eq_sum_repr hH,
    Finset.mul_sum]
  obtain ⟨j, hj⟩ := exists_repr_ne_zero hH hu0
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · by_cases hi : E < hH.eigenvalues i
    · exact mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)
    · have := (mem_spectralSubspace_iff hH _ u).mp hu i hi
      simp [this]
  · have hjE : E < hH.eigenvalues j := by
      by_contra h
      exact hj ((mem_spectralSubspace_iff hH _ u).mp hu j h)
    exact mul_lt_mul_of_pos_right hjE (by positivity)

theorem finrank_spectralSubspace_Ioi_add (E : ℝ) :
    Module.finrank ℂ (spectralSubspace hH (Set.Ioi E)) + eigenvalueCount hH E =
      Fintype.card ι := by
  classical
  rw [finrank_spectralSubspace, eigenvalueCount]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (fun i => hH.eigenvalues i ∈ Set.Ioi E)
  simpa [Set.mem_Ioi] using this

theorem finrank_spectralSubspace_Ici_add (E : ℝ) :
    Module.finrank ℂ (spectralSubspace hH (Set.Ici E)) + eigenvalueCountLT hH E =
      Fintype.card ι := by
  classical
  rw [finrank_spectralSubspace, eigenvalueCountLT]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (fun i => hH.eigenvalues i ∈ Set.Ici E)
  simpa [Set.mem_Ici] using this

omit [DecidableEq ι] in
theorem exists_mem_inf_ne_zero (V W : Submodule ℂ (ι → ℂ))
    (h : Fintype.card ι < Module.finrank ℂ V + Module.finrank ℂ W) :
    ∃ u ∈ V, u ∈ W ∧ u ≠ 0 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h2 : Module.finrank ℂ ↥(V ⊔ W) ≤ Fintype.card ι := by
    simpa using Submodule.finrank_le (V ⊔ W)
  have h3 : Module.finrank ℂ ↥(V ⊓ W) ≠ 0 := by omega
  have h4 : V ⊓ W ≠ ⊥ := fun hb => h3 (by rw [hb]; exact finrank_bot ℂ _)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  exact ⟨u, hu.1, hu.2, hu0⟩

/-- Min-max, upper bound: a subspace on which the form is `≤ E` has dimension at most the count. -/
theorem finrank_le_eigenvalueCount {E : ℝ} (V : Submodule ℂ (ι → ℂ))
    (hV : ∀ u ∈ V, (star u ⬝ᵥ (H *ᵥ u)).re ≤ E * (star u ⬝ᵥ u).re) :
    Module.finrank ℂ V ≤ eigenvalueCount hH E := by
  by_contra hlt
  have h1 := finrank_spectralSubspace_Ioi_add hH E
  obtain ⟨u, huV, huW, hu0⟩ := exists_mem_inf_ne_zero V (spectralSubspace hH (Set.Ioi E))
    (by omega)
  have := hV u huV
  have := lt_re_star_dotProduct_mulVec_of_mem_spectralSubspace_Ioi hH huW hu0
  linarith

theorem finrank_le_eigenvalueCountLT {E : ℝ} (V : Submodule ℂ (ι → ℂ))
    (hV : ∀ u ∈ V, u ≠ 0 → (star u ⬝ᵥ (H *ᵥ u)).re < E * (star u ⬝ᵥ u).re) :
    Module.finrank ℂ V ≤ eigenvalueCountLT hH E := by
  by_contra hlt
  have h1 := finrank_spectralSubspace_Ici_add hH E
  obtain ⟨u, huV, huW, hu0⟩ := exists_mem_inf_ne_zero V (spectralSubspace hH (Set.Ici E))
    (by omega)
  have := hV u huV hu0
  have := le_re_star_dotProduct_mulVec_of_mem_spectralSubspace_Ici hH huW
  linarith

/-- Min-max characterization of the count. -/
theorem isGreatest_eigenvalueCount (E : ℝ) :
    IsGreatest {d | ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = d ∧
      ∀ u ∈ V, (star u ⬝ᵥ (H *ᵥ u)).re ≤ E * (star u ⬝ᵥ u).re} (eigenvalueCount hH E) :=
  ⟨⟨spectralSubspace hH (Set.Iic E), finrank_spectralSubspace_Iic hH E,
    fun _ hu => re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic hH hu⟩,
    fun _ ⟨V, hV, hV'⟩ => hV ▸ finrank_le_eigenvalueCount hH V hV'⟩

theorem isGreatest_eigenvalueCountLT (E : ℝ) :
    IsGreatest {d | ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = d ∧
      ∀ u ∈ V, u ≠ 0 → (star u ⬝ᵥ (H *ᵥ u)).re < E * (star u ⬝ᵥ u).re}
      (eigenvalueCountLT hH E) :=
  ⟨⟨spectralSubspace hH (Set.Iio E), finrank_spectralSubspace_Iio hH E,
    fun _ hu hu0 => re_star_dotProduct_mulVec_lt_of_mem_spectralSubspace_Iio hH hu hu0⟩,
    fun _ ⟨V, hV, hV'⟩ => hV ▸ finrank_le_eigenvalueCountLT hH V hV'⟩

/-- A subspace on which the form is `≥ E` has dimension at most `card ι - eigenvalueCountLT`. -/
theorem finrank_add_eigenvalueCountLT_le {E : ℝ} (V : Submodule ℂ (ι → ℂ))
    (hV : ∀ u ∈ V, E * (star u ⬝ᵥ u).re ≤ (star u ⬝ᵥ (H *ᵥ u)).re) :
    Module.finrank ℂ V + eigenvalueCountLT hH E ≤ Fintype.card ι := by
  by_contra hlt
  obtain ⟨u, huV, huW, hu0⟩ := exists_mem_inf_ne_zero V (spectralSubspace hH (Set.Iio E))
    (by rw [finrank_spectralSubspace_Iio]; omega)
  have := hV u huV
  have := re_star_dotProduct_mulVec_lt_of_mem_spectralSubspace_Iio hH huW hu0
  linarith

theorem finrank_add_eigenvalueCount_le {E : ℝ} (V : Submodule ℂ (ι → ℂ))
    (hV : ∀ u ∈ V, u ≠ 0 → E * (star u ⬝ᵥ u).re < (star u ⬝ᵥ (H *ᵥ u)).re) :
    Module.finrank ℂ V + eigenvalueCount hH E ≤ Fintype.card ι := by
  by_contra hlt
  obtain ⟨u, huV, huW, hu0⟩ := exists_mem_inf_ne_zero V (spectralSubspace hH (Set.Iic E))
    (by rw [finrank_spectralSubspace_Iic]; omega)
  have := hV u huV hu0
  have := re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic hH huW
  linarith

end FroehlichSpencer.Infra
