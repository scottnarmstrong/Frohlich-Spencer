/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Weyl
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Regularity of spectral conditions

For a continuous (resp. measurable) family of Hermitian matrices, the eigenvalues are continuous
(resp. measurable), the spectral distance `min_i |λ_i - E|` is continuous, the spectral-gap events
are closed (resp. measurable), and the eigenvalue counting functions are measurable, also jointly
in the parameter and the energy. We also treat the family `v ↦ A + diagonal (v ∘ f)`.

This gives measurability of the events in Fröhlich–Spencer (1983) defined by
`dist(spec H, E) ≥ …` and of the counting function `N_Λ(E, v)`.
-/

@[expose] public section

open Matrix Finset

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*}

/-- Spectral conditions can be phrased through Mathlib's `spectrum ℝ`. -/
theorem forall_mem_spectrum_iff {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (p : ℝ → Prop) :
    (∀ μ ∈ spectrum ℝ H, p μ) ↔ ∀ i, p (hH.eigenvalues i) := by
  rw [hH.spectrum_real_eq_range_eigenvalues]
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]

theorem le_inf'_abs_eigenvalues_sub_iff [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (E κ : ℝ) :
    κ ≤ Finset.univ.inf' Finset.univ_nonempty (fun i => |hH.eigenvalues i - E|) ↔
      ∀ i, κ ≤ |hH.eigenvalues i - E| := by
  simp only [Finset.le_inf'_iff, Finset.mem_univ, true_implies]

section Topological
variable [TopologicalSpace X] {A : X → Matrix ι ι ℂ}

private theorem continuous_abs_eigenvalues_sub (hA : Continuous A)
    (hAH : ∀ x, (A x).IsHermitian) (E : ℝ) (i : ι) :
    Continuous fun x => |(hAH x).eigenvalues i - E| :=
  ((continuous_eigenvalues hA hAH i).sub continuous_const).abs

/-- The spectral distance `min_i |λ_i - E|` is continuous. -/
theorem continuous_inf'_abs_eigenvalues_sub [Nonempty ι] (hA : Continuous A)
    (hAH : ∀ x, (A x).IsHermitian) (E : ℝ) :
    Continuous fun x =>
      Finset.univ.inf' Finset.univ_nonempty (fun i => |(hAH x).eigenvalues i - E|) :=
  Continuous.finset_inf'_apply _ fun i _ => continuous_abs_eigenvalues_sub hA hAH E i

theorem isClosed_setOf_forall_le_abs_eigenvalues_sub (hA : Continuous A)
    (hAH : ∀ x, (A x).IsHermitian) (E κ : ℝ) :
    IsClosed {x | ∀ i, κ ≤ |(hAH x).eigenvalues i - E|} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i =>
    isClosed_le continuous_const (continuous_abs_eigenvalues_sub hA hAH E i)

theorem isOpen_setOf_forall_lt_abs_eigenvalues_sub (hA : Continuous A)
    (hAH : ∀ x, (A x).IsHermitian) (E κ : ℝ) :
    IsOpen {x | ∀ i, κ < |(hAH x).eigenvalues i - E|} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_abs_eigenvalues_sub hA hAH E i)

theorem isClosed_setOf_exists_abs_eigenvalues_sub_le (hA : Continuous A)
    (hAH : ∀ x, (A x).IsHermitian) (E κ : ℝ) :
    IsClosed {x | ∃ i, |(hAH x).eigenvalues i - E| ≤ κ} := by
  simp only [Set.ofPred_exists]
  exact isClosed_iUnion_of_finite fun i =>
    isClosed_le (continuous_abs_eigenvalues_sub hA hAH E i) continuous_const

end Topological

section Measurable
variable [MeasurableSpace X] {A : X → Matrix ι ι ℂ}

/-- The Hermitian part of a matrix. -/
private noncomputable def hermPart (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := (2⁻¹ : ℝ) • (M + Mᴴ)

omit [Fintype ι] [DecidableEq ι] in
private theorem isHermitian_hermPart (M : Matrix ι ι ℂ) : (hermPart M).IsHermitian := by
  unfold hermPart
  rw [IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  simp

omit [Fintype ι] [DecidableEq ι] in
private theorem hermPart_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    hermPart M = M := by
  unfold hermPart
  rw [hM.eq, ← two_smul ℝ M, smul_smul]
  norm_num

omit [Fintype ι] [DecidableEq ι] in
private theorem continuous_hermPart : Continuous (hermPart (ι := ι)) := by
  unfold hermPart
  exact ((continuous_id (X := Matrix ι ι ℂ)).add continuous_id.matrix_conjTranspose).const_smul
    ((2⁻¹ : ℝ))

theorem measurable_eigenvaluesAsc (hA : Measurable A) (hAH : ∀ x, (A x).IsHermitian)
    (k : Fin (Fintype.card ι)) : Measurable fun x => eigenvaluesAsc (hAH x) k := by
  have hc : Continuous fun M : Matrix ι ι ℂ => eigenvaluesAsc (isHermitian_hermPart M) k :=
    continuous_eigenvaluesAsc continuous_hermPart isHermitian_hermPart k
  have : (fun x => eigenvaluesAsc (hAH x) k) =
      fun x => eigenvaluesAsc (isHermitian_hermPart (A x)) k := by
    funext x
    rw [eigenvaluesAsc_congr (hAH x) (isHermitian_hermPart (A x))
      (hermPart_of_isHermitian (hAH x)).symm]
  rw [this]
  exact hc.measurable.comp hA

theorem measurable_eigenvalues (hA : Measurable A) (hAH : ∀ x, (A x).IsHermitian) (i : ι) :
    Measurable fun x => (hAH x).eigenvalues i := by
  have : (fun x => (hAH x).eigenvalues i) =
      fun x => eigenvaluesAsc (hAH x) (ascIndex ι i) :=
    funext fun x => eigenvalues_eq_eigenvaluesAsc_ascIndex (hAH x) i
  rw [this]
  exact measurable_eigenvaluesAsc hA hAH _

theorem measurable_inf'_abs_eigenvalues_sub [Nonempty ι] (hA : Measurable A)
    (hAH : ∀ x, (A x).IsHermitian) (E : ℝ) :
    Measurable fun x =>
      Finset.univ.inf' Finset.univ_nonempty (fun i => |(hAH x).eigenvalues i - E|) :=
  (Continuous.finset_inf'_apply (s := (Finset.univ : Finset ι)) Finset.univ_nonempty
    (f := fun i (w : ι → ℝ) => w i) fun i _ => continuous_apply i).measurable.comp
    (Measurable.of_eval fun i => (continuous_abs.measurable.comp
      ((measurable_eigenvalues hA hAH i).sub_const E)))

theorem measurableSet_setOf_forall_le_abs_eigenvalues_sub (hA : Measurable A)
    (hAH : ∀ x, (A x).IsHermitian) (E κ : ℝ) :
    MeasurableSet {x | ∀ i, κ ≤ |(hAH x).eigenvalues i - E|} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le measurable_const
      (continuous_abs.measurable.comp ((measurable_eigenvalues hA hAH i).sub_const E))

theorem measurableSet_setOf_exists_abs_eigenvalues_sub_le (hA : Measurable A)
    (hAH : ∀ x, (A x).IsHermitian) (E κ : ℝ) :
    MeasurableSet {x | ∃ i, |(hAH x).eigenvalues i - E| ≤ κ} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun i =>
    measurableSet_le
      (continuous_abs.measurable.comp ((measurable_eigenvalues hA hAH i).sub_const E))
      measurable_const

theorem measurable_eigenvalueCount (hA : Measurable A) (hAH : ∀ x, (A x).IsHermitian)
    (E : ℝ) : Measurable fun x => eigenvalueCount (hAH x) E := by
  have : (fun x => eigenvalueCount (hAH x) E) =
      fun x => ∑ k, if eigenvaluesAsc (hAH x) k ≤ E then 1 else 0 := by
    funext x
    rw [eigenvalueCount_eq_card_eigenvaluesAsc, Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurableSet_le (measurable_eigenvaluesAsc hA hAH k) measurable_const)
      measurable_const measurable_const

theorem measurable_eigenvalueCountLT (hA : Measurable A) (hAH : ∀ x, (A x).IsHermitian)
    (E : ℝ) : Measurable fun x => eigenvalueCountLT (hAH x) E := by
  have : (fun x => eigenvalueCountLT (hAH x) E) =
      fun x => ∑ k, if eigenvaluesAsc (hAH x) k < E then 1 else 0 := by
    funext x
    rw [← Finset.card_filter]
    refine Finset.card_equiv (ascIndex ι) fun k => ?_
    simp only [mem_filter, mem_univ, true_and]
    rw [eigenvalues_eq_eigenvaluesAsc_ascIndex (hAH x)]
  rw [this]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurableSet_lt (measurable_eigenvaluesAsc hA hAH k) measurable_const)
      measurable_const measurable_const

/-- Joint measurability in the parameter and the energy. -/
theorem measurable_eigenvalueCount_uncurry (hA : Measurable A) (hAH : ∀ x, (A x).IsHermitian) :
    Measurable fun p : X × ℝ => eigenvalueCount (hAH p.1) p.2 := by
  have : (fun p : X × ℝ => eigenvalueCount (hAH p.1) p.2) =
      fun p => ∑ k, if eigenvaluesAsc (hAH p.1) k ≤ p.2 then 1 else 0 := by
    funext p
    rw [eigenvalueCount_eq_card_eigenvaluesAsc, Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurableSet_le
      ((measurable_eigenvaluesAsc hA hAH k).comp measurable_fst) measurable_snd)
      measurable_const measurable_const

theorem measurable_eigenvalueCountLT_uncurry (hA : Measurable A)
    (hAH : ∀ x, (A x).IsHermitian) :
    Measurable fun p : X × ℝ => eigenvalueCountLT (hAH p.1) p.2 := by
  have : (fun p : X × ℝ => eigenvalueCountLT (hAH p.1) p.2) =
      fun p => ∑ k, if eigenvaluesAsc (hAH p.1) k < p.2 then 1 else 0 := by
    funext p
    rw [← Finset.card_filter]
    refine Finset.card_equiv (ascIndex ι) fun k => ?_
    simp only [mem_filter, mem_univ, true_and]
    rw [eigenvalues_eq_eigenvaluesAsc_ascIndex (hAH p.1)]
  rw [this]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurableSet_lt
      ((measurable_eigenvaluesAsc hA hAH k).comp measurable_fst) measurable_snd)
      measurable_const measurable_const

end Measurable

section DiagonalFamily
variable {J : Type*}

omit [Fintype ι] in
theorem isHermitian_add_diagonal {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℝ) :
    (A + diagonal (fun i => (v i : ℂ))).IsHermitian := by
  refine hA.add ?_
  rw [IsHermitian, diagonal_conjTranspose]
  simp

omit [Fintype ι] in
theorem continuous_add_diagonal_comp (A : Matrix ι ι ℂ) (f : ι → J) :
    Continuous fun v : J → ℝ => A + diagonal (fun i => (v (f i) : ℂ)) := by
  refine continuous_const.add (continuous_matrix fun i j => ?_)
  by_cases h : i = j
  · subst h
    simp only [diagonal_apply_eq]
    exact Complex.continuous_ofReal.comp (continuous_apply (f i))
  · simpa [diagonal_apply_ne _ h] using continuous_const

omit [Fintype ι] in
theorem measurable_add_diagonal_comp (A : Matrix ι ι ℂ) (f : ι → J) :
    Measurable fun v : J → ℝ => A + diagonal (fun i => (v (f i) : ℂ)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  by_cases h : i = j
  · subst h
    simp only [Matrix.add_apply, diagonal_apply_eq]
    exact measurable_const.add
      (Complex.continuous_ofReal.measurable.comp (measurable_pi_apply (f i)))
  · simp [diagonal_apply_ne _ h]

/-- The spectral-gap event for `A + diagonal (v ∘ f)` is closed in `J → ℝ` … -/
theorem isClosed_setOf_forall_le_abs_eigenvalues_add_diagonal_sub {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ι → J) (E κ : ℝ) :
    IsClosed {v : J → ℝ |
      ∀ i, κ ≤ |(isHermitian_add_diagonal hA (fun i => v (f i))).eigenvalues i - E|} :=
  isClosed_setOf_forall_le_abs_eigenvalues_sub (continuous_add_diagonal_comp A f)
    (fun v => isHermitian_add_diagonal hA (fun i => v (f i))) E κ

/-- … and measurable. -/
theorem measurableSet_setOf_forall_le_abs_eigenvalues_add_diagonal_sub {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ι → J) (E κ : ℝ) :
    MeasurableSet {v : J → ℝ |
      ∀ i, κ ≤ |(isHermitian_add_diagonal hA (fun i => v (f i))).eigenvalues i - E|} :=
  measurableSet_setOf_forall_le_abs_eigenvalues_sub (measurable_add_diagonal_comp A f)
    (fun v => isHermitian_add_diagonal hA (fun i => v (f i))) E κ

theorem measurable_eigenvalueCount_add_diagonal_uncurry {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ι → J) :
    Measurable fun p : (J → ℝ) × ℝ =>
      eigenvalueCount (isHermitian_add_diagonal hA (fun i => p.1 (f i))) p.2 :=
  measurable_eigenvalueCount_uncurry (measurable_add_diagonal_comp A f)
    (fun v => isHermitian_add_diagonal hA (fun i => v (f i)))

end DiagonalFamily

end FroehlichSpencer.Infra
