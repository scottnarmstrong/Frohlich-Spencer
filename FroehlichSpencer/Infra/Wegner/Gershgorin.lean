/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Location
public import FroehlichSpencer.Infra.Spectral.Regularity
public import FroehlichSpencer.Infra.Wegner.Gaussian
public import FroehlichSpencer.Infra.ProductMeasure

/-!
# Gershgorin resonance: an eigenvalue near `E` forces a site potential near `E`

Fröhlich–Spencer (1983), Appendix C, (C.5) (Fröhlich–Spencer (1983)), generic form:
if `A` is Hermitian with row sums `∑ y, ‖A x y‖ ≤ K` and `A + diagonal v` has an eigenvalue
within `κ` of `E`, then some site has `|v x - E| ≤ K + κ`.

Consequently, under
`productMeasure μ` the probability of such an eigenvalue is at most
`|Λ| μ {t | |t - E| ≤ K + κ}`, with an explicit bound for the Gaussian law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped ENNReal NNReal

namespace FroehlichSpencer.Infra

theorem exists_abs_sub_le_of_abs_eigenvalues_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {K : ℝ} (hK : ∀ x, ∑ y, ‖A x y‖ ≤ K) (v : ι → ℝ)
    {E κ : ℝ} {i : ι} (hi : |(isHermitian_add_diagonal hA v).eigenvalues i - E| ≤ κ) :
    ∃ x, |v x - E| ≤ K + κ := by
  obtain ⟨k, hk⟩ := exists_abs_eigenvalues_sub_diagonal_add_le A v
    (isHermitian_add_diagonal hA v) i
  refine ⟨k, ?_⟩
  have h1 : (A k k).re ≤ ‖A k k‖ := (Complex.re_le_norm _)
  have h2 : -‖A k k‖ ≤ (A k k).re := by
    have := Complex.abs_re_le_norm (A k k)
    linarith [(abs_le.mp this).1]
  have h3 : ‖A k k‖ + ∑ j ∈ univ.erase k, ‖A k j‖ ≤ K := by
    have := Finset.add_sum_erase univ (fun j => ‖A k j‖) (mem_univ k)
    linarith [hK k]
  have h4 := abs_le.mp hk
  have h5 := abs_le.mp hi
  rw [abs_le]
  constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]

section

variable {ι : Type*} [DecidableEq ι] {Λ : Finset ι} {A : Matrix Λ Λ ℂ}

theorem productMeasure_exists_abs_eigenvalues_sub_le_le_card_mul (hA : A.IsHermitian) {K : ℝ}
    (hK : ∀ x, ∑ y, ‖A x y‖ ≤ K) (μ : Measure ℝ) [IsProbabilityMeasure μ] (E κ : ℝ) :
    productMeasure μ {v : ι → ℝ |
        ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E| ≤ κ} ≤
      Λ.card * μ {t | |t - E| ≤ K + κ} := by
  have hmeas : MeasurableSet {t : ℝ | |t - E| ≤ K + κ} :=
    measurableSet_le (by fun_prop) measurable_const
  calc productMeasure μ {v : ι → ℝ |
        ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E| ≤ κ}
      ≤ productMeasure μ (⋃ x : Λ, {v : ι → ℝ | v x ∈ {t | |t - E| ≤ K + κ}}) := by
        refine measure_mono ?_
        rintro v ⟨i, hi⟩
        obtain ⟨x, hx⟩ := exists_abs_sub_le_of_abs_eigenvalues_sub_le hA hK
          (fun x : Λ => v x) hi
        exact Set.mem_iUnion.mpr ⟨x, hx⟩
    _ ≤ ∑ x : Λ, productMeasure μ {v : ι → ℝ | v x ∈ {t | |t - E| ≤ K + κ}} :=
        measure_iUnion_fintype_le _ _
    _ = Λ.card * μ {t | |t - E| ≤ K + κ} := by
        simp only [productMeasure_setOf_apply_mem μ _ hmeas, Finset.sum_const,
          Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

theorem productMeasure_gaussianReal_exists_abs_eigenvalues_sub_le_le (hA : A.IsHermitian)
    {K : ℝ} (hK : ∀ x, ∑ y, ‖A x y‖ ≤ K) {γ : ℝ≥0} (hγ : γ ≠ 0) {E κ : ℝ} (hKE : K + κ ≤ |E|) :
    productMeasure (gaussianReal 0 γ) {v : ι → ℝ |
        ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E| ≤ κ} ≤
      Λ.card * ENNReal.ofReal (2 * (K + κ) / √(2 * Real.pi * γ) *
        Real.exp (-(|E| - (K + κ)) ^ 2 / (2 * γ))) := by
  refine (productMeasure_exists_abs_eigenvalues_sub_le_le_card_mul hA hK _ E κ).trans ?_
  gcongr
  have hset : {t : ℝ | |t - E| ≤ K + κ} = Set.Icc (E - (K + κ)) (E + (K + κ)) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_sub_le_iff]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hset]
  exact gaussianReal_Icc_le hγ hKE

end

end FroehlichSpencer.Infra
