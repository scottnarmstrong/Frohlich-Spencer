/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.Hamiltonian
public import FroehlichSpencer.Surface.HamiltonianHermitian
public import FroehlichSpencer.Surface.DirichletLaplacian
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.GaussianLaw
public import FroehlichSpencer.Infra.Wegner.Resonance
public import FroehlichSpencer.Lattice.Kernel

/-!
Internal lemmas for the resonance event `Res(Λ, E, κ) = {v | dist(spec H_Λ(v), E) ≤ κ}` of the
finite-volume Hamiltonian: measurability, locality, the shift `H_Λ = A_Λ + diag v + 2ν`, the
bounded-density Wegner bound, the Gershgorin bound, and the two combined branch estimates
(Fröhlich–Spencer (1983), Appendix C, Fröhlich–Spencer (1983)).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal Matrix Pointwise

namespace FroehlichSpencer.T12

instance (γ : ℝ) (hγ : 0 < γ) : IsProbabilityMeasure (gaussianLaw γ hγ) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _


def resonanceEvent (ν : ℕ) (Λ : Finset (Site ν)) (E κ : ℝ) : Set (Configuration ν) :=
  {v | ∃ j, |(hamiltonian_isHermitian ν Λ v).eigenvalues j - E| ≤ κ}


noncomputable def hoppingMatrix (ν : ℕ) (Λ : Finset (Site ν)) :
    Matrix {x // x ∈ Λ} {x // x ∈ Λ} ℂ :=
  -dirichletLaplacian ν Λ - ((2 * ν : ℕ) : ℂ) • (1 : Matrix {x // x ∈ Λ} {x // x ∈ Λ} ℂ)

private theorem hoppingMatrix_apply (ν : ℕ) (Λ : Finset (Site ν)) (x y : {x // x ∈ Λ}) :
    hoppingMatrix ν Λ x y = hoppingKernel ν x.1 y.1 := by
  classical
  have hD : dirichletLaplacian ν Λ x y =
      (∑ k : Fin ν, if y.1 = x.1 + Pi.single k (1 : ℤ) then (1 : ℂ) else 0) +
      star (∑ k : Fin ν, if x.1 = y.1 + Pi.single k (1 : ℤ) then (1 : ℂ) else 0) -
      ((2 * ν : ℕ) : ℂ) * (if x = y then 1 else 0) := by
    unfold dirichletLaplacian
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rfl
  have h1 : ∀ k : Fin ν, (x.1 = y.1 + Pi.single k (1 : ℤ)) ↔
      (y.1 = x.1 - Pi.single k (1 : ℤ)) :=
    fun k => by constructor <;> intro h <;> rw [h] <;> simp
  have hstar : star (∑ k : Fin ν, if x.1 = y.1 + Pi.single k (1 : ℤ) then (1 : ℂ) else 0) =
      ∑ k : Fin ν, if y.1 = x.1 - Pi.single k (1 : ℤ) then (1 : ℂ) else 0 := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [h1]
    split_ifs <;> simp
  simp only [hoppingMatrix, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, hD, hstar, hoppingKernel, Finset.sum_add_distrib]
  ring


theorem isHermitian_hoppingMatrix (ν : ℕ) (Λ : Finset (Site ν)) :
    (hoppingMatrix ν Λ).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, hoppingMatrix_apply]
  rw [← hoppingKernel_symm]


theorem hoppingMatrix_apply_self (ν : ℕ) (Λ : Finset (Site ν)) (x : {x // x ∈ Λ}) :
    hoppingMatrix ν Λ x x = 0 := by
  classical
  rw [hoppingMatrix_apply]
  unfold hoppingKernel
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h : (Pi.single k (1 : ℤ) : Site ν) ≠ 0 := by
    intro h
    have := congrFun h k
    simp at this
  have h1 : x.1 ≠ x.1 + Pi.single k (1 : ℤ) := fun e => h (by simp at e)
  have h2 : x.1 ≠ x.1 - Pi.single k (1 : ℤ) := fun e => h (sub_eq_self.mp e.symm)
  simp [h1, h2]


theorem sum_norm_hoppingMatrix_le (ν : ℕ) (Λ : Finset (Site ν)) (x : {x // x ∈ Λ}) :
    ∑ y, ‖hoppingMatrix ν Λ x y‖ ≤ 2 * ν := by
  simp only [hoppingMatrix_apply]
  have := sum_norm_hoppingKernel_le ν x.1 Λ
  rwa [← Finset.sum_coe_sort Λ (fun w => ‖hoppingKernel ν x.1 w‖)] at this


theorem hamiltonian_eq_hoppingMatrix_add (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) :
    hamiltonian ν Λ v = hoppingMatrix ν Λ + Matrix.diagonal (fun x => (v x.1 : ℂ)) +
      ((2 * ν : ℕ) : ℂ) • (1 : Matrix {x // x ∈ Λ} {x // x ∈ Λ} ℂ) := by
  classical
  ext x y
  simp only [hamiltonian, hoppingMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

private theorem exists_abs_eigenvalues_sub_le_shift {n : Type*} [Fintype n] [DecidableEq n]
    {H M : Matrix n n ℂ} (hH : H.IsHermitian) (hM : M.IsHermitian) (c : ℝ)
    (hHM : H = M + algebraMap ℝ (Matrix n n ℂ) c) (E κ : ℝ) :
    (∃ j, |hH.eigenvalues j - E| ≤ κ) ↔ ∃ j, |hM.eigenvalues j - (E - c)| ≤ κ := by
  have hsp : spectrum ℝ H = spectrum ℝ M + ({c} : Set ℝ) := by
    rw [spectrum.add_singleton_eq, hHM]
  have h1 := hH.spectrum_real_eq_range_eigenvalues
  have h2 := hM.spectrum_real_eq_range_eigenvalues
  constructor
  · rintro ⟨j, hj⟩
    have : hH.eigenvalues j ∈ spectrum ℝ M + ({c} : Set ℝ) := hsp ▸ (h1 ▸ Set.mem_range_self j)
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp this
    rw [h2] at ha
    obtain ⟨i, rfl⟩ := ha
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨i, by rw [← hab] at hj; convert hj using 2; ring⟩
  · rintro ⟨j, hj⟩
    have : hM.eigenvalues j + c ∈ spectrum ℝ H := by
      rw [hsp]
      exact Set.add_mem_add (h2 ▸ Set.mem_range_self j) rfl
    rw [h1] at this
    obtain ⟨i, hi⟩ := this
    exact ⟨i, by rw [hi]; convert hj using 2; ring⟩


theorem mem_resonanceEvent_iff (ν : ℕ) (Λ : Finset (Site ν)) (E κ : ℝ) (v : Site ν → ℝ) :
    v ∈ resonanceEvent ν Λ E κ ↔
      ∃ j, |(Infra.isHermitian_add_diagonal (isHermitian_hoppingMatrix ν Λ)
        (fun x : {x // x ∈ Λ} => v x)).eigenvalues j - (E - 2 * ν)| ≤ κ := by
  classical
  refine exists_abs_eigenvalues_sub_le_shift (hamiltonian_isHermitian ν Λ v) _ (2 * ν) ?_ E κ
  rw [hamiltonian_eq_hoppingMatrix_add]
  congr 1
  ext i j
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.one_apply]


theorem measurableSet_resonanceEvent (ν : ℕ) (Λ : Finset (Site ν)) (E κ : ℝ) :
    MeasurableSet (resonanceEvent ν Λ E κ) := by
  have : resonanceEvent ν Λ E κ = {v : Site ν → ℝ | ∃ j, |(Infra.isHermitian_add_diagonal
      (isHermitian_hoppingMatrix ν Λ) (fun x : {x // x ∈ Λ} => v x)).eigenvalues j -
        (E - 2 * ν)| ≤ κ} := Set.ext fun v => mem_resonanceEvent_iff ν Λ E κ v
  rw [this]
  exact Infra.measurableSet_exists_abs_eigenvalues_sub_le (isHermitian_hoppingMatrix ν Λ) _ κ


theorem dependsOn_resonanceEvent (ν : ℕ) (Λ : Finset (Site ν)) (E κ : ℝ) :
    Infra.DependsOn (Λ : Set (Site ν)) (resonanceEvent ν Λ E κ) := by
  have : resonanceEvent ν Λ E κ = {v : Site ν → ℝ | ∃ j, |(Infra.isHermitian_add_diagonal
      (isHermitian_hoppingMatrix ν Λ) (fun x : {x // x ∈ Λ} => v x)).eigenvalues j -
        (E - 2 * ν)| ≤ κ} := Set.ext fun v => mem_resonanceEvent_iff ν Λ E κ v
  rw [this]
  exact Infra.dependsOn_exists_abs_eigenvalues_sub_le (isHermitian_hoppingMatrix ν Λ) _ κ

private theorem resonanceEvent_eq_setOf (ν : ℕ) (Λ : Finset (Site ν)) (E κ : ℝ) :
    resonanceEvent ν Λ E κ = {v : Site ν → ℝ | ∃ j, |(Infra.isHermitian_add_diagonal
      (isHermitian_hoppingMatrix ν Λ) (fun x : {x // x ∈ Λ} => v x)).eigenvalues j -
        (E - 2 * ν)| ≤ κ} := Set.ext fun v => mem_resonanceEvent_iff ν Λ E κ v

private theorem resonanceEvent_eq_empty (ν : ℕ) (Λ : Finset (Site ν)) (E : ℝ) {κ : ℝ}
    (hκ : κ < 0) : resonanceEvent ν Λ E κ = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨j, hj⟩ := hv
  linarith [abs_nonneg ((hamiltonian_isHermitian ν Λ v).eigenvalues j - E)]


theorem configurationMeasure_resonanceEvent_le_wegner (ν : ℕ) (Λ : Finset (Site ν))
    (law : Measure ℝ) [IsProbabilityMeasure law] {δ : ℝ} (hlaw : HasBoundedDensity law δ)
    (E κ : ℝ) :
    configurationMeasure ν law (resonanceEvent ν Λ E κ) ≤
      ENNReal.ofReal (2 * κ * δ⁻¹) * Λ.card := by
  classical
  by_cases hκ : κ < 0
  · rw [resonanceEvent_eq_empty ν Λ E hκ, measure_empty]
    exact bot_le
  push Not at hκ
  obtain ⟨hδ, g, -, hlg, hg⟩ := hlaw
  have h := Infra.productMeasure_exists_abs_eigenvalues_sub_le_le
    (ι := Site ν) (Λ := Λ) (isHermitian_hoppingMatrix ν Λ) law hlg
    (Filter.Eventually.of_forall hg) ENNReal.ofReal_ne_top (E - 2 * ν) κ
  rw [resonanceEvent_eq_setOf]
  refine h.trans_eq ?_
  rw [mul_comm (2 * κ) δ⁻¹, ENNReal.ofReal_mul (inv_nonneg.2 hδ.le)]


theorem exists_abs_sub_le_of_mem_resonanceEvent {ν : ℕ} {Λ : Finset (Site ν)} {E κ : ℝ}
    {v : Site ν → ℝ} (hv : v ∈ resonanceEvent ν Λ E κ) :
    ∃ x ∈ Λ, |v x - (E - 2 * ν)| ≤ 2 * ν + κ := by
  classical
  obtain ⟨j, hj⟩ := (mem_resonanceEvent_iff ν Λ E κ v).1 hv
  obtain ⟨x, hx⟩ := Infra.exists_abs_sub_le_of_abs_eigenvalues_sub_le
    (isHermitian_hoppingMatrix ν Λ) (sum_norm_hoppingMatrix_le ν Λ)
    (fun x : {x // x ∈ Λ} => v x) hj
  exact ⟨x.1, x.2, hx⟩

private theorem configurationMeasure_resonanceEvent_le_card_mul (ν : ℕ) (Λ : Finset (Site ν))
    (law : Measure ℝ) [IsProbabilityMeasure law] (E κ : ℝ) :
    configurationMeasure ν law (resonanceEvent ν Λ E κ) ≤
      Λ.card * law {t | |t - (E - 2 * ν)| ≤ 2 * ν + κ} := by
  classical
  rw [resonanceEvent_eq_setOf]
  exact Infra.productMeasure_exists_abs_eigenvalues_sub_le_le_card_mul
    (ι := Site ν) (Λ := Λ) (isHermitian_hoppingMatrix ν Λ) (sum_norm_hoppingMatrix_le ν Λ)
    law (E - 2 * ν) κ


theorem configurationMeasure_resonanceEvent_le_gershgorin (ν : ℕ) (Λ : Finset (Site ν))
    (law : Measure ℝ) [IsProbabilityMeasure law] (E : ℝ) {κ : ℝ} (hκ : κ ≤ 1) :
    configurationMeasure ν law (resonanceEvent ν Λ E κ) ≤
      Λ.card * law {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1} := by
  refine (configurationMeasure_resonanceEvent_le_card_mul ν Λ law E κ).trans ?_
  gcongr


theorem tendsto_gaussianLaw_window (ν : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun E : ℝ => (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1})
      (cocompact ℝ) (𝓝 0) := by
  set R : ℝ → ℝ := fun E => max 0 (|E - 2 * ν| - (2 * ν + 1)) with hR
  have hRtop : Tendsto R (cocompact ℝ) atTop := by
    have h1 : Tendsto (fun E : ℝ => |E| - (4 * ν + 1)) (cocompact ℝ) atTop := by
      have := tendsto_norm_cocompact_atTop (E := ℝ)
      exact tendsto_atTop_add_const_right _ _ this
    refine tendsto_atTop_mono (fun E => ?_) h1
    refine le_max_of_le_right ?_
    have := abs_sub_abs_le_abs_sub E (2 * (ν : ℝ))
    have h2 : |2 * (ν : ℝ)| = 2 * ν := abs_of_nonneg (by positivity)
    linarith
  have hup : Tendsto (fun E => 2 * Real.exp (-(R E) ^ 2 / (2 * γ))) (cocompact ℝ) (𝓝 0) := by
    have h2 : Tendsto (fun E => -(R E) ^ 2 / (2 * γ)) (cocompact ℝ) atBot := by
      have h3 : Tendsto (fun E => (R E) ^ 2) (cocompact ℝ) atTop :=
        (tendsto_pow_atTop (two_ne_zero)).comp hRtop
      have h4 : Tendsto (fun E => (R E) ^ 2 / (2 * γ)) (cocompact ℝ) atTop :=
        h3.atTop_div_const (by positivity)
      refine (tendsto_neg_atTop_atBot.comp h4).congr (fun E => ?_)
      simp [neg_div]
    simpa using (Real.tendsto_exp_atBot.comp h2).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun E => MeasureTheory.measureReal_nonneg) (fun E => ?_)
  have hsub : {t : ℝ | |t - (E - 2 * ν)| ≤ 2 * ν + 1} ⊆ {t | R E ≤ |t|} := by
    intro t ht
    have h1 : |t - (E - 2 * ν)| ≤ 2 * ν + 1 := ht
    have h2 := abs_sub_abs_le_abs_sub (E - 2 * ν) t
    have h3 := abs_sub_comm (E - 2 * ν) t
    refine max_le (abs_nonneg t) ?_
    linarith
  have hb := Infra.gaussianReal_le_abs_le (γ := ⟨γ, hγ.le⟩) (R := R E)
    (le_max_left _ _)
  have h5 : (gaussianLaw γ hγ) {t | R E ≤ |t|} ≤
      ENNReal.ofReal (2 * Real.exp (-(R E) ^ 2 / (2 * γ))) := hb
  have h6 := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((measure_mono hsub).trans h5)
  rwa [ENNReal.toReal_ofReal (by positivity)] at h6

private theorem ofReal_mul_le_of_min {P : ℝ≥0∞} {x y : ℝ} {n : ℝ≥0∞} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : P ≤ ENNReal.ofReal x * n) (h2 : P ≤ ENNReal.ofReal y * n) :
    P ≤ ENNReal.ofReal (Real.sqrt (x * y)) * n := by
  rcases le_total x y with hxy | hxy
  · refine h1.trans ?_
    gcongr
    calc x = Real.sqrt (x * x) := (Real.sqrt_mul_self hx).symm
      _ ≤ Real.sqrt (x * y) := Real.sqrt_le_sqrt (by gcongr)
  · refine h2.trans ?_
    gcongr
    calc y = Real.sqrt (y * y) := (Real.sqrt_mul_self hy).symm
      _ ≤ Real.sqrt (x * y) := Real.sqrt_le_sqrt (by nlinarith)


theorem resonance_bound_boundedDensity (ν : ℕ) (Λ : Finset (Site ν)) (law : Measure ℝ)
    [IsProbabilityMeasure law] {δ : ℝ} (hlaw : HasBoundedDensity law δ) (E κ : ℝ) :
    MeasurableSet (resonanceEvent ν Λ E κ) ∧
      configurationMeasure ν law (resonanceEvent ν Λ E κ) ≤
        ENNReal.ofReal (Real.sqrt (2 * κ) * Real.sqrt δ⁻¹) * Λ.card := by
  refine ⟨measurableSet_resonanceEvent ν Λ E κ, ?_⟩
  by_cases hκ : κ < 0
  · rw [resonanceEvent_eq_empty ν Λ E hκ, measure_empty]
    exact bot_le
  push Not at hκ
  have hδ := hlaw.1
  have h1 := configurationMeasure_resonanceEvent_le_wegner ν Λ law hlaw E κ
  have h2 : configurationMeasure ν law (resonanceEvent ν Λ E κ) ≤ ENNReal.ofReal 1 * Λ.card := by
    refine (configurationMeasure_resonanceEvent_le_card_mul ν Λ law E κ).trans ?_
    calc _ ≤ (Λ.card : ℝ≥0∞) * 1 := by gcongr; exact prob_le_one
      _ = _ := by rw [ENNReal.ofReal_one]; ring
  have := ofReal_mul_le_of_min (by positivity) zero_le_one h1 h2
  rwa [mul_one, Real.sqrt_mul (by positivity)] at this

/--
Needs `κ ≤ 1` (Gershgorin); `0 ≤ κ` is not needed.
-/
theorem resonance_bound_gaussian (ν : ℕ) (Λ : Finset (Site ν)) {γ : ℝ} (hγ : 0 < γ) (E : ℝ)
    {κ : ℝ} (hκ : κ ≤ 1) :
    MeasurableSet (resonanceEvent ν Λ E κ) ∧
      configurationMeasure ν (gaussianLaw γ hγ) (resonanceEvent ν Λ E κ) ≤
        ENNReal.ofReal (Real.sqrt (2 * κ) * Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
          (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1})) * Λ.card := by
  refine ⟨measurableSet_resonanceEvent ν Λ E κ, ?_⟩
  by_cases hκ0 : κ < 0
  · rw [resonanceEvent_eq_empty ν Λ E hκ0, measure_empty]
    exact bot_le
  push Not at hκ0
  have hs : 0 < Real.sqrt (2 * Real.pi * γ) := Real.sqrt_pos.2 (by positivity)
  have hlaw : HasBoundedDensity (gaussianLaw γ hγ) (Real.sqrt (2 * Real.pi * γ)) := by
    refine ⟨hs, ProbabilityTheory.gaussianPDF 0 ⟨γ, hγ.le⟩, ProbabilityTheory.measurable_gaussianPDF
      _ _, ?_, fun t => ?_⟩
    · have hne : (⟨γ, hγ.le⟩ : NNReal) ≠ 0 := fun h => hγ.ne' (congrArg NNReal.toReal h)
      exact ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hne
    · rw [← one_div]
      exact Infra.gaussianPDF_zero_le t
  have h1 := configurationMeasure_resonanceEvent_le_wegner ν Λ _ hlaw E κ
  rw [← one_div] at h1
  set T := (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1} with hT
  have h2 : configurationMeasure ν (gaussianLaw γ hγ) (resonanceEvent ν Λ E κ) ≤
      ENNReal.ofReal T * Λ.card := by
    refine (configurationMeasure_resonanceEvent_le_gershgorin ν Λ _ E hκ).trans ?_
    rw [hT, MeasureTheory.ofReal_measureReal, mul_comm]
  have hL : 0 ≤ 1 / Real.sqrt (2 * Real.pi * γ) := by positivity
  have := ofReal_mul_le_of_min (by positivity) MeasureTheory.measureReal_nonneg h1 h2
  rwa [show 2 * κ * (1 / Real.sqrt (2 * Real.pi * γ)) * T =
    2 * κ * (1 / Real.sqrt (2 * Real.pi * γ) * T) by ring,
    Real.sqrt_mul (by positivity)] at this

end FroehlichSpencer.T12
