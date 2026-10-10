/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Resonance
public import FroehlichSpencer.Multiscale.Measurability


@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace FroehlichSpencer.T12

open Multiscale

private theorem eigenvalue_eq_set_eq_iInter {ν : ℕ} (Λ : Finset (Site ν)) (E : ℝ) :
    {v : Configuration ν | ∃ j, (hamiltonian_isHermitian ν Λ v).eigenvalues j = E} =
      ⋂ n : ℕ, resonanceEvent ν Λ E (1 / ((n : ℝ) + 1)) := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · rintro ⟨j, hj⟩ n
    exact ⟨j, by rw [hj]; simp; positivity⟩
  · intro h
    by_contra hne
    push Not at hne
    have hpos : ∀ j, ∃ n : ℕ, 1 / ((n : ℝ) + 1) <
        |(hamiltonian_isHermitian ν Λ v).eigenvalues j - E| := fun j =>
      exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 (hne j)))
    choose N hN using hpos
    obtain ⟨j, hj⟩ := h (Finset.univ.sup N)
    have h1 : N j ≤ Finset.univ.sup N := Finset.le_sup (f := N) (Finset.mem_univ j)
    have h2 : 1 / (((Finset.univ.sup N : ℕ) : ℝ) + 1) ≤ 1 / (((N j : ℕ) : ℝ) + 1) := by
      gcongr
    linarith [hN j]


theorem measurableSet_eigenvalue_eq {ν : ℕ} (Λ : Finset (Site ν)) (E : ℝ) :
    MeasurableSet
      {v : Configuration ν | ∃ j, (hamiltonian_isHermitian ν Λ v).eigenvalues j = E} := by
  rw [eigenvalue_eq_set_eq_iInter]
  exact MeasurableSet.iInter fun n => measurableSet_resonanceEvent ν Λ E _

private theorem measure_eigenvalue_eq_le {ν : ℕ} (μ : Measure (Configuration ν))
    (Λ : Finset (Site ν)) (E : ℝ) (n : ℕ) :
    μ {v | ∃ j, (hamiltonian_isHermitian ν Λ v).eigenvalues j = E} ≤
      μ (resonanceEvent ν Λ E (1 / ((n : ℝ) + 1))) := by
  rw [eigenvalue_eq_set_eq_iInter]
  exact measure_mono (Set.iInter_subset _ n)

private theorem tendsto_sqrt_mul_card (c : ℝ) (m : ℕ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (2 * (1 / ((n : ℝ) + 1))) * c) * m)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => Real.sqrt (2 * (1 / ((n : ℝ) + 1))) * c) atTop (𝓝 0) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2).sqrt.mul_const c
    simpa using this
  have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (b := (m : ℝ≥0∞))
    (Or.inr (by simp))
  simpa using h2


theorem configurationMeasure_eigenvalue_eq_boundedDensity {ν : ℕ} (law : Measure ℝ)
    [IsProbabilityMeasure law] {δ : ℝ} (hlaw : HasBoundedDensity law δ) (Λ : Finset (Site ν))
    (E : ℝ) :
    configurationMeasure ν law
      {v | ∃ j, (hamiltonian_isHermitian ν Λ v).eigenvalues j = E} = 0 := by
  refine le_antisymm (ge_of_tendsto' (tendsto_sqrt_mul_card (Real.sqrt δ⁻¹) Λ.card) fun n => ?_)
    bot_le
  exact (measure_eigenvalue_eq_le _ Λ E n).trans (resonance_bound_boundedDensity ν Λ law hlaw
    E _).2


theorem configurationMeasure_eigenvalue_eq_gaussian {ν : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (Λ : Finset (Site ν)) (E : ℝ) :
    configurationMeasure ν (gaussianLaw γ hγ)
      {v | ∃ j, (hamiltonian_isHermitian ν Λ v).eigenvalues j = E} = 0 := by
  refine le_antisymm (ge_of_tendsto' (tendsto_sqrt_mul_card (Real.sqrt (1 / Real.sqrt
    (2 * Real.pi * γ) * (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1})) Λ.card)
    fun n => ?_) bot_le
  have hκ : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact (measure_eigenvalue_eq_le _ Λ E n).trans (resonance_bound_gaussian ν Λ hγ E hκ).2

private theorem eigenvalue_exists_of_eq {ν : ℕ} (P : Params) (i : ℕ) (v : Site ν → ℝ)
    {F G : Finset (Site ν)}
    (h : F = G) (hF : ¬ ∀ j, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
      |(hamiltonian_isHermitian ν F v).eigenvalues j - P.E|) :
    ∃ j, |(hamiltonian_isHermitian ν G v).eigenvalues j - P.E| <
      Real.exp (-Real.sqrt (scaleD P.K₀ i)) := by
  subst h
  push Not at hF
  exact hF


theorem tendsto_scaleD_atTop {K₀ : ℝ} (hK : 0 < K₀) :
    Tendsto (scaleD K₀) atTop atTop := by
  unfold scaleD
  refine Real.tendsto_exp_atTop.comp ?_
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 5 / 4)).const_mul_atTop hK

private theorem tendsto_exp_neg_sqrt_scaleD {K₀ : ℝ} (hK : 0 < K₀) :
    Tendsto (fun i : ℕ => Real.exp (-Real.sqrt (scaleD K₀ i))) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (Real.tendsto_sqrt_atTop.comp (tendsto_scaleD_atTop hK)))

private theorem exists_bound_siteDist {ν : ℕ} (Λ : Finset (Site ν)) :
    ∃ D : ℝ, ∀ a ∈ Λ, ∀ b ∈ Λ, siteDist ν a b ≤ D := by
  refine ⟨∑ a ∈ Λ, ∑ b ∈ Λ, siteDist ν a b, fun a ha b hb => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b ∈ Λ, siteDist ν a b)
    (fun a _ => Finset.sum_nonneg fun b _ => siteDist_nonneg ν a b) ha)
  exact Finset.single_le_sum (f := fun b => siteDist ν a b)
    (fun b _ => siteDist_nonneg ν a b) hb


theorem eigenvalue_eq_of_forall_mem_singularSetsIn {ν : ℕ} (P : Params) (hK : 0 < P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) {x : Site ν}
    (hx : ∀ i, x ∈ singularSetsIn P Λ v i) :
    ∃ j, (hamiltonian_isHermitian ν Λ v).eigenvalues j = P.E := by
  classical
  obtain ⟨D, hD⟩ := exists_bound_siteDist Λ
  have hev : ∀ᶠ i in atTop, D ≤ scaleD P.K₀ i := (tendsto_scaleD_atTop hK).eventually_ge_atTop D
  have key : ∀ i, D ≤ scaleD P.K₀ i → ∃ j,
      |(hamiltonian_isHermitian ν Λ v).eigenvalues j - P.E| <
        Real.exp (-Real.sqrt (scaleD P.K₀ i)) := by
    intro i hi
    have hxΛ : x ∈ Λ := singularSetsIn_subset P v Λ 0 (hx 0)
    have hS := (mem_singularSetsGen_succ_iff P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v i x).1
      (hx (i + 1))
    set C := chainCluster (siteDist ν) (singularSetsIn P Λ v i) (2 * scaleR P.K₀ i) x with hC
    have hCsub : C ⊆ Λ := fun y hy =>
      singularSetsIn_subset P v Λ i (chainCluster_subset x hy)
    have hfin : C.Finite := (Λ.finite_toSet).subset hCsub
    have hxC : x ∈ C := mem_chainCluster_self (hx i)
    have hdiam : DiamLE (siteDist ν) C (scaleD P.K₀ i) := fun a ha b hb =>
      (hD a (hCsub ha) b (hCsub hb)).trans hi
    have hng := hS.2
    unfold IsGentle at hng
    have hng' : ¬ ∀ j, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
        |(hamiltonian_isHermitian ν ((fun B => B ∩ Λ) (thicken hfin.toFinset
          (4 * scaleD P.K₀ i))) v).eigenvalues j - P.E| := fun h => hng ⟨hfin, hdiam, h⟩
    refine eigenvalue_exists_of_eq P i v ?_ hng'
    ext y
    simp only [Finset.mem_inter, mem_thicken, Set.Finite.mem_toFinset]
    constructor
    · exact fun h => h.2
    · intro hy
      refine ⟨⟨x, hxC, ?_⟩, hy⟩
      have := hD y hy x hxΛ
      have h4 : D ≤ 4 * scaleD P.K₀ i := by linarith [scaleD_pos P.K₀ i]
      linarith
  by_contra hne
  push Not at hne
  have hsmall : ∀ᶠ i in atTop, ∀ j, Real.exp (-Real.sqrt (scaleD P.K₀ i)) ≤
      |(hamiltonian_isHermitian ν Λ v).eigenvalues j - P.E| := by
    rw [Filter.eventually_all]
    intro j
    exact (tendsto_exp_neg_sqrt_scaleD hK).eventually_le_const
      (abs_pos.2 (sub_ne_zero.2 (hne j)))
  obtain ⟨i, hi1, hi2⟩ := (hev.and hsmall).exists
  obtain ⟨j, hj⟩ := key i hi1
  exact absurd (hi2 j) (not_le.2 hj)


theorem measurableSet_forall_mem_singularSetsIn {ν : ℕ} (P : Params) (Λ : Finset (Site ν))
    (x : Site ν) : MeasurableSet {v : Configuration ν | ∀ i, x ∈ singularSetsIn P Λ v i} := by
  have : {v : Configuration ν | ∀ i, x ∈ singularSetsIn P Λ v i} =
      ⋂ i, {v : Configuration ν | x ∈ singularSetsIn P Λ v i} := by
    ext v; simp
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_mem_singularSetsIn P Λ x i


theorem measurableSet_residual {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) :
    MeasurableSet {v : Configuration ν | ∃ x, ∀ i, x ∈ singularSetsIn P Λ v i} := by
  have : {v : Configuration ν | ∃ x, ∀ i, x ∈ singularSetsIn P Λ v i} =
      ⋃ x : Site ν, {v : Configuration ν | ∀ i, x ∈ singularSetsIn P Λ v i} := by
    ext v; simp
  rw [this]
  exact MeasurableSet.iUnion fun x => measurableSet_forall_mem_singularSetsIn P Λ x

private theorem residual_subset {ν : ℕ} (P : Params) (hK : 0 < P.K₀) (Λ : Finset (Site ν)) :
    {v : Configuration ν | ∃ x, ∀ i, x ∈ singularSetsIn P Λ v i} ⊆
      {v | ∃ j, (hamiltonian_isHermitian ν Λ v).eigenvalues j = P.E} := by
  rintro v ⟨x, hx⟩
  exact eigenvalue_eq_of_forall_mem_singularSetsIn P hK Λ v hx


theorem configurationMeasure_residual_boundedDensity {ν : ℕ} (law : Measure ℝ)
    [IsProbabilityMeasure law] {δ : ℝ} (hlaw : HasBoundedDensity law δ) (P : Params)
    (hK : 0 < P.K₀) (Λ : Finset (Site ν)) :
    MeasurableSet {v : Configuration ν | ∃ x, ∀ i, x ∈ singularSetsIn P Λ v i} ∧
      configurationMeasure ν law {v | ∃ x, ∀ i, x ∈ singularSetsIn P Λ v i} = 0 :=
  ⟨measurableSet_residual P Λ, measure_mono_null (residual_subset P hK Λ)
    (configurationMeasure_eigenvalue_eq_boundedDensity law hlaw Λ P.E)⟩


theorem configurationMeasure_residual_gaussian {ν : ℕ} {γ : ℝ} (hγ : 0 < γ) (P : Params)
    (hK : 0 < P.K₀) (Λ : Finset (Site ν)) :
    MeasurableSet {v : Configuration ν | ∃ x, ∀ i, x ∈ singularSetsIn P Λ v i} ∧
      configurationMeasure ν (gaussianLaw γ hγ) {v | ∃ x, ∀ i, x ∈ singularSetsIn P Λ v i} = 0 :=
  ⟨measurableSet_residual P Λ, measure_mono_null (residual_subset P hK Λ)
    (configurationMeasure_eigenvalue_eq_gaussian hγ Λ P.E)⟩


theorem measurableSet_residual_finset {ν : ℕ} (P : Params) (Λ F : Finset (Site ν)) :
    MeasurableSet {v : Configuration ν | ∃ x ∈ F, ∀ i, x ∈ singularSetsIn P Λ v i} := by
  have : {v : Configuration ν | ∃ x ∈ F, ∀ i, x ∈ singularSetsIn P Λ v i} =
      ⋃ x ∈ F, {v : Configuration ν | ∀ i, x ∈ singularSetsIn P Λ v i} := by
    ext v; simp
  rw [this]
  exact Finset.measurableSet_biUnion F fun x _ => measurableSet_forall_mem_singularSetsIn P Λ x


theorem configurationMeasure_residual_finset_boundedDensity {ν : ℕ} (law : Measure ℝ)
    [IsProbabilityMeasure law] {δ : ℝ} (hlaw : HasBoundedDensity law δ) (P : Params)
    (hK : 0 < P.K₀) (Λ F : Finset (Site ν)) (x : Site ν) :
    (MeasurableSet {v : Configuration ν | ∀ i, x ∈ singularSetsIn P Λ v i} ∧
      configurationMeasure ν law {v | ∀ i, x ∈ singularSetsIn P Λ v i} = 0) ∧
    (MeasurableSet {v : Configuration ν | ∃ x ∈ F, ∀ i, x ∈ singularSetsIn P Λ v i} ∧
      configurationMeasure ν law {v | ∃ x ∈ F, ∀ i, x ∈ singularSetsIn P Λ v i} = 0) :=
  ⟨⟨measurableSet_forall_mem_singularSetsIn P Λ x, measure_mono_null (fun v hv => by exact ⟨x, hv⟩)
      (configurationMeasure_residual_boundedDensity law hlaw P hK Λ).2⟩,
    ⟨measurableSet_residual_finset P Λ F,
      measure_mono_null (fun v hv => by obtain ⟨y, -, hy⟩ := hv; exact ⟨y, hy⟩)
      (configurationMeasure_residual_boundedDensity law hlaw P hK Λ).2⟩⟩


theorem configurationMeasure_residual_finset_gaussian {ν : ℕ} {γ : ℝ} (hγ : 0 < γ) (P : Params)
    (hK : 0 < P.K₀) (Λ F : Finset (Site ν)) (x : Site ν) :
    (MeasurableSet {v : Configuration ν | ∀ i, x ∈ singularSetsIn P Λ v i} ∧
      configurationMeasure ν (gaussianLaw γ hγ) {v | ∀ i, x ∈ singularSetsIn P Λ v i} = 0) ∧
    (MeasurableSet {v : Configuration ν | ∃ x ∈ F, ∀ i, x ∈ singularSetsIn P Λ v i} ∧
      configurationMeasure ν (gaussianLaw γ hγ)
        {v | ∃ x ∈ F, ∀ i, x ∈ singularSetsIn P Λ v i} = 0) :=
  ⟨⟨measurableSet_forall_mem_singularSetsIn P Λ x, measure_mono_null (fun v hv => by exact ⟨x, hv⟩)
      (configurationMeasure_residual_gaussian hγ P hK Λ).2⟩,
    ⟨measurableSet_residual_finset P Λ F,
      measure_mono_null (fun v hv => by obtain ⟨y, -, hy⟩ := hv; exact ⟨y, hy⟩)
      (configurationMeasure_residual_gaussian hγ P hK Λ).2⟩⟩

end FroehlichSpencer.T12

end
