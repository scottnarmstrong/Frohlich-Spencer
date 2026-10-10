/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Ergodic.MaximalDiscrete

/-!
# Wiener maximal inequality for cube averages on `ℤ^ν`

For a nonnegative integrable `f` on `(ℤ^ν → ℝ, productMeasure μ)` and `t > 0`,
`P {v | ∃ L, t < cubeAverage f L v} ≤ 3^ν ∫ f / t`.

It follows from the discrete maximal
inequality `mul_card_maximal_le` by Calderón's transference principle, using stationarity of the
product measure under lattice shifts.

Motivation: the ergodic theorem behind the integrated density
of states of Fröhlich–Spencer (1983), Fröhlich–Spencer (1983).
-/

@[expose] public section

open MeasureTheory Finset
open scoped Pointwise Topology

namespace FroehlichSpencer.Infra

variable {ν : ℕ}

/-- Truncated maximal set. -/
private def maxSet (f : ((Fin ν → ℤ) → ℝ) → ℝ) (t : ℝ) (L₀ : ℕ) : Set ((Fin ν → ℤ) → ℝ) :=
  {v | ∃ L ≤ L₀, t < cubeAverage f L v}

private theorem measurableSet_maxSet {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Measurable f) (t : ℝ)
    (L₀ : ℕ) : MeasurableSet (maxSet f t L₀) := by
  have : maxSet f t L₀ = ⋃ L ∈ Finset.range (L₀ + 1), {v | t < cubeAverage f L v} := by
    ext v
    simp only [maxSet, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨L, hL, h⟩
      exact ⟨L, by omega, h⟩
    · rintro ⟨L, hL, h⟩
      exact ⟨L, by omega, h⟩
  rw [this]
  exact Finset.measurableSet_biUnion _ fun L _ =>
    measurableSet_lt measurable_const (measurable_cubeAverage hf L)

private theorem add_cube_subset (R L₀ : ℕ) : cube ν R + cube ν L₀ ⊆ cube ν (R + L₀) := by
  intro z hz
  rw [Finset.mem_add] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  rw [mem_cube] at hx hy ⊢
  intro i
  have h1 := hx i
  have h2 := hy i
  simp only [Pi.add_apply]
  push_cast
  constructor <;> omega

/-- Transference for a fixed radius of centres `R`. -/
private theorem transfer_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ v, 0 ≤ f v)
    (hfi : Integrable f (productMeasure μ)) {t : ℝ} (ht : 0 < t) (L₀ R : ℕ) :
    t * ((2 * R + 1 : ℝ) ^ ν * (productMeasure μ).real (maxSet f t L₀)) ≤
      3 ^ ν * ((2 * (R + L₀) + 1 : ℝ) ^ ν * ∫ v, f v ∂productMeasure μ) := by
  classical
  set P := productMeasure μ
  set E := maxSet f t L₀ with hE
  have hEm : MeasurableSet E := measurableSet_maxSet hf t L₀
  set B := cube ν R
  set g : ((Fin ν → ℤ) → ℝ) → ℝ :=
    fun v => ∑ x ∈ B, E.indicator (fun _ => (1 : ℝ)) (latticeShift x v) with hg
  have hind : ∀ x, Integrable (fun v => E.indicator (fun _ => (1 : ℝ)) (latticeShift x v)) P := by
    intro x
    have h1 : Integrable (E.indicator (fun _ => (1 : ℝ))) P :=
      (integrable_const (1 : ℝ)).indicator hEm
    exact (measurePreserving_latticeShift μ x).integrable_comp_of_integrable h1
  have hgint : ∫ v, g v ∂P = (B.card : ℝ) * P.real E := by
    rw [hg, integral_finsetSum _ (fun x _ => hind x)]
    have : ∀ x ∈ B, ∫ v, E.indicator (fun _ => (1 : ℝ)) (latticeShift x v) ∂P = P.real E := by
      intro x _
      rw [integral_comp_latticeShift μ x (E.indicator (fun _ => (1 : ℝ)))]
      rw [integral_indicator hEm]
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
      rfl
    rw [Finset.sum_congr rfl this]
    simp
  have hpt : ∀ v, t * g v ≤ 3 ^ ν * ∑ y ∈ B + cube ν L₀, f (latticeShift y v) := by
    intro v
    have h := mul_card_maximal_le (φ := fun z => f (latticeShift z v)) (fun z => hf0 _) B L₀ ht
    have hcount : g v = (#{x ∈ B | ∃ L ≤ L₀, t < ((cube ν L).card : ℝ)⁻¹ *
        ∑ y ∈ cube ν L, f (latticeShift (x + y) v)} : ℝ) := by
      rw [hg]
      simp only [Set.indicator_apply]
      rw [Finset.sum_boole]
      congr 2
      apply Finset.filter_congr
      intro x _
      simp only [hE, maxSet, Set.mem_ofPred_eq, cubeAverage, latticeShift_latticeShift]
      constructor <;> rintro ⟨L, hL, h⟩ <;> refine ⟨L, hL, ?_⟩ <;>
        simpa only [add_comm] using h
    rw [hcount]
    exact h
  have hfs : ∀ y, Integrable (fun v => f (latticeShift y v)) P := fun y =>
    (measurePreserving_latticeShift μ y).integrable_comp_of_integrable hfi
  have hgi : Integrable g P := integrable_finsetSum _ fun x _ => hind x
  have hint : t * ∫ v, g v ∂P ≤ 3 ^ ν * ∑ y ∈ B + cube ν L₀, ∫ v, f v ∂P := by
    calc t * ∫ v, g v ∂P = ∫ v, t * g v ∂P := (integral_const_mul _ _).symm
      _ ≤ ∫ v, 3 ^ ν * ∑ y ∈ B + cube ν L₀, f (latticeShift y v) ∂P :=
          integral_mono (hgi.const_mul t)
            ((integrable_finsetSum _ fun y _ => hfs y).const_mul _) hpt
      _ = 3 ^ ν * ∑ y ∈ B + cube ν L₀, ∫ v, f v ∂P := by
          rw [integral_const_mul, integral_finsetSum _ (fun y _ => hfs y)]
          congr 1
          exact Finset.sum_congr rfl fun y _ => integral_comp_latticeShift μ y f
  have hI : 0 ≤ ∫ v, f v ∂P := integral_nonneg hf0
  have hcard : (((B + cube ν L₀).card : ℕ) : ℝ) ≤ ((cube ν (R + L₀)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (add_cube_subset R L₀)
  rw [hgint] at hint
  rw [Finset.sum_const, nsmul_eq_mul] at hint
  have hB : (B.card : ℝ) = (2 * R + 1 : ℝ) ^ ν := by
    rw [card_cube]; push_cast; ring
  have hB' : ((cube ν (R + L₀)).card : ℝ) = (2 * (R + L₀) + 1 : ℝ) ^ ν := by
    rw [card_cube]; push_cast; ring
  rw [hB] at hint
  rw [hB'] at hcard
  calc t * ((2 * R + 1 : ℝ) ^ ν * P.real E)
        ≤ 3 ^ ν * (((B + cube ν L₀).card : ℝ) * ∫ v, f v ∂P) := by linarith only [hint]
    _ ≤ 3 ^ ν * ((2 * (R + L₀) + 1 : ℝ) ^ ν * ∫ v, f v ∂P) := by gcongr

private theorem real_maxSet_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ v, 0 ≤ f v)
    (hfi : Integrable f (productMeasure μ)) {t : ℝ} (ht : 0 < t) (L₀ : ℕ) :
    (productMeasure μ).real (maxSet f t L₀) ≤ 3 ^ ν * (∫ v, f v ∂productMeasure μ) / t := by
  set I := ∫ v, f v ∂productMeasure μ
  set M := (productMeasure μ).real (maxSet f t L₀)
  have hI : 0 ≤ I := integral_nonneg hf0
  have hM : 0 ≤ M := measureReal_nonneg
  rw [le_div_iff₀ ht]
  have key : ∀ R : ℕ, M * t ≤ 3 ^ ν * I * (1 + 2 * (L₀ : ℝ) / (2 * R + 1)) ^ ν := by
    intro R
    have h := transfer_bound μ hf hf0 hfi ht L₀ R
    have hp : (0 : ℝ) < (2 * R + 1) ^ ν := by positivity
    have e : (2 * ((R : ℝ) + L₀) + 1) ^ ν =
        (2 * R + 1) ^ ν * (1 + 2 * (L₀ : ℝ) / (2 * R + 1)) ^ ν := by
      rw [← mul_pow]
      congr 1
      field_simp
      ring
    rw [e] at h
    have : (2 * R + 1 : ℝ) ^ ν * (M * t) ≤ (2 * R + 1 : ℝ) ^ ν *
        (3 ^ ν * I * (1 + 2 * (L₀ : ℝ) / (2 * R + 1)) ^ ν) := by
      linarith only [h]
    exact le_of_mul_le_mul_left this hp
  have hlim : Filter.Tendsto
      (fun R : ℕ => 3 ^ ν * I * (1 + 2 * (L₀ : ℝ) / (2 * R + 1)) ^ ν) Filter.atTop
      (𝓝 (3 ^ ν * I * (1 + 0) ^ ν)) := by
    have h0 : Filter.Tendsto (fun R : ℕ => 2 * (L₀ : ℝ) / (2 * R + 1)) Filter.atTop (𝓝 0) := by
      refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      refine Filter.tendsto_atTop_add_const_right _ _ ?_
      exact Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    exact (((tendsto_const_nhds.add h0).pow ν).const_mul _)
  have := ge_of_tendsto hlim (Filter.Eventually.of_forall key)
  simpa using this

/-- **Wiener maximal inequality** for cube averages: for nonnegative integrable `f`,
`P {v | ∃ L, t < A_L f v} ≤ 3^ν ∫ f / t`. -/
theorem measure_exists_lt_cubeAverage_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ v, 0 ≤ f v)
    (hfi : Integrable f (productMeasure μ)) {t : ℝ} (ht : 0 < t) :
    productMeasure μ {v | ∃ L, t < cubeAverage f L v} ≤
      ENNReal.ofReal (3 ^ ν * (∫ v, f v ∂productMeasure μ) / t) := by
  have hmono : Monotone (maxSet f t) := by
    intro a b hab v ⟨L, hL, h⟩
    exact ⟨L, hL.trans hab, h⟩
  have hU : {v | ∃ L, t < cubeAverage f L v} = ⋃ n, maxSet f t n := by
    ext v
    simp only [maxSet, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨L, h⟩
      exact ⟨L, L, le_rfl, h⟩
    · rintro ⟨n, L, _, h⟩
      exact ⟨L, h⟩
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (real_maxSet_le μ hf hf0 hfi ht n)

end FroehlichSpencer.Infra
