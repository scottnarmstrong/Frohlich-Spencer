/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Theorem22
public import FroehlichSpencer.T12.Residual
public import FroehlichSpencer.T12.Section5
public import FroehlichSpencer.Multiscale.Locality
public import FroehlichSpencer.Infra.Ergodic.Basic


@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.T12

open Multiscale


theorem mem_singularSetsIn_cases {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (v : Site ν → ℝ)
    {x : Site ν} {k : ℕ} (hx : x ∈ singularSetsIn P Λ v k) :
    (∀ i, x ∈ singularSetsIn P Λ v i) ∨
      ∃ s : ℕ, x ∈ gentlePart P (fun B => B ∩ Λ) (k + s) v (singularSetsIn P Λ v (k + s)) := by
  classical
  by_cases h : ∀ i, x ∈ singularSetsIn P Λ v i
  · exact Or.inl h
  right
  push Not at h
  have hex : ∃ i, x ∉ singularSetsIn P Λ v i := h
  set i := Nat.find hex with hi
  have hxi : x ∉ singularSetsIn P Λ v i := Nat.find_spec hex
  have hik : k < i := by
    by_contra hle
    push Not at hle
    exact hxi (singularSetsGen_antitone P _ _ v hle hx)
  obtain ⟨s, hs⟩ : ∃ s, i = k + s + 1 := ⟨i - k - 1, by omega⟩
  have hmin : x ∈ singularSetsIn P Λ v (k + s) := by
    have := Nat.find_min hex (m := k + s) (by omega)
    simpa using this
  refine ⟨s, ?_⟩
  rw [hs] at hxi
  by_contra hng
  exact hxi ⟨hmin, hng⟩


theorem card_filter_siteDist_le {ν : ℕ} (Λ : Finset (Site ν)) (a : Site ν) {R : ℝ} (hR : 1 ≤ R) :
    ((Λ.filter fun x => siteDist ν a x ≤ R).card : ℝ) ≤ (5 * R) ^ ν := by
  classical
  have hmaps : ∀ x ∈ Λ.filter (fun x => siteDist ν a x ≤ R),
      (x - a) ∈ Infra.cube ν ⌈R⌉₊ := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Infra.mem_cube]
    intro i
    have h1 : |((x i - a i : ℤ) : ℝ)| ≤ R := by
      have hd : |((x i - a i : ℤ) : ℝ)| ≤ siteDist ν a x := by
        rw [siteDist_comm]
        unfold siteDist latticeLength
        apply Real.abs_le_sqrt
        have := Finset.single_le_sum (f := fun j : Fin ν => (((x - a) j : ℤ) : ℝ) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        simpa using this
      exact hd.trans hx.2
    have h2 : |x i - a i| ≤ (⌈R⌉₊ : ℤ) := by
      have : (|x i - a i| : ℤ) ≤ ⌈R⌉₊ := by
        have h3 : ((|x i - a i| : ℤ) : ℝ) ≤ ⌈R⌉₊ := by
          push_cast at h1 ⊢; exact h1.trans (Nat.le_ceil R)
        exact_mod_cast h3
      exact this
    have := abs_le.1 h2
    simpa using this
  have hinj : Set.InjOn (fun x : Site ν => x - a)
      (Λ.filter (fun x => siteDist ν a x ≤ R) : Set (Site ν)) := by
    intro x _ y _ h
    simpa using h
  have hcard : (Λ.filter fun x => siteDist ν a x ≤ R).card ≤ (2 * ⌈R⌉₊ + 1) ^ ν := by
    rw [← Infra.card_cube ν ⌈R⌉₊]
    exact Finset.card_le_card_of_injOn (fun x => x - a) hmaps hinj
  have hceil : (⌈R⌉₊ : ℝ) < R + 1 := Nat.ceil_lt_add_one (by linarith)
  calc ((Λ.filter fun x => siteDist ν a x ≤ R).card : ℝ)
      ≤ (((2 * ⌈R⌉₊ + 1) ^ ν : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (2 * (⌈R⌉₊ : ℝ) + 1) ^ ν := by push_cast; ring
    _ ≤ (5 * R) ^ ν := by
      apply pow_le_pow_left₀ (by positivity)
      linarith

private theorem summable_scaleD_rpow_neg {K₀ q : ℝ} (hK : 0 < K₀) (hq : 0 < q) (k : ℕ) :
    Summable fun s : ℕ => scaleD K₀ (k + s) ^ (-q) := by
  set r : ℝ := Real.exp (-(q * K₀ / 4)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    have := mul_pos hq hK
    exact Real.exp_lt_exp.2 (by linarith)
  have hterm : ∀ s : ℕ, scaleD K₀ (k + s) ^ (-q) ≤ r ^ s := by
    intro s
    have e : ∀ n : ℕ, scaleD K₀ n ^ (-q) = Real.exp (-(q * (K₀ * (5 / 4 : ℝ) ^ n))) := by
      intro n
      unfold scaleD
      rw [← Real.exp_mul]
      congr 1
      ring
    rw [e, hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hb : (1 : ℝ) + s * (1 / 4) ≤ (1 + 1 / 4) ^ s :=
      one_add_mul_le_pow (by norm_num) s
    have hk1 : (1 : ℝ) ≤ (5 / 4) ^ k := one_le_pow₀ (by norm_num)
    have hpow : (5 / 4 : ℝ) ^ (k + s) = (5 / 4) ^ k * (5 / 4) ^ s := pow_add _ _ _
    have h54 : (1 + 1 / 4 : ℝ) = 5 / 4 := by norm_num
    rw [h54] at hb
    have hKq : 0 < q * K₀ := mul_pos hq hK
    have h1 : (5 / 4 : ℝ) ^ k * (1 + s * (1 / 4)) ≤ (5 / 4) ^ (k + s) := by
      rw [hpow]; exact mul_le_mul_of_nonneg_left hb (by positivity)
    have h2 : (1 : ℝ) + s / 4 ≤ (5 / 4) ^ k * (1 + s * (1 / 4)) := by
      have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) hKq.le
    nlinarith
  exact Summable.of_nonneg_of_le (fun s => Real.rpow_nonneg (scaleD_pos _ _).le _) hterm
    (summable_geometric_of_lt_one hr0 hr1)

private theorem measure_mem_singularSetsIn_le {ν : ℕ} (μ : Measure (Configuration ν))
    {K₀ : ℝ} (hK : 0 < K₀) {q : ℝ} (hq : 0 < q) (P : Params) (Λ : Finset (Site ν))
    (x : Site ν) (k : ℕ)
    (hres : μ {v | ∃ y, ∀ i, y ∈ singularSetsIn P Λ v i} = 0)
    (hg : ∀ j, k ≤ j → μ {v | x ∈ gentlePart P (fun B => B ∩ Λ) j v (singularSetsIn P Λ v j)} ≤
      ENNReal.ofReal (scaleD K₀ j ^ (-q))) :
    μ {v | x ∈ singularSetsIn P Λ v k} ≤
      ENNReal.ofReal ((1 - Real.exp (-(q * K₀ / 4)))⁻¹ * scaleD K₀ k ^ (-q)) := by
  have hsub : {v : Configuration ν | x ∈ singularSetsIn P Λ v k} ⊆
      {v | ∃ y, ∀ i, y ∈ singularSetsIn P Λ v i} ∪
        ⋃ s : ℕ, {v | x ∈ gentlePart P (fun B => B ∩ Λ) (k + s) v
          (singularSetsIn P Λ v (k + s))} := by
    intro v hv
    rcases mem_singularSetsIn_cases P Λ v hv with h | ⟨s, hs⟩
    · exact Or.inl ⟨x, h⟩
    · exact Or.inr (Set.mem_iUnion.2 ⟨s, hs⟩)
  have hnn : ∀ s : ℕ, 0 ≤ scaleD K₀ (k + s) ^ (-q) := fun s =>
    Real.rpow_nonneg (scaleD_pos _ _).le _
  calc μ {v | x ∈ singularSetsIn P Λ v k}
      ≤ μ ({v | ∃ y, ∀ i, y ∈ singularSetsIn P Λ v i} ∪
        ⋃ s : ℕ, {v | x ∈ gentlePart P (fun B => B ∩ Λ) (k + s) v
          (singularSetsIn P Λ v (k + s))}) := measure_mono hsub
    _ ≤ μ {v | ∃ y, ∀ i, y ∈ singularSetsIn P Λ v i} +
        μ (⋃ s : ℕ, {v | x ∈ gentlePart P (fun B => B ∩ Λ) (k + s) v
          (singularSetsIn P Λ v (k + s))}) := measure_union_le _ _
    _ ≤ 0 + ∑' s : ℕ, ENNReal.ofReal (scaleD K₀ (k + s) ^ (-q)) := by
        rw [hres]
        exact add_le_add le_rfl ((measure_iUnion_le _).trans
          (ENNReal.tsum_le_tsum fun s => hg (k + s) (by omega)))
    _ = ENNReal.ofReal (∑' s : ℕ, scaleD K₀ (k + s) ^ (-q)) := by
        rw [zero_add, ENNReal.ofReal_tsum_of_nonneg hnn (summable_scaleD_rpow_neg hK hq k)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (tsum_scaleD_rpow_neg_le hK hq k)


theorem exists_mem_singularSetsIn_le_boundedDensity (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) {q : ℝ}
    (hq : 0 < q) :
    ∃ δ₀ C : ℝ, ∀ (law : Measure ℝ) [IsProbabilityMeasure law] (δ : ℝ), HasBoundedDensity law δ →
      δ₀ ≤ δ → ∀ (P : Params), P.K₀ = K₀ → P.Nthr = Real.sqrt δ →
        ∀ (Λ : Finset (Site ν)) (x : Site ν) (k : ℕ), 1 ≤ k →
          MeasurableSet {v : Configuration ν | x ∈ singularSetsIn P Λ v k} ∧
            configurationMeasure ν law {v | x ∈ singularSetsIn P Λ v k} ≤
              ENNReal.ofReal (C * scaleD K₀ k ^ (-q)) := by
  obtain ⟨δ₀, h⟩ := exists_threshold_gentlePart_le_boundedDensity ν hK hq
  refine ⟨δ₀, (1 - Real.exp (-(q * K₀ / 4)))⁻¹, fun law _ δ hlaw hδ P hP hN Λ x k hk => ?_⟩
  refine ⟨measurableSet_mem_singularSetsIn P Λ x k, ?_⟩
  refine measure_mem_singularSetsIn_le _ hK hq P Λ x k ?_ fun j hj =>
    (h law δ hlaw hδ P hP hN Λ x j (hk.trans hj)).2
  exact (configurationMeasure_residual_boundedDensity law hlaw P (hP ▸ hK) Λ).2


theorem exists_mem_singularSetsIn_le_gaussian (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) {γ : ℝ}
    (hγ : 0 < γ) {q : ℝ} (hq : 0 < q) :
    ∃ E₀ C : ℝ, ∀ (P : Params), P.K₀ = K₀ → E₀ ≤ |P.E - 2 * ν| → P.Nthr = |P.E| / 2 →
      ∀ (Λ : Finset (Site ν)) (x : Site ν) (k : ℕ), 1 ≤ k →
        MeasurableSet {v : Configuration ν | x ∈ singularSetsIn P Λ v k} ∧
          configurationMeasure ν (gaussianLaw γ hγ) {v | x ∈ singularSetsIn P Λ v k} ≤
            ENNReal.ofReal (C * scaleD K₀ k ^ (-q)) := by
  obtain ⟨E₀, h⟩ := exists_threshold_gentlePart_le_gaussian ν hK hγ hq
  refine ⟨E₀, (1 - Real.exp (-(q * K₀ / 4)))⁻¹, fun P hP hE hN Λ x k hk => ?_⟩
  refine ⟨measurableSet_mem_singularSetsIn P Λ x k, ?_⟩
  refine measure_mem_singularSetsIn_le _ hK hq P Λ x k ?_ fun j hj =>
    (h P hP hE hN Λ x j (hk.trans hj)).2
  exact (configurationMeasure_residual_gaussian hγ P (hP ▸ hK) Λ).2


theorem measurableSet_ballEvent {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (a : Site ν) (R : ℝ)
    (k : ℕ) :
    MeasurableSet {v : Configuration ν | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} := by
  have : {v : Configuration ν | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} =
      ⋃ x : Site ν, {v : Configuration ν | siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} := by
    ext v; simp
  rw [this]
  refine MeasurableSet.iUnion fun x => ?_
  by_cases h : siteDist ν a x ≤ R
  · simpa [h] using measurableSet_mem_singularSetsIn P Λ x k
  · simp [h]


theorem ballEvent_congr {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (a : Site ν) (R : ℝ) (k : ℕ)
    {v w : Site ν → ℝ} (h : ∀ y, siteDist ν a y ≤ R + localityRadius P.K₀ k → v y = w y) :
    (∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k) ↔
      ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ w k := by
  constructor
  · rintro ⟨x, hx, hv⟩
    refine ⟨x, hx, (mem_singularSetsIn_congr P Λ (fun y hy => h y ?_)).1 hv⟩
    linarith [siteDist_triangle ν a y x, siteDist_comm ν x y]
  · rintro ⟨x, hx, hw⟩
    refine ⟨x, hx, (mem_singularSetsIn_congr P Λ (fun y hy => h y ?_)).2 hw⟩
    linarith [siteDist_triangle ν a y x, siteDist_comm ν x y]

private theorem measure_ballEvent_le {ν : ℕ} (μ : Measure (Configuration ν)) (P : Params)
    (Λ : Finset (Site ν)) (a : Site ν) {R : ℝ} (hR : 1 ≤ R) (k : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, μ {v | x ∈ singularSetsIn P Λ v k} ≤ ENNReal.ofReal c) :
    μ {v | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} ≤
      ENNReal.ofReal (5 ^ ν * R ^ ν * c) := by
  classical
  have hsub : {v : Configuration ν | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} ⊆
      ⋃ x ∈ Λ.filter (fun x => siteDist ν a x ≤ R), {v | x ∈ singularSetsIn P Λ v k} := by
    rintro v ⟨x, hx, hv⟩
    simp only [Set.mem_iUnion, Finset.mem_filter]
    exact ⟨x, ⟨singularSetsIn_subset P v Λ k hv, hx⟩, hv⟩
  calc μ {v | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k}
      ≤ μ (⋃ x ∈ Λ.filter (fun x => siteDist ν a x ≤ R), {v | x ∈ singularSetsIn P Λ v k}) :=
        measure_mono hsub
    _ ≤ ∑ x ∈ Λ.filter (fun x => siteDist ν a x ≤ R), μ {v | x ∈ singularSetsIn P Λ v k} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ Λ.filter (fun x => siteDist ν a x ≤ R), ENNReal.ofReal c :=
        Finset.sum_le_sum fun x _ => h x
    _ = ENNReal.ofReal (((Λ.filter fun x => siteDist ν a x ≤ R).card : ℝ) * c) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
    _ ≤ ENNReal.ofReal (5 ^ ν * R ^ ν * c) := by
        apply ENNReal.ofReal_le_ofReal
        have := card_filter_siteDist_le Λ a hR
        rw [mul_pow] at this
        exact mul_le_mul_of_nonneg_right this hc


theorem exists_ballEvent_le_boundedDensity (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) {q : ℝ} (hq : 0 < q) :
    ∃ δ₀ C : ℝ, ∀ (law : Measure ℝ) [IsProbabilityMeasure law] (δ : ℝ), HasBoundedDensity law δ →
      δ₀ ≤ δ → ∀ (P : Params), P.K₀ = K₀ → P.Nthr = Real.sqrt δ →
        ∀ (Λ : Finset (Site ν)) (a : Site ν) (R : ℝ) (k : ℕ), 1 ≤ k → 1 ≤ R →
          MeasurableSet
              {v : Configuration ν | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} ∧
            configurationMeasure ν law
                {v | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} ≤
              ENNReal.ofReal (C * R ^ ν * scaleD K₀ k ^ (-q)) := by
  obtain ⟨δ₀, h⟩ := exists_threshold_gentlePart_le_boundedDensity ν hK hq
  have hC : 0 ≤ (1 - Real.exp (-(q * K₀ / 4)))⁻¹ := by
    have : Real.exp (-(q * K₀ / 4)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by have := mul_pos hq hK; linarith)
    exact (inv_pos.2 (by linarith)).le
  refine ⟨δ₀, 5 ^ ν * (1 - Real.exp (-(q * K₀ / 4)))⁻¹,
    fun law _ δ hlaw hδ P hP hN Λ a R k hk hR => ?_⟩
  refine ⟨measurableSet_ballEvent P Λ a R k, ?_⟩
  have hs : ∀ x, configurationMeasure ν law {v | x ∈ singularSetsIn P Λ v k} ≤
      ENNReal.ofReal ((1 - Real.exp (-(q * K₀ / 4)))⁻¹ * scaleD K₀ k ^ (-q)) := fun x =>
    measure_mem_singularSetsIn_le _ hK hq P Λ x k
      (configurationMeasure_residual_boundedDensity law hlaw P (hP ▸ hK) Λ).2 fun j hj =>
      (h law δ hlaw hδ P hP hN Λ x j (hk.trans hj)).2
  have := measure_ballEvent_le (configurationMeasure ν law) P Λ a hR k
    (mul_nonneg hC (Real.rpow_nonneg (scaleD_pos _ _).le _)) hs
  convert this using 2
  ring


theorem exists_ballEvent_le_gaussian (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) {γ : ℝ} (hγ : 0 < γ)
    {q : ℝ} (hq : 0 < q) :
    ∃ E₀ C : ℝ, ∀ (P : Params), P.K₀ = K₀ → E₀ ≤ |P.E - 2 * ν| → P.Nthr = |P.E| / 2 →
      ∀ (Λ : Finset (Site ν)) (a : Site ν) (R : ℝ) (k : ℕ), 1 ≤ k → 1 ≤ R →
        MeasurableSet
            {v : Configuration ν | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} ∧
          configurationMeasure ν (gaussianLaw γ hγ)
              {v | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} ≤
            ENNReal.ofReal (C * R ^ ν * scaleD K₀ k ^ (-q)) := by
  obtain ⟨E₀, h⟩ := exists_threshold_gentlePart_le_gaussian ν hK hγ hq
  have hC : 0 ≤ (1 - Real.exp (-(q * K₀ / 4)))⁻¹ := by
    have : Real.exp (-(q * K₀ / 4)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by have := mul_pos hq hK; linarith)
    exact (inv_pos.2 (by linarith)).le
  refine ⟨E₀, 5 ^ ν * (1 - Real.exp (-(q * K₀ / 4)))⁻¹,
    fun P hP hE hN Λ a R k hk hR => ?_⟩
  refine ⟨measurableSet_ballEvent P Λ a R k, ?_⟩
  have hs : ∀ x, configurationMeasure ν (gaussianLaw γ hγ) {v | x ∈ singularSetsIn P Λ v k} ≤
      ENNReal.ofReal ((1 - Real.exp (-(q * K₀ / 4)))⁻¹ * scaleD K₀ k ^ (-q)) := fun x =>
    measure_mem_singularSetsIn_le _ hK hq P Λ x k
      (configurationMeasure_residual_gaussian hγ P (hP ▸ hK) Λ).2 fun j hj =>
      (h P hP hE hN Λ x j (hk.trans hj)).2
  have := measure_ballEvent_le (configurationMeasure ν (gaussianLaw γ hγ)) P Λ a hR k
    (mul_nonneg hC (Real.rpow_nonneg (scaleD_pos _ _).le _)) hs
  convert this using 2
  ring

end FroehlichSpencer.T12

end
