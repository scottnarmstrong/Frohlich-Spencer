/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Events
public import FroehlichSpencer.T12.Section5
public import FroehlichSpencer.T12.Theorem51
public import FroehlichSpencer.T12.Entropy
public import FroehlichSpencer.T12.Cubes
public import FroehlichSpencer.Multiscale.Measurability

/-!
# Probability of a gentle singular component

FS83 Theorem 2.2: in the bounded-density large-disorder and Gaussian high-energy regimes, the probability of membership in a gentle singular component decays as a prescribed power of the scale, uniformly in the site and finite volume. Measurability is included.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.T12

open Multiscale

/-! ### Real-variable estimates -/

private theorem poly_exp_half_le (N : ℕ) {d : ℝ} (hd : 0 ≤ d) :
    (1 + d) ^ N * Real.exp (-Real.sqrt d / 2) ≤
      4 ^ (2 * N) * (2 * N).factorial * Real.exp (1 / 4) := by
  set s := Real.sqrt d with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg d
  have hds : d = s ^ 2 := (Real.sq_sqrt hd).symm
  have h1 : (1 + d) ^ N ≤ (1 + s) ^ (2 * N) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    rw [hds]; nlinarith only [hs0]
  have h2 := Real.pow_div_factorial_le_exp ((1 + s) / 4) (by positivity) (2 * N)
  have hf : (0 : ℝ) < (2 * N).factorial := by exact_mod_cast Nat.factorial_pos _
  have h3 : (1 + s) ^ (2 * N) ≤ 4 ^ (2 * N) * (2 * N).factorial * Real.exp ((1 + s) / 4) := by
    rw [div_pow, div_le_iff₀ hf] at h2
    have : (4 : ℝ) ^ (2 * N) > 0 := by positivity
    rw [div_le_iff₀ this] at h2
    linarith only [h2]
  have h4 : Real.exp ((1 + s) / 4) * Real.exp (-s / 2) ≤ Real.exp (1 / 4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith only [hs0]
  calc (1 + d) ^ N * Real.exp (-s / 2)
      ≤ (4 ^ (2 * N) * (2 * N).factorial * Real.exp ((1 + s) / 4)) * Real.exp (-s / 2) := by
        gcongr; exact h1.trans h3
    _ = 4 ^ (2 * N) * (2 * N).factorial * (Real.exp ((1 + s) / 4) * Real.exp (-s / 2)) := by
        ring
    _ ≤ _ := by gcongr

private theorem exists_poly_rpow_exp_le (ν : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ∃ M : ℝ, 0 < M ∧ ∀ d : ℝ, 0 ≤ d →
      (1 + d) ^ ν * d ^ p * Real.exp (-Real.sqrt d / 2) ≤ M := by
  obtain ⟨m, hm⟩ := exists_nat_ge p
  refine ⟨4 ^ (2 * (ν + m)) * (2 * (ν + m)).factorial * Real.exp (1 / 4), by positivity,
    fun d hd => ?_⟩
  have h1 : d ^ p ≤ (1 + d) ^ m := by
    calc d ^ p ≤ (1 + d) ^ p := Real.rpow_le_rpow hd (by linarith only []) hp
      _ ≤ (1 + d) ^ (m : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hd]) hm
      _ = (1 + d) ^ m := Real.rpow_natCast _ _
  have h2 := poly_exp_half_le (ν + m) hd
  calc (1 + d) ^ ν * d ^ p * Real.exp (-Real.sqrt d / 2)
      ≤ (1 + d) ^ ν * (1 + d) ^ m * Real.exp (-Real.sqrt d / 2) := by gcongr
    _ = (1 + d) ^ (ν + m) * Real.exp (-Real.sqrt d / 2) := by rw [pow_add]
    _ ≤ _ := h2

private theorem scaleD_succ_rpow_neg {K₀ q : ℝ} (i : ℕ) :
    scaleD K₀ (i + 1) ^ (-q) = Real.exp (-((5 * q / 4) * (K₀ * (5 / 4 : ℝ) ^ i))) := by
  unfold scaleD
  rw [← Real.exp_mul]
  congr 1
  rw [pow_succ]
  ring

private theorem exists_rho_const (ν : ℕ) (K₀ : ℝ) {q : ℝ} (hq : 0 < q) :
    ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρ₁ → ∀ i : ℕ,
      Real.sqrt 2 * ρ * (11 ^ ν * (1 + scaleD K₀ i) ^ ν) *
          Real.exp (-Real.sqrt (scaleD K₀ i) / 2) ≤
        (scaleD K₀ (i + 1) ^ (-q) / 4) ^ 2 := by
  obtain ⟨M, hM, hMb⟩ := exists_poly_rpow_exp_le ν (p := 5 * q / 2) (by positivity)
  have hc : 0 < 16 * (Real.sqrt 2 * 11 ^ ν * M) := by positivity
  refine ⟨(16 * (Real.sqrt 2 * 11 ^ ν * M))⁻¹, by positivity, fun ρ hρ0 hρ i => ?_⟩
  set d := scaleD K₀ i with hd
  have hd0 : 0 < d := scaleD_pos K₀ i
  have hdu : d = Real.exp (K₀ * (5 / 4 : ℝ) ^ i) := rfl
  have hrhs : (scaleD K₀ (i + 1) ^ (-q) / 4) ^ 2 = 1 / (16 * d ^ (5 * q / 2)) := by
    rw [scaleD_succ_rpow_neg, hdu, ← Real.exp_mul, div_pow, ← Real.exp_nat_mul]
    have h : Real.exp (((2 : ℕ) : ℝ) * -(5 * q / 4 * (K₀ * (5 / 4 : ℝ) ^ i))) =
        (Real.exp (K₀ * (5 / 4 : ℝ) ^ i * (5 * q / 2)))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; push_cast; ring
    rw [h]
    have : (0 : ℝ) < Real.exp (K₀ * (5 / 4 : ℝ) ^ i * (5 * q / 2)) := Real.exp_pos _
    field_simp
    norm_num
  rw [hrhs, le_div_iff₀ (by positivity)]
  have hb := hMb d hd0.le
  have hK : 0 < Real.sqrt 2 * 11 ^ ν := by positivity
  have h1 : Real.sqrt 2 * ρ * (11 ^ ν * (1 + d) ^ ν) * Real.exp (-Real.sqrt d / 2) *
      (16 * d ^ (5 * q / 2)) =
      16 * (Real.sqrt 2 * 11 ^ ν * ρ) *
        ((1 + d) ^ ν * d ^ (5 * q / 2) * Real.exp (-Real.sqrt d / 2)) := by ring
  rw [h1]
  have hKρ : Real.sqrt 2 * 11 ^ ν * ρ ≤ (16 * M)⁻¹ := by
    have e : Real.sqrt 2 * 11 ^ ν * (16 * (Real.sqrt 2 * 11 ^ ν * M))⁻¹ = (16 * M)⁻¹ := by
      field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_left hρ hK.le
  have hB : 0 ≤ (1 + d) ^ ν * d ^ (5 * q / 2) * Real.exp (-Real.sqrt d / 2) := by positivity
  calc 16 * (Real.sqrt 2 * 11 ^ ν * ρ) *
        ((1 + d) ^ ν * d ^ (5 * q / 2) * Real.exp (-Real.sqrt d / 2))
      ≤ 16 * (16 * M)⁻¹ * M := by gcongr
    _ = 1 := by field_simp


theorem scaleD_rpow_neg_eq_exp (K₀ q : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    scaleD K₀ j ^ (-q) = Real.exp (-((5 * q / 4) * (K₀ * (5 / 4 : ℝ) ^ (j - 1)))) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact scaleD_succ_rpow_neg i

/-! ### Decomposition of `{x ∈ S_j^g}` -/

private theorem mem_gentlePart_singularSetsGen_iff {ν : ℕ} (P : Params)
    (blk : Finset (Site ν) → Finset (Site ν)) (S₀ : Set (Site ν)) (v : Site ν → ℝ) (j : ℕ)
    (x : Site ν) :
    x ∈ gentlePart P blk j v (singularSetsGen P blk S₀ v j) ↔
      x ∈ singularSetsGen P blk S₀ v j ∧ x ∉ singularSetsGen P blk S₀ v (j + 1) := by
  rw [singularSetsGen_succ]
  have hsub := gentlePart_subset P blk v j (singularSetsGen P blk S₀ v j)
  constructor
  · intro h
    exact ⟨hsub h, fun h' => h'.2 h⟩
  · rintro ⟨h1, h2⟩
    by_contra h
    exact h2 ⟨h1, h⟩


theorem measurableSet_mem_gentlePart_singularSetsIn {ν : ℕ} (P : Params) (Λ : Finset (Site ν))
    (x : Site ν) (j : ℕ) :
    MeasurableSet {v : Configuration ν |
      x ∈ gentlePart P (fun B => B ∩ Λ) j v (singularSetsIn P Λ v j)} := by
  have h : {v : Configuration ν |
      x ∈ gentlePart P (fun B => B ∩ Λ) j v (singularSetsIn P Λ v j)} =
      {v : Configuration ν | x ∈ singularSetsIn P Λ v j} ∩
        {v : Configuration ν | x ∈ singularSetsIn P Λ v (j + 1)}ᶜ := by
    ext v
    exact mem_gentlePart_singularSetsGen_iff P _ _ v j x
  rw [h]
  exact (measurableSet_mem_singularSetsIn P Λ x j).inter
    (measurableSet_mem_singularSetsIn P Λ x (j + 1)).compl

private theorem exists_finset_of_mem_gentlePart {ν : ℕ} (P : Params) (Λ : Finset (Site ν))
    (j : ℕ) (x : Site ν) (v : Configuration ν)
    (hv : x ∈ gentlePart P (fun B => B ∩ Λ) j v (singularSetsIn P Λ v j)) :
    ∃ D : Finset (Site ν), x ∈ D ∧ v ∈ gentleEventIn P Λ D j := by
  obtain ⟨C, ⟨hCc, hg⟩, hxC⟩ := hv
  obtain ⟨hfin, -⟩ := id hg
  have hDC : ((hfin.toFinset : Finset (Site ν)) : Set (Site ν)) = C := hfin.coe_toFinset
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [← Finset.mem_coe, hDC]; exact hxC
  · rw [mem_gentleEventIn, hDC]
    exact ⟨hCc, hg⟩

/-- A set not of diameter `≤ d_i` has cover volume above `log d_i = K₀ (5/4)^i`. -/
private theorem lt_coverVolume_of_not_diamLE {ν : ℕ} (K₀ : ℝ) (D : Finset (Site ν)) (i : ℕ)
    (h : ¬ DiamLE (siteDist ν) (D : Set (Site ν)) (scaleD K₀ i)) :
    K₀ * (5 / 4 : ℝ) ^ i < (coverVolume D : ℝ) := by
  unfold DiamLE at h
  push Not at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  have hD : D.Nonempty := ⟨a, ha⟩
  have hdiam : scaleD K₀ i < finDiam D := hab.trans_le (siteDist_le_finDiam ha hb)
  have hspec : 2 * finDiam D ≤ 2 ^ topScale D := by
    unfold topScale; exact Nat.find_spec (exists_two_mul_finDiam_le D)
  have hdp : 0 ≤ finDiam D := by unfold finDiam; positivity
  have h2 : (2 : ℝ) ^ topScale D ≤ Real.exp (topScale D : ℝ) := by
    have e2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
    calc (2 : ℝ) ^ topScale D ≤ (Real.exp 1) ^ topScale D := pow_le_pow_left₀ (by norm_num) e2 _
      _ = Real.exp (topScale D : ℝ) := by rw [← Real.exp_nat_mul]; simp
  have h1 : Real.exp (K₀ * (5 / 4 : ℝ) ^ i) < Real.exp (topScale D : ℝ) :=
    calc Real.exp (K₀ * (5 / 4 : ℝ) ^ i) = scaleD K₀ i := rfl
      _ < finDiam D := hdiam
      _ ≤ 2 * finDiam D := by linarith only [hdp]
      _ ≤ _ := hspec
      _ ≤ _ := h2
  have h3 : K₀ * (5 / 4 : ℝ) ^ i < (topScale D : ℝ) := Real.exp_lt_exp.1 h1
  have h4 : topScale D + 1 ≤ coverVolume D := by
    calc topScale D + 1 = ∑ n ∈ Finset.range (topScale D + 1), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun n _ => one_le_coverNumber n hD
  have h5 : ((topScale D + 1 : ℕ) : ℝ) ≤ (coverVolume D : ℝ) := by exact_mod_cast h4
  push_cast at h5
  linarith only [h3, h5]

/-! ### The fixed-component bound -/

private theorem sqrt_mul_exp_neg {Φ x : ℝ} (hΦ : 0 ≤ Φ) :
    (Φ * Real.exp (-x)) ^ (1 / 2 : ℝ) = Real.sqrt Φ * Real.exp (-x / 2) := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hΦ]
  congr 1
  have h : Real.exp (-x) = Real.exp (-x / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h, Real.sqrt_sq (Real.exp_pos _).le]


private theorem measure_gentleEventIn_le_beta {ν : ℕ} (law : Measure ℝ)
    [IsProbabilityMeasure law] (P : Params) (hK : 0 < P.K₀) (Λ D : Finset (Site ν))
    (i : ℕ) {t Φ : ℝ} (hΦ : 0 ≤ Φ)
    (hres : DiamLE (siteDist ν) (D : Set (Site ν)) (scaleD P.K₀ i) →
      configurationMeasure ν law (resonanceEvent ν (thicken D (4 * scaleD P.K₀ i) ∩ Λ) P.E
        (Real.exp (-Real.sqrt (scaleD P.K₀ i)))) ≤ ENNReal.ofReal Φ)
    (hVD : configurationMeasure ν law (gentleEventAnyIn P Λ D) ≤
      ENNReal.ofReal (Real.exp (-(t * coverVolume D)))) :
    configurationMeasure ν law (gentleEventIn P Λ D (i + 1)) ≤
      ENNReal.ofReal (Real.sqrt Φ * Real.exp (-(t * coverVolume D) / 2) +
        if P.K₀ * (5 / 4 : ℝ) ^ i < (coverVolume D : ℝ) then
          Real.exp (-(t * coverVolume D)) else 0) := by
  set μ := configurationMeasure ν law with hμ
  set V := coverVolume D with hV
  by_cases h1 : DiamLE (siteDist ν) (D : Set (Site ν)) (scaleD P.K₀ i)
  · have h := measure_gentleEventIn_le_sqrt law P hK.le Λ D (j := i + 1) (by omega)
      (by simpa using h1)
    simp only [Nat.add_sub_cancel] at h
    refine h.trans ?_
    have h2 : μ (resonanceEvent ν (thicken D (4 * scaleD P.K₀ i) ∩ Λ) P.E
          (Real.exp (-Real.sqrt (scaleD P.K₀ i)))) * μ (gentleEventAnyIn P Λ D) ≤
        ENNReal.ofReal (Φ * Real.exp (-(t * V))) := by
      rw [ENNReal.ofReal_mul hΦ]
      exact mul_le_mul' (hres h1) hVD
    refine (ENNReal.rpow_le_rpow h2 (by norm_num)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      sqrt_mul_exp_neg hΦ]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by split_ifs <;> positivity))
  · by_cases h2 : DiamLE (siteDist ν) (D : Set (Site ν)) (scaleD P.K₀ (i + 1))
    · have hlt : P.K₀ * (5 / 4 : ℝ) ^ i < (V : ℝ) := lt_coverVolume_of_not_diamLE P.K₀ D i h1
      simp only [hlt, ↓reduceIte]
      refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (by positivity)))
      exact (measure_mono (gentleEventIn_subset_any P Λ D (i + 1))).trans hVD
    · rw [gentleEventIn_eq_empty_of_diam P Λ D (i + 1) h2, measure_empty]
      exact bot_le

/-! ### Summation over cover volumes -/

private theorem exp_mul_beta_le {Kν t a Φs ε V : ℝ} (hV0 : 0 ≤ V) (hΦs : 0 ≤ Φs)
    (ht1 : Kν + 1 ≤ t / 2) (ht2 : 1 ≤ (t - Kν) / 2)
    (hε : ε = Real.exp (-((t - Kν) / 2 * a))) :
    Real.exp (Kν * V) * (Φs * Real.exp (-(t * V) / 2) +
        if a < V then Real.exp (-(t * V)) else 0) ≤ (Φs + ε) * Real.exp (-V) := by
  have hε0 : 0 ≤ ε := hε ▸ (Real.exp_pos _).le
  rw [mul_add]
  have e1 : Real.exp (Kν * V) * (Φs * Real.exp (-(t * V) / 2)) ≤ Φs * Real.exp (-V) := by
    have : Real.exp (Kν * V) * Real.exp (-(t * V) / 2) ≤ Real.exp (-V) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith only [hV0, ht1]
    calc Real.exp (Kν * V) * (Φs * Real.exp (-(t * V) / 2))
        = Φs * (Real.exp (Kν * V) * Real.exp (-(t * V) / 2)) := by ring
      _ ≤ Φs * Real.exp (-V) := by gcongr
  have e2 : Real.exp (Kν * V) * (if a < V then Real.exp (-(t * V)) else 0) ≤
      ε * Real.exp (-V) := by
    split_ifs with h
    · rw [← Real.exp_add, hε, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : (t - Kν) / 2 * a ≤ (t - Kν) / 2 * V :=
        mul_le_mul_of_nonneg_left h.le (by linarith only [ht2])
      nlinarith only [hV0, ht2, h1]
    · simp only [mul_zero]; positivity
  calc _ ≤ Φs * Real.exp (-V) + ε * Real.exp (-V) := add_le_add e1 e2
    _ = _ := by ring

private theorem ofReal_tsum_exp_neg_le {c : ℝ} (hc : 0 ≤ c) :
    ∑' V : ℕ, ENNReal.ofReal (c * Real.exp (-(V : ℝ))) ≤ ENNReal.ofReal (2 * c) := by
  have hr : ∀ V : ℕ, Real.exp (-(V : ℝ)) = Real.exp (-1) ^ V := fun V => by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hr1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    simpa using this
  have hr0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hsum : Summable fun V : ℕ => c * Real.exp (-(V : ℝ)) := by
    simp_rw [hr]
    exact (summable_geometric_of_lt_one hr0.le (by linarith only [hr1])).mul_left c
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun V => by positivity) hsum]
  apply ENNReal.ofReal_le_ofReal
  simp_rw [hr]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le (by linarith only [hr1])]
  have h1 : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith only [hr1]) (by norm_num)]
    linarith only [hr1]
  nlinarith only [hc, h1]

/-! ### The core estimate -/


private theorem measure_gentlePart_le_core {ν : ℕ} (law : Measure ℝ) [IsProbabilityMeasure law]
    (P : Params) (hK : 0 < P.K₀) {q t ρ Kν : ℝ}
    (hKν : ∀ (x : Site ν) (V : ℕ),
      {D : Finset (Site ν) | x ∈ D ∧ coverVolume D = V}.Finite ∧
        (({D : Finset (Site ν) | x ∈ D ∧ coverVolume D = V}.ncard : ℕ) : ℝ) ≤
          Real.exp (Kν * V))
    (ht1 : Kν + 1 ≤ t / 2) (ht2 : 1 ≤ (t - Kν) / 2)
    (ht3 : 5 * q / 4 + Real.log 4 / P.K₀ ≤ (t - Kν) / 2) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ i : ℕ, Real.sqrt 2 * ρ * (11 ^ ν * (1 + scaleD P.K₀ i) ^ ν) *
          Real.exp (-Real.sqrt (scaleD P.K₀ i) / 2) ≤ (scaleD P.K₀ (i + 1) ^ (-q) / 4) ^ 2)
    (hres : ∀ (Λ D : Finset (Site ν)) (R : ℝ), 0 ≤ R →
      DiamLE (siteDist ν) (D : Set (Site ν)) R →
      configurationMeasure ν law (resonanceEvent ν (thicken D (4 * R) ∩ Λ) P.E
        (Real.exp (-Real.sqrt R))) ≤
      ENNReal.ofReal (Real.sqrt 2 * ρ * (11 ^ ν * (1 + R) ^ ν) * Real.exp (-Real.sqrt R / 2)))
    (hV : ∀ (Λ D : Finset (Site ν)), D.Nonempty →
      configurationMeasure ν law (gentleEventAnyIn P Λ D) ≤
        ENNReal.ofReal (Real.exp (-(t * coverVolume D))))
    (Λ : Finset (Site ν)) (x : Site ν) (i : ℕ) :
    configurationMeasure ν law {v : Configuration ν |
        x ∈ gentlePart P (fun B => B ∩ Λ) (i + 1) v (singularSetsIn P Λ v (i + 1))} ≤
      ENNReal.ofReal (scaleD P.K₀ (i + 1) ^ (-q)) := by
  classical
  set μ := configurationMeasure ν law with hμ
  set Φ : ℝ := Real.sqrt 2 * ρ * (11 ^ ν * (1 + scaleD P.K₀ i) ^ ν) *
    Real.exp (-Real.sqrt (scaleD P.K₀ i) / 2) with hΦdef
  set a : ℝ := P.K₀ * (5 / 4 : ℝ) ^ i with ha
  set ε : ℝ := Real.exp (-((t - Kν) / 2 * a)) with hε
  set dq : ℝ := scaleD P.K₀ (i + 1) ^ (-q) with hdq
  have hdq0 : 0 < dq := Real.rpow_pos_of_pos (scaleD_pos _ _) _
  have hd0 := scaleD_pos P.K₀ i
  have hΦ0 : 0 ≤ Φ := by rw [hΦdef]; positivity
  have hsqrt : Real.sqrt Φ ≤ dq / 4 := Real.sqrt_le_iff.2 ⟨by positivity, hρ i⟩
  have hε' : ε ≤ dq / 4 := by
    have ha1 : P.K₀ ≤ a := by
      have : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      nlinarith only [hK, this]
    have h1 : Real.log 4 ≤ Real.log 4 / P.K₀ * a := by
      have h4 : 0 ≤ Real.log 4 / P.K₀ := div_nonneg (Real.log_nonneg (by norm_num)) hK.le
      have : Real.log 4 / P.K₀ * P.K₀ = Real.log 4 := by field_simp
      nlinarith only [ha1, h4, this]
    have h2 : 5 * q / 4 * a + Real.log 4 ≤ (t - Kν) / 2 * a := by
      have := mul_le_mul_of_nonneg_right ht3 (by positivity : 0 ≤ a)
      nlinarith only [h1, this]
    rw [hε, hdq, scaleD_succ_rpow_neg i, ← ha, le_div_iff₀ (by norm_num)]
    calc Real.exp (-((t - Kν) / 2 * a)) * 4
        ≤ Real.exp (-(5 * q / 4 * a + Real.log 4)) * 4 := by
          gcongr
      _ = Real.exp (-(5 * q / 4 * a)) := by
          rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 4), Real.exp_log (by norm_num)]
          field_simp
  -- decomposition
  set F : ℕ → Finset (Finset (Site ν)) := fun V => (hKν x V).1.toFinset with hF
  have hsub : {v : Configuration ν |
        x ∈ gentlePart P (fun B => B ∩ Λ) (i + 1) v (singularSetsIn P Λ v (i + 1))} ⊆
      ⋃ V : ℕ, ⋃ D ∈ F V, gentleEventIn P Λ D (i + 1) := by
    intro v hv
    obtain ⟨D, hxD, hvD⟩ := exists_finset_of_mem_gentlePart P Λ (i + 1) x v hv
    simp only [Set.mem_iUnion]
    exact ⟨coverVolume D, D, by simp [hF, hxD], hvD⟩
  -- the bound for each `V`
  have hper : ∀ V : ℕ, μ (⋃ D ∈ F V, gentleEventIn P Λ D (i + 1)) ≤
      ENNReal.ofReal ((Real.sqrt Φ + ε) * Real.exp (-(V : ℝ))) := by
    intro V
    have hbeta : ∀ D ∈ F V, μ (gentleEventIn P Λ D (i + 1)) ≤
        ENNReal.ofReal (Real.sqrt Φ * Real.exp (-(t * V) / 2) +
          if a < (V : ℝ) then Real.exp (-(t * V)) else 0) := by
      intro D hD
      have hD' : x ∈ D ∧ coverVolume D = V := by simpa [hF] using hD
      have h := measure_gentleEventIn_le_beta law P hK Λ D i hΦ0
        (fun hd => hres Λ D _ (scaleD_pos _ _).le hd) (hV Λ D ⟨x, hD'.1⟩)
      rw [hD'.2] at h
      exact h
    refine (measure_biUnion_finset_le (F V) _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ hbeta).trans ?_
    rw [nsmul_eq_mul]
    have hcard : ((F V).card : ℝ) ≤ Real.exp (Kν * V) := by
      have := (hKν x V).2
      rwa [Set.ncard_eq_toFinset_card _ (hKν x V).1] at this
    have hcard' : (((F V).card : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (Kν * V)) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hcard
    calc _ ≤ ENNReal.ofReal (Real.exp (Kν * V)) * ENNReal.ofReal (Real.sqrt Φ *
          Real.exp (-(t * V) / 2) + if a < (V : ℝ) then Real.exp (-(t * V)) else 0) :=
          mul_le_mul' hcard' le_rfl
      _ = ENNReal.ofReal (Real.exp (Kν * V) * (Real.sqrt Φ *
          Real.exp (-(t * V) / 2) + if a < (V : ℝ) then Real.exp (-(t * V)) else 0)) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal
          (exp_mul_beta_le (Nat.cast_nonneg V) (Real.sqrt_nonneg _) ht1 ht2 hε)
  calc μ _ ≤ μ (⋃ V : ℕ, ⋃ D ∈ F V, gentleEventIn P Λ D (i + 1)) := measure_mono hsub
    _ ≤ ∑' V : ℕ, μ (⋃ D ∈ F V, gentleEventIn P Λ D (i + 1)) := measure_iUnion_le _
    _ ≤ ∑' V : ℕ, ENNReal.ofReal ((Real.sqrt Φ + ε) * Real.exp (-(V : ℝ))) :=
        ENNReal.tsum_le_tsum hper
    _ ≤ ENNReal.ofReal (2 * (Real.sqrt Φ + ε)) :=
        ofReal_tsum_exp_neg_le (by positivity)
    _ ≤ ENNReal.ofReal dq := ENNReal.ofReal_le_ofReal (by linarith only [hsqrt, hε'])

/-! ### The thresholds -/

private theorem exists_abs_of_eventually_cocompact' {p : ℝ → Prop}
    (h : ∀ᶠ E in Filter.cocompact ℝ, p E) : ∃ R : ℝ, ∀ E : ℝ, R < |E| → p E := by
  obtain ⟨K, hKc, hKs⟩ := Filter.mem_cocompact.1 h
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨R, fun E hE => hKs ?_⟩
  intro hEK
  have := hR hEK
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith only [hE, this]

private theorem exists_volume_rate (ν : ℕ) {K₀ q : ℝ} (hK : 0 < K₀) (hq : 0 < q) :
    ∃ Kν t : ℝ, 0 < t ∧
      (∀ (x : Site ν) (V : ℕ), {D : Finset (Site ν) | x ∈ D ∧ coverVolume D = V}.Finite ∧
        (({D : Finset (Site ν) | x ∈ D ∧ coverVolume D = V}.ncard : ℕ) : ℝ) ≤
          Real.exp (Kν * V)) ∧
      Kν + 1 ≤ t / 2 ∧ 1 ≤ (t - Kν) / 2 ∧ 5 * q / 4 + Real.log 4 / K₀ ≤ (t - Kν) / 2 := by
  obtain ⟨Kν, hKν⟩ := exists_ncard_coverVolume_le ν
  have hl : 0 ≤ Real.log 4 / K₀ := div_nonneg (Real.log_nonneg (by norm_num)) hK.le
  have hab := le_abs_self Kν
  have hab' := neg_abs_le Kν
  have habs := abs_nonneg Kν
  refine ⟨Kν, 2 * |Kν| + 2 * (5 * q / 4 + Real.log 4 / K₀) + 4, by positivity, hKν, ?_, ?_, ?_⟩ <;>
    linarith only [hq, hl, hab, habs]


theorem exists_threshold_gentlePart_le_boundedDensity (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) {q : ℝ}
    (hq : 0 < q) :
    ∃ δ₀ : ℝ, ∀ (law : Measure ℝ) [IsProbabilityMeasure law] (δ : ℝ), HasBoundedDensity law δ →
      δ₀ ≤ δ → ∀ (P : Params), P.K₀ = K₀ → P.Nthr = Real.sqrt δ →
        ∀ (Λ : Finset (Site ν)) (x : Site ν) (j : ℕ), 1 ≤ j →
          MeasurableSet {v : Configuration ν |
              x ∈ gentlePart P (fun B => B ∩ Λ) j v (singularSetsIn P Λ v j)} ∧
            configurationMeasure ν law {v | x ∈ gentlePart P (fun B => B ∩ Λ) j v
              (singularSetsIn P Λ v j)} ≤ ENNReal.ofReal (scaleD K₀ j ^ (-q)) := by
  obtain ⟨Kν, t, ht, hKν, ht1, ht2, ht3⟩ := exists_volume_rate ν hK hq
  obtain ⟨δ₁, hδ₁⟩ := exists_threshold_gentleEventAnyIn_le_volume_boundedDensity ν hK ht
  obtain ⟨ρ₁, hρ₁, hρ⟩ := exists_rho_const ν K₀ hq
  refine ⟨max δ₁ (ρ₁⁻¹ ^ 2), fun law _ δ hlaw hδ P hP hN Λ x j hj => ⟨?_, ?_⟩⟩
  · exact measurableSet_mem_gentlePart_singularSetsIn P Λ x j
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hδpos : 0 < δ := hlaw.1
    have hδ1 : δ₁ ≤ δ := (le_max_left _ _).trans hδ
    have hδ2 : ρ₁⁻¹ ^ 2 ≤ δ := (le_max_right _ _).trans hδ
    have hρδ : Real.sqrt δ⁻¹ ≤ ρ₁ := by
      rw [Real.sqrt_le_left hρ₁.le, inv_le_comm₀ hδpos (by positivity)]
      simpa [inv_pow] using hδ2
    subst hP
    exact measure_gentlePart_le_core law P hK hKν ht1 ht2 ht3 (Real.sqrt_nonneg _)
      (fun i => hρ _ (Real.sqrt_nonneg _) hρδ i)
      (fun Λ' D R hR hd => measure_resonance_thicken_le_boundedDensity law hlaw P.E Λ' D hR hd)
      (fun Λ' D hD => hδ₁ law δ hlaw hδ1 P rfl hN Λ' D hD) Λ x i


theorem exists_threshold_gentlePart_le_gaussian (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) {γ : ℝ}
    (hγ : 0 < γ) {q : ℝ} (hq : 0 < q) :
    ∃ E₀ : ℝ, ∀ (P : Params), P.K₀ = K₀ → E₀ ≤ |P.E - 2 * ν| → P.Nthr = |P.E| / 2 →
      ∀ (Λ : Finset (Site ν)) (x : Site ν) (j : ℕ), 1 ≤ j →
        MeasurableSet {v : Configuration ν |
            x ∈ gentlePart P (fun B => B ∩ Λ) j v (singularSetsIn P Λ v j)} ∧
          configurationMeasure ν (gaussianLaw γ hγ) {v | x ∈ gentlePart P (fun B => B ∩ Λ) j v
            (singularSetsIn P Λ v j)} ≤ ENNReal.ofReal (scaleD K₀ j ^ (-q)) := by
  obtain ⟨Kν, t, ht, hKν, ht1, ht2, ht3⟩ := exists_volume_rate ν hK hq
  obtain ⟨E₁, hE₁⟩ := exists_threshold_gentleEventAnyIn_le_volume_gaussian ν hK hγ ht
  obtain ⟨ρ₁, hρ₁, hρ⟩ := exists_rho_const ν K₀ hq
  set L : ℝ := 1 / Real.sqrt (2 * Real.pi * γ) with hL
  have hLpos : 0 < L := by positivity
  have hev : ∀ᶠ E in Filter.cocompact ℝ, L * (gaussianLaw γ hγ).real
      {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1} < ρ₁ ^ 2 := by
    have := (tendsto_gaussianLaw_window ν hγ).const_mul L
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨Rt, hRt⟩ := exists_abs_of_eventually_cocompact' hev
  refine ⟨max E₁ (Rt + 2 * ν + 1), fun P hP hE hN Λ x j hj => ⟨?_, ?_⟩⟩
  · exact measurableSet_mem_gentlePart_singularSetsIn P Λ x j
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hE1 : E₁ ≤ |P.E - 2 * ν| := (le_max_left _ _).trans hE
    have hE2 : Rt + 2 * ν + 1 ≤ |P.E - 2 * ν| := (le_max_right _ _).trans hE
    have hν0 : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
    have habs : |P.E - 2 * ν| ≤ |P.E| + 2 * ν := by
      have := abs_sub (P.E) (2 * (ν : ℝ))
      rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ν)] at this
    have hρE : Real.sqrt (L * (gaussianLaw γ hγ).real
        {t | |t - (P.E - 2 * ν)| ≤ 2 * ν + 1}) ≤ ρ₁ := by
      rw [Real.sqrt_le_left hρ₁.le]
      exact (hRt P.E (by linarith only [hE2, habs])).le
    subst hP
    exact measure_gentlePart_le_core (gaussianLaw γ hγ) P hK hKν ht1 ht2 ht3 (Real.sqrt_nonneg _)
      (fun i => hρ _ (Real.sqrt_nonneg _) hρE i)
      (fun Λ' D R hR hd => measure_resonance_thicken_le_gaussian hγ P.E Λ' D hR hd)
      (fun Λ' D hD => hE₁ P rfl hE1 hN Λ' D hD) Λ x i

end FroehlichSpencer.T12

end
