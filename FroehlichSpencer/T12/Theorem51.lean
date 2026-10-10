/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Events
public import FroehlichSpencer.T12.Section5
public import FroehlichSpencer.T12.Lemma52
public import FroehlichSpencer.T12.Resonance
public import FroehlichSpencer.T12.Cubes
public import FroehlichSpencer.T12.Interpolation

/-!
# Theorem 5.1: the component occurrence bound
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.T12

open Multiscale

/-! ### The weighted product bound -/


private theorem measure_le_exp_neg_weighted {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Set Ω) (T : Finset ι) (w t : ι → ℝ) (hw : ∀ i ∈ T, 0 ≤ w i) (hsum : ∑ i ∈ T, w i ≤ 1)
    (h1 : μ S ≤ 1) (ht : ∀ i ∈ T, μ S ≤ ENNReal.ofReal (Real.exp (-t i))) :
    μ S ≤ ENNReal.ofReal (Real.exp (-∑ i ∈ T, w i * t i)) := by
  by_cases h0 : μ S = 0
  · rw [h0]; exact bot_le
  have hne : μ S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h1
  set x := (μ S).toReal with hx
  have hxpos : 0 < x := ENNReal.toReal_pos h0 hne
  have hx1 : x ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top h1
    simpa using this
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hxpos.le hx1
  have hi : ∀ i ∈ T, Real.log x ≤ -t i := by
    intro i hi
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (ht i hi)
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
    rw [Real.log_le_iff_le_exp hxpos]
    exact this
  have hmain : Real.log x ≤ -∑ i ∈ T, w i * t i := by
    have h2 : ∑ i ∈ T, w i * Real.log x ≤ ∑ i ∈ T, w i * (-t i) :=
      Finset.sum_le_sum fun i hiT => mul_le_mul_of_nonneg_left (hi i hiT) (hw i hiT)
    rw [← Finset.sum_mul] at h2
    have h3 : Real.log x ≤ (∑ i ∈ T, w i) * Real.log x := by nlinarith only [hsum, hlog]
    have h4 : ∑ i ∈ T, w i * (-t i) = -∑ i ∈ T, w i * t i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith only [h2, h3, h4]
  have : x ≤ Real.exp (-∑ i ∈ T, w i * t i) := (Real.log_le_iff_le_exp hxpos).1 hmain
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal this

/-- The weights `(1/5) (4/5)^n` have total mass at most one over any finite set of scales. -/
private theorem sum_weights_le_one (T : Finset ℕ) :
    ∑ n ∈ T, (1 / 5 : ℝ) * (4 / 5) ^ n ≤ 1 := by
  obtain ⟨m, hm⟩ : ∃ m, T ⊆ Finset.range m :=
    ⟨T.sup id + 1, fun n hn => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))⟩
  calc ∑ n ∈ T, (1 / 5 : ℝ) * (4 / 5) ^ n ≤ ∑ n ∈ Finset.range m, (1 / 5 : ℝ) * (4 / 5) ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hm (fun _ _ _ => by positivity)
    _ ≤ 1 := by
        rw [← Finset.mul_sum, geom_sum_eq (by norm_num)]
        have : (0 : ℝ) ≤ (4 / 5) ^ m := by positivity
        have h : ((4 / 5 : ℝ) ^ m - 1) / (4 / 5 - 1) = 5 * (1 - (4 / 5) ^ m) := by
          field_simp; ring
        rw [h]; nlinarith only [this]

/-! ### The resonance rate estimate -/

/-- `(1 + d)^ν e^{-√d/4}` is bounded uniformly in `d ≥ 0`. -/
private theorem poly_mul_exp_le (ν : ℕ) {d : ℝ} (hd : 0 ≤ d) :
    (1 + d) ^ ν * Real.exp (-Real.sqrt d / 4) ≤
      4 ^ (2 * ν) * (2 * ν).factorial * Real.exp (1 / 4) := by
  set s := Real.sqrt d with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg d
  have hds : d = s ^ 2 := (Real.sq_sqrt hd).symm
  have h1 : (1 + d) ^ ν ≤ (1 + s) ^ (2 * ν) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    rw [hds]; nlinarith only [hs0]
  have h2 := Real.pow_div_factorial_le_exp ((1 + s) / 4) (by positivity) (2 * ν)
  have hf : (0 : ℝ) < (2 * ν).factorial := by exact_mod_cast Nat.factorial_pos _
  have h3 : (1 + s) ^ (2 * ν) ≤ 4 ^ (2 * ν) * (2 * ν).factorial * Real.exp ((1 + s) / 4) := by
    rw [div_pow, div_le_iff₀ hf] at h2
    have : (4 : ℝ) ^ (2 * ν) > 0 := by positivity
    rw [div_le_iff₀ this] at h2
    linarith only [h2]
  calc (1 + d) ^ ν * Real.exp (-s / 4)
      ≤ (4 ^ (2 * ν) * (2 * ν).factorial * Real.exp ((1 + s) / 4)) * Real.exp (-s / 4) := by
        gcongr; exact h1.trans h3
    _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2; ring

/-- Large scales: `5 b (5/4)^n ≤ (√2)^n / 4 + M`. -/
private theorem exists_const_rate (b : ℝ) (hb : 0 ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, 5 * b * (5 / 4 : ℝ) ^ n ≤ Real.sqrt 2 ^ n / 4 + M := by
  have hr : 1 < Real.sqrt 2 / (5 / 4) := by
    rw [lt_div_iff₀ (by norm_num)]
    have : (5 / 4 : ℝ) < Real.sqrt 2 := by
      apply Real.lt_sqrt_of_sq_lt; norm_num
    linarith only [this]
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (20 * b) hr
  refine ⟨5 * b * (5 / 4 : ℝ) ^ N, by positivity, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have h1 : (Real.sqrt 2 / (5 / 4)) ^ N ≤ (Real.sqrt 2 / (5 / 4)) ^ n :=
      pow_le_pow_right₀ hr.le hn
    have h2 : Real.sqrt 2 ^ n = (Real.sqrt 2 / (5 / 4)) ^ n * (5 / 4) ^ n := by
      rw [← mul_pow]; congr 1; field_simp
    have h3 : (0 : ℝ) < (5 / 4) ^ n := by positivity
    have h4 : (0 : ℝ) ≤ 5 * b * (5 / 4) ^ N := by positivity
    have h5 : 20 * b * (5 / 4 : ℝ) ^ n ≤ Real.sqrt 2 ^ n := by
      rw [h2]; exact mul_le_mul_of_nonneg_right (hN.le.trans h1) h3.le
    linarith only [h4, h5]
  · push Not at hn
    have : (5 / 4 : ℝ) ^ n ≤ (5 / 4) ^ N := pow_le_pow_right₀ (by norm_num) hn.le
    have h6 : 0 ≤ Real.sqrt 2 ^ n / 4 := by positivity
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 5 * b)
    linarith only [h6, this]


private theorem exists_rho_bound (ν : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρ₀ → ∀ (n : ℕ) (d : ℝ), 2 * 2 ^ n ≤ d →
      Real.sqrt 2 * ρ * (11 ^ ν * (1 + d) ^ ν) * Real.exp (-Real.sqrt d / 2) ≤
        Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n)) := by
  obtain ⟨M, hM0, hM⟩ := exists_const_rate b hb
  set C : ℝ := 4 ^ (2 * ν) * (2 * ν).factorial * Real.exp (1 / 4) with hC
  have hCpos : 0 < C := by positivity
  have hK : 0 < Real.sqrt 2 * 11 ^ ν * C * Real.exp M := by positivity
  refine ⟨(Real.sqrt 2 * 11 ^ ν * C * Real.exp M)⁻¹, by positivity, fun ρ hρ0 hρ n d hd => ?_⟩
  have hd0 : 0 ≤ d := by have : (0 : ℝ) ≤ 2 * 2 ^ n := by positivity
                         linarith only [hd, this]
  have hsd : Real.sqrt 2 ^ n ≤ Real.sqrt d := by
    apply Real.le_sqrt_of_sq_le
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    linarith only [hd,
      show (2 : ℝ) ^ n ≤ 2 * 2 ^ n by linarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]]
  have hpoly := poly_mul_exp_le ν hd0
  have hexp1 : Real.exp (-Real.sqrt d / 2) = Real.exp (-Real.sqrt d / 4) *
      Real.exp (-Real.sqrt d / 4) := by rw [← Real.exp_add]; congr 1; ring
  have hexp2 : Real.exp (-Real.sqrt d / 4) ≤
      Real.exp M * Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := hM n
    linarith only [hsd, this]
  have hstep : (1 + d) ^ ν * Real.exp (-Real.sqrt d / 2) ≤
      C * (Real.exp M * Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n))) := by
    rw [hexp1, ← mul_assoc]
    calc (1 + d) ^ ν * Real.exp (-Real.sqrt d / 4) * Real.exp (-Real.sqrt d / 4)
        ≤ C * Real.exp (-Real.sqrt d / 4) := by gcongr
      _ ≤ _ := by gcongr
  have hρ' : ρ * (Real.sqrt 2 * 11 ^ ν * C * Real.exp M) ≤ 1 := by
    calc _ ≤ (Real.sqrt 2 * 11 ^ ν * C * Real.exp M)⁻¹ *
          (Real.sqrt 2 * 11 ^ ν * C * Real.exp M) := by gcongr
      _ = 1 := inv_mul_cancel₀ hK.ne'
  calc Real.sqrt 2 * ρ * (11 ^ ν * (1 + d) ^ ν) * Real.exp (-Real.sqrt d / 2)
      = (Real.sqrt 2 * ρ * 11 ^ ν) * ((1 + d) ^ ν * Real.exp (-Real.sqrt d / 2)) := by ring
    _ ≤ (Real.sqrt 2 * ρ * 11 ^ ν) *
        (C * (Real.exp M * Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n)))) := by
        gcongr
    _ = (ρ * (Real.sqrt 2 * 11 ^ ν * C * Real.exp M)) * Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n)) := by
        ring
    _ ≤ 1 * Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n)) := by gcongr
    _ = _ := one_mul _

/-! ### Scale comparison and disjointness of isolated blocks -/

private theorem exists_scaleD_ge' {K₀ : ℝ} (hK : 0 < K₀) (a : ℝ) : ∃ j, a ≤ scaleD K₀ j := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (a / K₀) (by norm_num : (1 : ℝ) < 5 / 4)
  refine ⟨j, ?_⟩
  have h1 : a ≤ K₀ * (5 / 4 : ℝ) ^ j := by
    have := (div_lt_iff₀ hK).1 hj
    linarith only [this]
  unfold scaleD
  linarith only [h1, Real.add_one_le_exp (K₀ * (5 / 4 : ℝ) ^ j)]

private theorem resScale_spec' {K₀ : ℝ} (hK : 0 < K₀) (ν n : ℕ) :
    2 * Real.sqrt ν * 2 ^ n ≤ scaleD K₀ (resScale ν K₀ n) := by
  classical
  have h := exists_scaleD_ge' hK (2 * Real.sqrt ν * 2 ^ n)
  unfold resScale
  simp only [h, ↓reduceDIte]
  exact Nat.find_spec h

private theorem lt_of_lt_resScale' {K₀ : ℝ} (hK : 0 < K₀) {ν n i : ℕ} (hi : i < resScale ν K₀ n) :
    scaleD K₀ i < 2 * Real.sqrt ν * 2 ^ n := by
  classical
  have h := exists_scaleD_ge' hK (2 * Real.sqrt ν * 2 ^ n)
  unfold resScale at hi
  simp only [h, ↓reduceDIte] at hi
  exact not_le.1 (Nat.find_min h hi)

private theorem two_rpow_nat_mul (a : ℝ) (n : ℕ) : (2 : ℝ) ^ (a * n) = ((2 : ℝ) ^ a) ^ n := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- `d_{j(n)} ≤ C_ν (2^{5/4})^n`. -/
private theorem scaleD_resScale_le {K₀ : ℝ} (hK : 0 < K₀) (ν n : ℕ) :
    scaleD K₀ (resScale ν K₀ n) ≤
      max (Real.exp K₀) ((2 * Real.sqrt ν) ^ (5 / 4 : ℝ)) * ((2 : ℝ) ^ (5 / 4 : ℝ)) ^ n := by
  have hb : (1 : ℝ) ≤ ((2 : ℝ) ^ (5 / 4 : ℝ)) ^ n :=
    one_le_pow₀ (Real.one_le_rpow (by norm_num) (by norm_num))
  rcases Nat.eq_zero_or_pos (resScale ν K₀ n) with h0 | hpos
  · rw [h0, scaleD_zero]
    calc Real.exp K₀ = Real.exp K₀ * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul (le_max_left _ _) hb zero_le_one
            (le_trans (Real.exp_pos _).le (le_max_left _ _))
  · obtain ⟨m, hm⟩ : ∃ m, resScale ν K₀ n = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hlt := lt_of_lt_resScale' hK (ν := ν) (n := n) (i := m) (by omega)
    rw [hm, ← scaleR_eq_scaleD_succ]
    unfold scaleR
    have h1 := Real.rpow_le_rpow (scaleD_pos K₀ m).le hlt.le (by norm_num : (0 : ℝ) ≤ 5 / 4)
    have h2 : (2 * Real.sqrt ν * 2 ^ n) ^ (5 / 4 : ℝ) =
        (2 * Real.sqrt ν) ^ (5 / 4 : ℝ) * ((2 : ℝ) ^ (5 / 4 : ℝ)) ^ n := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ), two_rpow_nat_mul]
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- For large `n` the `4 d_{j(n)}`-neighbourhoods of `2 · 2^{5n/3}`-separated sets are disjoint. -/
private theorem exists_nstar_disjoint {K₀ : ℝ} (hK : 0 < K₀) (ν : ℕ) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      8 * scaleD K₀ (resScale ν K₀ n) < 2 * (2 : ℝ) ^ ((5 / 3 : ℝ) * n) := by
  set C := max (Real.exp K₀) ((2 * Real.sqrt ν) ^ (5 / 4 : ℝ)) with hC
  have hs : 1 < (2 : ℝ) ^ (5 / 12 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (4 * C) hs
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ((2 : ℝ) ^ (5 / 12 : ℝ)) ^ N ≤ ((2 : ℝ) ^ (5 / 12 : ℝ)) ^ n :=
    pow_le_pow_right₀ hs.le hn
  have h3 : (2 : ℝ) ^ ((5 / 3 : ℝ) * n) =
      ((2 : ℝ) ^ (5 / 4 : ℝ)) ^ n * ((2 : ℝ) ^ (5 / 12 : ℝ)) ^ n := by
    rw [← mul_pow, ← Real.rpow_add (by norm_num), ← two_rpow_nat_mul]
    norm_num
  have hd := scaleD_resScale_le hK ν n
  have hb : (0 : ℝ) < ((2 : ℝ) ^ (5 / 4 : ℝ)) ^ n := by positivity
  rw [h3]
  have h4 : 4 * C < ((2 : ℝ) ^ (5 / 12 : ℝ)) ^ n := lt_of_lt_of_le hN h1
  nlinarith only [hd, hb, h4]

private theorem two_mul_cubeHalfSide_le' (n : ℕ) : 2 * cubeHalfSide n ≤ 2 ^ n := by
  unfold cubeHalfSide
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [hn.ne', ite_false]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]
    linarith only []

/-- Two points of one `n`-cube are at distance at most `√ν 2^n`. -/
private theorem siteDist_le_of_mem_dyCube' {ν n : ℕ} {k x y : Site ν} (hx : x ∈ dyCube n k)
    (hy : y ∈ dyCube n k) : siteDist ν x y ≤ Real.sqrt ν * 2 ^ n := by
  rw [mem_dyCube] at hx hy
  have hcoord : ∀ i, (((x - y) i : ℤ) : ℝ) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := by
    intro i
    have h1 := hx i
    have h2 := hy i
    have h3 := two_mul_cubeHalfSide_le' n
    have h4 : |(x - y) i| ≤ 2 ^ n := by
      rw [abs_le]; simp only [Pi.sub_apply]; constructor <;> linarith only [h1, h2, h3]
    have h5 : |(((x - y) i : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n := by
      rw [← Int.cast_abs]; exact_mod_cast h4
    exact sq_le_sq' (abs_le.1 h5).1 (abs_le.1 h5).2
  unfold siteDist latticeLength
  calc Real.sqrt (∑ i : Fin ν, (((x - y) i : ℤ) : ℝ) ^ 2)
      ≤ Real.sqrt (ν * ((2 : ℝ) ^ n) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc (∑ i : Fin ν, (((x - y) i : ℤ) : ℝ) ^ 2) ≤ ∑ _i : Fin ν, ((2 : ℝ) ^ n) ^ 2 :=
              Finset.sum_le_sum fun i _ => hcoord i
          _ = ν * ((2 : ℝ) ^ n) ^ 2 := by simp
    _ = Real.sqrt ν * 2 ^ n := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]

private theorem cubeDist_le_siteDist' {ν n : ℕ} {k k' x y : Site ν} (hx : x ∈ dyCube n k)
    (hy : y ∈ dyCube n k') : cubeDist n k k' ≤ siteDist ν x y := by
  unfold cubeDist
  have h : (dyCube n k ×ˢ dyCube n k').inf
      (fun p => ENNReal.ofReal (Multiscale.siteDist ν p.1 p.2)) ≤
      ENNReal.ofReal (siteDist ν x y) :=
    Finset.inf_le (f := fun p : Site ν × Site ν => ENNReal.ofReal (siteDist ν p.1 p.2))
      (b := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (siteDist_nonneg ν x y)] at this

private theorem mem_isolatedCubes' {ν : ℕ} {α M : ℝ} {n : ℕ} {D : Finset (Site ν)} {c : Site ν} :
    c ∈ isolatedCubes α M n D ↔ c ∈ minCover n D ∧
      ∀ k' ∈ minCover n D, k' ≠ c → M * 2 ^ (α * n) ≤ cubeDist n c k' := by
  classical
  unfold isolatedCubes
  simp only [Finset.mem_filter]


private theorem disjoint_blocks {ν : ℕ} (K₀ : ℝ) (n : ℕ) (Λ D : Finset (Site ν))
    (hn : 8 * scaleD K₀ (resScale ν K₀ n) < 2 * (2 : ℝ) ^ ((5 / 3 : ℝ) * n)) {c c' : Site ν}
    (hc : c ∈ isolatedCubes (5 / 3) 2 n D) (hc' : c' ∈ isolatedCubes (5 / 3) 2 n D)
    (hne : c ≠ c') :
    Disjoint (thicken (dyCube n c ∩ D) (4 * scaleD K₀ (resScale ν K₀ n)) ∩ Λ)
      (thicken (dyCube n c' ∩ D) (4 * scaleD K₀ (resScale ν K₀ n)) ∩ Λ) := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  obtain ⟨q, hq, hyq⟩ := mem_thicken.1 (Finset.mem_inter.1 hy).1
  obtain ⟨q', hq', hyq'⟩ := mem_thicken.1 (Finset.mem_inter.1 hy').1
  have hiso := (mem_isolatedCubes'.1 hc).2 c' (mem_isolatedCubes'.1 hc').1 hne.symm
  have h1 := cubeDist_le_siteDist' (Finset.mem_inter.1 hq).1 (Finset.mem_inter.1 hq').1
  have h2 := siteDist_triangle ν q q' y
  have h3 := siteDist_comm ν q y
  linarith only [hn, hyq, hyq', hiso, h1, h2, h3]

/-! ### Independence at scale zero -/

private theorem dependsOn_singular0 {ν : ℕ} (P : Params) (x : Site ν) :
    Infra.DependsOn (({x} : Finset (Site ν)) : Set (Site ν))
      {v : Configuration ν | x ∈ singular0 P v} := by
  apply Infra.dependsOn_of_measurable_of_invariant
  · have : {v : Configuration ν | x ∈ singular0 P v} =
        {v | |v x - P.E + 2 * ν| ≤ P.Nthr} := by
      ext v; simp [mem_singular0]
    rw [this]
    exact measurableSet_le (by fun_prop) measurable_const
  · intro v w hvw
    have : v x = w x := hvw x (by simp)
    simp [mem_singular0, this]

private theorem one_le_of_two_le_coverNumber {ν n : ℕ} {D : Finset (Site ν)}
    (h : 2 ≤ coverNumber n D) : 1 ≤ ν := by
  by_contra hν
  have hν0 : ν = 0 := by omega
  subst hν0
  have := coverNumber_le_card n D
  have h2 : D.card ≤ 1 := Finset.card_le_one_of_subsingleton D
  omega

/-! ### The per-scale bound and the core estimate -/

/-- Product bound for the isolated blocks at one scale. -/
private theorem measure_isolated_le {ν : ℕ} (law : Measure ℝ) [IsProbabilityMeasure law]
    (P : Params) (Λ D : Finset (Site ν)) (n : ℕ)
    (hn : 8 * scaleD P.K₀ (resScale ν P.K₀ n) < 2 * (2 : ℝ) ^ ((5 / 3 : ℝ) * n)) {u : ℝ}
    (hres : ∀ c : Site ν, configurationMeasure ν law
      (resonanceEvent ν (thicken (dyCube n c ∩ D) (4 * scaleD P.K₀ (resScale ν P.K₀ n)) ∩ Λ)
        P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (resScale ν P.K₀ n))))) ≤
      ENNReal.ofReal (Real.exp (-u))) :
    configurationMeasure ν law (⋂ c ∈ isolatedCubes (5 / 3) 2 n D,
      resonanceEvent ν (thicken (dyCube n c ∩ D) (4 * scaleD P.K₀ (resScale ν P.K₀ n)) ∩ Λ)
        P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (resScale ν P.K₀ n))))) ≤
      ENNReal.ofReal (Real.exp (-(u * isolatedCount (5 / 3) 2 n D))) := by
  rw [configurationMeasure_biInter_eq_prod law (isolatedCubes (5 / 3) 2 n D)
    (fun c => thicken (dyCube n c ∩ D) (4 * scaleD P.K₀ (resScale ν P.K₀ n)) ∩ Λ)
    (fun c hc c' hc' hne => disjoint_blocks P.K₀ n Λ D hn hc hc' hne) _
    (fun c _ => dependsOn_resonanceEvent ν _ _ _)]
  calc _ ≤ ∏ c ∈ isolatedCubes (5 / 3) 2 n D, ENNReal.ofReal (Real.exp (-u)) :=
        Finset.prod_le_prod fun c _ => hres c
    _ = ENNReal.ofReal (Real.exp (-u)) ^ isolatedCount (5 / 3) 2 n D := by
        rw [Finset.prod_const, card_isolatedCubes]
    _ = _ := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
        congr 2; ring


private theorem measure_gentleEventAnyIn_core {ν : ℕ} (law : Measure ℝ)
    [IsProbabilityMeasure law] (P : Params) (Λ D : Finset (Site ν)) (nstar n₁ : ℕ)
    (hn₁ : ∀ n : ℕ, n₁ ≤ n →
      8 * scaleD P.K₀ (resScale ν P.K₀ n) < 2 * (2 : ℝ) ^ ((5 / 3 : ℝ) * n))
    (hsub : gentleEventAnyIn P Λ D ⊆
        {v | ∀ x ∈ D, x ∈ singular0 P v} ∩
          ⋂ n ∈ Finset.Icc nstar (topScale D), ⋂ (_ : 2 ≤ coverNumber n D),
            ⋂ c ∈ isolatedCubes (5 / 3) 2 n D,
              resonanceEvent ν (thicken (dyCube n c ∩ D) (4 * scaleD P.K₀ (resScale ν P.K₀ n)) ∩ Λ)
                P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (resScale ν P.K₀ n)))))
    {a b : ℝ}
    (h0 : ∀ x : Site ν, configurationMeasure ν law {v | x ∈ singular0 P v} ≤
      ENNReal.ofReal (Real.exp (-(5 * a))))
    (hres : 1 ≤ ν → ∀ n : ℕ, max (max nstar n₁) 1 ≤ n → ∀ c : Site ν,
      configurationMeasure ν law
      (resonanceEvent ν (thicken (dyCube n c ∩ D) (4 * scaleD P.K₀ (resScale ν P.K₀ n)) ∩ Λ)
        P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (resScale ν P.K₀ n))))) ≤
      ENNReal.ofReal (Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n)))) :
    configurationMeasure ν law (gentleEventAnyIn P Λ D) ≤
      ENNReal.ofReal (Real.exp (-(a * coverNumber 0 D +
        b * isolatedVolumeFrom (5 / 3) 2 (max (max nstar n₁) 1) D))) := by
  classical
  have : IsProbabilityMeasure (configurationMeasure ν law) := by
    unfold configurationMeasure; infer_instance
  set n' := max (max nstar n₁) 1 with hn'
  set μ := configurationMeasure ν law with hμ
  set S := gentleEventAnyIn P Λ D with hS
  set T : Finset ℕ := (Finset.Icc n' (topScale D)).filter fun n => 2 ≤ coverNumber n D with hT
  have h0T : 0 ∉ T := by
    intro h
    have := (Finset.mem_Icc.1 (Finset.mem_filter.1 h).1).1
    omega
  let w : ℕ → ℝ := fun i => (1 / 5 : ℝ) * (4 / 5) ^ i
  let t : ℕ → ℝ := fun i => if i = 0 then 5 * a * (coverNumber 0 D : ℝ)
    else 5 * b * (5 / 4 : ℝ) ^ i * (isolatedCount (5 / 3) 2 i D : ℝ)
  have hmain := measure_le_exp_neg_weighted μ S (insert 0 T) w t (fun i _ => by positivity)
    (sum_weights_le_one _) prob_le_one (fun i hi => ?_)
  · refine hmain.trans (le_of_eq ?_)
    congr 2
    rw [Finset.sum_insert h0T]
    have e0 : w 0 * t 0 = a * (coverNumber 0 D : ℝ) := by
      simp only [w, t]; simp; ring
    have e1 : ∑ i ∈ T, w i * t i = b * (isolatedVolumeFrom (5 / 3) 2 n' D : ℝ) := by
      unfold isolatedVolumeFrom
      rw [← Finset.sum_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi0 : i ≠ 0 := fun h => h0T (h ▸ hi)
      simp only [w, t, hi0, ite_false]
      have : (4 / 5 : ℝ) ^ i * (5 / 4) ^ i = 1 := by
        rw [← mul_pow]; norm_num
      calc 1 / 5 * (4 / 5 : ℝ) ^ i * (5 * b * (5 / 4) ^ i * (isolatedCount (5 / 3) 2 i D : ℝ))
          = b * (isolatedCount (5 / 3) 2 i D : ℝ) * ((4 / 5 : ℝ) ^ i * (5 / 4) ^ i) := by ring
        _ = _ := by rw [this, mul_one]
    rw [e0, e1]
  · rcases Finset.mem_insert.1 hi with rfl | hiT
    · -- scale zero
      have hA : S ⊆ ⋂ x ∈ D, {v | x ∈ singular0 P v} := by
        intro v hv
        have := (hsub hv).1
        simp only [Set.mem_iInter]
        exact this
      refine (measure_mono hA).trans ?_
      rw [configurationMeasure_biInter_eq_prod law D (fun x => ({x} : Finset (Site ν)))
        (fun x _ y _ hxy => by simpa using hxy) _ (fun x _ => dependsOn_singular0 P x)]
      calc _ ≤ ∏ x ∈ D, ENNReal.ofReal (Real.exp (-(5 * a))) :=
            Finset.prod_le_prod fun x _ => h0 x
        _ = _ := by
            rw [Finset.prod_const, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
              ← coverNumber_zero]
            simp only [t, ite_true]
            congr 2; ring
    · obtain ⟨hI, h2⟩ := Finset.mem_filter.1 hiT
      obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hI
      have hi0 : i ≠ 0 := fun h => h0T (h ▸ hiT)
      have hν := one_le_of_two_le_coverNumber h2
      have hA : S ⊆ ⋂ c ∈ isolatedCubes (5 / 3) 2 i D,
          resonanceEvent ν (thicken (dyCube i c ∩ D) (4 * scaleD P.K₀ (resScale ν P.K₀ i)) ∩ Λ)
            P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (resScale ν P.K₀ i)))) := by
        intro v hv
        have := (hsub hv).2
        simp only [Set.mem_iInter] at this ⊢
        exact this i (Finset.mem_Icc.2 ⟨by omega, hn2⟩) h2
      refine (measure_mono hA).trans ?_
      refine (measure_isolated_le law P Λ D i (hn₁ i (by omega))
        (u := 5 * b * (5 / 4 : ℝ) ^ i) (hres hν i hn1)).trans ?_
      simp only [t, hi0, ite_false]
      exact le_rfl

/-! ### Setup (regime independent) and the rate hypothesis -/

/-- Regime-independent assembly: choose `n'`, `a`, `b` (depending only on `ν`, `K₀`, `s₀`, `s'`)
so that one-site and per-cube bounds at rates `5 a`, `5 b (5/4)^n` give the target bound. -/
private theorem exists_setup (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) {s₀ s' : ℝ} (hs₀ : 0 < s₀)
    (hs' : 0 < s') :
    ∃ (n' : ℕ) (a b : ℝ), 0 ≤ a ∧ 0 ≤ b ∧
      ∀ (law : Measure ℝ) [IsProbabilityMeasure law] (P : Params),
      P.K₀ = K₀ → ∀ (Λ D : Finset (Site ν)), D.Nonempty →
        (∀ x : Site ν, configurationMeasure ν law {v | x ∈ singular0 P v} ≤
          ENNReal.ofReal (Real.exp (-(5 * a)))) →
        (1 ≤ ν → ∀ n : ℕ, n' ≤ n → ∀ c : Site ν, configurationMeasure ν law
          (resonanceEvent ν (thicken (dyCube n c ∩ D) (4 * scaleD K₀ (resScale ν K₀ n)) ∩ Λ)
            P.E (Real.exp (-Real.sqrt (scaleD K₀ (resScale ν K₀ n))))) ≤
          ENNReal.ofReal (Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n)))) →
        configurationMeasure ν law (gentleEventAnyIn P Λ D) ≤
          ENNReal.ofReal (Real.exp (-(s₀ * coverNumber 0 D) -
            s' * isolatedVolume (5 / 3) 2 D)) := by
  obtain ⟨nstar, hsub⟩ := exists_gentleEventAnyIn_subset ν hK
  obtain ⟨n₁, hn₁⟩ := exists_nstar_disjoint hK ν
  obtain ⟨Cstar, hC⟩ := exists_isolatedVolume_le ν (5 / 3) 2 (max (max nstar n₁) 1)
  refine ⟨max (max nstar n₁) 1, s₀ + Cstar * s', s', by positivity, hs'.le,
    fun law _ P hP Λ D hD h0 hres => ?_⟩
  subst hP
  refine (measure_gentleEventAnyIn_core law P Λ D nstar n₁ hn₁ (hsub P rfl Λ D)
    (a := s₀ + Cstar * s') (b := s') h0 hres).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have h1 : (isolatedVolume (5 / 3) 2 D : ℝ) ≤
      isolatedVolumeFrom (5 / 3) 2 (max (max nstar n₁) 1) D + Cstar * coverNumber 0 D := by
    exact_mod_cast hC D hD
  have h2 := mul_le_mul_of_nonneg_left h1 hs'.le
  nlinarith only [h2]

/-- From a regime bound with coefficient `ρ` to the per-cube bound used in the core. -/
private theorem resonance_cube_le_of_bound {ν : ℕ} (law : Measure ℝ) [IsProbabilityMeasure law]
    (P : Params) (hK : 0 < P.K₀) (hν : 1 ≤ ν) {b ρ : ℝ}
    (hρ : ∀ (n : ℕ) (d : ℝ), 2 * 2 ^ n ≤ d →
      Real.sqrt 2 * ρ * (11 ^ ν * (1 + d) ^ ν) * Real.exp (-Real.sqrt d / 2) ≤
        Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n)))
    (hbound : ∀ (Λ D : Finset (Site ν)) (R : ℝ), 0 ≤ R →
      DiamLE (siteDist ν) (D : Set (Site ν)) R →
      configurationMeasure ν law (resonanceEvent ν (thicken D (4 * R) ∩ Λ) P.E
        (Real.exp (-Real.sqrt R))) ≤
      ENNReal.ofReal (Real.sqrt 2 * ρ * (11 ^ ν * (1 + R) ^ ν) * Real.exp (-Real.sqrt R / 2)))
    (Λ D : Finset (Site ν)) (n : ℕ) (c : Site ν) :
    configurationMeasure ν law
      (resonanceEvent ν (thicken (dyCube n c ∩ D) (4 * scaleD P.K₀ (resScale ν P.K₀ n)) ∩ Λ)
        P.E (Real.exp (-Real.sqrt (scaleD P.K₀ (resScale ν P.K₀ n))))) ≤
      ENNReal.ofReal (Real.exp (-(5 * b * (5 / 4 : ℝ) ^ n))) := by
  set R := scaleD P.K₀ (resScale ν P.K₀ n) with hR
  have hspec := resScale_spec' hK ν n
  rw [← hR] at hspec
  have hsq : (1 : ℝ) ≤ Real.sqrt ν := by
    rw [Real.one_le_sqrt]; exact_mod_cast hν
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hRge : 2 * 2 ^ n ≤ R := by nlinarith only [hspec, hsq, h2n]
  have hR0 : 0 ≤ R := by linarith only [h2n, hRge]
  have hdiam : DiamLE (siteDist ν) ((dyCube n c ∩ D : Finset (Site ν)) : Set (Site ν)) R := by
    intro a ha b hb
    have := siteDist_le_of_mem_dyCube' (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 hb).1
    nlinarith only [hspec, hR0, this]
  exact (hbound Λ _ R hR0 hdiam).trans (ENNReal.ofReal_le_ofReal (hρ n R hRge))

/-- A property holding eventually along `cocompact ℝ` holds for all `|E|` large. -/
private theorem exists_abs_of_eventually_cocompact {p : ℝ → Prop}
    (h : ∀ᶠ E in Filter.cocompact ℝ, p E) : ∃ R : ℝ, ∀ E : ℝ, R < |E| → p E := by
  obtain ⟨K, hKc, hKs⟩ := Filter.mem_cocompact.1 h
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨R, fun E hE => hKs ?_⟩
  intro hEK
  have := hR hEK
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith only [hE, this]

/-! ### Theorem 5.1 -/


theorem exists_threshold_gentleEventAnyIn_le_boundedDensity (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀)
    {s₀ s' : ℝ} (hs₀ : 0 < s₀) (hs' : 0 < s') :
    ∃ δ₀ : ℝ, ∀ (law : Measure ℝ) [IsProbabilityMeasure law] (δ : ℝ), HasBoundedDensity law δ →
      δ₀ ≤ δ → ∀ (P : Params), P.K₀ = K₀ → P.Nthr = Real.sqrt δ →
        ∀ (Λ D : Finset (Site ν)), D.Nonempty →
          configurationMeasure ν law (gentleEventAnyIn P Λ D) ≤
            ENNReal.ofReal (Real.exp (-(s₀ * coverNumber 0 D) -
              s' * isolatedVolume (5 / 3) 2 D)) := by
  obtain ⟨n', a, b, ha, hb, hset⟩ := exists_setup ν hK hs₀ hs'
  obtain ⟨ρ₀, hρ₀, hρ⟩ := exists_rho_bound ν hb
  refine ⟨max (ρ₀⁻¹ ^ 2) ((2 * Real.exp (5 * a)) ^ 2), fun law _ δ hlaw hδ P hP hN Λ D hD => ?_⟩
  have hδpos : 0 < δ := hlaw.1
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδpos
  have hδ1 : ρ₀⁻¹ ^ 2 ≤ δ := (le_max_left _ _).trans hδ
  have hδ2 : (2 * Real.exp (5 * a)) ^ 2 ≤ δ := (le_max_right _ _).trans hδ
  have hρδ : Real.sqrt δ⁻¹ ≤ ρ₀ := by
    rw [Real.sqrt_le_left hρ₀.le]
    rw [inv_le_comm₀ hδpos (by positivity)]
    simpa [inv_pow] using hδ1
  subst hP
  refine hset law P rfl Λ D hD (fun x => ?_) (fun hν n _ c => ?_)
  · refine (configurationMeasure_singular0_le_boundedDensity law hlaw P hN x).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have h1 : 2 * Real.exp (5 * a) ≤ Real.sqrt δ := Real.le_sqrt_of_sq_le hδ2
    rw [div_le_iff₀ hsq, Real.exp_neg]
    have hpos := Real.exp_pos (5 * a)
    calc (2 : ℝ) = (Real.exp (5 * a))⁻¹ * (2 * Real.exp (5 * a)) := by field_simp
      _ ≤ _ := by gcongr
  · refine resonance_cube_le_of_bound law P hK hν (ρ := Real.sqrt δ⁻¹)
      (fun n d hd => hρ _ (Real.sqrt_nonneg _) hρδ n d hd) ?_ Λ D n c
    intro Λ' D' R hR hd
    exact measure_resonance_thicken_le_boundedDensity law hlaw P.E Λ' D' hR hd


theorem exists_threshold_gentleEventAnyIn_le_gaussian (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀)
    {γ : ℝ} (hγ : 0 < γ) {s₀ s' : ℝ} (hs₀ : 0 < s₀) (hs' : 0 < s') :
    ∃ E₀ : ℝ, ∀ (P : Params), P.K₀ = K₀ → E₀ ≤ |P.E - 2 * ν| → P.Nthr = |P.E| / 2 →
      ∀ (Λ D : Finset (Site ν)), D.Nonempty →
        configurationMeasure ν (gaussianLaw γ hγ) (gentleEventAnyIn P Λ D) ≤
          ENNReal.ofReal (Real.exp (-(s₀ * coverNumber 0 D) -
            s' * isolatedVolume (5 / 3) 2 D)) := by
  obtain ⟨n', a, b, ha, hb, hset⟩ := exists_setup ν hK hs₀ hs'
  obtain ⟨ρ₀, hρ₀, hρ⟩ := exists_rho_bound ν hb
  set L : ℝ := 1 / Real.sqrt (2 * Real.pi * γ) with hL
  have hLpos : 0 < L := by positivity
  have hev : ∀ᶠ E in Filter.cocompact ℝ, L * (gaussianLaw γ hγ).real
      {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1} < ρ₀ ^ 2 := by
    have := (tendsto_gaussianLaw_window ν hγ).const_mul L
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨Rt, hRt⟩ := exists_abs_of_eventually_cocompact hev
  set X : ℝ := max 1 (2 * γ * (5 * a + Real.log 2)) with hX
  refine ⟨max (Rt + 2 * ν + 1) (2 * X + 6 * ν), fun P hP hE hN Λ D hD => ?_⟩
  have hE1 : Rt + 2 * ν + 1 ≤ |P.E - 2 * ν| := (le_max_left _ _).trans hE
  have hE2 : 2 * X + 6 * ν ≤ |P.E - 2 * ν| := (le_max_right _ _).trans hE
  have hν0 : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
  have habs : |P.E - 2 * ν| ≤ |P.E| + 2 * ν := by
    have := abs_sub (P.E) (2 * (ν : ℝ))
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ν)] at this
  have hX1 : (1 : ℝ) ≤ X := le_max_left _ _
  have hxX : X ≤ |P.E| / 2 - 2 * ν := by linarith only [hE2, habs]
  have hEpos : 2 * (ν : ℝ) < |P.E| / 2 := by linarith only [hX1, hxX]
  subst hP
  refine hset (gaussianLaw γ hγ) P rfl Λ D hD (fun x => ?_) (fun hν n _ c => ?_)
  · refine (configurationMeasure_singular0_le_gaussian hγ P hN hEpos x).trans ?_
    apply ENNReal.ofReal_le_ofReal
    set x' := |P.E| / 2 - 2 * ν with hx'
    have hx1 : 2 * γ * (5 * a + Real.log 2) ≤ x' := (le_max_right _ _).trans hxX
    have hx2 : 1 ≤ x' := hX1.trans hxX
    have hlog : 0 ≤ 5 * a + Real.log 2 := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      linarith only [ha, this]
    have h3 : 5 * a + Real.log 2 ≤ x' ^ 2 / (2 * γ) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hx1, hx2, mul_nonneg hγ.le hlog]
    have h4 : Real.exp (-x' ^ 2 / (2 * γ)) ≤ Real.exp (-(5 * a + Real.log 2)) := by
      apply Real.exp_le_exp.2
      rw [neg_div]; linarith only [h3]
    have h5 : Real.exp (-(5 * a + Real.log 2)) = Real.exp (-(5 * a)) / 2 := by
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 2), Real.exp_log (by norm_num)]
      ring
    rw [h5] at h4
    linarith only [h4]
  · have hρE : Real.sqrt (L * (gaussianLaw γ hγ).real
        {t | |t - (P.E - 2 * ν)| ≤ 2 * ν + 1}) ≤ ρ₀ := by
      rw [Real.sqrt_le_left hρ₀.le]
      exact (hRt P.E (by linarith only [hE1, habs])).le
    refine resonance_cube_le_of_bound (gaussianLaw γ hγ) P hK hν
      (ρ := Real.sqrt (L * (gaussianLaw γ hγ).real {t | |t - (P.E - 2 * ν)| ≤ 2 * ν + 1}))
      (fun n d hd => hρ _ (Real.sqrt_nonneg _) hρE n d hd) ?_ Λ D n c
    intro Λ' D' R hR hd
    exact measure_resonance_thicken_le_gaussian hγ P.E Λ' D' hR hd

/-- Rates for the `V(D)` form: from `V ≤ K₀' V₀ + K' V'` choose `s₀, s' > 0` with
`t V ≤ s₀ V₀ + s' V'`. -/
private theorem exists_rates_volume (ν : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ s₀ s' : ℝ, 0 < s₀ ∧ 0 < s' ∧ ∀ D : Finset (Site ν),
      t * (coverVolume D : ℝ) ≤ s₀ * coverNumber 0 D + s' * isolatedVolume (5 / 3) 2 D := by
  obtain ⟨K₀', K', h⟩ := exists_coverVolume_le ν (α := 5 / 3) (M := 2) (by norm_num) (by norm_num)
  refine ⟨t * (|K₀'| + 1), t * (|K'| + 1), by positivity, by positivity, fun D => ?_⟩
  have h1 := h D
  have hV0 : (0 : ℝ) ≤ coverNumber 0 D := Nat.cast_nonneg _
  have hV' : (0 : ℝ) ≤ isolatedVolume (5 / 3) 2 D := Nat.cast_nonneg _
  have a1 : K₀' * coverNumber 0 D ≤ (|K₀'| + 1) * coverNumber 0 D :=
    mul_le_mul_of_nonneg_right (by linarith only [le_abs_self K₀']) hV0
  have a2 : K' * isolatedVolume (5 / 3) 2 D ≤ (|K'| + 1) * isolatedVolume (5 / 3) 2 D :=
    mul_le_mul_of_nonneg_right (by linarith only [le_abs_self K']) hV'
  nlinarith only [ht, h1, a1, a2]


theorem exists_threshold_gentleEventAnyIn_le_volume_boundedDensity (ν : ℕ) {K₀ : ℝ}
    (hK : 0 < K₀) {t : ℝ} (ht : 0 < t) :
    ∃ δ₀ : ℝ, ∀ (law : Measure ℝ) [IsProbabilityMeasure law] (δ : ℝ), HasBoundedDensity law δ →
      δ₀ ≤ δ → ∀ (P : Params), P.K₀ = K₀ → P.Nthr = Real.sqrt δ →
        ∀ (Λ D : Finset (Site ν)), D.Nonempty →
          configurationMeasure ν law (gentleEventAnyIn P Λ D) ≤
            ENNReal.ofReal (Real.exp (-(t * coverVolume D))) := by
  obtain ⟨s₀, s', hs₀, hs', hrate⟩ := exists_rates_volume ν ht
  obtain ⟨δ₀, h⟩ := exists_threshold_gentleEventAnyIn_le_boundedDensity ν hK hs₀ hs'
  refine ⟨δ₀, fun law _ δ hlaw hδ P hP hN Λ D hD => ?_⟩
  refine (h law δ hlaw hδ P hP hN Λ D hD).trans (ENNReal.ofReal_le_ofReal ?_)
  apply Real.exp_le_exp.2
  linarith only [hrate D]


theorem exists_threshold_gentleEventAnyIn_le_volume_gaussian (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀)
    {γ : ℝ} (hγ : 0 < γ) {t : ℝ} (ht : 0 < t) :
    ∃ E₀ : ℝ, ∀ (P : Params), P.K₀ = K₀ → E₀ ≤ |P.E - 2 * ν| → P.Nthr = |P.E| / 2 →
      ∀ (Λ D : Finset (Site ν)), D.Nonempty →
        configurationMeasure ν (gaussianLaw γ hγ) (gentleEventAnyIn P Λ D) ≤
          ENNReal.ofReal (Real.exp (-(t * coverVolume D))) := by
  obtain ⟨s₀, s', hs₀, hs', hrate⟩ := exists_rates_volume ν ht
  obtain ⟨E₀, h⟩ := exists_threshold_gentleEventAnyIn_le_gaussian ν hK hγ hs₀ hs'
  refine ⟨E₀, fun P hP hE hN Λ D hD => ?_⟩
  refine (h P hP hE hN Λ D hD).trans (ENNReal.ofReal_le_ofReal ?_)
  apply Real.exp_le_exp.2
  linarith only [hrate D]

end FroehlichSpencer.T12

end
