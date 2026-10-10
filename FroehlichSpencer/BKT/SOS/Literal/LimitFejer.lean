/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitGauss

/-!
# Positive definiteness of FS81's factor `E_β` (the comb-inserted SOS construction)

FS81's (C.1) is `I_β = L_β E_β` with `E_β(t) = exp h(t)`, `h(t) = Σ_n c_n sinc²(t − n)` and
`c_n = β^{2/3}(1 + β^{2/3}n²)^{1/2} − β|n| > 0` (FS81). We prove that `E_β` is the
Fourier transform of an explicit finite nonnegative measure `η` (no Bochner theorem):

* `integral_tri_mul_cexp`: the triangle `(1 − |ω|)₊` has transform `sinc²(πu)`;
* `fejer_nonneg`: the Fejér kernel `(K+1) + 2Σ_{j<K}(K−j)cos(2π(j+1)ω)` is `≥ 0` (a sum of squares);
* `hasSum_fejer_decomposition`: for a convex null sequence, `c_m = Σ_i (i+1)Δ²c_{m+i}`;
* so `h = m̂_h` for `m_h = Σ_K (K+1)Δ²c_K (1 − |ω|)₊ fej_K(ω)/(K+1) dω` (`integral_cexp_hMeasure`);
* `E_β = e^h = η̂` with `η = Σ_j (1/j!) (Σ_l ω_l)_* m_h^{⊗j}` (`integral_cexp_etaMeasure`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Complex Filter Topology Finset
open scoped Real NNReal ENNReal Nat

/-! ## The triangle and its transform -/

/-- The triangle `(1 − |ω|)₊`. -/
def tri (ω : ℝ) : ℝ := max (1 - |ω|) 0

theorem tri_nonneg (ω : ℝ) : 0 ≤ tri ω := le_max_right _ _

theorem tri_le_one (ω : ℝ) : tri ω ≤ 1 :=
  max_le (by linarith [abs_nonneg ω]) zero_le_one

theorem tri_eq_zero {ω : ℝ} (h : ω ∉ Set.Ioc (-1 : ℝ) 1) : tri ω = 0 := by
  unfold tri
  rw [max_eq_right]
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem continuous_tri : Continuous tri := by
  unfold tri; fun_prop

/-- `∫₀¹ 2(1 − ω) cos(2πuω) dω = sinc(πu)²`. -/
theorem integral_tri_cos (u : ℝ) :
    ∫ ω in (0 : ℝ)..1, 2 * (1 - ω) * Real.cos (2 * π * u * ω) = Real.sinc (π * u) ^ 2 := by
  by_cases hu : u = 0
  · subst hu
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, Real.sinc_zero, one_pow]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp
    norm_num
  set α := 2 * π * u with hα
  have hα0 : α ≠ 0 := by
    rw [hα]; exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hu
  have hd : ∀ ω ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun ω => 2 * ((1 - ω) * Real.sin (α * ω) / α - Real.cos (α * ω) / α ^ 2))
      (2 * (1 - ω) * Real.cos (α * ω)) ω := by
    intro ω _
    have h1 : HasDerivAt (fun ω : ℝ => α * ω) α ω := by
      simpa using (hasDerivAt_id ω).const_mul α
    have hs := (Real.hasDerivAt_sin (α * ω)).comp ω h1
    have hc := (Real.hasDerivAt_cos (α * ω)).comp ω h1
    have h2 : HasDerivAt (fun ω : ℝ => 1 - ω) (-1) ω := (hasDerivAt_id ω).const_sub 1
    have := (((h2.mul hs).div_const α).sub (hc.div_const (α ^ 2))).const_mul 2
    refine this.congr_deriv ?_
    simp only [Function.comp]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun ω : ℝ => 2 * (1 - ω) * Real.cos (α * ω)).intervalIntegrable _ _)]
  simp only [sub_self, zero_mul, zero_div, mul_one, mul_zero, Real.cos_zero, Real.sin_zero]
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hu), div_pow]
  have hcos : Real.cos α = 1 - 2 * Real.sin (π * u) ^ 2 := by
    rw [hα, show 2 * π * u = 2 * (π * u) by ring, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hcos, hα]
  have hpu : π * u ≠ 0 := mul_ne_zero Real.pi_ne_zero hu
  field_simp
  ring

/-- **The transform of the triangle**: `∫ (1 − |ω|)₊ e^{2πiωu} dω = sinc(πu)²`. -/
theorem integral_tri_mul_cexp (u : ℝ) :
    ∫ ω, ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * u) = ((Real.sinc (π * u) ^ 2 : ℝ) : ℂ) := by
  have hzero : ∀ ω ∉ Set.Ioc (-1 : ℝ) 1, ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * u) = 0 :=
    fun ω hω => by rw [tri_eq_zero hω, Complex.ofReal_zero, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hcont : Continuous fun ω : ℝ => ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * u) := by
    have := continuous_tri; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  have hneg : ∫ ω in (-1 : ℝ)..0, ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * u) =
      ∫ ω in (0 : ℝ)..1, ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * (-ω) * u) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1)
      (fun ω : ℝ => ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * u))
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun ω _ => ?_
    simp only [tri, abs_neg, Complex.ofReal_neg]
  rw [hneg, add_comm, ← intervalIntegral.integral_add (hcont.intervalIntegrable _ _)
    ((by have := continuous_tri; fun_prop : Continuous fun ω : ℝ =>
      ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * (-ω) * u)).intervalIntegrable _ _)]
  have hcongr : ∀ ω ∈ Set.uIcc (0 : ℝ) 1,
      ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * u) +
        ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * (-ω) * u) =
      ((2 * (1 - ω) * Real.cos (2 * π * u * ω) : ℝ) : ℂ) := by
    intro ω hω
    rw [Set.uIcc_of_le zero_le_one] at hω
    have htri : tri ω = 1 - ω := by
      unfold tri; rw [abs_of_nonneg hω.1, max_eq_left (by linarith [hω.2])]
    rw [htri, ← mul_add, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cos,
      Complex.cos.eq_1]
    push_cast
    have e1 : 2 * (π : ℂ) * I * ω * u = (2 * π * u * ω) * I := by ring
    have e2 : 2 * (π : ℂ) * I * (-ω) * u = -((2 * π * u * ω) * I) := by ring
    rw [e1, e2]
    have e3 : -((2 * (π : ℂ) * u * ω) * I) = -(2 * π * u * ω) * I := by ring
    rw [e3]
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal, integral_tri_cos]

/-! ## The Fejér kernel -/

theorem sum_range_sum_range_sub_succ (g : ℤ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), ∑ i' ∈ range (n + 1), g ((i : ℤ) - i') =
      ∑ i ∈ range n, ∑ i' ∈ range n, g ((i : ℤ) - i') + ∑ i ∈ range n, g ((i : ℤ) - n) +
        ∑ i' ∈ range n, g ((n : ℤ) - i') + g 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i' => g ((n : ℤ) - i'))]
  simp_rw [Finset.sum_range_succ (fun i' : ℕ => g (_ - (i' : ℤ))) n]
  rw [Finset.sum_add_distrib, sub_self]
  ring

theorem sum_range_reflect_neg (g : ℤ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, g ((i : ℤ) - n) = ∑ j ∈ range n, g (-((j : ℤ) + 1)) := by
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  congr 1
  omega

theorem sum_range_reflect_pos (g : ℤ → ℝ) (n : ℕ) :
    ∑ i' ∈ range n, g ((n : ℤ) - i') = ∑ j ∈ range n, g ((j : ℤ) + 1) := by
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  congr 1
  omega

/-- **The counting identity** `Σ_{i,i' ≤ K} g(i − i') = (K+1)g(0) + Σ_{j<K}(K−j)(g(j+1) + g(−(j+1)))`. -/
theorem sum_range_sum_range_sub (g : ℤ → ℝ) (K : ℕ) :
    ∑ i ∈ range (K + 1), ∑ i' ∈ range (K + 1), g ((i : ℤ) - i') =
      ((K : ℝ) + 1) * g 0 + ∑ j ∈ range K, ((K : ℝ) - j) * (g ((j : ℤ) + 1) + g (-((j : ℤ) + 1))) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_sum_range_sub_succ, ih, sum_range_reflect_neg, sum_range_reflect_pos]
    set G : ℕ → ℝ := fun j => g ((j : ℤ) + 1) + g (-((j : ℤ) + 1)) with hG
    have h3 : ∑ j ∈ range (K + 1), (((K + 1 : ℕ) : ℝ) - j) * G j =
        ∑ j ∈ range K, ((K : ℝ) - j) * G j + ∑ j ∈ range (K + 1), G j := by
      calc ∑ j ∈ range (K + 1), (((K + 1 : ℕ) : ℝ) - j) * G j
          = ∑ j ∈ range (K + 1), (((K : ℝ) - j) * G j + G j) :=
            Finset.sum_congr rfl fun j _ => by push_cast; ring
        _ = ∑ j ∈ range (K + 1), ((K : ℝ) - j) * G j + ∑ j ∈ range (K + 1), G j :=
            Finset.sum_add_distrib
        _ = _ := by rw [Finset.sum_range_succ (fun j : ℕ => ((K : ℝ) - j) * G j), sub_self, zero_mul,
            add_zero]
    have h4 : ∑ j ∈ range (K + 1), G j =
        ∑ j ∈ range (K + 1), g ((j : ℤ) + 1) + ∑ j ∈ range (K + 1), g (-((j : ℤ) + 1)) :=
      Finset.sum_add_distrib
    rw [h3, h4]
    push_cast
    ring

/-- The Fejér kernel `(K+1) + 2Σ_{j<K}(K−j)cos(2π(j+1)ω)`. -/
def fej (K : ℕ) (ω : ℝ) : ℝ :=
  ((K : ℝ) + 1) + ∑ j ∈ range K, ((K : ℝ) - j) * (2 * Real.cos (2 * π * ((j : ℝ) + 1) * ω))

/-- **The Fejér kernel is nonnegative**: it is `|Σ_{i≤K} e^{2πiωi}|²`. -/
theorem fejer_nonneg (K : ℕ) (ω : ℝ) : 0 ≤ fej K ω := by
  have h := sum_range_sum_range_sub (fun n : ℤ => Real.cos (2 * π * ω * n)) K
  have hfej : fej K ω = ((K : ℝ) + 1) * Real.cos (2 * π * ω * ((0 : ℤ) : ℝ)) +
      ∑ j ∈ range K, ((K : ℝ) - j) * (Real.cos (2 * π * ω * (((j : ℤ) + 1 : ℤ) : ℝ)) +
        Real.cos (2 * π * ω * ((-((j : ℤ) + 1) : ℤ) : ℝ))) := by
    unfold fej
    simp only [Int.cast_zero, mul_zero, Real.cos_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [show 2 * π * ω * -((j : ℝ) + 1) = -(2 * π * ((j : ℝ) + 1) * ω) by ring, Real.cos_neg,
      show 2 * π * ω * ((j : ℝ) + 1) = 2 * π * ((j : ℝ) + 1) * ω by ring]
    ring
  rw [hfej, ← h]
  have hsq : ∀ i i' : ℕ, Real.cos (2 * π * ω * (((i : ℤ) - i' : ℤ) : ℝ)) =
      Real.cos (2 * π * ω * i) * Real.cos (2 * π * ω * i') +
        Real.sin (2 * π * ω * i) * Real.sin (2 * π * ω * i') := by
    intro i i'
    push_cast
    rw [show 2 * π * ω * ((i : ℝ) - i') = 2 * π * ω * i - 2 * π * ω * i' by ring, Real.cos_sub]
  simp_rw [hsq, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  nlinarith [sq_nonneg (∑ i ∈ range (K + 1), Real.cos (2 * π * ω * i)),
    sq_nonneg (∑ i ∈ range (K + 1), Real.sin (2 * π * ω * i))]

theorem integrable_tri_mul_cexp (u : ℝ) :
    Integrable fun ω : ℝ => ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * u) := by
  have hc : Continuous fun ω : ℝ => ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * u) := by
    have := continuous_tri; fun_prop
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun ω hω => ?_
  rw [tri_eq_zero (fun h => hω (Set.Ioc_subset_Icc_self h)), Complex.ofReal_zero, zero_mul]

/-- `sinc(πu)²`. -/
def sincSqR (u : ℝ) : ℝ := Real.sinc (π * u) ^ 2

theorem integral_tri_cos_mul_cexp (m t : ℝ) :
    ∫ ω, ((tri ω * (2 * Real.cos (2 * π * m * ω)) : ℝ) : ℂ) * cexp (2 * π * I * ω * t) =
      ((sincSqR (t + m) + sincSqR (t - m) : ℝ) : ℂ) := by
  have hpt : ∀ ω : ℝ, ((tri ω * (2 * Real.cos (2 * π * m * ω)) : ℝ) : ℂ) *
      cexp (2 * π * I * ω * t) =
      ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * ((t + m : ℝ) : ℂ)) +
        ((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * ((t - m : ℝ) : ℂ)) := by
    intro ω
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos.eq_1]
    have e1 : 2 * (π : ℂ) * I * ω * ((t + m : ℝ) : ℂ) =
        2 * π * I * ω * t + ((2 * π * m * ω : ℝ) : ℂ) * I := by push_cast; ring
    have e2 : 2 * (π : ℂ) * I * ω * ((t - m : ℝ) : ℂ) =
        2 * π * I * ω * t + -((2 * π * m * ω : ℝ) : ℂ) * I := by push_cast; ring
    rw [e1, e2, Complex.exp_add, Complex.exp_add]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_add (integrable_tri_mul_cexp _) (integrable_tri_mul_cexp _),
    integral_tri_mul_cexp, integral_tri_mul_cexp]
  unfold sincSqR
  push_cast
  ring

/-- The kernel `T_K(t) = (K+1)s(t) + Σ_{j<K}(K−j)(s(t+j+1) + s(t−j−1))`. -/
def fejT (K : ℕ) (t : ℝ) : ℝ :=
  ((K : ℝ) + 1) * sincSqR t +
    ∑ j ∈ range K, ((K : ℝ) - j) * (sincSqR (t + ((j : ℝ) + 1)) + sincSqR (t - ((j : ℝ) + 1)))

theorem integrable_tri_cos_mul_cexp (m t : ℝ) :
    Integrable fun ω : ℝ =>
      ((tri ω * (2 * Real.cos (2 * π * m * ω)) : ℝ) : ℂ) * cexp (2 * π * I * ω * t) := by
  have hc : Continuous fun ω : ℝ =>
      ((tri ω * (2 * Real.cos (2 * π * m * ω)) : ℝ) : ℂ) * cexp (2 * π * I * ω * t) := by
    have := continuous_tri; fun_prop
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun ω hω => ?_
  rw [tri_eq_zero (fun h => hω (Set.Ioc_subset_Icc_self h)), zero_mul, Complex.ofReal_zero,
    zero_mul]

/-- **The transform of `tri · fej_K`** is `T_K`. -/
theorem integral_tri_fej_mul_cexp (K : ℕ) (t : ℝ) :
    ∫ ω, ((tri ω * fej K ω : ℝ) : ℂ) * cexp (2 * π * I * ω * t) = ((fejT K t : ℝ) : ℂ) := by
  have hpt : ∀ ω : ℝ, ((tri ω * fej K ω : ℝ) : ℂ) * cexp (2 * π * I * ω * t) =
      ((K : ℂ) + 1) * (((tri ω : ℝ) : ℂ) * cexp (2 * π * I * ω * t)) +
        ∑ j ∈ range K, ((K : ℂ) - j) *
          (((tri ω * (2 * Real.cos (2 * π * ((j : ℝ) + 1) * ω)) : ℝ) : ℂ) *
            cexp (2 * π * I * ω * t)) := by
    intro ω
    unfold fej
    rw [mul_add, Complex.ofReal_add, add_mul, Finset.mul_sum, Complex.ofReal_sum,
      Finset.sum_mul]
    congr 1
    · push_cast; ring
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_add ((integrable_tri_mul_cexp t).const_mul _) (integrable_finsetSum _ fun j _ =>
    (integrable_tri_cos_mul_cexp _ _).const_mul _), integral_const_mul,
    integral_finsetSum _ fun j _ => (integrable_tri_cos_mul_cexp _ _).const_mul _]
  simp_rw [integral_const_mul, integral_tri_cos_mul_cexp, integral_tri_mul_cexp]
  unfold fejT sincSqR
  push_cast
  ring

/-! ## Convex null sequences -/

/-- The second difference `Δ²c_k = c_k − 2c_{k+1} + c_{k+2}`. -/
def dd2 (c : ℕ → ℝ) (k : ℕ) : ℝ := c k - 2 * c (k + 1) + c (k + 2)

theorem sum_range_fejer_partial (c : ℕ → ℝ) (m J : ℕ) :
    ∑ i ∈ range J, ((i : ℝ) + 1) * dd2 c (m + i) =
      c m - c (m + J) - (J : ℝ) * (c (m + J) - c (m + J + 1)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    unfold dd2
    rw [show m + (J + 1) = m + J + 1 by ring, show m + J + 2 = m + J + 1 + 1 by ring]
    push_cast
    ring

/-- For a convex nonincreasing null sequence, `k(c_k − c_{k+1}) → 0`. -/
theorem tendsto_mul_sub_of_convex {c : ℕ → ℝ} (hconv : ∀ k, 0 ≤ dd2 c k)
    (hdec : ∀ k, c (k + 1) ≤ c k) (hlim : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => (k : ℝ) * (c k - c (k + 1))) atTop (𝓝 0) := by
  have hanti : ∀ k, c (k + 1) - c (k + 2) ≤ c k - c (k + 1) := fun k => by
    have := hconv k; unfold dd2 at this; linarith
  have hd : ∀ n k : ℕ, n ≤ k → c k - c (k + 1) ≤ c n - c (n + 1) := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact (hanti k).trans ih
  have htel : ∀ n k : ℕ, n ≤ k → ((k : ℝ) - n) * (c k - c (k + 1)) ≤ c n - c k := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have h1 := hd k (k + 1) (Nat.le_succ k)
      have h2 : (0 : ℝ) ≤ (k : ℝ) - n := by
        have : (n : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have h3 : 0 ≤ c (k + 1) - c (k + 1 + 1) := by linarith [hdec (k + 1)]
      push_cast
      nlinarith
  have hupper : ∀ k : ℕ, (k : ℝ) * (c k - c (k + 1)) ≤ 2 * c (k / 2) := by
    intro k
    have h := htel (k / 2) k (Nat.div_le_self k 2)
    have hk2 : (k : ℝ) ≤ 2 * ((k : ℝ) - ((k / 2 : ℕ) : ℝ)) := by
      have : ((k / 2 : ℕ) : ℝ) * 2 ≤ k := by exact_mod_cast Nat.div_mul_le_self k 2
      linarith
    have hdk : 0 ≤ c k - c (k + 1) := by linarith [hdec k]
    have hck : ∀ n, 0 ≤ c n := by
      intro n
      have : ∀ j, n ≤ j → c j ≤ c n := by
        intro j hj
        induction j, hj using Nat.le_induction with
        | base => exact le_rfl
        | succ j _ ih => exact (hdec j).trans ih
      exact le_of_tendsto hlim (eventually_atTop.mpr ⟨n, this⟩)
    have := hck k
    nlinarith
  have hlow : ∀ k : ℕ, 0 ≤ (k : ℝ) * (c k - c (k + 1)) := fun k =>
    mul_nonneg (Nat.cast_nonneg k) (by linarith [hdec k])
  have hhalf : Tendsto (fun k : ℕ => 2 * c (k / 2)) atTop (𝓝 0) := by
    have := (hlim.comp (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))).const_mul 2
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhalf hlow hupper

/-- **Fejér's decomposition**: `c_m = Σ_i (i+1) Δ²c_{m+i}` for a convex nonincreasing null
sequence. -/
theorem hasSum_fejer_decomposition {c : ℕ → ℝ} (hconv : ∀ k, 0 ≤ dd2 c k)
    (hdec : ∀ k, c (k + 1) ≤ c k) (hlim : Tendsto c atTop (𝓝 0)) (m : ℕ) :
    HasSum (fun i : ℕ => ((i : ℝ) + 1) * dd2 c (m + i)) (c m) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => mul_nonneg (by positivity) (hconv _))]
  simp_rw [sum_range_fejer_partial]
  have hshift : Tendsto (fun J : ℕ => m + J) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => Nat.add_le_add_left h m) fun b => ⟨b, by omega⟩
  have h1 : Tendsto (fun J : ℕ => c (m + J)) atTop (𝓝 0) := hlim.comp hshift
  have h2 := (tendsto_mul_sub_of_convex hconv hdec hlim).comp hshift
  have h3 : Tendsto (fun J : ℕ => (J : ℝ) * (c (m + J) - c (m + J + 1))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun J => ?_)
      (fun J => ?_)
    · exact mul_nonneg (Nat.cast_nonneg J) (by linarith [hdec (m + J)])
    · simp only [Function.comp_apply]
      push_cast
      exact mul_le_mul_of_nonneg_right (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
        (by linarith [hdec (m + J)])
  have := (tendsto_const_nhds (x := c m)).sub h1 |>.sub h3
  simpa using this

/-! ## FS81's coefficients `c_k` -/

/-- `g(x) = √(1+x²) − x`. -/
def sqrtGap (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2) - x

theorem sqrtGap_mul (x : ℝ) : sqrtGap x * (Real.sqrt (1 + x ^ 2) + x) = 1 := by
  unfold sqrtGap
  have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + x ^ 2)
  nlinarith

theorem sqrt_one_add_sq_gt (x : ℝ) : x < Real.sqrt (1 + x ^ 2) := by
  rcases le_or_gt x 0 with hx | hx
  · exact lt_of_le_of_lt hx (Real.sqrt_pos.mpr (by positivity))
  · rw [Real.lt_sqrt hx.le]; linarith

theorem sqrtGap_pos (x : ℝ) : 0 < sqrtGap x := by
  unfold sqrtGap; linarith [sqrt_one_add_sq_gt x]

theorem sqrtGap_le {x : ℝ} (hx : 0 ≤ x) : sqrtGap x ≤ 1 / (1 + x) := by
  have h1 := sqrtGap_mul x
  have h2 : 1 ≤ Real.sqrt (1 + x ^ 2) := by
    rw [Real.le_sqrt zero_le_one] <;> nlinarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith [sqrtGap_pos x]

theorem sqrtGap_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : sqrtGap y ≤ sqrtGap x := by
  have h1 := sqrtGap_mul x
  have h2 := sqrtGap_mul y
  have h3 : Real.sqrt (1 + x ^ 2) ≤ Real.sqrt (1 + y ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hpy := sqrtGap_pos y
  have hD : Real.sqrt (1 + x ^ 2) + x ≤ Real.sqrt (1 + y ^ 2) + y := by linarith
  have hDx : 0 < Real.sqrt (1 + x ^ 2) + x := by
    have := Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + x ^ 2); linarith
  have h4 := mul_le_mul_of_nonneg_left hD hpy.le
  by_contra h
  push Not at h
  have h5 := mul_lt_mul_of_pos_right h hDx
  linarith

/-- `√(1+x²) + √(1+(x+2r)²) ≥ 2√(1+(x+r)²)`. -/
theorem sqrtGap_convex (x r : ℝ) :
    0 ≤ sqrtGap x - 2 * sqrtGap (x + r) + sqrtGap (x + 2 * r) := by
  unfold sqrtGap
  set X := Real.sqrt (1 + x ^ 2)
  set Y := Real.sqrt (1 + (x + 2 * r) ^ 2)
  set Z := Real.sqrt (1 + (x + r) ^ 2)
  have hX : X ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hY : Y ^ 2 = 1 + (x + 2 * r) ^ 2 := Real.sq_sqrt (by positivity)
  have hZ : Z ^ 2 = 1 + (x + r) ^ 2 := Real.sq_sqrt (by positivity)
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
  have hXY : 1 + x * (x + 2 * r) ≤ X * Y := by
    have hprod : (X * Y) ^ 2 = (1 + x ^ 2) * (1 + (x + 2 * r) ^ 2) := by
      rw [mul_pow, hX, hY]
    have h0 : 0 ≤ X * Y := mul_nonneg hX0 hY0
    have hge : (1 + x * (x + 2 * r)) ^ 2 ≤ (X * Y) ^ 2 := by
      rw [hprod]; nlinarith [sq_nonneg r]
    nlinarith [sq_nonneg (X * Y - (1 + x * (x + 2 * r))),
      sq_nonneg (X * Y + (1 + x * (x + 2 * r)))]
  have hsum : (2 * Z) ^ 2 ≤ (X + Y) ^ 2 := by nlinarith
  have : 2 * Z ≤ X + Y := by nlinarith [sq_nonneg (X + Y - 2 * Z)]
  linarith

theorem rpow_two_thirds_mul_sqrt {β : ℝ} (hβ : 0 < β) :
    β ^ (2 / 3 : ℝ) * Real.sqrt (β ^ (2 / 3 : ℝ)) = β := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hβ.le, ← Real.rpow_add hβ]
  norm_num

/-- FS81's coefficient `c_k = β^{2/3}(1 + β^{2/3}k²)^{1/2} − βk` of (C.1) (`= −sosDefect β k`). -/
def fsC (β : ℝ) (k : ℕ) : ℝ := -Interp.sosDefect β k

theorem fsC_eq {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    fsC β k = β ^ (2 / 3 : ℝ) * sqrtGap (Real.sqrt (β ^ (2 / 3 : ℝ)) * k) := by
  unfold fsC Interp.sosDefect sqrtGap
  have hb : 0 ≤ β ^ (2 / 3 : ℝ) := Real.rpow_nonneg hβ.le _
  have h1 : (Real.sqrt (β ^ (2 / 3 : ℝ)) * k) ^ 2 = β ^ (2 / 3 : ℝ) * (k : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb]
  have h2 := rpow_two_thirds_mul_sqrt hβ
  rw [h1]
  push_cast
  rw [abs_of_nonneg (Nat.cast_nonneg k)]
  nth_rewrite 1 [← h2]
  ring

theorem fsC_nonneg {β : ℝ} (hβ : 0 < β) (k : ℕ) : 0 ≤ fsC β k := by
  rw [fsC_eq hβ]
  exact mul_nonneg (Real.rpow_nonneg hβ.le _) (sqrtGap_pos _).le

theorem fsC_succ_le {β : ℝ} (hβ : 0 < β) (k : ℕ) : fsC β (k + 1) ≤ fsC β k := by
  rw [fsC_eq hβ, fsC_eq hβ]
  refine mul_le_mul_of_nonneg_left (sqrtGap_anti (by positivity) ?_)
    (Real.rpow_nonneg hβ.le _)
  push_cast
  nlinarith [Real.sqrt_nonneg (β ^ (2 / 3 : ℝ))]

theorem fsC_convex {β : ℝ} (hβ : 0 < β) (k : ℕ) : 0 ≤ dd2 (fsC β) k := by
  unfold dd2
  rw [fsC_eq hβ, fsC_eq hβ, fsC_eq hβ]
  set r := Real.sqrt (β ^ (2 / 3 : ℝ))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have h := sqrtGap_convex (r * k) r
  have e1 : r * ((k + 1 : ℕ) : ℝ) = r * k + r := by push_cast; ring
  have e2 : r * ((k + 2 : ℕ) : ℝ) = r * k + 2 * r := by push_cast; ring
  rw [e1, e2]
  have hb : 0 ≤ β ^ (2 / 3 : ℝ) := Real.rpow_nonneg hβ.le _
  nlinarith

theorem tendsto_fsC {β : ℝ} (hβ : 0 < β) : Tendsto (fsC β) atTop (𝓝 0) := by
  set r := Real.sqrt (β ^ (2 / 3 : ℝ))
  have hr : 0 < r := Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hβ _)
  have hb : 0 ≤ β ^ (2 / 3 : ℝ) := Real.rpow_nonneg hβ.le _
  have hup : ∀ k : ℕ, fsC β k ≤ β ^ (2 / 3 : ℝ) * (1 / (1 + r * k)) := fun k => by
    rw [fsC_eq hβ]
    exact mul_le_mul_of_nonneg_left (sqrtGap_le (by positivity)) hb
  have hlim : Tendsto (fun k : ℕ => β ^ (2 / 3 : ℝ) * (1 / (1 + r * k))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 + r * (k : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop hr)
    have h2 := (h1.inv_tendsto_atTop).const_mul (β ^ (2 / 3 : ℝ))
    simpa [one_div] using h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fsC_nonneg hβ) hup

theorem fsC_zero {β : ℝ} (hβ : 0 < β) : fsC β 0 = β ^ (2 / 3 : ℝ) := by
  rw [fsC_eq hβ]
  simp [sqrtGap]

/-! ## `h = Σ_K Δ²c_K T_K` -/

theorem sincSqR_nonneg (u : ℝ) : 0 ≤ sincSqR u := sq_nonneg _

theorem sincSqR_le (u : ℝ) : sincSqR u ≤ 2 / (1 + u ^ 2) := by
  have h := Rotator.BesselInterp.norm_sincSq_le_majorant (u : ℂ)
  rw [Rotator.BesselInterp.sincSq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)] at h
  simpa [sincSqR] using h

theorem sincSqR_intCast (n : ℤ) : sincSqR n = if n = 0 then 1 else 0 := by
  unfold sincSqR
  split_ifs with h
  · subst h; simp
  · rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero (Int.cast_ne_zero.mpr h)),
      mul_comm, Real.sin_int_mul_pi]
    simp

theorem summable_sincSqR_shift (t : ℝ) : Summable fun n : ℤ => sincSqR (t - n) := by
  refine Summable.of_nonneg_of_le (fun n => sincSqR_nonneg _) (fun n => sincSqR_le _)
    ((Rotator.BesselInterp.summable_inv_one_add_sq_shift t).mul_left 2 |>.congr fun n => ?_)
  ring

theorem nonneg_of_convex {c : ℕ → ℝ} (hdec : ∀ k, c (k + 1) ≤ c k)
    (hlim : Tendsto c atTop (𝓝 0)) (n : ℕ) : 0 ≤ c n := by
  have : ∀ j, n ≤ j → c j ≤ c n := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact (hdec j).trans ih
  exact le_of_tendsto hlim (eventually_atTop.mpr ⟨n, this⟩)

theorem le_zero_of_dec {c : ℕ → ℝ} (hdec : ∀ k, c (k + 1) ≤ c k) (n : ℕ) : c n ≤ c 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (hdec n).trans ih

/-- **`h = Σ_K Δ²c_K T_K`** for a convex nonincreasing null sequence. -/
theorem hasSum_dd2_mul_fejT {c : ℕ → ℝ} (hconv : ∀ k, 0 ≤ dd2 c k)
    (hdec : ∀ k, c (k + 1) ≤ c k) (hlim : Tendsto c atTop (𝓝 0)) (t : ℝ) :
    HasSum (fun K => dd2 c K * fejT K t) (∑' n : ℤ, c n.natAbs * sincSqR (t - n)) := by
  set w : ℕ → ℝ := fun j => sincSqR (t + ((j : ℝ) + 1)) + sincSqR (t - ((j : ℝ) + 1)) with hw
  have hc0 := nonneg_of_convex hdec hlim
  have hw0 : ∀ j, 0 ≤ w j := fun j => add_nonneg (sincSqR_nonneg _) (sincSqR_nonneg _)
  have hss := summable_sincSqR_shift t
  have hwsum : Summable w := by
    have h1 : Summable fun j : ℕ => sincSqR (t - ((j : ℤ) + 1 : ℤ)) :=
      hss.comp_injective (fun a b h => by simpa using h)
    have h2 : Summable fun j : ℕ => sincSqR (t - (-((j : ℤ) + 1) : ℤ)) :=
      hss.comp_injective (fun a b h => by simpa using h)
    refine (h2.add h1).congr fun j => ?_
    simp only [hw]
    push_cast
    ring_nf
  -- step A: the sum over `ℤ`
  set F : ℤ → ℝ := fun n => c n.natAbs * sincSqR (t - n) with hF
  have hFle : ∀ n, |F n| ≤ c 0 * sincSqR (t - n) := fun n => by
    rw [abs_of_nonneg (mul_nonneg (hc0 _) (sincSqR_nonneg _))]
    exact mul_le_mul_of_nonneg_right (le_zero_of_dec hdec _) (sincSqR_nonneg _)
  have hFs : Summable F := Summable.of_norm_bounded (hss.mul_left (c 0)) hFle
  have hA : ∑' n : ℤ, F n = c 0 * sincSqR t + ∑' j : ℕ, c (j + 1) * w j := by
    have h1 : Summable fun n : ℕ => F n := hFs.comp_injective Nat.cast_injective
    have h2 : Summable fun n : ℕ => F (-(n + 1)) :=
      hFs.comp_injective (fun a b h => by simpa using h)
    rw [tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_eq_zero_add]
    have h3 : Summable fun n : ℕ => F ((n + 1 : ℕ) : ℤ) :=
      (summable_nat_add_iff 1).mpr h1
    rw [add_assoc, ← h3.tsum_add h2]
    congr 1
    · simp [hF]
    · refine tsum_congr fun j => ?_
      simp only [hF, hw]
      have e1 : ((j + 1 : ℕ) : ℤ).natAbs = j + 1 := Int.natAbs_natCast _
      have e2 : (-((j : ℤ) + 1)).natAbs = j + 1 := by omega
      rw [e1, e2]
      push_cast
      ring_nf
  -- step B: the double sum
  set u : ℕ → ℕ → ℝ := fun K j => if j < K then ((K : ℝ) - j) * dd2 c K * w j else 0 with hu
  have hu0 : ∀ K j, 0 ≤ u K j := fun K j => by
    simp only [hu]
    split_ifs with h
    · have : (j : ℝ) < K := by exact_mod_cast h
      exact mul_nonneg (mul_nonneg (by linarith) (hconv K)) (hw0 j)
    · exact le_rfl
  have hcol : ∀ j, HasSum (fun K => u K j) (c (j + 1) * w j) := by
    intro j
    rw [← hasSum_nat_add_iff' (j + 1)]
    have hzero : ∑ i ∈ range (j + 1), u i j = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have : ¬ j < i := by have := Finset.mem_range.mp hi; omega
        simp only [hu, this, ↓reduceIte]
    rw [hzero, sub_zero]
    refine ((hasSum_fejer_decomposition hconv hdec hlim (j + 1)).mul_right (w j)).congr_fun
      fun i => ?_
    simp only [hu, show j < i + (j + 1) by omega, ↓reduceIte]
    rw [show i + (j + 1) = j + 1 + i by ring]
    push_cast
    ring
  have hv : Summable (fun q : ℕ × ℕ => u q.2 q.1) := by
    refine (summable_prod_of_nonneg fun q => hu0 _ _).mpr ⟨fun j => (hcol j).summable, ?_⟩
    simp_rw [fun j => (hcol j).tsum_eq]
    exact Summable.of_nonneg_of_le (fun j => mul_nonneg (hc0 _) (hw0 j))
      (fun j => mul_le_mul_of_nonneg_right (le_zero_of_dec hdec _) (hw0 j))
      (hwsum.mul_left (c 0))
  have hvtot : HasSum (fun q : ℕ × ℕ => u q.2 q.1) (∑' j : ℕ, c (j + 1) * w j) := by
    have h1 := hv.hasSum.prod_fiberwise fun j => hcol j
    rw [h1.tsum_eq]
    exact hv.hasSum
  have hutot : HasSum (fun q : ℕ × ℕ => u q.1 q.2) (∑' j : ℕ, c (j + 1) * w j) :=
    ((Equiv.prodComm ℕ ℕ).hasSum_iff (f := fun q : ℕ × ℕ => u q.1 q.2)).mp hvtot
  have hrow : ∀ K, HasSum (fun j => u K j) (∑ j ∈ range K, ((K : ℝ) - j) * dd2 c K * w j) := by
    intro K
    have h : HasSum (fun j => u K j) (∑ j ∈ range K, u K j) :=
      hasSum_sum_of_ne_finset_zero (f := fun j => u K j) (s := range K) fun j hj => by
      have : ¬ j < K := by simpa using hj
      simp only [hu, this, ↓reduceIte]
    have hsum_eq : ∑ j ∈ range K, u K j = ∑ j ∈ range K, ((K : ℝ) - j) * dd2 c K * w j :=
      Finset.sum_congr rfl fun j hj => by simp only [hu, Finset.mem_range.mp hj, ↓reduceIte]
    rwa [hsum_eq] at h
  have hK := hutot.prod_fiberwise hrow
  have h0 : HasSum (fun K : ℕ => ((K : ℝ) + 1) * dd2 c K * sincSqR t) (c 0 * sincSqR t) := by
    have := (hasSum_fejer_decomposition hconv hdec hlim 0).mul_right (sincSqR t)
    simpa only [zero_add] using this
  rw [hA]
  refine (h0.add hK).congr_fun fun K => ?_
  unfold fejT
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by simp only [hw]; ring

/-! ## The measure `m_h` and its transform -/

theorem continuous_fej (K : ℕ) : Continuous (fej K) := by
  unfold fej; fun_prop

theorem integrable_tri_fej (K : ℕ) : Integrable fun ω : ℝ => tri ω * fej K ω := by
  have hc : Continuous fun ω : ℝ => tri ω * fej K ω := continuous_tri.mul (continuous_fej K)
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun ω hω => ?_
  rw [tri_eq_zero (fun h => hω (Set.Ioc_subset_Icc_self h)), zero_mul]

theorem fejT_zero (K : ℕ) : fejT K 0 = (K : ℝ) + 1 := by
  unfold fejT
  have h0 : sincSqR 0 = 1 := by simp [sincSqR]
  have h1 : ∀ j : ℕ, sincSqR (0 + ((j : ℝ) + 1)) = 0 := fun j => by
    have := sincSqR_intCast ((j : ℤ) + 1)
    have hne : (j : ℤ) + 1 ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at this
    simpa using this
  have h2 : ∀ j : ℕ, sincSqR (0 - ((j : ℝ) + 1)) = 0 := fun j => by
    have := sincSqR_intCast (-((j : ℤ) + 1))
    have hne : -((j : ℤ) + 1) ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at this
    simpa [neg_add] using this
  simp only [h0, h1, h2, add_zero, mul_zero, Finset.sum_const_zero, mul_one]

theorem integral_tri_fej (K : ℕ) : ∫ ω, tri ω * fej K ω = (K : ℝ) + 1 := by
  have h := integral_tri_fej_mul_cexp K 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  rw [integral_complex_ofReal, fejT_zero] at h
  exact_mod_cast h

/-- The density `(1 − |ω|)₊ fej_K(ω)` as an `ℝ≥0`-valued function. -/
def fejDensity (K : ℕ) (ω : ℝ) : ℝ≥0 := Real.toNNReal (tri ω * fej K ω)

theorem measurable_fejDensity (K : ℕ) : Measurable (fejDensity K) :=
  (continuous_tri.mul (continuous_fej K)).measurable.real_toNNReal

/-- The measure `m_h = Σ_K Δ²c_K (1 − |ω|)₊ fej_K(ω) dω`. -/
def hMeasure (c : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun K => ENNReal.ofReal (dd2 c K) •
    (volume : Measure ℝ).withDensity fun ω => (fejDensity K ω : ℝ≥0∞)

theorem withDensity_fejDensity_univ (K : ℕ) :
    (volume : Measure ℝ).withDensity (fun ω => (fejDensity K ω : ℝ≥0∞)) Set.univ =
      ENNReal.ofReal ((K : ℝ) + 1) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← integral_tri_fej K,
    ofReal_integral_eq_lintegral_ofReal (integrable_tri_fej K)
      (Eventually.of_forall fun ω => mul_nonneg (tri_nonneg ω) (fejer_nonneg K ω))]
  rfl

theorem hMeasure_univ {c : ℕ → ℝ} (hconv : ∀ k, 0 ≤ dd2 c k) (hdec : ∀ k, c (k + 1) ≤ c k)
    (hlim : Tendsto c atTop (𝓝 0)) : hMeasure c Set.univ = ENNReal.ofReal (c 0) := by
  unfold hMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, withDensity_fejDensity_univ]
  have h := hasSum_fejer_decomposition hconv hdec hlim 0
  simp only [zero_add] at h
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun K => mul_nonneg (by positivity) (hconv K))
    h.summable]
  refine tsum_congr fun K => ?_
  rw [← ENNReal.ofReal_mul (hconv K), mul_comm]

theorem isFiniteMeasure_hMeasure {c : ℕ → ℝ} (hconv : ∀ k, 0 ≤ dd2 c k)
    (hdec : ∀ k, c (k + 1) ≤ c k) (hlim : Tendsto c atTop (𝓝 0)) :
    IsFiniteMeasure (hMeasure c) :=
  ⟨by rw [hMeasure_univ hconv hdec hlim]; exact ENNReal.ofReal_lt_top⟩

/-- **`h = m̂_h`**. -/
theorem integral_cexp_hMeasure {c : ℕ → ℝ} (hconv : ∀ k, 0 ≤ dd2 c k)
    (hdec : ∀ k, c (k + 1) ≤ c k) (hlim : Tendsto c atTop (𝓝 0)) (t : ℝ) :
    ∫ ω, cexp (2 * π * I * ω * t) ∂hMeasure c =
      ((∑' n : ℤ, c n.natAbs * sincSqR (t - n) : ℝ) : ℂ) := by
  have hfin := isFiniteMeasure_hMeasure hconv hdec hlim
  have hint : Integrable (fun ω : ℝ => cexp (2 * π * I * ω * t)) (hMeasure c) := by
    refine Integrable.of_bound (C := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun ω => ?_)
    rw [show 2 * (π : ℂ) * I * ω * t = ((2 * π * ω * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  unfold hMeasure at hint ⊢
  rw [integral_sum_measure hint, ← (hasSum_dd2_mul_fejT hconv hdec hlim t).tsum_eq,
    Complex.ofReal_tsum]
  refine tsum_congr fun K => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hconv K),
    integral_withDensity_eq_integral_smul (measurable_fejDensity K)]
  have h := integral_tri_fej_mul_cexp K t
  have hd : ∀ ω, (fejDensity K ω) • cexp (2 * π * I * ω * t) =
      ((tri ω * fej K ω : ℝ) : ℂ) * cexp (2 * π * I * ω * t) := fun ω => by
    rw [NNReal.smul_def, fejDensity, Real.coe_toNNReal _
      (mul_nonneg (tri_nonneg ω) (fejer_nonneg K ω)), Complex.real_smul]
  simp_rw [hd, h]
  rw [real_smul, Complex.ofReal_mul]

/-! ## The measure `η` and `E = e^h = η̂` -/

/-- `η = Σ_j (1/j!) (Σ_l ω_l)_* m_h^{⊗j}`. -/
def etaMeasure (c : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun j : ℕ => ENNReal.ofReal (1 / (j ! : ℝ)) •
    (Measure.pi fun _ : Fin j => hMeasure c).map fun ω => ∑ l, ω l

theorem isFiniteMeasure_etaMeasure {c : ℕ → ℝ} (hconv : ∀ k, 0 ≤ dd2 c k)
    (hdec : ∀ k, c (k + 1) ≤ c k) (hlim : Tendsto c atTop (𝓝 0)) :
    IsFiniteMeasure (etaMeasure c) := by
  have hfin := isFiniteMeasure_hMeasure hconv hdec hlim
  have hc0 := nonneg_of_convex hdec hlim 0
  refine ⟨?_⟩
  unfold etaMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hmap : ∀ j : ℕ, ((Measure.pi fun _ : Fin j => hMeasure c).map fun ω => ∑ l, ω l)
      Set.univ = ENNReal.ofReal (c 0 ^ j) := fun j => by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, Measure.pi_univ]
    simp only [hMeasure_univ hconv hdec hlim, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [ENNReal.ofReal_pow hc0]
  simp_rw [hmap]
  have hs := Real.summable_pow_div_factorial (c 0)
  have heq : ∀ j : ℕ, ENNReal.ofReal (1 / (j ! : ℝ)) * ENNReal.ofReal (c 0 ^ j) =
      ENNReal.ofReal (c 0 ^ j / j !) := fun j => by
    rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs]
  exact ENNReal.ofReal_lt_top

/-- **`e^h = η̂`**. -/
theorem integral_cexp_etaMeasure {c : ℕ → ℝ} (hconv : ∀ k, 0 ≤ dd2 c k)
    (hdec : ∀ k, c (k + 1) ≤ c k) (hlim : Tendsto c atTop (𝓝 0)) (t : ℝ) :
    ∫ ξ, cexp (2 * π * I * ξ * t) ∂etaMeasure c =
      ((Real.exp (∑' n : ℤ, c n.natAbs * sincSqR (t - n)) : ℝ) : ℂ) := by
  have hfin := isFiniteMeasure_hMeasure hconv hdec hlim
  have hefin := isFiniteMeasure_etaMeasure hconv hdec hlim
  set hval : ℝ := ∑' n : ℤ, c n.natAbs * sincSqR (t - n) with hhval
  have hint : Integrable (fun ξ : ℝ => cexp (2 * π * I * ξ * t)) (etaMeasure c) := by
    refine Integrable.of_bound (C := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun ξ => ?_)
    rw [show 2 * (π : ℂ) * I * ξ * t = ((2 * π * ξ * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  unfold etaMeasure at hint ⊢
  rw [integral_sum_measure hint]
  have hterm : ∀ j : ℕ, ∫ ξ, cexp (2 * π * I * ξ * t) ∂(ENNReal.ofReal (1 / (j ! : ℝ)) •
      (Measure.pi fun _ : Fin j => hMeasure c).map fun ω => ∑ l, ω l) =
      ((hval ^ j / j ! : ℝ) : ℂ) := by
    intro j
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
      integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop))]
    have hprod : ∀ ω : Fin j → ℝ, cexp (2 * π * I * ((∑ l, ω l : ℝ) : ℂ) * t) =
        ∏ l, cexp (2 * π * I * ω l * t) := fun ω => by
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
    simp_rw [hprod]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun _ (ω : ℝ) => cexp (2 * π * I * ω * t))]
    simp only [integral_cexp_hMeasure hconv hdec hlim, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← hhval, real_smul]
    push_cast
    ring
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

end FroehlichSpencer.BKT.SOS.Literal

end
