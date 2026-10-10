/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Fejér polynomials used in the finite-volume cell limit

The polynomial is the Fejér weight from KP §5.1, p. 4 (transcription
Kharash–Peled, first version). -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The real cosine coefficient of the Fejér polynomial in KP §5.1, p. 4. -/
noncomputable def fejerCosineCoefficient (N q : ℕ) : ℝ := 1 - (q : ℝ) / N

/-- The Fejér polynomial from KP §5.1, p. 4. -/
noncomputable def fejerPolynomial (N : ℕ) (x : ℝ) : ℝ :=
  1 + ∑ r ∈ Finset.range N,
    2 * fejerCosineCoefficient N (r + 1) *
      Real.cos (((r + 1 : ℕ) : ℝ) * x)

/-- The Dirichlet polynomial whose Cesàro means are the Fejér polynomials. -/
noncomputable def fejerDirichletKernel (n : ℕ) (x : ℝ) : ℝ :=
  1 + 2 * ∑ r ∈ Finset.range n, Real.cos (((r + 1 : ℕ) : ℝ) * x)

/-- The Cesàro average of the finite Dirichlet polynomials. -/
noncomputable def fejerDirichletAverage (N : ℕ) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, fejerDirichletKernel n x) / N

/-- Multiplication by `sin (x/2)` telescopes the finite Dirichlet polynomial. -/
theorem sin_half_mul_fejerDirichletKernel (n : ℕ) (x : ℝ) :
    Real.sin (x / 2) * fejerDirichletKernel n x =
      Real.sin (((n : ℝ) + 1 / 2) * x) := by
  induction n with
  | zero =>
    simp only [fejerDirichletKernel, Finset.range_zero, Finset.sum_empty,
      mul_zero, add_zero]
    ring_nf
  | succ n ih =>
    have hD : fejerDirichletKernel (n + 1) x =
        fejerDirichletKernel n x + 2 * Real.cos (((n + 1 : ℕ) : ℝ) * x) := by
      simp [fejerDirichletKernel, Finset.sum_range_succ]
      ring
    have hplus : (((n : ℝ) + 1) + 1 / 2) * x =
        ((n : ℝ) + 1) * x + x / 2 := by ring
    have hminus : ((n : ℝ) + 1 / 2) * x =
        ((n : ℝ) + 1) * x - x / 2 := by ring
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
    have htrig : Real.sin (x / 2) *
          (2 * Real.cos (((n + 1 : ℕ) : ℝ) * x)) =
        Real.sin ((((n : ℝ) + 1) + 1 / 2) * x) -
          Real.sin (((n : ℝ) + 1 / 2) * x) := by
      rw [hcast, hplus, hminus, Real.sin_add, Real.sin_sub]
      ring_nf
    rw [hD, mul_add, ih, htrig]
    push_cast
    ring

/-- The complex Fourier coefficient of the Fejér polynomial, extended by zero
outside its finite frequency range. -/
noncomputable def fejerFourierCoefficient (N : ℕ) (q : ℤ) : ℝ :=
  if q.natAbs ≤ N then 1 - (q.natAbs : ℝ) / N else 0

/-- The Fejér polynomial is even. -/
theorem fejerPolynomial_even (N : ℕ) (x : ℝ) :
    fejerPolynomial N (-x) = fejerPolynomial N x := by
  simp [fejerPolynomial, Real.cos_neg]

/-- The range-indexed definition is exactly KP's displayed cosine polynomial;
the endpoint `q = N` contributes zero. -/
theorem fejerPolynomial_eq_kp (N : ℕ) (x : ℝ) :
    fejerPolynomial N x = 1 + ∑ q ∈ Finset.Icc 1 N,
      2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x) := by
  unfold fejerPolynomial
  congr 1
  apply Finset.sum_bij (fun r hr => r + 1)
  · intro r hr
    have hr' : r < N := Finset.mem_range.mp hr
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro r hr s hs h
    omega
  · intro q hq
    refine ⟨q - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have hq' := Finset.mem_Icc.mp hq
      omega
    · have hq' := Finset.mem_Icc.mp hq
      simp [Nat.sub_add_cancel hq'.1]
  · intro r hr
    rfl

/-- The sum of the first `N` Dirichlet polynomials has the triangular cosine
coefficients defining the Fejér polynomial. -/
theorem sum_fejerDirichletKernel (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.range N, fejerDirichletKernel n x) =
      (N : ℝ) + 2 * ∑ r ∈ Finset.range N,
        ((N : ℝ) - ((r + 1 : ℕ) : ℝ)) *
          Real.cos (((r + 1 : ℕ) : ℝ) * x) := by
  induction N with
  | zero => simp [fejerDirichletKernel]
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    rw [ih]
    simp only [fejerDirichletKernel]
    simp only [Nat.cast_succ]
    simp only [sub_self, zero_mul, add_zero]
    have hsum :
        (∑ r ∈ Finset.range N,
          ((N : ℝ) - ((r : ℝ) + 1)) *
            Real.cos (((r : ℝ) + 1) * x)) +
        ∑ r ∈ Finset.range N, Real.cos (((r : ℝ) + 1) * x) =
          ∑ r ∈ Finset.range N,
            ((N : ℝ) + 1 - ((r : ℝ) + 1)) *
              Real.cos (((r : ℝ) + 1) * x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [← hsum]
    ring

/-- Multiplying the KP polynomial by its degree clears its coefficients. -/
theorem fejerPolynomial_mul_degree (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (N : ℝ) * fejerPolynomial N x =
      (N : ℝ) + 2 * ∑ r ∈ Finset.range N,
        ((N : ℝ) - ((r + 1 : ℕ) : ℝ)) *
          Real.cos (((r + 1 : ℕ) : ℝ) * x) := by
  rw [fejerPolynomial]
  rw [mul_add, Finset.mul_sum]
  rw [mul_one]
  conv_rhs => rw [Finset.mul_sum]
  apply congrArg (fun z : ℝ => (N : ℝ) + z)
  apply Finset.sum_congr rfl
  intro r hr
  simp only [fejerCosineCoefficient]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hN']

/-- Fejér polynomials are the Cesàro means of the Dirichlet polynomials. -/
theorem fejerPolynomial_eq_dirichletAverage (N : ℕ) (hN : 0 < N) (x : ℝ) :
    fejerPolynomial N x = fejerDirichletAverage N x := by
  rw [fejerDirichletAverage, sum_fejerDirichletKernel,
    ← fejerPolynomial_mul_degree N hN x]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hN']

/-- The Fejér polynomial's sine identity, obtained by summing the telescoping
Dirichlet identity. -/
theorem fejerPolynomial_mul_sin_sq (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (N : ℝ) * fejerPolynomial N x * Real.sin (x / 2) ^ 2 =
      Real.sin ((N : ℝ) * x / 2) ^ 2 := by
  rw [fejerPolynomial_eq_dirichletAverage N hN x, fejerDirichletAverage]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hsum :
      Real.sin (x / 2) *
          (∑ n ∈ Finset.range N, fejerDirichletKernel n x) =
        ∑ n ∈ Finset.range N, Real.sin (((n : ℝ) + 1 / 2) * x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact sin_half_mul_fejerDirichletKernel n x
  have htrig := Real.sin_mul_sum_sin N x (x / 2)
  have hsumArg :
      (∑ n ∈ Finset.range N, Real.sin (((n : ℝ) + 1 / 2) * x)) =
        ∑ n ∈ Finset.range N, Real.sin (x * n + x / 2) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    ring
  have hargN :
      ((N : ℝ) - 1) * x / 2 + x / 2 = (N : ℝ) * x / 2 := by ring
  have htrig' : Real.sin (x / 2) *
      (∑ n ∈ Finset.range N, Real.sin (((n : ℝ) + 1 / 2) * x)) =
        Real.sin ((N : ℝ) * x / 2) ^ 2 := by
    calc
      _ = Real.sin (x / 2) *
          (∑ n ∈ Finset.range N, Real.sin (x * n + x / 2)) := by rw [hsumArg]
      _ = Real.sin ((N : ℝ) * x / 2) ^ 2 := by
        rw [hargN] at htrig
        simpa only [pow_two] using htrig
  field_simp [hN']
  calc
    (∑ n ∈ Finset.range N, fejerDirichletKernel n x) * Real.sin (x / 2) ^ 2 =
        Real.sin (x / 2) *
          (Real.sin (x / 2) * ∑ n ∈ Finset.range N, fejerDirichletKernel n x) := by ring
    _ = Real.sin (x / 2) *
          ∑ n ∈ Finset.range N, Real.sin (((n : ℝ) + 1 / 2) * x) := by rw [hsum]
    _ = Real.sin ((N : ℝ) * x / 2) ^ 2 := htrig'

/-- The Fejér polynomial is nonnegative, from its squared-sine formula away
from multiples of `2π` and its explicit value at those points. -/
theorem fejerPolynomial_nonneg (N : ℕ) (hN : 0 < N) (x : ℝ) :
    0 ≤ fejerPolynomial N x := by
  by_cases hs : Real.sin (x / 2) = 0
  · obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
    have hx : x = 2 * (k : ℝ) * Real.pi := by
      nlinarith only [hk]
    rw [fejerPolynomial_eq_kp]
    have hcos (q : ℕ) : Real.cos ((q : ℝ) * x) = 1 := by
      have harg : (q : ℝ) * x = (((q : ℤ) * k : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hx]
        push_cast
        ring
      rw [harg, Real.cos_int_mul_two_pi]
    simp_rw [hcos]
    apply add_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro q hq
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hq' : (q : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hq).2
    have hcoef : 0 ≤ 1 - (q : ℝ) / N := by
      apply sub_nonneg.mpr
      exact (div_le_one hN').2 hq'
    positivity
  · have hspos : 0 < Real.sin (x / 2) ^ 2 := sq_pos_of_ne_zero hs
    have hcoef : 0 < (N : ℝ) * Real.sin (x / 2) ^ 2 :=
      mul_pos (by exact_mod_cast hN) hspos
    have hprod : fejerPolynomial N x *
        ((N : ℝ) * Real.sin (x / 2) ^ 2) =
          Real.sin ((N : ℝ) * x / 2) ^ 2 := by
      calc
        fejerPolynomial N x * ((N : ℝ) * Real.sin (x / 2) ^ 2) =
            (N : ℝ) * fejerPolynomial N x * Real.sin (x / 2) ^ 2 := by ring
        _ = Real.sin ((N : ℝ) * x / 2) ^ 2 := fejerPolynomial_mul_sin_sq N hN x
    have hformula : fejerPolynomial N x =
        Real.sin ((N : ℝ) * x / 2) ^ 2 /
          ((N : ℝ) * Real.sin (x / 2) ^ 2) :=
      (eq_div_iff hcoef.ne').2 hprod
    rw [hformula]
    exact div_nonneg (sq_nonneg _) (le_of_lt hcoef)

/-- Fejér polynomials are `2π`-periodic. -/
theorem fejerPolynomial_add_two_pi_int (N : ℕ) (k : ℤ) (x : ℝ) :
    fejerPolynomial N (x + 2 * Real.pi * k) = fejerPolynomial N x := by
  rw [fejerPolynomial_eq_kp, fejerPolynomial_eq_kp]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have harg : (q : ℝ) * (x + 2 * Real.pi * k) =
      (q : ℝ) * x + (((q : ℤ) * k : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.cos_add_int_mul_two_pi]

/-- The Fejér tail estimate on one period, KP §5.1, p. 4. -/
theorem fejerPolynomial_tail_bound (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδπ : δ ≤ Real.pi)
    (x : ℝ) (hδx : δ ≤ |x|) (hxπ : |x| ≤ Real.pi) :
    fejerPolynomial N x ≤
      1 / ((N : ℝ) * Real.sin (δ / 2) ^ 2) := by
  have hδsin : 0 < Real.sin (δ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith only [hδ]
    · linarith only [hδπ, Real.pi_pos]
  have hsinabs : Real.sin (x / 2) ^ 2 = Real.sin (|x| / 2) ^ 2 := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      have habs : |x| / 2 = -(x / 2) := by
        rw [abs_of_nonpos hx']
        ring
      rw [habs, Real.sin_neg]
      ring
  have hsinle : Real.sin (δ / 2) ≤ Real.sin (|x| / 2) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith only [hδ, hδx, hxπ]
    · nlinarith only [hxπ]
    · linarith only [hδx]
  have hsinabspos : 0 ≤ Real.sin (|x| / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · nlinarith only [hδ, hδx, hxπ]
  have hsmall : Real.sin (δ / 2) ^ 2 ≤ Real.sin (x / 2) ^ 2 := by
    rw [hsinabs]
    exact (sq_le_sq₀ hδsin.le hsinabspos).2 hsinle
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) * Real.sin (δ / 2) ^ 2 :=
    mul_pos hNpos (sq_pos_of_ne_zero hδsin.ne')
  have hF := fejerPolynomial_nonneg N hN x
  have hNF : 0 ≤ (N : ℝ) * fejerPolynomial N x := mul_nonneg hNpos.le hF
  have hprod : (N : ℝ) * fejerPolynomial N x * Real.sin (δ / 2) ^ 2 ≤ 1 := by
    calc
      (N : ℝ) * fejerPolynomial N x * Real.sin (δ / 2) ^ 2 ≤
          (N : ℝ) * fejerPolynomial N x * Real.sin (x / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsmall hNF
      _ = Real.sin ((N : ℝ) * x / 2) ^ 2 :=
        fejerPolynomial_mul_sin_sq N hN x
      _ ≤ 1 := by
        have hsinbound : |Real.sin ((N : ℝ) * x / 2)| ≤ 1 :=
          abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
        have hs := abs_le.mp hsinbound
        have hprod : 0 ≤
            (1 - Real.sin ((N : ℝ) * x / 2)) *
              (1 + Real.sin ((N : ℝ) * x / 2)) :=
          mul_nonneg (sub_nonneg.mpr hs.2) (by linarith only [hs])
        nlinarith only [hprod]
  apply (le_div_iff₀ hden).2
  nlinarith only [hprod]

/-- Fejér's nonnegative-frequency coefficients lie in `[0,1]`. -/
theorem fejerCosineCoefficient_mem_Icc (N q : ℕ) (hN : 0 < N) (hq : q ≤ N) :
    fejerCosineCoefficient N q ∈ Set.Icc 0 1 := by
  rw [Set.mem_Icc]
  constructor
  · dsimp [fejerCosineCoefficient]
    apply sub_nonneg.mpr
    exact (div_le_one (by exact_mod_cast hN)).2 (by exact_mod_cast hq)
  · dsimp [fejerCosineCoefficient]
    have hq0 : 0 ≤ (q : ℝ) / N := by positivity
    linarith only [hq0]

/-- The signed Fourier coefficient is even in its frequency. -/
theorem fejerFourierCoefficient_neg (N : ℕ) (q : ℤ) :
    fejerFourierCoefficient N (-q) = fejerFourierCoefficient N q := by
  simp [fejerFourierCoefficient]

/-- On nonnegative frequencies, the signed-frequency coefficient is the
coefficient displayed in KP's cosine form. -/
theorem fejerFourierCoefficient_nat (N q : ℕ) :
    fejerFourierCoefficient N (q : ℤ) =
      if q ≤ N then fejerCosineCoefficient N q else 0 := by
  simp [fejerFourierCoefficient, fejerCosineCoefficient]

/-- KP's displayed Fejér polynomial is recovered from the signed-frequency
coefficient carrier. -/
theorem fejerPolynomial_eq_fourierCosineExpansion (N : ℕ) (x : ℝ) :
    fejerPolynomial N x = 1 + ∑ q ∈ Finset.Icc 1 N,
      2 * fejerFourierCoefficient N (q : ℤ) * Real.cos ((q : ℝ) * x) := by
  rw [fejerPolynomial_eq_kp]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [fejerFourierCoefficient_nat]
  split_ifs with h
  · rfl
  · exact (h (Finset.mem_Icc.mp hq).2).elim

/-- Every Fejér Fourier coefficient is between zero and one when `N` is
positive. -/
theorem fejerFourierCoefficient_mem_Icc (N : ℕ) (q : ℤ) (hN : 0 < N) :
    fejerFourierCoefficient N q ∈ Set.Icc 0 1 := by
  rw [Set.mem_Icc]
  constructor
  · simp only [fejerFourierCoefficient]
    split_ifs with hq
    · apply sub_nonneg.mpr
      apply (div_le_one (by exact_mod_cast hN)).2
      exact_mod_cast hq
    · norm_num
  · simp only [fejerFourierCoefficient]
    split_ifs with hq
    · have hq0 : 0 ≤ (q.natAbs : ℝ) / N := by positivity
      linarith only [hq0]
    · norm_num

/-- Integrating a positive integer cosine frequency over the KP cell gives
zero. -/
theorem intervalIntegral_cos_nat_mul_eq_zero (q : ℕ) (hq : 0 < q) :
    ∫ x in -Real.pi..Real.pi, Real.cos ((q : ℝ) * x) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos)
    (c := (q : ℝ)) (by positivity : (q : ℝ) ≠ 0)]
  rw [integral_cos]
  have hsin : Real.sin ((q : ℝ) * Real.pi) = 0 := Real.sin_nat_mul_pi q
  rw [hsin]
  have hsinNeg : Real.sin ((q : ℝ) * -Real.pi) = 0 := by
    rw [mul_neg, Real.sin_neg, hsin, neg_zero]
  rw [hsinNeg, sub_self]
  simp

/-- The integral mass of the Fejér polynomial on one period is `2π`. -/
theorem fejerPolynomial_intervalIntegral (N : ℕ) :
    ∫ x in -Real.pi..Real.pi, fejerPolynomial N x = 2 * Real.pi := by
  simp_rw [fejerPolynomial_eq_kp]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_neg_eq_add]
    rw [intervalIntegral.integral_finsetSum]
    · have hterms : ∑ q ∈ Finset.Icc 1 N,
          ∫ x in -Real.pi..Real.pi,
            2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_cos_nat_mul_eq_zero q (by
            have hq' := Finset.mem_Icc.mp hq
            omega)]
        ring
      rw [hterms]
      ring
    · intro q hq
      have hcont : Continuous
          (fun x : ℝ => 2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x)) := by
        fun_prop
      exact hcont.intervalIntegrable (μ := MeasureTheory.volume) (-Real.pi) Real.pi
  · exact intervalIntegrable_const
  · have hcont : Continuous (fun x : ℝ =>
        ∑ q ∈ Finset.Icc 1 N,
          2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := MeasureTheory.volume) (-Real.pi) Real.pi

/-- The sum of the first odd integers is the square needed to evaluate the
Dirichlet Cesàro mean at the origin. -/
private theorem sum_range_two_mul_add_one_eq_sq (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 + 2 * (n : ℝ))) = (N : ℝ) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- At the origin the Fejér polynomial has its standard height `N`, KP §5.1,
p. 4. -/
theorem fejerPolynomial_zero (N : ℕ) (hN : 0 < N) :
    fejerPolynomial N 0 = N := by
  rw [fejerPolynomial_eq_dirichletAverage N hN 0, fejerDirichletAverage]
  have hsum :
      (∑ n ∈ Finset.range N, fejerDirichletKernel n 0) = (N : ℝ) ^ 2 := by
    calc
      _ = ∑ n ∈ Finset.range N, (1 + 2 * (n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [fejerDirichletKernel, Real.cos_zero]
      _ = (N : ℝ) ^ 2 := sum_range_two_mul_add_one_eq_sq N
  rw [hsum]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hNne]

/-- Positivity at the origin extends to a neighborhood, uniformly for all
points in a sufficiently small interval. -/
theorem exists_fejerPolynomial_pos_radius (N : ℕ) (hN : 0 < N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x| < δ → 0 < fejerPolynomial N x := by
  have hpos : 0 < fejerPolynomial N 0 := by
    rw [fejerPolynomial_zero N hN]
    exact_mod_cast hN
  have hcont : ContinuousAt (fejerPolynomial N) 0 := by
    unfold fejerPolynomial
    fun_prop
  have hset : {x : ℝ | 0 < fejerPolynomial N x} ∈ nhds (0 : ℝ) :=
    hcont.eventually_mem (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hset
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hxball : x ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero] using hx
  exact hball hxball

/-- Degree one gives the constant Fejér polynomial. -/
example : fejerPolynomial 1 0 = 1 := by
  rw [fejerPolynomial_zero 1 (by norm_num)]
  norm_num

/-- A signed frequency has the expected triangular coefficient. -/
example : fejerFourierCoefficient 5 (-2) = 3 / 5 := by
  norm_num [fejerFourierCoefficient]

end FroehlichSpencer.BKT

end
