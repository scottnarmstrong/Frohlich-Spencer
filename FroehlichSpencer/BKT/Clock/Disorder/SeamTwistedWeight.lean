/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.SeamCurrentFourier
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# The clock Fourier coefficients of the twisted rotator weight

For the twisted edge weight `w_δ(x) = exp(β cos(x + δ))`, the product
`exp((β/2)e^{iy}) exp((β/2)e^{−iy})` gives the double series
`w_δ(y − δ) = ∑_{a,b ≥ 0} T(a, b) e^{i(a−b)y}`, `T(a, b) = (β/2)^{a+b}/(a! b!) ≥ 0`
(`exp_cos_eq_tsum`). Sampling at the clock angles aliases the frequencies `a − b` modulo `N`:

`ŵ_δ(μ) = ∑_{a − b ≡ μ (N)} T(a, b) e^{i(a−b)δ}`   (`clockAngleFourier_twistedClockWeight`).

* At `δ = 0` all phases are `1`, so `ŵ₀(μ) = c(μ)` is a positive real number for `β > 0`.
* If `Nδ ∉ 2πℤ`, the two frequencies `μ` and `μ + N` carry phases differing by `e^{iNδ} ≠ 1`, so
  `‖ŵ_δ(μ)‖ < c(μ)`. Hence there is `λ < 1` with `‖ŵ_δ‖ ≤ λ c` at every `μ`
  (`exists_twistedClockWeight_contraction`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open Complex Finset

/-- The twisted rotator edge weight `exp(β cos(x + δ))`. -/
def twistedClockWeight (β δ : ℝ) (x : ℝ) : ℝ := Real.exp (β * Real.cos (x + δ))

theorem twistedClockWeight_periodic (β δ : ℝ) :
    Function.Periodic (twistedClockWeight β δ) (2 * Real.pi) := by
  intro x
  unfold twistedClockWeight
  rw [show x + 2 * Real.pi + δ = (x + δ) + 2 * Real.pi by ring, Real.cos_add_two_pi]

/-- The coefficient `T(a, b) = (β/2)^{a+b}/(a! b!)`. -/
def besselTerm (β : ℝ) (x : ℕ × ℕ) : ℝ :=
  (β / 2) ^ x.1 / (x.1.factorial : ℝ) * ((β / 2) ^ x.2 / (x.2.factorial : ℝ))

theorem besselTerm_nonneg {β : ℝ} (hβ : 0 ≤ β) (x : ℕ × ℕ) : 0 ≤ besselTerm β x := by
  unfold besselTerm
  positivity

theorem besselTerm_pos {β : ℝ} (hβ : 0 < β) (x : ℕ × ℕ) : 0 < besselTerm β x := by
  unfold besselTerm
  positivity

theorem summable_norm_besselTerm (β : ℝ) : Summable fun x : ℕ × ℕ => ‖besselTerm β x‖ := by
  have h := Real.summable_pow_div_factorial (|β| / 2)
  have hprod := h.mul_of_nonneg h (fun _ => by positivity) (fun _ => by positivity)
  refine hprod.congr fun x => ?_
  unfold besselTerm
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_div, abs_pow, abs_pow, abs_div, abs_two,
    Nat.abs_cast, Nat.abs_cast]

/-- The phase `e^{i(a − b)y}`. -/
def besselPhase (x : ℕ × ℕ) (y : ℝ) : ℂ := Complex.exp ((((x.1 : ℤ) - x.2 : ℤ) : ℂ) * y * I)

theorem norm_besselPhase (x : ℕ × ℕ) (y : ℝ) : ‖besselPhase x y‖ = 1 := by
  unfold besselPhase
  rw [Complex.norm_exp]
  simp

/-- **The double series of the rotator weight**:
`exp(β cos y) = ∑_{a,b} T(a, b) e^{i(a−b)y}`. -/
theorem exp_cos_eq_tsum (β y : ℝ) :
    ((Real.exp (β * Real.cos y) : ℝ) : ℂ) =
      ∑' x : ℕ × ℕ, (besselTerm β x : ℂ) * besselPhase x y := by
  set A : ℂ := (β / 2 : ℂ) * Complex.exp (y * I) with hA
  set B : ℂ := (β / 2 : ℂ) * Complex.exp (-(y * I)) with hB
  have hsplit : ((Real.exp (β * Real.cos y) : ℝ) : ℂ) = Complex.exp A * Complex.exp B := by
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    rw [hA, hB]
    push_cast
    rw [Complex.cos]
    ring_nf
  have hexp : ∀ z : ℂ, Complex.exp z = ∑' n : ℕ, z ^ n / (n.factorial : ℂ) := by
    intro z
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp z).tsum_eq.symm
  have hnormA : ∀ n : ℕ, ‖A ^ n / (n.factorial : ℂ)‖ = (|β| / 2) ^ n / n.factorial := by
    intro n
    rw [norm_div, norm_pow, hA, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    simp
  have hnormB : ∀ n : ℕ, ‖B ^ n / (n.factorial : ℂ)‖ = (|β| / 2) ^ n / n.factorial := by
    intro n
    rw [norm_div, norm_pow, hB, norm_mul, ← neg_mul, ← Complex.ofReal_neg,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    simp
  have hsA : Summable fun n : ℕ => ‖A ^ n / (n.factorial : ℂ)‖ := by
    simp_rw [hnormA]; exact Real.summable_pow_div_factorial _
  have hsB : Summable fun n : ℕ => ‖B ^ n / (n.factorial : ℂ)‖ := by
    simp_rw [hnormB]; exact Real.summable_pow_div_factorial _
  rw [hsplit, hexp A, hexp B, tsum_mul_tsum_of_summable_norm hsA hsB]
  refine tsum_congr fun x => ?_
  rw [hA, hB, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  unfold besselTerm besselPhase
  push_cast
  have hexp2 : Complex.exp (x.1 * (y * I)) * Complex.exp (x.2 * -(y * I)) =
      Complex.exp ((x.1 - x.2 : ℂ) * y * I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← hexp2]
  ring

/-- The clock aliasing indicator `[N ∣ a − b − μ]`. -/
def clockAlias (N : ℕ) (μ : Fin N) (x : ℕ × ℕ) : ℝ :=
  if (N : ℤ) ∣ ((x.1 : ℤ) - x.2 - (μ : ℕ)) then 1 else 0

theorem clockAlias_nonneg (N : ℕ) (μ : Fin N) (x : ℕ × ℕ) : 0 ≤ clockAlias N μ x := by
  unfold clockAlias; split_ifs <;> norm_num

theorem clockAlias_le_one (N : ℕ) (μ : Fin N) (x : ℕ × ℕ) : clockAlias N μ x ≤ 1 := by
  unfold clockAlias; split_ifs <;> norm_num

/-- **The clock Fourier coefficient of the twisted weight**:
`ŵ_δ(μ) = ∑_{a − b ≡ μ (N)} T(a, b) e^{i(a−b)δ}`. -/
theorem clockAngleFourier_twistedClockWeight {N : ℕ} (hN : 0 < N) (β δ : ℝ) (μ : Fin N) :
    clockAngleFourier N (twistedClockWeight β δ) μ =
      ∑' x : ℕ × ℕ, (besselTerm β x : ℂ) * besselPhase x δ * (clockAlias N μ x : ℂ) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsum : ∀ l : Fin N, Summable fun x : ℕ × ℕ =>
      (besselTerm β x : ℂ) * besselPhase x (2 * Real.pi * (l : ℕ) / N + δ) *
        clockChar N (-((μ : ℕ) * (l : ℕ))) := by
    intro l
    refine Summable.of_norm ((summable_norm_besselTerm β).congr fun x => ?_)
    rw [norm_mul, norm_mul, norm_besselPhase, Complex.norm_real]
    unfold clockChar
    rw [Complex.norm_exp]
    simp
  unfold clockAngleFourier twistedClockWeight
  simp_rw [exp_cos_eq_tsum, ← tsum_mul_right]
  rw [← (Summable.tsum_finsetSum fun l _ => hsum l), ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  -- the finite clock sum of one frequency
  have hterm : ∀ l : Fin N,
      (besselTerm β x : ℂ) * besselPhase x (2 * Real.pi * (l : ℕ) / N + δ) *
        clockChar N (-((μ : ℕ) * (l : ℕ))) =
      (besselTerm β x : ℂ) * besselPhase x δ *
        clockChar N ((l : ℕ) * (((x.1 : ℤ) - x.2) - (μ : ℕ))) := by
    intro l
    unfold besselPhase clockChar
    rw [mul_assoc (besselTerm β x : ℂ), mul_assoc (besselTerm β x : ℂ), ← Complex.exp_add,
      ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_clockChar_mul hN]
  unfold clockAlias
  split_ifs
  · push_cast
    field_simp
  · push_cast
    ring

/-- The untwisted coefficient `c(μ) = ∑_{a − b ≡ μ (N)} T(a, b)`. -/
def clockWeightCoeff (N : ℕ) (β : ℝ) (μ : Fin N) : ℝ :=
  ∑' x : ℕ × ℕ, besselTerm β x * clockAlias N μ x

theorem summable_besselTerm_mul_clockAlias {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) (μ : Fin N) :
    Summable fun x : ℕ × ℕ => besselTerm β x * clockAlias N μ x := by
  refine Summable.of_nonneg_of_le (fun x => mul_nonneg (besselTerm_nonneg hβ x)
    (clockAlias_nonneg N μ x)) (fun x => ?_) ((summable_norm_besselTerm β).congr fun x =>
      Real.norm_of_nonneg (besselTerm_nonneg hβ x))
  exact mul_le_of_le_one_right (besselTerm_nonneg hβ x) (clockAlias_le_one N μ x)

/-- At `δ = 0` the clock coefficients are the real numbers `c(μ)`. -/
theorem clockAngleFourier_twistedClockWeight_zero {N : ℕ} (hN : 0 < N) (β : ℝ) (μ : Fin N) :
    clockAngleFourier N (twistedClockWeight β 0) μ = (clockWeightCoeff N β μ : ℂ) := by
  rw [clockAngleFourier_twistedClockWeight hN, clockWeightCoeff,
    Complex.ofReal_tsum]
  refine tsum_congr fun x => ?_
  unfold besselPhase
  push_cast
  simp

theorem clockWeightCoeff_pos {N : ℕ} {β : ℝ} (hβ : 0 < β) (μ : Fin N) :
    0 < clockWeightCoeff N β μ := by
  have hx : clockAlias N μ ((μ : ℕ), 0) = 1 := by
    unfold clockAlias
    simp
  have h := (summable_besselTerm_mul_clockAlias hβ.le μ).le_tsum ((μ : ℕ), 0) fun x _ =>
    mul_nonneg (besselTerm_nonneg hβ.le x) (clockAlias_nonneg N μ x)
  rw [hx, mul_one] at h
  exact lt_of_lt_of_le (besselTerm_pos hβ _) h

/-- Two unit-modulus phases that differ give a strict triangle inequality. -/
theorem norm_add_mul_lt {T₁ T₂ : ℝ} (h₁ : 0 < T₁) (h₂ : 0 < T₂) {w : ℂ} (hw : ‖w‖ = 1)
    (hw1 : w ≠ 1) : ‖(T₁ : ℂ) + T₂ * w‖ < T₁ + T₂ := by
  have hre : w.re < 1 := by
    have hnorm : w.re ^ 2 + w.im ^ 2 = 1 := by
      have := Complex.sq_norm w
      rw [hw, Complex.normSq_apply] at this
      nlinarith
    by_contra hge
    push Not at hge
    have hre1 : w.re = 1 := by nlinarith [Complex.re_le_norm w]
    have him : w.im = 0 := by nlinarith
    exact hw1 (Complex.ext hre1 him)
  have hnorm : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at this
    nlinarith
  have hsq : ‖(T₁ : ℂ) + T₂ * w‖ ^ 2 < (T₁ + T₂) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.add_im, Complex.mul_im, zero_add, add_zero]
    have key : (T₁ + T₂ * w.re) * (T₁ + T₂ * w.re) + T₂ * w.im * (T₂ * w.im) =
        T₁ ^ 2 + 2 * T₁ * T₂ * w.re + T₂ ^ 2 * (w.re ^ 2 + w.im ^ 2) := by ring
    rw [key, hnorm]
    have h12 : T₁ * T₂ * w.re < T₁ * T₂ := by
      have := mul_pos h₁ h₂
      nlinarith
    nlinarith
  have hpos : 0 ≤ T₁ + T₂ := by positivity
  exact lt_of_pow_lt_pow_left₀ 2 hpos hsq

/-- A summable complex series with two non-aligned terms has `‖∑'‖ < ∑' ‖·‖`. -/
theorem norm_tsum_lt_of_two {ι : Type*} [DecidableEq ι] {f : ι → ℂ}
    (hf : Summable fun i => ‖f i‖) {i j : ι} (hij : i ≠ j)
    (hlt : ‖f i + f j‖ < ‖f i‖ + ‖f j‖) : ‖∑' x, f x‖ < ∑' x, ‖f x‖ := by
  set s : Finset ι := {i, j}
  have hf' : Summable f := hf.of_norm
  rw [← hf'.sum_add_tsum_compl (s := s), ← hf.sum_add_tsum_compl (s := s)]
  have hs1 : ∑ x ∈ s, f x = f i + f j := Finset.sum_pair hij
  have hs2 : ∑ x ∈ s, ‖f x‖ = ‖f i‖ + ‖f j‖ := Finset.sum_pair hij
  rw [hs1, hs2]
  have hrest : ‖∑' x : ↑(sᶜ : Set ι), f x‖ ≤ ∑' x : ↑(sᶜ : Set ι), ‖f x‖ :=
    norm_tsum_le_tsum_norm (hf.subtype _)
  calc ‖f i + f j + ∑' x : ↑(sᶜ : Set ι), f x‖
      ≤ ‖f i + f j‖ + ‖∑' x : ↑(sᶜ : Set ι), f x‖ := norm_add_le _ _
    _ < ‖f i‖ + ‖f j‖ + ∑' x : ↑(sᶜ : Set ι), ‖f x‖ := by linarith

/-- **The strict contraction of one clock coefficient** for `Nδ ∉ 2πℤ`. -/
theorem norm_clockAngleFourier_twistedClockWeight_lt {N : ℕ} (hN : 0 < N) {β δ : ℝ} (hβ : 0 < β)
    (hδ : ∀ j : ℤ, (N : ℝ) * δ ≠ j * (2 * Real.pi)) (μ : Fin N) :
    ‖clockAngleFourier N (twistedClockWeight β δ) μ‖ < clockWeightCoeff N β μ := by
  classical
  set f : ℕ × ℕ → ℂ := fun x => (besselTerm β x : ℂ) * besselPhase x δ * (clockAlias N μ x : ℂ)
    with hfdef
  have hnorm : ∀ x, ‖f x‖ = besselTerm β x * clockAlias N μ x := by
    intro x
    rw [hfdef, norm_mul, norm_mul, norm_besselPhase, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (besselTerm_nonneg hβ.le x),
      Real.norm_of_nonneg (clockAlias_nonneg N μ x), mul_one]
  have hsum : Summable fun x => ‖f x‖ := by
    simp_rw [hnorm]; exact summable_besselTerm_mul_clockAlias hβ.le μ
  set x₁ : ℕ × ℕ := ((μ : ℕ), 0)
  set x₂ : ℕ × ℕ := ((μ : ℕ) + N, 0)
  have hx₁ : clockAlias N μ x₁ = 1 := by unfold clockAlias; simp [x₁]
  have hx₂ : clockAlias N μ x₂ = 1 := by unfold clockAlias; simp [x₂]
  have hne : x₁ ≠ x₂ := by
    intro h
    have := congrArg Prod.fst h
    simp [x₁, x₂] at this
    omega
  have hw : besselPhase x₂ δ = besselPhase x₁ δ * Complex.exp ((N : ℂ) * δ * I) := by
    unfold besselPhase
    rw [← Complex.exp_add]
    congr 1
    simp [x₁, x₂]
    ring
  have hw1 : Complex.exp ((N : ℂ) * δ * I) ≠ 1 := by
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨j, hj⟩ := h
    apply hδ j
    have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have h2 : ((N : ℝ) * δ : ℂ) = (j * (2 * Real.pi) : ℝ) := by
      push_cast
      have := hj
      field_simp at this
      linear_combination this
    exact_mod_cast h2
  have hlt : ‖f x₁ + f x₂‖ < ‖f x₁‖ + ‖f x₂‖ := by
    have e1 : f x₁ + f x₂ = besselPhase x₁ δ * ((besselTerm β x₁ : ℂ) +
        (besselTerm β x₂ : ℂ) * Complex.exp ((N : ℂ) * δ * I)) := by
      simp only [hfdef, hx₁, hx₂, hw, Complex.ofReal_one, mul_one]
      ring
    rw [e1, norm_mul, norm_besselPhase, one_mul, hnorm, hnorm, hx₁, hx₂, mul_one, mul_one]
    refine norm_add_mul_lt (besselTerm_pos hβ _) (besselTerm_pos hβ _) ?_ hw1
    rw [Complex.norm_exp]
    simp
  have h := norm_tsum_lt_of_two hsum hne hlt
  rw [← clockAngleFourier_twistedClockWeight hN] at h
  simp_rw [hnorm] at h
  exact h

/-- **A uniform contraction** for `Nδ ∉ 2πℤ`: some `λ < 1` with `‖ŵ_δ(μ)‖ ≤ λ c(μ)` for all `μ`. -/
theorem exists_twistedClockWeight_contraction {N : ℕ} (hN : 0 < N) {β δ : ℝ} (hβ : 0 < β)
    (hδ : ∀ j : ℤ, (N : ℝ) * δ ≠ j * (2 * Real.pi)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧
      ∀ μ : Fin N, ‖clockAngleFourier N (twistedClockWeight β δ) μ‖ ≤ lam * clockWeightCoeff N β μ := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨μ₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun μ => ‖clockAngleFourier N (twistedClockWeight β δ) μ‖ / clockWeightCoeff N β μ) hne
  refine ⟨‖clockAngleFourier N (twistedClockWeight β δ) μ₀‖ / clockWeightCoeff N β μ₀,
    div_nonneg (norm_nonneg _) (clockWeightCoeff_pos hβ μ₀).le, ?_, fun μ => ?_⟩
  · rw [div_lt_one (clockWeightCoeff_pos hβ μ₀)]
    exact norm_clockAngleFourier_twistedClockWeight_lt hN hβ hδ μ₀
  · have h := hmax μ (Finset.mem_univ _)
    rwa [div_le_iff₀ (clockWeightCoeff_pos hβ μ)] at h

end FroehlichSpencer.BKT.Clock.Disorder

end
