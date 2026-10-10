/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The whole-plane lattice potential (FS81 p. 529, free boundary condition)

In two dimensions this
Green function is defined up to an additive constant, which drops out of the energy of every
neutral configuration ((1.14), p. 531).

We use the standard normalization by the **potential
kernel**

`a(z) = (2π)⁻² ∫_{[0,2π)²} (1 - cos ⟨k, z⟩) / ε(k) dk`,  `ε(k) = 2 (1 - cos k₁) + 2 (1 - cos k₂)`,

and `C(i - j) = -a(i - j)`, so that `C(0,0) - C(0,x) = a(x)` as in the Remark on J p. 567.

* `potentialKernelIntegrand_le`: `0 ≤ (1 - cos ⟨k,z⟩)/ε(k) ≤ |z|²` for **every** `k` (with the
  value `0` where `ε = 0`); the proof uses `1 - cos(a + b) ≤ 2(1 - cos a) + 2(1 - cos b)` and
  `1 - cos(n x) ≤ n²(1 - cos x)`, so no Taylor expansion and no polar coordinates are needed.

The integrand is therefore bounded and the integral is an honest Lebesgue integral.
* `potentialKernel_laplacian` (**characterization**): `Δa = δ₀` on `ℤ²`, i.e.

`-Δ C = δ₀`:
  `C` is a Green function of `-Δ` on `ℤ²`.

Also `a(0) = 0`, `a(-z) = a(z)`, `a ≥ 0`.

The torus Green functions converge to `-a` on neutral charges (`Coulomb/TorusKernel.lean`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory Set

/-! ### Elementary trigonometric inequalities -/

theorem abs_sin_nat_mul_le (m : ℕ) (x : ℝ) : |Real.sin (m * x)| ≤ m * |Real.sin x| := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : Real.sin (((m + 1 : ℕ) : ℝ) * x) =
        Real.sin (m * x) * Real.cos x + Real.cos (m * x) * Real.sin x := by
      rw [← Real.sin_add]; push_cast; ring_nf
    rw [h]
    calc |Real.sin (m * x) * Real.cos x + Real.cos (m * x) * Real.sin x|
        ≤ |Real.sin (m * x) * Real.cos x| + |Real.cos (m * x) * Real.sin x| := abs_add_le _ _
      _ ≤ |Real.sin (m * x)| + |Real.sin x| := by
        rw [abs_mul, abs_mul]
        gcongr
        · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
        · exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ m * |Real.sin x| + |Real.sin x| := by linarith
      _ = ((m + 1 : ℕ) : ℝ) * |Real.sin x| := by push_cast; ring

theorem abs_sin_int_mul_le (n : ℤ) (x : ℝ) : |Real.sin (n * x)| ≤ |(n : ℝ)| * |Real.sin x| := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using abs_sin_nat_mul_le m x
  · have := abs_sin_nat_mul_le m x
    simpa [neg_mul, Real.sin_neg, abs_neg] using this

theorem one_sub_cos_eq_two_mul_sin_sq (x : ℝ) : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  rw [h]
  have := Real.sin_sq_add_cos_sq (x / 2)
  linarith

theorem one_sub_cos_int_mul_le (n : ℤ) (x : ℝ) :
    1 - Real.cos (n * x) ≤ (n : ℝ) ^ 2 * (1 - Real.cos x) := by
  rw [one_sub_cos_eq_two_mul_sin_sq, one_sub_cos_eq_two_mul_sin_sq,
    show (n : ℝ) * x / 2 = n * (x / 2) by ring]
  have h := abs_sin_int_mul_le n (x / 2)
  have h2 : Real.sin (n * (x / 2)) ^ 2 ≤ (n : ℝ) ^ 2 * Real.sin (x / 2) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h 2
    rwa [sq_abs, mul_pow, sq_abs, sq_abs] at this
  linarith

theorem one_sub_cos_add_le (a b : ℝ) :
    1 - Real.cos (a + b) ≤ 2 * (1 - Real.cos a) + 2 * (1 - Real.cos b) := by
  rw [one_sub_cos_eq_two_mul_sin_sq, one_sub_cos_eq_two_mul_sin_sq,
    one_sub_cos_eq_two_mul_sin_sq, show (a + b) / 2 = a / 2 + b / 2 by ring, Real.sin_add]
  have hca := Real.abs_cos_le_one (b / 2)
  have hcb := Real.abs_cos_le_one (a / 2)
  have h1 : |Real.sin (a / 2) * Real.cos (b / 2) + Real.cos (a / 2) * Real.sin (b / 2)| ≤
      |Real.sin (a / 2)| + |Real.sin (b / 2)| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
    · exact mul_le_of_le_one_right (abs_nonneg _) hca
    · exact mul_le_of_le_one_left (abs_nonneg _) hcb
  have h2 : (Real.sin (a / 2) * Real.cos (b / 2) + Real.cos (a / 2) * Real.sin (b / 2)) ^ 2 ≤
      (|Real.sin (a / 2)| + |Real.sin (b / 2)|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : (|Real.sin (a / 2)| + |Real.sin (b / 2)|) ^ 2 ≤
      2 * Real.sin (a / 2) ^ 2 + 2 * Real.sin (b / 2) ^ 2 := by
    nlinarith [sq_abs (Real.sin (a / 2)), sq_abs (Real.sin (b / 2)),
      sq_nonneg (|Real.sin (a / 2)| - |Real.sin (b / 2)|)]
  nlinarith

/-! ### The lattice symbol and the potential kernel -/

/-- The symbol of `-Δ` on `ℤ²`: `ε(k) = 2 (1 - cos k₁) + 2 (1 - cos k₂)`. -/
def latticeSymbolInternal (k : ℝ × ℝ) : ℝ :=
  2 * (1 - Real.cos k.1) + 2 * (1 - Real.cos k.2)

/-- The integrand `(1 - cos ⟨k, z⟩) / ε(k)` of the potential kernel (`0` where `ε = 0`). -/
def potentialKernelIntegrandInternal (z : ℤ × ℤ) (k : ℝ × ℝ) : ℝ :=
  (1 - Real.cos (k.1 * z.1 + k.2 * z.2)) / latticeSymbolInternal k

/-- The fundamental frequency square `[0, 2π)²`. -/
def frequencySquareInternal : Set (ℝ × ℝ) :=
  Ico 0 (2 * Real.pi) ×ˢ Ico 0 (2 * Real.pi)

/-- The potential kernel of the two-dimensional lattice,
`a(z) = (2π)⁻² ∫_{[0,2π)²} (1 - cos ⟨k, z⟩) / ε(k) dk`. FS81's free potential is
`C(i - j) = -a(i - j)` (up to an additive constant, irrelevant for neutral charges). -/
def potentialKernelInternal (z : ℤ × ℤ) : ℝ :=
  ((2 * Real.pi) ^ 2)⁻¹ * ∫ k in frequencySquareInternal, potentialKernelIntegrandInternal z k

theorem latticeSymbol_nonneg (k : ℝ × ℝ) : 0 ≤ latticeSymbolInternal k := by
  unfold latticeSymbolInternal
  have := Real.cos_le_one k.1
  have := Real.cos_le_one k.2
  linarith

theorem one_sub_cos_phase_le (z : ℤ × ℤ) (k : ℝ × ℝ) :
    1 - Real.cos (k.1 * z.1 + k.2 * z.2) ≤
      ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) * latticeSymbolInternal k := by
  have h1 := one_sub_cos_add_le (k.1 * z.1) (k.2 * z.2)
  have h2 := one_sub_cos_int_mul_le z.1 k.1
  have h3 := one_sub_cos_int_mul_le z.2 k.2
  rw [mul_comm (z.1 : ℝ)] at h2
  rw [mul_comm (z.2 : ℝ)] at h3
  have hc1 := Real.cos_le_one k.1
  have hc2 := Real.cos_le_one k.2
  unfold latticeSymbolInternal
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ),
    mul_nonneg (sq_nonneg (z.1 : ℝ)) (sub_nonneg.2 hc2),
    mul_nonneg (sq_nonneg (z.2 : ℝ)) (sub_nonneg.2 hc1)]

theorem potentialKernelIntegrand_nonneg (z : ℤ × ℤ) (k : ℝ × ℝ) :
    0 ≤ potentialKernelIntegrandInternal z k :=
  div_nonneg (sub_nonneg.2 (Real.cos_le_one _)) (latticeSymbol_nonneg k)

theorem potentialKernelIntegrand_le (z : ℤ × ℤ) (k : ℝ × ℝ) :
    potentialKernelIntegrandInternal z k ≤ (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  unfold potentialKernelIntegrandInternal
  rcases (latticeSymbol_nonneg k).eq_or_lt with h | h
  · rw [← h, div_zero]; positivity
  · rw [div_le_iff₀ h]
    exact one_sub_cos_phase_le z k

theorem measurable_potentialKernelIntegrand (z : ℤ × ℤ) :
    Measurable (potentialKernelIntegrandInternal z) := by
  unfold potentialKernelIntegrandInternal latticeSymbolInternal
  fun_prop

theorem volume_frequencySquare_lt_top : volume frequencySquareInternal < ⊤ := by
  rw [frequencySquareInternal, Measure.volume_eq_prod, Measure.prod_prod]
  simp [Real.volume_Ico, ENNReal.mul_lt_top]

theorem measurableSet_frequencySquare : MeasurableSet frequencySquareInternal :=
  measurableSet_Ico.prod measurableSet_Ico

instance : IsFiniteMeasure (volume.restrict frequencySquareInternal) :=
  isFiniteMeasure_restrict.2 volume_frequencySquare_lt_top.ne

/-- A function bounded in absolute value on the frequency square is integrable there. -/
theorem integrableOn_frequencySquare_of_bound {F : ℝ × ℝ → ℝ} (hF : AEStronglyMeasurable F
    (volume.restrict frequencySquareInternal)) (B : ℝ) (hB : ∀ k, |F k| ≤ B) :
    IntegrableOn F frequencySquareInternal :=
  Integrable.of_bound hF B (ae_of_all _ fun k => (Real.norm_eq_abs _).le.trans (hB k))

theorem integrableOn_potentialKernelIntegrand (z : ℤ × ℤ) :
    IntegrableOn (potentialKernelIntegrandInternal z) frequencySquareInternal :=
  integrableOn_frequencySquare_of_bound
    (measurable_potentialKernelIntegrand z).aestronglyMeasurable _ fun k => by
      rw [abs_of_nonneg (potentialKernelIntegrand_nonneg z k)]
      exact potentialKernelIntegrand_le z k

theorem potentialKernel_zero : potentialKernelInternal 0 = 0 := by
  simp [potentialKernelInternal, potentialKernelIntegrandInternal]

theorem potentialKernel_neg (z : ℤ × ℤ) :
    potentialKernelInternal (-z) = potentialKernelInternal z := by
  unfold potentialKernelInternal potentialKernelIntegrandInternal
  congr 2
  funext k
  congr 2
  rw [← Real.cos_neg]
  congr 1
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

theorem potentialKernel_nonneg (z : ℤ × ℤ) : 0 ≤ potentialKernelInternal z :=
  mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_frequencySquare fun k _ =>
      potentialKernelIntegrand_nonneg z k)

/-! ### `a` is the Green function of `-Δ` on `ℤ²` (up to sign) -/

theorem integral_exp_int_mul_Ico (n : ℤ) :
    (∫ t in Ico 0 (2 * Real.pi), Complex.exp (Complex.I * n * t)) =
      if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
  by_cases hn : n = 0
  · subst hn
    simp [intervalIntegral.integral_const]
  · have hc : Complex.I * (n : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hn)
    rw [integral_exp_mul_complex hc]
    have hper : Complex.exp (Complex.I * n * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have : Complex.I * n * ((2 * Real.pi : ℝ) : ℂ) = n * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [hper]
    simp [hn]

theorem integral_cos_phase (z : ℤ × ℤ) :
    ∫ k in frequencySquareInternal, Real.cos (k.1 * z.1 + k.2 * z.2) =
      if z = 0 then (2 * Real.pi) ^ 2 else 0 := by
  set F : ℝ × ℝ → ℂ := fun k => Complex.exp (Complex.I * z.1 * k.1) *
    Complex.exp (Complex.I * z.2 * k.2) with hF
  have hint : IntegrableOn F frequencySquareInternal := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun k => ?_)
    simp only [hF, norm_mul]
    rw [show Complex.I * z.1 * k.1 = ((z.1 * k.1 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      show Complex.I * z.2 * k.2 = ((z.2 * k.2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hre : ∀ k : ℝ × ℝ, Real.cos (k.1 * z.1 + k.2 * z.2) = RCLike.re (F k) := by
    intro k
    simp only [hF, RCLike.re_to_complex, ← Complex.exp_add]
    rw [show Complex.I * z.1 * k.1 + Complex.I * z.2 * k.2 =
      ((k.1 * z.1 + k.2 * z.2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  simp_rw [hre]
  rw [integral_re hint]
  have hprod : ∫ k in frequencySquareInternal, F k =
      (∫ t in Ico 0 (2 * Real.pi), Complex.exp (Complex.I * z.1 * t)) *
        ∫ t in Ico 0 (2 * Real.pi), Complex.exp (Complex.I * z.2 * t) := by
    rw [frequencySquareInternal, Measure.volume_eq_prod]
    exact setIntegral_prod_mul (fun t : ℝ => Complex.exp (Complex.I * z.1 * t))
      (fun t : ℝ => Complex.exp (Complex.I * z.2 * t)) _ _
  rw [hprod, integral_exp_int_mul_Ico, integral_exp_int_mul_Ico]
  rcases z with ⟨z₁, z₂⟩
  by_cases h1 : z₁ = 0 <;> by_cases h2 : z₂ = 0 <;> simp [h1, h2]
  ring

theorem latticeSymbol_ne_zero_of_mem {k : ℝ × ℝ} (hk : k ∈ frequencySquareInternal)
    (hk0 : k ≠ 0) : latticeSymbolInternal k ≠ 0 := by
  intro h
  have hc1 := Real.cos_le_one k.1
  have hc2 := Real.cos_le_one k.2
  unfold latticeSymbolInternal at h
  have e1 : Real.cos k.1 = 1 := by linarith
  have e2 : Real.cos k.2 = 1 := by linarith
  have hpi := Real.pi_pos
  rcases hk with ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
  have k1 : k.1 = 0 := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) b1).1 e1
  have k2 : k.2 = 0 := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) b2).1 e2
  exact hk0 (Prod.ext k1 k2)

theorem ae_ne_zero_prod : ∀ᵐ k ∂(volume : Measure (ℝ × ℝ)), k ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
  rw [show ({0} : Set (ℝ × ℝ)) = {0} ×ˢ {0} by simp [Set.singleton_prod_singleton]; rfl,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- The pointwise lattice-Laplacian identity of the integrand. -/
theorem potentialKernelIntegrand_laplacian (z : ℤ × ℤ) {k : ℝ × ℝ}
    (hk : latticeSymbolInternal k ≠ 0) :
    potentialKernelIntegrandInternal (z + (1, 0)) k +
        potentialKernelIntegrandInternal (z - (1, 0)) k +
        potentialKernelIntegrandInternal (z + (0, 1)) k +
        potentialKernelIntegrandInternal (z - (0, 1)) k -
        4 * potentialKernelIntegrandInternal z k =
      Real.cos (k.1 * z.1 + k.2 * z.2) := by
  unfold potentialKernelIntegrandInternal
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Int.cast_add,
    Int.cast_sub, Int.cast_one, add_zero, sub_zero]
  set ε := latticeSymbolInternal k with hε
  set θ := k.1 * z.1 + k.2 * z.2
  have e1 : k.1 * (z.1 + 1) + k.2 * z.2 = θ + k.1 := by ring
  have e2 : k.1 * (z.1 - 1) + k.2 * z.2 = θ - k.1 := by ring
  have e3 : k.1 * z.1 + k.2 * (z.2 + 1) = θ + k.2 := by ring
  have e4 : k.1 * z.1 + k.2 * (z.2 - 1) = θ - k.2 := by ring
  rw [e1, e2, e3, e4]
  have key : (1 - Real.cos (θ + k.1)) + (1 - Real.cos (θ - k.1)) + (1 - Real.cos (θ + k.2)) +
      (1 - Real.cos (θ - k.2)) - 4 * (1 - Real.cos θ) = Real.cos θ * ε := by
    rw [Real.cos_add θ k.1, Real.cos_sub θ k.1, Real.cos_add θ k.2, Real.cos_sub θ k.2, hε]
    unfold latticeSymbolInternal
    ring
  rw [show (1 - Real.cos (θ + k.1)) / ε + (1 - Real.cos (θ - k.1)) / ε +
      (1 - Real.cos (θ + k.2)) / ε + (1 - Real.cos (θ - k.2)) / ε - 4 * ((1 - Real.cos θ) / ε) =
      ((1 - Real.cos (θ + k.1)) + (1 - Real.cos (θ - k.1)) + (1 - Real.cos (θ + k.2)) +
      (1 - Real.cos (θ - k.2)) - 4 * (1 - Real.cos θ)) / ε by ring, key,
    mul_div_assoc, div_self hk, mul_one]

/-- **FS81 p. 529 (i): the whole-plane Green function.** The potential kernel satisfies
`Δa = δ₀` on `ℤ²` (`Δ f(z) = ∑_{|e|=1} (f(z+e) - f(z))`), so `C = -a` satisfies `-ΔC = δ₀`. -/
theorem potentialKernel_laplacian (z : ℤ × ℤ) :
    potentialKernelInternal (z + (1, 0)) + potentialKernelInternal (z - (1, 0)) +
        potentialKernelInternal (z + (0, 1)) + potentialKernelInternal (z - (0, 1)) -
        4 * potentialKernelInternal z = if z = 0 then 1 else 0 := by
  have hI := integrableOn_potentialKernelIntegrand
  unfold potentialKernelInternal
  have hcomb : ∫ k in frequencySquareInternal,
      (potentialKernelIntegrandInternal (z + (1, 0)) k +
        potentialKernelIntegrandInternal (z - (1, 0)) k +
        potentialKernelIntegrandInternal (z + (0, 1)) k +
        potentialKernelIntegrandInternal (z - (0, 1)) k -
        4 * potentialKernelIntegrandInternal z k) =
      ∫ k in frequencySquareInternal, Real.cos (k.1 * z.1 + k.2 * z.2) := by
    refine setIntegral_congr_ae measurableSet_frequencySquare ?_
    filter_upwards [ae_ne_zero_prod] with k hk0 hk
    exact potentialKernelIntegrand_laplacian z (latticeSymbol_ne_zero_of_mem hk hk0)
  set h₁ := potentialKernelIntegrandInternal (z + (1, 0))
  set h₂ := potentialKernelIntegrandInternal (z - (1, 0))
  set h₃ := potentialKernelIntegrandInternal (z + (0, 1))
  set h₄ := potentialKernelIntegrandInternal (z - (0, 1))
  set h₀ := potentialKernelIntegrandInternal z
  have i1 : IntegrableOn h₁ frequencySquareInternal := hI _
  have i2 : IntegrableOn h₂ frequencySquareInternal := hI _
  have i3 : IntegrableOn h₃ frequencySquareInternal := hI _
  have i4 : IntegrableOn h₄ frequencySquareInternal := hI _
  have i0 : IntegrableOn h₀ frequencySquareInternal := hI _
  rw [integral_sub (f := fun k => h₁ k + h₂ k + h₃ k + h₄ k) (g := fun k => 4 * h₀ k)
      (((i1.add i2).add i3).add i4) (i0.const_mul 4),
    integral_add (f := fun k => h₁ k + h₂ k + h₃ k) (g := h₄) ((i1.add i2).add i3) i4,
    integral_add (f := fun k => h₁ k + h₂ k) (g := h₃) (i1.add i2) i3,
    integral_add (f := h₁) (g := h₂) i1 i2, integral_const_mul, integral_cos_phase] at hcomb
  have hpi : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  split_ifs at hcomb ⊢ with hz
  · field_simp
    linear_combination hcomb
  · have : ((2 * Real.pi) ^ 2)⁻¹ * ((∫ k in frequencySquareInternal,
        potentialKernelIntegrandInternal (z + (1, 0)) k) +
        (∫ k in frequencySquareInternal, potentialKernelIntegrandInternal (z - (1, 0)) k) +
        (∫ k in frequencySquareInternal, potentialKernelIntegrandInternal (z + (0, 1)) k) +
        (∫ k in frequencySquareInternal, potentialKernelIntegrandInternal (z - (0, 1)) k) -
        4 * ∫ k in frequencySquareInternal, potentialKernelIntegrandInternal z k) = 0 := by
      rw [hcomb, mul_zero]
    linear_combination this

end FroehlichSpencer.BKT.Coulomb
