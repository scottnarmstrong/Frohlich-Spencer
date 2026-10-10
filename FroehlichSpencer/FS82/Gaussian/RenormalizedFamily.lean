/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.ConditionalGaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

open Complex MeasureTheory

namespace FroehlichSpencer.FS82.Gaussian.RenormalizedFamily

open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian

variable {C P : Type*} [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]

local instance (priority := 2000) selectedCoordFintype (B : Finset C) :
    Fintype {c : C // c ∈ B} := Subtype.fintype _

local instance (priority := 2000) retainedCoordFintype (B : Finset C) :
    Fintype {c : C // c ∉ B} := Subtype.fintype _

open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian

/-- The normalized real density of a normal variable with mean `m` and variance `β / n`. -/
noncomputable def selectedGaussianDensity (β n m x : ℝ) : ℝ :=
  Real.exp (-(n / (2 * β)) * (x - m) ^ 2) / linkGaussianMass β n

/--
The complex Gaussian integral's coefficient is the real normalization factor already used by
conditional integration.
-/
theorem complexGaussianCoefficient_eq_linkGaussianMass (β n : ℝ)
    (hβ : 0 < β) (hn : 0 < n) :
    ((Real.pi : ℂ) / ((n / (2 * β) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
      (linkGaussianMass β n : ℂ) := by
  let A : ℝ := n / (2 * β)
  let b : ℂ := (-(A : ℝ) : ℂ)
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (by exact_mod_cast hn) (by positivity)
  have hb : b.re < 0 := by
    change -A < 0
    exact neg_lt_zero.mpr hA
  have hquad := _root_.integral_cexp_quadratic hb (0 : ℂ) (0 : ℂ)
  have hcoeff :
      ((Real.pi : ℂ) / ((n / (2 * β) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
        ∫ x : ℝ, Complex.exp (b * (x : ℂ) ^ 2) := by
    symm
    simpa [b, A, Complex.exp_zero] using hquad
  have hfun : (fun x : ℝ => Complex.exp (b * (x : ℂ) ^ 2)) =
      (fun x : ℝ => (Complex.ofReal (Real.exp (-(n / (2 * β)) * x ^ 2)))) := by
    funext x
    rw [Complex.ofReal_exp]
    congr 1
    dsimp [b, A]
    push_cast
    ring
  rw [hcoeff, hfun, integral_complex_ofReal]
  have hmass := completedSquare_link_mass β n 0 hβ hn
  simpa [linkGaussianMass] using congrArg (fun r : ℝ => (r : ℂ)) hmass

/-- The unnormalized one-coordinate complex tilt/characteristic integral for the conditional
normal law. `u` is the real tilt coefficient; the requested `t * a` specialization is below. -/
theorem selectedGaussian_tiltCharacteristic_raw (β n m u q : ℝ)
    (hβ : 0 < β) (hn : 0 < n) :
    (∫ x : ℝ,
      Complex.exp ((-(n / (2 * β)) * (x - m) ^ 2 : ℝ) : ℂ) *
        Complex.exp (((u * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ))) =
      (linkGaussianMass β n : ℂ) *
        Complex.exp ((u * m + β * u ^ 2 / (2 * n) - β * q ^ 2 / (2 * n) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (q * m + β * u * q / n : ℝ)) := by
  let A : ℝ := n / (2 * β)
  let b : ℂ := (-(A : ℝ) : ℂ)
  let c : ℂ := ((2 * A * m + u : ℝ) : ℂ) + Complex.I * (q : ℂ)
  let d : ℂ := (-(A * m ^ 2 : ℝ) : ℂ)
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (by exact_mod_cast hn) (by positivity)
  have hb : b.re < 0 := by
    change -A < 0
    exact neg_lt_zero.mpr hA
  have hrewrite (x : ℝ) :
      Complex.exp ((-(n / (2 * β)) * (x - m) ^ 2 : ℝ) : ℂ) *
          Complex.exp (((u * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ)) =
        Complex.exp (b * (x : ℂ) ^ 2 + c * (x : ℂ) + d) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [A, b, c, d]
    push_cast
    ring
  have hintegral :
      (∫ x : ℝ,
        Complex.exp ((-(n / (2 * β)) * (x - m) ^ 2 : ℝ) : ℂ) *
          Complex.exp (((u * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ))) =
        (Real.pi / -b) ^ (1 / 2 : ℂ) *
          Complex.exp (d - c ^ 2 / (4 * b)) := by
    rw [show (fun x : ℝ =>
      Complex.exp ((-(n / (2 * β)) * (x - m) ^ 2 : ℝ) : ℂ) *
        Complex.exp (((u * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ))) =
      (fun x : ℝ => Complex.exp (b * (x : ℂ) ^ 2 + c * (x : ℂ) + d)) from funext hrewrite]
    exact _root_.integral_cexp_quadratic hb c d
  have hcoeff : (Real.pi / -b) ^ (1 / 2 : ℂ) =
      (linkGaussianMass β n : ℂ) := by
    simpa [b, A] using complexGaussianCoefficient_eq_linkGaussianMass β n hβ hn
  have hexp : d - c ^ 2 / (4 * b) =
      ((u * m + β * u ^ 2 / (2 * n) - β * q ^ 2 / (2 * n) : ℝ) : ℂ) +
        Complex.I * (q * m + β * u * q / n : ℝ) := by
    dsimp [A, b, c, d]
    push_cast
    field_simp [ne_of_gt hβ, ne_of_gt (show (n : ℝ) > 0 by exact_mod_cast hn)]
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [hintegral, hcoeff, hexp, Complex.exp_add]
  simp only [mul_assoc]

/-- A normalized Gaussian expectation of the tilt `exp(t a X)` and character `exp(i q X)` for
`X ~ N(m, β/n)`. The four factors expose the tilt, Gaussian damping, mean phase, and tilt phase. -/
theorem selectedGaussian_tiltCharacteristic (β n m t a q : ℝ)
    (hβ : 0 < β) (hn : 0 < n) :
    (∫ x : ℝ,
      (selectedGaussianDensity β n m x : ℂ) *
        Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ))) =
      Complex.exp ((t * a * m + β * t ^ 2 * a ^ 2 / (2 * n) : ℝ) : ℂ) *
        Complex.exp ((-(β * q ^ 2 / (2 * n)) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (q * m : ℝ)) *
        Complex.exp (Complex.I * (β * t * a * q / n : ℝ)) := by
  let D : ℝ := linkGaussianMass β n
  have hD : D ≠ 0 := ne_of_gt (linkGaussianMass_pos β n hβ (by exact_mod_cast hn))
  have hfactor (x : ℝ) :
      (selectedGaussianDensity β n m x : ℂ) *
          Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ)) =
        (D⁻¹ : ℂ) *
          (Complex.exp ((-(n / (2 * β)) * (x - m) ^ 2 : ℝ) : ℂ) *
            Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ))) := by
    change Complex.ofReal (Real.exp (-(n / (2 * β)) * (x - m) ^ 2) /
          linkGaussianMass β n) *
        Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ)) = _
    rw [Complex.ofReal_div, Complex.ofReal_exp]
    simp only [div_eq_mul_inv]
    ring
  rw [show (fun x : ℝ =>
      (selectedGaussianDensity β n m x : ℂ) *
        Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ))) =
      (fun x : ℝ => (D⁻¹ : ℂ) *
        (Complex.exp ((-(n / (2 * β)) * (x - m) ^ 2 : ℝ) : ℂ) *
          Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ)))) from funext hfactor]
  rw [integral_const_mul]
  rw [selectedGaussian_tiltCharacteristic_raw β n m (t * a) q hβ hn]
  have hDcomplex : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  rw [show (linkGaussianMass β n : ℂ) = (D : ℂ) by rfl]
  have hreal :
      (t * a * m + β * (t * a) ^ 2 / (2 * n) - β * q ^ 2 / (2 * n) : ℝ) =
        (t * a * m + β * t ^ 2 * a ^ 2 / (2 * n)) +
          (-(β * q ^ 2 / (2 * n))) := by ring
  have himag :
      (q * m + β * (t * a) * q / n : ℝ) = q * m + β * t * a * q / n := by ring
  have hphase :
      Complex.exp (Complex.I * Complex.ofReal (q * m + β * t * a * q / n)) =
        Complex.exp (Complex.I * Complex.ofReal (q * m)) *
          Complex.exp (Complex.I * Complex.ofReal (β * t * a * q / n)) := by
    have hcast : Complex.ofReal (q * m + β * t * a * q / n) =
        Complex.ofReal (q * m) + Complex.ofReal (β * t * a * q / n) :=
      Complex.ofReal_add _ _
    rw [hcast, mul_add, Complex.exp_add]
  have hsplit :
      Complex.exp
          ((t * a * m + β * (t * a) ^ 2 / (2 * n) - β * q ^ 2 / (2 * n) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (q * m + β * (t * a) * q / n : ℝ)) =
      Complex.exp ((t * a * m + β * t ^ 2 * a ^ 2 / (2 * n) : ℝ) : ℂ) *
        Complex.exp ((-(β * q ^ 2 / (2 * n)) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (q * m : ℝ)) *
        Complex.exp (Complex.I * (β * t * a * q / n : ℝ)) := by
    rw [show ((t * a * m + β * (t * a) ^ 2 / (2 * n) - β * q ^ 2 / (2 * n) : ℝ) : ℂ) =
        ((t * a * m + β * t ^ 2 * a ^ 2 / (2 * n) : ℝ) : ℂ) +
          ((-(β * q ^ 2 / (2 * n)) : ℝ) : ℂ) by exact_mod_cast hreal]
    rw [Complex.exp_add]
    rw [himag, hphase]
    ring_nf
  have hcancel : (D⁻¹ : ℂ) * (D : ℂ) = 1 := inv_mul_cancel₀ hDcomplex
  calc
    _ = ((D⁻¹ : ℂ) * (D : ℂ)) *
        (Complex.exp
          ((t * a * m + β * (t * a) ^ 2 / (2 * n) - β * q ^ 2 / (2 * n) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (q * m + β * (t * a) * q / n : ℝ))) := by ring
    _ = Complex.exp
        ((t * a * m + β * (t * a) ^ 2 / (2 * n) - β * q ^ 2 / (2 * n) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (q * m + β * (t * a) * q / n : ℝ)) := by
        rw [hcancel, one_mul]
    _ = _ := hsplit

/-- The one-coordinate Gaussian tilt/character integrand is Bochner integrable. -/
theorem selectedGaussian_tiltCharacteristic_integrable (β n m t a q : ℝ)
    (hβ : 0 < β) (hn : 0 < n) :
    Integrable (fun x : ℝ =>
      (selectedGaussianDensity β n m x : ℂ) *
        Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ))) := by
  let A : ℝ := n / (2 * β)
  let b : ℂ := (-(A : ℝ) : ℂ)
  let c : ℂ := ((2 * A * m + t * a : ℝ) : ℂ) + Complex.I * (q : ℂ)
  let d : ℂ := (-(A * m ^ 2 : ℝ) : ℂ)
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (by exact_mod_cast hn) (by positivity)
  have hb : b.re < 0 := by
    change -A < 0
    exact neg_lt_zero.mpr hA
  have hquad := integrable_cexp_quadratic' hb c d
  let D := linkGaussianMass β n
  have hrewrite (x : ℝ) :
      (selectedGaussianDensity β n m x : ℂ) *
          Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ)) =
        (D⁻¹ : ℂ) * Complex.exp (b * (x : ℂ) ^ 2 + c * (x : ℂ) + d) := by
    change Complex.ofReal
        (Real.exp (-(n / (2 * β)) * (x - m) ^ 2) / linkGaussianMass β n) * _ = _
    rw [Complex.ofReal_div, Complex.ofReal_exp]
    simp only [div_eq_mul_inv]
    calc
      _ = (D⁻¹ : ℂ) *
          (Complex.exp ((-(n / (2 * β)) * (x - m) ^ 2 : ℝ) : ℂ) *
            Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ))) := by
              change Complex.exp ((-(n / (2 * β)) * (x - m) ^ 2 : ℝ) : ℂ) *
                (Complex.ofReal (linkGaussianMass β n))⁻¹ * _ = _
              change Complex.exp ((-(n / (2 * β)) * (x - m) ^ 2 : ℝ) : ℂ) *
                (D : ℂ)⁻¹ * _ = _
              ring
      _ = (D⁻¹ : ℂ) * Complex.exp (b * (x : ℂ) ^ 2 + c * (x : ℂ) + d) := by
        congr 2
        rw [← Complex.exp_add]
        congr 1
        dsimp [A, b, c, d]
        push_cast
        ring
  have heq : (fun x : ℝ =>
      (selectedGaussianDensity β n m x : ℂ) *
        Complex.exp (((t * a * x : ℝ) : ℂ) + Complex.I * (q * x : ℝ))) =
      fun x : ℝ => (D⁻¹ : ℂ) * Complex.exp (b * (x : ℂ) ^ 2 + c * (x : ℂ) + d) := by
    funext x
    exact hrewrite x
  rw [heq]
  exact hquad.const_mul _

omit [DecidableEq P] in
/-- The selected conditional density is the finite product of the one-coordinate Gaussian
densities with means `selectedMean` and precisions `linkMass`. -/
theorem selectedConditionalWeight_eq_prod_density
    (β : ℝ) (s : P → C → ℝ)
    (B : Finset C) (y : {c : C // c ∉ B} → ℝ)
    (x : {c : C // c ∈ B} → ℝ) :
    selectedConditionalWeight β s B y x =
      ∏ b : {c : C // c ∈ B},
        selectedGaussianDensity β (linkMass s b.1)
          (selectedMean s B y b) (x b) := by
  classical
  rw [selectedConditionalWeight]
  change
    (∏ b : {c : C // c ∈ B},
      Real.exp (-(linkMass s b.1 / (2 * β)) *
        (x b + linkOffset s B y b.1 / linkMass s b.1) ^ 2)) /
        (∏ b : {c : C // c ∈ B}, linkGaussianMass β (linkMass s b.1)) = _
  rw [← Finset.prod_div_distrib (s := Finset.univ)]
  apply Finset.prod_congr rfl
  intro b hb
  unfold selectedGaussianDensity selectedMean
  congr 1
  congr 2
  ring

omit [DecidableEq P] in
/-- The conditional selected-coordinate integral of an arbitrary linear character factors into
the one-coordinate complex Gaussian tilt/character integrals. -/
theorem selectedConditionalWeight_integral_character
    (β t : ℝ) (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (τ q : C → ℝ)
    (hβ : 0 < β) (hn : ∀ b ∈ B, 0 < linkMass s b) :
    (∫ x : {c : C // c ∈ B} → ℝ,
      (selectedConditionalWeight β s B y x : ℂ) *
        Complex.exp
          ((∑ b : {c : C // c ∈ B}, t * τ b.1 * x b : ℝ) : ℂ) *
        Complex.exp
          (Complex.I * ((∑ b : {c : C // c ∈ B}, q b.1 * x b : ℝ) : ℂ))) =
      ∏ b : {c : C // c ∈ B},
        (Complex.exp
          ((t * τ b.1 * selectedMean s B y b +
            β * t ^ 2 * τ b.1 ^ 2 / (2 * linkMass s b.1) : ℝ) : ℂ) *
          Complex.exp
            ((-(β * q b.1 ^ 2 / (2 * linkMass s b.1)) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (q b.1 * selectedMean s B y b : ℝ)) *
          Complex.exp
            (Complex.I * (β * t * τ b.1 * q b.1 / linkMass s b.1 : ℝ))) := by
  classical
  let D := {c : C // c ∈ B}
  let f : D → ℝ → ℂ := fun b z =>
    (selectedGaussianDensity β (linkMass s b.1)
      (selectedMean s B y b) z : ℂ) *
      Complex.exp (((t * τ b.1 * z : ℝ) : ℂ) +
        Complex.I * (q b.1 * z : ℝ))
  have hfun :
      (fun x : D → ℝ =>
        (selectedConditionalWeight β s B y x : ℂ) *
          Complex.exp
            ((∑ b : D, t * τ b.1 * x b : ℝ) : ℂ) *
          Complex.exp
            (Complex.I * ((∑ b : D, q b.1 * x b : ℝ) : ℂ))) =
      fun x => ∏ b : D, f b (x b) := by
    funext x
    rw [selectedConditionalWeight_eq_prod_density]
    have hexp :
        Complex.exp
            ((∑ b : D, t * τ b.1 * x b : ℝ) : ℂ) *
          Complex.exp
            (Complex.I * ((∑ b : D, q b.1 * x b : ℝ) : ℂ)) =
          ∏ b : D, Complex.exp
            (((t * τ b.1 * x b : ℝ) : ℂ) +
              Complex.I * (q b.1 * x b : ℝ)) := by
      rw [← Complex.exp_add]
      rw [show
          ((∑ b : D, t * τ b.1 * x b : ℝ) : ℂ) +
              Complex.I * ((∑ b : D, q b.1 * x b : ℝ) : ℂ) =
            ∑ b : D,
              (((t * τ b.1 * x b : ℝ) : ℂ) +
                Complex.I * (q b.1 * x b : ℝ)) by
          rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]]
      rw [Complex.exp_sum]
    rw [mul_assoc, hexp, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  calc
    _ = ∫ x : D → ℝ, ∏ b : D, f b (x b) := by rw [hfun]
    _ = ∏ b : D, ∫ z : ℝ, f b z := by
      rw [MeasureTheory.integral_fintype_prod_volume_eq_prod]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro b hb
      exact selectedGaussian_tiltCharacteristic β (linkMass s b.1)
        (selectedMean s B y b) t (τ b.1) (q b.1) hβ (hn b.1 b.2)

omit [DecidableEq P] in
/-- Integrability for the selected product characteristic with any real linear tilt. -/
theorem selectedConditionalWeight_character_integrable
    (β t : ℝ) (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (τ q : C → ℝ)
    (hβ : 0 < β) (hn : ∀ b ∈ B, 0 < linkMass s b) :
    Integrable (fun x : {c : C // c ∈ B} → ℝ =>
      (selectedConditionalWeight β s B y x : ℂ) *
        Complex.exp
          ((∑ b : {c : C // c ∈ B}, t * τ b.1 * x b : ℝ) : ℂ) *
        Complex.exp
          (Complex.I * ((∑ b : {c : C // c ∈ B}, q b.1 * x b : ℝ) : ℂ))) := by
  classical
  let D := {c : C // c ∈ B}
  let f : D → ℝ → ℂ := fun b z =>
    (selectedGaussianDensity β (linkMass s b.1)
      (selectedMean s B y b) z : ℂ) *
      Complex.exp (((t * τ b.1 * z : ℝ) : ℂ) +
        Complex.I * (q b.1 * z : ℝ))
  have hfun :
      (fun x : D → ℝ =>
        (selectedConditionalWeight β s B y x : ℂ) *
          Complex.exp
            ((∑ b : D, t * τ b.1 * x b : ℝ) : ℂ) *
          Complex.exp
            (Complex.I * ((∑ b : D, q b.1 * x b : ℝ) : ℂ))) =
      fun x => ∏ b : D, f b (x b) := by
    funext x
    rw [selectedConditionalWeight_eq_prod_density]
    have hexp :
        Complex.exp
            ((∑ b : D, t * τ b.1 * x b : ℝ) : ℂ) *
          Complex.exp
            (Complex.I * ((∑ b : D, q b.1 * x b : ℝ) : ℂ)) =
          ∏ b : D, Complex.exp
            (((t * τ b.1 * x b : ℝ) : ℂ) +
              Complex.I * (q b.1 * x b : ℝ)) := by
      rw [← Complex.exp_add]
      rw [show
          ((∑ b : D, t * τ b.1 * x b : ℝ) : ℂ) +
              Complex.I * ((∑ b : D, q b.1 * x b : ℝ) : ℂ) =
            ∑ b : D,
              (((t * τ b.1 * x b : ℝ) : ℂ) +
                Complex.I * (q b.1 * x b : ℝ)) by
          rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]]
      rw [Complex.exp_sum]
    rw [mul_assoc, hexp, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [hfun, volume_pi]
  exact MeasureTheory.Integrable.fintype_prod (fun b =>
    selectedGaussian_tiltCharacteristic_integrable β (linkMass s b.1)
      (selectedMean s B y b) t (τ b.1) (q b.1) hβ (hn b.1 b.2))

namespace RenormalizedCharacters

open scoped BigOperators

/-- The three modes of the finite cosine expansion: zero, positive and negative. -/
abbrev Sign := Fin 3

/-- Summing a product over all sign assignments is the product of the current-wise mode sums. -/
theorem signAssignments_sum_eq_product {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Sign → ℂ) :
    (∑ σ : I → Sign, ∏ i : I, f i (σ i)) = ∏ i : I, ∑ ε : Sign, f i ε :=
  (Fintype.prod_sum f).symm

def signValue (σ : Sign) : ℝ :=
  if σ.val = 0 then 0 else if σ.val = 1 then 1 else -1

noncomputable def signCoeff (K : ℝ) (σ : Sign) : ℂ :=
  if σ.val = 0 then 1 else (K : ℂ) / 2

noncomputable def charTerm (K u : ℝ) (σ : Sign) : ℂ :=
  signCoeff K σ * Complex.exp (Complex.I * (signValue σ * u))

lemma eulerCosine (u : ℝ) :
    Complex.exp (Complex.I * (u : ℂ)) + Complex.exp (-(Complex.I * (u : ℂ))) =
      2 * (Real.cos u : ℂ) := by
  have hp : Complex.I * (u : ℂ) = (u : ℂ) * Complex.I := by ring
  rw [hp, Complex.exp_mul_I]
  rw [show -((u : ℂ) * Complex.I) = (-u : ℂ) * Complex.I by ring,
    Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring_nf

theorem oneFactorExpansion (K u : ℝ) :
    (1 : ℂ) + (K : ℂ) * (Real.cos u : ℂ) = ∑ σ : Sign, charTerm K u σ := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp [charTerm, signCoeff, signValue]
  rw [← mul_add, eulerCosine]
  rw [← Complex.ofReal_cos]
  ring

theorem familyCosineExpansion {I : Type*} [Fintype I] [DecidableEq I]
    (K : I → ℝ) (u : I → ℝ) :
    ∏ i : I, ((1 : ℂ) + (K i : ℂ) * (Real.cos (u i) : ℂ)) =
      ∑ σ : I → Sign, ∏ i : I, charTerm (K i) (u i) (σ i) := by
  classical
  calc
    ∏ i : I, ((1 : ℂ) + (K i : ℂ) * (Real.cos (u i) : ℂ)) =
        ∏ i : I, ∑ σ : Sign, charTerm (K i) (u i) σ := by
      congr 1
      funext i
      exact oneFactorExpansion (K i) (u i)
    _ = ∑ σ : I → Sign, ∏ i : I, charTerm (K i) (u i) (σ i) :=
      Fintype.prod_sum (fun i σ => charTerm (K i) (u i) σ)

/-- Exponentials turn finite sums into products. -/
lemma exp_finset_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℂ) :
    Complex.exp (∑ a ∈ s, f a) = ∏ a ∈ s, Complex.exp (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Complex.exp_add, ih]

def selectedUnion {I C : Type*} [Fintype I] [DecidableEq C]
    (Bᵢ : I → Finset C) : Finset C := Finset.univ.biUnion Bᵢ

def signedFrequency {I C : Type*} [Fintype I]
    (σ : I → Sign) (ρ : I → C → ℝ) (b : C) : ℝ :=
  ∑ i, signValue (σ i) * ρ i b

def currentSelectedPhase {I C : Type*} [Fintype I] [DecidableEq C]
    (σ : I → Sign) (ρ : I → C → ℝ) (Bᵢ : I → Finset C) (x : C → ℝ) : ℝ :=
  ∑ i, signValue (σ i) * ∑ b ∈ Bᵢ i, ρ i b * x b

def coordinateSelectedPhase {I C : Type*} [Fintype I] [DecidableEq C]
    (σ : I → Sign) (ρ : I → C → ℝ) (Bᵢ : I → Finset C) (x : C → ℝ) : ℝ :=
  ∑ b ∈ selectedUnion Bᵢ, signedFrequency σ ρ b * x b

lemma signedFrequency_eq_owner {I C : Type*} [Fintype I] [DecidableEq I]
    (σ : I → Sign) (ρ : I → C → ℝ) (Bᵢ : I → Finset C)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0)
    (i : I) (b : C) (hb : b ∈ Bᵢ i) :
    signedFrequency σ ρ b = signValue (σ i) * ρ i b := by
  classical
  unfold signedFrequency
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  intro j hj hji
  have hz : ρ j b = 0 := hcross i j b (Ne.symm hji) hb
  simp [hz]

theorem selectedPhase_regrouping {I C : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq C] (σ : I → Sign) (ρ : I → C → ℝ) (Bᵢ : I → Finset C)
    (x : C → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    currentSelectedPhase σ ρ Bᵢ x = coordinateSelectedPhase σ ρ Bᵢ x := by
  classical
  have hpair : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint Bᵢ := by
    apply Finset.pairwiseDisjoint_coe.mp
    rw [Set.pairwiseDisjoint_iff]
    intro i hi j hj hinter
    by_cases hij : i = j
    · exact hij
    · rcases hinter with ⟨b, hb⟩
      have hne := (Finset.disjoint_left.mp (hdisj i j hij)) hb.1
      exact False.elim (hne hb.2)
  unfold currentSelectedPhase coordinateSelectedPhase selectedUnion
  rw [Finset.sum_biUnion hpair]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro b hb
  rw [signedFrequency_eq_owner σ ρ Bᵢ hcross i b hb]
  ring_nf

theorem selectedCharacter_regrouping {I C : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq C] (σ : I → Sign) (ρ : I → C → ℝ) (Bᵢ : I → Finset C)
    (x : C → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    (∏ i, Complex.exp (Complex.I *
      ((signValue (σ i) * ∑ b ∈ Bᵢ i, ρ i b * x b : ℝ) : ℂ))) =
      ∏ b ∈ selectedUnion Bᵢ, Complex.exp (Complex.I *
        ((signedFrequency σ ρ b * x b : ℝ) : ℂ)) := by
  classical
  rw [← exp_finset_sum Finset.univ (fun i => Complex.I *
    ((signValue (σ i) * ∑ b ∈ Bᵢ i, ρ i b * x b : ℝ) : ℂ))]
  rw [← exp_finset_sum (selectedUnion Bᵢ) (fun b => Complex.I *
    ((signedFrequency σ ρ b * x b : ℝ) : ℂ))]
  congr 1
  have hphase := selectedPhase_regrouping σ ρ Bᵢ x hdisj hcross
  unfold currentSelectedPhase coordinateSelectedPhase at hphase
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum]
  rw [hphase]

theorem characterProduct_regrouping {I C : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq C] (K θ : I → ℝ) (ρ : I → C → ℝ) (Bᵢ : I → Finset C)
    (x : C → ℝ) (σ : I → Sign)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    (∏ i, charTerm (K i)
      (θ i + ∑ b ∈ Bᵢ i, ρ i b * x b) (σ i)) =
      (∏ i, signCoeff (K i) (σ i) *
        Complex.exp (Complex.I * ((signValue (σ i) * θ i : ℝ) : ℂ))) *
        ∏ b ∈ selectedUnion Bᵢ, Complex.exp (Complex.I *
          ((signedFrequency σ ρ b * x b : ℝ) : ℂ)) := by
  classical
  unfold charTerm
  rw [Finset.prod_mul_distrib]
  have hsplit :
      (∏ i, Complex.exp (Complex.I *
        ((signValue (σ i) : ℂ) * ((θ i + ∑ b ∈ Bᵢ i, ρ i b * x b) : ℂ)))) =
      (∏ i, Complex.exp (Complex.I * ((signValue (σ i) : ℂ) * (θ i : ℂ)))) *
        ∏ i, Complex.exp (Complex.I *
          ((signValue (σ i) : ℂ) * ((∑ b ∈ Bᵢ i, ρ i b * x b : ℝ) : ℂ))) := by
    calc
      (∏ i, Complex.exp (Complex.I *
          ((signValue (σ i) : ℂ) * ((θ i + ∑ b ∈ Bᵢ i, ρ i b * x b) : ℂ)))) =
          ∏ i, (Complex.exp (Complex.I * ((signValue (σ i) : ℂ) * (θ i : ℂ))) *
            Complex.exp (Complex.I *
              ((signValue (σ i) : ℂ) * ((∑ b ∈ Bᵢ i, ρ i b * x b : ℝ) : ℂ)))) := by
        apply Finset.prod_congr rfl
        intro i hi
        have harg : Complex.I *
            ((signValue (σ i) : ℂ) * ((θ i + ∑ b ∈ Bᵢ i, ρ i b * x b) : ℂ)) =
            Complex.I * ((signValue (σ i) : ℂ) * (θ i : ℂ)) +
              Complex.I * ((signValue (σ i) : ℂ) *
                ((∑ b ∈ Bᵢ i, ρ i b * x b : ℝ) : ℂ)) := by
          push_cast
          ring
        rw [harg, Complex.exp_add]
      _ = (∏ i, Complex.exp (Complex.I * ((signValue (σ i) : ℂ) * (θ i : ℂ)))) *
          ∏ i, Complex.exp (Complex.I *
            ((signValue (σ i) : ℂ) * ((∑ b ∈ Bᵢ i, ρ i b * x b : ℝ) : ℂ))) :=
        Finset.prod_mul_distrib
  have hreg :
      (∏ i, Complex.exp (Complex.I *
        ((signValue (σ i) : ℂ) *
          ((∑ b ∈ Bᵢ i, ρ i b * x b : ℝ) : ℂ)))) =
        ∏ b ∈ selectedUnion Bᵢ, Complex.exp (Complex.I *
          ((signedFrequency σ ρ b : ℂ) * (x b : ℂ))) := by
    simpa only [Complex.ofReal_mul] using
      selectedCharacter_regrouping σ ρ Bᵢ x hdisj hcross
  have hmain :
      (∏ i, signCoeff (K i) (σ i)) *
        ∏ i, Complex.exp (Complex.I *
          ((signValue (σ i) : ℂ) *
            ((θ i : ℂ) + ((∑ b ∈ Bᵢ i, ρ i b * x b : ℝ) : ℂ)))) =
      (∏ i, signCoeff (K i) (σ i) *
        Complex.exp (Complex.I * ((signValue (σ i) : ℂ) * (θ i : ℂ)))) *
        ∏ b ∈ selectedUnion Bᵢ, Complex.exp (Complex.I *
          ((signedFrequency σ ρ b : ℂ) * (x b : ℂ))) := by
    calc
      _ = (∏ i, signCoeff (K i) (σ i)) *
          ((∏ i, Complex.exp (Complex.I * ((signValue (σ i) : ℂ) * (θ i : ℂ)))) *
            ∏ i, Complex.exp (Complex.I *
              ((signValue (σ i) : ℂ) *
                ((∑ b ∈ Bᵢ i, ρ i b * x b : ℝ) : ℂ)))) := by rw [hsplit]
      _ = _ := by
        rw [Finset.prod_mul_distrib, hreg]
        ring
  simpa only [Complex.ofReal_mul, Complex.ofReal_add] using hmain

theorem familyCharacterSum_regrouping {I C : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq C] (K θ : I → ℝ) (ρ : I → C → ℝ) (Bᵢ : I → Finset C)
    (x : C → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    ∏ i, ((1 : ℂ) + (K i : ℂ) *
      (Real.cos (θ i + ∑ b ∈ Bᵢ i, ρ i b * x b) : ℂ)) =
      ∑ σ : I → Sign,
        (∏ i, signCoeff (K i) (σ i) *
          Complex.exp (Complex.I * ((signValue (σ i) * θ i : ℝ) : ℂ))) *
          ∏ b ∈ selectedUnion Bᵢ, Complex.exp (Complex.I *
            ((signedFrequency σ ρ b * x b : ℝ) : ℂ)) := by
  classical
  rw [familyCosineExpansion K (fun i => θ i + ∑ b ∈ Bᵢ i, ρ i b * x b)]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact characterProduct_regrouping K θ ρ Bᵢ x σ hdisj hcross

end RenormalizedCharacters

open RenormalizedCharacters

lemma chartPairing_assemble_split (f : C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (x : {c : C // c ∈ B} → ℝ) :
    chartPairing f (assemble B y x) =
      chartPairing f (retainedField B y) +
        ∑ b : {c : C // c ∈ B}, f b.1 * x b := by
  classical
  unfold chartPairing assemble
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hsel : (∑ c : C, f c * selectedField B x c) =
      ∑ b : {c : C // c ∈ B}, f b.1 * x b := by
    let g : C → ℝ := fun c => if h : c ∈ B then f c * x ⟨c, h⟩ else 0
    have hterm (c : C) : f c * selectedField B x c = g c := by
      by_cases hc : c ∈ B <;> simp [g, selectedField, hc]
    rw [show (∑ c : C, f c * selectedField B x c) = ∑ c : C, g c by
      apply Finset.sum_congr rfl
      intro c _
      exact hterm c]
    have hsubset : (∑ c ∈ B, g c) = ∑ c ∈ (Finset.univ : Finset C), g c :=
      Finset.sum_subset (Finset.subset_univ B) (by
        intro c hc hnot
        simp [g, hnot])
    have huniv : (∑ c : C, g c) = ∑ c ∈ (Finset.univ : Finset C), g c := rfl
    have hsubtype : (∑ c ∈ B, g c) =
        ∑ b : {c : C // c ∈ B}, f b.1 * x b := by
      simpa [g] using (Finset.sum_subtype B (fun _ => Iff.rfl) g)
    rw [huniv, ← hsubset, hsubtype]
  rw [hsel]

omit [DecidableEq P] in
lemma renormalizedFunctional_eq_retained_add_mean (s : P → C → ℝ) (B : Finset C)
    (f : C → ℝ) (y : {c : C // c ∉ B} → ℝ) :
    renormalizedFunctional s B f y =
      chartPairing f (retainedField B y) +
        ∑ b : {c : C // c ∈ B}, f b.1 * selectedMean s B y b := by
  rw [renormalizedFunctional, chartPairing_assemble_split]

omit [Fintype C] in
lemma selectedUnion_eq_B {I : Type*} [Fintype I] [DecidableEq I]
    (B : Finset C) (Bᵢ : I → Finset C)
    (hsub : ∀ i, Bᵢ i ⊆ B) (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i) :
    selectedUnion Bᵢ = B := by
  classical
  ext b
  simp only [selectedUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact hsub i hi
  · exact hcover b

lemma selectedSum_eq_union_sum {I : Type*} [Fintype I] [DecidableEq I]
    (B : Finset C) (Bᵢ : I → Finset C)
    (hsub : ∀ i, Bᵢ i ⊆ B) (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (f : C → ℂ) :
    (∑ b : {c : C // c ∈ B}, f b.1) = ∑ b ∈ selectedUnion Bᵢ, f b := by
  classical
  rw [← selectedUnion_eq_B B Bᵢ hsub hcover]
  exact (Finset.sum_subtype (selectedUnion Bᵢ) (fun _ => Iff.rfl) f).symm

omit [Fintype C] [DecidableEq C] in
lemma current_vanish_outside {I : Type*} [Fintype I] [DecidableEq I]
    (B : Finset C) (Bᵢ : I → Finset C) (ρ : I → C → ℝ)
    (hcover : ∀ b ∈ B, ∃ j, b ∈ Bᵢ j)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0)
    (i : I) {b : C} (hbB : b ∈ B) (hbnot : b ∉ Bᵢ i) :
    ρ i b = 0 := by
  obtain ⟨j, hj⟩ := hcover b hbB
  have hji : j ≠ i := by
    intro h
    subst j
    exact hbnot hj
  exact hcross j i b hji hj

lemma chartPairing_assemble_current_split {I : Type*} [Fintype I] [DecidableEq I]
    (B : Finset C) (Bᵢ : I → Finset C) (ρ : I → C → ℝ)
    (y : {c : C // c ∉ B} → ℝ) (x : {c : C // c ∈ B} → ℝ)
    (hsub : ∀ i, Bᵢ i ⊆ B) (hcover : ∀ b ∈ B, ∃ j, b ∈ Bᵢ j)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) (i : I) :
    chartPairing (ρ i) (assemble B y x) =
      chartPairing (ρ i) (retainedField B y) +
        ∑ b ∈ Bᵢ i, ρ i b * selectedField B x b := by
  classical
  rw [chartPairing_assemble_split]
  have hsubtype : (∑ b : {c : C // c ∈ B}, ρ i b.1 * x b) =
      ∑ b ∈ B, ρ i b * selectedField B x b := by
    symm
    simpa [selectedField] using
      (Finset.sum_subtype B (fun _ => Iff.rfl)
        (fun b => ρ i b * selectedField B x b))
  rw [hsubtype]
  have hsum : (∑ b ∈ Bᵢ i, ρ i b * selectedField B x b) =
      ∑ b ∈ B, ρ i b * selectedField B x b :=
    Finset.sum_subset (hsub i) (by
      intro b hbB hbnot
      rw [current_vanish_outside B Bᵢ ρ hcover hcross i hbB hbnot]
      simp)
  rw [← hsum]

lemma signValue_sq (σ : Sign) :
    signValue σ ^ 2 = if σ.val = 0 then 0 else 1 := by
  unfold signValue
  split_ifs <;> norm_num

lemma signValue_zero_iff (σ : Sign) : signValue σ = 0 ↔ σ.val = 0 := by
  unfold signValue
  split_ifs <;> simp_all

omit [Fintype C] in
lemma sum_signed_weight_regroup {I : Type*} [Fintype I] [DecidableEq I]
    (B : Finset C) (Bᵢ : I → Finset C) (σ : I → Sign) (ρ : I → C → ℝ)
    (f : C → ℝ) (hsub : ∀ i, Bᵢ i ⊆ B)
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    (∑ b ∈ B, signedFrequency σ ρ b * f b) =
      ∑ i, signValue (σ i) * ∑ b ∈ Bᵢ i, ρ i b * f b := by
  have h := selectedPhase_regrouping σ ρ Bᵢ f hdisj hcross
  unfold currentSelectedPhase coordinateSelectedPhase at h
  rw [selectedUnion_eq_B B Bᵢ hsub hcover] at h
  exact h.symm

omit [Fintype C] in
lemma sum_signed_square_regroup {I : Type*} [Fintype I] [DecidableEq I]
    (B : Finset C) (Bᵢ : I → Finset C) (σ : I → Sign) (ρ : I → C → ℝ)
    (g : C → ℝ) (hsub : ∀ i, Bᵢ i ⊆ B)
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    (∑ b ∈ B, (signedFrequency σ ρ b) ^ 2 * g b) =
      ∑ i, (signValue (σ i)) ^ 2 * ∑ b ∈ Bᵢ i, (ρ i b) ^ 2 * g b := by
  classical
  have hpair : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint Bᵢ := by
    apply Finset.pairwiseDisjoint_coe.mp
    rw [Set.pairwiseDisjoint_iff]
    intro i hi j hj hinter
    by_cases hij : i = j
    · exact hij
    · rcases hinter with ⟨b, hb⟩
      have hne := (Finset.disjoint_left.mp (hdisj i j hij)) hb.1
      exact False.elim (hne hb.2)
  rw [← selectedUnion_eq_B B Bᵢ hsub hcover]
  unfold selectedUnion
  rw [Finset.sum_biUnion hpair]
  simp_rw [signValue_sq]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro b hb
  rw [signedFrequency_eq_owner σ ρ Bᵢ hcross i b hb]
  rw [mul_pow, signValue_sq]
  ring

lemma selectedCharacterProduct_eq_exp_sum {I : Type*} [Fintype I] [DecidableEq I]
    (B : Finset C) (Bᵢ : I → Finset C) (σ : I → Sign) (ρ : I → C → ℝ)
    (x : {c : C // c ∈ B} → ℝ) (hsub : ∀ i, Bᵢ i ⊆ B)
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i) :
    (∏ b ∈ selectedUnion Bᵢ, Complex.exp (Complex.I *
      ((signedFrequency σ ρ b * selectedField B x b : ℝ) : ℂ))) =
      Complex.exp (Complex.I *
        ((∑ b : {c : C // c ∈ B}, signedFrequency σ ρ b * x b : ℝ) : ℂ)) := by
  classical
  rw [selectedUnion_eq_B B Bᵢ hsub hcover]
  rw [← exp_finset_sum B (fun b => Complex.I *
    ((signedFrequency σ ρ b * selectedField B x b : ℝ) : ℂ))]
  apply congrArg Complex.exp
  calc
    (∑ b ∈ B, Complex.I *
        ((signedFrequency σ ρ b * selectedField B x b : ℝ) : ℂ)) =
        Complex.I * ∑ b ∈ B,
          ((signedFrequency σ ρ b * selectedField B x b : ℝ) : ℂ) := by
            rw [Finset.mul_sum]
    _ = Complex.I *
        ((∑ b : {c : C // c ∈ B}, signedFrequency σ ρ b * x b : ℝ) : ℂ) := by
          congr 1
          rw [← Complex.ofReal_sum]
          have hs : (∑ b ∈ B,
              signedFrequency σ ρ b * selectedField B x b) =
                ∑ b : {c : C // c ∈ B}, signedFrequency σ ρ b * x b := by
            simpa [selectedField] using
              (Finset.sum_subtype B (fun _ => Iff.rfl)
                (fun b => signedFrequency σ ρ b * selectedField B x b))
          exact_mod_cast hs

omit [DecidableEq P] in
lemma renormalizedFunctional_current_split {I : Type*} [Fintype I] [DecidableEq I]
    (s : P → C → ℝ) (B : Finset C) (Bᵢ : I → Finset C) (ρ : I → C → ℝ)
    (y : {c : C // c ∉ B} → ℝ) (hsub : ∀ i, Bᵢ i ⊆ B)
    (hcover : ∀ b ∈ B, ∃ j, b ∈ Bᵢ j)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) (i : I) :
    renormalizedFunctional s B (ρ i) y =
      chartPairing (ρ i) (retainedField B y) +
        ∑ b ∈ Bᵢ i, ρ i b *
          selectedField B (selectedMean s B y) b := by
  rw [renormalizedFunctional]
  rw [chartPairing_assemble_current_split B Bᵢ ρ y
    (selectedMean s B y) hsub hcover hcross i]

lemma prod_exp_four_sum {D : Type*} [Fintype D]
    (a b c d : D → ℝ) :
    (∏ x : D, (Complex.exp ((a x : ℝ) : ℂ) *
      Complex.exp ((b x : ℝ) : ℂ) *
      Complex.exp (Complex.I * (c x : ℝ)) *
      Complex.exp (Complex.I * (d x : ℝ)))) =
      Complex.exp ((∑ x : D, a x : ℝ) : ℂ) *
      Complex.exp ((∑ x : D, b x : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((∑ x : D, c x : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((∑ x : D, d x : ℝ) : ℂ)) := by
  classical
  simp only [Finset.prod_mul_distrib]
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_sum]
  congr 1 <;> simp only [Complex.ofReal_sum, Finset.mul_sum]

lemma exp_real_fintype_sum {D : Type*} [Fintype D] (f : D → ℝ) :
    Complex.exp ((∑ i : D, f i : ℝ) : ℂ) =
      ∏ i : D, Complex.exp ((f i : ℝ) : ℂ) := by
  rw [← Complex.exp_sum]
  simp only [Complex.ofReal_sum]

lemma exp_im_fintype_sum {D : Type*} [Fintype D] (f : D → ℝ) :
    Complex.exp (Complex.I * ((∑ i : D, f i : ℝ) : ℂ)) =
      ∏ i : D, Complex.exp (Complex.I * (f i : ℝ)) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, ← Complex.ofReal_sum]

lemma signCoeff_damping (β K Q : ℝ) (σ : Sign) :
    signCoeff K σ *
        Complex.exp (((-(β / 2) * (signValue σ) ^ 2 * Q : ℝ) : ℝ) : ℂ) =
      signCoeff (K * Real.exp (-(β / 2) * Q)) σ := by
  fin_cases σ <;> simp [signCoeff, signValue, Complex.ofReal_exp] <;> ring

local instance (priority := 2000) selectedCoordFintypeMode (B : Finset C) :
    Fintype {c : C // c ∈ B} := Subtype.fintype _

omit [DecidableEq P] in
lemma conditionalMode_regroup
    {I : Type*} [Fintype I] [DecidableEq I]
    (β t : ℝ) (s : P → C → ℝ) (B : Finset C)
    (Bᵢ : I → Finset C) (ρ : I → C → ℝ) (K θ : I → ℝ)
    (τ : C → ℝ) (y : {c : C // c ∉ B} → ℝ)
    (_hβ : 0 < β) (_hn : ∀ b ∈ B, 0 < linkMass s b)
    (hsub : ∀ i, Bᵢ i ⊆ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0)
    (σ : I → Sign) :
    (∏ i, signCoeff (K i) (σ i) * Complex.exp (Complex.I *
        ((signValue (σ i) * (θ i + chartPairing (ρ i) (retainedField B y)) : ℝ) : ℂ))) *
      Complex.exp (((t * chartPairing τ (retainedField B y) : ℝ) : ℂ)) *
      ∏ b : {c : C // c ∈ B},
        (Complex.exp ((t * τ b.1 * selectedMean s B y b +
          β * t ^ 2 * τ b.1 ^ 2 / (2 * linkMass s b.1) : ℝ) : ℂ) *
         Complex.exp ((-(β * (signedFrequency σ ρ b.1) ^ 2 /
            (2 * linkMass s b.1)) : ℝ) : ℂ) *
         Complex.exp (Complex.I * (signedFrequency σ ρ b.1 *
            selectedMean s B y b : ℝ)) *
         Complex.exp (Complex.I * (β * t * τ b.1 *
            signedFrequency σ ρ b.1 / linkMass s b.1 : ℝ))) =
      (chartTiltConstant β t s B τ : ℂ) *
        Complex.exp ((t * renormalizedFunctional s B τ y : ℝ) : ℂ) *
        ∏ i, charTerm (renormalizedActivity β (K i) s (Bᵢ i) (ρ i))
          (renormalizedFunctional s B (ρ i) y + θ i +
            chartTiltPhase β t s (Bᵢ i) τ (ρ i)) (σ i) := by
  classical
  let D := {c : C // c ∈ B}
  let μ : D → ℝ := selectedMean s B y
  let q : C → ℝ := signedFrequency σ ρ
  let μfull : C → ℝ := selectedField B μ
  let A : D → ℝ := fun b => t * τ b.1 * μ b +
    β * t ^ 2 * τ b.1 ^ 2 / (2 * linkMass s b.1)
  let E : D → ℝ := fun b => -(β * q b.1 ^ 2 / (2 * linkMass s b.1))
  let M : D → ℝ := fun b => q b.1 * μ b
  let X : D → ℝ := fun b => β * t * τ b.1 * q b.1 / linkMass s b.1
  let V : ℝ := ∑ b : D, τ b.1 ^ 2 / linkMass s b.1
  let U : ℝ := ∑ b : D, τ b.1 * μ b
  have hprod := prod_exp_four_sum A E M X
  have hA : (∑ b : D, A b) = t * U + β * t ^ 2 / 2 * V := by
    dsimp [A, U, V]
    rw [Finset.sum_add_distrib]
    apply congrArg₂ (· + ·)
    · calc
        (∑ b : D, t * τ b.1 * μ b) =
            ∑ b : D, t * (τ b.1 * μ b) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
        _ = t * ∑ b : D, τ b.1 * μ b := (Finset.mul_sum _ _ _).symm
    · calc
        (∑ b : D, β * t ^ 2 * τ b.1 ^ 2 / (2 * linkMass s b.1)) =
            ∑ b : D, (β * t ^ 2 / 2) *
              (τ b.1 ^ 2 / linkMass s b.1) := by
                apply Finset.sum_congr rfl
                intro b hb
                ring
        _ = β * t ^ 2 / 2 *
            ∑ b : D, τ b.1 ^ 2 / linkMass s b.1 :=
              (Finset.mul_sum _ _ _).symm
  have hV : V = ∑ b ∈ B, τ b ^ 2 / linkMass s b := by
    dsimp [V]
    calc
      (∑ b : D, τ b.1 ^ 2 / linkMass s b.1) =
          ∑ b : D, τ b.1 ^ 2 * (linkMass s b.1)⁻¹ := by
            apply Finset.sum_congr rfl
            intro b hb
            ring
      _ = ∑ b ∈ B, τ b ^ 2 * (linkMass s b)⁻¹ := by
            exact (Finset.sum_subtype B (fun _ => Iff.rfl)
              (fun b => τ b ^ 2 * (linkMass s b)⁻¹)).symm
      _ = ∑ b ∈ B, τ b ^ 2 / linkMass s b := by
            apply Finset.sum_congr rfl
            intro b hb
            ring
  have hE : (∑ b : D, E b) =
      ∑ i, (-(β / 2)) * ((signValue (σ i)) ^ 2 *
        ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b) := by
    have hEfactor : (∑ b : D, E b) =
        -(β / 2) * ∑ b : D,
          (signedFrequency σ ρ b.1) ^ 2 / linkMass s b.1 := by
      dsimp [E, q]
      calc
        (∑ b : D, -(β * (signedFrequency σ ρ b.1) ^ 2 /
            (2 * linkMass s b.1))) =
            ∑ b : D, (-(β / 2)) *
              ((signedFrequency σ ρ b.1) ^ 2 / linkMass s b.1) := by
                apply Finset.sum_congr rfl
                intro b hb
                ring
        _ = -(β / 2) * ∑ b : D,
            (signedFrequency σ ρ b.1) ^ 2 / linkMass s b.1 :=
              (Finset.mul_sum _ _ _).symm
    have htype : (∑ b : D,
        (signedFrequency σ ρ b.1) ^ 2 / linkMass s b.1) =
        ∑ b ∈ B, (signedFrequency σ ρ b) ^ 2 * (1 / linkMass s b) := by
      calc
        (∑ b : D, (signedFrequency σ ρ b.1) ^ 2 / linkMass s b.1) =
            ∑ b : D, (signedFrequency σ ρ b.1) ^ 2 *
              (linkMass s b.1)⁻¹ := by
                apply Finset.sum_congr rfl
                intro b hb
                ring
        _ = ∑ b ∈ B, (signedFrequency σ ρ b) ^ 2 *
              (linkMass s b)⁻¹ := by
                exact (Finset.sum_subtype B (fun _ => Iff.rfl)
                  (fun b => (signedFrequency σ ρ b) ^ 2 * (linkMass s b)⁻¹)).symm
        _ = ∑ b ∈ B, (signedFrequency σ ρ b) ^ 2 *
              (1 / linkMass s b) := by
                apply Finset.sum_congr rfl
                intro b hb
                ring
    have hSqDiv : (∑ b ∈ B,
        (signedFrequency σ ρ b) ^ 2 / linkMass s b) =
        ∑ i, (signValue (σ i)) ^ 2 *
          ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b := by
      calc
        (∑ b ∈ B, (signedFrequency σ ρ b) ^ 2 / linkMass s b) =
            ∑ b ∈ B, (signedFrequency σ ρ b) ^ 2 *
              (1 / linkMass s b) := by
                apply Finset.sum_congr rfl
                intro b hb
                ring
        _ = ∑ i, (signValue (σ i)) ^ 2 *
              ∑ b ∈ Bᵢ i, ρ i b ^ 2 * (1 / linkMass s b) :=
                sum_signed_square_regroup B Bᵢ σ ρ
                  (fun b => 1 / linkMass s b) hsub hcover hdisj hcross
        _ = ∑ i, (signValue (σ i)) ^ 2 *
              ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b := by
                apply Finset.sum_congr rfl
                intro i hi
                congr 1
                apply Finset.sum_congr rfl
                intro b hb
                ring
    calc
      (∑ b : D, E b) =
          -(β / 2) * ∑ b ∈ B,
            (signedFrequency σ ρ b) ^ 2 / linkMass s b := by
              rw [hEfactor, htype]
              apply congrArg (fun r : ℝ => -(β / 2) * r)
              apply Finset.sum_congr rfl
              intro b hb
              ring
      _ = ∑ i, (-(β / 2)) * ((signValue (σ i)) ^ 2 *
            ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b) := by
              rw [hSqDiv]
              exact Finset.mul_sum _ _ _
  have hMeanType : (∑ b : D, q b.1 * μ b) =
      ∑ b ∈ B, q b * μfull b := by
    simpa [μfull, selectedField, μ] using
      (Finset.sum_subtype B (fun _ => Iff.rfl)
        (fun b => q b * μfull b)).symm
  have hMean := hMeanType.trans (sum_signed_weight_regroup B Bᵢ σ ρ
    μfull hsub hcover hdisj hcross)
  have hCrossType : (∑ b : D,
      τ b.1 * q b.1 / linkMass s b.1) =
        ∑ b ∈ B, q b * (τ b / linkMass s b) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Finset.sum_subtype B (fun _ => Iff.rfl)
        (fun b => q b * (τ b / linkMass s b))).symm
  have hCross := hCrossType.trans (sum_signed_weight_regroup B Bᵢ σ ρ
    (fun b => τ b / linkMass s b) hsub hcover hdisj hcross)
  have hX : (∑ b : D, X b) =
      ∑ i, β * t * signValue (σ i) *
        ∑ b ∈ Bᵢ i, ρ i b * (τ b / linkMass s b) := by
    dsimp [X]
    rw [show (∑ b : D,
      β * t * τ b.1 * q b.1 / linkMass s b.1) =
      β * t * ∑ b : D, τ b.1 * q b.1 / linkMass s b.1 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring]
    rw [hCross]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hphase (i : I) :
      Complex.exp (Complex.I *
          ((signValue (σ i) * (θ i + chartPairing (ρ i) (retainedField B y)) : ℝ) : ℂ)) *
        Complex.exp (Complex.I *
          ((signValue (σ i) *
            ∑ b ∈ Bᵢ i, ρ i b * μfull b : ℝ) : ℂ)) *
        Complex.exp (Complex.I *
          ((β * t * signValue (σ i) *
            ∑ b ∈ Bᵢ i, ρ i b * (τ b / linkMass s b) : ℝ) : ℂ)) =
      Complex.exp (Complex.I *
        ((signValue (σ i) *
          (renormalizedFunctional s B (ρ i) y + θ i +
            chartTiltPhase β t s (Bᵢ i) τ (ρ i)) : ℝ) : ℂ)) := by
    have hren := renormalizedFunctional_current_split s B Bᵢ ρ y
      hsub hcover hcross i
    have hcov : selectedCovariancePairing s (Bᵢ i) τ (ρ i) =
        ∑ b ∈ Bᵢ i, ρ i b * (τ b / linkMass s b) := by
      unfold selectedCovariancePairing
      apply Finset.sum_congr rfl
      intro b hb
      ring
    dsimp [μfull, μ] at *
    unfold chartTiltPhase
    rw [hren, hcov]
    rw [← Complex.exp_add, ← Complex.exp_add]
    apply congrArg Complex.exp
    push_cast
    ring
  have hbase :
      Complex.exp (((t * chartPairing τ (retainedField B y) : ℝ) : ℂ)) *
        Complex.exp ((∑ b : D, A b : ℝ) : ℂ) =
      (chartTiltConstant β t s B τ : ℂ) *
        Complex.exp ((t * renormalizedFunctional s B τ y : ℝ) : ℂ) := by
    rw [hA, hV]
    simp only [chartTiltConstant, Complex.ofReal_exp]
    calc
      Complex.exp ((t * chartPairing τ (retainedField B y) : ℝ) : ℂ) *
          Complex.exp ((t * U + β * t ^ 2 / 2 *
            (∑ b ∈ B, τ b ^ 2 / linkMass s b) : ℝ) : ℂ) =
        Complex.exp ((t * chartPairing τ (retainedField B y) +
          (t * U + β * t ^ 2 / 2 *
            (∑ b ∈ B, τ b ^ 2 / linkMass s b)) : ℝ) : ℂ) := by
              rw [← Complex.exp_add]
              apply congrArg Complex.exp
              push_cast
              ring
      _ = Complex.exp ((β * t ^ 2 / 2 *
            (∑ b ∈ B, τ b ^ 2 / linkMass s b) +
          t * renormalizedFunctional s B τ y : ℝ) : ℂ) := by
              apply congrArg Complex.exp
              rw [renormalizedFunctional_eq_retained_add_mean]
              dsimp [U, μ]
              push_cast
              ring_nf
              ring
      _ = Complex.exp ((β * t ^ 2 / 2 *
            (∑ b ∈ B, τ b ^ 2 / linkMass s b) : ℝ) : ℂ) *
          Complex.exp ((t * renormalizedFunctional s B τ y : ℝ) : ℂ) :=
            by rw [Complex.ofReal_add]; exact Complex.exp_add _ _
  have hcombine :
      (∏ i, signCoeff (K i) (σ i) * Complex.exp (Complex.I *
          ((signValue (σ i) *
            (θ i + chartPairing (ρ i) (retainedField B y)) : ℝ) : ℂ))) *
        Complex.exp (((t * chartPairing τ (retainedField B y) : ℝ) : ℂ)) *
        (Complex.exp ((∑ b : D, A b : ℝ) : ℂ) *
          Complex.exp ((∑ i, (-(β / 2)) * ((signValue (σ i)) ^ 2 *
            ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((∑ i, signValue (σ i) *
            ∑ b ∈ Bᵢ i, ρ i b * μfull b : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((∑ i, β * t * signValue (σ i) *
            ∑ b ∈ Bᵢ i, ρ i b * (τ b / linkMass s b) : ℝ) : ℂ))) =
        (chartTiltConstant β t s B τ : ℂ) *
          Complex.exp ((t * renormalizedFunctional s B τ y : ℝ) : ℂ) *
          ((∏ i, signCoeff (K i) (σ i) * Complex.exp (Complex.I *
              ((signValue (σ i) *
                (θ i + chartPairing (ρ i) (retainedField B y)) : ℝ) : ℂ))) *
            Complex.exp ((∑ i, (-(β / 2)) * ((signValue (σ i)) ^ 2 *
              ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((∑ i, signValue (σ i) *
              ∑ b ∈ Bᵢ i, ρ i b * μfull b : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((∑ i, β * t * signValue (σ i) *
              ∑ b ∈ Bᵢ i, ρ i b * (τ b / linkMass s b) : ℝ) : ℂ))) := by
    calc
      _ = ((∏ i, signCoeff (K i) (σ i) * Complex.exp (Complex.I *
              ((signValue (σ i) *
                (θ i + chartPairing (ρ i) (retainedField B y)) : ℝ) : ℂ))) *
            (Complex.exp (((t * chartPairing τ (retainedField B y) : ℝ) : ℂ)) *
              Complex.exp ((∑ b : D, A b : ℝ) : ℂ))) *
          (Complex.exp ((∑ i, (-(β / 2)) * ((signValue (σ i)) ^ 2 *
              ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((∑ i, signValue (σ i) *
              ∑ b ∈ Bᵢ i, ρ i b * μfull b : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((∑ i, β * t * signValue (σ i) *
              ∑ b ∈ Bᵢ i, ρ i b * (τ b / linkMass s b) : ℝ) : ℂ))) := by ring
      _ = ((∏ i, signCoeff (K i) (σ i) * Complex.exp (Complex.I *
              ((signValue (σ i) *
                (θ i + chartPairing (ρ i) (retainedField B y)) : ℝ) : ℂ))) *
            ((chartTiltConstant β t s B τ : ℂ) *
              Complex.exp ((t * renormalizedFunctional s B τ y : ℝ) : ℂ))) *
          (Complex.exp ((∑ i, (-(β / 2)) * ((signValue (σ i)) ^ 2 *
              ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((∑ i, signValue (σ i) *
              ∑ b ∈ Bᵢ i, ρ i b * μfull b : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((∑ i, β * t * signValue (σ i) *
              ∑ b ∈ Bᵢ i, ρ i b * (τ b / linkMass s b) : ℝ) : ℂ))) := by
                rw [hbase]
      _ = _ := by ring
  have hmodeSum :
      (∏ i, signCoeff (K i) (σ i) * Complex.exp (Complex.I *
          ((signValue (σ i) *
            (θ i + chartPairing (ρ i) (retainedField B y)) : ℝ) : ℂ))) *
        (∏ i, Complex.exp (((-(β / 2)) * ((signValue (σ i)) ^ 2 *
          ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b : ℝ) : ℂ))) *
        (∏ i, Complex.exp (Complex.I * ((signValue (σ i) *
          ∑ b ∈ Bᵢ i, ρ i b * μfull b : ℝ) : ℂ))) *
        (∏ i, Complex.exp (Complex.I * ((β * t * signValue (σ i) *
          ∑ b ∈ Bᵢ i, ρ i b * (τ b / linkMass s b) : ℝ) : ℂ))) =
      ∏ i, charTerm (renormalizedActivity β (K i) s (Bᵢ i) (ρ i))
        (renormalizedFunctional s B (ρ i) y + θ i +
          chartTiltPhase β t s (Bᵢ i) τ (ρ i)) (σ i) := by
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [charTerm]
    calc
      _ = (signCoeff (K i) (σ i) *
            Complex.exp (((-(β / 2)) * ((signValue (σ i)) ^ 2 *
              ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b : ℝ) : ℂ))) *
          (Complex.exp (Complex.I * ((signValue (σ i) *
              (θ i + chartPairing (ρ i) (retainedField B y)) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((signValue (σ i) *
              ∑ b ∈ Bᵢ i, ρ i b * μfull b : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((β * t * signValue (σ i) *
              ∑ b ∈ Bᵢ i, ρ i b * (τ b / linkMass s b) : ℝ) : ℂ))) := by
                ac_rfl
      _ = signCoeff (renormalizedActivity β (K i) s (Bᵢ i) (ρ i)) (σ i) *
          Complex.exp (Complex.I * ((signValue (σ i) *
            (renormalizedFunctional s B (ρ i) y + θ i +
              chartTiltPhase β t s (Bᵢ i) τ (ρ i)) : ℝ) : ℂ)) := by
            have hdamp : signCoeff (K i) (σ i) *
                Complex.exp (((-(β / 2) * (signValue (σ i)) ^ 2 *
                  ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b : ℝ) : ℂ)) =
              signCoeff (renormalizedActivity β (K i) s (Bᵢ i) (ρ i)) (σ i) := by
                convert (signCoeff_damping β (K i)
                  (∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b) (σ i)) using 1
                all_goals simp [renormalizedActivity]
            have hExp : Complex.exp
                ((-(β : ℂ) / 2) *
                  ((signValue (σ i)) ^ 2 *
                    ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b : ℝ) : ℂ) =
                Complex.exp (((-(β / 2) * (signValue (σ i)) ^ 2 *
                  ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b : ℝ) : ℝ) : ℂ) := by
                  congr 1
                  push_cast
                  ring_nf
            have hExpSign : Complex.exp
                (-((β : ℂ) / 2) *
                  ((signValue (σ i)) ^ 2 *
                    ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b : ℝ) : ℂ) =
                Complex.exp
                (((-(β : ℂ)) / 2) *
                  ((signValue (σ i)) ^ 2 *
                    ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b : ℝ) : ℂ) := by
                  congr 1
                  ring
            rw [hExpSign, hExp, hdamp]
            rw [hphase i]
      _ = charTerm (renormalizedActivity β (K i) s (Bᵢ i) (ρ i))
          (renormalizedFunctional s B (ρ i) y + θ i +
            chartTiltPhase β t s (Bᵢ i) τ (ρ i)) (σ i) := by
              rw [charTerm]
              apply congrArg (fun z : ℂ =>
                signCoeff (renormalizedActivity β (K i) s (Bᵢ i) (ρ i)) (σ i) *
                  Complex.exp (Complex.I * z))
              exact Complex.ofReal_mul _ _
  rw [hprod, hE, hMean, hX, hcombine]
  rw [exp_real_fintype_sum, exp_im_fintype_sum, exp_im_fintype_sum]
  have hmodeDamp (i : I) :
      Complex.exp (-((β : ℂ) / 2) *
        Complex.ofReal ((signValue (σ i)) ^ 2 *
          ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b)) =
      Complex.exp (Complex.ofReal (-(β / 2) * ((signValue (σ i)) ^ 2 *
          ∑ b ∈ Bᵢ i, ρ i b ^ 2 / linkMass s b))) := by
    congr 1
    push_cast
    ring_nf
  simp_rw [hmodeDamp] at hmodeSum
  rw [hmodeSum]


omit [DecidableEq P] in
/-- The selected-coordinate family identity in complex form, at fixed retained coordinates. -/
theorem conditionalFamilyIdentity_complex
    {I : Type*} [Fintype I] [DecidableEq I]
    (β t : ℝ) (s : P → C → ℝ) (B : Finset C)
    (Bᵢ : I → Finset C) (ρ : I → C → ℝ) (K θ : I → ℝ)
    (τ : C → ℝ) (y : {c : C // c ∉ B} → ℝ)
    (hβ : 0 < β)
    (_hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b)
    (hsub : ∀ i, Bᵢ i ⊆ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    (∫ x : {c : C // c ∈ B} → ℝ,
      (selectedConditionalWeight β s B y x : ℂ) *
        Complex.exp ((t * chartPairing τ (assemble B y x) : ℝ) : ℂ) *
        ∏ i, ((1 : ℂ) + (K i : ℂ) *
          (Real.cos (chartPairing (ρ i) (assemble B y x) + θ i) : ℂ))) =
      (chartTiltConstant β t s B τ : ℂ) *
        Complex.exp ((t * renormalizedFunctional s B τ y : ℝ) : ℂ) *
        ∏ i, ((1 : ℂ) +
          (renormalizedActivity β (K i) s (Bᵢ i) (ρ i) : ℂ) *
          (Real.cos (renormalizedFunctional s B (ρ i) y + θ i +
            chartTiltPhase β t s (Bᵢ i) τ (ρ i)) : ℂ)) := by
  classical
  let D := {c : C // c ∈ B}
  let thetaRet : I → ℝ := fun i => θ i + chartPairing (ρ i) (retainedField B y)
  let modeCoeff : (I → Sign) → ℂ := fun σ =>
    ∏ i, signCoeff (K i) (σ i) * Complex.exp (Complex.I *
      ((signValue (σ i) * thetaRet i : ℝ) : ℂ))
  let selectedTilt (x : D → ℝ) : ℂ :=
    Complex.exp ((∑ b : D, t * τ b.1 * x b : ℝ) : ℂ)
  let selectedChar (σ : I → Sign) (x : D → ℝ) : ℂ :=
    Complex.exp (Complex.I *
      ((∑ b : D, signedFrequency σ ρ b.1 * x b : ℝ) : ℂ))
  let mode (σ : I → Sign) (x : D → ℝ) : ℂ :=
    modeCoeff σ * Complex.exp ((t * chartPairing τ (retainedField B y) : ℝ) : ℂ) *
      ((selectedConditionalWeight β s B y x : ℂ) * selectedTilt x *
        selectedChar σ x)
  have harg (x : D → ℝ) (i : I) :
      chartPairing (ρ i) (assemble B y x) + θ i =
        thetaRet i + ∑ b ∈ Bᵢ i, ρ i b * selectedField B x b := by
    rw [chartPairing_assemble_current_split B Bᵢ ρ y x
      hsub hcover hcross i]
    dsimp [thetaRet]
    ring
  have hcos (x : D → ℝ) :
      (∏ i, ((1 : ℂ) + (K i : ℂ) *
        (Real.cos (chartPairing (ρ i) (assemble B y x) + θ i) : ℂ))) =
      ∑ σ : I → Sign, modeCoeff σ * Complex.exp (Complex.I *
        ((∑ b : D, signedFrequency σ ρ b.1 * x b : ℝ) : ℂ)) := by
    have hselected := familyCharacterSum_regrouping K thetaRet ρ Bᵢ
      (selectedField B x) hdisj hcross
    calc
      _ = ∏ i, ((1 : ℂ) + (K i : ℂ) *
          (Real.cos (thetaRet i + ∑ b ∈ Bᵢ i,
            ρ i b * selectedField B x b) : ℂ)) := by
              apply Finset.prod_congr rfl
              intro i hi
              apply congrArg (fun z : ℝ => (1 : ℂ) + (K i : ℂ) *
                (Real.cos z : ℂ))
              exact harg x i
      _ = ∑ σ : I → Sign,
          (∏ i, signCoeff (K i) (σ i) * Complex.exp (Complex.I *
            ((signValue (σ i) * thetaRet i : ℝ) : ℂ))) *
            ∏ b ∈ selectedUnion Bᵢ, Complex.exp (Complex.I *
              ((signedFrequency σ ρ b * selectedField B x b : ℝ) : ℂ)) := by
                simpa [modeCoeff] using hselected
      _ = _ := by
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [selectedCharacterProduct_eq_exp_sum B Bᵢ σ ρ x hsub hcover]
  have htilt (x : D → ℝ) :
      Complex.exp ((t * chartPairing τ (assemble B y x) : ℝ) : ℂ) =
        Complex.exp ((t * chartPairing τ (retainedField B y) : ℝ) : ℂ) *
          selectedTilt x := by
    have hreal : t * chartPairing τ (assemble B y x) =
        t * chartPairing τ (retainedField B y) +
          ∑ b : D, t * τ b.1 * x b := by
      calc
        _ = t * (chartPairing τ (retainedField B y) +
            ∑ b : D, τ b.1 * x b) := by rw [chartPairing_assemble_split]
        _ = _ := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro b hb
          ring
    rw [congrArg (fun r : ℝ => Complex.exp (r : ℂ)) hreal]
    rw [Complex.ofReal_add, Complex.exp_add]
  have hpoint (x : D → ℝ) :
      (selectedConditionalWeight β s B y x : ℂ) *
        Complex.exp ((t * chartPairing τ (assemble B y x) : ℝ) : ℂ) *
        ∏ i, ((1 : ℂ) + (K i : ℂ) *
          (Real.cos (chartPairing (ρ i) (assemble B y x) + θ i) : ℂ)) =
      ∑ σ : I → Sign, mode σ x := by
    rw [hcos x, htilt x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    dsimp [mode, selectedTilt, selectedChar]
    ring
  have hcharacterInt (σ : I → Sign) :
      Integrable (fun x : D → ℝ =>
        (selectedConditionalWeight β s B y x : ℂ) *
          selectedTilt x * selectedChar σ x) := by
    simpa [selectedTilt, selectedChar] using
      selectedConditionalWeight_character_integrable β t s B y τ
        (signedFrequency σ ρ) hβ hn
  have hmodeInt (σ : I → Sign) : Integrable (fun x : D → ℝ => mode σ x) := by
    simpa [mode, mul_assoc] using
      (hcharacterInt σ).const_mul
        (modeCoeff σ * Complex.exp ((t * chartPairing τ (retainedField B y) : ℝ) : ℂ))
  have hmodesInt : Integrable (fun x : D → ℝ => ∑ σ : I → Sign, mode σ x) := by
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro σ hσ
    exact hmodeInt σ
  calc
    (∫ x : D → ℝ,
        (selectedConditionalWeight β s B y x : ℂ) *
          Complex.exp ((t * chartPairing τ (assemble B y x) : ℝ) : ℂ) *
          ∏ i, ((1 : ℂ) + (K i : ℂ) *
            (Real.cos (chartPairing (ρ i) (assemble B y x) + θ i) : ℂ))) =
        ∫ x : D → ℝ, ∑ σ : I → Sign, mode σ x := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hpoint x
    _ = ∑ σ : I → Sign, ∫ x : D → ℝ, mode σ x := by
          exact MeasureTheory.integral_finsetSum Finset.univ
            (fun σ hσ => hmodeInt σ)
    _ = ∑ σ : I → Sign,
          (chartTiltConstant β t s B τ : ℂ) *
            Complex.exp ((t * renormalizedFunctional s B τ y : ℝ) : ℂ) *
            ∏ i, charTerm (renormalizedActivity β (K i) s (Bᵢ i) (ρ i))
              (renormalizedFunctional s B (ρ i) y + θ i +
                chartTiltPhase β t s (Bᵢ i) τ (ρ i)) (σ i) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          dsimp [mode]
          rw [integral_const_mul]
          rw [selectedConditionalWeight_integral_character β t s B y τ
            (signedFrequency σ ρ) hβ hn]
          exact conditionalMode_regroup β t s B Bᵢ ρ K θ τ y hβ hn
            hsub hdisj hcover hcross σ
    _ = ((chartTiltConstant β t s B τ : ℂ) *
          Complex.exp ((t * renormalizedFunctional s B τ y : ℝ) : ℂ)) *
          ∏ i, ((1 : ℂ) +
            (renormalizedActivity β (K i) s (Bᵢ i) (ρ i) : ℂ) *
            (Real.cos (renormalizedFunctional s B (ρ i) y + θ i +
              chartTiltPhase β t s (Bᵢ i) τ (ρ i)) : ℂ)) := by
          rw [← Finset.mul_sum]
          rw [← familyCosineExpansion
            (fun i => renormalizedActivity β (K i) s (Bᵢ i) (ρ i))
            (fun i => renormalizedFunctional s B (ρ i) y + θ i +
              chartTiltPhase β t s (Bᵢ i) τ (ρ i))]

omit [DecidableEq P] in
/-- The real fixed-retained-coordinate family identity. -/
theorem conditionalFamilyIdentity
    {I : Type*} [Fintype I] [DecidableEq I]
    (β t : ℝ) (s : P → C → ℝ) (B : Finset C)
    (Bᵢ : I → Finset C) (ρ : I → C → ℝ) (K θ : I → ℝ)
    (τ : C → ℝ) (y : {c : C // c ∉ B} → ℝ)
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b)
    (hsub : ∀ i, Bᵢ i ⊆ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    (∫ x : {c : C // c ∈ B} → ℝ,
      selectedConditionalWeight β s B y x *
        (Real.exp (t * chartPairing τ (assemble B y x)) *
          ∏ i, (1 + K i * Real.cos
            (chartPairing (ρ i) (assemble B y x) + θ i)))) =
      chartTiltConstant β t s B τ *
        Real.exp (t * renormalizedFunctional s B τ y) *
        ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
          Real.cos (renormalizedFunctional s B (ρ i) y + θ i +
            chartTiltPhase β t s (Bᵢ i) τ (ρ i))) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  convert conditionalFamilyIdentity_complex β t s B Bᵢ ρ K θ τ y
    hβ hsep hn hsub hdisj hcover hcross using 1
  all_goals simp [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_exp,
    Complex.ofReal_cos]
  all_goals
    try
      apply integral_congr_ae
      filter_upwards [] with x
      ring

omit [DecidableEq P] in
/-- Integration against the literal retained marginal density. -/
theorem reducedMeasure_integral_eq (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (F : ({c : C // c ∉ B} → ℝ) → ℝ) :
    (∫ y, F y ∂reducedMeasure β s B) =
      ∫ y, reducedWeight β s B y * F y := by
  classical
  have hretained :
      Measurable (fun y : {c : C // c ∉ B} → ℝ => retainedField B y) := by
    apply measurable_pi_iff.2
    intro c
    by_cases hc : c ∈ B
    · simp [retainedField, hc]
    · simpa [retainedField, hc] using
        (measurable_pi_apply (⟨c, hc⟩ : {c : C // c ∉ B}))
  have hOffset (b : C) :
      Measurable (fun y : {c : C // c ∉ B} → ℝ => linkOffset s B y b) := by
    unfold linkOffset
    fun_prop [FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlField]
  rw [reducedMeasure, integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards [] with y
    change (ENNReal.ofReal (reducedWeight β s B y)).toReal * F y = _
    have hnonneg : 0 ≤ reducedWeight β s B y := by
      unfold reducedWeight
      apply mul_nonneg
      · positivity
      · apply Finset.prod_nonneg
        intro b hb
        exact Real.sqrt_nonneg _
    rw [ENNReal.toReal_ofReal hnonneg]
  · fun_prop [reducedWeight, reducedEnergy, linkMass,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlField]
  · filter_upwards [] with y
    exact ENNReal.ofReal_lt_top

omit [DecidableEq P] in
/-- The one-link renormalization boxed identity for the literal unnormalized chart measure. The explicit integrability
premise is the finite-mass gate for the chart Gaussian. -/
theorem chartFamilyIdentity
    {I : Type*} [Fintype I] [DecidableEq I]
    (β t : ℝ) (s : P → C → ℝ) (B : Finset C)
    (Bᵢ : I → Finset C) (ρ : I → C → ℝ) (K θ : I → ℝ)
    (τ : C → ℝ)
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b)
    (hsub : ∀ i, Bᵢ i ⊆ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0)
    (hF : Integrable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        chartWeight β s (assemble B z.1 z.2) *
          (Real.exp (t * chartPairing τ (assemble B z.1 z.2)) *
            ∏ i, (1 + K i * Real.cos
              (chartPairing (ρ i) (assemble B z.1 z.2) + θ i))))
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ))))) :
    (∫ x : C → ℝ,
      Real.exp (t * chartPairing τ x) *
        ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) x + θ i))
      ∂chartMeasure β s) =
      chartTiltConstant β t s B τ *
        (∫ y : {c : C // c ∉ B} → ℝ,
          Real.exp (t * renormalizedFunctional s B τ y) *
            ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
              Real.cos (renormalizedFunctional s B (ρ i) y + θ i +
                chartTiltPhase β t s (Bᵢ i) τ (ρ i)))
          ∂reducedMeasure β s B) := by
  classical
  let F : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) → ℝ := fun z =>
    Real.exp (t * chartPairing τ (assemble B z.1 z.2)) *
      ∏ i, (1 + K i * Real.cos
        (chartPairing (ρ i) (assemble B z.1 z.2) + θ i))
  have hchart (x : C → ℝ) :
      assemble B ((chartSplitEquiv B x).1) ((chartSplitEquiv B x).2) = x := by
    rw [← chartSplitEquiv_symm_apply B ((chartSplitEquiv B x).1)
      ((chartSplitEquiv B x).2)]
    exact MeasurableEquiv.symm_apply_apply (chartSplitEquiv B) x
  calc
    _ = ∫ x : C → ℝ, F (chartSplitEquiv B x) ∂chartMeasure β s := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [F]
          rw [hchart x]
    _ = ∫ y : {c : C // c ∉ B} → ℝ,
          reducedWeight β s B y *
            (∫ x : {c : C // c ∈ B} → ℝ,
              selectedConditionalWeight β s B y x * F (y, x)
              ∂Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))
          ∂Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ)) := by
          exact chartMeasure_fubini β s B F hF hβ hsep hn
    _ = ∫ y : {c : C // c ∉ B} → ℝ,
          reducedWeight β s B y *
            (chartTiltConstant β t s B τ *
              (Real.exp (t * renormalizedFunctional s B τ y) *
                ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
                  Real.cos (renormalizedFunctional s B (ρ i) y + θ i +
                    chartTiltPhase β t s (Bᵢ i) τ (ρ i)))))
          ∂Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ)) := by
          apply integral_congr_ae
          filter_upwards [] with y
          dsimp [F]
          have hid := conditionalFamilyIdentity β t s B Bᵢ ρ K θ τ y
            hβ hsep hn hsub hdisj hcover hcross
          rw [volume_pi] at hid
          calc
            _ = reducedWeight β s B y *
                (chartTiltConstant β t s B τ *
                  Real.exp (t * renormalizedFunctional s B τ y) *
                  ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
                    Real.cos (renormalizedFunctional s B (ρ i) y + θ i +
                      chartTiltPhase β t s (Bᵢ i) τ (ρ i)))) :=
              congrArg (fun r : ℝ => reducedWeight β s B y * r) hid
            _ = reducedWeight β s B y *
                (chartTiltConstant β t s B τ *
                  (Real.exp (t * renormalizedFunctional s B τ y) *
                    ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
                      Real.cos (renormalizedFunctional s B (ρ i) y + θ i +
                        chartTiltPhase β t s (Bᵢ i) τ (ρ i))))) := by ring
    _ = chartTiltConstant β t s B τ *
          (∫ y : {c : C // c ∉ B} → ℝ,
            Real.exp (t * renormalizedFunctional s B τ y) *
              ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
                Real.cos (renormalizedFunctional s B (ρ i) y + θ i +
                  chartTiltPhase β t s (Bᵢ i) τ (ρ i)))
            ∂reducedMeasure β s B) := by
          rw [reducedMeasure_integral_eq β s B]
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with y
          ring

/-- The total mass of the literal chart density. -/
noncomputable def chartPartitionFunction (β : ℝ) (s : P → C → ℝ) : ℝ :=
  ∫ x : C → ℝ, chartWeight β s x

omit [DecidableEq P] in
/-- Integrating the chart density and the retained marginal gives the same partition function.
The integrability hypothesis is explicit because the selected-block hypotheses alone do not
control null directions among the retained coordinates. -/
theorem chartPartitionFunction_eq_reducedMeasure_mass
    (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (hWeight : Integrable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        chartWeight β s (assemble B z.1 z.2))
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))))
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b) :
    chartPartitionFunction β s = ∫ _, 1 ∂reducedMeasure β s B := by
  classical
  have hFubini := chartMeasure_fubini β s B (fun _ => (1 : ℝ)) (by simpa using hWeight)
    hβ hsep hn
  have hConditional (y : {c : C // c ∉ B} → ℝ) :
      (∫ x : {c : C // c ∈ B} → ℝ,
        selectedConditionalWeight β s B y x
        ∂Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ))) = 1 := by
    simpa only [volume_pi] using selectedConditionalWeight_integral β B s y hβ hn
  have hMass :
      (∫ x : C → ℝ, (1 : ℝ) ∂chartMeasure β s) =
        ∫ y : {c : C // c ∉ B} → ℝ, reducedWeight β s B y := by
    calc
      _ = ∫ y : {c : C // c ∉ B} → ℝ,
            reducedWeight β s B y *
              (∫ x : {c : C // c ∈ B} → ℝ,
                selectedConditionalWeight β s B y x * 1
                ∂Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ))) := hFubini
      _ = ∫ y : {c : C // c ∉ B} → ℝ, reducedWeight β s B y := by
            apply integral_congr_ae
            filter_upwards [] with y
            rw [integral_mul_const, mul_one, hConditional y, mul_one]
  calc
    chartPartitionFunction β s = ∫ x : C → ℝ, (1 : ℝ) ∂chartMeasure β s := by
      rw [chartPartitionFunction, chartMeasure_integral_eq β s (fun _ => (1 : ℝ))]
      simp
    _ = ∫ y : {c : C // c ∉ B} → ℝ, reducedWeight β s B y := hMass
    _ = ∫ y, 1 ∂reducedMeasure β s B := by
      rw [reducedMeasure_integral_eq β s B]
      simp

omit [DecidableEq P] in
/--
The full family identity after dividing both chart integrals by their common finite-volume
partition function.

The preceding mass theorem identifies this denominator with the retained
marginal's mass; separately identifies the normalized chart law with the source quotient law.
-/
theorem chartFamilyIdentity_normalized
    {I : Type*} [Fintype I] [DecidableEq I]
    (β t : ℝ) (s : P → C → ℝ) (B : Finset C)
    (Bᵢ : I → Finset C) (ρ : I → C → ℝ) (K θ : I → ℝ)
    (τ : C → ℝ)
    (hF : Integrable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        chartWeight β s (assemble B z.1 z.2) *
          (Real.exp (t * chartPairing τ (assemble B z.1 z.2)) *
            ∏ i, (1 + K i * Real.cos
              (chartPairing (ρ i) (assemble B z.1 z.2) + θ i))))
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))))
    (hWeight : Integrable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        chartWeight β s (assemble B z.1 z.2))
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))))
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b)
    (hsub : ∀ i, Bᵢ i ⊆ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0)
    (hZ : 0 < chartPartitionFunction β s) :
    (∫ x : C → ℝ,
      Real.exp (t * chartPairing τ x) *
        ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) x + θ i))
      ∂chartMeasure β s) / chartPartitionFunction β s =
      chartTiltConstant β t s B τ *
        ((∫ y : {c : C // c ∉ B} → ℝ,
          Real.exp (t * renormalizedFunctional s B τ y) *
            ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
              Real.cos (renormalizedFunctional s B (ρ i) y + θ i +
                chartTiltPhase β t s (Bᵢ i) τ (ρ i)))
          ∂reducedMeasure β s B) / chartPartitionFunction β s) := by
  have _hMass := chartPartitionFunction_eq_reducedMeasure_mass β s B hWeight hβ hsep hn
  have hidentity := chartFamilyIdentity β t s B Bᵢ ρ K θ τ hβ hsep hn
    hsub hdisj hcover hcross hF
  rw [hidentity]
  have hZne : chartPartitionFunction β s ≠ 0 := ne_of_gt hZ
  field_simp

omit [DecidableEq P] in
/-- The unnormalized chart identity at zero tilt. -/
theorem chartFamilyIdentity_zeroTilt
    {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (Bᵢ : I → Finset C) (ρ : I → C → ℝ) (K θ : I → ℝ)
    (hF : Integrable
      (fun z : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) =>
        chartWeight β s (assemble B z.1 z.2) *
          ∏ i, (1 + K i * Real.cos
            (chartPairing (ρ i) (assemble B z.1 z.2) + θ i)))
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))))
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b)
    (hsub : ∀ i, Bᵢ i ⊆ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    (∫ x : C → ℝ, ∏ i, (1 + K i * Real.cos (chartPairing (ρ i) x + θ i))
      ∂chartMeasure β s) =
      ∫ y : {c : C // c ∉ B} → ℝ,
        ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
          Real.cos (renormalizedFunctional s B (ρ i) y + θ i))
        ∂reducedMeasure β s B := by
  have hidentity := chartFamilyIdentity β 0 s B Bᵢ ρ K θ (fun _ => 0)
    hβ hsep hn hsub hdisj hcover hcross (by simpa using hF)
  simpa [chartTiltConstant_zero, chartTiltPhase_zero] using hidentity

omit [DecidableEq P] in
/-- The fixed-retained-coordinate family identity at zero tilt: the common factor is one and the
local covariance phase disappears. -/
theorem conditionalFamilyIdentity_zeroTilt
    {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (Bᵢ : I → Finset C) (ρ : I → C → ℝ) (K θ : I → ℝ)
    (y : {c : C // c ∉ B} → ℝ)
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b)
    (hsub : ∀ i, Bᵢ i ⊆ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hcover : ∀ b ∈ B, ∃ i, b ∈ Bᵢ i)
    (hcross : ∀ i j b, i ≠ j → b ∈ Bᵢ i → ρ j b = 0) :
    (∫ x : {c : C // c ∈ B} → ℝ,
      selectedConditionalWeight β s B y x *
        ∏ i, (1 + K i * Real.cos
          (chartPairing (ρ i) (assemble B y x) + θ i))) =
      ∏ i, (1 + renormalizedActivity β (K i) s (Bᵢ i) (ρ i) *
        Real.cos (renormalizedFunctional s B (ρ i) y + θ i)) := by
  simpa [chartTiltConstant_zero, chartTiltPhase_zero] using
    (conditionalFamilyIdentity β 0 s B Bᵢ ρ K θ (fun _ => 0) y hβ hsep hn
      hsub hdisj hcover hcross)

omit [Fintype C] [DecidableEq C] [DecidableEq P] in
/-- The one-link renormalization activity estimate holds componentwise for a finite current family, with equality for
nonnegative bare activities. -/
theorem familyActivity_le_abs
    {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (s : P → C → ℝ) (Bᵢ : I → Finset C)
    (ρ : I → C → ℝ) (K : I → ℝ) :
    ∀ i, renormalizedActivity β (K i) s (Bᵢ i) (ρ i) ≤
      |K i| * Real.exp (-(β / 2) * ∑ b ∈ Bᵢ i, (ρ i b) ^ 2 / linkMass s b) := by
  intro i
  exact renormalizedActivity_le_abs β (K i) s (Bᵢ i) (ρ i)

omit [Fintype C] [DecidableEq C] [DecidableEq P] in
theorem familyActivity_eq_abs_of_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (s : P → C → ℝ) (Bᵢ : I → Finset C)
    (ρ : I → C → ℝ) (K : I → ℝ) (hK : ∀ i, 0 ≤ K i) :
    ∀ i, renormalizedActivity β (K i) s (Bᵢ i) (ρ i) =
      |K i| * Real.exp (-(β / 2) * ∑ b ∈ Bᵢ i, (ρ i b) ^ 2 / linkMass s b) := by
  intro i
  exact renormalizedActivity_eq_abs_of_nonneg β (K i) s (Bᵢ i) (ρ i) (hK i)


end FroehlichSpencer.FS82.Gaussian.RenormalizedFamily

end
