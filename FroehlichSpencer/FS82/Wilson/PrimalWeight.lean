/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Periodized Gaussian Villain weight
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open Real Complex

private theorem summable_gaussian_nat (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2) := by
  have hgeom : Summable fun n : ℕ => Real.exp ((n : ℝ) * (-c)) :=
    Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hc)
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) ?_ hgeom
  intro n
  apply Real.exp_le_exp.mpr
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
        have hn1 : (1 : ℝ) ≤ ((Nat.succ n : ℕ) : ℝ) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))
        have hxnonneg : 0 ≤ ((Nat.succ n : ℕ) : ℝ) := by positivity
        nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hxnonneg]
  have hmul := mul_le_mul_of_nonneg_left hn hc.le
  nlinarith

private theorem summable_gaussian_int (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact (summable_gaussian_nat c hc).congr fun n => by simp
  · exact (summable_gaussian_nat c hc).congr fun n => by simp

/-- The periodized one-dimensional Villain weight, in the normalization of (2.19). -/
@[expose] noncomputable def villainWeight (β x : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-(β / 2) * (x - 2 * Real.pi * n) ^ 2)

theorem villainWeight_summable (β x : ℝ) (hβ : 0 < β) :
    Summable fun n : ℤ => Real.exp (-(β / 2) * (x - 2 * Real.pi * n) ^ 2) := by
  let c := β * Real.pi ^ 2
  have hc : 0 < c := mul_pos hβ (sq_pos_of_pos Real.pi_pos)
  have hbase := summable_gaussian_int c hc
  have hbound (n : ℤ) :
      Real.exp (-(β / 2) * (x - 2 * Real.pi * n) ^ 2) ≤
        Real.exp (β / 2 * x ^ 2) * Real.exp (-c * (n : ℝ) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [c]
    nlinarith [sq_nonneg (2 * x - 2 * Real.pi * (n : ℝ))]
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) ?_
    (hbase.mul_left (Real.exp (β / 2 * x ^ 2)))
  exact hbound

theorem villainWeight_pos (β x : ℝ) (hβ : 0 < β) : 0 < villainWeight β x := by
  unfold villainWeight
  exact (villainWeight_summable β x hβ).tsum_pos
    (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)


/-- Gaussian Poisson summation gives the complex character expansion of the
periodized Villain weight. -/
theorem villainWeight_eq_complexCharacterSum (β x : ℝ) (hβ : 0 < β) :
    (villainWeight β x : ℂ) =
      (1 / (Real.sqrt (2 * Real.pi * β) : ℝ) : ℂ) *
        ∑' k : ℤ, (Real.exp (-(k : ℝ) ^ 2 / (2 * β)) : ℂ) *
          Complex.exp (-Complex.I * (k : ℝ) * x) := by
  let a : ℂ := (2 * Real.pi * β : ℝ)
  let b : ℂ := (β * x : ℝ)
  let c : ℂ := (Real.exp (-(β / 2) * x ^ 2) : ℝ)
  have ha : 0 < a.re := by
    dsimp [a]
    positivity
  have hpois := Complex.tsum_exp_neg_quadratic ha b
  have hexp (k : ℤ) :
      c * Complex.exp (-Real.pi / a * ((k : ℂ) + Complex.I * b) ^ 2) =
        (Real.exp (-(k : ℝ) ^ 2 / (2 * β)) : ℂ) *
          Complex.exp (-Complex.I * (k : ℝ) * x) := by
    rw [show c = Complex.exp (-(β / 2) * x ^ 2 : ℝ) by
      simp [c, Complex.ofReal_exp], Complex.ofReal_exp, ← Complex.exp_add]
    rw [← Complex.exp_add]
    apply congrArg Complex.exp
    dsimp [a, b, c]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    field_simp [show (β : ℂ) ≠ 0 by exact_mod_cast hβ.ne']
    ring
  have hscale : (1 / (a ^ (1 / 2 : ℂ))) =
      (1 / (Real.sqrt (2 * Real.pi * β) : ℝ) : ℂ) := by
    have hpow : a ^ (1 / 2 : ℂ) =
        (Real.sqrt (2 * Real.pi * β) : ℂ) := by
      rw [show a = ((2 * Real.pi * β : ℝ) : ℂ) by rfl]
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      rw [← Complex.ofReal_cpow (by positivity) (1 / 2 : ℝ), Real.sqrt_eq_rpow]
    rw [hpow]
  calc
    (villainWeight β x : ℂ) =
        ∑' n : ℤ, Complex.exp (-(β / 2) * (x - 2 * Real.pi * n) ^ 2) := by
          rw [villainWeight, Complex.ofReal_tsum]
          apply tsum_congr
          intro n
          rw [Complex.ofReal_exp]
          congr 1
          push_cast
          ring
    _ = c * ∑' n : ℤ,
          Complex.exp (-Real.pi * a * (n : ℂ) ^ 2 + 2 * Real.pi * b * n) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          rw [show c = Complex.exp (-(β / 2) * x ^ 2 : ℝ) by
            simp [c, Complex.ofReal_exp], ← Complex.exp_add]
          apply congrArg Complex.exp
          dsimp [a, b, c]
          push_cast
          ring
    _ = c * ((1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, Complex.exp (-Real.pi / a * ((k : ℂ) + Complex.I * b) ^ 2)) := by
          rw [hpois]
    _ = (1 / (Real.sqrt (2 * Real.pi * β) : ℝ) : ℂ) *
          ∑' k : ℤ, (Real.exp (-(k : ℝ) ^ 2 / (2 * β)) : ℂ) *
            Complex.exp (-Complex.I * (k : ℝ) * x) := by
          rw [hscale]
          calc
            c * ((1 / (Real.sqrt (2 * Real.pi * β) : ℝ) : ℂ) *
                ∑' k : ℤ, Complex.exp (-Real.pi / a * ((k : ℂ) + Complex.I * b) ^ 2)) =
              (1 / (Real.sqrt (2 * Real.pi * β) : ℝ) : ℂ) *
                (c * ∑' k : ℤ,
                  Complex.exp (-Real.pi / a * ((k : ℂ) + Complex.I * b) ^ 2)) := by ring
            _ = (1 / (Real.sqrt (2 * Real.pi * β) : ℝ) : ℂ) *
                ∑' k : ℤ, c * Complex.exp (-Real.pi / a * ((k : ℂ) + Complex.I * b) ^ 2) := by
                  rw [← tsum_mul_left]
            _ = _ := by
                  congr 1
                  apply tsum_congr
                  intro k
                  exact hexp k

/-- The real cosine-series form of the Villain character expansion. -/
theorem villainWeight_eq_fourierCosineSum (β x : ℝ) (hβ : 0 < β) :
    villainWeight β x =
      (1 / Real.sqrt (2 * Real.pi * β)) *
        ∑' m : ℤ, Real.exp (-(m : ℝ) ^ 2 / (2 * β)) *
          Real.cos ((m : ℝ) * x) := by
  let g : ℤ → ℝ := fun m => Real.exp (-(m : ℝ) ^ 2 / (2 * β))
  let f : ℤ → ℝ := fun m => g m * Real.cos ((m : ℝ) * x)
  let z : ℤ → ℂ := fun m => (g m : ℂ) * Complex.exp (-Complex.I * (m : ℝ) * x)
  have hgcoef : 0 < 1 / (2 * β) := by positivity
  have hgauss : Summable fun m : ℤ => Real.exp (-(1 / (2 * β)) * (m : ℝ) ^ 2) :=
    summable_gaussian_int (1 / (2 * β)) hgcoef
  have hg : Summable g := by
    exact hgauss.congr fun m => by
      congr 1
      field_simp
  have hf : Summable f := by
    apply hg.of_norm_bounded
    intro m
    dsimp [f, g]
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp (-(m : ℝ) ^ 2 / (2 * β)) * 1 :=
        mul_le_mul_of_nonneg_left (abs_cos_le_one _) (Real.exp_nonneg _)
      _ = Real.exp (-(m : ℝ) ^ 2 / (2 * β)) := mul_one _
  have hz : Summable z := by
    apply hg.of_norm_bounded
    intro m
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
    rw [abs_of_nonneg (Real.exp_nonneg _)]
  have hre (m : ℤ) : (z m).re = f m := by
    calc
      (z m).re = g m * (Complex.exp (-Complex.I * (m : ℝ) * x)).re := by
        simp [z, Complex.mul_re]
      _ = g m * Real.cos ((m : ℝ) * x) := by
        rw [Complex.exp_re]
        simp [Complex.mul_re, Complex.mul_im]
  have hcomplex := villainWeight_eq_complexCharacterSum β x hβ
  have hreal := congrArg Complex.re hcomplex
  have hP_re :
      (1 / (Real.sqrt (2 * Real.pi * β) : ℝ) : ℂ).re =
        1 / Real.sqrt (2 * Real.pi * β) := by simp
  have hP_im :
      (1 / (Real.sqrt (2 * Real.pi * β) : ℝ) : ℂ).im = 0 := by simp
  rw [Complex.mul_re, hP_re, hP_im, zero_mul,
    Complex.re_tsum hz] at hreal
  ring_nf at hreal
  have hsum : (∑' m : ℤ, (z m).re) = ∑' m : ℤ, f m := tsum_congr hre
  rw [hsum] at hreal
  have hcoef :
      1 / Real.sqrt (2 * Real.pi * β) =
        (Real.sqrt 2)⁻¹ * (Real.sqrt (Real.pi * β))⁻¹ := by
    rw [show 2 * Real.pi * β = 2 * (Real.pi * β) by ring,
      Real.sqrt_mul (by positivity)]
    field_simp
  rw [hcoef]
  simpa [f, g] using hreal

theorem villainCharacterCoeff_summable (β : ℝ) (hβ : 0 < β) :
    Summable fun m : ℤ => Real.exp (-(m : ℝ) ^ 2 / (2 * β)) := by
  have hcoef : 0 < 1 / (2 * β) := by positivity
  have hgauss := summable_gaussian_int (1 / (2 * β)) hcoef
  refine hgauss.congr fun m => ?_
  congr 1
  field_simp

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

/-- A canonical real representative of a unit-circle angle, in `(-1/2,1/2]`. -/
@[expose] noncomputable def circleRepresentative (z : UnitAddCircle) : ℝ :=
  (AddCircle.equivIoc (1 : ℝ) (-1 / 2) z).1

theorem circleRepresentative_mem (z : UnitAddCircle) :
    circleRepresentative z ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
  have h := (AddCircle.equivIoc (1 : ℝ) (-1 / 2) z).2
  norm_num [circleRepresentative] at h ⊢
  exact h

@[simp] theorem circleRepresentative_coe (z : UnitAddCircle) :
    (circleRepresentative z : UnitAddCircle) = z :=
  AddCircle.coe_equivIoc

/-- The continuous Villain character series on the unit additive circle.  The
physical angle represented by `z` is `2π z`; the character index is negated
to match the Fourier convention in (2.19). -/
@[expose] noncomputable def villainCircleFourierMap (β : ℝ) :
    C(UnitAddCircle, ℂ) :=
  (1 / Real.sqrt (2 * Real.pi * β) : ℂ) •
    ∑' m : ℤ,
      (Real.exp (-(m : ℝ) ^ 2 / (2 * β)) : ℂ) •
        (fourier (T := (1 : ℝ)) (-m))

private theorem villainCircleFourierTerms_summable (β : ℝ) (hβ : 0 < β) :
    Summable fun m : ℤ =>
      (Real.exp (-(m : ℝ) ^ 2 / (2 * β)) : ℂ) •
        (fourier (T := (1 : ℝ)) (-m)) := by
  apply Summable.of_norm_bounded (villainCharacterCoeff_summable β hβ)
  intro m
  rw [norm_smul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  have hfourier : ‖fourier (T := (1 : ℝ)) (-m)‖ = 1 :=
    fourier_norm (T := (1 : ℝ)) (-m)
  rw [hfourier]
  simp

/-- The continuous circle weight agrees with the literal periodized Gaussian
on the canonical representative. -/
theorem villainCircleFourierMap_apply (β : ℝ) (z : UnitAddCircle) (hβ : 0 < β) :
    villainCircleFourierMap β z =
      (villainWeight β (2 * Real.pi * circleRepresentative z) : ℂ) := by
  let r := circleRepresentative z
  have hr : (r : UnitAddCircle) = z := by
    dsimp [r]
    exact AddCircle.coe_equivIoc
  have hsum := ContinuousMap.tsum_apply
    (villainCircleFourierTerms_summable β hβ) (r : UnitAddCircle)
  have hterms : ∀ m : ℤ,
      ((Real.exp (-(m : ℝ) ^ 2 / (2 * β)) : ℂ) •
      fourier (T := (1 : ℝ)) (-m))
          (r : UnitAddCircle) =
        (Real.exp (-(m : ℝ) ^ 2 / (2 * β)) : ℂ) *
          Complex.exp (-Complex.I * (m : ℝ) * (2 * Real.pi * r)) := by
    intro m
    change (Real.exp (-(m : ℝ) ^ 2 / (2 * β)) : ℂ) *
      fourier (T := (1 : ℝ)) (-m) (r : UnitAddCircle) = _
    rw [fourier_coe_apply (T := (1 : ℝ))]
    congr 1
    push_cast
    ring_nf
  have hsum' :
      (∑' m : ℤ,
        ((Real.exp (-(m : ℝ) ^ 2 / (2 * β)) : ℂ) •
          fourier (T := (1 : ℝ)) (-m))
          (r : UnitAddCircle)) =
        ∑' m : ℤ,
          (Real.exp (-(m : ℝ) ^ 2 / (2 * β)) : ℂ) *
            Complex.exp (-Complex.I * (m : ℝ) * (2 * Real.pi * r)) :=
    tsum_congr hterms
  rw [villainCircleFourierMap, ContinuousMap.smul_apply, ← hr, ← hsum, hsum']
  simp only [smul_eq_mul]
  have hrep : circleRepresentative (r : UnitAddCircle) = r := by
    have hrmem : r ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1) := by
      rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
      exact circleRepresentative_mem z
    have h := AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (-1 / 2 : ℝ)) hrmem
    exact congrArg Subtype.val h
  rw [hrep]
  symm
  have hpoisson := villainWeight_eq_complexCharacterSum β (2 * Real.pi * r) hβ
  have hphase (m : ℤ) :
      Complex.exp (-Complex.I * (m : ℝ) * ((2 * Real.pi * r : ℝ) : ℂ)) =
        Complex.exp (-Complex.I * (m : ℝ) * (2 * (Real.pi : ℂ) * (r : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [show (∑' m : ℤ,
      (Real.exp (-(m : ℝ) ^ 2 / (2 * β)) : ℂ) *
        Complex.exp (-Complex.I * (m : ℝ) * ((2 * Real.pi * r : ℝ) : ℂ))) =
      ∑' m : ℤ,
        (Real.exp (-(m : ℝ) ^ 2 / (2 * β)) : ℂ) *
          Complex.exp (-Complex.I * (m : ℝ) * (2 * (Real.pi : ℂ) * (r : ℂ))) by
      apply tsum_congr
      intro m
      rw [hphase]] at hpoisson
  exact hpoisson

end FroehlichSpencer.FS82.Wilson

end
