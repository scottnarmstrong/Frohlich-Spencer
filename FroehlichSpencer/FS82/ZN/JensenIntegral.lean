/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.JensenStep

/-!
# the lower bound (3.49)

For the renormalized factors `1 + z_i F_i(θ; ε, δ_i)` and the Wilson weight `W_ε`:

* `renormU_eq_mul_exp`: `U(θ; ε, δ) = U(θ; 0, 0) e^{Δ(ε, δ)}` with `Δ = shiftDelta`;
* `norm_shiftDelta_le`: `|Δ(ε, δ)| ≤ shiftK1 = 2π|δ| + Σ_p β (e^{|η_p|} − 1) 2π|ε_p|`;
* `norm_shiftDelta_add_neg_le`: `|Δ(ε, δ) + Δ(−ε, −δ)| ≤ shiftK2 = Σ_p β (e^{|η_p|} − 1)(2πε_p)²`;
* `renormF_neg`, `wilsonWeight_neg`: the reflection `θ ↦ −θ` is `(ε, δ) ↦ (−ε, −δ)`;
* `integral_renorm_jensen`: FS82 (3.49).

`shiftK1` is the quantity `k_ϱ(ε)` of FS82 (3.45), up to constants: the phase `|ε(μ_ϱ)|` plus
`β` times the sum of `|ε_p|` over the plaquettes of the selected links.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.ZN.Torus

noncomputable section

local instance jensenIntegral_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance jensenIntegral_measureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-! ### The exponent of `i_β` -/

/-- The exponent of `shiftFactor`. -/
def shiftExponent (β η : ℝ) (z : UnitAddCircle) : ℂ :=
  ((β * ((Real.cosh η - 1) * (cosC z - 1)) : ℝ) : ℂ) -
    Complex.I * ((β * (Real.sinh η * sinC z) : ℝ) : ℂ)

theorem shiftFactor_eq_exp (β η : ℝ) (z : UnitAddCircle) :
    shiftFactor β η z = Complex.exp (shiftExponent β η z) := rfl

theorem shiftExponent_re (β η : ℝ) (z : UnitAddCircle) :
    (shiftExponent β η z).re = β * ((Real.cosh η - 1) * (cosC z - 1)) := by
  unfold shiftExponent
  rw [Complex.sub_re, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im]
  ring

theorem shiftExponent_im (β η : ℝ) (z : UnitAddCircle) :
    (shiftExponent β η z).im = -(β * (Real.sinh η * sinC z)) := by
  unfold shiftExponent
  rw [Complex.sub_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re]
  ring

theorem cosh_sub_one_add_abs_sinh (η : ℝ) :
    Real.cosh η - 1 + |Real.sinh η| = Real.exp |η| - 1 := by
  rw [Real.abs_sinh, ← Real.cosh_abs η, ← Real.cosh_add_sinh |η|]
  ring

theorem exp_abs_sub_one_nonneg (η : ℝ) : 0 ≤ Real.exp |η| - 1 := by
  have := Real.add_one_le_exp |η|
  linarith [abs_nonneg η]

/-- First difference of the exponent. -/
theorem norm_shiftExponent_sub_le {β : ℝ} (hβ : 0 ≤ β) (η : ℝ) (z : UnitAddCircle) (e : ℝ) :
    ‖shiftExponent β η (z + (e : UnitAddCircle)) - shiftExponent β η z‖ ≤
      β * (Real.exp |η| - 1) * (2 * Real.pi * |e|) := by
  obtain ⟨x, rfl⟩ := exists_real_lift z
  have hpi := Real.pi_pos
  have hc := Real.abs_cos_sub_cos_le (2 * Real.pi * (x + e)) (2 * Real.pi * x)
  have hs := Real.abs_sin_sub_sin_le (2 * Real.pi * (x + e)) (2 * Real.pi * x)
  have hd : |2 * Real.pi * (x + e) - 2 * Real.pi * x| = 2 * Real.pi * |e| := by
    rw [show 2 * Real.pi * (x + e) - 2 * Real.pi * x = 2 * Real.pi * e by ring, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [hd] at hc hs
  have hch : 0 ≤ Real.cosh η - 1 := by linarith [Real.one_le_cosh η]
  have hre : (shiftExponent β η ((x : UnitAddCircle) + (e : UnitAddCircle)) -
      shiftExponent β η (x : UnitAddCircle)).re =
      β * ((Real.cosh η - 1) *
        (Real.cos (2 * Real.pi * (x + e)) - Real.cos (2 * Real.pi * x))) := by
    rw [Complex.sub_re, shiftExponent_re, shiftExponent_re, ← AddCircle.coe_add, cosC_coe,
      cosC_coe]
    ring
  have him : (shiftExponent β η ((x : UnitAddCircle) + (e : UnitAddCircle)) -
      shiftExponent β η (x : UnitAddCircle)).im =
      -(β * (Real.sinh η *
        (Real.sin (2 * Real.pi * (x + e)) - Real.sin (2 * Real.pi * x)))) := by
    rw [Complex.sub_im, shiftExponent_im, shiftExponent_im, ← AddCircle.coe_add, sinC_coe,
      sinC_coe]
    ring
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [hre, him, abs_neg, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hβ, abs_of_nonneg hch,
    ← cosh_sub_one_add_abs_sinh]
  have h1 : β * ((Real.cosh η - 1) *
      |Real.cos (2 * Real.pi * (x + e)) - Real.cos (2 * Real.pi * x)|) ≤
      β * ((Real.cosh η - 1) * (2 * Real.pi * |e|)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hch) hβ
  have h2 : β * (|Real.sinh η| *
      |Real.sin (2 * Real.pi * (x + e)) - Real.sin (2 * Real.pi * x)|) ≤
      β * (|Real.sinh η| * (2 * Real.pi * |e|)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) hβ
  linarith

theorem abs_cos_sub_one_le (t : ℝ) : |Real.cos t - 1| ≤ t ^ 2 / 2 := by
  rw [abs_le]
  constructor
  · linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  · linarith [Real.cos_le_one t, sq_nonneg t]

/-- Second difference of the exponent. -/
theorem norm_shiftExponent_second_diff_le {β : ℝ} (hβ : 0 ≤ β) (η : ℝ) (z : UnitAddCircle)
    (e : ℝ) :
    ‖(shiftExponent β η (z + (e : UnitAddCircle)) - shiftExponent β η z) +
        (shiftExponent β η (z + ((-e : ℝ) : UnitAddCircle)) - shiftExponent β η z)‖ ≤
      β * (Real.exp |η| - 1) * (2 * Real.pi * e) ^ 2 := by
  obtain ⟨x, rfl⟩ := exists_real_lift z
  have hch : 0 ≤ Real.cosh η - 1 := by linarith [Real.one_le_cosh η]
  have hcosd := abs_cos_sub_one_le (2 * Real.pi * e)
  have hcos1 := Real.abs_cos_le_one (2 * Real.pi * x)
  have hsin1 := Real.abs_sin_le_one (2 * Real.pi * x)
  have hcc : Real.cos (2 * Real.pi * (x + e)) + Real.cos (2 * Real.pi * (x + -e)) -
      2 * Real.cos (2 * Real.pi * x) =
      2 * Real.cos (2 * Real.pi * x) * (Real.cos (2 * Real.pi * e) - 1) := by
    rw [show 2 * Real.pi * (x + e) = 2 * Real.pi * x + 2 * Real.pi * e by ring,
      show 2 * Real.pi * (x + -e) = 2 * Real.pi * x - 2 * Real.pi * e by ring,
      Real.cos_add, Real.cos_sub]
    ring
  have hss : Real.sin (2 * Real.pi * (x + e)) + Real.sin (2 * Real.pi * (x + -e)) -
      2 * Real.sin (2 * Real.pi * x) =
      2 * Real.sin (2 * Real.pi * x) * (Real.cos (2 * Real.pi * e) - 1) := by
    rw [show 2 * Real.pi * (x + e) = 2 * Real.pi * x + 2 * Real.pi * e by ring,
      show 2 * Real.pi * (x + -e) = 2 * Real.pi * x - 2 * Real.pi * e by ring,
      Real.sin_add, Real.sin_sub]
    ring
  have hre : ((shiftExponent β η ((x : UnitAddCircle) + (e : UnitAddCircle)) -
        shiftExponent β η (x : UnitAddCircle)) +
      (shiftExponent β η ((x : UnitAddCircle) + ((-e : ℝ) : UnitAddCircle)) -
        shiftExponent β η (x : UnitAddCircle))).re =
      β * ((Real.cosh η - 1) *
        (2 * Real.cos (2 * Real.pi * x) * (Real.cos (2 * Real.pi * e) - 1))) := by
    rw [← hcc, Complex.add_re, Complex.sub_re, Complex.sub_re, shiftExponent_re, shiftExponent_re,
      shiftExponent_re, ← AddCircle.coe_add, ← AddCircle.coe_add, cosC_coe, cosC_coe, cosC_coe]
    ring
  have him : ((shiftExponent β η ((x : UnitAddCircle) + (e : UnitAddCircle)) -
        shiftExponent β η (x : UnitAddCircle)) +
      (shiftExponent β η ((x : UnitAddCircle) + ((-e : ℝ) : UnitAddCircle)) -
        shiftExponent β η (x : UnitAddCircle))).im =
      -(β * (Real.sinh η *
        (2 * Real.sin (2 * Real.pi * x) * (Real.cos (2 * Real.pi * e) - 1)))) := by
    rw [← hss, Complex.add_im, Complex.sub_im, Complex.sub_im, shiftExponent_im, shiftExponent_im,
      shiftExponent_im, ← AddCircle.coe_add, ← AddCircle.coe_add, sinC_coe, sinC_coe, sinC_coe]
    ring
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [hre, him, abs_neg, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hβ, abs_of_nonneg hch, ← cosh_sub_one_add_abs_sinh,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hE : (0 : ℝ) ≤ (2 * Real.pi * e) ^ 2 := sq_nonneg _
  have h1 : 2 * |Real.cos (2 * Real.pi * x)| * |Real.cos (2 * Real.pi * e) - 1| ≤
      (2 * Real.pi * e) ^ 2 := by
    have := mul_le_mul hcos1 hcosd (abs_nonneg _) zero_le_one
    nlinarith
  have h2 : 2 * |Real.sin (2 * Real.pi * x)| * |Real.cos (2 * Real.pi * e) - 1| ≤
      (2 * Real.pi * e) ^ 2 := by
    have := mul_le_mul hsin1 hcosd (abs_nonneg _) zero_le_one
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hch) hβ
  have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (abs_nonneg (Real.sinh η))) hβ
  linarith

variable {E P ι : Type*} [Fintype E] [Fintype P] [Fintype ι]

/-! ### The dependence of `U` on `(ε, δ)` -/

/-- `Δ(ε, δ)`: the logarithm of `U(θ; ε, δ)/U(θ; 0, 0)`. -/
def shiftDelta (β : ℝ) (c : P → E → ℤ) (a : E → ℝ) (ε : P → ℝ) (δ : ℝ)
    (θ : E → UnitAddCircle) : ℂ :=
  ((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I +
    ∑ p, (shiftExponent β (plaqShift c a p) (flux c p θ + (ε p : UnitAddCircle)) -
      shiftExponent β (plaqShift c a p) (flux c p θ))

theorem renormU_eq_mul_exp (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ) (δ : ℝ)
    (a : E → ℝ) (θ : E → UnitAddCircle) :
    renormU β c ε ρ δ a θ =
      renormU β c (fun _ => 0) ρ 0 a θ * Complex.exp (shiftDelta β c a ε δ θ) := by
  unfold renormU shiftDelta
  rw [Complex.exp_add, Complex.exp_sum, eC_add, eC_coe]
  simp only [AddCircle.coe_zero, add_zero]
  have hprod : (∏ p, shiftFactor β (plaqShift c a p) (flux c p θ + (ε p : UnitAddCircle))) =
      (∏ p, shiftFactor β (plaqShift c a p) (flux c p θ)) *
        ∏ p, Complex.exp (shiftExponent β (plaqShift c a p) (flux c p θ + (ε p : UnitAddCircle)) -
          shiftExponent β (plaqShift c a p) (flux c p θ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [shiftFactor_eq_exp, shiftFactor_eq_exp, ← Complex.exp_add]
    congr 1
    ring
  rw [hprod]
  ring

/-- The first-order bound `k₁`: `2π|δ| + Σ_p β (e^{|η_p|} − 1) 2π|ε_p|`. -/
def shiftK1 (β : ℝ) (c : P → E → ℤ) (a : E → ℝ) (ε : P → ℝ) (δ : ℝ) : ℝ :=
  2 * Real.pi * |δ| + ∑ p, β * (Real.exp |plaqShift c a p| - 1) * (2 * Real.pi * |ε p|)

/-- The second-order bound `k₂`: `Σ_p β (e^{|η_p|} − 1) (2πε_p)²`. -/
def shiftK2 (β : ℝ) (c : P → E → ℤ) (a : E → ℝ) (ε : P → ℝ) : ℝ :=
  ∑ p, β * (Real.exp |plaqShift c a p| - 1) * (2 * Real.pi * ε p) ^ 2

theorem norm_shiftDelta_le {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (a : E → ℝ) (ε : P → ℝ)
    (δ : ℝ) (θ : E → UnitAddCircle) :
    ‖shiftDelta β c a ε δ θ‖ ≤ shiftK1 β c a ε δ := by
  unfold shiftDelta shiftK1
  have h1 : ‖((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I‖ = 2 * Real.pi * |δ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  refine (norm_add_le _ _).trans ?_
  rw [h1]
  refine add_le_add le_rfl ((norm_sum_le _ _).trans ?_)
  exact Finset.sum_le_sum fun p _ => norm_shiftExponent_sub_le hβ _ _ _

theorem norm_shiftDelta_add_neg_le {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (a : E → ℝ)
    (ε : P → ℝ) (δ : ℝ) (θ : E → UnitAddCircle) :
    ‖shiftDelta β c a ε δ θ + shiftDelta β c a (fun p => -ε p) (-δ) θ‖ ≤ shiftK2 β c a ε := by
  unfold shiftDelta shiftK2
  have hsum : ((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I +
        ∑ p, (shiftExponent β (plaqShift c a p) (flux c p θ + (ε p : UnitAddCircle)) -
          shiftExponent β (plaqShift c a p) (flux c p θ)) +
      (((2 * Real.pi * -δ : ℝ) : ℂ) * Complex.I +
        ∑ p, (shiftExponent β (plaqShift c a p) (flux c p θ + ((-ε p : ℝ) : UnitAddCircle)) -
          shiftExponent β (plaqShift c a p) (flux c p θ))) =
      ∑ p, ((shiftExponent β (plaqShift c a p) (flux c p θ + (ε p : UnitAddCircle)) -
          shiftExponent β (plaqShift c a p) (flux c p θ)) +
        (shiftExponent β (plaqShift c a p) (flux c p θ + ((-ε p : ℝ) : UnitAddCircle)) -
          shiftExponent β (plaqShift c a p) (flux c p θ))) := by
    rw [Finset.sum_add_distrib]
    push_cast
    ring
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun p _ => norm_shiftExponent_second_diff_le hβ _ _ _

theorem shiftK1_neg (β : ℝ) (c : P → E → ℤ) (a : E → ℝ) (ε : P → ℝ) (δ : ℝ) :
    shiftK1 β c a (fun p => -ε p) (-δ) = shiftK1 β c a ε δ := by
  unfold shiftK1
  simp only [abs_neg]

/-! ### Reflection -/

theorem renormF_neg (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ) (δ : ℝ) (a : E → ℝ)
    (θ : E → UnitAddCircle) :
    renormF β c ε ρ δ a (-θ) = renormF β c (fun p => -ε p) ρ (-δ) a θ := by
  have hU : renormU β c ε ρ δ a (-θ) =
      (starRingEnd ℂ) (renormU β c (fun p => -ε p) ρ (-δ) a θ) := by
    unfold renormU
    rw [map_mul, map_prod, ← eC_neg]
    congr 1
    · congr 1
      rw [pair_neg, AddCircle.coe_neg]
      abel
    · refine Finset.prod_congr rfl fun p _ => ?_
      rw [← shiftFactor_neg_arg]
      congr 1
      unfold flux
      rw [pair_neg, AddCircle.coe_neg]
      abel
  unfold renormF
  rw [hU, Complex.conj_re]

theorem wilsonWeight_neg (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (θ : E → UnitAddCircle) :
    wilsonWeight β c ε (-θ) = wilsonWeight β c (fun p => -ε p) θ := by
  unfold wilsonWeight
  refine Finset.prod_congr rfl fun p _ => ?_
  congr 2
  rw [← cosC_neg]
  congr 1
  unfold flux
  rw [pair_neg, AddCircle.coe_neg]
  abel

theorem wilsonWeight_eq_exp_sum (β : ℝ) (c : P → E → ℤ) (ε : P → ℝ) (θ : E → UnitAddCircle) :
    wilsonWeight β c ε θ =
      Real.exp (∑ p, β * cosC (flux c p θ + (ε p : UnitAddCircle))) := by
  unfold wilsonWeight
  rw [Real.exp_sum]

/-- FS82 (3.46)–(3.47) in symmetrized form:
`W_ε(θ) W_{−ε}(θ) ≥ W_0(θ)² e^{−β Σ_p (2πε_p)²}`. -/
theorem wilsonWeight_mul_reflect_ge {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (ε : P → ℝ)
    (θ : E → UnitAddCircle) :
    wilsonWeight β c (fun _ => 0) θ ^ 2 * Real.exp (-(β * ∑ p, (2 * Real.pi * ε p) ^ 2)) ≤
      wilsonWeight β c ε θ * wilsonWeight β c (fun p => -ε p) θ := by
  rw [wilsonWeight_eq_exp_sum, wilsonWeight_eq_exp_sum, wilsonWeight_eq_exp_sum, ← Real.exp_add,
    sq, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  obtain ⟨x, hx⟩ := exists_real_lift (flux c p θ)
  rw [← hx, AddCircle.coe_zero, add_zero, ← AddCircle.coe_add, ← AddCircle.coe_add, cosC_coe,
    cosC_coe, cosC_coe]
  have hcc : Real.cos (2 * Real.pi * (x + ε p)) + Real.cos (2 * Real.pi * (x + -ε p)) =
      2 * Real.cos (2 * Real.pi * x) * Real.cos (2 * Real.pi * ε p) := by
    rw [show 2 * Real.pi * (x + ε p) = 2 * Real.pi * x + 2 * Real.pi * ε p by ring,
      show 2 * Real.pi * (x + -ε p) = 2 * Real.pi * x - 2 * Real.pi * ε p by ring,
      Real.cos_add, Real.cos_sub]
    ring
  have hcosd := abs_le.mp (abs_cos_sub_one_le (2 * Real.pi * ε p))
  have hcos1 := abs_le.mp (Real.abs_cos_le_one (2 * Real.pi * x))
  have hkey : 2 * Real.cos (2 * Real.pi * x) - (2 * Real.pi * ε p) ^ 2 ≤
      2 * Real.cos (2 * Real.pi * x) * Real.cos (2 * Real.pi * ε p) := by
    have h1 : 0 ≤ 1 - Real.cos (2 * Real.pi * ε p) := by linarith [Real.cos_le_one (2 * Real.pi * ε p)]
    nlinarith [mul_le_mul_of_nonneg_right hcos1.2 h1]
  have := mul_le_mul_of_nonneg_left hkey hβ
  nlinarith [hcc]

/-! ### The integral inequality -/

theorem renormFactor_pos {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ) (δ : ℝ)
    (a : E → ℝ) (θ : E → UnitAddCircle) {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) :
    0 < 1 + z * renormF β c ε ρ δ a θ := by
  have h := abs_le.mp (abs_renormF_le_one hβ c ε ρ δ a θ)
  nlinarith [h.1]

/-- The pointwise two-point inequality for one renormalized factor. -/
theorem renormFactor_two_point {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (ε : P → ℝ) (ρ : E → ℤ)
    (δ : ℝ) (a : E → ℝ) (θ : E → UnitAddCircle) {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) :
    (1 + z * renormF β c (fun _ => 0) ρ 0 a θ) ^ 2 *
        Real.exp (-(6 * z * (2 * shiftK2 β c a ε + 12 * shiftK1 β c a ε δ ^ 2))) ≤
      (1 + z * renormF β c ε ρ δ a θ) *
        (1 + z * renormF β c (fun p => -ε p) ρ (-δ) a θ) := by
  have hp := renormU_eq_mul_exp β c ε ρ δ a θ
  have hm := renormU_eq_mul_exp β c (fun p => -ε p) ρ (-δ) a θ
  have h := two_point_lower_bound (u₀ := renormU β c (fun _ => 0) ρ 0 a θ)
    (Δp := shiftDelta β c a ε δ θ) (Δm := shiftDelta β c a (fun p => -ε p) (-δ) θ)
    (k₁ := shiftK1 β c a ε δ) (k₂ := shiftK2 β c a ε) hz0 hz
    (norm_renormU_le_one hβ c _ ρ 0 a θ)
    (by rw [← hp]; exact norm_renormU_le_one hβ c ε ρ δ a θ)
    (by rw [← hm]; exact norm_renormU_le_one hβ c _ ρ (-δ) a θ)
    (norm_shiftDelta_le hβ c a ε δ θ)
    (by rw [← shiftK1_neg]; exact norm_shiftDelta_le hβ c a _ (-δ) θ)
    (norm_shiftDelta_add_neg_le hβ c a ε δ θ)
  rw [← hp, ← hm] at h
  exact h

/-- **FS82 (3.49).** For activities `0 ≤ z_i ≤ 1/2`,
`∫ ∏ (1 + z_i F_i(ε, δ_i)) W_ε ≥ e^{−E} ∫ ∏ (1 + z_i F_i(0, 0)) W_0` with
`E = Σ_i 3 z_i (2 k₂,i + 12 k₁,i²) + (β/2) Σ_p (2πε_p)²`. -/
theorem integral_renorm_jensen {β : ℝ} (hβ : 0 ≤ β) (c : P → E → ℤ) (ε : P → ℝ)
    (zc : ι → ℝ) (hz0 : ∀ i, 0 ≤ zc i) (hz : ∀ i, zc i ≤ 1 / 2)
    (ρ : ι → E → ℤ) (δ : ι → ℝ) (a : ι → E → ℝ) :
    Real.exp (-(∑ i, 3 * zc i * (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (δ i) ^ 2) +
          β / 2 * ∑ p, (2 * Real.pi * ε p) ^ 2)) *
        ∫ θ, (∏ i, (1 + zc i * renormF β c (fun _ => 0) (ρ i) 0 (a i) θ)) *
          wilsonWeight β c (fun _ => 0) θ ≤
      ∫ θ, (∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) θ)) * wilsonWeight β c ε θ := by
  set Err := ∑ i, 3 * zc i * (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (δ i) ^ 2) +
    β / 2 * ∑ p, (2 * Real.pi * ε p) ^ 2 with hErr
  have hcontG : ∀ (ε' : P → ℝ) (δ' : ι → ℝ), Continuous fun θ : E → UnitAddCircle =>
      (∏ i, (1 + zc i * renormF β c ε' (ρ i) (δ' i) (a i) θ)) * wilsonWeight β c ε' θ :=
    fun ε' δ' => (continuous_finsetProd _ fun i _ =>
      continuous_const.add (continuous_const.mul (continuous_renormF β c ε' (ρ i) (δ' i) (a i)))).mul
      (continuous_wilsonWeight β c ε')
  have hpoint : ∀ θ : E → UnitAddCircle,
      Real.exp (-Err) * ((∏ i, (1 + zc i * renormF β c (fun _ => 0) (ρ i) 0 (a i) θ)) *
          wilsonWeight β c (fun _ => 0) θ) ≤
        ((∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) θ)) * wilsonWeight β c ε θ +
          (∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) (-θ))) *
            wilsonWeight β c ε (-θ)) / 2 := by
    intro θ
    have hA : 0 ≤ ∏ i, (1 + zc i * renormF β c (fun _ => 0) (ρ i) 0 (a i) θ) :=
      Finset.prod_nonneg fun i _ => (renormFactor_pos hβ c _ (ρ i) 0 (a i) θ (hz0 i) (hz i)).le
    have hP : 0 ≤ ∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) θ) :=
      Finset.prod_nonneg fun i _ => (renormFactor_pos hβ c ε (ρ i) (δ i) (a i) θ (hz0 i) (hz i)).le
    have hM : 0 ≤ ∏ i, (1 + zc i * renormF β c (fun p => -ε p) (ρ i) (-δ i) (a i) θ) :=
      Finset.prod_nonneg fun i _ =>
        (renormFactor_pos hβ c _ (ρ i) (-δ i) (a i) θ (hz0 i) (hz i)).le
    have hprod : (∏ i, (1 + zc i * renormF β c (fun _ => 0) (ρ i) 0 (a i) θ)) ^ 2 *
        Real.exp (-(∑ i, 6 * zc i *
          (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (δ i) ^ 2))) ≤
        (∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) θ)) *
          ∏ i, (1 + zc i * renormF β c (fun p => -ε p) (ρ i) (-δ i) (a i) θ) := by
      rw [← Finset.prod_pow, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
      exact renormFactor_two_point hβ c ε (ρ i) (δ i) (a i) θ (hz0 i) (hz i)
    have hw := wilsonWeight_mul_reflect_ge hβ c ε θ
    have hw0 := (wilsonWeight_pos β c (fun _ => 0) θ).le
    have hwp := (wilsonWeight_pos β c ε θ).le
    have hwm := (wilsonWeight_pos β c (fun p => -ε p) θ).le
    simp_rw [renormF_neg, wilsonWeight_neg]
    set A := ∏ i, (1 + zc i * renormF β c (fun _ => 0) (ρ i) 0 (a i) θ) with hAdef
    set Pp := ∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) θ) with hPdef
    set Pm := ∏ i, (1 + zc i * renormF β c (fun p => -ε p) (ρ i) (-δ i) (a i) θ) with hMdef
    set w0 := wilsonWeight β c (fun _ => 0) θ with hw0def
    set wp := wilsonWeight β c ε θ with hwpdef
    set wm := wilsonWeight β c (fun p => -ε p) θ with hwmdef
    set q := ∑ i, 6 * zc i * (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (δ i) ^ 2)
      with hq
    set r := β * ∑ p, (2 * Real.pi * ε p) ^ 2 with hr
    have hqr : q + r = 2 * Err := by
      have h1 : q = 2 * ∑ i, 3 * zc i *
          (2 * shiftK2 β c (a i) ε + 12 * shiftK1 β c (a i) ε (δ i) ^ 2) := by
        rw [hq, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hErr, h1, hr]
      ring
    have hErr2 : Real.exp (-Err) ^ 2 = Real.exp (-q) * Real.exp (-r) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      push_cast
      linarith
    have hc2 : (Real.exp (-Err) * (A * w0)) ^ 2 ≤ (Pp * wp) * (Pm * wm) := by
      have h1 : (Real.exp (-Err) * (A * w0)) ^ 2 =
          (A ^ 2 * Real.exp (-q)) * (w0 ^ 2 * Real.exp (-r)) := by
        rw [mul_pow, hErr2]
        ring
      rw [h1]
      calc A ^ 2 * Real.exp (-q) * (w0 ^ 2 * Real.exp (-r))
          ≤ (Pp * Pm) * (wp * wm) :=
            mul_le_mul hprod hw (by positivity) (mul_nonneg hP hM)
        _ = _ := by ring
    have hc0 : 0 ≤ Real.exp (-Err) * (A * w0) := by positivity
    have ha0 : 0 ≤ Pp * wp := mul_nonneg hP hwp
    have hb0 : 0 ≤ Pm * wm := mul_nonneg hM hwm
    nlinarith [sq_nonneg (Pp * wp - Pm * wm), sq_nonneg (Pp * wp + Pm * wm - 2 * (Real.exp (-Err) * (A * w0)))]
  have hint0 := integrable_of_continuous _ (hcontG (fun _ => 0) (fun _ => 0))
  have hintε := integrable_of_continuous _ (hcontG ε δ)
  have hintneg : Integrable fun θ : E → UnitAddCircle =>
      (∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) (-θ))) * wilsonWeight β c ε (-θ) :=
    integrable_of_continuous _ ((hcontG ε δ).comp continuous_neg)
  calc Real.exp (-Err) * ∫ θ, (∏ i, (1 + zc i * renormF β c (fun _ => 0) (ρ i) 0 (a i) θ)) *
          wilsonWeight β c (fun _ => 0) θ
      = ∫ θ, Real.exp (-Err) * ((∏ i, (1 + zc i * renormF β c (fun _ => 0) (ρ i) 0 (a i) θ)) *
          wilsonWeight β c (fun _ => 0) θ) := (integral_const_mul _ _).symm
    _ ≤ ∫ θ, ((∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) θ)) * wilsonWeight β c ε θ +
          (∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) (-θ))) *
            wilsonWeight β c ε (-θ)) / 2 :=
        integral_mono (hint0.const_mul _) ((hintε.add hintneg).div_const 2) hpoint
    _ = ∫ θ, (∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) θ)) * wilsonWeight β c ε θ := by
        rw [integral_div, integral_add hintε hintneg,
          integral_neg_config (fun θ : E → UnitAddCircle =>
            (∏ i, (1 + zc i * renormF β c ε (ρ i) (δ i) (a i) θ)) * wilsonWeight β c ε θ)]
        ring

end

end FroehlichSpencer.FS82.ZN.Torus

end
