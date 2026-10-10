/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.LeftRight

/-!
# From the moment bound to the variance (the dipole tilt construction: FS81 Remark 1 after Theorem 7.3)

FS81 derive (7.18) from (7.17) "by expanding to second order in `ε`". For a symmetric weight `w` and
a symmetric observable `X` with exponential moments, a prefactor-one lower bound
`⟨e^{εX}⟩ ≥ e^{aε²}` (small `ε > 0`) gives `⟨X²⟩ ≥ a` (`le_tsum_sq_mul_of_exp_le`):

* `e^y ≤ 1 + y + y² e^{|y|}` (`exp_le_one_add_add_sq_mul_exp_abs`), so
  `⟨e^{εX}⟩ ≤ 1 + ε⟨X⟩ + ε²⟨X² e^{ε|X|}⟩` with `⟨X⟩ = 0` by symmetry;
* hence `a ≤ ⟨X² e^{ε|X|}⟩` for every small `ε > 0`, and Tannery's theorem
  (`tendsto_tsum_of_dominated_convergence`) lets `ε → 0`.

The lower bound must have prefactor one (a bound `c e^{aε²}` with `c < 1` gives nothing), which is
why the repair of FS81's proof keeps the prefactor one throughout.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Roughening

open Filter Topology

/-- `e^y ≤ 1 + y + y² e^{|y|}`. -/
theorem exp_le_one_add_add_sq_mul_exp_abs (y : ℝ) :
    Real.exp y ≤ 1 + y + y ^ 2 * Real.exp |y| := by
  have h2 : y ^ 2 ≤ y ^ 2 * Real.exp |y| :=
    le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (abs_nonneg y))
  by_cases hy : |y| ≤ 1
  · have h := Real.abs_exp_sub_one_sub_id_le hy
    have h3 := le_abs_self (Real.exp y - 1 - y)
    linarith
  · push Not at hy
    have hsq : |y| ≤ y ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg y]
    rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0] at hy hsq ⊢
      have : Real.exp y ≤ y ^ 2 * Real.exp y :=
        le_mul_of_one_le_left (Real.exp_pos y).le (by nlinarith)
      linarith
    · rw [abs_of_neg h0] at hsq
      have h1 : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr h0.le
      linarith

/-- `x² e^{δ₀|x|} ≤ (2/δ₀²)(e^{2δ₀x} + e^{−2δ₀x})`. -/
theorem sq_mul_exp_abs_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (x : ℝ) :
    x ^ 2 * Real.exp (δ₀ * |x|) ≤
      2 / δ₀ ^ 2 * (Real.exp (2 * δ₀ * x) + Real.exp (-(2 * δ₀) * x)) := by
  set t := δ₀ * |x| with ht
  have ht0 : 0 ≤ t := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg ht0
  have htsq : t ^ 2 ≤ 2 * Real.exp t := by nlinarith
  have hx2 : x ^ 2 = t ^ 2 / δ₀ ^ 2 := by
    rw [ht, mul_pow, sq_abs]; field_simp
  have he : Real.exp t * Real.exp t ≤ Real.exp (2 * δ₀ * x) + Real.exp (-(2 * δ₀) * x) := by
    rw [← Real.exp_add]
    rcases le_or_gt 0 x with h0 | h0
    · have : t + t = 2 * δ₀ * x := by rw [ht, abs_of_nonneg h0]; ring
      rw [this]; linarith [Real.exp_pos (-(2 * δ₀) * x)]
    · have : t + t = -(2 * δ₀) * x := by rw [ht, abs_of_neg h0]; ring
      rw [this]; linarith [Real.exp_pos (2 * δ₀ * x)]
  rw [hx2]
  calc t ^ 2 / δ₀ ^ 2 * Real.exp t ≤ 2 * Real.exp t / δ₀ ^ 2 * Real.exp t :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right htsq (by positivity))
          (Real.exp_pos _).le
    _ = 2 / δ₀ ^ 2 * (Real.exp t * Real.exp t) := by ring
    _ ≤ 2 / δ₀ ^ 2 * (Real.exp (2 * δ₀ * x) + Real.exp (-(2 * δ₀) * x)) :=
        mul_le_mul_of_nonneg_left he (by positivity)

/-- `|x| ≤ (1/δ₀)(e^{2δ₀x} + e^{−2δ₀x})`. -/
theorem abs_le_exp_add_exp {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (x : ℝ) :
    |x| ≤ 1 / δ₀ * (Real.exp (2 * δ₀ * x) + Real.exp (-(2 * δ₀) * x)) := by
  have h1 : δ₀ * |x| ≤ Real.exp (2 * δ₀ * |x|) := by
    have := Real.add_one_le_exp (2 * δ₀ * |x|)
    nlinarith [abs_nonneg x]
  have h2 : Real.exp (2 * δ₀ * |x|) ≤ Real.exp (2 * δ₀ * x) + Real.exp (-(2 * δ₀) * x) := by
    rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0]; linarith [Real.exp_pos (-(2 * δ₀) * x)]
    · rw [abs_of_neg h0]
      have : 2 * δ₀ * -x = -(2 * δ₀) * x := by ring
      rw [this]; linarith [Real.exp_pos (2 * δ₀ * x)]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ₀, mul_comm]
  linarith

/-- **The variance from the moment bound** (FS81 (7.17) ⇒ (7.18)). For a weight `w ≥ 0` and an
observable `X`, both symmetric under an involution-like equivalence `e` (`X ∘ e = −X`,
`w ∘ e = w`), with exponential moments `Σ e^{cX} w < ∞` for `|c| ≤ δ`: if
`e^{aε²} Σ w ≤ Σ e^{εX} w` for `0 < ε ≤ δ`, then `a Σ w ≤ Σ X² w`. -/
theorem le_tsum_sq_mul_of_exp_le {ι : Type*} {X w : ι → ℝ} (e : ι ≃ ι)
    (hXe : ∀ n, X (e n) = -X n) (hwe : ∀ n, w (e n) = w n) (hw0 : ∀ n, 0 ≤ w n) {δ a : ℝ}
    (hδ : 0 < δ) (hsum : ∀ c, |c| ≤ δ → Summable fun n => Real.exp (c * X n) * w n)
    (hM : ∀ ε, 0 < ε → ε ≤ δ →
      Real.exp (a * ε ^ 2) * ∑' n, w n ≤ ∑' n, Real.exp (ε * X n) * w n) :
    a * ∑' n, w n ≤ ∑' n, X n ^ 2 * w n := by
  set δ₀ := δ / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := half_pos hδ
  have h2δ₀ : 2 * δ₀ = δ := by rw [hδ₀def]; ring
  set Z := ∑' n, w n with hZ
  have hsw : Summable w := by
    have h := hsum 0 (by rw [abs_zero]; exact hδ.le)
    simpa using h
  have hZ0 : 0 ≤ Z := tsum_nonneg hw0
  -- the dominating family
  set bnd : ι → ℝ := fun n => 2 / δ₀ ^ 2 *
    ((Real.exp (δ * X n) + Real.exp (-δ * X n)) * w n) with hbnd
  have hsplus : Summable fun n => (Real.exp (δ * X n) + Real.exp (-δ * X n)) * w n := by
    have h1 := hsum δ (by rw [abs_of_pos hδ])
    have h2 := hsum (-δ) (by rw [abs_neg, abs_of_pos hδ])
    exact (h1.add h2).congr fun n => by ring
  have hbsum : Summable bnd := hsplus.mul_left _
  have hbound : ∀ ε, 0 ≤ ε → ε ≤ δ₀ → ∀ n,
      |X n ^ 2 * Real.exp (ε * |X n|) * w n| ≤ bnd n := by
    intro ε hε0 hε n
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (hw0 n))]
    have h1 : Real.exp (ε * |X n|) ≤ Real.exp (δ₀ * |X n|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hε (abs_nonneg _))
    have h2 := sq_mul_exp_abs_le hδ₀ (X n)
    rw [h2δ₀] at h2
    have h3 : X n ^ 2 * Real.exp (ε * |X n|) ≤
        2 / δ₀ ^ 2 * (Real.exp (δ * X n) + Real.exp (-δ * X n)) :=
      (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)).trans h2
    rw [hbnd]
    calc X n ^ 2 * Real.exp (ε * |X n|) * w n
        ≤ 2 / δ₀ ^ 2 * (Real.exp (δ * X n) + Real.exp (-δ * X n)) * w n :=
          mul_le_mul_of_nonneg_right h3 (hw0 n)
      _ = _ := by ring
  have hS : ∀ ε, 0 ≤ ε → ε ≤ δ₀ →
      Summable fun n => X n ^ 2 * Real.exp (ε * |X n|) * w n := fun ε hε0 hε =>
    Summable.of_norm_bounded hbsum fun n => by
      rw [Real.norm_eq_abs]; exact hbound ε hε0 hε n
  -- the first moment vanishes
  have hX1 : Summable fun n => X n * w n := by
    refine Summable.of_norm_bounded (hsplus.mul_left (1 / δ₀)) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 n)]
    have h := abs_le_exp_add_exp hδ₀ (X n)
    rw [h2δ₀] at h
    calc |X n| * w n ≤ 1 / δ₀ * (Real.exp (δ * X n) + Real.exp (-δ * X n)) * w n :=
          mul_le_mul_of_nonneg_right (h.trans (le_of_eq (by ring_nf))) (hw0 n)
      _ = _ := by ring
  have hmean : ∑' n, X n * w n = 0 := by
    have h := e.tsum_eq (fun n => X n * w n)
    simp only [hXe, hwe, neg_mul, tsum_neg] at h
    linarith
  -- the second-order bound at every small `ε`
  have hsmall : ∀ ε, 0 < ε → ε ≤ δ₀ →
      a * Z ≤ ∑' n, X n ^ 2 * Real.exp (ε * |X n|) * w n := by
    intro ε hε0 hε
    have hεδ : ε ≤ δ := by linarith
    have hupper : ∑' n, Real.exp (ε * X n) * w n ≤
        Z + ε * ∑' n, X n * w n + ε ^ 2 * ∑' n, X n ^ 2 * Real.exp (ε * |X n|) * w n := by
      rw [hZ, ← tsum_mul_left, ← tsum_mul_left, ← hsw.tsum_add (hX1.mul_left ε),
        ← (hsw.add (hX1.mul_left ε)).tsum_add ((hS ε hε0.le hε).mul_left _)]
      refine (hsum ε (by rw [abs_of_pos hε0]; exact hεδ)).tsum_le_tsum (fun n => ?_)
        ((hsw.add (hX1.mul_left ε)).add ((hS ε hε0.le hε).mul_left _))
      have h := exp_le_one_add_add_sq_mul_exp_abs (ε * X n)
      rw [abs_mul, abs_of_pos hε0] at h
      have := mul_le_mul_of_nonneg_right h (hw0 n)
      nlinarith [this]
    have hlow := hM ε hε0 hεδ
    have hexp : 1 + a * ε ^ 2 ≤ Real.exp (a * ε ^ 2) := by
      linarith [Real.add_one_le_exp (a * ε ^ 2)]
    rw [hmean, mul_zero, add_zero] at hupper
    have h1 : (1 + a * ε ^ 2) * Z ≤ Z + ε ^ 2 * ∑' n, X n ^ 2 * Real.exp (ε * |X n|) * w n :=
      ((mul_le_mul_of_nonneg_right hexp hZ0).trans hlow).trans hupper
    have hε2 : 0 < ε ^ 2 := by positivity
    nlinarith
  -- the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => ∑' n, X n ^ 2 * Real.exp (ε * |X n|) * w n) (𝓝[>] 0)
      (𝓝 (∑' n, X n ^ 2 * Real.exp (0 * |X n|) * w n)) := by
    refine tendsto_tsum_of_dominated_convergence hbsum (fun n => ?_) ?_
    · have hc : Continuous fun ε : ℝ => X n ^ 2 * Real.exp (ε * |X n|) * w n :=
        (continuous_const.mul (Real.continuous_exp.comp (continuous_id.mul continuous_const))).mul
          continuous_const
      exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hδ₀] with ε hε n
      rw [Real.norm_eq_abs]
      exact hbound ε hε.1.le hε.2.le n
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a * Z ≤ ∑' n, X n ^ 2 * Real.exp (ε * |X n|) * w n := by
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with ε hε
    exact hsmall ε hε.1 hε.2.le
  have h := ge_of_tendsto hlim hev
  simpa using h

end FroehlichSpencer.BKT.SOS.Roughening

end
