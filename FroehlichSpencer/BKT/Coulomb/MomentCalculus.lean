/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Second moments from exponential-moment lower bounds

* `two_mul_le_of_exp_sq_le`: if `M ≥ e^{A u²}` near `0` with `M(0) = 1`, `M` has a derivative
  `M'` near `0` and `M'` has derivative `m₂` at `0`, then `2A ≤ m₂`.

Evenness of `M` is not
  needed: the first derivative vanishes because `M - e^{A u²}` has a local minimum at `0`.

The proof is the mean value theorem, not an analytic expansion.
* `hasDerivAt_integral_pow_mul_exp_mul`: differentiation under the integral sign,
  `d/du ∫ X^k e^{uX} W dμ = ∫ X^{k+1} e^{uX} W dμ`, for bounded `W` and `X` with all exponential
  moments finite; the dominating function is `|B| (k+1)!

(e^{cX} + e^{-cX})`,
  `c = |u₀| + 2` (`abs_pow_mul_exp_le`).

It supplies the twice-differentiability of the
  normalized moment functional and identifies its second derivative as a genuine integral
  (no `tsum` is involved).
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology Set MeasureTheory Metric

/-- If `M ≥ exp (A u²)` near `0` with equality at `0`, `M` is differentiable near `0` with
derivative `M'`, and `M'` has derivative `m₂` at `0`, then `2 A ≤ m₂`. FS81 (5.5). -/
theorem two_mul_le_of_exp_sq_le {M M' : ℝ → ℝ} {A m₂ : ℝ} (hM0 : M 0 = 1)
    (hM : ∀ᶠ u in 𝓝 0, HasDerivAt M (M' u) u) (hM' : HasDerivAt M' m₂ 0)
    (hlow : ∀ᶠ u in 𝓝 0, Real.exp (A * u ^ 2) ≤ M u) : 2 * A ≤ m₂ := by
  set g : ℝ → ℝ := fun u => M u - Real.exp (A * u ^ 2) with hgdef
  set g' : ℝ → ℝ := fun u => M' u - 2 * A * u * Real.exp (A * u ^ 2) with hg'def
  have hE : ∀ u : ℝ, HasDerivAt (fun u => Real.exp (A * u ^ 2))
      (2 * A * u * Real.exp (A * u ^ 2)) u := by
    intro u
    have h := ((hasDerivAt_pow 2 u).const_mul A).exp
    convert h using 1
    push_cast
    ring
  have hg : ∀ᶠ u in 𝓝 0, HasDerivAt g (g' u) u :=
    hM.mono fun u hu => hu.sub (hE u)
  have hg0 : g 0 = 0 := by simp [hgdef, hM0]
  have hgnn : ∀ᶠ u in 𝓝 0, 0 ≤ g u := hlow.mono fun u hu => by simp only [hgdef]; linarith
  have hmin : IsLocalMin g 0 := hgnn.mono fun u hu => by rw [hg0]; exact hu
  have hg'0 : g' 0 = 0 := hmin.hasDerivAt_eq_zero hg.self_of_nhds
  have hE' : HasDerivAt (fun u => 2 * A * u * Real.exp (A * u ^ 2)) (2 * A) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * A)).mul (hE 0)
    convert h using 1
    · funext u
      simp only [Pi.mul_apply, id]
    · simp
  have hg'd : HasDerivAt g' (m₂ - 2 * A) 0 := hM'.sub hE'
  by_contra hcon
  push Not at hcon
  have hc : m₂ - 2 * A < 0 := by linarith
  have hslope := hg'd.tendsto_slope_zero_right
  simp only [zero_add, hg'0, sub_zero, smul_eq_mul] at hslope
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * g' t < 0 :=
    hslope.eventually (gt_mem_nhds hc)
  have hneg' : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioi 0 → t⁻¹ * g' t < 0 :=
    eventually_nhdsWithin_iff.1 hneg
  obtain ⟨ε, hε, h₁⟩ := Metric.eventually_nhds_iff.1 (hg.and (hgnn.and hneg'))
  set b := ε / 2 with hb
  have hbpos : 0 < b := by positivity
  have hbε : b < ε := by linarith
  have hin : ∀ x ∈ Icc 0 b, dist x 0 < ε := by
    intro x hx
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    exact lt_of_le_of_lt hx.2 hbε
  have hcont : ContinuousOn g (Icc 0 b) := fun x hx =>
    (h₁ (hin x hx)).1.continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo 0 b, HasDerivAt g (g' x) x := fun x hx =>
    (h₁ (hin x (Ioo_subset_Icc_self hx))).1
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hbpos hcont hderiv
  have hgb : 0 ≤ g b := (h₁ (hin b ⟨hbpos.le, le_rfl⟩)).2.1
  have hξnn : 0 ≤ g' ξ := by
    rw [hξeq, hg0, sub_zero, sub_zero]
    exact div_nonneg hgb hbpos.le
  have hξneg : ξ⁻¹ * g' ξ < 0 :=
    (h₁ (hin ξ (Ioo_subset_Icc_self hξ))).2.2 hξ.1
  have : 0 ≤ ξ⁻¹ * g' ξ := mul_nonneg (inv_nonneg.2 hξ.1.le) hξnn
  linarith

/-- `|x^k e^{u x}| ≤ k! (e^{c x} + e^{-c x})` whenever `|u| + 1 ≤ c`. -/
theorem abs_pow_mul_exp_le (k : ℕ) (x u c : ℝ) (hc : |u| + 1 ≤ c) :
    |x ^ k * Real.exp (u * x)| ≤ k.factorial * (Real.exp (c * x) + Real.exp (-c * x)) := by
  have hpow : |x| ^ k ≤ k.factorial * Real.exp |x| := by
    have h := Real.pow_div_factorial_le_exp _ (abs_nonneg x) k
    rw [div_le_iff₀ (Nat.cast_pos.mpr k.factorial_pos)] at h
    linarith
  have hexp : Real.exp (u * x) ≤ Real.exp (|u| * |x|) := by
    apply Real.exp_le_exp.2
    calc u * x ≤ |u * x| := le_abs_self _
      _ = |u| * |x| := abs_mul u x
  have hsum : Real.exp (c * |x|) ≤ Real.exp (c * x) + Real.exp (-c * x) := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [Real.exp_pos (-c * x)]
    · rw [h, mul_neg, ← neg_mul]; linarith [Real.exp_pos (c * x)]
  have hc' : 0 ≤ c := by linarith [abs_nonneg u]
  calc |x ^ k * Real.exp (u * x)| = |x| ^ k * Real.exp (u * x) := by
        rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    _ ≤ (k.factorial * Real.exp |x|) * Real.exp (|u| * |x|) :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    _ = k.factorial * Real.exp ((|u| + 1) * |x|) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
    _ ≤ k.factorial * Real.exp (c * |x|) := by
        gcongr
    _ ≤ k.factorial * (Real.exp (c * x) + Real.exp (-c * x)) := by
        gcongr

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Integrability of `X^k e^{u X} W` when every exponential moment of `X` is finite and `W` is
bounded. -/
theorem integrable_pow_mul_exp_mul {X W : α → ℝ} (hX : Measurable X)
    (hW : AEStronglyMeasurable W μ) {B : ℝ} (hWB : ∀ x, |W x| ≤ B)
    (hexp : ∀ c : ℝ, Integrable (fun x => Real.exp (c * X x)) μ) (k : ℕ) (u : ℝ) :
    Integrable (fun x => X x ^ k * Real.exp (u * X x) * W x) μ := by
  have hint : Integrable (fun x => B * (k.factorial *
      (Real.exp ((|u| + 1) * X x) + Real.exp (-(|u| + 1) * X x)))) μ :=
    (((hexp _).add (hexp _)).const_mul _).const_mul _
  refine hint.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (((hX.pow_const k).mul ((measurable_const.mul hX).exp)).aestronglyMeasurable).mul hW
  · rw [Real.norm_eq_abs, abs_mul, mul_comm]
    have hB : 0 ≤ B := (abs_nonneg _).trans (hWB x)
    exact mul_le_mul (hWB x) (abs_pow_mul_exp_le k (X x) u _ le_rfl) (abs_nonneg _) hB

/-- Differentiation under the integral: `d/du ∫ X^k e^{u X} W dμ = ∫ X^{k+1} e^{u X} W dμ`. -/
theorem hasDerivAt_integral_pow_mul_exp_mul {X W : α → ℝ} (hX : Measurable X)
    (hW : AEStronglyMeasurable W μ) {B : ℝ} (hWB : ∀ x, |W x| ≤ B)
    (hexp : ∀ c : ℝ, Integrable (fun x => Real.exp (c * X x)) μ) (k : ℕ) (u₀ : ℝ) :
    HasDerivAt (fun u => ∫ x, X x ^ k * Real.exp (u * X x) * W x ∂μ)
      (∫ x, X x ^ (k + 1) * Real.exp (u₀ * X x) * W x ∂μ) u₀ := by
  set c := |u₀| + 2
  have hbound_int : Integrable (fun x => |B| * ((k + 1).factorial *
      (Real.exp (c * X x) + Real.exp (-c * X x)))) μ :=
    (((hexp _).add (hexp _)).const_mul _).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := u₀)
    (F := fun u x => X x ^ k * Real.exp (u * X x) * W x)
    (F' := fun u x => X x ^ (k + 1) * Real.exp (u * X x) * W x)
    (bound := fun x => |B| * ((k + 1).factorial * (Real.exp (c * X x) + Real.exp (-c * X x))))
    (ball_mem_nhds u₀ zero_lt_one) ?_ ?_ ?_ ?_ hbound_int ?_).2
  · exact Filter.Eventually.of_forall fun u =>
      (integrable_pow_mul_exp_mul hX hW hWB hexp k u).aestronglyMeasurable
  · exact integrable_pow_mul_exp_mul hX hW hWB hexp k u₀
  · exact (integrable_pow_mul_exp_mul hX hW hWB hexp (k + 1) u₀).aestronglyMeasurable
  · refine ae_of_all _ fun x u hu => ?_
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    have hu' : |u| + 1 ≤ c := by
      have := abs_sub_abs_le_abs_sub u u₀
      rw [mem_ball, Real.dist_eq] at hu
      simp only [c]
      linarith
    exact mul_le_mul ((hWB x).trans (le_abs_self B)) (abs_pow_mul_exp_le (k + 1) (X x) u c hu')
      (abs_nonneg _) (abs_nonneg B)
  · refine ae_of_all _ fun x u _ => ?_
    have h := (((hasDerivAt_id' u).mul_const (X x)).exp.const_mul (X x ^ k)).mul_const (W x)
    convert h using 1
    ring

end FroehlichSpencer.BKT.Coulomb
