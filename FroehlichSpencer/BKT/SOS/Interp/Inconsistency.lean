/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The literal SOS derivative condition (d) cannot hold

FS81 §7.2 (J p.590) asks for an interpolation `I_β` of `e^{-β|n|}` with
`|d^m/dφ^m log(I_β(φ+ia)/I_β(φ))| ≤ C β^{1/3} g(a)` for `m = 1, 2`, where `g(a) ≤ const·a²` for
small `a` (the `g` of Sect. 6).
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Interp

open Complex Filter Topology

/-- A derivative of a function vanishing at `0` with a quadratic bound near `0` is zero. -/
lemma hasDerivAt_eq_zero_of_norm_le_sq {g : ℝ → ℂ} {g' : ℂ} {C δ : ℝ} (hδ : 0 < δ)
    (hg : HasDerivAt g g' 0) (hg0 : g 0 = 0) (hb : ∀ a : ℝ, |a| ≤ δ → ‖g a‖ ≤ C * a ^ 2) :
    g' = 0 := by
  have h1 := hg.tendsto_slope_zero
  simp only [zero_add, hg0, sub_zero] at h1
  have h2 : Tendsto (fun t : ℝ => t⁻¹ • g t) (𝓝[≠] 0) (𝓝 0) := by
    have hC : Tendsto (fun t : ℝ => C * |t|) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => C * |t|) (𝓝 0) (𝓝 (C * |0|)) :=
        (continuous_const.mul continuous_abs).tendsto 0
      rw [abs_zero, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hC
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| ≤ δ := by
      refine (Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun t ht => ?_⟩).filter_mono
        nhdsWithin_le_nhds
      rw [Real.dist_eq, sub_zero] at ht; exact ht.le
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htne
    rw [norm_smul, norm_inv, Real.norm_eq_abs]
    have htpos : 0 < |t| := abs_pos.mpr htne
    rw [inv_mul_le_iff₀ htpos]
    calc ‖g t‖ ≤ C * t ^ 2 := hb t ht
      _ = |t| * (C * |t|) := by rw [← sq_abs t]; ring
  exact tendsto_nhds_unique h1 h2

/-- FS81 §7.2 condition (d) with a quadratic small-`a` envelope is impossible for every
interpolation of `e^{-β|n|}` that is holomorphic and nonvanishing on a strip . -/
theorem not_literal_derivative_bound {f : ℂ → ℂ} {r β C δ : ℝ} (hr : 0 < r) (hβ : 0 < β)
    (hf : ∀ z : ℂ, |z.im| < r → DifferentiableAt ℂ f z) (hne : ∀ z : ℂ, |z.im| < r → f z ≠ 0)
    (h0 : f 0 = 1) (h1 : f 1 = Real.exp (-β)) (hm1 : f (-1) = Real.exp (-β)) (hδ : 0 < δ)
    (hd : ∀ x a : ℝ, |a| ≤ δ → ‖logDeriv f (x + a * Complex.I) - logDeriv f x‖ ≤ C * a ^ 2) :
    False := by
  set U : Set ℂ := {z : ℂ | |z.im| < r} with hU
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hfU : DifferentiableOn ℂ f U := fun z hz => (hf z hz).differentiableWithinAt
  have hf'U : DifferentiableOn ℂ (deriv f) U := hfU.deriv hUo
  -- the logarithmic derivative is holomorphic on the strip
  have hL : ∀ z ∈ U, DifferentiableAt ℂ (logDeriv f) z := by
    intro z hz
    have hd1 : DifferentiableAt ℂ (deriv f) z := hf'U.differentiableAt (hUo.mem_nhds hz)
    have hfz : DifferentiableAt ℂ f z := hf z hz
    have : logDeriv f = fun w => deriv f w / f w := rfl
    rw [this]
    exact hd1.div hfz (hne z hz)
  have hreal : ∀ t : ℝ, (t : ℂ) ∈ U := fun t => by
    show |((t : ℂ)).im| < r; simpa using hr
  -- `L' = 0` on the real axis
  have hL'0 : ∀ x : ℝ, deriv (logDeriv f) x = 0 := by
    intro x
    have hLx := (hL x (hreal x)).hasDerivAt
    -- along the imaginary direction
    have hline : HasDerivAt (fun a : ℝ => (x : ℂ) + (a : ℂ) * Complex.I) Complex.I 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const Complex.I
      simpa using this.const_add (x : ℂ)
    have hcomp : HasDerivAt (fun a : ℝ => logDeriv f ((x : ℂ) + (a : ℂ) * Complex.I))
        (deriv (logDeriv f) x * Complex.I) 0 := by
      have hLx' : HasDerivAt (logDeriv f) (deriv (logDeriv f) x)
          ((fun a : ℝ => (x : ℂ) + (a : ℂ) * Complex.I) 0) := by simpa using hLx
      exact hLx'.comp (0 : ℝ) hline
    have hsub : HasDerivAt (fun a : ℝ => logDeriv f ((x : ℂ) + (a : ℂ) * Complex.I) -
        logDeriv f x) (deriv (logDeriv f) x * Complex.I) 0 := hcomp.sub_const _
    have hz := hasDerivAt_eq_zero_of_norm_le_sq hδ hsub (by simp) (fun a ha => hd x a ha)
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h Complex.I_ne_zero
  -- hence `L` is constant on the real axis
  set c : ℂ := logDeriv f 0 with hc
  have hLconst : ∀ t : ℝ, logDeriv f t = c := by
    have hdiff : Differentiable ℝ (fun t : ℝ => logDeriv f t) := fun t =>
      ((hL t (hreal t)).hasDerivAt.comp_ofReal).differentiableAt
    have hder : ∀ t : ℝ, deriv (fun t : ℝ => logDeriv f t) t = 0 := fun t => by
      rw [((hL t (hreal t)).hasDerivAt.comp_ofReal).deriv, hL'0 t]
    intro t
    have := is_const_of_deriv_eq_zero hdiff hder t 0
    simpa [hc] using this
  -- `t ↦ f(t) e^{-ct}` is constant
  set h : ℝ → ℂ := fun t => f t * Complex.exp (-(c * t)) with hh
  have hhder : ∀ t : ℝ, HasDerivAt h 0 t := by
    intro t
    have hft : HasDerivAt (fun s : ℝ => f s) (deriv f t) t :=
      ((hf t (hreal t)).hasDerivAt).comp_ofReal
    have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-(c * s))) (Complex.exp (-(c * t)) * (-c)) t := by
      have h1 : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-c) t := by
        have := (((hasDerivAt_id' (t : ℝ)).ofReal_comp).const_mul c).fun_neg
        simpa using this
      exact h1.cexp
    have hprod := hft.mul hexp
    have hfderiv : deriv f t = c * f t := by
      have := hLconst t
      rw [logDeriv_apply, div_eq_iff (hne t (hreal t))] at this
      exact this
    have : deriv f t * Complex.exp (-(c * t)) + f t * (Complex.exp (-(c * t)) * -c) = 0 := by
      rw [hfderiv]; ring
    rw [this] at hprod
    exact hprod
  have hhconst : ∀ t : ℝ, h t = h 0 :=
    fun t => is_const_of_deriv_eq_zero (fun t => (hhder t).differentiableAt)
      (fun t => (hhder t).deriv) t 0
  have e1 : (Real.exp (-β) : ℂ) * Complex.exp (-c) = 1 := by
    have := hhconst 1
    simpa [hh, h0, h1] using this
  have em1 : (Real.exp (-β) : ℂ) * Complex.exp c = 1 := by
    have := hhconst (-1)
    simpa [hh, h0, hm1] using this
  have hprod : ((Real.exp (-β) : ℂ) * (Real.exp (-β) : ℂ)) *
      (Complex.exp (-c) * Complex.exp c) = 1 := by
    calc ((Real.exp (-β) : ℂ) * (Real.exp (-β) : ℂ)) * (Complex.exp (-c) * Complex.exp c)
        = ((Real.exp (-β) : ℂ) * Complex.exp (-c)) * ((Real.exp (-β) : ℂ) * Complex.exp c) := by
          ring
      _ = 1 := by rw [e1, em1, one_mul]
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one, ← Complex.ofReal_mul,
    ← Real.exp_add] at hprod
  have hreal1 : Real.exp (-β + -β) = 1 := by exact_mod_cast hprod
  rw [Real.exp_eq_one_iff] at hreal1
  linarith

end FroehlichSpencer.BKT.SOS.Interp
