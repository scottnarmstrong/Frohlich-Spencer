/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.StripWeight
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.FiniteGraph.Basic

/-!
# The real shift of the edge weights, and symmetrization (generic core)

* **Real shift (6.28).** For a strip weight with the one-sided curvature bound
  `log w(t + s) ≥ log w(t) + (log w)'(t) s − κ s²` (`HasCurvatureBound`), shifting every edge
  gradient by a real `θ(e)` multiplies the edge product by at least
  `exp(H₀ − κ‖θ‖²)` with `H₀ = ∑_e Re (log w)'(∇φ(e)) θ(e)` (`prod_re_shift_ge`).

Since `w` is
  even, `(log w)'` is odd on the real axis (`logDeriv_neg_ofReal`), so `H₀` is odd in the field
  (`edgeShiftExponent_neg`).
* **Symmetrization (6.38)–(6.39).** If `I(φ) ≥ e^{−R} f(φ) e^{H(φ)}` with `f ≥ 0` even (a.e.),
  `H` odd and `I, f` integrable, then `∫ I ≥ e^{−R} ∫ f` (`integral_ge_of_odd_exponent`): average
  `I(φ)` and `I(−φ)` and use `cosh ≥ 1`.

No integrability or measurability of `e^{H}` is needed;
  Lebesgue measure on `V → ℝ` is invariant under `φ ↦ −φ` (`measurePreserving_neg_pi`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Filter Topology

/-! ## Oddness of the logarithmic derivative -/

/-- `(log w)'` is odd on the real axis for an even strip weight of positive width. -/
theorem logDeriv_neg_ofReal {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c)
    (hW : 0 < W) (x : ℝ) : logDeriv w ((-x : ℝ) : ℂ) = -logDeriv w (x : ℂ) := by
  have hx : |((x : ℂ)).im| ≤ W := by simpa using hW.le
  have hnx : |(((-x : ℝ) : ℂ)).im| ≤ W := by simpa using hW.le
  have hdiffx : DifferentiableAt ℂ w (x : ℂ) := (hw.analyticAt _ hx).differentiableAt
  have hdiffnx : DifferentiableAt ℂ w (((-x : ℝ) : ℂ)) := (hw.analyticAt _ hnx).differentiableAt
  -- `w(-z) = w(z)` near the real point `x`
  have hev : (fun z : ℂ => w (-z)) =ᶠ[𝓝 (x : ℂ)] w := by
    have hopen : IsOpen {z : ℂ | |z.im| < W} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    filter_upwards [hopen.mem_nhds (by simpa using hW)] with z hz
    exact hw.even z (le_of_lt hz)
  have hd : deriv (fun z : ℂ => w (-z)) (x : ℂ) = deriv w (x : ℂ) := hev.deriv_eq
  have hdiffnx' : DifferentiableAt ℂ w (-(x : ℂ)) := by
    have h := hdiffnx
    rwa [show ((-x : ℝ) : ℂ) = -(x : ℂ) by push_cast; ring] at h
  have hchain : deriv (fun z : ℂ => w (-z)) (x : ℂ) = -deriv w (-(x : ℂ)) := by
    have h := hdiffnx'.hasDerivAt.comp (x : ℂ) (hasDerivAt_neg (x : ℂ))
    simpa [Function.comp_def] using h.deriv
  have hwx : w (((-x : ℝ) : ℂ)) = w (x : ℂ) := by
    rw [show ((-x : ℝ) : ℂ) = -(x : ℂ) by push_cast; ring]
    exact hw.even _ hx
  unfold logDeriv
  simp only [Pi.div_apply]
  rw [hwx, show ((-x : ℝ) : ℂ) = -(x : ℂ) by push_cast; ring]
  have : deriv w (-(x : ℂ)) = -deriv w (x : ℂ) := by rw [← hd, hchain, neg_neg]
  rw [this, neg_div]

/-! ## The real shift of the edge weights -/

/-- One edge: `Re w(t + s) ≥ Re w(t) · exp(Re (log w)'(t) s − κ s²)`. -/
theorem re_shift_ge {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) {κ : ℝ}
    (hcurv : HasCurvatureBound w κ) (t s : ℝ) :
    (w (t : ℂ)).re * Real.exp ((logDeriv w (t : ℂ)).re * s - κ * s ^ 2) ≤
      (w ((t + s : ℝ) : ℂ)).re := by
  have hpos := hw.ofReal_re_pos t
  have hpos' := hw.ofReal_re_pos (t + s)
  have h := hcurv t s
  have h2 := Real.exp_le_exp.mpr h
  rw [Real.exp_log hpos'] at h2
  calc (w (t : ℂ)).re * Real.exp ((logDeriv w (t : ℂ)).re * s - κ * s ^ 2)
      = Real.exp (Real.log (w (t : ℂ)).re + (logDeriv w (t : ℂ)).re * s - κ * s ^ 2) := by
        rw [add_sub_assoc, Real.exp_add, Real.exp_log hpos]
    _ ≤ (w ((t + s : ℝ) : ℂ)).re := h2

/-- **FS81 (6.28), summed over the edges**: the shifted edge product dominates
`∏_e Re w(x_e) · exp(∑_e Re (log w)'(x_e) θ_e − κ ∑_e θ_e²)`. -/
theorem prod_re_shift_ge {E : Type*} [Fintype E] {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
    (hw : IsStripWeight w W c) {κ : ℝ} (hcurv : HasCurvatureBound w κ) (x θ : E → ℝ) :
    (∏ e, (w (x e : ℂ)).re) *
        Real.exp (∑ e, (logDeriv w (x e : ℂ)).re * θ e - κ * ∑ e, θ e ^ 2) ≤
      ∏ e, (w ((x e + θ e : ℝ) : ℂ)).re := by
  have hsplit : Real.exp (∑ e, (logDeriv w (x e : ℂ)).re * θ e - κ * ∑ e, θ e ^ 2) =
      ∏ e, Real.exp ((logDeriv w (x e : ℂ)).re * θ e - κ * θ e ^ 2) := by
    rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun e _ => mul_nonneg (hw.ofReal_re_pos _).le (Real.exp_pos _).le)
    fun e _ => re_shift_ge hw hcurv (x e) (θ e)

/-- The first-order exponent of the real shift, `H₀(φ) = ∑_e Re (log w)'(∇φ(e)) θ(e)`. -/
def edgeShiftExponent {V E : Type*} [Fintype E] (G : Multigraph V E) (w : ℂ → ℂ) (θ : E → ℝ)
    (φ : V → ℝ) : ℝ :=
  ∑ e, (logDeriv w ((G.grad φ e : ℝ) : ℂ)).re * θ e

/-- `H₀` is odd in the field. -/
theorem edgeShiftExponent_neg {V E : Type*} [Fintype E] {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
    (hw : IsStripWeight w W c) (hW : 0 < W) (G : Multigraph V E) (θ : E → ℝ) (φ : V → ℝ) :
    edgeShiftExponent G w θ (-φ) = -edgeShiftExponent G w θ φ := by
  unfold edgeShiftExponent
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hg : G.grad (-φ) e = -G.grad φ e := by
    simp only [Multigraph.grad, Pi.neg_apply]; ring
  rw [hg, logDeriv_neg_ofReal hw hW, Complex.neg_re, neg_mul]

/-! ## Symmetrization -/

/-- Lebesgue measure on `V → ℝ` is invariant under `φ ↦ −φ`. -/
theorem measurePreserving_neg_pi {V : Type*} [Fintype V] [DecidableEq V] :
    MeasurePreserving (fun φ : V → ℝ => -φ) (volume : Measure (V → ℝ)) volume := by
  have hlin : (fun φ : V → ℝ => -φ) =
      ⇑((-1 : ℝ) • LinearMap.id : (V → ℝ) →ₗ[ℝ] (V → ℝ)) := by
    funext φ; simp
  have hdet : LinearMap.det ((-1 : ℝ) • LinearMap.id : (V → ℝ) →ₗ[ℝ] (V → ℝ)) =
      (-1) ^ Fintype.card V := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fintype_fun_eq_card]
  have hne : LinearMap.det ((-1 : ℝ) • LinearMap.id : (V → ℝ) →ₗ[ℝ] (V → ℝ)) ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (by norm_num)
  refine ⟨measurable_neg, ?_⟩
  rw [hlin, Real.map_linearMap_volume_pi_eq_smul_volume_pi hne, hdet, abs_inv, abs_pow,
    abs_neg, abs_one, one_pow, inv_one, ENNReal.ofReal_one, one_smul]

/-- `∫ g(−φ) dφ = ∫ g(φ) dφ` on `V → ℝ`. -/
theorem integral_comp_neg_pi {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℝ) → ℝ) :
    ∫ φ, g (-φ) = ∫ φ, g φ :=
  (measurePreserving_neg_pi).integral_comp (Homeomorph.neg (V → ℝ)).measurableEmbedding g

/-- **Symmetrization (FS81 (6.38)–(6.39)).** If `e^{−R} f e^{H} ≤ I` pointwise, `f ≥ 0` is even
almost everywhere, `H` is odd, and `I`, `f` are integrable, then `e^{−R} ∫ f ≤ ∫ I`. -/
theorem integral_ge_of_odd_exponent {V : Type*} [Fintype V] [DecidableEq V]
    {I f H : (V → ℝ) → ℝ} (R : ℝ) (hI : Integrable I) (hf : Integrable f)
    (hf0 : ∀ φ, 0 ≤ f φ) (hfeven : ∀ᵐ φ, f (-φ) = f φ) (hHodd : ∀ φ, H (-φ) = -H φ)
    (hle : ∀ φ, Real.exp (-R) * (f φ * Real.exp (H φ)) ≤ I φ) :
    Real.exp (-R) * ∫ φ, f φ ≤ ∫ φ, I φ := by
  have hIneg : Integrable fun φ => I (-φ) :=
    (measurePreserving_neg_pi.integrable_comp_emb
      (Homeomorph.neg (V → ℝ)).measurableEmbedding).mpr hI
  have hsym : ∫ φ, I φ = (1 / 2 : ℝ) * ∫ φ, (I φ + I (-φ)) := by
    rw [integral_add hI hIneg, integral_comp_neg_pi I]; ring
  rw [hsym, ← integral_const_mul, ← integral_const_mul]
  refine integral_mono_ae (hf.const_mul _) ((hI.add hIneg).const_mul _) ?_
  filter_upwards [hfeven] with φ hφ
  have h1 := hle φ
  have h2 := hle (-φ)
  rw [hφ, hHodd φ] at h2
  have hcosh : 2 ≤ Real.exp (H φ) + Real.exp (-H φ) := by
    linarith [Real.add_one_le_exp (H φ), Real.add_one_le_exp (-H φ)]
  have hR := Real.exp_pos (-R)
  have hf0φ := hf0 φ
  show Real.exp (-R) * f φ ≤ 1 / 2 * (I φ + I (-φ))
  nlinarith [mul_le_mul_of_nonneg_left hcosh (mul_nonneg hR.le hf0φ)]

end FroehlichSpencer.BKT.Generic

end
