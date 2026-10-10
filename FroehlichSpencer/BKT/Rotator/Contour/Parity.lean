/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Contour.Products
import FroehlichSpencer.BKT.Rotator.BesselInterp.Debye
import FroehlichSpencer.BKT.Rotator.BesselInterp.Coeff
import FroehlichSpencer.BKT.Rotator.BesselInterp.Kernel

/-!
# Evenness of the interpolation on the strip and parity of the local functionals

The interpolation `I_β` is even on the whole strip `|Im z| < β`, not only on the real axis: the
principal `sinh⁻¹` is odd there (`w + (1+w²)^{1/2}` has positive real part and
`(−w + (1+w²)^{1/2})(w + (1+w²)^{1/2}) = 1`), so the explicit logarithm `ℓ_β` is even, and the
defect series is even by reindexing `n ↦ −n`. Consequently `i_β(a; −x) = i_β(−a; x)`, and the local
functionals of FS81 (6.18) satisfy Theorem 6.1 (2): `F₁` is odd and `F₂` is even in `∇φ`
(jointly with the direction `θ` of the line).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Contour

open Complex
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-- The principal `sinh⁻¹` is odd on the strip `|Im w| < 1`. -/
lemma carsinh_neg {w : ℂ} (hw : |w.im| < 1) : carsinh (-w) = -carsinh w := by
  unfold carsinh
  set s := (1 + w ^ 2) ^ (1 / 2 : ℂ) with hs
  have hneg : (1 + (-w) ^ 2) ^ (1 / 2 : ℂ) = s := by rw [neg_sq]
  rw [hneg]
  have hre := add_sqrt_re_pos hw
  have hne : w + s ≠ 0 := by
    intro h; rw [h, zero_re] at hre; exact lt_irrefl _ hre
  have hinv : -w + s = (w + s)⁻¹ := by
    have hsq : s ^ 2 = 1 + w ^ 2 := half_cpow_sq _
    refine eq_inv_of_mul_eq_one_left ?_
    linear_combination hsq
  have harg : (w + s).arg ≠ π := by
    intro h
    rw [arg_eq_pi_iff] at h
    linarith [h.1]
  rw [hinv, Complex.log_inv _ harg]

lemma debye_neg {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    debye β (-z) = debye β z := by
  have hw : |(z / β).im| < 1 := im_div_ofReal_lt hβ hz
  unfold debye
  rw [neg_sq, neg_div, carsinh_neg hw]
  ring_nf

lemma logDefect_neg (β : ℝ) (n : ℤ) : logDefect β (-n) = logDefect β n := by
  unfold logDefect
  rw [besselCoeffRe_neg, Int.cast_neg, debyeRe_neg]

lemma defectSeries_neg (β : ℝ) (z : ℂ) : defectSeries β (-z) = defectSeries β z := by
  unfold defectSeries
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply, logDefect_neg, Int.cast_neg]
  rw [show -z - -(n : ℂ) = -(z - n) by ring, sincSq_neg]

/-- `I_β` is even on the strip `|Im z| < β`. -/
theorem besselInterp_neg {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    besselInterp β (-z) = besselInterp β z := by
  unfold besselInterp defectFactor
  rw [debye_neg hβ hz, defectSeries_neg]

/-- `i_β(a; −x) = i_β(−a; x)` for real `x` and `|a| ≤ β/2`. -/
theorem normalizedFactor_neg {β C a : ℝ} (hβ : 0 < β) (ha : |a| ≤ β / 2) (x : ℝ) :
    normalizedFactor β C a (-(x : ℂ)) = normalizedFactor β C (-a) x := by
  unfold normalizedFactor
  have h1 : |((x : ℂ) + ((-a : ℝ) : ℂ) * I).im| < β := by simp; linarith [abs_nonneg a]
  have h0 : |((x : ℂ)).im| < β := by simpa using hβ
  rw [show -(x : ℂ) + a * I = -((x : ℂ) + ((-a : ℝ) : ℂ) * I) by push_cast; ring,
    besselInterp_neg hβ h1, besselInterp_neg hβ h0, cEnvelope_neg]

/-- Parity of the edge products under `(∇φ, θ) ↦ (−∇φ, −θ)`. -/
theorem edgeProduct_neg {ι : Type*} {β C : ℝ} (hβ : 0 < β) (S : Finset ι) (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ : ℝ) :
    edgeProduct β C S a (-x) (-θ) μ = edgeProduct β C S (-a) x θ μ := by
  unfold edgeProduct
  refine Finset.prod_congr rfl fun e he => ?_
  have := normalizedFactor_neg (C := C) hβ (ha e he) (x e + μ * θ e)
  simp only [Pi.neg_apply]
  push_cast at this ⊢
  rw [show -(x e : ℂ) + μ * -(θ e : ℂ) = -((x e : ℂ) + μ * θ e) by ring, this]

/-- FS81 Theorem 6.1 (2): `F₁` is odd. -/
theorem localF₁_neg {ι : Type*} {β C : ℝ} (hβ : 0 < β) (S : Finset ι) (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ : ℝ) :
    localF₁ β C S a (-x) (-θ) μ = -localF₁ β C S a x θ μ := by
  have ha' : ∀ e ∈ S, |(-a) e| ≤ β / 2 := fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he
  unfold localF₁
  rw [edgeProduct_neg hβ S a x θ ha μ, edgeProduct_neg hβ S (-a) x θ ha' μ, neg_neg]
  ring

/-- FS81 Theorem 6.1 (2): `F₂` is even. -/
theorem localF₂_neg {ι : Type*} {β C : ℝ} (hβ : 0 < β) (S : Finset ι) (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ β / 2) (μ : ℝ) :
    localF₂ β C S a (-x) (-θ) μ = localF₂ β C S a x θ μ := by
  have ha' : ∀ e ∈ S, |(-a) e| ≤ β / 2 := fun e he => by rw [Pi.neg_apply, abs_neg]; exact ha e he
  unfold localF₂
  rw [edgeProduct_neg hβ S a x θ ha μ, edgeProduct_neg hβ S (-a) x θ ha' μ, neg_neg]
  ring

end FroehlichSpencer.BKT.Rotator.Contour
