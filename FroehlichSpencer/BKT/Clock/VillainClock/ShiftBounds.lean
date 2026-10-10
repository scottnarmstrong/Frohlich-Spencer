/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Fourier.PeriodizedGaussian
public import FroehlichSpencer.BKT.Generic.LocalFactor
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Real and complex shift bounds for the Villain weight

Symmetrizing the double Gaussian alias series yields a real log-convexity bound.

Taking norms
term by term gives the Gaussian cost for a complex shift.

These are local estimates for a Villain
marked expansion; they do not by themselves prove the clock analogues of FS81 (7.1)(2) or (7.5).
-/

@[expose] public section

open FroehlichSpencer.BKT

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- A real Gaussian alias in the periodized Villain weight. -/
def villainGaussianTerm (β t : ℝ) (m : ℤ) : ℝ :=
  Real.exp (-(β / 2) * (t + 2 * Real.pi * m) ^ 2)

private theorem pairedGaussian_bound (β t s : ℝ) (m n : ℤ) :
    2 * (Real.exp (-β * s ^ 2) *
        (villainGaussianTerm β t m * villainGaussianTerm β t n)) ≤
      villainGaussianTerm β (t + s) m * villainGaussianTerm β (t - s) n +
        villainGaussianTerm β (t + s) n * villainGaussianTerm β (t - s) m := by
  let a := t + 2 * Real.pi * (m : ℝ)
  let b := t + 2 * Real.pi * (n : ℝ)
  let z := β * s * (a - b)
  have hexp : 2 ≤ Real.exp z + Real.exp (-z) := by
    have h₁ := Real.add_one_le_exp z
    have h₂ := Real.add_one_le_exp (-z)
    linarith
  have h₁ : villainGaussianTerm β (t + s) m * villainGaussianTerm β (t - s) n =
      (Real.exp (-β * s ^ 2) *
        (villainGaussianTerm β t m * villainGaussianTerm β t n)) * Real.exp (-z) := by
    simp only [villainGaussianTerm, a, b, z, ← Real.exp_add]
    congr 1
    ring_nf
  have h₂ : villainGaussianTerm β (t + s) n * villainGaussianTerm β (t - s) m =
      (Real.exp (-β * s ^ 2) *
        (villainGaussianTerm β t m * villainGaussianTerm β t n)) * Real.exp z := by
    simp only [villainGaussianTerm, a, b, z, ← Real.exp_add]
    congr 1
    ring_nf
  rw [h₁, h₂]
  have hbase : 0 ≤ Real.exp (-β * s ^ 2) *
      (villainGaussianTerm β t m * villainGaussianTerm β t n) := by
    exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hexp hbase]

/-- Symmetric shifts of the periodized Gaussian dominate its unshifted square, with exact
Gaussian curvature `β s²`. -/
theorem villainWeight_shift_product (β t s : ℝ) (hβ : 0 < β) :
    Real.exp (-β * s ^ 2) * villainWeight β t ^ 2 ≤
      villainWeight β (t + s) * villainWeight β (t - s) := by
  let f : ℤ → ℝ := villainGaussianTerm β t
  let fp : ℤ → ℝ := villainGaussianTerm β (t + s)
  let fm : ℤ → ℝ := villainGaussianTerm β (t - s)
  let A : ℤ × ℤ → ℝ := fun p => fp p.1 * fm p.2
  let B : ℤ × ℤ → ℝ := fun p => fp p.2 * fm p.1
  let C : ℝ := Real.exp (-β * s ^ 2)
  have hf : Summable f := by
    exact (VillainWeight.villainWeight_summable hβ t).congr fun m => rfl
  have hfp : Summable fp := by
    exact (VillainWeight.villainWeight_summable hβ (t + s)).congr fun m => rfl
  have hfm : Summable fm := by
    exact (VillainWeight.villainWeight_summable hβ (t - s)).congr fun m => rfl
  have hff : Summable (fun p : ℤ × ℤ => f p.1 * f p.2) :=
    hf.mul_of_nonneg hf (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hA : Summable A := by
    dsimp [A]
    exact hfp.mul_of_nonneg hfm (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hB : Summable B := by
    simpa [A, B, Function.comp_def] using
      (Equiv.prodComm ℤ ℤ).summable_iff.mpr hA
  have hAB : Summable (fun p : ℤ × ℤ => A p + B p) := hA.add hB
  have hpoint (p : ℤ × ℤ) :
      2 * (C * (f p.1 * f p.2)) ≤ A p + B p := by
    simpa [A, B, C, f, fp, fm] using pairedGaussian_bound β t s p.1 p.2
  have hlowSummable : Summable (fun p : ℤ × ℤ => 2 * (C * (f p.1 * f p.2))) := by
    exact (hff.mul_left (2 * C)).congr fun p => by ring
  have hsum := hlowSummable.tsum_le_tsum hpoint hAB
  have hAprod : (∑' m : ℤ, fp m) * (∑' n : ℤ, fm n) = ∑' p : ℤ × ℤ, A p :=
    hfp.tsum_mul_tsum hfm hA
  have hBsum : (∑' p : ℤ × ℤ, B p) = ∑' p : ℤ × ℤ, A p := by
    simpa [A, B] using (Equiv.prodComm ℤ ℤ).tsum_eq (fun p : ℤ × ℤ => A p)
  have hffprod : (∑' m : ℤ, f m) * (∑' n : ℤ, f n) =
      ∑' p : ℤ × ℤ, f p.1 * f p.2 := hf.tsum_mul_tsum hf hff
  have hsumAB : (∑' p : ℤ × ℤ, (A p + B p)) =
      2 * ((∑' m : ℤ, fp m) * (∑' n : ℤ, fm n)) := by
    rw [hA.tsum_add hB, hBsum, hAprod]
    ring
  have hsumlow : (∑' p : ℤ × ℤ, (2 * (C * (f p.1 * f p.2)))) =
      2 * (C * ((∑' m : ℤ, f m) ^ 2)) := by
    calc
      _ = ∑' p : ℤ × ℤ, ((2 * C) * (f p.1 * f p.2)) := by
        apply tsum_congr
        intro p
        ring
      _ = (2 * C) * (∑' p : ℤ × ℤ, f p.1 * f p.2) :=
        Summable.tsum_mul_left (2 * C) hff
      _ = 2 * (C * ((∑' m : ℤ, f m) ^ 2)) := by rw [← hffprod]; ring
  have hv : (∑' m : ℤ, f m) = villainWeight β t := by rfl
  have hvp : (∑' m : ℤ, fp m) = villainWeight β (t + s) := by rfl
  have hvm : (∑' m : ℤ, fm m) = villainWeight β (t - s) := by rfl
  rw [hsumlow, hsumAB] at hsum
  rw [← hv, ← hvp, ← hvm]
  dsimp [C] at hsum ⊢
  nlinarith [hsum]

/-- One complex Gaussian alias for real part `t` and imaginary part `u`. -/
def villainComplexTerm (β t u : ℝ) (m : ℤ) : ℂ :=
  Complex.exp (-(β / 2 : ℝ) * (((t : ℂ) + (u : ℂ) * Complex.I) + (2 * Real.pi * m : ℝ)) ^ 2)

/-- The periodized Gaussian evaluated at `t + i u`. -/
def villainComplexWeight (β t u : ℝ) : ℂ :=
  ∑' m : ℤ, villainComplexTerm β t u m

/-- On the real axis the complex alias sum is the original Villain weight. -/
theorem villainComplexWeight_real_eq (β t : ℝ) :
    villainComplexWeight β t 0 = (villainWeight β t : ℂ) := by
  rw [villainComplexWeight, villainWeight, Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  simp [villainComplexTerm]

/-- The norm of a complex alias is its real Gaussian factor times the imaginary-shift cost. -/
theorem villainComplexTerm_norm (β t u : ℝ) (m : ℤ) :
    ‖villainComplexTerm β t u m‖ =
      Real.exp (β * u ^ 2 / 2) * villainGaussianTerm β t m := by
  rw [villainComplexTerm, Complex.norm_exp]
  let x : ℝ := t + 2 * Real.pi * m
  let w : ℂ := (x : ℂ) + (u : ℂ) * Complex.I
  have hwre : w.re = x := by simp [w]
  have hwim : w.im = u := by simp [w]
  have hsq : (w ^ 2).re = x ^ 2 - u ^ 2 := by
    rw [pow_two, Complex.mul_re, hwre, hwim]
    ring
  have hre :
      (-(β / 2 : ℝ) * (((t : ℂ) + (u : ℂ) * Complex.I) + (2 * Real.pi * m : ℝ)) ^ 2).re =
        β * u ^ 2 / 2 - (β / 2) * x ^ 2 := by
    rw [show (((t : ℂ) + (u : ℂ) * Complex.I) + (2 * Real.pi * m : ℝ)) = w by
      simp only [w, x, Complex.ofReal_add, Complex.ofReal_mul]
      ring]
    rw [Complex.mul_re]
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
      neg_zero, zero_mul, sub_zero]
    rw [hsq]
    ring
  rw [hre]
  rw [villainGaussianTerm]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The complex alias series is absolutely summable for every real and imaginary shift. -/
theorem villainComplexTerm_norm_summable (β t u : ℝ) (hβ : 0 < β) :
    Summable (fun m : ℤ => ‖villainComplexTerm β t u m‖) := by
  have hf : Summable (villainGaussianTerm β t) := by
    exact (VillainWeight.villainWeight_summable hβ t).congr fun m => rfl
  exact (Summable.mul_left (Real.exp (β * u ^ 2 / 2)) hf).congr fun m =>
    (villainComplexTerm_norm β t u m).symm

/-- The complex periodized Gaussian obeys the sharp Gaussian cost for an imaginary shift. -/
theorem villainComplexWeight_norm_le (β t u : ℝ) (hβ : 0 < β) :
    ‖villainComplexWeight β t u‖ ≤ Real.exp (β * u ^ 2 / 2) * villainWeight β t := by
  calc
    _ ≤ ∑' m : ℤ, ‖villainComplexTerm β t u m‖ :=
      norm_tsum_le_tsum_norm (villainComplexTerm_norm_summable β t u hβ)
    _ = ∑' m : ℤ, Real.exp (β * u ^ 2 / 2) * villainGaussianTerm β t m := by
      apply tsum_congr
      intro m
      exact villainComplexTerm_norm β t u m
    _ = Real.exp (β * u ^ 2 / 2) * villainWeight β t := by
      rw [tsum_mul_left]
      simp [villainWeight, villainGaussianTerm]

/-- Dividing the complex shift by the positive real Villain weight leaves only the Gaussian
imaginary-shift cost. -/
theorem villainComplexWeight_ratio_norm_le (β t u : ℝ) (hβ : 0 < β) :
    ‖villainComplexWeight β t u / (villainWeight β t : ℂ)‖ ≤ Real.exp (β * u ^ 2 / 2) := by
  have hden : 0 < villainWeight β t := VillainWeight.villainWeight_pos hβ t
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using villainComplexWeight_norm_le β t u hβ)

/-- The same ratio estimate when the imaginary shift has the normalized clock scale `u / n`. -/
theorem villainComplexWeight_scaledRatio_norm_le (β t u n : ℝ) (hβ : 0 < β) (hn : 0 < n) :
    ‖villainComplexWeight β t (u / n) / (villainWeight β t : ℂ)‖ ≤
      Real.exp (β * u ^ 2 / (2 * n ^ 2)) := by
  calc
    _ ≤ Real.exp (β * (u / n) ^ 2 / 2) := villainComplexWeight_ratio_norm_le β t (u / n) hβ
    _ = Real.exp (β * u ^ 2 / (2 * n ^ 2)) := by
      congr 1
      field_simp [ne_of_gt hn]

/-- The Villain edge weight on the compact angle scale `φ = n θ`. -/
def villainClockEdgeWeight (β n : ℝ) (z : ℂ) : ℂ :=
  villainComplexWeight β (z.re / n) (z.im / n)

/-- The quadratic local translation cost corresponding to the Villain clock weight. -/
def villainClockShiftCost (β n u : ℝ) : ℝ := β * u ^ 2 / (2 * n ^ 2)

/-- The compact Villain edge weight restricts to the periodized Gaussian on real angles. -/
theorem villainClockEdgeWeight_ofReal (β n t : ℝ) :
    villainClockEdgeWeight β n t = (villainWeight β (t / n) : ℂ) := by
  rw [villainClockEdgeWeight, Complex.ofReal_re, Complex.ofReal_im, zero_div,
    villainComplexWeight_real_eq]

/-- The real Villain clock edge weight is nonzero at positive inverse temperature. -/
theorem villainClockEdgeWeight_ofReal_ne_zero (β n t : ℝ) (hβ : 0 < β) :
    villainClockEdgeWeight β n t ≠ 0 := by
  rw [villainClockEdgeWeight_ofReal]
  exact_mod_cast (VillainWeight.villainWeight_pos hβ (t / n)).ne'

/-- On the real axis the compact Villain edge weight has period `2πn`. -/
theorem villainClockEdgeWeight_add_period (β n t : ℝ) (hn : 0 < n) :
    villainClockEdgeWeight β n ((t + 2 * Real.pi * n : ℝ) : ℂ) =
      villainClockEdgeWeight β n (t : ℂ) := by
  rw [villainClockEdgeWeight_ofReal, villainClockEdgeWeight_ofReal]
  congr 1
  rw [show (t + 2 * Real.pi * n) / n = t / n + 2 * Real.pi by
    field_simp [ne_of_gt hn]]
  exact VillainWeight.villainWeight_add_two_pi β (t / n)

/-- The normalized Villain clock edge ratio has the exact quadratic cost required by the local
factor estimate. -/
theorem villainClockEdgeWeight_ratio_le (β n t u : ℝ) (hβ : 0 < β) (hn : 0 < n) :
    ‖villainClockEdgeWeight β n ((t : ℂ) + (u : ℂ) * Complex.I) /
        villainClockEdgeWeight β n t‖ ≤ Real.exp (villainClockShiftCost β n u) := by
  have hnum : villainClockEdgeWeight β n ((t : ℂ) + (u : ℂ) * Complex.I) =
      villainComplexWeight β (t / n) (u / n) := by
    simp [villainClockEdgeWeight]
  have hden : villainClockEdgeWeight β n t = (villainWeight β (t / n) : ℂ) :=
    villainClockEdgeWeight_ofReal β n t
  rw [hnum, hden, villainClockShiftCost]
  exact villainComplexWeight_scaledRatio_norm_le β (t / n) u n hβ hn

/-- Complex conjugation of the Villain series changes the sign of its imaginary shift. -/
theorem villainComplexWeight_conj_imag (β t u : ℝ) :
    villainComplexWeight β t (-u) = starRingEnd ℂ (villainComplexWeight β t u) := by
  unfold villainComplexWeight
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro m
  rw [villainComplexTerm, villainComplexTerm, ← Complex.exp_conj]
  congr 1
  simp only [map_pow, map_mul, map_neg, map_add, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring_nf

/-- The compact Villain edge weight commutes with complex conjugation. -/
theorem villainClockEdgeWeight_conj (β n : ℝ) (z : ℂ) :
    starRingEnd ℂ (villainClockEdgeWeight β n z) =
      villainClockEdgeWeight β n (starRingEnd ℂ z) := by
  simp only [villainClockEdgeWeight, Complex.conj_re, Complex.conj_im, neg_div]
  exact (villainComplexWeight_conj_imag β (z.re / n) (z.im / n)).symm

/-- The local Villain translation cost is even. -/
theorem villainClockShiftCost_even (β n : ℝ) (u : ℝ) :
    villainClockShiftCost β n (-u) = villainClockShiftCost β n u := by
  simp [villainClockShiftCost]

/-- Villain local factors are bounded by one, using the Gaussian complex-shift ratio estimate. -/
theorem villainClockLocalFactor_norm_le_one {E : Type*} [Fintype E]
    (β n : ℝ) (hβ : 0 < β) (hn : 0 < n) {W : ℝ} (b x : E → ℝ)
    (hb : ∀ e, |b e| ≤ W) (θ : ℝ) :
    ‖FroehlichSpencer.BKT.Generic.localFactor (villainClockEdgeWeight β n)
      (villainClockShiftCost β n) b x θ‖ ≤ 1 := by
  exact FroehlichSpencer.BKT.Generic.norm_localFactor_le_one
    (w := villainClockEdgeWeight β n) (c := villainClockShiftCost β n) (W := W)
    (fun t u _ => villainClockEdgeWeight_ratio_le β n t u hβ hn) b x hb θ

/-- Villain local factors are real on real base points, by conjugation symmetry and the even
quadratic shift cost. -/
theorem villainClockLocalFactor_im_eq_zero {E : Type*} [Fintype E]
    (β n : ℝ) {W : ℝ} (b x : E → ℝ)
    (hb : ∀ e, |b e| ≤ W) (θ : ℝ) :
    (FroehlichSpencer.BKT.Generic.localFactor (villainClockEdgeWeight β n)
      (villainClockShiftCost β n) b x θ).im = 0 := by
  exact FroehlichSpencer.BKT.Generic.localFactor_im_eq_zero
    (w := villainClockEdgeWeight β n) (c := villainClockShiftCost β n) (W := W)
    (fun z _ => villainClockEdgeWeight_conj β n z) (villainClockShiftCost_even β n)
    b x hb θ

/-- With no contour wave, the Villain local factor is exactly the real cosine character. -/
theorem villainClockLocalFactor_zero {E : Type*} [Fintype E]
    (β n : ℝ) (hβ : 0 < β) (x : E → ℝ) (θ : ℝ) :
    FroehlichSpencer.BKT.Generic.localFactor (villainClockEdgeWeight β n)
      (villainClockShiftCost β n) 0 x θ = Real.cos θ := by
  apply FroehlichSpencer.BKT.Generic.localFactor_zero
  · simp [villainClockShiftCost]
  · intro e
    exact villainClockEdgeWeight_ofReal_ne_zero β n (x e) hβ

end FroehlichSpencer.BKT.Clock.VillainClock

end
