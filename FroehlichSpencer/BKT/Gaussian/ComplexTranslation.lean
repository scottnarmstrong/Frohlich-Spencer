/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.Normalization
public import FroehlichSpencer.BKT.FiniteGraph.Laplacian
public import FroehlichSpencer.BKT.FiniteGraph.Green
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complex translation of the pinned finite-volume GFF

The one-variable contour identity is KP Lemma 4.8, p. 29, extended to
nonempty finite families of complex centers as required by successive shifts.
The multivariate identity is KP (2.19), p. 13, with `Eβ` as in (2.12), p. 10.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace FroehlichSpencer.BKT

/-! ## One-variable contour translation -/

/-- The one-variable complex Gaussian with a finite family of centers. -/
def complexGaussianContourWeight {ι : Type*} (centers : Finset ι)
    (xj : ι → ℂ) (β q : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (q : ℂ) * z) *
    Complex.exp (-((β : ℂ) / 2) * ∑ j ∈ centers, (z - xj j) ^ 2)

private theorem complexGaussian_center_square_sum {ι : Type*}
    (centers : Finset ι) (xj : ι → ℂ) (z : ℂ) :
    (∑ j ∈ centers, (z - xj j) ^ 2) =
      (centers.card : ℂ) * z ^ 2 - 2 * z * (∑ j ∈ centers, xj j) +
        ∑ j ∈ centers, (xj j) ^ 2 := by
  calc
    (∑ j ∈ centers, (z - xj j) ^ 2) =
        ∑ j ∈ centers, (z ^ 2 + (-2 * z * xj j) + (xj j) ^ 2) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ j ∈ centers, z ^ 2) +
        (∑ j ∈ centers, (-2 * z * xj j)) +
        ∑ j ∈ centers, (xj j) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (centers.card : ℂ) * z ^ 2 -
        2 * z * (∑ j ∈ centers, xj j) +
        ∑ j ∈ centers, (xj j) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [show (∑ j ∈ centers, (-2 * z * xj j)) =
              (-2 * z) * (∑ j ∈ centers, xj j) by
                rw [Finset.mul_sum]]
          ring

private def complexGaussianQuadraticB {ι : Type*} (centers : Finset ι)
    (β : ℝ) : ℂ := (-(β * (centers.card : ℝ) / 2) : ℂ)

private def complexGaussianQuadraticC {ι : Type*} (centers : Finset ι)
    (xj : ι → ℂ) (β q : ℝ) : ℂ :=
  Complex.I * (q : ℂ) + (β : ℂ) * ∑ j ∈ centers, xj j

private def complexGaussianQuadraticD {ι : Type*} (centers : Finset ι)
    (xj : ι → ℂ) (β : ℝ) : ℂ :=
  -((β : ℂ) / 2) * ∑ j ∈ centers, (xj j) ^ 2

private theorem complexGaussianContourWeight_eq_quadratic {ι : Type*}
    (centers : Finset ι) (xj : ι → ℂ) (β q : ℝ) (z : ℂ) :
    complexGaussianContourWeight centers xj β q z =
      Complex.exp (complexGaussianQuadraticB centers β * z ^ 2 +
        complexGaussianQuadraticC centers xj β q * z +
        complexGaussianQuadraticD centers xj β) := by
  rw [complexGaussianContourWeight, ← Complex.exp_add,
    complexGaussian_center_square_sum]
  simp only [complexGaussianQuadraticB, complexGaussianQuadraticC,
    complexGaussianQuadraticD]
  push_cast
  ring_nf

/-- Translating the line of integration for any decaying complex quadratic.
Mathlib's `integral_cexp_quadratic` proves this formula by the rectangular
Cauchy theorem and vanishing vertical sides. -/
private theorem integral_cexp_quadratic_im_shift {b c d : ℂ} (hb : b.re < 0)
    (a : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (b * (x : ℂ) ^ 2 + c * x + d))
        (volume : Measure ℝ) ∧
    Integrable (fun x : ℝ => Complex.exp
      (b * ((x : ℂ) + Complex.I * a) ^ 2 +
        c * ((x : ℂ) + Complex.I * a) + d)) (volume : Measure ℝ) ∧
    (∫ x : ℝ, Complex.exp (b * (x : ℂ) ^ 2 + c * x + d)) =
      ∫ x : ℝ, Complex.exp
        (b * ((x : ℂ) + Complex.I * a) ^ 2 +
          c * ((x : ℂ) + Complex.I * a) + d) := by
  let c' := c + 2 * Complex.I * (a : ℂ) * b
  let d' := d + Complex.I * (a : ℂ) * c - (a : ℂ) ^ 2 * b
  have hbne : b ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hb
    exact (not_lt_of_ge (le_refl 0)) hb
  have htranslate (x : ℝ) :
      b * ((x : ℂ) + Complex.I * a) ^ 2 +
          c * ((x : ℂ) + Complex.I * a) + d =
        b * (x : ℂ) ^ 2 + c' * x + d' := by
    dsimp [c', d']
    ring_nf
    rw [Complex.I_sq]
    ring
  have hleft := integrable_cexp_quadratic' hb c d
  have hrightPoly := integrable_cexp_quadratic' hb c' d'
  have hright : Integrable (fun x : ℝ => Complex.exp
      (b * ((x : ℂ) + Complex.I * a) ^ 2 +
        c * ((x : ℂ) + Complex.I * a) + d)) (volume : Measure ℝ) :=
    hrightPoly.congr (Filter.Eventually.of_forall fun x => by
      change Complex.exp (b * (x : ℂ) ^ 2 + c' * x + d') =
        Complex.exp (b * ((x : ℂ) + Complex.I * a) ^ 2 +
          c * ((x : ℂ) + Complex.I * a) + d)
      exact congrArg Complex.exp (htranslate x).symm)
  have hformulaLeft := integral_cexp_quadratic hb c d
  have hformulaRight := integral_cexp_quadratic hb c' d'
  have hexp : d - c ^ 2 / (4 * b) = d' - c' ^ 2 / (4 * b) := by
    dsimp [c', d']
    field_simp [hbne]
    ring_nf
    rw [Complex.I_sq]
    ring
  refine ⟨hleft, hright, ?_⟩
  calc
    (∫ x : ℝ, Complex.exp (b * (x : ℂ) ^ 2 + c * x + d)) =
        (Real.pi / -b) ^ (1 / 2 : ℂ) * Complex.exp (d - c ^ 2 / (4 * b)) :=
          hformulaLeft
    _ = (Real.pi / -b) ^ (1 / 2 : ℂ) *
        Complex.exp (d' - c' ^ 2 / (4 * b)) := by rw [hexp]
    _ = ∫ x : ℝ, Complex.exp
        (b * ((x : ℂ) + Complex.I * a) ^ 2 +
          c * ((x : ℂ) + Complex.I * a) + d) := by
            calc
              (Real.pi / -b) ^ (1 / 2 : ℂ) *
                  Complex.exp (d' - c' ^ 2 / (4 * b)) =
                ∫ x : ℝ, Complex.exp (b * (x : ℂ) ^ 2 + c' * x + d') :=
                  hformulaRight.symm
              _ = ∫ x : ℝ, Complex.exp
                  (b * ((x : ℂ) + Complex.I * a) ^ 2 +
                    c * ((x : ℂ) + Complex.I * a) + d) := by
                  apply integral_congr_ae
                  exact Filter.Eventually.of_forall fun x =>
                    congrArg Complex.exp (htranslate x).symm

/-- KP Lemma 4.8 (4.36), p. 29, with the complex-center extension needed
for iterated translations. The finite family is represented by a nonempty
finset, so the Gaussian is integrable on both horizontal lines. -/
theorem complexGaussian_contour_shift {ι : Type*} [DecidableEq ι]
    (centers : Finset ι) (hcenters : centers.Nonempty) (xj : ι → ℂ)
    (β q a : ℝ) (hβ : 0 < β) :
    Integrable (fun x : ℝ =>
      complexGaussianContourWeight centers xj β q (x : ℂ))
        (volume : Measure ℝ) ∧
    Integrable (fun x : ℝ => complexGaussianContourWeight centers xj β q
      ((x : ℂ) + Complex.I * a)) (volume : Measure ℝ) ∧
    (∫ x : ℝ, complexGaussianContourWeight centers xj β q (x : ℂ)) =
      ∫ x : ℝ, complexGaussianContourWeight centers xj β q
        ((x : ℂ) + Complex.I * a) := by
  let b := complexGaussianQuadraticB centers β
  let c := complexGaussianQuadraticC centers xj β q
  let d := complexGaussianQuadraticD centers xj β
  have hcard : 0 < centers.card := Finset.card_pos.mpr hcenters
  have hb : b.re < 0 := by
    dsimp [b, complexGaussianQuadraticB]
    have hcardR : 0 < (centers.card : ℝ) := by exact_mod_cast hcard
    have hcoef : 0 < β * (centers.card : ℝ) / 2 :=
      div_pos (mul_pos hβ hcardR) (by norm_num)
    change -(((β : ℂ) * (centers.card : ℝ) / 2).re) < 0
    simpa using (neg_neg_of_pos hcoef)
  have hleft (x : ℝ) :
      complexGaussianContourWeight centers xj β q (x : ℂ) =
        Complex.exp (b * (x : ℂ) ^ 2 + c * x + d) := by
    simpa [b, c, d] using complexGaussianContourWeight_eq_quadratic
      centers xj β q (x : ℂ)
  have hright (x : ℝ) :
      complexGaussianContourWeight centers xj β q
        ((x : ℂ) + Complex.I * a) =
        Complex.exp (b * ((x : ℂ) + Complex.I * a) ^ 2 +
          c * ((x : ℂ) + Complex.I * a) + d) := by
    simpa [b, c, d] using complexGaussianContourWeight_eq_quadratic
      centers xj β q ((x : ℂ) + Complex.I * a)
  have hquad := integral_cexp_quadratic_im_shift (b := b) (c := c) (d := d) hb a
  refine ⟨?_, ?_, ?_⟩
  · exact hquad.1.congr (ae_of_all _ fun x => (hleft x).symm)
  · exact hquad.2.1.congr (ae_of_all _ fun x => (hright x).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall hleft),
      integral_congr_ae (Filter.Eventually.of_forall hright)]
    exact hquad.2.2

/-! ## The KP shift energy -/

/-- The exponent in the complex-translation identity, KP (2.12), p. 10.
The graph energy counts every multigraph edge once. -/
def gffTranslationEnergy {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (β : ℝ) (a τ : V → ℝ) : ℝ :=
  Multigraph.pairing a τ - (β / 2) * G.energy a

end FroehlichSpencer.BKT

end
