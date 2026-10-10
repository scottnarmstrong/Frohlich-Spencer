/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# A finite-dimensional Poisson summation criterion

The finite-dimensional torus Fourier theorem turns a continuous periodization into Poisson
summation once its coefficients have been identified with the Euclidean Fourier integrals.  The
analytic work of constructing the periodization and proving that coefficient identity is kept
explicit in the hypotheses, so applications can discharge it from their own domination estimates.
-/

@[expose] public section

open Complex MeasureTheory
open scoped FourierTransform

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

/-- The Euclidean Fourier coefficient with the negative exponential convention used by the
finite-frequency comb. -/
def multiEuclideanFourierCoefficient {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℂ) (q : ι → ℤ) : ℂ :=
  ∫ x : ι → ℝ,
    Complex.exp
      (((-2 * Real.pi * ∑ i : ι, x i * (q i : ℝ) : ℝ) : ℂ) * Complex.I) * f x

/-- Multidimensional Poisson summation for a continuous torus periodization.  The hypotheses are
the two analytic periodization identities: the torus Fourier coefficients are the Euclidean
Fourier integrals of `f`, and the value at zero is the lattice sample sum.  Summability of the
Fourier coefficients makes the torus Fourier series converge pointwise by Mathlib's product-torus
Fourier theorem. -/
theorem tsum_multiEuclideanFourierCoefficient_eq_latticeSamples
    {ι : Type*} [Fintype ι] [MeasurableSpace (UnitAddTorus ι)]
    [BorelSpace (UnitAddTorus ι)]
    (f : (ι → ℝ) → ℂ) (P : C(UnitAddTorus ι, ℂ))
    (hcoeff : ∀ q : ι → ℤ,
      UnitAddTorus.mFourierCoeff P q = multiEuclideanFourierCoefficient f q)
    (hsample : P 0 = ∑' x : ι → ℤ, f (fun i => (x i : ℝ)))
    (hcoeffsum : Summable (multiEuclideanFourierCoefficient f)) :
    ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q =
      ∑' x : ι → ℤ, f (fun i => (x i : ℝ)) := by
  have htorus : Summable (UnitAddTorus.mFourierCoeff P) := by
    apply hcoeffsum.congr
    intro q
    exact (hcoeff q).symm
  have hpoint := UnitAddTorus.hasSum_mFourier_series_apply_of_summable htorus
    (0 : UnitAddTorus ι)
  have hzero : ∀ q : ι → ℤ,
      UnitAddTorus.mFourier q (0 : UnitAddTorus ι) = 1 := by
    intro q
    simp [UnitAddTorus.mFourier]
  have hseries :
      ∑' q : ι → ℤ,
          UnitAddTorus.mFourierCoeff P q * UnitAddTorus.mFourier q 0 = P 0 := by
    have := hpoint.tsum_eq
    simpa only [smul_eq_mul] using this
  calc
    ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q =
        ∑' q : ι → ℤ,
          UnitAddTorus.mFourierCoeff P q * UnitAddTorus.mFourier q 0 := by
      apply tsum_congr
      intro q
      rw [hcoeff q, hzero q, mul_one]
    _ = P 0 := hseries
    _ = ∑' x : ι → ℤ, f (fun i => (x i : ℝ)) := hsample

end FroehlichSpencer.BKT.Rotator

end
