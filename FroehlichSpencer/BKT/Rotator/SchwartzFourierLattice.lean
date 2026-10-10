/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.LatticeSchwartzSummability
public import FroehlichSpencer.BKT.Rotator.PoissonMulti
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Schwartz Fourier coefficients on finite integer lattices -/

@[expose] public section

open Complex MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

/-- Pull a Schwartz function on the coordinate model back to Euclidean space. -/
def schwartzToEuclidean {ι : Type*} [Fintype ι] (f : 𝓢(ι → ℝ, ℂ)) :
    𝓢(EuclideanSpace ℝ ι, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv ι ℝ)) f

/-- The Euclidean Fourier transform, expressed again on the coordinate model. -/
def schwartzFourierOnPi {ι : Type*} [Fintype ι] (f : 𝓢(ι → ℝ, ℂ)) :
    𝓢(ι → ℝ, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv ι ℝ).symm)
    ((SchwartzMap.fourierTransformCLM ℂ) (schwartzToEuclidean f))

/-- For a Schwartz function, the explicit negative-phase coefficient integral is its Euclidean
Fourier transform sampled at the corresponding integer vector. -/
theorem multiEuclideanFourierCoefficient_eq_schwartzFourierOnPi
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : 𝓢(ι → ℝ, ℂ)) (q : ι → ℤ) :
    multiEuclideanFourierCoefficient f q =
      schwartzFourierOnPi f (fun i => (q i : ℝ)) := by
  let e := MeasurableEquiv.toLp 2 (ι → ℝ)
  have hmp : MeasurePreserving (fun x : ι → ℝ => (EuclideanSpace.equiv ι ℝ).symm x)
      volume volume := by
    convert PiLp.volume_preserving_toLp ι using 1
    funext x
    rfl
  let fE := schwartzToEuclidean f
  have hfE (x : ι → ℝ) : fE ((EuclideanSpace.equiv ι ℝ).symm x) = f x := by
    change f ((EuclideanSpace.equiv ι ℝ) ((EuclideanSpace.equiv ι ℝ).symm x)) = f x
    exact congrArg f ((EuclideanSpace.equiv ι ℝ).apply_symm_apply x)
  let qE : EuclideanSpace ℝ ι :=
    (EuclideanSpace.equiv ι ℝ).symm (fun i => (q i : ℝ))
  have hinner (x : ι → ℝ) :
      inner ℝ ((EuclideanSpace.equiv ι ℝ).symm x) qE =
        ∑ i : ι, x i * (q i : ℝ) := by
    dsimp [qE]
    rw [show (EuclideanSpace.equiv ι ℝ).symm x =
      (WithLp.toLp 2 x : EuclideanSpace ℝ ι) by rfl]
    rw [show (EuclideanSpace.equiv ι ℝ).symm (fun i => (q i : ℝ)) =
      (WithLp.toLp 2 (fun i => (q i : ℝ)) : EuclideanSpace ℝ ι) by rfl]
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  have hback : schwartzFourierOnPi f (fun i => (q i : ℝ)) = 𝓕 fE qE := by
    simp [schwartzFourierOnPi, schwartzToEuclidean, fE, qE,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.fourierTransformCLM_apply]
  rw [multiEuclideanFourierCoefficient, hback]
  calc
    (∫ x : ι → ℝ,
        Complex.exp (((-2 * Real.pi * ∑ i : ι, x i * (q i : ℝ) : ℝ) : ℂ) * Complex.I) * f x) =
      ∫ x : ι → ℝ,
        cexp ((-2 * Real.pi * inner ℝ ((EuclideanSpace.equiv ι ℝ).symm x) qE : ℝ) * Complex.I) •
          fE ((EuclideanSpace.equiv ι ℝ).symm x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hinner, hfE]
        simp [smul_eq_mul]
    _ = ∫ y : EuclideanSpace ℝ ι,
        cexp ((-2 * Real.pi * inner ℝ y qE : ℝ) * Complex.I) • fE y := by
          exact hmp.integral_comp e.measurableEmbedding
            (fun y : EuclideanSpace ℝ ι =>
              cexp ((-2 * Real.pi * inner ℝ y qE : ℝ) * Complex.I) • fE y)
    _ = 𝓕 fE qE := (Real.fourier_eq' fE qE).symm

/-- Schwartz decay makes the complete family of lattice Fourier coefficients summable in every
finite coordinate dimension. -/
theorem summable_multiEuclideanFourierCoefficient_of_schwartz
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : 𝓢(ι → ℝ, ℂ)) :
    Summable (multiEuclideanFourierCoefficient f) := by
  have h := schwartz_pi_lattice_samples_summable (schwartzFourierOnPi f)
  refine h.congr fun q => ?_
  exact (multiEuclideanFourierCoefficient_eq_schwartzFourierOnPi f q).symm

/-- A Schwartz function on a finite coordinate space is integrable. -/
theorem integrable_schwartz_pi {ι : Type*} [Fintype ι] (f : 𝓢(ι → ℝ, ℂ)) :
    Integrable f := by
  exact f.integrable

end FroehlichSpencer.BKT.Rotator

end
