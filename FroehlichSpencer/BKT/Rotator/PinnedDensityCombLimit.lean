/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.FiniteComb
public import FroehlichSpencer.BKT.Rotator.PinnedDensitySchwartz
public import FroehlichSpencer.BKT.Rotator.SchwartzFourierLattice

/-! # Fourier summability and cutoff convergence for pinned densities -/

@[expose] public section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform SchwartzMap
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Lattice2D

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

/-- The proof-carrying finite-face frequency assignments are equivalent to ordinary integer
vectors. -/
def faceFrequencyEquiv (ι : Type*) [Fintype ι] : FaceFrequency ι ≃ (ι → ℤ) where
  toFun q i := q i (Finset.mem_univ i)
  invFun q i _ := q i
  left_inv q := by
    funext i hi
    congr 1
  right_inv q := by
    funext i
    rfl

/-- The Fourier coefficient using `faceCombMode` is the same negative-phase Euclidean Fourier
integral used by the generic finite-dimensional Poisson theorem. -/
theorem faceFourierCoefficient_eq_multiEuclideanFourierCoefficient
    {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ) (q : FaceFrequency ι) :
    faceFourierCoefficient f q =
      multiEuclideanFourierCoefficient f (fun i => q i (Finset.mem_univ i)) := by
  unfold faceFourierCoefficient multiEuclideanFourierCoefficient faceCombMode
  congr 1

/-- Fourier coefficients of any Schwartz density on a finite pinned coordinate space are
absolutely summable. -/
theorem summable_faceFourierCoefficient_of_schwartz
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : 𝓢(ι → ℝ, ℂ)) :
    Summable (faceFourierCoefficient f) := by
  have h := summable_multiEuclideanFourierCoefficient_of_schwartz f
  have h' : Summable (fun q : FaceFrequency ι =>
      multiEuclideanFourierCoefficient f (faceFrequencyEquiv ι q)) :=
    (faceFrequencyEquiv ι).summable_iff.mpr h
  exact h'.congr fun q => (faceFourierCoefficient_eq_multiEuclideanFourierCoefficient f q).symm

/-- The pinned interpolated density is integrable in every finite volume with `β ≥ 1`, by its
Schwartz representative. -/
theorem integrable_rotatorPinnedInterpolatedDensityCoords {L : ℕ} {β : ℝ}
    (hβ : 1 ≤ β) : Integrable (rotatorPinnedInterpolatedDensityCoords L β) := by
  obtain ⟨f, hf⟩ := exists_rotatorPinnedInterpolatedDensityCoords_schwartz hβ
  refine (integrable_schwartz_pi f).congr ?_
  filter_upwards [] with x
  exact hf x

/-- Fourier coefficients of the pinned interpolated density are summable in every volume. -/
theorem summable_rotatorPinnedInterpolatedDensityCoords_fourier {L : ℕ} {β : ℝ}
    (hβ : 1 ≤ β) :
    Summable (faceFourierCoefficient (rotatorPinnedInterpolatedDensityCoords L β)) := by
  obtain ⟨f, hf⟩ := exists_rotatorPinnedInterpolatedDensityCoords_schwartz hβ
  have h := summable_faceFourierCoefficient_of_schwartz f
  refine h.congr fun q => ?_
  unfold faceFourierCoefficient
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hf]

/-- In every finite volume, the symmetric finite-frequency comb pairings converge to the full
Fourier-coefficient sum of the pinned real-field density. -/
theorem rotatorPinnedCombCutoffPairing_tendsto_fourier {L : ℕ} {β : ℝ}
    (hβ : 1 ≤ β) :
    Tendsto (fun N : ℕ => rotatorPinnedCombCutoffPairing L β N) atTop
      (𝓝 (∑' q : FaceFrequency (SquareFreeVertex L),
        faceFourierCoefficient (rotatorPinnedInterpolatedDensityCoords L β) q)) := by
  exact faceCombCutoffPairing_tendsto_fourier
    (integrable_rotatorPinnedInterpolatedDensityCoords hβ)
    (summable_rotatorPinnedInterpolatedDensityCoords_fourier hβ)

end FroehlichSpencer.BKT.Rotator

end
