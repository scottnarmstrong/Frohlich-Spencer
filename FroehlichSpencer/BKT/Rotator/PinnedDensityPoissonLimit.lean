/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.PinnedDensityCombLimit
public import FroehlichSpencer.BKT.Rotator.PoissonMultiSchwartz

/-! # General-volume comb limit for pinned interpolated densities -/

@[expose] public section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform SchwartzMap
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Lattice2D

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

/-- Pinned integer face heights are equivalent to arbitrary integer coordinates on the bounded
faces. -/
def rotatorFaceHeightCoordsEquiv {L : ℕ} :
    RotatorFaceHeight L ≃ (SquareFreeVertex L → ℤ) where
  toFun := rotatorFaceHeightCoords
  invFun q := ⟨fun p => p.elim 0 q, rfl⟩
  left_inv h := by
    apply Subtype.ext
    funext p
    cases p with
    | none => simp [h.2]
    | some v => rfl
  right_inv q := by
    funext v
    rfl

/-- In every finite box, the unconditional multidimensional Poisson formula identifies the
Fourier-coefficient sum of the pinned Bessel density with the pinned integer-height partition
factor. -/
theorem rotatorPinnedInterpolatedDensity_fourierSum_eq_heightPartitionFactor
    {L : ℕ} {β : ℝ} (hβ : 1 ≤ β) :
    (∑' q : FaceFrequency (SquareFreeVertex L),
      faceFourierCoefficient (rotatorPinnedInterpolatedDensityCoords L β) q) =
      rotatorHeightPartitionFactor L β := by
  let ι := SquareFreeVertex L
  obtain ⟨f, hf⟩ := exists_rotatorPinnedInterpolatedDensityCoords_schwartz hβ
  have hcoeff (q : FaceFrequency ι) :
      faceFourierCoefficient (rotatorPinnedInterpolatedDensityCoords L β) q =
        multiEuclideanFourierCoefficient f (faceFrequencyEquiv ι q) := by
    rw [faceFourierCoefficient_eq_multiEuclideanFourierCoefficient
      (rotatorPinnedInterpolatedDensityCoords L β) q]
    rw [show faceFrequencyEquiv ι q = (fun i => q i (Finset.mem_univ i)) by rfl]
    unfold multiEuclideanFourierCoefficient
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hf]
  have hcoeffSum :
      (∑' q : FaceFrequency ι,
        faceFourierCoefficient (rotatorPinnedInterpolatedDensityCoords L β) q) =
        ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q := by
    calc
      _ = ∑' q : FaceFrequency ι,
            multiEuclideanFourierCoefficient f (faceFrequencyEquiv ι q) := by
          apply tsum_congr
          exact hcoeff
      _ = ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q :=
        (faceFrequencyEquiv ι).tsum_eq (multiEuclideanFourierCoefficient f)
  have hpoisson := poissonSummation_schwartz_pi_unconditional f
  have hsample :
      (∑' z : ι → ℤ,
        rotatorPinnedInterpolatedDensityCoords L β (fun i => (z i : ℝ))) =
        rotatorHeightPartitionFactor L β := by
    calc
      _ = ∑' h : RotatorFaceHeight L,
            rotatorPinnedInterpolatedDensityCoords L β
              (fun v => (rotatorFaceHeightCoords h v : ℝ)) := by
          symm
          exact (rotatorFaceHeightCoordsEquiv (L := L)).tsum_eq
            (fun q : SquareFreeVertex L → ℤ =>
              rotatorPinnedInterpolatedDensityCoords L β (fun v => (q v : ℝ)))
      _ = rotatorHeightPartitionFactor L β :=
        (rotatorHeightPartitionFactor_eq_coordsSum (L := L) β (by linarith)).symm
  calc
    _ = ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q := hcoeffSum
    _ = ∑' z : ι → ℤ, f (fun i => (z i : ℝ)) := hpoisson
    _ = ∑' z : ι → ℤ,
          rotatorPinnedInterpolatedDensityCoords L β (fun i => (z i : ℝ)) := by
          apply tsum_congr
          intro z
          exact hf (fun i => (z i : ℝ))
    _ = rotatorHeightPartitionFactor L β := hsample

/-- The actual finite-frequency comb pairings of the pinned density converge to the pinned height
partition factor in every finite volume. -/
theorem rotatorPinnedCombCutoffPairing_tendsto_heightPartitionFactor
    {L : ℕ} {β : ℝ} (hβ : 1 ≤ β) :
    Tendsto (fun N : ℕ => rotatorPinnedCombCutoffPairing L β N) atTop
      (𝓝 (rotatorHeightPartitionFactor L β)) := by
  have hcut := rotatorPinnedCombCutoffPairing_tendsto_fourier (L := L) hβ
  rw [rotatorPinnedInterpolatedDensity_fourierSum_eq_heightPartitionFactor hβ] at hcut
  exact hcut

end FroehlichSpencer.BKT.Rotator

end
