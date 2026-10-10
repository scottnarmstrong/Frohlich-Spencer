/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.TheoremC.Defs
public import FroehlichSpencer.BKT.Rotator.PinnedDensityPoissonLimit

/-!
# The marked pinned height sum as a limit of comb pairings

FS81 (1.35)–(1.37) (J pp. 534–535, Appendix A): the free-box plane-rotator two-point function is
the ratio of the marked zero-exterior height sum `∑_h ∏_e I_β(∇h(e) + j(e))` to the unmarked one,
where `j` is an integer source current (`rotatorMeasureInternal_character_integral_eq_heightRatio`).

The unmarked denominator is already the limit of the comb pairings of the pinned interpolated
density (`rotatorPinnedCombCutoffPairing_tendsto_heightPartitionFactor`).

* `exists_rotatorPinnedMarkedDensityCoords_schwartz`: the marked density
  `x ↦ ∏_e I_β(∇x(e) + j(e))` in bounded-face coordinates is Schwartz (a constant shift of the
  edge product of one-dimensional Bessel–Schwartz functions, pulled back along the injective
  pinned gradient);
* `integrable_rotatorPinnedMarkedDensityCoords`;
* `rotatorPinnedMarkedCombCutoffPairing_tendsto`: its box-comb pairings converge to the marked
  height factor `rotatorHeightMarkedFactor L β j`, by Fourier summability, the comb cutoff limit
  and multidimensional Poisson summation, with `I_β(n) = rotatorI β n` at integers.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform SchwartzMap
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator.BesselInterp

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

/-- The marked density is the edge product evaluated at the pinned gradient shifted by `j`. -/
theorem rotatorPinnedMarkedDensityCoords_eq {L : ℕ} (β : ℝ) (j : RotatorInternalBond L → ℤ)
    (x : SquareFreeVertex L → ℝ) :
    rotatorPinnedMarkedDensityCoords L β j x =
      ∏ e : RotatorInternalBond L,
        besselInterp β (((rotatorCoordsGradientLinearMap L x e + (j e : ℝ) : ℝ)) : ℂ) := by
  rfl

/-- The marked pinned density in bounded-face coordinates has a Schwartz representative for every
`β ≥ 1` and every integer source current `j`. -/
theorem exists_rotatorPinnedMarkedDensityCoords_schwartz {L : ℕ} {β : ℝ} (hβ : 1 ≤ β)
    (j : RotatorInternalBond L → ℤ) :
    ∃ f : 𝓢(SquareFreeVertex L → ℝ, ℂ), ∀ x, f x = rotatorPinnedMarkedDensityCoords L β j x := by
  classical
  let bessel : 𝓢(ℝ, ℂ) := besselInterpRealSchwartz β hβ
  obtain ⟨edgeProduct, hedgeProduct⟩ :=
    exists_schwartz_pi_product (ι := RotatorInternalBond L) bessel
  let jR : RotatorInternalBond L → ℝ := fun e => (j e : ℝ)
  let shifted : 𝓢(RotatorInternalBond L → ℝ, ℂ) :=
    SchwartzMap.compSubConstCLM ℂ (-jR) edgeProduct
  let grad : (SquareFreeVertex L → ℝ) →L[ℝ] (RotatorInternalBond L → ℝ) :=
    (rotatorCoordsGradientLinearMap L).toContinuousLinearMap
  obtain ⟨K, -, hanti⟩ :=
    (rotatorCoordsGradientLinearMap L).injective_iff_antilipschitz.mp
      (rotatorCoordsGradientLinearMap_injective L)
  have hanti' : AntilipschitzWith K grad := by
    change AntilipschitzWith K (rotatorCoordsGradientLinearMap L)
    exact hanti
  let f : 𝓢(SquareFreeVertex L → ℝ, ℂ) :=
    (SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti') shifted
  refine ⟨f, fun x => ?_⟩
  have hcomp : f x = shifted (grad x) := by
    change ((SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti')
      shifted) x = shifted (grad x)
    simp only [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]
  have hshift : shifted (grad x) = edgeProduct (grad x - -jR) :=
    SchwartzMap.compSubConstCLM_apply edgeProduct (-jR) (grad x)
  rw [hcomp, hshift, hedgeProduct, rotatorPinnedMarkedDensityCoords_eq]
  refine Finset.prod_congr rfl fun e _ => ?_
  change besselInterp β (((grad x - -jR) e : ℝ) : ℂ) = _
  rw [Pi.sub_apply, Pi.neg_apply, sub_neg_eq_add]
  rfl

/-- The marked pinned density is integrable in every finite volume, for `β ≥ 1`. -/
theorem integrable_rotatorPinnedMarkedDensityCoords {L : ℕ} {β : ℝ} (hβ : 1 ≤ β)
    (j : RotatorInternalBond L → ℤ) : Integrable (rotatorPinnedMarkedDensityCoords L β j) := by
  obtain ⟨f, hf⟩ := exists_rotatorPinnedMarkedDensityCoords_schwartz hβ j
  refine (integrable_schwartz_pi f).congr ?_
  filter_upwards [] with x
  exact hf x

/-- The Fourier coefficients of the marked pinned density are summable. -/
theorem summable_rotatorPinnedMarkedDensityCoords_fourier {L : ℕ} {β : ℝ} (hβ : 1 ≤ β)
    (j : RotatorInternalBond L → ℤ) :
    Summable (faceFourierCoefficient (rotatorPinnedMarkedDensityCoords L β j)) := by
  classical
  obtain ⟨f, hf⟩ := exists_rotatorPinnedMarkedDensityCoords_schwartz hβ j
  refine (summable_faceFourierCoefficient_of_schwartz f).congr fun q => ?_
  unfold faceFourierCoefficient
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hf]

/-- On integer coordinates the marked density is the marked integer-height weight. -/
theorem rotatorPinnedMarkedDensityCoords_height {L : ℕ} {β : ℝ} (hβ : 0 < β)
    (j : RotatorInternalBond L → ℤ) (h : RotatorFaceHeight L) :
    rotatorPinnedMarkedDensityCoords L β j (fun v => (rotatorFaceHeightCoords h v : ℝ)) =
      ∏ e : RotatorInternalBond L, rotatorI β (rotatorFaceHeightCurrent h e + j e) := by
  have hfield : ∀ p : RotatorDualFace L,
      (rotatorPinnedRealFieldOfCoords (fun v => (rotatorFaceHeightCoords h v : ℝ))).1 p =
        (h.1 p : ℝ) := by
    intro p
    cases p with
    | none => simp [rotatorPinnedRealFieldOfCoords, h.2]
    | some v => rfl
  unfold rotatorPinnedMarkedDensityCoords
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [hfield, hfield, ← besselInterp_intCast_eq_rotatorI hβ]
  congr 1
  simp only [rotatorFaceHeightCurrent]
  push_cast
  ring

/-- **Poisson summation for the marked density**: the Fourier-coefficient sum of the marked
pinned density is the marked zero-exterior height factor. -/
theorem rotatorPinnedMarkedDensity_fourierSum_eq_heightMarkedFactor {L : ℕ} {β : ℝ}
    (hβ : 1 ≤ β) (j : RotatorInternalBond L → ℤ) :
    (∑' q : FaceFrequency (SquareFreeVertex L),
      faceFourierCoefficient (rotatorPinnedMarkedDensityCoords L β j) q) =
      rotatorHeightMarkedFactor L β j := by
  classical
  let ι := SquareFreeVertex L
  obtain ⟨f, hf⟩ := exists_rotatorPinnedMarkedDensityCoords_schwartz hβ j
  have hcoeff (q : FaceFrequency ι) :
      faceFourierCoefficient (rotatorPinnedMarkedDensityCoords L β j) q =
        multiEuclideanFourierCoefficient f (faceFrequencyEquiv ι q) := by
    rw [faceFourierCoefficient_eq_multiEuclideanFourierCoefficient
      (rotatorPinnedMarkedDensityCoords L β j) q]
    rw [show faceFrequencyEquiv ι q = (fun i => q i (Finset.mem_univ i)) by rfl]
    unfold multiEuclideanFourierCoefficient
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hf]
  have hcoeffSum :
      (∑' q : FaceFrequency ι,
        faceFourierCoefficient (rotatorPinnedMarkedDensityCoords L β j) q) =
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
      (∑' z : ι → ℤ, rotatorPinnedMarkedDensityCoords L β j (fun i => (z i : ℝ))) =
        rotatorHeightMarkedFactor L β j := by
    calc
      _ = ∑' h : RotatorFaceHeight L,
            rotatorPinnedMarkedDensityCoords L β j
              (fun v => (rotatorFaceHeightCoords h v : ℝ)) := by
          symm
          exact (rotatorFaceHeightCoordsEquiv (L := L)).tsum_eq
            (fun q : SquareFreeVertex L → ℤ =>
              rotatorPinnedMarkedDensityCoords L β j (fun v => (q v : ℝ)))
      _ = rotatorHeightMarkedFactor L β j := by
          unfold rotatorHeightMarkedFactor
          apply tsum_congr
          intro h
          exact rotatorPinnedMarkedDensityCoords_height (by linarith) j h
  calc
    _ = ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q := hcoeffSum
    _ = ∑' z : ι → ℤ, f (fun i => (z i : ℝ)) := hpoisson
    _ = ∑' z : ι → ℤ, rotatorPinnedMarkedDensityCoords L β j (fun i => (z i : ℝ)) := by
          apply tsum_congr
          intro z
          exact hf (fun i => (z i : ℝ))
    _ = rotatorHeightMarkedFactor L β j := hsample

/-- **The marked comb limit**: the box-comb pairings of the marked pinned density converge to the
marked zero-exterior height factor, in every finite volume and for `β ≥ 1`. -/
theorem rotatorPinnedMarkedCombCutoffPairing_tendsto {L : ℕ} {β : ℝ} (hβ : 1 ≤ β)
    (j : RotatorInternalBond L → ℤ) :
    Tendsto (fun N : ℕ => rotatorPinnedMarkedCombCutoffPairing L β j N) atTop
      (𝓝 (rotatorHeightMarkedFactor L β j)) := by
  classical
  have hcut := faceCombCutoffPairing_tendsto_fourier
    (integrable_rotatorPinnedMarkedDensityCoords hβ j)
    (summable_rotatorPinnedMarkedDensityCoords_fourier hβ j)
  rw [rotatorPinnedMarkedDensity_fourierSum_eq_heightMarkedFactor hβ j] at hcut
  exact hcut

end FroehlichSpencer.BKT.Rotator.TheoremC

end
