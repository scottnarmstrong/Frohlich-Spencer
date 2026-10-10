/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.SurfacePrimalProof.Expectation
public import FroehlichSpencer.FS82.SurfacePrimalProof.Face
public import FroehlichSpencer.FS82.Infinite.PrimalPackageGeometry
import Mathlib.Tactic

@[expose] public section
open MeasureTheory
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Nonsummability
namespace FroehlichSpencer.FS82.SurfaceInfinite

/-- The literal integral is real and is the finite cube curvature pair moment
away from the diagonal. The containment witnesses are carried by the map. -/
theorem sourcePrimalPair_eq_cube (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β)
    (x y : LatticePoint) (hxy : x ≠ y)
    (hP : ∀ p ∈ pairPlaquettes x y, inCube (Surface.centredCube N hN) p) :
    (∫ θ : Surface.PrimalLinks (Surface.centredCube N hN) → ℝ,
      sourcePrimalFieldStrength _ β hβ θ
        (sourceC4PrimalFace N hN (dualCurvatureAt x)
          (hP _ (by simp [pairPlaquettes]))) *
      sourcePrimalFieldStrength _ β hβ θ
        (sourceC4PrimalFace N hN (dualCurvatureAt y)
          (hP _ (by simp [pairPlaquettes])))
      ∂Surface.primalVillainLaw _ β hβ) =
      (primalCubePrimalCorrelation N β hβ x y : ℂ) := by
  rw [sourcePrimalPairExpectation_eq_internal,
    sourceC4PrimalFace_eq_primalFace, sourceC4PrimalFace_eq_primalFace]
  exact primalFieldStrengthCorrelation_eq_cubeCurvaturePMF N β hβ x y hxy (fun p hp => (source_inCube_iff N hN p).mp (hP p hp))

/-- Uniform containment over any fixed finite Følner box is eventually valid. -/
theorem sourcePrimal_validCube_eventually (n : ℕ) (d : LatticePoint) :
    ∃ N₀, ∀ N ≥ N₀, ∀ hN : 0 < N,
      ∀ a ∈ sourceShiftBox n, ∀ p ∈ pairPlaquettes
        (a 0, a 1, a 2, a 3) (d + (a 0, a 1, a 2, a 3)),
        inCube (Surface.centredCube N hN) p := by
  obtain ⟨N₀, hN₀⟩ := primalPackage_validCube_eventually n d
  refine ⟨N₀, ?_⟩
  intro N hN hpos a ha p hp
  exact (source_inCube_iff N hpos p).mpr (hN₀ N hN a ha p hp)

end FroehlichSpencer.FS82.SurfaceInfinite
end
