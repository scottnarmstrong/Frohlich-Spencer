/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfacePrimal.SourcePrimalFieldStrength
public import FroehlichSpencer.FS82.SurfacePrimal.SourceC4PrimalFace
public import FroehlichSpencer.FS82.SurfaceInfinite.CubeRegion
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquetteAxes
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquette
public import FroehlichSpencer.FS82.SurfaceInfinite.InCube
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceCurrentEquiv
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceCurrentEquivSpec
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceIntegerCellSign
public import FroehlichSpencer.FS82.SurfaceInfinite.CubeCurvatureMap
public import FroehlichSpencer.FS82.SurfaceInfinite.CubeCurvatureLaw
public import FroehlichSpencer.FS82.SurfaceInfinite.CubeCurvatureLimitState
public import FroehlichSpencer.FS82.SurfaceInfinite.LatticePoint
public import FroehlichSpencer.FS82.SurfaceInfinite.Torus4
public import FroehlichSpencer.FS82.SurfaceInfinite.CellDegree
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkField
public import FroehlichSpencer.FS82.SurfaceInfinite.CellBaseCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.CellPoint
public import FroehlichSpencer.FS82.SurfaceInfinite.LinkAxisCell
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkAxisSupport
public import FroehlichSpencer.FS82.SurfaceInfinite.LatticeCharacter
public import FroehlichSpencer.FS82.SurfaceInfinite.Torus4Haar
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkFourierComponent
public import FroehlichSpencer.FS82.SurfaceInfinite.FourierLaplacianSymbol
public import FroehlichSpencer.FS82.SurfaceInfinite.FourierGreenDensity
public import FroehlichSpencer.FS82.SurfaceInfinite.FourierGreenQuadratic
public import FroehlichSpencer.FS82.SurfaceInfinite.SourcePointCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.DualCurvatureCell
public import FroehlichSpencer.FS82.SurfaceInfinite.DualCurvatureAt
public import FroehlichSpencer.FS82.SurfaceInfinite.PairPlaquettes
public import FroehlichSpencer.FS82.SurfaceInfinite.PairProduct
public import FroehlichSpencer.FS82.SurfaceInfinite.CurvatureCylinderState
public import FroehlichSpencer.FS82.SurfaceInfinite.DualCurvatureCorrelation
public import FroehlichSpencer.FS82.SurfaceInfinite.AbsolutelySummableCorrelation
public import FroehlichSpencer.FS82.SurfaceInfinite.CellOrientationSign
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquetteField
public import FroehlichSpencer.FS82.SurfaceInfinite.FillingPlaquetteEmbedding
public import FroehlichSpencer.FS82.SurfaceInfinite.FillingCurvatureIndexSet
public import FroehlichSpencer.FS82.SurfaceInfinite.FillingCurvaturePairing
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceLatticeShift
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCoordinate
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCell
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCellAdd
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCellZero
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceGlobalPlaquetteAxesTranslate
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslatePlaquetteEquiv
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslatePlaquettes
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslatePlaquetteIndex
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceUntranslateCurvatureAssignment
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceTranslateCylinderLaw
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceCubeStateToCylinderState
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBoxSet
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBoxSetFinite
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBox
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftUniform
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceFiniteShiftAverage
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceAveragedCylinderLaw
public import FroehlichSpencer.FS82.Surface.PrimalVillainLaw
public import FroehlichSpencer.FS82.Provider.PrimalFieldStrengthNonsummability

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section
open MeasureTheory Filter Topology
namespace FroehlichSpencer.FS82.SurfaceInfinite

theorem source_primalFieldStrength_nonsummable :
    ∃ β₁ : {b : ℝ // 0 < b}, ∀ β (hβ : β₁.val ≤ β),
      ∃ L : CubeCurvatureLimitState β (lt_of_lt_of_le β₁.property hβ),
        ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ S : CurvatureCylinderState,
          (∀ P x, Tendsto
            (fun k => (sourceAveragedCylinderLaw
              (sourceCubeStateToCylinderState L) (s k) P x).toReal)
            atTop (𝓝 ((S.law P x).toReal))) ∧
          (∀ a P, sourceTranslateCylinderLaw S a P = S.law P) ∧
          (∃ m : ℕ → ℕ, StrictMono m ∧
            ∀ d : LatticePoint, d ≠ 0 → ∀ ε : ℝ, 0 < ε →
              ∃ k₀, ∀ k ≥ k₀, ∃ hN : 0 < L.subsequence (m k),
                ∃ hvalid : ∀ a ∈ sourceShiftBox (s k), ∀ p ∈ pairPlaquettes
                    (a 0, a 1, a 2, a 3) (d + (a 0, a 1, a 2, a 3)),
                    inCube (Surface.centredCube (L.subsequence (m k)) hN) p,
                  dist ((Fintype.card {a : SourceLatticeShift // a ∈ sourceShiftBox (s k)} : ℝ)⁻¹ *
                    ∑ a : {a : SourceLatticeShift // a ∈ sourceShiftBox (s k)},
                      (∫ θ : Surface.PrimalLinks
                          (Surface.centredCube (L.subsequence (m k)) hN) → ℝ,
                        sourcePrimalFieldStrength _ β (lt_of_lt_of_le β₁.property hβ) θ
                          (sourceC4PrimalFace (L.subsequence (m k)) hN
                            (dualCurvatureAt (a.val 0, a.val 1, a.val 2, a.val 3))
                            (hvalid a.val a.property _ (by simp [pairPlaquettes]))) *
                        sourcePrimalFieldStrength _ β (lt_of_lt_of_le β₁.property hβ) θ
                          (sourceC4PrimalFace (L.subsequence (m k)) hN
                            (dualCurvatureAt (d + (a.val 0, a.val 1, a.val 2, a.val 3)))
                            (hvalid a.val a.property _ (by simp [pairPlaquettes])))
                        ∂Surface.primalVillainLaw _ β
                          (lt_of_lt_of_le β₁.property hβ)).re)
                    (dualCurvatureCorrelation S d) < ε) ∧
          ¬ AbsolutelySummableCorrelation (dualCurvatureCorrelation S) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.FS82.Provider.PrimalFieldStrengthNonsummability.source_primalFieldStrength_nonsummable
  -- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.FS82.SurfaceInfinite
end
-- FROZEN_ANCHOR_SUFFIX_END
