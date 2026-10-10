/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
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
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.CorrelationNonsummability

@[expose] public section

open MeasureTheory
open Filter Topology
open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.Provider.InfiniteRoot211

theorem source_curvatureCorrelation_nonsummable :
    ∃ β₁ : {b : ℝ // 0 < b},
      ∀ β (hβ : β₁.val ≤ β),
        ∃ L : SurfaceInfinite.CubeCurvatureLimitState β
            (lt_of_lt_of_le β₁.property hβ),
          ∃ s : ℕ → ℕ, StrictMono s ∧
            ∃ S : SurfaceInfinite.CurvatureCylinderState,
              (∀ P x, Tendsto
                (fun k => (SurfaceInfinite.sourceAveragedCylinderLaw
                  (SurfaceInfinite.sourceCubeStateToCylinderState L) (s k) P x).toReal)
                atTop (𝓝 ((S.law P x).toReal))) ∧
              (∀ a P, SurfaceInfinite.sourceTranslateCylinderLaw S a P = S.law P) ∧
              ¬ SurfaceInfinite.AbsolutelySummableCorrelation
                (SurfaceInfinite.dualCurvatureCorrelation S) := by
  exact FroehlichSpencer.FS82.SurfaceInfinite.source_root_211_internal

end FroehlichSpencer.FS82.Provider.InfiniteRoot211

end
