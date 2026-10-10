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
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.MomentComparison

@[expose] public section

open MeasureTheory
open Filter Topology
open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.Provider.InfiniteRoot293

theorem source_infiniteVolume_momentComparison :
  ∃ β₀ : {b : ℝ // 0 < b}, ∃ cPack : ℝ → ℝ,
    (∀ β, β₀.val ≤ β → 0 < cPack β) ∧
    Tendsto (fun β : ℝ => 2 * β * cPack β) atTop (𝓝 0) ∧
    (∀ β, β₀.val ≤ β →
      0 < Surface.betaDoublePrime cPack β ∧
      Surface.betaDoublePrime cPack β < β) ∧
    Tendsto (Surface.betaDoublePrime cPack) atTop atTop ∧
    ∀ β (hβ : β₀.val ≤ β),
      ∀ L : SurfaceInfinite.CubeCurvatureLimitState β (lt_of_lt_of_le β₀.property hβ),
        ∀ μ : SurfaceInfinite.GlobalLinkField,
          Surface.realLatticeBoundary (μ : Surface.RealLatticeChain) = 0 →
          ∀ σ : SurfaceInfinite.GlobalPlaquetteField,
            Surface.realLatticeBoundary (σ : Surface.RealLatticeChain) =
              (μ : Surface.RealLatticeChain) →
            ∀ t : ℝ,
              Real.exp ((t ^ 2 * Surface.betaDoublePrime cPack β / 2) *
                  SurfaceInfinite.fourierGreenQuadratic μ) ≤
                ∫ x, Real.exp (t * SurfaceInfinite.fillingCurvaturePairing σ x) ∂
                  (L.law (SurfaceInfinite.fillingCurvatureIndexSet σ)).toMeasure ∧
              (∫ x, Real.exp (t * SurfaceInfinite.fillingCurvaturePairing σ x) ∂
                  (L.law (SurfaceInfinite.fillingCurvatureIndexSet σ)).toMeasure) ≤
                Real.exp ((t ^ 2 * β / 2) * SurfaceInfinite.fourierGreenQuadratic μ) := by
  exact FroehlichSpencer.FS82.SurfaceInfinite.source_root_293_internal

end FroehlichSpencer.FS82.Provider.InfiniteRoot293

end
