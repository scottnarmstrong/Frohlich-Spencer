/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib
public import FroehlichSpencer.FS82.Surface.FiniteVillainDualMomentComparisonLogThick
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceInfiniteVolumeMomentComparison
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceCurvatureCorrelationNonsummable
public import FroehlichSpencer.FS82.SurfacePrimal.SourcePrimalFieldStrengthNonsummable
public import FroehlichSpencer.FS82.Surface.WilsonLoopPerimeterLawCube
public import FroehlichSpencer.FS82.Surface.WilsonLoopPerimeterLawCubeLimit
public import FroehlichSpencer.FS82.Surface.WilsonLoopAreaLawCube
public import FroehlichSpencer.FS82.Surface.WilsonLoopAreaLawCubeLimit
public import FroehlichSpencer.FS82.Surface.WilsonLoopTransitionCube
public import FroehlichSpencer.FS82.SurfaceZN.fs82_zn_disorder_perimeter_root
public import FroehlichSpencer.FS82.SurfaceXY.fs82_xy_spinCorrelation_root

-- Reset the auxiliary-lemma cache between copied source modules.
-- This preserves generated proof names without changing definitions or assumptions.
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
@[expose] public section
namespace FroehlichSpencer.FS82.Surface
theorem _root_.FSComparator.FS82.fs82FiniteVillainDualMomentComparisonLogThick :
∃ β₀ : {b : ℝ // 0 < b}, ∃ cPack : ℝ → ℝ,
      (∀ β : ℝ, β₀.val ≤ β → 0 < cPack β) ∧
      Tendsto (fun β : ℝ => 2 * β * cPack β) atTop (nhds 0) ∧
      (∀ β : ℝ, β₀.val ≤ β →
        0 < betaDoublePrime cPack β ∧ betaDoublePrime cPack β < β) ∧
      Tendsto (betaDoublePrime cPack) atTop atTop ∧
      ∀ β : ℝ, (hβRange : β₀.val ≤ β) →
        ∀ R : RectBox4,
          IsLogThickRectBox4 R →
        ∀ μ : RealDualField R,
          ∀ hglobal : μ ∈ GlobalCoClosed R,
            ∀ hinterior : IsInteriorSupported R μ,
          ∀ ε : ℝ,
            ENNReal.ofReal
                (Real.exp (ε ^ 2 * betaDoublePrime cPack β / 2 *
                  finiteLatticeCovarianceQuadratic R
                    (sourceTestToW R μ hinterior hglobal))) ≤
              discreteDualMoment R β
                (by have := β₀.property; linarith [hβRange]) ε
                (sourceTestToW R μ hinterior hglobal) ∧
            discreteDualMoment R β
                (by have := β₀.property; linarith [hβRange]) ε
                (sourceTestToW R μ hinterior hglobal) ≤
              ENNReal.ofReal
                (Real.exp (ε ^ 2 * β / 2 *
                  finiteLatticeCovarianceQuadratic R
                    (sourceTestToW R μ hinterior hglobal))) :=
  by exact FroehlichSpencer.FS82.Surface.fs82FiniteVillainDualMomentComparisonLogThick
end FroehlichSpencer.FS82.Surface
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite
noncomputable section
theorem _root_.FSComparator.FS82.source_infiniteVolume_momentComparison :
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
                Real.exp ((t ^ 2 * β / 2) * SurfaceInfinite.fourierGreenQuadratic μ) :=
  by exact FroehlichSpencer.FS82.SurfaceInfinite.source_infiniteVolume_momentComparison
end
end FroehlichSpencer.FS82.SurfaceInfinite
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory
open Filter Topology
open scoped ComplexConjugate
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite
noncomputable section
theorem _root_.FSComparator.FS82.source_curvatureCorrelation_nonsummable :
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
                (SurfaceInfinite.dualCurvatureCorrelation S) :=
  by exact FroehlichSpencer.FS82.SurfaceInfinite.source_curvatureCorrelation_nonsummable
end
end FroehlichSpencer.FS82.SurfaceInfinite
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory Filter Topology
namespace FroehlichSpencer.FS82.SurfaceInfinite
theorem _root_.FSComparator.FS82.source_primalFieldStrength_nonsummable :
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
  by exact FroehlichSpencer.FS82.SurfaceInfinite.source_primalFieldStrength_nonsummable
end FroehlichSpencer.FS82.SurfaceInfinite
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
theorem _root_.FSComparator.FS82.fs82WilsonLoopPerimeterLawCube :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β : ℝ) (hβ : 0 < β), β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
        (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧
        Real.exp (-(d * ((L : ℝ) + T))) ≤
          (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re :=
  by exact FroehlichSpencer.FS82.Surface.fs82WilsonLoopPerimeterLawCube
end FroehlichSpencer.FS82.Surface
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
theorem _root_.FSComparator.FS82.fs82WilsonLoopPerimeterLawCubeLimit :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β : ℝ) (hβ : 0 < β), β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        (∃ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T)) ∧
        (∀ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T) →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ x) ∧
        Real.exp (-(d * ((L : ℝ) + T))) ≤ Filter.liminf (wilsonCubeSequence β hβ L T) atTop ∧
        ∀ w : ℝ, Tendsto (wilsonCubeSequence β hβ L T) atTop (nhds w) →
          Real.exp (-(d * ((L : ℝ) + T))) ≤ w :=
  by exact FroehlichSpencer.FS82.Surface.fs82WilsonLoopPerimeterLawCubeLimit
end FroehlichSpencer.FS82.Surface
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
theorem _root_.FSComparator.FS82.fs82WilsonLoopAreaLawCube :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
        (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧
        0 ≤ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ∧
        (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ≤
          Real.exp (-(c * ((L : ℝ) * T))) :=
  by exact FroehlichSpencer.FS82.Surface.fs82WilsonLoopAreaLawCube
end FroehlichSpencer.FS82.Surface
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
theorem _root_.FSComparator.FS82.fs82WilsonLoopAreaLawCubeLimit :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        (∃ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T)) ∧
        (∀ x : ℝ, MapClusterPt x atTop (wilsonCubeSequence β hβ L T) →
          0 ≤ x ∧ x ≤ Real.exp (-(c * ((L : ℝ) * T)))) ∧
        Filter.limsup (wilsonCubeSequence β hβ L T) atTop ≤ Real.exp (-(c * ((L : ℝ) * T))) ∧
        ∀ w : ℝ, Tendsto (wilsonCubeSequence β hβ L T) atTop (nhds w) →
          0 ≤ w ∧ w ≤ Real.exp (-(c * ((L : ℝ) * T))) :=
  by exact FroehlichSpencer.FS82.Surface.fs82WilsonLoopAreaLawCubeLimit
end FroehlichSpencer.FS82.Surface
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open scoped BigOperators
open Filter
namespace FroehlichSpencer.FS82.Surface
theorem _root_.FSComparator.FS82.fs82WilsonLoopTransitionCube :
    ∃ β₀ β₁ c : ℝ, 0 < β₀ ∧ β₀ < β₁ ∧ 0 < c ∧
      (∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ →
        ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
          (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧
          0 ≤ (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ∧
          (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re ≤
            Real.exp (-(c * ((L : ℝ) * T)))) ∧
      (∀ (β : ℝ) (hβ : 0 < β), β₁ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
        ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ (N : ℕ) (hN : 0 < N), max L T + 1 ≤ N →
          (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).im = 0 ∧
          Real.exp (-(d * ((L : ℝ) + T))) ≤
            (wilsonLoopExpectation (centredCube N hN) β hβ (rectangularLoop L T)).re) :=
  by exact FroehlichSpencer.FS82.Surface.fs82WilsonLoopTransitionCube
end FroehlichSpencer.FS82.Surface
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer.FS82.SurfaceZN
noncomputable section
open Classical
theorem _root_.FSComparator.FS82.fs82_zn_disorder_perimeter_root :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 < β → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ ξ : ℕ, 1 ≤ ξ → ξ < N → ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        ∀ (M : ℕ) (hL : L ≤ M) (hT : T ≤ M) (hbox : 0 < M),
          (∀ h : NNReal,
            Real.exp (-(C * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤
              finiteCenteredDisorderExpectation β N ξ L T M h hL hT hbox) ∧
          Real.exp (-(C * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤
            discreteCenteredDisorderExpectation β N ξ L T M hL hT hbox :=
  by exact FroehlichSpencer.FS82.SurfaceZN.fs82_zn_disorder_perimeter_root
end
end FroehlichSpencer.FS82.SurfaceZN
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped BigOperators
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer.FS82.SurfaceXY
noncomputable section
open Classical
theorem _root_.FSComparator.FS82.fs82_xy_spinCorrelation_root :
    ∀ D : ℕ, 3 ≤ D →
      ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧
        ∀ β : ℝ, β₀ ≤ β → ∀ N : ℕ,
          ∀ x y : XYSite (xyCubeFamily D N),
            Real.exp (-(C / β)) ≤ xySpinCorrelation β x y :=
  by exact FroehlichSpencer.FS82.SurfaceXY.fs82_xy_spinCorrelation_root
end
end FroehlichSpencer.FS82.SurfaceXY
end
