module

public import FroehlichSpencer.FS82.SurfaceInfiniteProof.StateIdentities
public import FroehlichSpencer.FS82.FiniteMomentBridge.LiteralRoot
public import FroehlichSpencer.FS82.Root.FiniteMomentComparison
public import FroehlichSpencer.FS82.Infinite.LimitStateRoot
public import FroehlichSpencer.FS82.Surface.BetaDoublePrime
public import Mathlib.Tactic
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.BoundaryBridge
@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SurfaceInfinite
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.Comparison

namespace FroehlichSpencer.FS82.SurfaceInfinite


theorem sourceFourierGreenQuadratic_eq_internal
    (μ : SurfaceInfinite.GlobalLinkField) :
    SurfaceInfinite.fourierGreenQuadratic μ =
      Infinite.Fourier.fourierGreenQuadratic μ := rfl

theorem sourceFillingCurvaturePairing_eq_internal
    (σ : SurfaceInfinite.GlobalPlaquetteField)
    (x : SurfaceInfinite.fillingCurvatureIndexSet σ → ℤ) :
    SurfaceInfinite.fillingCurvaturePairing σ x =
      Infinite.sourceFillingCurvaturePairing σ x := by
  classical
  unfold SurfaceInfinite.fillingCurvaturePairing Infinite.sourceFillingCurvaturePairing
  apply Finset.sum_congr rfl
  intro p hp
  have haxes : SurfaceInfinite.globalPlaquetteAxes p.1.1 =
      FroehlichSpencer.FS82.Gaussian.latticeCellAxes p.1.1 := by
    ext i
    rfl
  rw [show SurfaceInfinite.cellOrientationSign p.1.1 =
      FroehlichSpencer.FS82.Gaussian.latticeCellOrientationSign p.1.1 by
      unfold SurfaceInfinite.cellOrientationSign
      rw [haxes]
      rfl]
  rfl

theorem source_root_293_internal :
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
  obtain ⟨b, hbpos, hbthr, hb⟩ := FiniteMomentBridge.exists_literal_threshold
  refine ⟨⟨b, hbpos⟩, rootPackingCoefficient, ?_, FiniteMomentBridge.tendsto_two_mul_rootPackingCoefficient,
    ?_, ?_, ?_⟩
  · intro β hβ
    exact rootPackingCoefficient_pos β
  · intro β hβ
    have hβpos : 0 < β := lt_of_lt_of_le hbpos hβ
    have hcpos : 0 < 2 * β * rootPackingCoefficient β :=
      mul_pos (mul_pos (by norm_num) hβpos) (rootPackingCoefficient_pos β)
    have hcone : 2 * β * rootPackingCoefficient β < 1 := hb β hβ
    unfold Surface.betaDoublePrime
    constructor <;> nlinarith
  · rw [FiniteMomentBridge.betaDoublePrime_eq]
    exact rootBetaDoublePrime_behavior.1
  · intro β hβRange L μ hμ σ hfill t
    have hβroot : rootBetaThreshold ≤ β := le_trans hbthr hβRange
    let Lint : Infinite.CubeCurvatureLimitState β (rootBeta_pos hβroot) :=
      cubeStateToInternal L
    have hμinternal : globallyCoClosed μ := by
      change globalBoundary (μ : FroehlichSpencer.FS82.Cubical.RealLatticeChain 4) = 0
      rw [← FroehlichSpencer.FS82.SurfaceInfiniteProof.surface_boundary_eq_global]
      exact hμ
    have hfillinternal : globalBoundary
        (σ : FroehlichSpencer.FS82.Cubical.RealLatticeChain 4) =
        (μ : FroehlichSpencer.FS82.Cubical.RealLatticeChain 4) := by
      rw [← FroehlichSpencer.FS82.SurfaceInfiniteProof.surface_boundary_eq_global]
      exact hfill
    have hroot := cubeCurvatureLimitState_sourceFilling_mgf_bounds
      hβroot Lint μ hμinternal σ hfillinternal t
    rw [FiniteMomentBridge.betaDoublePrime_eq]
    have hpair (x : SurfaceInfinite.fillingCurvatureIndexSet σ → ℤ) :
        SurfaceInfinite.fillingCurvaturePairing σ x =
          Infinite.sourceFillingCurvaturePairing σ x :=
      sourceFillingCurvaturePairing_eq_internal σ x
    have hmoment :
        (∫ x, Real.exp (t * SurfaceInfinite.fillingCurvaturePairing σ x) ∂
            (L.law (SurfaceInfinite.fillingCurvatureIndexSet σ)).toMeasure) =
          (∫ x, Real.exp (t * Infinite.sourceFillingCurvaturePairing σ x) ∂
            (Lint.law (Infinite.fillingCurvatureIndexSet σ)).toMeasure) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hpair x]
    rw [hmoment]
    rw [← sourceFourierGreenQuadratic_eq_internal] at hroot
    simpa [Lint, cubeStateToInternal] using hroot

end FroehlichSpencer.FS82.SurfaceInfinite
