module

public import FroehlichSpencer.FS82.SurfaceInfiniteProof.StationaryIdentities
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.StateIdentities
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.CurvatureCylinderModel
public import FroehlichSpencer.FS82.FiniteMomentBridge.LiteralRoot
public import FroehlichSpencer.FS82.Infinite.NonsummabilityPrimal
public import Mathlib.Tactic
@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SurfaceInfinite
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Nonsummability
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.Comparison

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable def CurvatureCylinderState.ofInternal
    (S : Infinite.Nonsummability.CurvatureCylinderState) : CurvatureCylinderState where
  law := S.law
  consistent := S.consistent

theorem sourceDualCurvatureCorrelation_eq_selectedState
    (S : FroehlichSpencer.FS82.CurvatureStateBridge.SourceCurvatureCylinderState)
    (d : SurfaceInfinite.LatticePoint) :
    SurfaceInfinite.dualCurvatureCorrelation (CurvatureCylinderState.ofInternal S.toInternal) d =
      FroehlichSpencer.FS82.CurvatureStateBridge.sourceFieldStrengthCorrelation S d := by
  rfl

theorem source_root_211_withRates :
    ∃ β₀ : {b : ℝ // 0 < b}, ∃ cPack : ℝ → ℝ,
      (∀ β, β₀.val ≤ β → 0 < cPack β) ∧
      Tendsto (fun β : ℝ => 2 * β * cPack β) atTop (𝓝 0) ∧
      (∀ β, β₀.val ≤ β →
        0 < Surface.betaDoublePrime cPack β ∧
        Surface.betaDoublePrime cPack β < β) ∧
      Tendsto (Surface.betaDoublePrime cPack) atTop atTop ∧
      ∃ B : ℝ,
        (∀ β, B ≤ β → 0 < Surface.betaDoublePrime cPack β) ∧
        ∀ (β : ℝ) (hβ : max β₀.val B ≤ β),
          ∃ L : SurfaceInfinite.CubeCurvatureLimitState β
              (lt_of_lt_of_le β₀.property (le_trans (le_max_left β₀.val B) hβ)),
            ∃ s : ℕ → ℕ, StrictMono s ∧
              ∃ S : SurfaceInfinite.CurvatureCylinderState,
                (∀ P x, Tendsto
                  (fun k => (SurfaceInfinite.sourceAveragedCylinderLaw
                    (SurfaceInfinite.sourceCubeStateToCylinderState L) (s k) P x).toReal)
                  atTop (𝓝 ((S.law P x).toReal))) ∧
                (∀ a P, SurfaceInfinite.sourceTranslateCylinderLaw S a P = S.law P) ∧
                ¬ SurfaceInfinite.AbsolutelySummableCorrelation
                  (SurfaceInfinite.dualCurvatureCorrelation S) := by
  obtain ⟨b, hbpos, hbthr, hb⟩ := FiniteMomentBridge.exists_literal_threshold
  obtain ⟨B, hB, hroot⟩ :=
    FroehlichSpencer.FS82.CurvatureStateBridge.source_stationary_nonsummability_from_internal_root
  refine ⟨⟨b, hbpos⟩, rootPackingCoefficient, ?_, FiniteMomentBridge.tendsto_two_mul_rootPackingCoefficient,
    ?_, ?_, B, ?_, ?_⟩
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
  · intro β hβ
    have h := hB β hβ
    simpa [FiniteMomentBridge.betaDoublePrime_eq] using h
  · intro β hβ
    have hβb : b ≤ β := le_trans (le_max_left b B) hβ
    have hβB : B ≤ β := le_trans (le_max_right b B) hβ
    have hβroot : max rootBetaThreshold B ≤ β := by
      apply max_le
      · exact le_trans hbthr hβb
      · exact hβB
    obtain ⟨Lint, s, hs, SS, hpoint, hinv, hns⟩ := hroot β hβroot
    let L : SurfaceInfinite.CubeCurvatureLimitState β
        (lt_of_lt_of_le hbpos hβb) := cubeStateOfInternal Lint
    let S : SurfaceInfinite.CurvatureCylinderState :=
      CurvatureCylinderState.ofInternal SS.toInternal
    have hstate : (sourceCubeStateToCylinderState L).toInternal =
        Infinite.Nonsummability.cubeStateToCylinderState Lint := by
      change Infinite.Nonsummability.CurvatureCylinderState.mk
          L.law L.consistent =
        Infinite.Nonsummability.CurvatureCylinderState.mk
          Lint.law Lint.consistent
      have hlaw : L.law = Lint.law := rfl
      cases hlaw
      have hcons : L.consistent = Lint.consistent := Subsingleton.elim _ _
      cases hcons
      rfl
    have hAvg (n : ℕ) (P : Finset GlobalPlaquette) :
        sourceAveragedCylinderLaw (sourceCubeStateToCylinderState L) n P =
          Infinite.Nonsummability.averagedCylinderLaw
            (Infinite.Nonsummability.cubeStateToCylinderState Lint) n P := by
      rw [sourceAveragedCylinderLaw_eq_internal, hstate]
    have hpoint' : ∀ P x, Tendsto
        (fun k => (sourceAveragedCylinderLaw
          (sourceCubeStateToCylinderState L) (s k) P x).toReal) atTop
        (𝓝 ((S.law P x).toReal)) := by
      intro P x
      have hseq : (fun k => (sourceAveragedCylinderLaw
          (sourceCubeStateToCylinderState L) (s k) P x).toReal) =
          (fun k => (Infinite.Nonsummability.averagedCylinderLaw
            (Infinite.Nonsummability.cubeStateToCylinderState Lint)
            (s k) P x).toReal) := by
        funext k
        exact congrArg (fun q : PMF (P → ℤ) => (q x).toReal) (hAvg (s k) P)
      rw [hseq]
      change Tendsto (fun k =>
        (Infinite.Nonsummability.averagedCylinderLaw
          (Infinite.Nonsummability.cubeStateToCylinderState Lint)
          (s k) P x).toReal) atTop
        (𝓝 ((SS.toInternal.law P x).toReal))
      exact hpoint P x
    have hinv' : ∀ a P, sourceTranslateCylinderLaw S a P = S.law P := by
      intro a P
      rw [sourceTranslateCylinderLaw_eq_internal]
      have hSInternal : S.toInternal = SS.toInternal := by
        change (CurvatureCylinderState.ofInternal SS.toInternal).toInternal =
          SS.toInternal
        cases SS.toInternal
        rfl
      rw [hSInternal]
      exact hinv a P
    have hns' : ¬ SurfaceInfinite.AbsolutelySummableCorrelation
        (SurfaceInfinite.dualCurvatureCorrelation S) := by
      intro habs
      apply hns
      change Summable (fun d =>
        |SurfaceInfinite.dualCurvatureCorrelation
          (CurvatureCylinderState.ofInternal SS.toInternal) d|) at habs
      simpa [SurfaceInfinite.AbsolutelySummableCorrelation,
        FroehlichSpencer.FS82.CurvatureStateBridge.AbsolutelySummableCorrelation,
        sourceDualCurvatureCorrelation_eq_selectedState] using habs
    exact ⟨L, s, hs, S, hpoint', hinv', hns'⟩

/-- The source root needs only one sufficiently large positive inverse temperature.
Its witness is independent of the finite-root rate constants. -/
theorem source_root_211_internal :
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
  obtain ⟨β₀, cPack, _, _, _, _, B, _, hroot⟩ := source_root_211_withRates
  let β₁ : {b : ℝ // 0 < b} :=
    ⟨max β₀.val B, lt_of_lt_of_le β₀.property (le_max_left _ _)⟩
  refine ⟨β₁, ?_⟩
  intro β hβ
  have hβ' : max β₀.val B ≤ β := by
    simpa [β₁] using hβ
  obtain ⟨L, s, hs, S, hpoint, hinv, hns⟩ := hroot β hβ'
  exact ⟨L, s, hs, S, hpoint, hinv, hns⟩

end FroehlichSpencer.FS82.SurfaceInfinite
