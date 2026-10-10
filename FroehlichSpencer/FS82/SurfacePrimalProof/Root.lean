/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.SurfacePrimalProof.Expectation
public import FroehlichSpencer.FS82.SurfacePrimalProof.Face
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceCurvatureCorrelationNonsummable
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.StateIdentities
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.StationaryIdentities
public import FroehlichSpencer.FS82.Infinite.NonsummabilityPrimalLimit
import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Topology
namespace FroehlichSpencer.FS82.SurfaceInfinite

theorem source_primalFieldStrength_nonsummable_internal :
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
          ¬ AbsolutelySummableCorrelation (dualCurvatureCorrelation S) := by
  classical
  obtain ⟨b, hb⟩ := source_curvatureCorrelation_nonsummable
  let β₁ : {b : ℝ // 0 < b} :=
    ⟨max b.val Root.rootBetaThreshold, lt_of_lt_of_le b.property (le_max_left _ _)⟩
  refine ⟨β₁, ?_⟩
  intro β hβ
  have hβb : b.val ≤ β := le_trans (le_max_left _ _) hβ
  have hβroot : Root.rootBetaThreshold ≤ β := le_trans (le_max_right _ _) hβ
  obtain ⟨L, s, hs, S, hpoint, hinv, hns⟩ := hb β hβb
  refine ⟨L, s, hs, S, hpoint, hinv, ?_, hns⟩
  let Li := cubeStateToInternal L
  have hstate : (sourceCubeStateToCylinderState L).toInternal =
      Infinite.Nonsummability.cubeStateToCylinderState Li := rfl
  have hAvg (n : ℕ) (P : Finset GlobalPlaquette) :
      sourceAveragedCylinderLaw (sourceCubeStateToCylinderState L) n P =
        Infinite.Nonsummability.averagedCylinderLaw
          (Infinite.Nonsummability.cubeStateToCylinderState Li) n P :=
    (sourceAveragedCylinderLaw_eq_internal _ n P).trans
      (congrArg (fun T => Infinite.Nonsummability.averagedCylinderLaw T n P) hstate)
  have hp : ∀ P x, Tendsto
      (fun k => (Infinite.Nonsummability.averagedCylinderLaw
        (Infinite.Nonsummability.cubeStateToCylinderState Li) (s k) P x).toReal)
      atTop (𝓝 ((S.toInternal.law P x).toReal)) := by
    intro P x
    apply (hpoint P x).congr'
    exact Filter.Eventually.of_forall fun k =>
      congrArg (fun law : PMF (P → ℤ) => (law x).toReal) (hAvg (s k) P)
  have hi : ∀ a P, Infinite.Nonsummability.translateCylinderLaw S.toInternal a P =
      S.toInternal.law P := by
    intro a P
    exact (sourceTranslateCylinderLaw_eq_internal S a P).symm.trans (hinv a P)
  obtain ⟨m, hm, hclose⟩ :=
    Infinite.Nonsummability.primal_selectedActualPrimalFølnerCorrelation_eventually_close
      hβroot Li s S.toInternal hp hi
  refine ⟨m, hm, ?_⟩
  intro d hd ε hε
  obtain ⟨k₀, hk₀⟩ := hclose d hd ε hε
  refine ⟨max k₀ 1, ?_⟩
  intro k hk
  obtain ⟨hv, hdist⟩ := hk₀ k (le_trans (le_max_left _ _) hk)
  have hN : 0 < L.subsequence (m k) := by
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
    have hmk := hm.id_le k
    have hL := L.strictMono_subsequence.id_le (m k)
    exact lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hk1) (le_trans hmk hL)
  have hv' : ∀ a ∈ sourceShiftBox (s k), ∀ p ∈ pairPlaquettes
      (a 0, a 1, a 2, a 3) (d + (a 0, a 1, a 2, a 3)),
      inCube (Surface.centredCube (L.subsequence (m k)) hN) p := by
    intro a ha p hp
    exact (source_inCube_iff _ hN p).mpr (hv a ha p hp)
  refine ⟨hN, hv', ?_⟩
  have havg :
      (Fintype.card {a : SourceLatticeShift // a ∈ sourceShiftBox (s k)} : ℝ)⁻¹ *
                    ∑ a : {a : SourceLatticeShift // a ∈ sourceShiftBox (s k)},
                      (∫ θ : Surface.PrimalLinks
                          (Surface.centredCube (L.subsequence (m k)) hN) → ℝ,
                        sourcePrimalFieldStrength _ β (lt_of_lt_of_le β₁.property hβ) θ
                          (sourceC4PrimalFace (L.subsequence (m k)) hN
                            (dualCurvatureAt (a.val 0, a.val 1, a.val 2, a.val 3))
                            (hv' a.val a.property _ (by simp [pairPlaquettes]))) *
                        sourcePrimalFieldStrength _ β (lt_of_lt_of_le β₁.property hβ) θ
                          (sourceC4PrimalFace (L.subsequence (m k)) hN
                            (dualCurvatureAt (d + (a.val 0, a.val 1, a.val 2, a.val 3)))
                            (hv' a.val a.property _ (by simp [pairPlaquettes])))
                        ∂Surface.primalVillainLaw _ β
                          (lt_of_lt_of_le β₁.property hβ)).re =
      Infinite.Nonsummability.primalActualPrimalFølnerCorrelation
        (Li.subsequence (m k)) (s k) β (Root.rootBeta_pos hβroot) d hv := by
    unfold Infinite.Nonsummability.primalActualPrimalFølnerCorrelation
    congr 1
    apply Fintype.sum_congr
    intro a
    rw [sourcePrimalPairExpectation_eq_internal]
    rw [sourceC4PrimalFace_eq_primalFace, sourceC4PrimalFace_eq_primalFace]
    rfl
  rw [havg]
  exact hdist

end FroehlichSpencer.FS82.SurfaceInfinite
end
