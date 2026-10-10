/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.SurfacePrimal.SourcePrimalFieldStrengthNonsummable
public import FroehlichSpencer.FS82.SurfacePrimalProof.Finite

@[expose] public section
open MeasureTheory Filter Topology
namespace FroehlichSpencer.FS82.SurfaceInfinite

theorem sourcePrimalPackage_jointWitnesses :
    ∃ β₁ : {b : ℝ // 0 < b}, ∃ β, ∃ hβ : β₁.val ≤ β,
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
  obtain ⟨β₁, h⟩ := source_primalFieldStrength_nonsummable
  exact ⟨β₁, β₁.val, le_rfl, h β₁.val le_rfl⟩

/-- The root's actual diagonal selection has contained faces eventually for
every fixed nonzero displacement, independently of any tolerance binder. -/
theorem sourcePrimalPackage_containedSelection :
    ∃ β₁ : {b : ℝ // 0 < b}, ∀ β (hβ : β₁.val ≤ β),
      ∃ L : CubeCurvatureLimitState β (lt_of_lt_of_le β₁.property hβ),
        ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ m : ℕ → ℕ, StrictMono m ∧
          ∀ d : LatticePoint, d ≠ 0 → ∃ k₀, ∀ k ≥ k₀,
            ∃ hN : 0 < L.subsequence (m k),
              ∀ a ∈ sourceShiftBox (s k), ∀ p ∈ pairPlaquettes
                (a 0, a 1, a 2, a 3) (d + (a 0, a 1, a 2, a 3)),
                inCube (Surface.centredCube (L.subsequence (m k)) hN) p := by
  obtain ⟨β₁, hroot⟩ := source_primalFieldStrength_nonsummable
  refine ⟨β₁, ?_⟩
  intro β hβ
  obtain ⟨L, s, hs, S, hpoint, hinv, hm, hns⟩ := hroot β hβ
  obtain ⟨m, hmono, hclose⟩ := hm
  refine ⟨L, s, hs, m, hmono, ?_⟩
  intro d hd
  obtain ⟨k₀, hk₀⟩ := hclose d hd 1 zero_lt_one
  refine ⟨k₀, ?_⟩
  intro k hk
  obtain ⟨hN, hv, _⟩ := hk₀ k hk
  exact ⟨hN, hv⟩

end FroehlichSpencer.FS82.SurfaceInfinite
end
