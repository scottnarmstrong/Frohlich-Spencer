/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.SurfacePrimalProof.Root

@[expose] public section
open MeasureTheory Filter Topology
open FroehlichSpencer.FS82.SurfaceInfinite
namespace FroehlichSpencer.FS82.Provider.PrimalFieldStrengthNonsummability

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
          ¬ AbsolutelySummableCorrelation (dualCurvatureCorrelation S) := by
  exact FroehlichSpencer.FS82.SurfaceInfinite.source_primalFieldStrength_nonsummable_internal

end FroehlichSpencer.FS82.Provider.PrimalFieldStrengthNonsummability
end
