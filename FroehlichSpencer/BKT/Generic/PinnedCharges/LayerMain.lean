/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerCoefficient
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerWitness

/-!
With the coefficient bound proved along the selection (`combCoefficientBound`), the pinned layer
hypothesis — and with it FS81 Theorem C (6.1) and the Kosterlitz–Thouless transition for the plane
rotator — follows from the single statement `PinnedTerminalWaves`: the Appendix D multiscale spin
waves on the terminal ensembles of the scale-ordered selection.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open Filter
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator.TheoremC

/-- **The pinned layer hypothesis from the terminal waves.** -/
theorem pinnedLayerHypothesisD_of_pinnedTerminalWaves {α K₀ K₁ cP Kv : ℝ} {Kov L₀ : ℕ}
    (hα : 1 < α) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hcP : 0 < cP) (hKv : 0 ≤ Kv)
    (hW : PinnedTerminalWaves α K₀ K₁ cP Kv Kov L₀) : PinnedLayerHypothesisD :=
  pinnedLayerHypothesisD_of_terminalWaves (Real.log_nonneg (by norm_num))
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))) combCoefficientBound hα hK₀
    hK₁ hcP hKv hW

/-- **FS81 Theorem C from the terminal waves.** -/
theorem theoremC_of_pinnedTerminalWaves {α K₀ K₁ cP Kv : ℝ} {Kov L₀ : ℕ}
    (hα : 1 < α) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hcP : 0 < cP) (hKv : 0 ≤ Kv)
    (hW : PinnedTerminalWaves α K₀ K₁ cP Kv Kov L₀) :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v :=
  theoremC_of_pinnedLayerD (pinnedLayerHypothesisD_of_pinnedTerminalWaves hα hK₀ hK₁ hcP hKv hW)

/-- **The Kosterlitz–Thouless transition from the terminal waves.** -/
theorem exists_transition_of_pinnedTerminalWaves {α K₀ K₁ cP Kv : ℝ} {Kov L₀ : ℕ}
    (hα : 1 < α) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hcP : 0 < cP) (hKv : 0 ≤ Kv)
    (hW : PinnedTerminalWaves α K₀ K₁ cP Kv Kov L₀) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_pinnedLayerD
    (pinnedLayerHypothesisD_of_pinnedTerminalWaves hα hK₀ hK₁ hcP hKv hW)

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
