/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Layer.Rate
public import FroehlichSpencer.BKT.PlaneRotator.TheoremC

/-!
# The pinned SOS carrier and its activity rate, unconditionally

The SOS branch uses the same comb charge layer as FS81 Theorem C: the Appendix D pinned layer
on `squareZero L` for the root-relative comb `pinnedCombLam`, which does not see the bond weight.

With `PlaneRotator.pinnedLayerHypothesisD_holds` it holds outright.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.SOS.Star

/-- **The pinned SOS carrier, unconditionally.** -/
theorem sosPinnedCarrierHypothesis_holds : SOSPinnedCarrierHypothesis :=
  PlaneRotator.pinnedLayerHypothesisD_holds

/-- **The uniform logarithmic SOS activity rate, unconditionally.** -/
theorem sos_uniform_activity_rate_holds :
    ∃ (D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ) (Kov L₀ : ℕ) (r T₀ : ℝ), 0 < r ∧ 1 ≤ T₀ ∧
      ∀ T, T₀ ≤ T → ∀ L, L₀ ≤ L → ∀ N, 1 ≤ N →
        ∃ Wit : PinnedLayerWitnessD L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov,
          ∀ i (ρ : RotatorDualFace L → ℤ), ρ ∈ Wit.layer.N i →
            |rootedActivityD Wit.layer (sosCost T) (sosKappa T) (sosAmp K₁ T)
                (sosCutoff (gradExponent α) T) i ρ| ≤
              Real.exp (-(r * T) * (∑ j, |(ρ j : ℝ)| + Wit.A ρ)) :=
  sos_uniform_activity_rate sosPinnedCarrierHypothesis_holds

end FroehlichSpencer.BKT.SOS.Layer

end
