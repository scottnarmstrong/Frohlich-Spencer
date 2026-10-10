/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3CertTerminal
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3DecompTerminal
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileBCombinatorics
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileGSplit
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileAAssembly
public import FroehlichSpencer.BKT.Villain.TheoremC.MainD

/-!
# FS81 Theorem C, unconditionally (internal, non-)

Fröhlich–Spencer (1981), Theorem C (J p. 534) and (6.1) (J p. 575): for large inverse temperature
the free infinite-volume two-point functions of the plane rotator and of the Villain model obey a
power-law lower bound, for every integer harmonic `ξ`, with exponent `ξ²/(2πβ'(β))`,
`β' > 1/(4π)` and `β' → ∞`; and the plane rotator has a Kosterlitz–Thouless transition.

This module only composes results:

* `pinnedLayerHypothesisD_holds` discharges `PinnedLayerHypothesisD`, the Appendix D pinned
  charge layer, through the chain:
  - the selection expansion (`SelectionG*`);
  - the witness assembly (`Layer*`, `LayerRoutine*`);
  - the corrected profile split: part (A) is `TerminalProfileA*`, part (B) is
    `badSelectedBound_proof`;
  - the collapsed-metric support control (`TerminalProfileA3*`), with the component
    decomposition `terminalProfileA3UniqueMaxDecompositionLarge`.
* The rotator statement comes from `theoremC_of_supportControl`, the Villain statement from
  `villain_theoremC_of_pinnedLayerD`, and the transition from `exists_transition_of_supportControl`.
-/

@[expose] public section

open Filter
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Rotator.Transition
open FroehlichSpencer.BKT.Rotator.Ginibre

namespace FroehlichSpencer.BKT.PlaneRotator

/-- The collapsed-metric support control holds for every comb terminal. -/
theorem supportControl_holds : TerminalSupportControl :=
  terminalSupportControl_of_collapsed (terminalCollapsedSupportControl_of_large
    (terminalCollapsedSupportControlLarge_of_rootedComponents
      (terminalRootedComponentsLarge_of_decomposition terminalProfileA3UniqueMaxDecompositionLarge)))

/-- The FS81 Appendix D pinned charge layer, unconditionally. -/
theorem pinnedLayerHypothesisD_holds : PinnedLayerHypothesisD :=
  pinnedLayerHypothesisD_of_terminalWavesW
    (Real.log_nonneg (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
    combCoefficientBound (α := 7 / 4) (by norm_num) (lt_max_of_lt_left (by norm_num))
    (lt_max_of_lt_left (by norm_num)) (by norm_num : (0 : ℝ) < 1 / 3) routineKv_nonneg
    (pinnedTerminalWavesW_of_profilesW (by norm_num)
      (pinnedTerminalProfilesW_of_split
        (pinnedTerminalProfilesG_of_supportControl (by norm_num) supportControl_holds)
        badSelectedBound_proof))

/-- **FS81 Theorem C and (6.1), plane rotator**: the free infinite-volume two-point function. -/
theorem rotator_theoremC :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            freeTwoPointLimit β hβ ξ u v :=
  theoremC_of_supportControl supportControl_holds

/-- **The Kosterlitz–Thouless transition for the plane rotator**: a single `β_c ≥ 1/2` with
exponential decay below it and neither exponential decay nor long-range order above it. -/
theorem rotator_kt_transition :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) :=
  exists_transition_of_supportControl supportControl_holds

/-- **FS81 Theorem C and (6.1), Villain model**: the free infinite-volume two-point function. -/
theorem villain_theoremC :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ β (hβ : 0 < β), β₀ ≤ β →
        1 / (4 * Real.pi) < β' β ∧
          ∀ (ξ : ℤ) (u v : ℤ × ℤ),
            Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
                ((l1Norm (u - v) : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
              (FroehlichSpencer.BKT.Ginibre.villainModel β hβ).twoPointLimit ξ u v :=
  FroehlichSpencer.BKT.Villain.TheoremC.villain_theoremC_of_pinnedLayerD pinnedLayerHypothesisD_holds

end FroehlichSpencer.BKT.PlaneRotator

end
