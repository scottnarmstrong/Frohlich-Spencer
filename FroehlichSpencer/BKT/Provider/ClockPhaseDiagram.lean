/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ClockPhases
public import FroehlichSpencer.BKT.Bridge.ClockIntermediatePhase
public import FroehlichSpencer.BKT.Surface.ClockIntermediatePhase
public import FroehlichSpencer.BKT.Clock.PhaseDiagram
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.clock_phase_diagram`

This module contains `FroehlichSpencer.BKT.Provider.clock_phase_diagram`, the proof of the
statement `FroehlichSpencer.BKT.clock_phase_diagram` (file
`FroehlichSpencer/BKT/Surface/ClockPhaseDiagram.lean`, the phase diagram).

The internal `Clock.clock_phase_diagram` states its high-temperature clause only for large `n`; the
proof is replayed with `β_h` from the high-temperature statement (every `n ≥ 2`), `β₀`, `β'` from
the massless window and `β̄(n)` from the Peierls statement.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Clock
open FroehlichSpencer.BKT.Clock.Window FroehlichSpencer.BKT.Clock.Source
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)
open FroehlichSpencer.BKT.Bridge.ClockPhases
  (isClockExpDecay_of_internal isClockLongRangeOrder_of_internal)
open FroehlichSpencer.BKT.Bridge.ClockIntermediatePhase (isClockIntermediatePhase_of_exact)

/--
The internal `Clock.clock_phase_diagram` states
its high-temperature clause only for large `n`; here the proof is replayed with `β_h` from the
high-temperature statement (every `n ≥ 2`), `β₀`, `β'` from the massless window and `β̄(n)` from the
Peierls statement, and the two orderings are re-derived as there.
-/
theorem clock_phase_diagram :
    ∃ βh β₀ : ℝ, 0 < βh ∧ βh ≤ β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧ ∃ βbar : ℕ → ℝ,
      (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), β < βh →
        IsClockExpDecay n hn β hβ 1) ∧
      (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), βbar n < β →
        ∀ ξ : ℤ, IsClockLongRangeOrder n hn β hβ ξ) ∧
      ∀ q : ℝ, 0 < q → q < 1 → ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧ ∃ n₁ : ℕ,
        ∀ (n : ℕ) (hn : 0 < n), n₁ ≤ n → β₀ < β₁ n ∧ β₁ n ≤ βbar n ∧
          ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ β₁ n →
            IsClockIntermediatePhase n hn β hβ q (β' β) := by
  obtain ⟨βh, hβh, hhigh⟩ := HighTemp.clockHighTemperatureStatement_holds
  obtain ⟨β₀, hβ₀, β', hβ', hwindow⟩ := Source.clock_massless_window_exact
  let βbar : ℕ → ℝ := fun n =>
    if h : 2 ≤ n then Classical.choose (Peierls.clockPeierlsStatement_holds n h) else 0
  have hbar : ∀ (n : ℕ) (hn : 2 ≤ n) (β : ℝ) (hβ : 0 ≤ β), βbar n < β →
      ∀ ξ : ℤ, ClockHasLongRangeOrder n (by omega) β hβ ξ := by
    intro n hn β hβ hlt ξ
    have hb : βbar n = Classical.choose (Peierls.clockPeierlsStatement_holds n hn) :=
      dite_eq_left hn
    rw [hb] at hlt
    exact Classical.choose_spec (Peierls.clockPeierlsStatement_holds n hn) β hβ hlt ξ
  have hthresholdOrder : βh ≤ β₀ := by
    by_contra hnot
    have hβ₀h : β₀ < βh := lt_of_not_ge hnot
    obtain ⟨β₁, -, n₀, hn₀⟩ := hwindow (1 / 3) (by norm_num)
    let n := max n₀ 3
    have hN := hn₀ n (le_max_left _ _) (by omega)
    have hphase : IsClockIntermediatePhaseExact n (by omega) β₀ (le_of_lt hβ₀) (1 / 3) (β' β₀) :=
      hN.2 β₀ (le_of_lt hβ₀) le_rfl hN.1.le
    have hexp : ClockHasExpDecay n (by omega) β₀ (le_of_lt hβ₀) 1 :=
      hhigh n (by omega) β₀ (le_of_lt hβ₀) hβ₀h
    exact hphase.to_qualitative.massless 1 hexp
  refine ⟨βh, β₀, hβh, hthresholdOrder, β', hβ', βbar, ?_, ?_, ?_⟩
  · intro n hn h2 β hβ hlt
    exact isClockExpDecay_of_internal hn hβ (hhigh n h2 β hβ hlt)
  · intro n hn h2 β hβ hlt ξ
    exact isClockLongRangeOrder_of_internal hn hβ (hbar n h2 β hβ hlt ξ)
  · intro q hq _
    let q' : ℝ := min q (1 / 3)
    have hq' : 0 < q' := lt_min hq (by norm_num)
    have hq'le : q' ≤ q := min_le_left _ _
    have hq'third : q' ≤ (1 : ℝ) / 3 := min_le_right _ _
    obtain ⟨β₁, hβ₁, n₀, hn₀⟩ := hwindow q' hq'
    refine ⟨β₁, hβ₁, max n₀ 3, fun n hn hn₁n => ?_⟩
    have hn3 : 3 ≤ n := (le_max_right _ _).trans hn₁n
    have hN := hn₀ n ((le_max_left _ _).trans hn₁n) hn
    have hordN : β₁ n ≤ βbar n := by
      by_contra hnot
      have hbarlt : βbar n < β₁ n := lt_of_not_ge hnot
      have hmaxlt : max β₀ (βbar n) < β₁ n := max_lt_iff.mpr ⟨hN.1, hbarlt⟩
      let β : ℝ := (max β₀ (βbar n) + β₁ n) / 2
      have hβ₀β : β₀ ≤ β := by dsimp [β]; linarith [le_max_left β₀ (βbar n), hmaxlt]
      have hββ₁ : β ≤ β₁ n := by dsimp [β]; linarith
      have hbarβ : βbar n < β := by dsimp [β]; linarith [le_max_right β₀ (βbar n), hmaxlt]
      have hβnonneg : 0 ≤ β := (le_of_lt hβ₀).trans hβ₀β
      have hphase' : IsClockIntermediatePhaseExact n hn β hβnonneg q' (β' β) :=
        hN.2 β hβnonneg hβ₀β hββ₁
      have hhalf := half_harmonic_restricted hn3 hq'third
      have hno := hphase'.to_qualitative.noLongRangeOrder hhalf.1 hhalf.2.1 hhalf.2.2
      exact hno (hbar n (by omega) β hβnonneg hbarβ ((n / 2 : ℕ) : ℤ))
    refine ⟨hN.1, hordN, fun β hβ hlo hhi => ?_⟩
    have hphase' : IsClockIntermediatePhaseExact n hn β hβ q' (β' β) := hN.2 β hβ hlo hhi
    refine isClockIntermediatePhase_of_exact hn hβ ⟨hphase'.lower, ?_⟩
    obtain ⟨β'', hβ'', C, hC, hup⟩ := hphase'.upper
    exact ⟨β'', hβ'', C, hC, fun ξ hξ0 hξn hqξ u v => hup ξ hξ0 hξn (hq'le.trans hqξ) u v⟩

end FroehlichSpencer.BKT.Provider

end
