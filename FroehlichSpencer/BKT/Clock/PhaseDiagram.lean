/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.Limit
public import FroehlichSpencer.BKT.Clock.Peierls.ClockPeierls
public import FroehlichSpencer.BKT.Clock.Source.Result4
import Mathlib.Tactic

/-!
# The three phases of the Zn clock model

The high-temperature exponential-decay,
source-exact intermediate-window, and Peierls long-range-order theorems supply the three regimes.

Their defining estimates force beta_h <= beta_0 and beta_1(n) <= beta_bar(n), so the intervals
are ordered and disjoint.

For an arbitrary requested margin q, the incompatibility argument uses
the stronger margin min q (1/3), where the half harmonic is restricted for n >= 3; the resulting
upper bound then implies the one at q.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.Clock.Window
open FroehlichSpencer.BKT.Clock.Source
open FroehlichSpencer.BKT.Clock.HighTemp
open FroehlichSpencer.BKT.Clock.Peierls

namespace FroehlichSpencer.BKT.Clock

/-- **The three phases of the Zn clock model** (FS81 result 4 and §7.1, Remark 2). A common
high-temperature threshold beta_h and massless-window threshold beta_0 satisfy beta_h <= beta_0.
For every margin q > 0, the exact intermediate phase holds on [beta_0, beta_1(n)] for all
sufficiently large n, where beta_1(n) tends to infinity; a Peierls threshold beta_bar(n) satisfies
beta_1(n) <= beta_bar(n). Below beta_h the fundamental harmonic has exponential decay, and above
beta_bar(n) every harmonic has long-range order. The threshold inequalities make these three
temperature intervals pairwise disjoint. -/
theorem clock_phase_diagram :
    ∃ (βh β₀ : ℝ) (β' : ℝ → ℝ) (βbar : ∀ n : ℕ, 2 ≤ n → ℝ),
      0 < βh ∧ 0 < β₀ ∧ Tendsto β' atTop atTop ∧ βh ≤ β₀ ∧
      (∀ (n : ℕ) (hn : 2 ≤ n) (β : ℝ) (hβ : 0 ≤ β), βbar n hn < β →
        ∀ ξ : ℤ, ClockHasLongRangeOrder n (by omega) β hβ ξ) ∧
      ∀ (q : ℝ), 0 < q →
        ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧
          ∃ n₁ : ℕ, 3 ≤ n₁ ∧
            ∀ (n : ℕ) (hn3 : 3 ≤ n), n₁ ≤ n →
              β₀ < β₁ n ∧ β₁ n ≤ βbar n (by omega) ∧
              (∀ (β : ℝ) (hβ : 0 ≤ β), β < βh →
                ClockHasExpDecay n (by omega) β hβ 1) ∧
              (∀ (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ β₁ n →
                IsClockIntermediatePhaseExact n (by omega) β hβ q (β' β)) := by
  obtain ⟨βh, hβh, hhigh⟩ := clockHighTemperatureStatement_holds
  obtain ⟨β₀, hβ₀, β', hβ', hwindow⟩ := clock_massless_window_exact
  let βbar : ∀ n : ℕ, 2 ≤ n → ℝ := fun n hn =>
    Classical.choose (clockPeierlsStatement_holds n hn)
  have hbar : ∀ (n : ℕ) (hn : 2 ≤ n) (β : ℝ) (hβ : 0 ≤ β), βbar n hn < β →
      ∀ ξ : ℤ, ClockHasLongRangeOrder n (by omega) β hβ ξ := by
    intro n hn β hβ hβbar ξ
    exact Classical.choose_spec (clockPeierlsStatement_holds n hn) β hβ hβbar ξ
  have hthresholdOrder : βh ≤ β₀ := by
    by_contra hnot
    have hβ₀h : β₀ < βh := lt_of_not_ge hnot
    obtain ⟨β₁, hβ₁, n₀, hn₀⟩ := hwindow (1 / 3) (by norm_num)
    let n := max n₀ 3
    have hn₀n : n₀ ≤ n := le_max_left _ _
    have hn3 : 3 ≤ n := le_max_right _ _
    have hnpos : 0 < n := by omega
    have hN := hn₀ n hn₀n hnpos
    have hphase : IsClockIntermediatePhaseExact n (by omega) β₀ (le_of_lt hβ₀)
        (1 / 3) (β' β₀) :=
      hN.2 β₀ (le_of_lt hβ₀) le_rfl hN.1.le
    have hexp : ClockHasExpDecay n (by omega) β₀ (le_of_lt hβ₀) 1 :=
      hhigh n (by omega) β₀ (le_of_lt hβ₀) hβ₀h
    exact hphase.to_qualitative.massless 1 hexp
  refine ⟨βh, β₀, β', βbar, hβh, hβ₀, hβ', hthresholdOrder, hbar, ?_⟩
  intro q hq
  let q' : ℝ := min q (1 / 3)
  have hq' : 0 < q' := by
    dsimp [q']
    exact lt_min hq (by norm_num)
  have hq'le : q' ≤ q := min_le_left _ _
  have hq'third : q' ≤ (1 : ℝ) / 3 := min_le_right _ _
  obtain ⟨β₁, hβ₁, n₀, hn₀⟩ := hwindow q' hq'
  let n₁ : ℕ := max n₀ 3
  refine ⟨β₁, hβ₁, n₁, le_max_right _ _, ?_⟩
  intro n hn3 hn₁n
  have hn₀n : n₀ ≤ n := (le_max_left _ _).trans hn₁n
  have hnpos : 0 < n := by omega
  have hN := hn₀ n hn₀n hnpos
  have hthresholdOrderN : β₁ n ≤ βbar n (by omega) := by
    by_contra hnot
    have hbarlt : βbar n (by omega) < β₁ n := lt_of_not_ge hnot
    have hmaxlt : max β₀ (βbar n (by omega)) < β₁ n := max_lt_iff.mpr ⟨hN.1, hbarlt⟩
    let β : ℝ := (max β₀ (βbar n (by omega)) + β₁ n) / 2
    have hβ₀β : β₀ ≤ β := by
      dsimp [β]
      linarith [le_max_left β₀ (βbar n (by omega)), hmaxlt]
    have hββ₁ : β ≤ β₁ n := by
      dsimp [β]
      linarith
    have hbarβ : βbar n (by omega) < β := by
      dsimp [β]
      linarith [le_max_right β₀ (βbar n (by omega)), hmaxlt]
    have hβnonneg : 0 ≤ β := (le_of_lt hβ₀).trans hβ₀β
    have hphase' : IsClockIntermediatePhaseExact n (by omega) β hβnonneg q' (β' β) :=
      hN.2 β hβnonneg hβ₀β hββ₁
    have hphase : IsClockIntermediatePhaseExact n (by omega) β hβnonneg q (β' β) := by
      refine ⟨hphase'.lower, ?_⟩
      obtain ⟨β'', hβ'', C, hC, hup⟩ := hphase'.upper
      refine ⟨β'', hβ'', C, hC, ?_⟩
      intro ξ hξ0 hξn hqξ u v
      exact hup ξ hξ0 hξn (hq'le.trans hqξ) u v
    have hhalf := half_harmonic_restricted hn3 hq'third
    have hno := hphase'.to_qualitative.noLongRangeOrder hhalf.1 hhalf.2.1 hhalf.2.2
    have hlro := hbar n (by omega) β hβnonneg hbarβ (n / 2)
    exact hno hlro
  refine ⟨hN.1, hthresholdOrderN, ?_, ?_⟩
  · intro β hβ hβsmall
    exact hhigh n (by omega) β hβ hβsmall
  · intro β hβ hβ₀β hββ₁
    have hphase' : IsClockIntermediatePhaseExact n (by omega) β hβ q' (β' β) :=
      hN.2 β hβ hβ₀β hββ₁
    refine ⟨hphase'.lower, ?_⟩
    obtain ⟨β'', hβ'', C, hC, hup⟩ := hphase'.upper
    refine ⟨β'', hβ'', C, hC, ?_⟩
    intro ξ hξ0 hξn hqξ u v
    exact hup ξ hξ0 hξn (hq'le.trans hqξ) u v


end FroehlichSpencer.BKT.Clock

end
