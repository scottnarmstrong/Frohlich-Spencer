/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.GridLowerBound
public import FroehlichSpencer.BKT.Clock.VillainClock.ShiftLowerBound
import Mathlib.Tactic

/-!
# Exhausting limit points for Villain-clock disorder

The predicate `IsFreeSquareDisorderIndexedLimit` in `DisorderCarrier.lean` allows an arbitrary index
sequence, including a constant one, and therefore need not describe a thermodynamic limit. `IsFreeSquareDisorderExhaustingLimitPoint` below requires both strict
increase and divergence of the box indices. The strict-only `IsFreeSquareDisorderThermoLimitPoint`
is equivalent over natural-number sequences and is bridged explicitly.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

private theorem strictMono_nat_tendsto_atTop {s : ℕ → ℕ} (hs : StrictMono s) :
    Tendsto s atTop atTop := by
  have hle : ∀ n, n ≤ s n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hstep : s n < s (n + 1) := hs (Nat.lt_succ_self n)
      omega
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  exact hn.trans (hle n)

/-- A Villain-clock disorder limit point along boxes that genuinely exhaust the plane: the box
indices are strictly increasing and tend to infinity, and the corresponding seam expectations
converge. The predicate arbitrary-sequence `IsFreeSquareDisorderIndexedLimit` is not the source carrier. -/
def IsFreeSquareDisorderExhaustingLimitPoint (N r : ℕ) (β ξ c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) : Prop :=
  ∃ s : ℕ → ℕ, StrictMono s ∧ Tendsto s atTop atTop ∧
    Tendsto (fun t => freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr (s t)) atTop
      (𝓝 c)

/-- An exhausting disorder limit point is in particular an indexed limit. -/
theorem IsFreeSquareDisorderExhaustingLimitPoint.isFreeSquareDisorderIndexedLimit
    {N r : ℕ} {β ξ c : ℝ} {hβ : 0 < β} {hN : 0 < N} {hr : 0 < r}
    (h : IsFreeSquareDisorderExhaustingLimitPoint N r β ξ c hβ hN hr) :
    IsFreeSquareDisorderIndexedLimit N r β ξ c hβ hN hr := by
  obtain ⟨s, -, -, hs⟩ := h
  exact ⟨s, hs⟩

/-- The corrected exhausting carrier implies the prior strict-monotone thermodynamic carrier. -/
theorem IsFreeSquareDisorderExhaustingLimitPoint.isFreeSquareDisorderThermoLimitPoint
    {N r : ℕ} {β ξ c : ℝ} {hβ : 0 < β} {hN : 0 < N} {hr : 0 < r}
    (h : IsFreeSquareDisorderExhaustingLimitPoint N r β ξ c hβ hN hr) :
    IsFreeSquareDisorderThermoLimitPoint N r β ξ c hβ hN hr := by
  obtain ⟨s, hsmono, -, hs⟩ := h
  exact ⟨s, hsmono, hs⟩

/-- A limit along the existing strict-monotone carrier is genuinely exhausting: strict monotonicity
of natural-number indices implies that they tend to infinity. -/
theorem IsFreeSquareDisorderThermoLimitPoint.isExhaustingLimitPoint
    {N r : ℕ} {β ξ c : ℝ} {hβ : 0 < β} {hN : 0 < N} {hr : 0 < r}
    (h : IsFreeSquareDisorderThermoLimitPoint N r β ξ c hβ hN hr) :
    IsFreeSquareDisorderExhaustingLimitPoint N r β ξ c hβ hN hr := by
  obtain ⟨s, hsmono, hs⟩ := h
  exact ⟨s, hsmono, strictMono_nat_tendsto_atTop hsmono, hs⟩

/-- Uniform finite lower bounds pass to the corrected exhausting Villain-clock carrier. -/
theorem freeSquareDisorderExhaustingLimitPoint_ge_of_uniformLower (N r : ℕ) (β ξ b c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hfinite : ∀ t, b ≤ freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr t)
    (hc : IsFreeSquareDisorderExhaustingLimitPoint N r β ξ c hβ hN hr) : b ≤ c :=
  freeSquareDisorderIndexedLimit_ge_of_uniformLower N r β ξ b c hβ hN hr hfinite
    hc.isFreeSquareDisorderIndexedLimit

/-- Uniform finite power lower bounds pass to the corrected exhausting Villain-clock carrier. -/
theorem freeSquareDisorderExhaustingLimitPoint_ge_of_uniformPowerLower
    (N r : ℕ) (β ξ K β''' c : ℝ) (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hfinite : ∀ t,
      K * Real.rpow (1 + (r : ℝ)) (-(ξ ^ 2 * β''' / (2 * Real.pi))) ≤
        freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr t)
    (hc : IsFreeSquareDisorderExhaustingLimitPoint N r β ξ c hβ hN hr) :
    K * Real.rpow (1 + (r : ℝ)) (-(ξ ^ 2 * β''' / (2 * Real.pi))) ≤ c :=
  freeSquareDisorderIndexedLimit_ge_of_uniformPowerLower N r β ξ K β''' c hβ hN hr hfinite
    hc.isFreeSquareDisorderIndexedLimit

/-- Uniform finite upper bounds pass to the corrected exhausting Villain-clock carrier. -/
theorem freeSquareDisorderExhaustingLimitPoint_le_of_uniformUpper (N r : ℕ) (β ξ b c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hfinite : ∀ t, freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr t ≤ b)
    (hc : IsFreeSquareDisorderExhaustingLimitPoint N r β ξ c hβ hN hr) : c ≤ b :=
  freeSquareDisorderIndexedLimit_le_of_uniformUpper N r β ξ b c hβ hN hr hfinite
    hc.isFreeSquareDisorderIndexedLimit

/-- The finite straight-seam Villain shift lower bound passes to the corrected exhausting
carrier. -/
theorem freeSquareDisorderExhaustingLimitPoint_ge_villain_shift {r : ℕ} (N : ℕ) (β ξ c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hc : IsFreeSquareDisorderExhaustingLimitPoint N r β ξ c hβ hN hr) :
    Real.sqrt (Real.exp (-β * (2 * Real.pi * ξ) ^ 2) ^ r) ≤ c :=
  freeSquareDisorderIndexedLimit_ge_villain_shift N β ξ c hβ hN hr
    hc.isFreeSquareDisorderIndexedLimit

/-- FS81's Villain-clock (7.5) grid theorem on the corrected source carrier. It has the same
constants and grid quantifiers as `villainClock_disorder_lowerBound_grid`, while requiring every
limit point to arise along a strictly increasing, unbounded box sequence. -/
theorem villainClock_disorder_lowerBound_grid_exhausting :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N), n₁ β ≤ N →
        ∃ β''' : ℝ, 0 ≤ β''' ∧ ∃ C : ℝ, 0 < C ∧
          ∀ k : ℕ, 1 ≤ k → k < N →
            ∀ (r : ℕ) (hr : 0 < r) (c : ℝ),
              IsFreeSquareDisorderExhaustingLimitPoint N r β ((k : ℝ) / N) c hβ hN hr →
                C * (1 + (r : ℝ)) ^ (-(((k : ℝ) / N) ^ 2 * β''' / (2 * Real.pi))) ≤ c := by
  obtain ⟨n₁, hn₁, hgrid⟩ := villainClock_disorder_lowerBound_grid
  refine ⟨n₁, hn₁, ?_⟩
  intro β hβ N hN hn₁N
  obtain ⟨β''', hβ''', C, hC, hrest⟩ := hgrid β hβ N hN hn₁N
  refine ⟨β''', hβ''', C, hC, ?_⟩
  intro k hk0 hkN r hr c hc
  exact hrest k hk0 hkN r hr c hc.isFreeSquareDisorderThermoLimitPoint

end FroehlichSpencer.BKT.Clock.VillainClock

end
