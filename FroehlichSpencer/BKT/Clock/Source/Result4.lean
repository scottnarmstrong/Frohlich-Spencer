/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Window.MasslessWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Source-exact FS81 result 4 and (7.3)–(7.4)

`IsClockIntermediatePhaseExact` fixes the printed exponent in (7.3) using one scale `b` for every
integer harmonic, and uses one finite `β''` for all restricted harmonics in (7.4). The window below
uses the plane-rotator scale `β'(β)` from Theorem C. Source: FS81 result 4, J p. 528, and Theorem
7.1, Remark 2, (7.3)–(7.4), J pp. 585–586; FS81.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Clock.Window
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Source

/-- The printed (7.3)–(7.4) intermediate-phase predicate, with its common lower scale `b` fixed.
The upper exponent uses a single finite `β''` and prefactor `C` for every restricted harmonic. -/
structure IsClockIntermediatePhaseExact (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β)
    (q b : ℝ) : Prop where
  lower : 1 / (4 * Real.pi) < b ∧ ∀ ξ : ℤ, ∀ u v : ℤ × ℤ,
    Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * b))) *
      ((l1Dist u v : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * b))) ≤
        clockCorr n hn β hβ ξ u v
  upper : ∃ β'' : ℝ, 0 < β'' ∧ ∃ C : ℝ, 0 < C ∧
    ∀ ξ : ℕ, 0 < ξ → ξ < n → q ≤ dipoleGap ((ξ : ℝ) / n) → ∀ u v : ℤ × ℤ,
      clockCorr n hn β hβ ξ u v ≤
        C * ((l1Dist u v : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'')))

theorem IsClockIntermediatePhaseExact.to_qualitative {n : ℕ} {hn : 0 < n} {β : ℝ}
    {hβ : 0 ≤ β} {q b : ℝ} (h : IsClockIntermediatePhaseExact n hn β hβ q b) :
    IsClockIntermediatePhase n hn β hβ q := by
  refine ⟨?_, ?_⟩
  · intro ξ
    refine ⟨Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * b))),
      (ξ : ℝ) ^ 2 / (2 * Real.pi * b), Real.exp_pos _, ?_⟩
    exact h.lower.2 ξ
  · intro ξ hξ0 hξn hq
    obtain ⟨β'', hβ'', C, hC, hup⟩ := h.upper
    let p : ℝ := (ξ : ℝ) ^ 2 / (2 * Real.pi * β'')
    have hp : 0 < p := by
      dsimp [p]
      have hξ : (0 : ℝ) < ξ := by exact_mod_cast hξ0
      exact div_pos (sq_pos_of_pos hξ) (by positivity)
    exact ⟨C, p, hp, fun u v => by simpa [p] using hup ξ hξ0 hξn hq u v⟩

private theorem sourceDecayExponent_le {c : ℝ} (hc : 0 < c) {n ξ : ℕ} (hn : 0 < n)
    (hξn : ξ < n) :
    (ξ : ℝ) ^ 2 / (2 * Real.pi * ((n : ℝ) ^ 2 / (2 * Real.pi * c))) ≤ c := by
  have hξ : (ξ : ℝ) ≤ n := by exact_mod_cast hξn.le
  have hsq : (ξ : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : c ≠ 0 := hc.ne'
  have hn' : (n : ℝ) ≠ 0 := hnR.ne'
  field_simp [Real.pi_ne_zero, hc']
  nlinarith

/-- **FS81 result 4 in its source-exact (7.3)–(7.4) predicate.** There are a lower temperature
scale `β₀ > 0` and the Theorem C function `β'` with `β'(β) → ∞`; for every margin `q > 0` there
are `β₁(n) → ∞` and `n₁` such that the exact predicate holds throughout `[β₀, β₁(n)]` for each
`n ≥ n₁`, with its lower scale equal to `β'(β)`. The quantifier order matches
`Window.clock_massless_window`. -/
theorem clock_massless_window_exact :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ q : ℝ, 0 < q → ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧
        ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ hn : 0 < n, β₀ < β₁ n ∧
          ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ β₁ n →
            IsClockIntermediatePhaseExact n hn β hβ q (β' β) := by
  obtain ⟨βlo, hβlo, _⟩ := clock_powerLaw_lower
  obtain ⟨β73, β', hβ', h73⟩ := clock_theorem73
  obtain ⟨c, hc, hup⟩ := clock_powerLaw_upper_uniform
  let β₀ := max βlo β73
  have hβ₀ : 0 < β₀ := by dsimp [β₀]; positivity
  refine ⟨β₀, hβ₀, β', hβ', fun q hq => ?_⟩
  choose n₀ hn₀ hN using fun B : ℝ => hup q hq (max B 0) (le_max_right _ _)
  obtain ⟨β₁, hβ₁, n₁, hn₁⟩ := exists_window_of_thresholds β₀ n₀
  refine ⟨β₁, hβ₁, n₁, fun n hn => ?_⟩
  have hwindow := hn₁ n hn
  intro hnpos
  refine ⟨hwindow.1, fun β hβ hβ₀β hβ₁β => ?_⟩
  have hupper := hN (β₁ n) n hwindow.2 hnpos β hβ (hβ₁β.trans (le_max_left _ _))
  have hlower := h73 n hnpos β hβ ((le_max_right _ _).trans hβ₀β)
  refine ⟨⟨hlower.1, fun ξ u v => hlower.2 ξ u v⟩, ?_⟩
  let β'' : ℝ := (n : ℝ) ^ 2 / (2 * Real.pi * c)
  have hβ'' : 0 < β'' := by
    dsimp [β'']
    exact div_pos (sq_pos_of_pos (by exact_mod_cast hnpos)) (by positivity)
  refine ⟨β'', hβ'', 2, by norm_num, fun ξ hξ0 hξn hqξ u v => ?_⟩
  have hα : (ξ : ℝ) ^ 2 / (2 * Real.pi * β'') ≤ c := by
    simpa [β''] using sourceDecayExponent_le hc hnpos hξn
  have hd : 0 ≤ (l1Dist u v : ℝ) := by exact_mod_cast Nat.zero_le (l1Dist u v)
  have hx : 1 ≤ (l1Dist u v : ℝ) + 1 := by linarith
  have hpow : ((l1Dist u v : ℝ) + 1) ^ (-c) ≤
      ((l1Dist u v : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β''))) :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hα)
  have hscale : 2 * ((l1Dist u v : ℝ) + 1) ^ (-c) ≤
      2 * ((l1Dist u v : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β''))) :=
    mul_le_mul_of_nonneg_left hpow (by norm_num)
  exact (hupper ξ hξ0 hξn hqξ u v).trans hscale

end FroehlichSpencer.BKT.Clock.Source

end
