/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockCorrelation
public import FroehlichSpencer.BKT.Bridge.ClockCorrelation
public import FroehlichSpencer.BKT.Bridge.ClockProfile
public import FroehlichSpencer.BKT.Clock.Source.Theorem71
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.clockCorrelation_highHarmonic_upper_bound`

This module contains `FroehlichSpencer.BKT.Provider.clockCorrelation_highHarmonic_upper_bound`, the
proof of the statement `FroehlichSpencer.BKT.clockCorrelation_highHarmonic_upper_bound` (file
`FroehlichSpencer/BKT/Surface/ClockHighHarmonicDecay.lean`, FS81 Theorem 7.1 (2)).

It is imported
only by that statement.

-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Clock
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)
open FroehlichSpencer.BKT.Bridge.ClockCorrelation (clockCorrelation_eq)
open FroehlichSpencer.BKT.Bridge.ClockProfile


theorem clockCorrelation_highHarmonic_upper_bound :
    ∃ n₀ : ℝ → ℝ → ℕ, (∀ q : ℝ, 0 < q → q < 1 → Tendsto (fun β => n₀ β q) atTop atTop) ∧
      (∀ β : ℝ, 0 ≤ β → Tendsto (fun q => n₀ β q) (𝓝[>] 0) atTop) ∧
      ∀ (β : ℝ) (hβ : 0 ≤ β) (q : ℝ), 0 < q → q < 1 → ∀ (n : ℕ) (hn : 0 < n), n₀ β q ≤ n →
        ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, 0 < A ∧ ∀ ξ : ℤ, 1 ≤ ξ → ξ ≤ (n : ℤ) - 1 →
          q ≤ min ((ξ : ℝ) / n) (1 - (ξ : ℝ) / n) → ∀ x : ℤ × ℤ,
            clockCorrelation n hn β hβ ξ 0 x ≤
              A * (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)) ^
                (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β''))) := by
  obtain ⟨-, -, n₀, β'', hgβ, hgq, hpos, h⟩ := Source.clock_theorem71_2_source
  refine ⟨n₀, fun q hq _ => hgβ q hq, hgq, fun β hβ q hq _ n hn hn₀ => ?_⟩
  refine ⟨β'' β n q, hpos β n q hn₀, 2, by norm_num, fun ξ h1 h2 hqξ x => ?_⟩
  obtain ⟨hξ0, hξn, hξ⟩ := harmonic_toNat (n := n) h1 h2
  have hlim := (h q hq β hβ n hn₀ hn ξ.toNat hξ0 hξn (by rw [dipoleGap_eq h1]; exact hqξ)).2 0 x
  have hp : (ξ.toNat : ℝ) ^ 2 / (2 * Real.pi * β'' β n q) =
      (ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q) := by
    rw [show ((ξ.toNat : ℕ) : ℝ) = (ξ : ℝ) by exact_mod_cast hξ]
  rw [hp] at hlim
  have hc : clockCorrelation n hn β hβ ξ 0 x =
      (clockModel n hn β hβ).twoPointLimit ((ξ.toNat : ℕ) : ℤ) 0 x := by
    rw [clockCorrelation_eq, hξ]
  rw [hc]
  refine hlim.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have : 0 ≤ (ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q) := by
    have := hpos β n q hn₀
    positivity
  exact l1Profile_le_euclidProfile this le_rfl x

end FroehlichSpencer.BKT.Provider

end
