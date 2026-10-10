/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ClockDisorder
import Mathlib.Tactic

/-!
# Provider: FS81 (7.5) fails off the grid

At `β = 1`, `n = n₁(1) + 1`, `ξ = 1/(2n)`, every joint limit value satisfies `D r ≤ λ^r` with
`λ < 1` (`clockDisorderLimitPoint_le_pow`), which beats every power `C (1 + r)^{-B}`
(`exists_pow_lt_rpow`); a joint limit exists (`exists_clockDisorderLimit`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Clock.Disorder
open FroehlichSpencer.BKT.Bridge.ClockDisorder


theorem not_clock_disorder_lowerBound_offGrid :
    ¬ ∃ n₁ : ℝ → ℕ, ∀ β : ℝ, 0 < β → ∀ (n : ℕ) (hn : 0 < n), n₁ β ≤ n →
      ∃ β''' : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ C : ℝ, 0 < C ∧
        ∀ D : ℕ → ℝ, IsClockDisorderLimit n hn β ξ D → ∀ r : ℕ, 0 < r →
          C * (1 + (r : ℝ)) ^ (-(ξ ^ 2 * β''' / (2 * Real.pi))) ≤ D r := by
  rintro ⟨n₁, h⟩
  have hN : 0 < n₁ 1 + 1 := Nat.succ_pos _
  obtain ⟨β''', hb⟩ := h 1 one_pos (n₁ 1 + 1) hN (Nat.le_succ _)
  obtain ⟨hξ0, hξ1, hξZ⟩ := offGrid_xi hN
  obtain ⟨C, hC, hlow⟩ := hb _ hξ0 hξ1
  obtain ⟨lam, hlam0, hlam1, hle⟩ := clockDisorderLimitPoint_le_pow hN one_pos hξZ
  obtain ⟨r, hr, hlt⟩ := exists_pow_lt_rpow hlam0 hlam1 hC
    ((1 / (2 * ((n₁ 1 + 1 : ℕ) : ℝ))) ^ 2 * β''' / (2 * Real.pi))
  obtain ⟨D, hD⟩ := exists_clockDisorderLimit (n₁ 1 + 1) hN 1 (1 / (2 * ((n₁ 1 + 1 : ℕ) : ℝ)))
  have h1 := hlow D hD r hr
  have h2 := hle r hr (D r) (isClockDisorderLimitPoint_of_limit hD r hr)
  linarith
end FroehlichSpencer.BKT.Provider

end
