/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.Models

/-!
# FS81 Theorem 7.1(1): clock correlations dominate the rotator

The `ℤ_N` clock and plane-rotator free models use the same edge weight
`exp(β cos(θ_i - θ_j))`. Ginibre's clock/circle comparison proves the clock two-point function
dominates the rotator two-point function on every finite free domain. Taking the free limits gives
the infinite-volume comparison. The comparison is stated for the real cosine correlation, which is
the ordered real observable represented by the exponential notation in FS81 Theorem 7.1(1).
-/

@[expose] public section

open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre

namespace FroehlichSpencer.BKT.Clock

/-- The clock and rotator models have the same bond coupling `β`; the clock parameter changes
only the single-site measure. -/
theorem clock_rotator_bondWeight_eq (N : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β) :
    (clockModel N hN β hβ).w = (rotatorModel β hβ).w := by
  rfl

/-- On every finite free domain, the `N`-state clock cosine correlation dominates the
plane-rotator cosine correlation, for every integer frequency. This includes the source range
`1 ≤ ξ ≤ N - 1`. -/
theorem correlation_dominates_rotator_finite (N : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β)
    (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : {z // z ∈ Λ}) :
    freeTwoPoint β ξ Λ u.1 v.1 ≤
      (clockModel N hN β hβ).twoPoint ξ Λ u.1 v.1 := by
  exact freeTwoPoint_le_clock N hN hβ ξ Λ u.1 v.1

/-- The finite free-box instance of Theorem 7.1(1), with both marked sites in the box. -/
theorem correlation_dominates_rotator_freeBox (N L : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β)
    (ξ : ℤ) (u v : {z // z ∈ freeBox L}) :
    freeTwoPoint β ξ (freeBox L) u.1 v.1 ≤
      (clockModel N hN β hβ).twoPoint ξ (freeBox L) u.1 v.1 := by
  exact correlation_dominates_rotator_finite N hN hβ ξ (freeBox L) u v

/-- Theorem 7.1(1) for the free thermodynamic limits. The centered-square limits agree with the
source's free states, independently of the increasing finite exhaustion. -/
theorem correlation_dominates_rotator_limit (N : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β)
    (ξ : ℤ) (u v : ℤ × ℤ) :
    freeTwoPointLimit β hβ ξ u v ≤
      (clockModel N hN β hβ).twoPointLimit ξ u v := by
  exact freeTwoPointLimit_le_clock N hN hβ ξ u v

end FroehlichSpencer.BKT.Clock

end
