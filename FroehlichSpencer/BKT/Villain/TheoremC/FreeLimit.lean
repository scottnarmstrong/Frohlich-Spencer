/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.Models

/-! # Passing a uniform Villain box estimate to the free limit

The Villain free two-point function is the monotone thermodynamic limit in `Ginibre.FreeModel`.
This module records the limit step needed after a finite free-box estimate has been established.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

/-- A lower bound holding eventually along the centered free boxes passes to the Villain free
thermodynamic limit. -/
theorem villainModel_twoPointLimit_ge_of_eventually
    {β : ℝ} (hβ : 0 < β) (ξ : ℤ) (u v : ℤ × ℤ) {a : ℝ}
    (hbound : ∀ᶠ L in atTop, a ≤
      (villainModel β hβ).twoPoint ξ (freeBox L) u v) :
    a ≤ (villainModel β hβ).twoPointLimit ξ u v :=
  ge_of_tendsto ((villainModel β hβ).tendsto_twoPointLimit ξ u v) hbound

/-- The uniform form used in Theorem C: any finite cutoff after which the free-box correlation
has the stated lower bound yields the same bound in the thermodynamic limit. -/
theorem villainModel_twoPointLimit_ge_of_boxBound
    {β : ℝ} (hβ : 0 < β) (ξ : ℤ) (u v : ℤ × ℤ) {a : ℝ} {L₀ : ℕ}
    (hbound : ∀ L : ℕ, L₀ ≤ L → a ≤
      (villainModel β hβ).twoPoint ξ (freeBox L) u v) :
    a ≤ (villainModel β hβ).twoPointLimit ξ u v := by
  apply villainModel_twoPointLimit_ge_of_eventually hβ ξ u v
  filter_upwards [eventually_ge_atTop L₀] with L hL
  exact hbound L hL

end FroehlichSpencer.BKT.Villain.TheoremC

end
