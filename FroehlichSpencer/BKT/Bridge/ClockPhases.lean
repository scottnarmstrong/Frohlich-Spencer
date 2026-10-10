/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockExpDecay
public import FroehlichSpencer.BKT.Surface.ClockLongRangeOrder
public import FroehlichSpencer.BKT.Bridge.ClockCorrelation
public import FroehlichSpencer.BKT.Bridge.ClockProfile
public import FroehlichSpencer.BKT.Clock.Window.MasslessWindow
import Mathlib.Tactic

/-!
The internal phase predicates (`Clock.Window.ClockHasExpDecay`, `ClockHasLongRangeOrder`) are stated
for every pair of sites and the ℓ¹ distance; the predicates `IsClockExpDecay` and
`IsClockLongRangeOrder`  are stated at the sites `0, x` with the Euclidean
`|x|`, on source's  `clockCorrelation`.

The conversions (`isClockExpDecay_of_internal`,
`isClockLongRangeOrder_of_internal`) use source's installed
`Bridge.ClockCorrelation.clockCorrelation_eq`, the translation invariance `twoPointLimit_translate`
(`l1Dist_eq_zero_sub`), and source's installed profile comparisons `|x| ≤ |x|₁ ≤ 2 |x|`
(`Bridge.ClockProfile`).

They serve the three clock roots (providers in `BKT/Provider/`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ClockPhases

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Clock
open FroehlichSpencer.BKT.Clock.Window
open FroehlichSpencer.BKT.Bridge.ClockCorrelation (clockCorrelation_eq)
open FroehlichSpencer.BKT.Bridge.ClockProfile (euclid euclid_le_l1Dist l1Dist_le_two_euclid)

/-- The internal ℓ¹ distance is translation invariant. -/
theorem l1Dist_eq_zero_sub (u v : ℤ × ℤ) : Compact.l1Dist u v = Compact.l1Dist 0 (v - u) := by
  simp only [Compact.l1Dist, Prod.fst_zero, Prod.snd_zero, Prod.fst_sub, Prod.snd_sub, zero_sub,
    Int.natAbs_neg]
  rw [← Int.natAbs_neg (u.1 - v.1), ← Int.natAbs_neg (u.2 - v.2)]
  congr 2 <;> ring

/-- Internal exponential decay (all pairs, ℓ¹) gives the surface predicate. -/
theorem isClockExpDecay_of_internal {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β) {ξ : ℤ}
    (h : ClockHasExpDecay n hn β hβ ξ) : IsClockExpDecay n hn β hβ ξ := by
  obtain ⟨C, m, hm, hC⟩ := h
  refine ⟨max C 0, m, hm, fun x => ?_⟩
  rw [clockCorrelation_eq]
  refine (hC 0 x).trans ?_
  calc C * Real.exp (-m * (Compact.l1Dist 0 x : ℝ))
      ≤ max C 0 * Real.exp (-m * (Compact.l1Dist 0 x : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (-m * euclid x) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_max_right _ _)
        exact mul_le_mul_of_nonpos_left (euclid_le_l1Dist x) (by linarith)

/-- Internal long-range order (some pair at ℓ¹ distance `≥ R`) gives the surface predicate (the
site `0` and Euclidean `|x| ≥ R`), by translation invariance. -/
theorem isClockLongRangeOrder_of_internal {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β) {ξ : ℤ}
    (h : ClockHasLongRangeOrder n hn β hβ ξ) : IsClockLongRangeOrder n hn β hβ ξ := by
  obtain ⟨ε, hε, hR⟩ := h
  refine ⟨ε, hε, fun R => ?_⟩
  obtain ⟨u, v, huv, hcorr⟩ := hR ⌈2 * R⌉₊
  refine ⟨v - u, ?_, ?_⟩
  · have h1 : (⌈2 * R⌉₊ : ℝ) ≤ (Compact.l1Dist 0 (v - u) : ℝ) := by
      rw [← l1Dist_eq_zero_sub]; exact_mod_cast huv
    have h2 := l1Dist_le_two_euclid (v - u)
    have h3 := Nat.le_ceil (2 * R)
    change R ≤ euclid (v - u)
    linarith
  · rw [clockCorrelation_eq]
    have ht := (clockModel n hn β hβ).twoPointLimit_translate ξ 0 (v - u) u
    rw [zero_add, sub_add_cancel] at ht
    rw [← ht]
    exact hcorr

end FroehlichSpencer.BKT.Bridge.ClockPhases

end
