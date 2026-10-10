/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockIntermediatePhase
public import FroehlichSpencer.BKT.Bridge.ClockCorrelation
public import FroehlichSpencer.BKT.Bridge.ClockProfile
public import FroehlichSpencer.BKT.Clock.Source.Result4
import Mathlib.Tactic

/-!
It serves FS81 result 4
(provider in `BKT/Provider/`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ClockIntermediatePhase

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Clock
open FroehlichSpencer.BKT.Clock.Source (IsClockIntermediatePhaseExact)
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)
open FroehlichSpencer.BKT.Bridge.ClockCorrelation (clockCorrelation_eq)
open FroehlichSpencer.BKT.Bridge.ClockProfile

/--
The internal exact intermediate phase (all pairs, ℓ¹; harmonics `0 < ξ < n` as naturals) gives
the predicate `IsClockIntermediatePhase` at the same lower scale `b`.
-/
theorem isClockIntermediatePhase_of_exact {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β) {q b : ℝ}
    (hE : IsClockIntermediatePhaseExact n hn β hβ q b) :
    IsClockIntermediatePhase n hn β hβ q b := by
  refine ⟨⟨lt_trans (by positivity) hE.lower.1, fun ξ _ _ => ?_⟩, ?_⟩
  · set p := (ξ : ℝ) ^ 2 / (2 * Real.pi * b) with hpdef
    have hp : 0 ≤ p := by
      have := lt_trans (by positivity : (0 : ℝ) < 1 / (4 * Real.pi)) hE.lower.1
      positivity
    refine ⟨Real.exp (-p) * (2 : ℝ) ^ (-p), by positivity, fun x => ?_⟩
    have hl := hE.lower.2 ξ 0 x
    rw [← hpdef] at hl
    rw [clockCorrelation_eq]
    calc Real.exp (-p) * (2 : ℝ) ^ (-p) * (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)) ^ (-p)
        = Real.exp (-p) * ((2 : ℝ) ^ (-p) * (1 + euclid x) ^ (-p)) := by rw [mul_assoc]
      _ ≤ Real.exp (-p) * ((Compact.l1Dist 0 x : ℝ) + 1) ^ (-p) :=
          mul_le_mul_of_nonneg_left (euclidProfile_le_l1Profile hp x) (Real.exp_pos _).le
      _ ≤ _ := hl
  · obtain ⟨β'', hβ'', C, hC, hup⟩ := hE.upper
    refine ⟨β'', hβ'', C, hC, fun ξ h1 h2 hqξ x => ?_⟩
    obtain ⟨hξ0, hξn, hξ⟩ := harmonic_toNat (n := n) h1 h2
    have hu := hup ξ.toNat hξ0 hξn (by rw [dipoleGap_eq h1]; exact hqξ) 0 x
    have hp : (ξ.toNat : ℝ) ^ 2 / (2 * Real.pi * β'') = (ξ : ℝ) ^ 2 / (2 * Real.pi * β'') := by
      rw [show ((ξ.toNat : ℕ) : ℝ) = (ξ : ℝ) by exact_mod_cast hξ]
    rw [hp] at hu
    have hc : clockCorrelation n hn β hβ ξ 0 x =
        (clockModel n hn β hβ).twoPointLimit ((ξ.toNat : ℕ) : ℤ) 0 x := by
      rw [clockCorrelation_eq, hξ]
    rw [hc]
    refine hu.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    have : 0 ≤ (ξ : ℝ) ^ 2 / (2 * Real.pi * β'') := by positivity
    exact l1Profile_le_euclidProfile this le_rfl x

end FroehlichSpencer.BKT.Bridge.ClockIntermediatePhase

end
