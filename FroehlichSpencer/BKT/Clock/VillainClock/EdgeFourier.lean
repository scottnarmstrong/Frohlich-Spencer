/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.ResidueFourier
import Mathlib.Tactic

/-!
# Residue Fourier expansion on a clock edge

The finite residue expansion is compatible with differences of clock angles, including the wrap
around at the end of the clock.

The coefficient for a residue remains the full Gaussian alias
sum.

This records the exact local input for a finite-graph current expansion.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The clock residue of the oriented difference of two clock labels. -/
def clockSubIndex {N : ℕ} (a b : Fin N) : Fin N :=
  ⟨if b.val ≤ a.val then a.val - b.val else a.val + N - b.val, by
    by_cases h : b.val ≤ a.val
    · simp [h]
      omega
    · simp [h]
      omega⟩

/-- The difference of two clock angles equals the representative angle, modulo one turn. -/
theorem clockAngle_sub_clockAngle {N : ℕ} (hN : 0 < N) (a b : Fin N) :
    clockAngle N a - clockAngle N b =
      if b.val ≤ a.val then clockAngle N (clockSubIndex a b)
      else clockAngle N (clockSubIndex a b) - 2 * Real.pi := by
  by_cases h : b.val ≤ a.val
  · have hval : (clockSubIndex a b).val = a.val - b.val := by simp [clockSubIndex, h]
    have hcast : ((clockSubIndex a b).val : ℝ) = (a.val : ℝ) - b.val := by
      rw [hval, Nat.cast_sub h]
    unfold clockAngle
    simp only [h, ite_true, hcast]
    field_simp [ne_of_gt hN]
  · have hval : (clockSubIndex a b).val = a.val + N - b.val := by simp [clockSubIndex, h]
    have hle : b.val ≤ a.val + N := by omega
    have hcast : ((clockSubIndex a b).val : ℝ) = (a.val : ℝ) + N - b.val := by
      rw [hval, Nat.cast_sub hle]
      push_cast
      ring
    unfold clockAngle
    simp only [h, ite_false]
    rw [hcast]
    field_simp [ne_of_gt hN]
    ring_nf

private theorem villainWeight_sub_two_pi (β x : ℝ) :
    villainWeight β (x - 2 * Real.pi) = villainWeight β x := by
  have h := VillainWeight.villainWeight_add_two_pi β (x - 2 * Real.pi)
  simpa [sub_add_cancel] using h.symm

private theorem exp_character_two_pi_int (m : ℤ) :
    Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
  Complex.exp_int_mul_two_pi_mul_I m

/-- The Villain edge between two clock labels is exactly the residue character sum with Gaussian
alias coefficients. -/
theorem villainClock_edge_eq_residueFourier (β : ℝ) {N : ℕ} (hN : 0 < N)
    (hβ : 0 < β) (a b : Fin N) :
    (villainWeight β (clockAngle N a - clockAngle N b) : ℂ) =
      ∑ q : Fin N, gaussianAliasCoefficient β N q *
        Complex.exp (Complex.I * (q : ℂ) *
          ((clockAngle N a - clockAngle N b : ℝ) : ℂ)) := by
  let k := clockSubIndex a b
  have hweight : villainWeight β (clockAngle N a - clockAngle N b) =
      villainWeight β (clockAngle N k) := by
    rw [clockAngle_sub_clockAngle hN a b]
    split_ifs with hab
    · rfl
    · change villainWeight β (clockAngle N k - 2 * Real.pi) =
        villainWeight β (clockAngle N k)
      exact villainWeight_sub_two_pi β _
  rw [hweight, sampledVillain_eq_gaussianAliasFourier β hN hβ k]
  apply Finset.sum_congr rfl
  intro q _
  have hangle := clockAngle_sub_clockAngle hN a b
  have hphase : Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
      Complex.exp (Complex.I * (q : ℂ) *
        ((clockAngle N a - clockAngle N b : ℝ) : ℂ)) := by
    rw [hangle]
    split_ifs with hab
    · simp [k]
    · change Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
          Complex.exp (Complex.I * (q : ℂ) *
            (((clockAngle N k : ℝ) - 2 * Real.pi : ℝ) : ℂ))
      have harg : Complex.I * (q : ℂ) *
          (((clockAngle N k : ℝ) - 2 * Real.pi : ℝ) : ℂ) =
          Complex.I * (q : ℂ) * (clockAngle N k : ℂ) +
            ((-(q : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring_nf
      rw [harg, Complex.exp_add, exp_character_two_pi_int, mul_one]
  exact congrArg (fun z : ℂ => gaussianAliasCoefficient β N q * z) hphase

end FroehlichSpencer.BKT.Clock.VillainClock

end
