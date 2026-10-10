/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Coordinate contraction identities

Interval path telescoping and coordinate sign cancellation used by the finite cubical boundary.

Source: FS82 journal (2.9)–(2.13), Fröhlich–Spencer (1982).
-/

public section

namespace FroehlichSpencer.FS82.Cubical.Contraction

noncomputable section
open Classical

@[expose] def intervalBoundary (t : ℕ) : ℕ → ℤ := fun x =>
  (if x = t + 1 then 1 else 0) - (if x = t then 1 else 0)

/-- The one-dimensional path chain from `a` to `b`, written as its edge coefficients. -/
@[expose] def intervalPath (a b : ℕ) (t : ℕ) : ℤ :=
  if a ≤ b then (if t ∈ Finset.Ico a b then 1 else 0)
  else -(if t ∈ Finset.Ico b a then 1 else 0)

private theorem forwardPath_boundary (a b x : ℕ) (hab : a ≤ b) :
    (∑ t ∈ Finset.Ico a b, intervalBoundary t x) =
      (if x = b then 1 else 0) - (if x = a then 1 else 0) := by
  induction b generalizing a x with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ n ih =>
      by_cases hn : a ≤ n
      · rw [Finset.sum_Ico_succ_top hn]
        rw [ih a x hn]
        simp only [intervalBoundary]
        split_ifs <;> omega
      · have ha : a = n + 1 := by omega
        subst a
        simp [intervalBoundary]

/-- The oriented interval path has boundary its endpoint difference. -/
theorem intervalPath_boundary (a b x : ℕ) :
    (∑ t ∈ Finset.Ico (min a b) (max a b), intervalPath a b t * intervalBoundary t x) =
      (if x = b then 1 else 0) - (if x = a then 1 else 0) := by
  by_cases hab : a ≤ b
  · rw [Nat.min_eq_left hab, Nat.max_eq_right hab]
    calc
      _ = ∑ t ∈ Finset.Ico a b, intervalBoundary t x := by
        apply Finset.sum_congr rfl
        intro t ht
        simp [intervalPath, hab, ht]
      _ = _ := forwardPath_boundary a b x hab
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    rw [Nat.min_eq_right hba, Nat.max_eq_left hba]
    calc
      _ = - ∑ t ∈ Finset.Ico b a, intervalBoundary t x := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        simp [intervalPath, hab, ht]
      _ = _ := by
        rw [forwardPath_boundary b a x hba]
        split_ifs <;> omega

@[expose] def axisRank {d : ℕ} (I : Finset (Fin d)) (i : Fin d) : ℕ :=
  (I.filter fun j => j < i).card

/-- Removing an earlier oriented axis lowers the rank of a later axis by one. -/
theorem axisRank_erase {d : ℕ} {I : Finset (Fin d)} {i j : Fin d}
    (hij : i < j) (hi : i ∈ I) :
    axisRank (I.erase i) j + 1 = axisRank I j := by
  have hmem : i ∈ I.filter (fun a => a < j) := Finset.mem_filter.mpr ⟨hi, hij⟩
  have hpos : 0 < (I.filter fun a => a < j).card := Finset.card_pos.mpr ⟨i, hmem⟩
  simp [axisRank, Finset.filter_erase, hmem]
  omega

/-- The two iterated-face orientations of a coordinate square have opposite sign. -/
theorem cubical_sign_swap {d : ℕ} (I : Finset (Fin d)) (i j : Fin d)
    (hij : i < j) (hi : i ∈ I) (hj : j ∈ I) :
    (-1 : ℤ) ^ axisRank I i * (-1 : ℤ) ^ axisRank (I.erase i) j =
      - ((-1 : ℤ) ^ axisRank I j * (-1 : ℤ) ^ axisRank (I.erase j) i) := by
  have hji : ¬ j < i := not_lt_of_ge hij.le
  have hirank : axisRank (I.erase j) i = axisRank I i := by
    simp [axisRank, Finset.filter_erase, hji, hj]
  have hjrank : axisRank (I.erase i) j + 1 = axisRank I j := axisRank_erase hij hi
  rw [hirank]
  have hs := congrArg (fun n : ℕ => (-1 : ℤ) ^ n) hjrank
  rw [pow_succ] at hs
  rw [← hs]
  ring

end
end FroehlichSpencer.FS82.Cubical.Contraction

end
