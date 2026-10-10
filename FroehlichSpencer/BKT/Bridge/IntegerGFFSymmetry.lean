/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.IntegerField
import Mathlib.Tactic.Ring

/-! # Sign symmetry of the pinned integer Gaussian field

The sign change of a pinned height preserves the KP energy and reverses every
linear observable. This is the discrete symmetry used in the moment argument
for KP Theorem 1.1 (p. 3).
-/

@[expose] public section

namespace FroehlichSpencer.BKT

open Multigraph

universe u v

variable {V : Type u} {E : Type v}

/-- Negation on fields pinned at the origin. -/
def pinnedIntegerFieldNegEquiv (root : V) :
    pinnedIntegerField V root ≃ pinnedIntegerField V root where
  toFun m := ⟨-m.1, by simp [m.2]⟩
  invFun m := ⟨-m.1, by simp [m.2]⟩
  left_inv m := by
    apply Subtype.ext
    funext j
    simp
  right_inv m := by
    apply Subtype.ext
    funext j
    simp

/-- Negating an integer field leaves its edge energy unchanged. -/
theorem energy_intField_neg (G : Multigraph V E) [Fintype E]
    (m : V → ℤ) :
    G.energy (fun j => ((-m j : ℤ) : ℝ)) =
      G.energy (fun j => (m j : ℝ)) := by
  unfold Multigraph.energy Multigraph.grad
  apply Finset.sum_congr rfl
  intro e he
  simp only [Int.cast_neg]
  ring

/-- Negating a pinned field preserves its KP integer Gaussian weight. -/
theorem igffWeight_neg (G : Multigraph V E) [Fintype E] [DecidableEq V]
    (β : ℝ) {root : V} (m : pinnedIntegerField V root) :
    igffWeight G β (pinnedIntegerFieldNegEquiv root m) = igffWeight G β m := by
  have hfield : (pinnedIntegerFieldNegEquiv root m).1 = fun j => -m.1 j := rfl
  change Real.exp (-(β / 2) * G.energy
    (fun j => ((pinnedIntegerFieldNegEquiv root m).1 j : ℝ))) =
      Real.exp (-(β / 2) * G.energy (fun j => (m.1 j : ℝ)))
  rw [hfield, energy_intField_neg]

/-- The linear pairing of a negated integer field is the negative pairing. -/
theorem pairing_intField_neg [Fintype V] (m : V → ℤ) (f : V → ℝ) :
    pairing (fun j => ((-m j : ℤ) : ℝ)) f =
      -pairing (fun j => (m j : ℝ)) f := by
  unfold pairing
  simp only [Int.cast_neg, neg_mul]
  exact Finset.sum_neg_distrib (s := Finset.univ)
    (f := fun j : V => (m j : ℝ) * f j)

/-- The normalized lattice expectation of every linear observable is zero,
by the sign symmetry of the pinned IGFF weight. -/
theorem igffExpectation_pairing_eq_zero (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (f : V → ℝ) :
    igffExpectation G hG β hβ root
      (fun m => pairing (fun j => (m.1 j : ℝ)) f) = 0 := by
  let e := pinnedIntegerFieldNegEquiv root
  let g : pinnedIntegerField V root → ℝ := fun m =>
    pairing (fun j => (m.1 j : ℝ)) f * igffWeight G β m
  have hneg (m : pinnedIntegerField V root) :
      g m = -(g (e m)) := by
    have hfield : (e m).1 = fun j => -m.1 j := rfl
    have hp : pairing (fun j => ((e m).1 j : ℝ)) f =
        -pairing (fun j => (m.1 j : ℝ)) f := by
      rw [hfield]
      exact pairing_intField_neg m.1 f
    dsimp [g]
    rw [igffWeight_neg, hp]
    ring
  have hsum : (∑' m, g m) = -(∑' m, g m) := by
    calc
      (∑' m, g m) = ∑' m, -(g (e m)) := by
        apply tsum_congr
        intro m
        exact hneg m
      _ = ∑' m, -g m := Equiv.tsum_eq e (fun m => -g m)
      _ = -(∑' m, g m) := by rw [← tsum_neg]
  have hzero : (∑' m, g m) = 0 := by linarith
  change (∑' m, g m) / igffPartitionFunction G β root = 0
  rw [hzero, zero_div]

end FroehlichSpencer.BKT

end
