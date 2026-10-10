/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.RecurrenceArithmetic
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyRecurrence

/-! # Iteration and fiber composition for boundary entropy

This module isolates the finite recurrence calculus used after the one-step
geometric cover estimate. The iteration and summation theorem is generic in
the scale map; its two numerical inputs are the terminal-weight estimate and
the iterate-fiber estimate.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

/-- The `m`-fold iterate of a natural scale map, in the source's order. -/
def boundaryEntropyIterate (γ : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | m + 1, k => boundaryEntropyIterate γ m (γ k)

private theorem boundaryEntropyIterate_succ (γ : ℕ → ℕ) (m k : ℕ) :
    boundaryEntropyIterate γ (m + 1) k =
      boundaryEntropyIterate γ m (γ k) := rfl

/-- One expansion step moves the separated term to the first output scale. -/
private theorem boundaryEntropySeparatedSum_succ (γ : ℕ → ℕ)
    (d k : ℕ) (P : ℕ → ℝ) :
    (∑ m ∈ Finset.range (d + 1),
      (1 / 2 : ℝ) ^ m * P (boundaryEntropyIterate γ (m + 1) k)) =
      P (γ k) + (1 / 2 : ℝ) *
        ∑ m ∈ Finset.range d,
          (1 / 2 : ℝ) ^ m *
            P (boundaryEntropyIterate γ (m + 1) (γ k)) := by
  rw [Finset.sum_range_succ']
  calc
    _ = (∑ m ∈ Finset.range d,
          (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ m *
            P (boundaryEntropyIterate γ (m + 1) (γ k)))) + P (γ k) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro m hm
        rw [boundaryEntropyIterate_succ]
        rw [pow_succ]
        ring
      · simp [boundaryEntropyIterate]
    _ = P (γ k) + (1 / 2 : ℝ) *
          ∑ m ∈ Finset.range d,
            (1 / 2 : ℝ) ^ m *
              P (boundaryEntropyIterate γ (m + 1) (γ k)) := by
      rw [← Finset.mul_sum]
      ring

/-- Iterating the recurrence terminates at the designated initial scale and
adds one separated term at every preceding scale. -/
theorem boundaryEntropy_iterate_expansion
    (A P : ℕ → ℝ) (γ depth : ℕ → ℕ) (initial : ℕ)
    (hstep : ∀ k, initial ≤ k → A k ≤
      (1 / 2 : ℝ) * A (γ k) + P (γ k))
    (hdepth : ∀ k, 0 < depth k →
      initial ≤ k ∧ depth (γ k) + 1 = depth k) (k : ℕ) :
    A k ≤ (1 / 2 : ℝ) ^ depth k *
        A (boundaryEntropyIterate γ (depth k) k) +
      ∑ m ∈ Finset.range (depth k),
        (1 / 2 : ℝ) ^ m * P (boundaryEntropyIterate γ (m + 1) k) := by
  let aux : ∀ d k, depth k = d →
      A k ≤ (1 / 2 : ℝ) ^ d * A (boundaryEntropyIterate γ d k) +
        ∑ m ∈ Finset.range d,
          (1 / 2 : ℝ) ^ m * P (boundaryEntropyIterate γ (m + 1) k) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro k hd
      by_cases hd0 : d = 0
      · have hdEq : depth k = 0 := by omega
        subst d
        rw [hdEq]
        simp [boundaryEntropyIterate]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        have hvalid := hdepth k (by rw [hd]; exact hdpos)
        obtain ⟨hk, hdeq⟩ := hvalid
        have hγdepth : depth (γ k) = d - 1 := by omega
        have hγexp := ih (d - 1) (by omega) (γ k) hγdepth
        have hlocal := hstep k hk
        have hterminal :
            boundaryEntropyIterate γ (d - 1) (γ k) =
              boundaryEntropyIterate γ d k := by
          have hd' : d - 1 + 1 = d := by omega
          rw [← hd']
          rfl
        rw [hterminal] at hγexp
        have hcoeff : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (d - 1) =
            (1 / 2 : ℝ) ^ d := by
          have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
          calc
            (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (d - 1) =
                (1 / 2 : ℝ) ^ (d - 1) * (1 / 2 : ℝ) := by ring
            _ = (1 / 2 : ℝ) ^ (d - 1 + 1) := by rw [pow_succ]
            _ = (1 / 2 : ℝ) ^ d := by rw [Nat.sub_add_cancel hd1]
        have hsum := boundaryEntropySeparatedSum_succ γ (d - 1) k P
        have hd' : d - 1 + 1 = d := by omega
        have hsum' :
            (∑ m ∈ Finset.range d,
              (1 / 2 : ℝ) ^ m *
                P (boundaryEntropyIterate γ (m + 1) k)) =
              P (γ k) + (1 / 2 : ℝ) *
                ∑ m ∈ Finset.range (d - 1),
                  (1 / 2 : ℝ) ^ m *
                    P (boundaryEntropyIterate γ (m + 1) (γ k)) := by
          simpa [hd'] using hsum
        calc
          A k ≤ (1 / 2 : ℝ) * A (γ k) + P (γ k) := hlocal
          _ ≤ (1 / 2 : ℝ) *
                ((1 / 2 : ℝ) ^ (d - 1) *
                  A (boundaryEntropyIterate γ d k) +
                  ∑ m ∈ Finset.range (d - 1),
                    (1 / 2 : ℝ) ^ m *
                      P (boundaryEntropyIterate γ (m + 1) (γ k))) + P (γ k) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hγexp (by norm_num)) le_rfl
          _ = (1 / 2 : ℝ) ^ d * A (boundaryEntropyIterate γ d k) +
                ∑ m ∈ Finset.range d,
                  (1 / 2 : ℝ) ^ m *
                    P (boundaryEntropyIterate γ (m + 1) k) := by
                rw [hsum']
                calc
                  _ = ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (d - 1)) *
                        A (boundaryEntropyIterate γ d k) +
                      (P (γ k) + (1 / 2 : ℝ) *
                        ∑ m ∈ Finset.range (d - 1),
                          (1 / 2 : ℝ) ^ m *
                            P (boundaryEntropyIterate γ (m + 1) (γ k))) := by ring
                  _ = (1 / 2 : ℝ) ^ d *
                        A (boundaryEntropyIterate γ d k) +
                      (P (γ k) + (1 / 2 : ℝ) *
                        ∑ m ∈ Finset.range (d - 1),
                          (1 / 2 : ℝ) ^ m *
                            P (boundaryEntropyIterate γ (m + 1) (γ k))) := by
                        rw [hcoeff]
  exact aux (depth k) k rfl

/-- The finite weighted separated-term sum is controlled by the source fiber
bound, after composing the matching-group recurrence over all scales. -/
theorem boundaryEntropy_sum_bound_of_iteration_fibers
    (A P : ℕ → ℝ) (γ depth : ℕ → ℕ) (initial n : ℕ)
    (hstep : ∀ k, initial ≤ k → A k ≤
      (1 / 2 : ℝ) * A (γ k) + P (γ k))
    (hdepth : ∀ k, 0 < depth k →
      initial ≤ k ∧ depth (γ k) + 1 = depth k)
    (hstop : ∀ k, boundaryEntropyIterate γ (depth k) k < initial)
    (hterminal : ∀ k, k < initial → A k ≤ A 0)
    (hAnonneg : ∀ k, 0 ≤ A k)
    (hPnonneg : ∀ j, 0 ≤ P j)
    (Cterm : ℝ)
    (hweights : (∑ k ∈ Finset.range (n + 1),
        (1 / 2 : ℝ) ^ depth k) ≤ Cterm)
    (hfiber : ∀ m,
      (∑ k ∈ Finset.range (n + 1),
        P (boundaryEntropyIterate γ (m + 1) k)) ≤
        (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℕ, P j) :
    (∑ k ∈ Finset.range (n + 1), A k) ≤
      Cterm * A 0 + (196 / 3 : ℝ) * ∑' j : ℕ, P j := by
  classical
  let T := ∑ k ∈ Finset.range (n + 1), depth k
  have hterm (k : ℕ) :
      A k ≤ (1 / 2 : ℝ) ^ depth k * A 0 +
        ∑ m ∈ Finset.range (depth k),
          (1 / 2 : ℝ) ^ m *
            P (boundaryEntropyIterate γ (m + 1) k) := by
    have hexpand := boundaryEntropy_iterate_expansion A P γ depth initial
      hstep hdepth k
    have hlow : boundaryEntropyIterate γ (depth k) k < initial := hstop k
    have htermA := hterminal _ hlow
    calc
      _ ≤ (1 / 2 : ℝ) ^ depth k *
            A (boundaryEntropyIterate γ (depth k) k) +
          ∑ m ∈ Finset.range (depth k),
            (1 / 2 : ℝ) ^ m *
              P (boundaryEntropyIterate γ (m + 1) k) := hexpand
      _ ≤ (1 / 2 : ℝ) ^ depth k * A 0 +
          ∑ m ∈ Finset.range (depth k),
            (1 / 2 : ℝ) ^ m *
              P (boundaryEntropyIterate γ (m + 1) k) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left htermA (by positivity)) le_rfl
  have hTbound : ∀ k ∈ Finset.range (n + 1), depth k ≤ T := by
    intro k hk
    exact Finset.single_le_sum (s := Finset.range (n + 1))
      (f := depth) (fun _ _ => Nat.zero_le _) hk
  have hdouble :
      (∑ k ∈ Finset.range (n + 1),
        ∑ m ∈ Finset.range (depth k),
          (1 / 2 : ℝ) ^ m *
            P (boundaryEntropyIterate γ (m + 1) k)) ≤
      ∑ k ∈ Finset.range (n + 1),
        ∑ m ∈ Finset.range T,
          (1 / 2 : ℝ) ^ m *
            P (boundaryEntropyIterate γ (m + 1) k) := by
    apply Finset.sum_le_sum
    intro k hk
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (hTbound k hk))
    intro m hm _
    exact mul_nonneg (by positivity) (hPnonneg _)
  have hswap :
      (∑ k ∈ Finset.range (n + 1),
        ∑ m ∈ Finset.range T,
          (1 / 2 : ℝ) ^ m *
            P (boundaryEntropyIterate γ (m + 1) k)) =
      ∑ m ∈ Finset.range T,
        (1 / 2 : ℝ) ^ m *
          ∑ k ∈ Finset.range (n + 1),
            P (boundaryEntropyIterate γ (m + 1) k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
  have hgeom :
      (∑ m ∈ Finset.range T,
        (1 / 2 : ℝ) ^ m *
          ((14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℕ, P j)) ≤
        (196 / 3 : ℝ) * ∑' j : ℕ, P j := by
    have hconst :
        (14 / 3 : ℝ) * (7 / 4 : ℝ) * ∑' m : ℕ, (7 / 8 : ℝ) ^ m =
          196 / 3 := by
      simpa [recurrenceSeparatedCoefficient] using recurrenceSeparatedCoefficient_eq
    have hgeomSum : Summable (fun m : ℕ => (7 / 8 : ℝ) ^ m) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hgeomFinite :
        (∑ m ∈ Finset.range T, (7 / 8 : ℝ) ^ m) ≤
          ∑' m : ℕ, (7 / 8 : ℝ) ^ m :=
      Summable.sum_le_tsum _ (by intro m hm; positivity) hgeomSum
    have hPsum : 0 ≤ ∑' j : ℕ, P j := tsum_nonneg hPnonneg
    have hrewrite : ∀ m,
        (1 / 2 : ℝ) ^ m *
          ((14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℕ, P j) =
        ((14 / 3 : ℝ) * (7 / 4 : ℝ) * ∑' j : ℕ, P j) *
          (7 / 8 : ℝ) ^ m := by
      intro m
      rw [pow_succ]
      calc
        (1 / 2 : ℝ) ^ m *
            ((14 / 3 : ℝ) * ((7 / 4 : ℝ) ^ m * (7 / 4 : ℝ)) *
              ∑' j : ℕ, P j) =
            ((14 / 3 : ℝ) * (7 / 4 : ℝ) * ∑' j : ℕ, P j) *
              ((1 / 2 : ℝ) ^ m * (7 / 4 : ℝ) ^ m) := by ring
        _ = ((14 / 3 : ℝ) * (7 / 4 : ℝ) * ∑' j : ℕ, P j) *
              (7 / 8 : ℝ) ^ m := by
                rw [← mul_pow]
                norm_num
    calc
      _ = ((14 / 3 : ℝ) * (7 / 4 : ℝ) * ∑' j : ℕ, P j) *
          ∑ m ∈ Finset.range T, (7 / 8 : ℝ) ^ m := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            exact hrewrite m
      _ ≤ ((14 / 3 : ℝ) * (7 / 4 : ℝ) * ∑' j : ℕ, P j) *
          ∑' m : ℕ, (7 / 8 : ℝ) ^ m := by
            apply mul_le_mul_of_nonneg_left hgeomFinite
            positivity
      _ = (196 / 3 : ℝ) * ∑' j : ℕ, P j := by
            calc
              (14 / 3 : ℝ) * (7 / 4 : ℝ) * (∑' j : ℕ, P j) *
                  (∑' m : ℕ, (7 / 8 : ℝ) ^ m) =
                ((14 / 3 : ℝ) * (7 / 4 : ℝ) *
                  ∑' m : ℕ, (7 / 8 : ℝ) ^ m) * ∑' j : ℕ, P j := by ring
              _ = (196 / 3 : ℝ) * ∑' j : ℕ, P j := by rw [hconst]
  have hseparated :
      (∑ k ∈ Finset.range (n + 1),
        ∑ m ∈ Finset.range T,
          (1 / 2 : ℝ) ^ m *
            P (boundaryEntropyIterate γ (m + 1) k)) ≤
      (196 / 3 : ℝ) * ∑' j : ℕ, P j := by
    rw [hswap]
    calc
      _ ≤ ∑ m ∈ Finset.range T,
          (1 / 2 : ℝ) ^ m *
            ((14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℕ, P j) := by
              apply Finset.sum_le_sum
              intro m hm
              exact mul_le_mul_of_nonneg_left (hfiber m) (by positivity)
      _ ≤ (196 / 3 : ℝ) * ∑' j : ℕ, P j := hgeom
  have hweightsTerm :
      (∑ k ∈ Finset.range (n + 1),
        (1 / 2 : ℝ) ^ depth k * A 0) ≤ Cterm * A 0 := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hweights (hAnonneg 0)
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          ((1 / 2 : ℝ) ^ depth k * A 0 +
            ∑ m ∈ Finset.range (depth k),
              (1 / 2 : ℝ) ^ m *
                P (boundaryEntropyIterate γ (m + 1) k)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k
    _ ≤ (∑ k ∈ Finset.range (n + 1),
          (1 / 2 : ℝ) ^ depth k * A 0) +
        ∑ k ∈ Finset.range (n + 1),
          ∑ m ∈ Finset.range T,
            (1 / 2 : ℝ) ^ m *
              P (boundaryEntropyIterate γ (m + 1) k) := by
          rw [Finset.sum_add_distrib]
          exact add_le_add le_rfl hdouble
    _ ≤ Cterm * A 0 + (196 / 3 : ℝ) * ∑' j : ℕ, P j :=
          add_le_add hweightsTerm hseparated

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
