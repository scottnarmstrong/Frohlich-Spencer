/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.PathTools
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Geometric tail for square-lattice paths

At bond activity at most `1/8`, the total weight of simple paths from a
vertex has an exponential tail in graph distance.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open Finset

/-- At activity at most `1/8`, paths in a graph of degree at most four have
a geometric tail in graph distance. -/
theorem simpleGraph_path_weight_sum_le_geometric
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [SimpleGraph.LocallyFinite G]
    (hdeg : ∀ x, G.degree x ≤ 4) (u v : V) (r : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 8) :
    (∑ p : G.Path u v, r ^ p.1.length) ≤ 2 * (1 / 2 : ℝ) ^ G.dist u v := by
  classical
  let N := Fintype.card V
  let fiber (n : Fin N) := {p : G.Path u v // p.1.length = n.val}
  let e : G.Path u v ≃ Σ n : Fin N, fiber n :=
    { toFun := fun p => ⟨⟨p.1.length, p.2.length_lt⟩, ⟨p, rfl⟩⟩
      invFun := fun a => a.2.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨n, ⟨p, hp⟩⟩
        have hn : (⟨p.1.length, p.2.length_lt⟩ : Fin N) = n := Fin.ext hp
        cases hn
        rfl }
  have hfiber_card (n : Fin N) : Fintype.card (fiber n) ≤ 4 ^ n.val := by
    let toWalk : fiber n → {w : G.Walk u v | w.length = n.val} :=
      fun p => ⟨p.1.1, p.2⟩
    have hinj : Function.Injective toWalk := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      simpa only [toWalk] using
        congrArg (fun x : {w : G.Walk u v | w.length = n.val} => x.1) hab
    calc
      Fintype.card (fiber n) ≤
          Fintype.card {w : G.Walk u v // w.length = n.val} :=
        Fintype.card_le_of_injective toWalk hinj
      _ = (G.finsetWalkLength n.val u v).card := by
        change Fintype.card {w : G.Walk u v | w.length = n.val} = _
        exact G.card_set_walk_length_eq u v n.val
      _ ≤ 4 ^ n.val := card_finsetWalkLength_le_four_pow G hdeg n.val u v
  have hfiber_sum (n : Fin N) :
      (∑ p : fiber n, r ^ p.1.1.length) =
        (Fintype.card (fiber n) : ℝ) * r ^ n.val := by
    calc
      (∑ p : fiber n, r ^ p.1.1.length) = ∑ _p : fiber n, r ^ n.val := by
        apply Fintype.sum_congr
        intro p
        rw [p.2]
      _ = (Fintype.card (fiber n) : ℝ) * r ^ n.val := by simp [mul_comm]
  have hfiber_bound (n : Fin N) :
      (∑ p : fiber n, r ^ p.1.1.length) ≤
        if G.dist u v ≤ n.val then (1 / 2 : ℝ) ^ n.val else 0 := by
    by_cases hdist : G.dist u v ≤ n.val
    · have hif :
          (if G.dist u v ≤ n.val then (1 / 2 : ℝ) ^ n.val else 0) =
            (1 / 2 : ℝ) ^ n.val := by
          exact dite_eq_left hdist
      rw [hif]
      rw [hfiber_sum n]
      have hcard : (Fintype.card (fiber n) : ℝ) ≤ (4 : ℝ) ^ n.val := by
        exact_mod_cast hfiber_card n
      calc
        (Fintype.card (fiber n) : ℝ) * r ^ n.val ≤
            (4 : ℝ) ^ n.val * r ^ n.val :=
          mul_le_mul_of_nonneg_right hcard (pow_nonneg hr0 _)
        _ = (4 * r) ^ n.val := by rw [mul_pow]
        _ ≤ (1 / 2 : ℝ) ^ n.val := by
          apply pow_le_pow_left₀
          · nlinarith [hr0]
          · nlinarith [hr]
    · have hif :
          (if G.dist u v ≤ n.val then (1 / 2 : ℝ) ^ n.val else 0) = 0 := by
          exact dite_eq_right hdist
      rw [hif]
      have hempty : IsEmpty (fiber n) := ⟨fun p => hdist (by
        simpa [p.2] using (G.dist_le (p.1.1 : G.Walk u v)))⟩
      have hsum : (∑ p : fiber n, r ^ p.1.1.length) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        exact (hempty.false p).elim
      exact le_of_eq hsum
  have hgeosummable (d : ℕ) :
      Summable (fun i : ℕ => if d ≤ i then (2 : ℝ)⁻¹ ^ i else 0) := by
    refine (summable_geometric_two.indicator {i | d ≤ i}).congr ?_
    intro i
    by_cases hi : d ≤ i <;> simp [Set.mem_ofPred_eq, hi, one_div]
  calc
    (∑ p : G.Path u v, r ^ p.1.length) =
        ∑ n : Fin N, ∑ p : fiber n, r ^ p.1.1.length := by
      calc
        (∑ p : G.Path u v, r ^ p.1.length) =
            ∑ a : Σ n : Fin N, fiber n, r ^ a.2.1.1.length := by
          exact Equiv.sum_comp e (fun a => r ^ a.2.1.1.length)
        _ = ∑ n : Fin N, ∑ p : fiber n, r ^ p.1.1.length := by
          exact Fintype.sum_sigma' (fun (n : Fin N) (p : fiber n) => r ^ p.1.1.length)
    _ ≤ ∑ n : Fin N, if G.dist u v ≤ n.val then (1 / 2 : ℝ) ^ n.val else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      exact hfiber_bound n
    _ = ∑ k ∈ Finset.range N,
          if G.dist u v ≤ k then (1 / 2 : ℝ) ^ k else 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun n =>
        if G.dist u v ≤ n then (1 / 2 : ℝ) ^ n else 0)]
    _ ≤ ∑' k : ℕ, if G.dist u v ≤ k then (2 : ℝ)⁻¹ ^ k else 0 := by
      simpa [one_div] using
        (hgeosummable (G.dist u v)).sum_le_tsum (Finset.range N)
          (fun k hk => by split_ifs <;> positivity)
    _ = 2 * (1 / 2 : ℝ) ^ G.dist u v := by
      rw [tsum_geometric_inv_two_ge]
      norm_num [one_div]

end FroehlichSpencer.BKT.Clock.HighTemp

end
