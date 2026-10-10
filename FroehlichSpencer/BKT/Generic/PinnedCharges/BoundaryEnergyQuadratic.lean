/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Quadratic energy expansion for finite profile sums -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

universe u v

/-- Edge-gradient inner product of two profiles. -/
def boundaryEnergyCrossTerm {V : Type u} {E : Type v} [Fintype E]
    (G : Multigraph V E) (f g : V → ℝ) : ℝ :=
  ∑ e, G.grad f e * G.grad g e

/-- The absolute ordered-pair cross-term sum for a finite profile family. -/
def boundaryEnergyOrderedCrossSum {V : Type u} {E : Type v} [Fintype E]
    {ι : Type*} [DecidableEq ι] (G : Multigraph V E)
    (I : Finset ι) (f : ι → V → ℝ) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I, |boundaryEnergyCrossTerm G (f i) (f j)|

/-- The energy of a finite profile sum is bounded by the sum of absolute ordered
cross terms. The diagonal terms are the individual profile energies; the
off-diagonal terms contain both orientations of every cross term. -/
theorem energy_finset_sum_le_orderedCrossSum
    {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    {ι : Type*} [DecidableEq ι] (G : Multigraph V E)
    (I : Finset ι) (f : ι → V → ℝ) :
    G.energy (fun x => ∑ i ∈ I, f i x) ≤
      boundaryEnergyOrderedCrossSum G I f := by
  classical
  have hgrad (e : E) :
      G.grad (fun x => ∑ i ∈ I, f i x) e = ∑ i ∈ I, G.grad (f i) e := by
    simp only [Multigraph.grad]
    rw [Finset.sum_sub_distrib]
  unfold Multigraph.energy boundaryEnergyOrderedCrossSum boundaryEnergyCrossTerm
  calc
    (∑ e, G.grad (fun x => ∑ i ∈ I, f i x) e ^ 2) =
        ∑ e, ∑ i ∈ I, ∑ j ∈ I,
          G.grad (f i) e * G.grad (f j) e := by
            apply Finset.sum_congr rfl
            intro e he
            rw [hgrad e, sq]
            exact Finset.sum_mul_sum I I (fun i => G.grad (f i) e)
              (fun i => G.grad (f i) e)
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ e,
          G.grad (f i) e * G.grad (f j) e := by
            classical
            calc
              (∑ e, ∑ i ∈ I, ∑ j ∈ I,
                  G.grad (f i) e * G.grad (f j) e) =
                  ∑ i ∈ I, ∑ e, ∑ j ∈ I,
                    G.grad (f i) e * G.grad (f j) e := by
                      convert (Finset.sum_comm
                        (s := (Finset.univ : Finset E)) (t := I)
                        (f := fun e i => ∑ j ∈ I,
                          G.grad (f i) e * G.grad (f j) e)) using 1
              _ = ∑ i ∈ I, ∑ j ∈ I, ∑ e,
                    G.grad (f i) e * G.grad (f j) e := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      convert (Finset.sum_comm
                        (s := (Finset.univ : Finset E)) (t := I)
                        (f := fun e j =>
                          G.grad (f i) e * G.grad (f j) e)) using 1
    _ ≤ ∑ i ∈ I, ∑ j ∈ I,
          |(∑ e, G.grad (f i) e * G.grad (f j) e)| := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            exact le_abs_self _

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
