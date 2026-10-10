/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.FiniteModel
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Poisson

def positiveMode (q : ℕ) : ℕ := q + 1

noncomputable def inactiveWeight (z : ℕ → ℝ) (q : ℕ) : ℝ :=
  2 / z (positiveMode q)


theorem hasSum_fin_inactiveWeight_one (z : ℕ → ℝ)
    (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q) (n : ℕ) :
    HasSum (fun q : Fin n → ℕ => ∏ i, inactiveWeight z (q i)) 1 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    let e : (Fin (n + 1) → ℕ) ≃ ℕ × (Fin n → ℕ) :=
      ((finSuccEquiv n).piCongrLeft (fun _ => ℕ)).trans Equiv.piOptionEquivProd
    have hprod_nonneg (p : ℕ × (Fin n → ℕ)) :
        0 ≤ inactiveWeight z p.1 * ∏ i, inactiveWeight z (p.2 i) := by
      apply mul_nonneg (hweight_nonneg p.1)
      exact Finset.prod_nonneg fun i hi => hweight_nonneg (p.2 i)
    have hprod_sum : Summable (fun p : ℕ × (Fin n → ℕ) =>
        inactiveWeight z p.1 * ∏ i, inactiveWeight z (p.2 i)) := by
      rw [summable_prod_of_nonneg hprod_nonneg]
      constructor
      · intro a
        exact ih.summable.mul_left (inactiveWeight z a)
      · convert hnorm.summable using 1
        funext a
        calc
          _ = inactiveWeight z a * ∑' q : Fin n → ℕ, ∏ i, inactiveWeight z (q i) :=
            ih.summable.tsum_mul_left _
          _ = inactiveWeight z a := by rw [ih.tsum_eq]; simp
    apply e.symm.hasSum_iff.mp
    convert hnorm.mul ih hprod_sum using 1
    · funext p
      change (∏ i : Fin (n + 1), inactiveWeight z ((e.symm p) i)) =
        inactiveWeight z p.1 * ∏ i : Fin n, inactiveWeight z (p.2 i)
      rw [Fin.prod_univ_succ]
      have hzero : (e.symm p) 0 = p.1 := by
        simp [e, Equiv.trans_apply, finSuccEquiv,
          Equiv.piCongrLeft, Equiv.piOptionEquivProd]
      have hsucc (i : Fin n) : (e.symm p) i.succ = p.2 i := by
        simp [e, Equiv.trans_apply, finSuccEquiv,
          Equiv.piCongrLeft, Equiv.piOptionEquivProd, finSuccEquiv']
      rw [hzero]
      congr 1
    · norm_num


end FroehlichSpencer.FS82.Poisson
