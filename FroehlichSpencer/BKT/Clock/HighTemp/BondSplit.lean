/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.TwoPoint
public import FroehlichSpencer.BKT.Clock.HighTemp.BondWeight
import Mathlib.Tactic

/-!
# Finite-volume bond splitting for the clock model

This module expresses the clock Boltzmann weight as a product of nonnegative
bond defects and records the finite subset expansion used in the high-
temperature argument.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Compact

/-- The clock box weight with every bond split into its constant and defect parts. -/
theorem clockBoxWeight_eq_bondSplit (N L : ℕ) (β : ℝ) (k : RotatorSpinSite L → Fin N) :
    clockBoxWeight N L β k =
      Real.exp (-β * Fintype.card (RotatorInternalBond L)) *
        ∏ e : RotatorInternalBond L,
          (1 + bondDefect β (clockAngles N k ((rotatorFreeGraph L).src e) -
            clockAngles N k ((rotatorFreeGraph L).tgt e))) := by
  classical
  unfold clockBoxWeight
  rw [Real.exp_sum]
  rw [show (∏ e : RotatorInternalBond L,
      Real.exp (β * Real.cos (clockAngles N k ((rotatorFreeGraph L).src e) -
        clockAngles N k ((rotatorFreeGraph L).tgt e)))) =
      ∏ e : RotatorInternalBond L,
        (Real.exp (-β) * (1 + bondDefect β
          (clockAngles N k ((rotatorFreeGraph L).src e) -
            clockAngles N k ((rotatorFreeGraph L).tgt e)))) by
        refine Finset.prod_congr rfl fun e _ => ?_
        exact expCos_eq_const_mul_one_add_bondDefect β _]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Expanding the product of split bonds gives a sum over edge subsets. -/
theorem prod_one_add_bondDefect_eq_sum (N L : ℕ) (β : ℝ)
    (k : RotatorSpinSite L → Fin N) :
    (∏ e : RotatorInternalBond L,
      (1 + bondDefect β (clockAngles N k ((rotatorFreeGraph L).src e) -
        clockAngles N k ((rotatorFreeGraph L).tgt e)))) =
      ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
        ∏ e ∈ A, bondDefect β (clockAngles N k ((rotatorFreeGraph L).src e) -
          clockAngles N k ((rotatorFreeGraph L).tgt e)) := by
  classical
  exact Finset.prod_one_add _

end FroehlichSpencer.BKT.Clock.HighTemp

end
