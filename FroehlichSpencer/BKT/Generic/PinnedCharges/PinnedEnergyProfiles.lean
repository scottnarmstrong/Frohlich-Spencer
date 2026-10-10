/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.PinnedEnergy

/-! # Variational reduction for pinned profile families

This lemma isolates the analytic last step of a local-energy construction. If a test field pairs
with a pinned charge by at least `m` and has Dirichlet energy at most `C*m`, then the Green energy
of the charge is at least `m/C`. Constructing the required multiscale profile and proving its
energy bound remain geometric obligations.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- A profile with pairing at least `m` and energy at most `C*m` certifies a linear lower bound
on the pinned Green energy. This is the variational implication needed after the Appendix D test
profile has been constructed. -/
theorem pinned_greenEnergy_ge_of_profile (hL : 1 < L)
    (q : Fin L × Fin L → ℤ) (u : RotatorDualFace L → ℝ) (hu : u none = 0)
    (m C : ℝ) (hm : 0 ≤ m) (hC : 0 ≤ C)
    (hpair : m ≤ |∑ x, u (some x) * (q x : ℝ)|)
    (henergy : (squareZero L).energy u ≤ C * m) :
    m ≤ C * Multigraph.pairing (realNeutralizeAtWiredRoot q)
      (-(squareZero L).greenOp (squareZero_connected L hL)
        (realNeutralizeAtWiredRoot q)) := by
  let Q := Multigraph.pairing (realNeutralizeAtWiredRoot q)
    (-(squareZero L).greenOp (squareZero_connected L hL)
      (realNeutralizeAtWiredRoot q))
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact (squareZero L).pairing_greenOp_nonneg (squareZero_connected L hL)
      (realNeutralizeAtWiredRoot q) (sum_realNeutralizeAtWiredRoot q)
  have hvariational := pinned_charge_pairing_sq_le_greenEnergy_mul_testEnergy
    hL q u hu
  have hpairSq : m ^ 2 ≤ (∑ x, u (some x) * (q x : ℝ)) ^ 2 := by
    have hsq := (sq_le_sq₀ hm (abs_nonneg _)).2 (by
      simpa [abs_of_nonneg hm] using hpair)
    simpa [sq_abs] using hsq
  have hprofile : m ^ 2 ≤ Q * (C * m) := by
    dsimp [Q] at hvariational ⊢
    exact hpairSq.trans (hvariational.trans
      (mul_le_mul_of_nonneg_left henergy hQ))
  by_cases hm0 : m = 0
  · subst m
    simpa [Q] using mul_nonneg hC hQ
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    nlinarith [hprofile]

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
