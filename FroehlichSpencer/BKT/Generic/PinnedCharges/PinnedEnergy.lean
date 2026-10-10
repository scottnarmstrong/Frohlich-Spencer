/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.WiredAdapter
public import FroehlichSpencer.BKT.Potential.Variational

/-! # Dirichlet's variational inequality on the augmented pinned carrier

The wired-root compensation turns every bounded-box charge into a zero-sum source on `squareZero`.
The finite-graph Dirichlet principle then gives the Green-energy lower bound against any pinned
test field. This is the analytic inequality used by the Appendix D local-energy construction; the
multiscale construction and its profile-overlap count are separate obligations.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- The real source obtained by adding the opposite total charge at the wired exterior. -/
def realNeutralizeAtWiredRoot (q : Fin L × Fin L → ℤ) : RotatorDualFace L → ℝ :=
  fun x => (neutralizeAtWiredRoot q x : ℝ)

theorem sum_realNeutralizeAtWiredRoot (q : Fin L × Fin L → ℤ) :
    ∑ x : RotatorDualFace L, realNeutralizeAtWiredRoot q x = 0 := by
  classical
  simp [realNeutralizeAtWiredRoot, ← Int.cast_sum]

/--
Green's variational inequality for an arbitrary pinned test field, with the precise charge
pairing on bounded faces on the left.

The right-hand Green form is the Dirichlet electrostatic
energy on the augmented carrier.
-/
theorem pinned_charge_pairing_sq_le_greenEnergy_mul_testEnergy (hL : 1 < L)
    (q : Fin L × Fin L → ℤ) (u : RotatorDualFace L → ℝ) (hu : u none = 0) :
    (∑ x, u (some x) * (q x : ℝ)) ^ 2 ≤
      Multigraph.pairing (realNeutralizeAtWiredRoot q)
          (-(squareZero L).greenOp (squareZero_connected L hL)
            (realNeutralizeAtWiredRoot q)) *
        (squareZero L).energy u := by
  classical
  let f : RotatorDualFace L → ℝ := realNeutralizeAtWiredRoot q
  have hf : ∑ x : RotatorDualFace L, f x = 0 := by
    exact sum_realNeutralizeAtWiredRoot q
  have hDP := Multigraph.dirichlet_principle (squareZero L)
    (squareZero_connected L hL) f hf u
  have hpair : Multigraph.pairing u f = ∑ x, u (some x) * (q x : ℝ) := by
    rw [Multigraph.pairing]
    rw [Fintype.sum_option]
    simp only [f, realNeutralizeAtWiredRoot, neutralizeAtWiredRoot,
      Int.cast_neg]
    simp [hu]
  simpa [f, hpair] using hDP

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
