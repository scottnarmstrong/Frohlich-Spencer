/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.FinitePathEstimate
public import FroehlichSpencer.BKT.Clock.Compact.Theorem71

/-! # Centered free-box estimate -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Lattice2D

/-- The uniform square estimate transfers to centered free boxes. -/
theorem clockModel_twoPoint_freeBox_le_exp_small (N R : ℕ) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hβsmall : β ≤ Real.log (8 / 7) / 2)
    (u v : ℤ × ℤ) (hu : boxRadius u ≤ R) (hv : boxRadius v ≤ R) :
    (clockModel N (by omega) β hβ).twoPoint 1 (freeBox R) u v ≤
      2 * Real.exp (-Real.log 2 * (l1Dist u v : ℝ)) := by
  have hsq := clockModel_twoPoint_squareBox_le_exp_small N (2 * R) hN hβ hβsmall
    (boxSite R u) (boxSite R v)
  rw [freeRadius_boxSite hu hv, siteToZ_boxSite hu, siteToZ_boxSite hv] at hsq
  rw [freeBox_eq_translateDomain R]
  let w : ℤ × ℤ := (-(R : ℤ), -(R : ℤ))
  have ht := (clockModel N (by omega) β hβ).twoPoint_translate 1 (squareBoxZ (2 * R))
    (u + ((R : ℤ), (R : ℤ))) (v + ((R : ℤ), (R : ℤ))) w
  have hu' : u + ((R : ℤ), (R : ℤ)) + w = u := by
    ext <;> simp [w]
  have hv' : v + ((R : ℤ), (R : ℤ)) + w = v := by
    ext <;> simp [w]
  rw [hu', hv'] at ht
  rw [ht]
  exact hsq

end FroehlichSpencer.BKT.Clock.HighTemp

end
