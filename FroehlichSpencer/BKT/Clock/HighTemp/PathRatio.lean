/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.FiniteExpansion
public import FroehlichSpencer.BKT.Clock.HighTemp.PathCover
public import FroehlichSpencer.BKT.Clock.HighTemp.PathGraph
import Mathlib.Tactic

/-! # Normalize connected-subset terms along paths -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open Classical
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Clock.Compact

/-- Connected selected-subset terms, normalized by the full bond product, are
bounded by the sum of the normalized activities of full-graph paths. -/
theorem clockBoxConnectedSubsetRatioBound (N L : ℕ) {β : ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ Real.log (8 / 7) / 2)
    (u v : RotatorSpinSite L) :
    (∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
      if (selectedBondGraph L A).Reachable u v then
        ∑ k : RotatorSpinSite L → Fin N,
          ∏ e ∈ A, clockBondDefectAt N L β k e
      else 0) ≤
    (∑ k : RotatorSpinSite L → Fin N,
      ∏ e : RotatorInternalBond L, (1 + clockBondDefectAt N L β k e)) *
      ∑ p : (fullBondGraph L).Path u v, (1 / 8 : ℝ) ^ p.1.length := by
  classical
  let g (k : RotatorSpinSite L → Fin N) (e : RotatorInternalBond L) :=
    clockBondDefectAt N L β k e
  have hratio (k : RotatorSpinSite L → Fin N) (e : RotatorInternalBond L) :
      g k e / (1 + g k e) ≤ 1 / 8 := by
    simpa [g, clockBondDefectAt] using
      (bondDefect_ratio_le_eight (β := β) (x :=
        clockAngles N k ((rotatorFreeGraph L).src e) -
          clockAngles N k ((rotatorFreeGraph L).tgt e)) hβ hβsmall)
  have hdenpos (k : RotatorSpinSite L → Fin N) (e : RotatorInternalBond L) :
      0 < 1 + g k e := by
    dsimp [g, clockBondDefectAt, bondDefect]
    rw [show 1 + (Real.exp _ - 1) = Real.exp _ by ring]
    exact Real.exp_pos _
  have hconnPath := clockBoxConnectedSubset_le_pathFactors N L hβ u v
  change (∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
      if (selectedBondGraph L A).Reachable u v then
        ∑ k : RotatorSpinSite L → Fin N,
          ∏ e ∈ A, g k e else 0) ≤ _
  calc
    _ ≤ ∑ p : (fullBondGraph L).Path u v,
          ∑ k : RotatorSpinSite L → Fin N,
            (∏ e ∈ pathBondSet p, g k e) *
              ∏ e ∈ (Finset.univ : Finset (RotatorInternalBond L)) \ pathBondSet p,
                (1 + g k e) := by
                  simpa [g] using hconnPath
    _ ≤ ∑ p : (fullBondGraph L).Path u v,
          ∑ k : RotatorSpinSite L → Fin N,
            (∏ e : RotatorInternalBond L, (1 + g k e)) *
              (1 / 8 : ℝ) ^ p.1.length := by
              apply Finset.sum_le_sum
              intro p hp
              apply Finset.sum_le_sum
              intro k hk
              have hfactor := prod_path_and_complement_eq_total_mul_ratio
                (g k) (pathBondSet p) (fun e => (hdenpos k e).ne')
              rw [hfactor]
              have hcard : (pathBondSet p).card = p.1.length := by
                apply selectedPathBondFinset_card p.1 p.2
                intro e he
                exact selectedWalk_edgeLabel_cover p.1 e he
              have hpow := prod_bondRatio_le_pow (g k) (pathBondSet p) (1 / 8 : ℝ)
                (fun e => bondDefect_nonneg hβ)
                (fun e => hdenpos k e)
                (fun e => hratio k e)
              rw [hcard] at hpow
              exact mul_le_mul_of_nonneg_left hpow
                (Finset.prod_nonneg fun e he => (hdenpos k e).le)
    _ = (∑ k : RotatorSpinSite L → Fin N,
          ∏ e : RotatorInternalBond L, (1 + g k e)) *
        ∑ p : (fullBondGraph L).Path u v, (1 / 8 : ℝ) ^ p.1.length := by
          calc
            (∑ p : (fullBondGraph L).Path u v,
              ∑ k : RotatorSpinSite L → Fin N,
                (∏ e : RotatorInternalBond L, (1 + g k e)) *
                  (1 / 8 : ℝ) ^ p.1.length) =
                ∑ p : (fullBondGraph L).Path u v,
                  (∑ k : RotatorSpinSite L → Fin N,
                    ∏ e : RotatorInternalBond L, (1 + g k e)) *
                    (1 / 8 : ℝ) ^ p.1.length := by
                      apply Finset.sum_congr rfl
                      intro p hp
                      rw [← Finset.sum_mul]
            _ = _ := by
              rw [Finset.mul_sum]

end FroehlichSpencer.BKT.Clock.HighTemp

end
