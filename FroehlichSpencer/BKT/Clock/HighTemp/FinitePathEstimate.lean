/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.FiniteExpansion
public import FroehlichSpencer.BKT.Clock.HighTemp.PathRatio
public import FroehlichSpencer.BKT.Clock.HighTemp.PathTail
public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
import Mathlib.Tactic
import Mathlib.Data.Int.NatAbs

/-!
# Finite-box high-temperature estimate

The connected-subset expansion is covered by simple paths. Each path contributes
its bond activity ratios, and the degree-four path count gives a uniform tail.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open Classical
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.SpinWaves
open FroehlichSpencer.BKT.Clock.Compact (l1Dist)

/-- The finite clock two-point function on the free square has a uniform
exponential upper bound for small coupling. -/
theorem clockModel_twoPoint_squareBox_le_exp_small (N L : ℕ) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hβsmall : β ≤ Real.log (8 / 7) / 2)
    (a b : RotatorSpinSite L) :
    (clockModel N (by omega) β hβ).twoPoint 1 (squareBoxZ L) (siteToZ a) (siteToZ b) ≤
      2 * Real.exp (-Real.log 2 * (freeRadius a b : ℝ)) := by
  classical
  let c := Real.exp (-β * (Fintype.card (RotatorInternalBond L) : ℝ))
  let Zsplit := ∑ k : RotatorSpinSite L → Fin N,
    ∏ e : RotatorInternalBond L, (1 + clockBondDefectAt N L β k e)
  have hdenpos (k : RotatorSpinSite L → Fin N) (e : RotatorInternalBond L) :
      0 < 1 + clockBondDefectAt N L β k e := by
    dsimp [clockBondDefectAt, bondDefect]
    rw [show 1 + (Real.exp _ - 1) = Real.exp _ by ring]
    exact Real.exp_pos _
  have hfullpos (k : RotatorSpinSite L → Fin N) :
      0 < ∏ e : RotatorInternalBond L, (1 + clockBondDefectAt N L β k e) :=
    Finset.prod_pos fun e he => hdenpos k e
  have hconfig : Nonempty (RotatorSpinSite L → Fin N) :=
    ⟨fun _ => ⟨0, by omega⟩⟩
  have hZsplit : 0 < Zsplit :=
    Finset.sum_pos (fun k hk => hfullpos k) (Finset.univ_nonempty_iff.mpr hconfig)
  have hZ : (∑ k : RotatorSpinSite L → Fin N, clockBoxWeight N L β k) = c * Zsplit := by
    simpa [c, Zsplit] using clockBoxPartition_eq_fullProductSum N L β
  have hnumConnected := clockBoxNumerator_le_exp_connected N L hN hβ a b
  let connectedPropTerm (A : Finset (RotatorInternalBond L)) :=
    @ite ℝ ((selectedBondGraph L A).Reachable a b) (Classical.propDecidable _)
      (∑ k : RotatorSpinSite L → Fin N,
        ∏ e ∈ A, clockBondDefectAt N L β k e) 0
  let connectedGraphTerm (A : Finset (RotatorInternalBond L)) :=
    @ite ℝ ((selectedBondGraph L A).Reachable a b)
      ((selectedBondGraph L A).instDecidableRelReachable a b)
      (∑ k : RotatorSpinSite L → Fin N,
        ∏ e ∈ A, clockBondDefectAt N L β k e) 0
  have hconnectedTerms :
      (∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
        connectedPropTerm A) =
      ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
        connectedGraphTerm A := by
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hconn : (selectedBondGraph L A).Reachable a b <;>
      simp [connectedPropTerm, connectedGraphTerm, hconn]
  have hpathRatioGraph := clockBoxConnectedSubsetRatioBound N L hβ hβsmall a b
  have hpathRatio :
      (∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
        connectedPropTerm A) ≤
      Zsplit * ∑ p : (fullBondGraph L).Path a b, (1 / 8 : ℝ) ^ p.1.length := by
    calc
      _ = ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
            connectedGraphTerm A := hconnectedTerms
      _ ≤ _ := by simpa [connectedGraphTerm, Zsplit] using hpathRatioGraph
  have hpath := simpleGraph_path_weight_sum_le_geometric
    (G := fullBondGraph L)
    (fun x => by
      simpa [fullBondGraph] using fullSelectedBondGraph_degree_le_four L x)
    a b (1 / 8 : ℝ) (by norm_num) (by norm_num)
  rw [fullBondGraph_dist_eq_freeRadius] at hpath
  have hnum :
      (∑ k : RotatorSpinSite L → Fin N,
        Real.cos (clockAngles N k a - clockAngles N k b) * clockBoxWeight N L β k) ≤
        (∑ k : RotatorSpinSite L → Fin N, clockBoxWeight N L β k) *
          (2 * Real.exp (-Real.log 2 * (freeRadius a b : ℝ))) := by
    calc
      _ ≤ c * (Zsplit * ∑ p : (fullBondGraph L).Path a b, (1 / 8 : ℝ) ^ p.1.length) :=
        le_trans hnumConnected (mul_le_mul_of_nonneg_left hpathRatio (Real.exp_pos _).le)
      _ ≤ c * (Zsplit * (2 * (1 / 2 : ℝ) ^ freeRadius a b)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpath hZsplit.le)
          (Real.exp_pos _).le
      _ = (∑ k : RotatorSpinSite L → Fin N, clockBoxWeight N L β k) *
          (2 * Real.exp (-Real.log 2 * (freeRadius a b : ℝ))) := by
        rw [hZ]
        have hpow : (1 / 2 : ℝ) ^ freeRadius a b =
            Real.exp (-Real.log 2 * (freeRadius a b : ℝ)) := by
          have hbase : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
            norm_num
          rw [← hbase, ← Real.exp_nat_mul, mul_comm]
        rw [hpow]
        ring
  have hZactual : 0 < ∑ k : RotatorSpinSite L → Fin N, clockBoxWeight N L β k := by
    rw [hZ]
    exact mul_pos (Real.exp_pos _) hZsplit
  rw [clockModel_twoPoint_squareBox N L (by omega) hβ 1 a b]
  have hnum' :
      (∑ k : RotatorSpinSite L → Fin N,
        Real.cos (clockAngles N k a - clockAngles N k b) * clockBoxWeight N L β k) ≤
        2 * Real.exp (-Real.log 2 * (freeRadius a b : ℝ)) *
          (∑ k : RotatorSpinSite L → Fin N, clockBoxWeight N L β k) := by
    simpa only [mul_comm] using hnum
  apply (div_le_iff₀ hZactual).2
  convert hnum' using 1
  norm_num

end FroehlichSpencer.BKT.Clock.HighTemp

end
