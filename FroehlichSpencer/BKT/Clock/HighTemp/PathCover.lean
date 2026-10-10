/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.HighTemp.FiniteExpansion
public import FroehlichSpencer.BKT.Clock.HighTemp.ConnectedSubset
public import FroehlichSpencer.BKT.Clock.HighTemp.PathGraph
import Mathlib.Tactic

/-! # Cover connected bond sets by paths -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open Classical
open FroehlichSpencer.BKT.Rotator

/-- Reorder the connected unmarked subset sum and apply the path-cover bound
configuration by configuration. -/
theorem clockBoxConnectedSubset_le_pathFactors (N L : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (u v : RotatorSpinSite L) :
    (∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
      if (selectedBondGraph L A).Reachable u v then
        ∑ k : RotatorSpinSite L → Fin N,
          ∏ e ∈ A, clockBondDefectAt N L β k e
      else 0) ≤
    ∑ p : (fullBondGraph L).Path u v,
      ∑ k : RotatorSpinSite L → Fin N,
        (∏ e ∈ pathBondSet p, clockBondDefectAt N L β k e) *
          ∏ e ∈ (Finset.univ : Finset (RotatorInternalBond L)) \ pathBondSet p,
            (1 + clockBondDefectAt N L β k e) := by
  classical
  calc
    (∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
      if (selectedBondGraph L A).Reachable u v then
        ∑ k : RotatorSpinSite L → Fin N,
          ∏ e ∈ A, clockBondDefectAt N L β k e
      else 0) =
        ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
          ∑ k : RotatorSpinSite L → Fin N,
            if (selectedBondGraph L A).Reachable u v then
              ∏ e ∈ A, clockBondDefectAt N L β k e else 0 := by
                apply Finset.sum_congr rfl
                intro A hA
                by_cases hconn : (selectedBondGraph L A).Reachable u v <;> simp [hconn]
    _ = ∑ k : RotatorSpinSite L → Fin N,
          ∑ A ∈ (Finset.univ : Finset (RotatorInternalBond L)).powerset,
            if (selectedBondGraph L A).Reachable u v then
              ∏ e ∈ A, clockBondDefectAt N L β k e else 0 := by rw [Finset.sum_comm]
    _ ≤ ∑ k : RotatorSpinSite L → Fin N,
          ∑ p : (fullBondGraph L).Path u v,
            (∏ e ∈ pathBondSet p, clockBondDefectAt N L β k e) *
              ∏ e ∈ (Finset.univ : Finset (RotatorInternalBond L)) \ pathBondSet p,
                (1 + clockBondDefectAt N L β k e) := by
          apply Finset.sum_le_sum
          intro k hk
          apply connectedSubsetSum_le_indexedPathFactorization
            (g := clockBondDefectAt N L β k)
            (connected := fun A => (selectedBondGraph L A).Reachable u v)
            (paths := Finset.univ)
            (pathEdges := fun p : (fullBondGraph L).Path u v => pathBondSet p)
          · intro e
            exact bondDefect_nonneg hβ
          · intro A hA hconn
            obtain ⟨q, hq, hsub, hcard⟩ := reachable_path_full_with_bondFinset hconn
            exact ⟨⟨q, hq⟩, Finset.mem_univ _, hsub⟩
    _ = ∑ p : (fullBondGraph L).Path u v,
          ∑ k : RotatorSpinSite L → Fin N,
            (∏ e ∈ pathBondSet p, clockBondDefectAt N L β k e) *
              ∏ e ∈ (Finset.univ : Finset (RotatorInternalBond L)) \ pathBondSet p,
                (1 + clockBondDefectAt N L β k e) := by rw [Finset.sum_comm]

end FroehlichSpencer.BKT.Clock.HighTemp

end
