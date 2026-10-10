/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.CorrectedSource
public import FroehlichSpencer.BKT.Rotator.Periodic.SectorComb

/-!
# Corrected source on the periodic square carrier

Transporting the torus Hodge correction through the dual-carrier isomorphism preserves its
edge-square energy and pins the translated height at the square root.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator.Periodic

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {L : ℕ} [NeZero L]

/-- Signed dual-carrier transport preserves the sum of edge squares. -/
theorem sum_sq_torusDualFieldToSquare (hL : 2 < L) (f : TorusEdge L → ℝ) :
    (∑ e : SquarePeriodicEdge L, torusDualFieldToSquare hL f e ^ 2) =
      ∑ e : TorusEdge L, f e ^ 2 := by
  classical
  let I := torusDualSquareIso hL
  calc
    _ = ∑ e : TorusEdge L, torusDualFieldToSquare hL f (I.edges e) ^ 2 :=
      (Equiv.sum_comp I.edges (fun e : SquarePeriodicEdge L =>
        torusDualFieldToSquare hL f e ^ 2)).symm
    _ = ∑ e : TorusEdge L, f e ^ 2 := by
      apply Finset.sum_congr rfl
      intro e he
      unfold torusDualFieldToSquare
      simp only [I, Equiv.symm_apply_apply]
      split_ifs <;> ring

/-- The fixed torus source path with its Hodge height correction, viewed on the square-periodic
carrier. The height is pinned at the carrier root and the energy has the same uniform bound. -/
theorem exists_periodicCorrectedSource_squareEnergy (hL : 2 < L)
    (a x : TorusVertex L) (ξ : ℤ) :
    ∃ (σ : TorusVertex L → ℝ) (θ : SquarePeriodicEdge L → ℝ),
      ((torusDualSquareIso hL).pushField σ)
          ((torusDualSquareIso hL).vertices (0, 0)) = 0 ∧
      θ = torusDualFieldToSquare hL (fun e =>
        ((torusSourcePathCurrent a x ξ e : ℤ) : ℝ) +
          (torusDualGraph hL).grad σ e) ∧
      (∑ e : SquarePeriodicEdge L, θ e ^ 2) ≤
        350 * (ξ : ℝ) ^ 2 *
          (1 + Real.log (((torusRadius a x + 1 : ℕ) : ℝ))) := by
  obtain ⟨σ, hroot, henergy⟩ := exists_periodicCorrectedSource_energy hL a x ξ
  let I := torusDualSquareIso hL
  let θ : SquarePeriodicEdge L → ℝ := torusDualFieldToSquare hL (fun e =>
    ((torusSourcePathCurrent a x ξ e : ℤ) : ℝ) + (torusDualGraph hL).grad σ e)
  have hrootSq : (I.pushField σ) (I.vertices (0, 0)) = 0 := by
    change σ (I.vertices.symm (I.vertices (0, 0))) = 0
    simpa using hroot
  have hθ : θ = torusDualFieldToSquare hL (fun e =>
      ((torusSourcePathCurrent a x ξ e : ℤ) : ℝ) +
        (torusDualGraph hL).grad σ e) := rfl
  refine ⟨σ, θ, hrootSq, hθ, ?_⟩
  rw [hθ, sum_sq_torusDualFieldToSquare]
  exact henergy

/-- The transported correction gradient is the square-periodic gradient of the pushed height. -/
theorem torusDualFieldToSquare_correctionGradient (hL : 2 < L)
    (σ : TorusVertex L → ℝ) :
    torusDualFieldToSquare hL (fun e => (torusDualGraph hL).grad σ e) =
      fun e => (squarePeriodic L).grad ((torusDualSquareIso hL).pushField σ) e := by
  funext e
  let I := torusDualSquareIso hL
  obtain ⟨e₀, rfl⟩ := I.edges.surjective e
  exact torusDualFieldToSquare_grad hL σ e₀

end FroehlichSpencer.BKT.Rotator.Periodic

end
