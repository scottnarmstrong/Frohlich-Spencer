/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.DisorderCarrier
public import FroehlichSpencer.BKT.Clock.VillainClock.ProfileShift
import Mathlib.Tactic

/-!
# Villain-clock disorder as a shifted-profile partition ratio

The finite seam observable is exactly a profile-shifted Villain-clock partition ratio.

Its direct
seam profile has energy proportional to the separation.

The real vortex decomposition does not by
itself reduce this energy on the finite clock carrier.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The finite free-square shift profile representing the oriented Villain-clock disorder seam.
Its sign is chosen to match the graph orientation in `rotatorFreeGraph`. -/
def freeSquareDisorderProfile {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (ξ : ℝ)
    (e : RotatorInternalBond (2 * L)) : ℝ :=
  if e ∈ freeSquareDisorderEdgeSet hL hr then -2 * Real.pi * ξ else 0

/-- Inserting the disorder seam is the same pointwise operation as applying the corresponding
real edge profile to the Villain-clock configuration weight. -/
theorem freeSquareTwistedPartition_eq_profilePartition {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hL : 0 < L) (hr : r ≤ L) :
    twistedPartitionFunction (rotatorFreeGraph (2 * L)) (freeSquareDisorderEdgeSet hL hr)
        β (-ξ) N =
      villainProfilePartitionFunction (N := N) (rotatorFreeGraph (2 * L)) β
        (freeSquareDisorderProfile hL hr ξ) := by
  classical
  unfold twistedPartitionFunction villainProfilePartitionFunction
  apply Finset.sum_congr rfl
  intro s hs
  unfold twistedConfigurationWeight villainProfileConfigurationWeight
    freeSquareDisorderProfile
  apply Finset.prod_congr rfl
  intro e he
  by_cases heS : e ∈ freeSquareDisorderEdgeSet hL hr
  · simp only [heS]
    congr 1
    simp only [Multigraph.grad]
    ring_nf
  · simp only [heS]
    rfl

/-- The finite Villain-clock disorder expectation is a shifted-profile partition ratio. -/
theorem freeSquareDisorderExpectation_eq_profilePartition_ratio {r L : ℕ} (N : ℕ)
    (β ξ : ℝ) (hβ : 0 < β) (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    freeSquareDisorderExpectation N β ξ hβ hN hL hr =
      villainProfilePartitionFunction (N := N) (rotatorFreeGraph (2 * L)) β
        (freeSquareDisorderProfile hL hr ξ) / freeSquarePartitionFunction N L β := by
  rw [freeSquareDisorderExpectation_eq_twistedPartition_ratio N β ξ hβ hN hL hr,
    freeSquareTwistedPartition_eq_profilePartition N β ξ hL hr]

/-- The straight seam profile has linear energy in its length. -/
theorem freeSquareDisorderProfile_energy {r L : ℕ} (ξ : ℝ) (hL : 0 < L) (hr : r ≤ L) :
    (∑ e : RotatorInternalBond (2 * L),
      freeSquareDisorderProfile hL hr ξ e ^ 2) =
      (r : ℝ) * (2 * Real.pi * ξ) ^ 2 := by
  classical
  unfold freeSquareDisorderProfile
  calc
    (∑ e : RotatorInternalBond (2 * L),
        (if e ∈ freeSquareDisorderEdgeSet hL hr then -2 * Real.pi * ξ else 0) ^ 2) =
        ∑ e ∈ freeSquareDisorderEdgeSet hL hr, (-2 * Real.pi * ξ) ^ 2 := by
      have hsum : ∑ e : RotatorInternalBond (2 * L),
          (if e ∈ freeSquareDisorderEdgeSet hL hr then -2 * Real.pi * ξ else 0) ^ 2 =
        ∑ e, if e ∈ freeSquareDisorderEdgeSet hL hr then (-2 * Real.pi * ξ) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : e ∈ freeSquareDisorderEdgeSet hL hr <;> simp [h]
      rw [hsum, Finset.sum_ite_mem_eq]
    _ = ∑ i : Fin r, (-2 * Real.pi * ξ) ^ 2 := by
      rw [freeSquareDisorderEdgeSet, Finset.sum_image
        (disorderSeamEdge_injective hL hr).injOn]
    _ = (r : ℝ) * (2 * Real.pi * ξ) ^ 2 := by
      simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]

/-- Applying the Villain profile inequality to the exact seam profile recovers the exponential
lower bound in the seam length. This does not yield the logarithmic-energy input of (7.5). -/
theorem freeSquareDisorderExpectation_ge_linearProfile {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    Real.exp (-β / 2 * ((r : ℝ) * (2 * Real.pi * ξ) ^ 2)) ≤
      freeSquareDisorderExpectation N β ξ hβ hN hL hr := by
  rw [freeSquareDisorderExpectation_eq_profilePartition_ratio N β ξ hβ hN hL hr]
  have hbase : 0 < freeSquarePartitionFunction N L β :=
    freeSquarePartitionFunction_pos N L β hβ hN
  apply (le_div_iff₀ hbase).2
  have hprofile := villainProfilePartitionFunction_lower hN hβ
    (rotatorFreeGraph (2 * L)) (freeSquareDisorderProfile hL hr ξ)
  rw [freeSquareDisorderProfile_energy ξ hL hr] at hprofile
  simpa [freeSquarePartitionFunction, villainProfilePartitionFunction, partitionFunction] using hprofile

end FroehlichSpencer.BKT.Clock.VillainClock

end
