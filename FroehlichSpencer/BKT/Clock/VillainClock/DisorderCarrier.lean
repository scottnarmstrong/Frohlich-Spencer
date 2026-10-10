/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.FiniteLaw
public import FroehlichSpencer.BKT.Rotator.FreeBox
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Finite free-box Villain-clock disorder carrier

It does not assert existence of a
thermodynamic disorder limit or the estimate (7.5).

The free-box edge law is the finite restriction of FS81 (1.26), with the clock support from (7.2).

The seam uses the orientation and `+2πξ` shift in (1.32); Remark 4's citation of (1.31) is the
recorded misreference.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.Rotator

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- Lower endpoint of the oriented seam bond at centered coordinate `(L+i+1,L)`. -/
def disorderSeamLower {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    RotatorSpinSite (2 * L) :=
  (⟨L + i.val + 1, by have hi := i.isLt; omega⟩, ⟨L, by omega⟩)

/-- Upper endpoint of the oriented seam bond at centered coordinate `(L+i+1,L+1)`. -/
def disorderSeamUpper {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    RotatorSpinSite (2 * L) :=
  (⟨L + i.val + 1, by have hi := i.isLt; omega⟩, ⟨L + 1, by omega⟩)

/-- The positively oriented vertical free-box edge crossing the `i`-th disorder seam bond. -/
def disorderSeamEdge {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    RotatorInternalBond (2 * L) :=
  Sum.inr (⟨⟨L + i.val + 1, by have hi := i.isLt; omega⟩,
    ⟨⟨L, by omega⟩, by
      change L + 1 < 2 * L + 1
      omega⟩⟩)

/-- The set of free-box edges crossed by the length-`r` disorder seam. -/
def freeSquareDisorderEdgeSet {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) :
    Finset (RotatorInternalBond (2 * L)) :=
  Finset.univ.image (disorderSeamEdge hL hr)

theorem disorderSeamEdge_injective {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) :
    Function.Injective (disorderSeamEdge hL hr) := by
  intro i j hij
  have hcoord := congrArg (fun e : RotatorInternalBond (2 * L) =>
    match e with
    | Sum.inl _ => 0
    | Sum.inr e => e.1.val) hij
  have hcoord' : L + i.val + 1 = L + j.val + 1 := by
    simpa [disorderSeamEdge] using hcoord
  apply Fin.ext
  omega

@[simp] theorem rotatorFreeGraph_src_disorderSeamEdge {r L : ℕ} (hL : 0 < L)
    (hr : r ≤ L) (i : Fin r) :
    (rotatorFreeGraph (2 * L)).src (disorderSeamEdge hL hr i) = disorderSeamLower hL hr i := rfl

@[simp] theorem rotatorFreeGraph_tgt_disorderSeamEdge {r L : ℕ} (hL : 0 < L)
    (hr : r ≤ L) (i : Fin r) :
    (rotatorFreeGraph (2 * L)).tgt (disorderSeamEdge hL hr i) = disorderSeamUpper hL hr i := rfl

/-- The Villain-clock Boltzmann weight on the centered square of radius `L`. -/
def freeSquareConfigurationWeight (N L : ℕ) (β : ℝ)
    (s : RotatorSpinSite (2 * L) → Fin N) : ℝ :=
  configurationWeight (rotatorFreeGraph (2 * L)) β N s

/-- The partition function of the finite free Villain-clock law on the centered square. -/
def freeSquarePartitionFunction (N L : ℕ) (β : ℝ) : ℝ :=
  partitionFunction (rotatorFreeGraph (2 * L)) β N

/-- One factor of the (1.32) Villain-clock seam insertion. -/
def freeSquareDisorderFactor {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (s : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) (i : Fin r) : ℝ :=
  let d := clockAngle N (s (disorderSeamUpper hL hr i)) -
    clockAngle N (s (disorderSeamLower hL hr i))
  villainWeight β (d + 2 * Real.pi * ξ) / villainWeight β d

/-- The positive Villain-clock disorder observable on the `r` oriented seam bonds. -/
def freeSquareDisorderObservable {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (s : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) : ℝ :=
  ∏ i : Fin r, freeSquareDisorderFactor N β ξ s hL hr i

/-- The finite free-box Villain-clock disorder expectation. -/
def freeSquareDisorderExpectation {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (_hβ : 0 < β) (_hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) : ℝ :=
  (∑ s : RotatorSpinSite (2 * L) → Fin N,
    freeSquareDisorderObservable N β ξ s hL hr * freeSquareConfigurationWeight N L β s) /
    freeSquarePartitionFunction N L β

/-- The seam observable is the generic finite-graph Villain insertion on its exact crossing-edge
set. -/
theorem freeSquareDisorderObservable_eq_disorderObservable {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (s : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) :
    freeSquareDisorderObservable N β ξ s hL hr =
      disorderObservable (rotatorFreeGraph (2 * L)) (freeSquareDisorderEdgeSet hL hr)
        β (-ξ) N s := by
  classical
  unfold freeSquareDisorderObservable freeSquareDisorderFactor disorderObservable
  rw [Finset.prod_ite_mem_eq]
  rw [freeSquareDisorderEdgeSet, Finset.prod_image
    (disorderSeamEdge_injective hL hr).injOn]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [rotatorFreeGraph_src_disorderSeamEdge, rotatorFreeGraph_tgt_disorderSeamEdge]
  let d := clockAngle N (s (disorderSeamLower hL hr i)) -
    clockAngle N (s (disorderSeamUpper hL hr i))
  have hnum :
      clockAngle N (s (disorderSeamUpper hL hr i)) -
          clockAngle N (s (disorderSeamLower hL hr i)) + 2 * Real.pi * ξ =
        -(d + 2 * Real.pi * -ξ) := by
    dsimp [d]
    ring
  have hden :
      clockAngle N (s (disorderSeamUpper hL hr i)) -
          clockAngle N (s (disorderSeamLower hL hr i)) = -d := by
    dsimp [d]
    ring
  rw [hnum, hden, VillainWeight.villainWeight_neg, VillainWeight.villainWeight_neg]
  rfl

/-- The free-square seam expectation is the generic disorder expectation on its crossing-edge
set, with the sign adjusted to the free graph's positive vertical orientation. -/
theorem freeSquareDisorderExpectation_eq_disorderExpectation {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    freeSquareDisorderExpectation N β ξ hβ hN hL hr =
      disorderExpectation (rotatorFreeGraph (2 * L)) (freeSquareDisorderEdgeSet hL hr)
        β (-ξ) N := by
  unfold freeSquareDisorderExpectation freeSquarePartitionFunction disorderExpectation
  simp only [freeSquareConfigurationWeight]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [freeSquareDisorderObservable_eq_disorderObservable]

/-- Exact finite-volume partition-ratio form of the free-square Villain-clock disorder
expectation. -/
theorem freeSquareDisorderExpectation_eq_twistedPartition_ratio {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    freeSquareDisorderExpectation N β ξ hβ hN hL hr =
      twistedPartitionFunction (rotatorFreeGraph (2 * L)) (freeSquareDisorderEdgeSet hL hr)
        β (-ξ) N / freeSquarePartitionFunction N L β := by
  rw [freeSquareDisorderExpectation_eq_disorderExpectation N β ξ hβ hN hL hr]
  exact disorderExpectation_eq_twistedPartition_ratio (rotatorFreeGraph (2 * L))
    (freeSquareDisorderEdgeSet hL hr) hβ (-ξ) N

/-- The free-square Villain-clock partition function is positive. -/
theorem freeSquarePartitionFunction_pos (N L : ℕ) (β : ℝ) (hβ : 0 < β) (hN : 0 < N) :
    0 < freeSquarePartitionFunction N L β := by
  exact partitionFunction_pos (rotatorFreeGraph (2 * L)) hβ hN

/-- Every individual Villain-clock seam ratio is positive. -/
theorem freeSquareDisorderFactor_pos {r L : ℕ} (N : ℕ) (β ξ : ℝ) (hβ : 0 < β)
    (s : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    0 < freeSquareDisorderFactor N β ξ s hL hr i := by
  unfold freeSquareDisorderFactor
  exact div_pos (VillainWeight.villainWeight_pos hβ _) (VillainWeight.villainWeight_pos hβ _)

/-- The Villain-clock seam observable is positive on every finite configuration. -/
theorem freeSquareDisorderObservable_pos {r L : ℕ} (N : ℕ) (β ξ : ℝ) (hβ : 0 < β)
    (s : RotatorSpinSite (2 * L) → Fin N) (hL : 0 < L) (hr : r ≤ L) :
    0 < freeSquareDisorderObservable N β ξ s hL hr := by
  unfold freeSquareDisorderObservable
  exact Finset.prod_pos fun i _ => freeSquareDisorderFactor_pos N β ξ hβ s hL hr i

/-- The normalized finite free-box disorder expectation is positive. -/
theorem freeSquareDisorderExpectation_pos {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    0 < freeSquareDisorderExpectation N β ξ hβ hN hL hr := by
  unfold freeSquareDisorderExpectation
  apply div_pos
  · apply Finset.sum_pos
    · intro s hs
      exact mul_pos (freeSquareDisorderObservable_pos N β ξ hβ s hL hr)
        (configurationWeight_pos (rotatorFreeGraph (2 * L)) hβ N s)
    · exact ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  · exact freeSquarePartitionFunction_pos N L β hβ hN

/-- The fixed seam of length `r` in the centered free-square exhaustion. -/
def freeSquareDisorderExpectationExhaustion (N r : ℕ) (β ξ : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) (t : ℕ) : ℝ :=
  freeSquareDisorderExpectation (r := r) (L := r + t) N β ξ hβ hN (by omega) (by omega)

/-- A limit of the centered free-square Villain-clock disorder expectations along an arbitrary
index sequence (possibly constant, so not necessarily a thermodynamic limit). Internal helper
carrier; the source-facing carrier is `IsFreeSquareDisorderExhaustingLimitPoint`. -/
def IsFreeSquareDisorderIndexedLimit (N r : ℕ) (β ξ c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) : Prop :=
  ∃ s : ℕ → ℕ,
    Tendsto (fun k => freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr (s k))
      atTop (𝓝 c)

/-- Every selected Villain-clock disorder limit point inherits any bound uniform along the
centered free-square exhaustion. -/
theorem freeSquareDisorderIndexedLimit_ge_of_uniformLower (N r : ℕ) (β ξ b c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hfinite : ∀ t, b ≤ freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr t)
    (hc : IsFreeSquareDisorderIndexedLimit N r β ξ c hβ hN hr) :
    b ≤ c := by
  rcases hc with ⟨s, hs⟩
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hs
    (eventually_atTop.2 ⟨0, fun t _ => hfinite (s t)⟩)

/-- A finite-volume power lower bound uniform along the centered-square exhaustion passes to every
selected Villain-clock disorder limit point. -/
theorem freeSquareDisorderIndexedLimit_ge_of_uniformPowerLower (N r : ℕ) (β ξ K β''' c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hfinite : ∀ t,
      K * Real.rpow (1 + (r : ℝ)) (-(ξ ^ 2 * β''' / (2 * Real.pi))) ≤
        freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr t)
    (hc : IsFreeSquareDisorderIndexedLimit N r β ξ c hβ hN hr) :
    K * Real.rpow (1 + (r : ℝ)) (-(ξ ^ 2 * β''' / (2 * Real.pi))) ≤ c :=
  freeSquareDisorderIndexedLimit_ge_of_uniformLower N r β ξ _ c hβ hN hr hfinite hc

/-- Every selected Villain-clock disorder limit point inherits any upper bound uniform along the
centered free-square exhaustion. -/
theorem freeSquareDisorderIndexedLimit_le_of_uniformUpper (N r : ℕ) (β ξ b c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hfinite : ∀ t, freeSquareDisorderExpectationExhaustion N r β ξ hβ hN hr t ≤ b)
    (hc : IsFreeSquareDisorderIndexedLimit N r β ξ c hβ hN hr) :
    c ≤ b := by
  rcases hc with ⟨s, hs⟩
  exact le_of_tendsto_of_tendsto hs tendsto_const_nhds
    (eventually_atTop.2 ⟨0, fun t _ => hfinite (s t)⟩)

end FroehlichSpencer.BKT.Clock.VillainClock

end
