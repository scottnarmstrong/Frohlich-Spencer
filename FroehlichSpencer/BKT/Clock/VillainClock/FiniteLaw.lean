/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Fourier.PeriodizedGaussian
public import FroehlichSpencer.BKT.Ginibre.Models
import Mathlib.Tactic.FieldSimp

/-!
# The finite free-box Villain-clock law and disorder insertion

We use counting measure on clock configurations.

The
`N^{-|Λ|}` factor from the comb measure cancels in normalized expectations.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Ginibre

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The angle at a clock value `k ∈ Fin N`. -/
def clockAngle (N : ℕ) (k : Fin N) : ℝ := 2 * Real.pi * (k : ℝ) / N

/-- The finite clock angle field on a vertex set. -/
def angleField {V : Type*} (N : ℕ) (s : V → Fin N) : V → ℝ :=
  fun v => clockAngle N (s v)

/-- The free-boundary Villain-clock Boltzmann weight on a finite oriented graph. -/
def configurationWeight {V E : Type*} [Fintype E]
    (G : Multigraph V E) (β : ℝ) (N : ℕ) (s : V → Fin N) : ℝ :=
  ∏ e : E, villainWeight β
    (angleField N s (G.src e) - angleField N s (G.tgt e))

/-- The finite free-box Villain-clock partition function with counting-measure normalization. -/
def partitionFunction {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Multigraph V E) (β : ℝ) (N : ℕ) : ℝ :=
  ∑ s : V → Fin N, configurationWeight G β N s

/-- The positive seam insertion on an oriented marked edge set, using the shift `+2πξ`. -/
def disorderObservable {V E : Type*} [Fintype E] [DecidableEq E]
    (G : Multigraph V E) (M : Finset E) (β ξ : ℝ) (N : ℕ) (s : V → Fin N) : ℝ :=
  ∏ e : E, if e ∈ M then
    villainWeight β (angleField N s (G.src e) - angleField N s (G.tgt e) + 2 * Real.pi * ξ) /
      villainWeight β (angleField N s (G.src e) - angleField N s (G.tgt e))
  else 1

/-- The finite Boltzmann weight after shifting each marked seam edge by `+2πξ`. -/
def twistedConfigurationWeight {V E : Type*} [Fintype E] [DecidableEq E]
    (G : Multigraph V E) (M : Finset E) (β ξ : ℝ) (N : ℕ) (s : V → Fin N) : ℝ :=
  ∏ e : E, villainWeight β
    (angleField N s (G.src e) - angleField N s (G.tgt e) +
      if e ∈ M then 2 * Real.pi * ξ else 0)

/-- The partition function with the Villain-clock seam shift inserted. -/
def twistedPartitionFunction {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Multigraph V E) (M : Finset E) (β ξ : ℝ) (N : ℕ) : ℝ :=
  ∑ s : V → Fin N, twistedConfigurationWeight G M β ξ N s

/-- The normalized finite-volume Villain-clock disorder expectation. -/
def disorderExpectation {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Multigraph V E) (M : Finset E) (β ξ : ℝ) (N : ℕ) : ℝ :=
  (∑ s : V → Fin N, disorderObservable G M β ξ N s * configurationWeight G β N s) /
    partitionFunction G β N

/-- Every finite configuration has positive Villain-clock weight at positive temperature. -/
theorem configurationWeight_pos {V E : Type*} [Fintype E]
    (G : Multigraph V E) {β : ℝ} (hβ : 0 < β) (N : ℕ) (s : V → Fin N) :
    0 < configurationWeight G β N s := by
  unfold configurationWeight
  exact Finset.prod_pos fun e _ => VillainWeight.villainWeight_pos hβ _

/-- The finite Villain-clock partition function is strictly positive for every positive clock
order and inverse temperature. -/
theorem partitionFunction_pos {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Multigraph V E) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    0 < partitionFunction G β N := by
  classical
  unfold partitionFunction
  let s₀ : V → Fin N := fun _ => ⟨0, by omega⟩
  exact Finset.sum_pos (fun s _ => configurationWeight_pos G hβ N s)
    ⟨s₀, Finset.mem_univ _⟩

/-- Multiplying by the seam observable inserts exactly the shifted edge weights. -/
theorem configurationWeight_mul_disorderObservable_eq_twisted
    {V E : Type*} [Fintype E] [DecidableEq E]
    (G : Multigraph V E) (M : Finset E) {β : ℝ} (hβ : 0 < β) (ξ : ℝ)
    (N : ℕ) (s : V → Fin N) :
    configurationWeight G β N s * disorderObservable G M β ξ N s =
      twistedConfigurationWeight G M β ξ N s := by
  classical
  unfold configurationWeight disorderObservable twistedConfigurationWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases hm : e ∈ M
  · simp only [ite_eq_left hm]
    have hne : villainWeight β
        (angleField N s (G.src e) - angleField N s (G.tgt e)) ≠ 0 :=
      (VillainWeight.villainWeight_pos hβ _).ne'
    field_simp
  · simp [hm]

/-- The finite Villain-clock disorder expectation equals the shifted/unshifted partition ratio. -/
theorem disorderExpectation_eq_twistedPartition_ratio
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Multigraph V E) (M : Finset E) {β : ℝ} (hβ : 0 < β) (ξ : ℝ)
    (N : ℕ) :
    disorderExpectation G M β ξ N =
      twistedPartitionFunction G M β ξ N / partitionFunction G β N := by
  classical
  unfold disorderExpectation twistedPartitionFunction
  congr 1
  rw [Finset.sum_congr rfl]
  intro s hs
  rw [mul_comm, configurationWeight_mul_disorderObservable_eq_twisted G M hβ ξ N s]

end FroehlichSpencer.BKT.Clock.VillainClock

end
