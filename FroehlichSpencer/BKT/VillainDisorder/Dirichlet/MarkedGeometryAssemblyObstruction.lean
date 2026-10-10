/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedInterface
import Mathlib.Tactic

/-!
The second goal is stated here as `RemainderWaveGoalForAll`, verbatim from the note.

It is
strictly stronger than the term field.

On the triangle with one remainder charge of activity `2`
and composite gain `0`:
* the term data hold (`rootedMarkedTermData_triangle`);
* the remainder goal fails (`not_remainderWaveGoalForAll_triangle`).

The admissible composite wave
  `a₀ = (1, 1, 0)` makes the clauses `⟨a_ϱ, σ⟩ = 0` and `⟨a₀, Δ a_ϱ⟩ = 0` force `a_ϱ` constant, so
  the renormalized activity of the remainder charge stays `2 > 1`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.Marked

section Goal

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- The design note's `RemainderWaveGoal`: remainder waves for **every** composite wave `a₀`
satisfying the remainder orthogonality and the gain. -/
def RemainderWaveGoalForAll (G : Multigraph V E) (τ : ℝ) (N : Finset (V → ℤ))
    (K cost : (V → ℤ) → ℝ) (ξ : ℝ) (ρ₀ : V → ℤ) (adj : (V → ℤ) → Finset (V → ℤ) → Prop)
    (γ ℓ : ℝ) : Prop :=
  ∀ C ∈ clusters adj N, ∀ T ⊆ C, ∀ a₀ : V → ℝ,
    (∀ ϱ ∈ remainder adj N C, Multigraph.pairing a₀ (fun j => (ϱ j : ℝ)) = 0) →
    γ * (∑ m ∈ C, cost m + ℓ) ≤ gffTranslationEnergy G τ a₀ (rootedMarkedComposite ξ ρ₀ C T) →
    ∃ a : (V → ℤ) → V → ℝ,
      (∀ ϱ ∈ remainder adj N C,
        Multigraph.pairing (a ϱ) (rootedMarkedComposite ξ ρ₀ C T) = 0) ∧
      (∀ ϱ ∈ remainder adj N C, ∀ ϱ' ∈ remainder adj N C, ϱ ≠ ϱ' →
        Multigraph.pairing (a ϱ) (fun j => (ϱ' j : ℝ)) = 0) ∧
      (∀ ϱ ∈ remainder adj N C, Multigraph.pairing a₀ (G.laplacian (a ϱ)) = 0) ∧
      (∀ ϱ ∈ remainder adj N C, ∀ ϱ' ∈ remainder adj N C, ϱ ≠ ϱ' →
        Multigraph.pairing (a ϱ) (G.laplacian (a ϱ')) = 0) ∧
      (∀ ϱ ∈ remainder adj N C, |K ϱ| * Real.exp
        (-gffTranslationEnergy G τ (a ϱ) (fun j => (ϱ j : ℝ))) ≤ 1)

end Goal

/-! ### The triangle -/

/-- The triangle `0 – 1 – 2 – 0`, with edges `0 → 1`, `1 → 2`, `0 → 2`. -/
def triangleGraph : Multigraph (Fin 3) (Fin 3) where
  src := ![0, 1, 0]
  tgt := ![1, 2, 2]
  src_ne_tgt := by decide

/-- The remainder charge `δ₀ − δ₁`. -/
def triangleCharge : Fin 3 → ℤ := ![1, -1, 0]

/-- The mark `δ₁ − δ₂`. -/
def triangleMark : Fin 3 → ℤ := ![0, 1, -1]

/-- The adjacency with no adjacent pair. -/
def triangleAdj : (Fin 3 → ℤ) → Finset (Fin 3 → ℤ) → Prop := fun _ _ => False

theorem growIter_triangleAdj (T : Finset (Fin 3 → ℤ)) (k : ℕ) : growIter triangleAdj T k = ∅ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [growIter_succ, ih]
    unfold growStep
    ext m
    simp only [Finset.empty_union, Finset.notMem_empty, iff_false, Finset.mem_filter]
    exact fun h => h.2

theorem eq_empty_of_mem_clusters_triangleAdj {C : Finset (Fin 3 → ℤ)}
    (hC : C ∈ clusters triangleAdj {triangleCharge}) : C = ∅ := by
  have h := (mem_clusters.1 hC).2
  unfold component at h
  rw [growIter_triangleAdj] at h
  exact h.symm

theorem empty_mem_clusters_triangleAdj : (∅ : Finset (Fin 3 → ℤ)) ∈
    clusters triangleAdj {triangleCharge} :=
  mem_clusters.2 ⟨Finset.empty_subset _, growIter_triangleAdj _ _⟩

theorem remainder_triangleAdj : remainder triangleAdj {triangleCharge} ∅ = {triangleCharge} := by
  unfold remainder
  simp [triangleAdj]

theorem triangle_composite :
    rootedMarkedComposite (1 / 2) triangleMark ∅ ∅ = ![0, 1 / 2, -1 / 2] := by
  funext j
  fin_cases j <;> simp [rootedMarkedComposite, triangleMark]
  norm_num

/-- **The term data hold on the triangle**: `a₀ = 0` and `a_ϱ = (2, 0, 0)`. -/
theorem rootedMarkedTermData_triangle :
    ∀ C ∈ clusters triangleAdj {triangleCharge}, ∀ T ⊆ C,
      RootedMarkedTermData triangleGraph (1 / 4) (fun _ => 2)
        (rootedMarkedComposite (1 / 2) triangleMark C T)
        (remainder triangleAdj {triangleCharge} C) (0 * (∑ _m ∈ C, (0 : ℝ) + 0)) := by
  intro C hC T hT
  obtain rfl := eq_empty_of_mem_clusters_triangleAdj hC
  obtain rfl := Finset.subset_empty.mp hT
  rw [remainder_triangleAdj]
  refine ⟨0, fun _ => ![2, 0, 0], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ϱ _
    simp [Multigraph.pairing]
  · intro ϱ _
    rw [triangle_composite]
    simp [Multigraph.pairing, Fin.sum_univ_three]
  · intro ϱ hϱ ϱ' hϱ' hne
    rw [Finset.mem_singleton] at hϱ hϱ'
    exact absurd (hϱ.trans hϱ'.symm) hne
  · intro ϱ _
    simp [Multigraph.pairing]
  · intro ϱ hϱ ϱ' hϱ' hne
    rw [Finset.mem_singleton] at hϱ hϱ'
    exact absurd (hϱ.trans hϱ'.symm) hne
  · intro ϱ hϱ
    rw [Finset.mem_singleton] at hϱ
    subst hϱ
    have hE : gffTranslationEnergy triangleGraph (1 / 4) ![2, 0, 0]
        (fun j => (triangleCharge j : ℝ)) = 1 := by
      simp [gffTranslationEnergy, Multigraph.pairing, Multigraph.energy, Multigraph.grad,
        Fin.sum_univ_three, triangleGraph, triangleCharge]
      norm_num
    rw [hE]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    rw [Real.exp_neg, abs_two]
    rw [mul_inv_le_iff₀ (Real.exp_pos 1)]
    linarith
  · simp [gffTranslationEnergy, Multigraph.pairing, Multigraph.energy, Multigraph.grad]

/-- **The remainder goal for every composite wave fails on the triangle.** -/
theorem not_remainderWaveGoalForAll_triangle :
    ¬ RemainderWaveGoalForAll triangleGraph (1 / 4) {triangleCharge} (fun _ => 2) (fun _ => 0)
      (1 / 2) triangleMark triangleAdj 0 0 := by
  intro H
  have hpair : ∀ ϱ ∈ remainder triangleAdj {triangleCharge} ∅,
      Multigraph.pairing ![(1 : ℝ), 1, 0] (fun j => (ϱ j : ℝ)) = 0 := by
    intro ϱ hϱ
    rw [remainder_triangleAdj, Finset.mem_singleton] at hϱ
    subst hϱ
    simp [Multigraph.pairing, Fin.sum_univ_three, triangleCharge]
  have hgain : 0 * (∑ m ∈ (∅ : Finset (Fin 3 → ℤ)), (fun _ => (0 : ℝ)) m + 0) ≤
      gffTranslationEnergy triangleGraph (1 / 4) ![(1 : ℝ), 1, 0]
        (rootedMarkedComposite (1 / 2) triangleMark ∅ ∅) := by
    simp only [Finset.sum_empty, add_zero, mul_zero]
    rw [triangle_composite]
    simp [gffTranslationEnergy, Multigraph.pairing, Multigraph.energy, Multigraph.grad,
      Fin.sum_univ_three, triangleGraph]
    norm_num
  obtain ⟨a, h₁, -, h₃, -, h₅⟩ := H ∅ empty_mem_clusters_triangleAdj ∅ (Finset.Subset.refl _)
    ![1, 1, 0] hpair hgain
  have hmem : triangleCharge ∈ remainder triangleAdj {triangleCharge} ∅ := by
    rw [remainder_triangleAdj]
    exact Finset.mem_singleton_self _
  set b := a triangleCharge with hb
  have e₁ := h₁ triangleCharge hmem
  have e₃ := h₃ triangleCharge hmem
  have e₅ := h₅ triangleCharge hmem
  rw [← hb] at e₁ e₃ e₅
  rw [Multigraph.pairing_laplacian_eq_neg_sum_grad_mul] at e₃
  rw [triangle_composite] at e₁
  simp [Multigraph.pairing, Fin.sum_univ_three] at e₁
  simp [Multigraph.grad, Fin.sum_univ_three, triangleGraph] at e₃
  have hb12 : b 1 = b 2 := by linarith
  have hb02 : b 0 = b 2 := by linarith
  have hE : gffTranslationEnergy triangleGraph (1 / 4) b (fun j => (triangleCharge j : ℝ)) = 0 := by
    simp [gffTranslationEnergy, Multigraph.pairing, Multigraph.energy, Multigraph.grad,
      Fin.sum_univ_three, triangleGraph, triangleCharge, hb12, hb02]
  rw [hE, neg_zero, Real.exp_zero, mul_one] at e₅
  norm_num at e₅

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
