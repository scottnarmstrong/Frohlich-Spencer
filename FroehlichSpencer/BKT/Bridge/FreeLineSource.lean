/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.SquareCarriers
public import FroehlichSpencer.BKT.Lattice2D.C64Reflection
public import FroehlichSpencer.BKT.Lattice2D.TorusPotential

/-!
# Free square transport and line-source algebra

Transport between the free square and the internal model, and the
algebra of the free line source used for KP (6.3).
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Edge sums of an even function of the gradient are invariant under graph isomorphism. -/
theorem Multigraph.Isomorphism.sum_comp_grad_of_even {V E W F : Type*}
    {G : Multigraph V E} {H : Multigraph W F} (I : Multigraph.Isomorphism G H)
    [Fintype E] [Fintype F] (h : ℝ → ℝ) (heven : ∀ t, h (-t) = h t) (f : V → ℝ) :
    ∑ e, h (H.grad (I.pushField f) e) = ∑ e, h (G.grad f e) := by
  classical
  rw [← I.edges.sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  rcases I.endpoints e with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
  · simp [Multigraph.grad, Multigraph.Isomorphism.pushField, hsrc, htgt]
  · have : H.grad (I.pushField f) (I.edges e) = -G.grad f e := by
      simp [Multigraph.grad, Multigraph.Isomorphism.pushField, hsrc, htgt]
    rw [this, heven]

/--
The free-square Green form equals the internal `greenBilinear`.
-/
theorem squareFree_pairing_neg_greenOp_eq_greenBilinear {L : ℕ} (hL : 1 < L)
    (hG : (Lattice2D.squareFreeGraph L).Connected) (f : Fin L × Fin L → ℝ) :
    Multigraph.pairing f (-(squareFree L).greenOp (squareFree_connected L hL) f) =
      Lattice2D.greenBilinear (Lattice2D.squareFreeGraph L) hG f f := by
  have h := Multigraph.Isomorphism.greenOp_transport (squareFreeSourceGraphIsomorphism L)
    (squareFree_connected L hL) (f := f)
  have h2 := Multigraph.Isomorphism.pairing_transport (squareFreeSourceGraphIsomorphism L)
    f (-(squareFree L).greenOp (squareFree_connected L hL) f)
  unfold Lattice2D.greenBilinear
  rw [← h2]
  have h3 : (squareFreeSourceGraphIsomorphism L).pushField f = f := rfl
  have h4 : (squareFreeSourceGraphIsomorphism L).pushField
      (-(squareFree L).greenOp (squareFree_connected L hL) f) =
      -(Lattice2D.squareFreeGraph L).greenOp hG f := by
    exact congrArg Neg.neg h
  rw [h3, h4]

/--
Even edge functions of the Green potential's gradient agree on the and internal free
squares.
-/
theorem squareFree_sum_comp_grad_greenOp_of_even {L : ℕ} (hL : 1 < L)
    (hG : (Lattice2D.squareFreeGraph L).Connected) (h : ℝ → ℝ) (heven : ∀ t, h (-t) = h t)
    (f : Fin L × Fin L → ℝ) :
    ∑ e, h ((squareFree L).grad ((squareFree L).greenOp (squareFree_connected L hL) f) e) =
      ∑ e, h ((Lattice2D.squareFreeGraph L).grad
        ((Lattice2D.squareFreeGraph L).greenOp hG f) e) := by
  have h1 := Multigraph.Isomorphism.greenOp_transport (squareFreeSourceGraphIsomorphism L)
    (squareFree_connected L hL) (f := f)
  have h2 := Multigraph.Isomorphism.sum_comp_grad_of_even (squareFreeSourceGraphIsomorphism L)
    h heven ((squareFree L).greenOp (squareFree_connected L hL) f)
  rw [← h2]
  exact congrArg (fun u => ∑ e, h ((Lattice2D.squareFreeGraph L).grad u e)) h1

/-- Pairing with the line source of KP (6.3) sums the row differences over the columns `t ≥ y₀`. -/
theorem sum_mul_squareFreeLineSource {L : ℕ} (y₀ y₁ : ℕ) (hy₁ : y₁ + 1 < L)
    (φ : Fin L × Fin L → ℝ) :
    ∑ j, φ j * Lattice2D.squareFreeLineSource L y₀ y₁ j =
      ∑ t : Fin L with y₀ ≤ t.val,
        (φ (t, ⟨y₁, by omega⟩) - φ (t, ⟨y₁ + 1, hy₁⟩)) := by
  rw [Fintype.sum_prod_type, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : y₀ ≤ t.val
  · simp only [Lattice2D.squareFreeLineSource, ht, true_and, ite_true, mul_sub, mul_ite,
      mul_one, mul_zero, Finset.sum_sub_distrib]
    have e1 : ∀ x : Fin L, (x.val = y₁) ↔ x = (⟨y₁, by omega⟩ : Fin L) := fun x => by rw [Fin.ext_iff]
    have e2 : ∀ x : Fin L, (x.val = y₁ + 1) ↔ x = (⟨y₁ + 1, hy₁⟩ : Fin L) :=
      fun x => by rw [Fin.ext_iff]
    simp_rw [e1, e2]
    rw [Finset.sum_ite_eq' Finset.univ (⟨y₁, by omega⟩ : Fin L) (fun j => φ (t, j)),
      Finset.sum_ite_eq' Finset.univ (⟨y₁ + 1, hy₁⟩ : Fin L) (fun j => φ (t, j))]
    simp
  · simp [Lattice2D.squareFreeLineSource, ht]

/-- The corrected line source of KP (6.3) is neutral. -/
theorem sum_squareFreeLineSource {L : ℕ} (y₀ y₁ : ℕ) (hy₁ : y₁ + 1 < L) :
    ∑ j, Lattice2D.squareFreeLineSource L y₀ y₁ j = 0 := by
  have := sum_mul_squareFreeLineSource y₀ y₁ hy₁ (fun _ => 1)
  simpa using this

/-- There are `L - y₀` columns `t ≥ y₀`. -/
theorem card_filter_le_val (L y₀ : ℕ) :
    (Finset.univ.filter fun t : Fin L => y₀ ≤ t.val).card = L - y₀ := by
  have h : (Finset.univ.filter fun t : Fin L => y₀ ≤ t.val).map Fin.valEmbedding =
      Finset.Ico y₀ L := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, a.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨n, h2⟩, h1, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h]
  simp

end FroehlichSpencer.BKT

end
