/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Peierls.ExpandedEdges
import Mathlib.Tactic

/-! # Exact edge correspondence for the zero boundary SOS box -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Peierls

open Classical
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.SOS.Roughening (sosHeightWeight)

/-- The pinned SOS bonds are exactly the free edges of the expanded square that touch its
interior box. -/
def squareZeroBondExpandedEdgeEquiv (L : ℕ) : SquareZeroBond L ≃ ExpandedInnerEdge L := by
  apply Equiv.ofBijective squareZeroBondToExpandedInnerEdge
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact squareZeroBondToExpandedInnerEdge_injective
  · calc
      Fintype.card (SquareZeroBond L) =
          Fintype.card (Lattice2D.SquareFreeEdge (L + 1)) :=
        Fintype.card_congr (FroehlichSpencer.BKT.Duality.squareZeroWiredBoxEdgeEquiv L)
      _ = Fintype.card (ExpandedInnerEdge L) :=
        (Fintype.card_congr (expandedInnerEdgeEquiv L)).symm

private def expandedEdgeTouchesInner (L : ℕ) (e : Lattice2D.SquareFreeEdge (L + 2)) : Prop :=
  isInnerVertex L ((squareFreeGraph (L + 2)).src e) ∨
    isInnerVertex L ((squareFreeGraph (L + 2)).tgt e)

/-- The expanded height weight factors over the inner-touching edges and the outer-only edges;
the latter all have zero gradient. -/
theorem expandedHeightWeight_eq_prod_innerEdges (L : ℕ) (β : ℝ) (n : Site L → ℤ) :
    (∏ e : Lattice2D.SquareFreeEdge (L + 2),
      Real.exp (-(β * |(squareFreeGraph (L + 2)).grad (extendHeight L n) e|))) =
      ∏ e : ExpandedInnerEdge L,
        Real.exp (-(β * |(squareFreeGraph (L + 2)).grad (extendHeight L n) e.1|)) := by
  classical
  let f : Lattice2D.SquareFreeEdge (L + 2) → ℝ := fun e =>
    Real.exp (-(β * |(squareFreeGraph (L + 2)).grad (extendHeight L n) e|))
  let P := expandedEdgeTouchesInner L
  let split := Equiv.sumCompl P
  let innerEquiv : {e : Lattice2D.SquareFreeEdge (L + 2) // P e} ≃
      ExpandedInnerEdge L :=
    { toFun := fun e => ⟨e.1, e.2⟩
      invFun := fun e => ⟨e.1, e.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have houter : (∏ x : {e : Lattice2D.SquareFreeEdge (L + 2) // ¬ P e}, f x.1) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    have hsrc : ¬ isInnerVertex L ((squareFreeGraph (L + 2)).src x.1) :=
      (not_or.mp x.2).1
    have htgt : ¬ isInnerVertex L ((squareFreeGraph (L + 2)).tgt x.1) :=
      (not_or.mp x.2).2
    have hgrad := outerOuterGradient_zero n x.1 hsrc htgt
    simp [f, hgrad]
  calc
    (∏ e : Lattice2D.SquareFreeEdge (L + 2), f e) =
        ∏ x : {e : Lattice2D.SquareFreeEdge (L + 2) // P e}, f x.1 := by
      calc
        _ = ∏ x : {e : Lattice2D.SquareFreeEdge (L + 2) // P e} ⊕
              {e : Lattice2D.SquareFreeEdge (L + 2) // ¬ P e}, f (split x) :=
          (Fintype.prod_equiv split (fun x => f (split x)) f (fun _ => rfl)).symm
        _ = (∏ x : {e : Lattice2D.SquareFreeEdge (L + 2) // P e}, f x.1) *
              ∏ x : {e : Lattice2D.SquareFreeEdge (L + 2) // ¬ P e}, f x.1 := by
          rw [Fintype.prod_sum_type]
          dsimp only [split]
          simp only [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
        _ = ∏ x : {e : Lattice2D.SquareFreeEdge (L + 2) // P e}, f x.1 := by
          rw [houter, mul_one]
    _ = ∏ e : ExpandedInnerEdge L, f e.1 := by
      exact Fintype.prod_equiv innerEquiv _ _ (fun _ => rfl)

/-- The SOS energy on `squareZero L` is exactly the expanded free-square energy after zero
extension, including the outer-only edges whose gradients vanish. -/
theorem sosHeightWeight_eq_prod_expandedEdges {L : ℕ} (β : ℝ) (n : Site L → ℤ) :
    sosHeightWeight L β n =
      ∏ e : Lattice2D.SquareFreeEdge (L + 2),
        Real.exp (-(β * |(squareFreeGraph (L + 2)).grad (extendHeight L n) e|)) := by
  rw [expandedHeightWeight_eq_prod_innerEdges]
  rw [← Fintype.prod_equiv (squareZeroBondExpandedEdgeEquiv L)
    (fun b : SquareZeroBond L =>
      Real.exp (-(β * |(squareFreeGraph (L + 2)).grad (extendHeight L n)
        (squareZeroBondToExpandedInnerEdge b).1|)))
    (fun e : ExpandedInnerEdge L =>
      Real.exp (-(β * |(squareFreeGraph (L + 2)).grad (extendHeight L n) e.1|)))
    (fun _ => rfl)]
  exact sosHeightWeight_eq_prod_mappedEdges β n

end FroehlichSpencer.BKT.SOS.Peierls

end
