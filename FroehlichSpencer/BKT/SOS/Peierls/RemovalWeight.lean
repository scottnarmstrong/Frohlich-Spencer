/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Peierls.BondEquiv
public import FroehlichSpencer.BKT.SOS.Peierls.RemovalGeometry
import Mathlib.Tactic

/-! # Exact SOS weight factorization under contour removal -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Peierls

open Classical
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Clock.Peierls
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site)
open FroehlichSpencer.BKT.SOS.Roughening (sosHeightWeight)

private theorem prod_split_filter {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (f : E → ℝ) :
    (∏ e : E, f e) =
      (∏ e ∈ S, f e) *
        ∏ e ∈ (Finset.univ.filter fun e : E => e ∉ S), f e := by
  classical
  calc
    (∏ e : E, f e) =
        ∏ e ∈ (Finset.univ : Finset E), if e ∈ S then f e else f e := by
      simp
    _ = (∏ e ∈ (Finset.univ : Finset E) with e ∈ S, f e) *
          ∏ e ∈ (Finset.univ : Finset E) with e ∉ S, f e := Finset.prod_ite _ _
    _ = (∏ e ∈ S, f e) *
          ∏ e ∈ (Finset.univ.filter fun e : E => e ∉ S), f e := by
      congr 1
      · simp

/-- The free-square SOS product on the expanded side-`L+2` box. -/
def expandedSOSWeight (L : ℕ) (β : ℝ)
    (n : Lattice2D.SquareFreeVertex (L + 2) → ℤ) : ℝ :=
  ∏ e : Lattice2D.SquareFreeEdge (L + 2),
    Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n e|))

/-- Removing a fixed saturated contour factors the expanded SOS weight into the removed
configuration's weight and the Boltzmann weights of the recorded contour gradients. -/
theorem expandedSOSWeight_eq_contourRemoved_mul_labels {L : ℕ}
    (β : ℝ) (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (n : RemovableSOSHeight Γ) :
    expandedSOSWeight L β n.1 =
      expandedSOSWeight L β (contourRemovedHeight Γ n) *
        ∏ e ∈ Γ,
          Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|)) := by
  classical
  let f (h : Lattice2D.SquareFreeVertex (L + 2) → ℤ)
      (e : Lattice2D.SquareFreeEdge (L + 2)) : ℝ :=
    Real.exp (-(β * |(squareFreeGraph (L + 2)).grad h e|))
  have hnSpec := contourRemovedHeight_spec Γ n
  have hremovedEdge (e : Lattice2D.SquareFreeEdge (L + 2)) (he : e ∈ Γ) :
      (squareFreeGraph (L + 2)).grad (contourRemovedHeight Γ n) e = 0 := by
    rw [hnSpec.2 e]
    simp [restrictEdgeFieldOutside, he]
  have houtside (e : Lattice2D.SquareFreeEdge (L + 2)) (he : e ∉ Γ) :
      (squareFreeGraph (L + 2)).grad n.1 e =
        (squareFreeGraph (L + 2)).grad (contourRemovedHeight Γ n) e := by
    have h := hnSpec.2 e
    rw [restrictEdgeFieldOutside, ite_eq_right he] at h
    exact h.symm
  have hfull (h : Lattice2D.SquareFreeVertex (L + 2) → ℤ) :
      expandedSOSWeight L β h =
        (∏ e ∈ Γ, f h e) *
          ∏ e ∈ (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge (L + 2) => e ∉ Γ),
            f h e := by
    dsimp [expandedSOSWeight, f]
    exact prod_split_filter Γ _
  have hΓremoved :
      (∏ e ∈ Γ, f (contourRemovedHeight Γ n) e) = 1 := by
    apply Finset.prod_eq_one
    intro e he
    simp [f, hremovedEdge e he]
  have houtsideEq :
      (∏ e ∈ (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge (L + 2) => e ∉ Γ), f n.1 e) =
        ∏ e ∈ (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge (L + 2) => e ∉ Γ),
          f (contourRemovedHeight Γ n) e := by
    apply Finset.prod_congr rfl
    intro e he
    dsimp [f]
    exact congrArg (fun z : ℤ => Real.exp (-(β * |z|)))
      (houtside e (Finset.mem_filter.mp he).2)
  calc
    expandedSOSWeight L β n.1 =
        (∏ e ∈ Γ, f n.1 e) *
          ∏ e ∈ (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge (L + 2) => e ∉ Γ),
            f n.1 e := hfull n.1
    _ = (∏ e ∈ Γ, f n.1 e) *
          ∏ e ∈ (Finset.univ.filter fun e : Lattice2D.SquareFreeEdge (L + 2) => e ∉ Γ),
            f (contourRemovedHeight Γ n) e := by rw [houtsideEq]
    _ = expandedSOSWeight L β (contourRemovedHeight Γ n) *
          ∏ e ∈ Γ, f n.1 e := by
      rw [hfull (contourRemovedHeight Γ n), hΓremoved]
      ring
    _ = _ := rfl

/-- The exact contour-removal factorization transferred back to the pinned SOS weight. -/
theorem sosHeightWeight_eq_contourRemoved_mul_labels {L : ℕ}
    (β : ℝ) (Γ : Finset (Lattice2D.SquareFreeEdge (L + 2)))
    (n : RemovableSOSHeight Γ) :
    sosHeightWeight L β (restrictHeight n.1) =
      sosHeightWeight L β (restrictHeight (contourRemovedHeight Γ n)) *
        ∏ e ∈ Γ,
          Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|)) := by
  have hextOrig : extendHeight L (restrictHeight n.1) = n.1 :=
    extendHeight_restrictHeight n.1 n.2.1
  have hextRemoved :
      extendHeight L (restrictHeight (contourRemovedHeight Γ n)) = contourRemovedHeight Γ n :=
    extendHeight_restrictHeight (contourRemovedHeight Γ n)
      (contourRemovedHeight_spec Γ n).1
  have hOrigWeight :
      sosHeightWeight L β (restrictHeight n.1) = expandedSOSWeight L β n.1 := by
    rw [sosHeightWeight_eq_prod_expandedEdges β (restrictHeight n.1)]
    unfold expandedSOSWeight
    simp only [hextOrig]
  have hRemovedWeight :
      expandedSOSWeight L β (contourRemovedHeight Γ n) =
        sosHeightWeight L β (restrictHeight (contourRemovedHeight Γ n)) := by
    rw [sosHeightWeight_eq_prod_expandedEdges β
      (restrictHeight (contourRemovedHeight Γ n))]
    change (∏ e : Lattice2D.SquareFreeEdge (L + 2),
      Real.exp (-(β * |(squareFreeGraph (L + 2)).grad
        (contourRemovedHeight Γ n) e|))) = _
    simp only [hextRemoved]
  calc
    sosHeightWeight L β (restrictHeight n.1) = expandedSOSWeight L β n.1 := hOrigWeight
    _ = expandedSOSWeight L β (contourRemovedHeight Γ n) *
          ∏ e ∈ Γ,
            Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|)) :=
      expandedSOSWeight_eq_contourRemoved_mul_labels β Γ n
    _ = sosHeightWeight L β (restrictHeight (contourRemovedHeight Γ n)) *
          ∏ e ∈ Γ,
            Real.exp (-(β * |(squareFreeGraph (L + 2)).grad n.1 e|)) := by
      rw [hRemovedWeight]

end FroehlichSpencer.BKT.SOS.Peierls

end
