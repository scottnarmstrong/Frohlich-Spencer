/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Duality.WiredBox
public import FroehlichSpencer.BKT.Duality.Expectation
public import FroehlichSpencer.BKT.Bridge.SquareCarriers
public import FroehlichSpencer.BKT.Villain.SquareSymmetry
public import FroehlichSpencer.BKT.Potential.Transport
public import FroehlichSpencer.BKT.Villain.GraphSymmetry

/-! # Coordinate symmetries of the internal wired square

The primal reflection and coordinate swap act on the crossed-edge labels of the dual-square
carrier. These are the graph symmetries used to reduce wired observables to a chosen side.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Duality

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D

/--
The positive horizontal coordinate step in a  edge follows from its row equality.
-/
private theorem wiredBoxSourceHorizontalStep {L : ℕ} (e : SquareFreeEdge L)
    (hrow : e.1.1.2 = e.1.2.2) : e.1.1.1.val + 1 = e.1.2.1.val := by
  rcases squareFreeEdge_classification e with hh | hv
  · exact hh.2
  · have hrowval := congrArg Fin.val hrow
    have hcolval := congrArg Fin.val hv.1
    omega

/--
The positive vertical coordinate step in a  edge follows from its column equality.
-/
private theorem wiredBoxSourceVerticalStep {L : ℕ} (e : SquareFreeEdge L)
    (hrow : e.1.1.2 ≠ e.1.2.2) :
    e.1.1.1 = e.1.2.1 ∧ e.1.1.2.val + 1 = e.1.2.2.val := by
  rcases squareFreeEdge_classification e with hh | hv
  · exact False.elim (hrow hh.1)
  · exact hv

/--
The dual edge crossing a  free-square edge.

Horizontal  edges are crossed by
vertical dual edges and vertical  edges by horizontal dual edges (KP §6.1, p. 32).
-/
def wiredBoxCrossesFreeEdge (L : ℕ) (e : SquareFreeEdge L) : WiredEdge L := by
  classical
  by_cases hrow : e.1.1.2 = e.1.2.2
  · exact verticalDualEdge (Fin.succ e.1.1.1) e.1.1.2
  · exact horizontalDualEdge e.1.1.1 (Fin.succ e.1.1.2)

/--
The dual crossing edge has the free edge's endpoint pair, possibly with reversed
orientation.
-/
theorem wiredBoxCrossesFreeEdge_endpoints (L : ℕ) (e : SquareFreeEdge L) :
    ((wiredBoxGraph L).src (wiredBoxCrossesFreeEdge L e) =
        some ((squareFree L).src e) ∧
      (wiredBoxGraph L).tgt (wiredBoxCrossesFreeEdge L e) =
        some ((squareFree L).tgt e)) ∨
    ((wiredBoxGraph L).src (wiredBoxCrossesFreeEdge L e) =
        some ((squareFree L).tgt e) ∧
      (wiredBoxGraph L).tgt (wiredBoxCrossesFreeEdge L e) =
        some ((squareFree L).src e)) := by
  by_cases hrow : e.1.1.2 = e.1.2.2
  · have hstep := wiredBoxSourceHorizontalStep e hrow
    left
    constructor
    · simp [wiredBoxCrossesFreeEdge, hrow, wiredBoxGraph, wiredBoxSrc,
        squareFree,
        verticalDualEdge, verticalDualEdgeData, verticalPrimalSrc, verticalFaceY,
        Fin.val_succ]
      apply Prod.ext
      · rfl
      · exact hrow.symm
    · simp [wiredBoxCrossesFreeEdge, hrow, wiredBoxGraph, wiredBoxTgt,
        squareFree,
        verticalDualEdge, verticalDualEdgeData, verticalPrimalTgt, verticalFaceY,
        Fin.val_succ, hstep]
  · right
    have hstep := wiredBoxSourceVerticalStep e hrow
    constructor
    · simp [wiredBoxCrossesFreeEdge, hrow, wiredBoxGraph, wiredBoxSrc,
        squareFree,
        horizontalDualEdge, horizontalDualEdgeData, horizontalPrimalSrc, horizontalFaceX,
        Fin.val_succ, hstep]
    · simp [wiredBoxCrossesFreeEdge, hrow, wiredBoxGraph, wiredBoxTgt,
        squareFree,
        horizontalDualEdge, horizontalDualEdgeData, horizontalPrimalTgt, horizontalFaceX,
        Fin.val_succ]

/-- Reflect an internal wired edge in the first primal coordinate. -/
def wiredBoxReflectEdge (L : ℕ) : WiredEdge L → WiredEdge L
  | .inl e => .inl (horizontalDualEdgeData (horizontalFaceX e).rev e.2)
  | .inr e => .inr (verticalDualEdgeData e.1.rev (verticalFaceY e))

/-- Swap the coordinates of an internal wired edge. -/
def wiredBoxSwapEdge (L : ℕ) : WiredEdge L → WiredEdge L
  | .inl e => .inr (verticalDualEdgeData e.2 (horizontalFaceX e))
  | .inr e => .inl (horizontalDualEdgeData (verticalFaceY e) e.1)

@[simp] theorem horizontalFaceX_horizontalDualEdgeData {L : ℕ} (i : Fin L)
    (j : Fin (L + 1)) :
    horizontalFaceX (horizontalDualEdgeData i j) = i := by
  apply Fin.ext
  simp [horizontalFaceX, horizontalDualEdgeData]

@[simp] theorem verticalFaceY_verticalDualEdgeData {L : ℕ} (i : Fin (L + 1))
    (j : Fin L) :
    verticalFaceY (verticalDualEdgeData i j) = j := by
  apply Fin.ext
  simp [verticalFaceY, verticalDualEdgeData]

@[simp] theorem horizontalDualEdgeData_face {L : ℕ}
    (e : SquareFreeHorizontalEdge (L + 1)) :
    horizontalDualEdgeData (horizontalFaceX e) e.2 = e := by
  apply Prod.ext
  · apply Subtype.ext
    apply Fin.ext
    simp [horizontalDualEdgeData, horizontalFaceX]
  · rfl

@[simp] theorem horizontalDualEdgeData_snd {L : ℕ} (i : Fin L)
    (j : Fin (L + 1)) : (horizontalDualEdgeData i j).2 = j := rfl

@[simp] theorem verticalDualEdgeData_fst {L : ℕ} (i : Fin (L + 1))
    (j : Fin L) : (verticalDualEdgeData i j).1 = i := rfl

@[simp] theorem verticalDualEdgeData_face {L : ℕ}
    (e : SquareFreeVerticalEdge (L + 1)) :
    verticalDualEdgeData e.1 (verticalFaceY e) = e := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Fin.ext
    simp [verticalDualEdgeData, verticalFaceY]

/-- Reflection is an involution on the internal wired edge carrier. -/
def wiredBoxReflectEdgeEquiv (L : ℕ) : WiredEdge L ≃ WiredEdge L where
  toFun := wiredBoxReflectEdge L
  invFun := wiredBoxReflectEdge L
  left_inv e := by
    cases e with
    | inl e =>
        apply congrArg Sum.inl
        simp only [horizontalFaceX_horizontalDualEdgeData,
          Fin.rev_rev, horizontalDualEdgeData_snd]
        exact horizontalDualEdgeData_face e
    | inr e =>
        apply congrArg Sum.inr
        simp only [verticalFaceY_verticalDualEdgeData,
          Fin.rev_rev, verticalDualEdgeData_fst]
        exact verticalDualEdgeData_face e
  right_inv e := by
    cases e with
    | inl e =>
        apply congrArg Sum.inl
        simp only [horizontalFaceX_horizontalDualEdgeData,
          Fin.rev_rev, horizontalDualEdgeData_snd]
        exact horizontalDualEdgeData_face e
    | inr e =>
        apply congrArg Sum.inr
        simp only [verticalFaceY_verticalDualEdgeData,
          Fin.rev_rev, verticalDualEdgeData_fst]
        exact verticalDualEdgeData_face e

/-- Coordinate swap is an involution on the internal wired edge carrier. -/
def wiredBoxSwapEdgeEquiv (L : ℕ) : WiredEdge L ≃ WiredEdge L where
  toFun := wiredBoxSwapEdge L
  invFun := wiredBoxSwapEdge L
  left_inv e := by
    cases e with
    | inl e =>
        simp only [wiredBoxSwapEdge, verticalFaceY_verticalDualEdgeData,
          verticalDualEdgeData_fst, horizontalDualEdgeData_face]
    | inr e =>
        simp only [wiredBoxSwapEdge, horizontalDualEdgeData_snd,
          horizontalFaceX_horizontalDualEdgeData,
          verticalDualEdgeData_face]
  right_inv e := by
    cases e with
    | inl e =>
        simp only [wiredBoxSwapEdge, verticalFaceY_verticalDualEdgeData,
          verticalDualEdgeData_fst, horizontalDualEdgeData_face]
    | inr e =>
        simp only [wiredBoxSwapEdge, horizontalDualEdgeData_snd,
          horizontalFaceX_horizontalDualEdgeData,
          verticalDualEdgeData_face]

/-- Source endpoint of a horizontal dual edge, viewed in the wired primal graph. -/
@[simp] theorem wiredBoxSrc_horizontalDualEdge (L : ℕ) (i : Fin L)
    (j : Fin (L + 1)) :
    (wiredBoxGraph L).src (horizontalDualEdge i j) =
      if h : j.val < L then some (i, ⟨j.val, h⟩) else none := by
  simp only [wiredBoxGraph, wiredBoxSrc, horizontalDualEdge, horizontalPrimalSrc,
    horizontalFaceX_horizontalDualEdgeData, horizontalDualEdgeData_snd]

/-- Target endpoint of a horizontal dual edge, viewed in the wired primal graph. -/
@[simp] theorem wiredBoxTgt_horizontalDualEdge (L : ℕ) (i : Fin L)
    (j : Fin (L + 1)) :
    (wiredBoxGraph L).tgt (horizontalDualEdge i j) =
      if h : j.val = 0 then none else
        some (i, ⟨j.val - 1, by have hj := j.isLt; omega⟩) := by
  simp only [wiredBoxGraph, wiredBoxTgt, horizontalDualEdge, horizontalPrimalTgt,
    horizontalFaceX_horizontalDualEdgeData, horizontalDualEdgeData_snd]

/-- Source endpoint of a vertical dual edge, viewed in the wired primal graph. -/
@[simp] theorem wiredBoxSrc_verticalDualEdge (L : ℕ) (i : Fin (L + 1))
    (j : Fin L) :
    (wiredBoxGraph L).src (verticalDualEdge i j) =
      if h : i.val = 0 then none else
        some (⟨i.val - 1, by have hi := i.isLt; omega⟩, j) := by
  simp only [wiredBoxGraph, wiredBoxSrc, verticalDualEdge, verticalPrimalSrc,
    verticalFaceY_verticalDualEdgeData, verticalDualEdgeData_fst]

/-- Target endpoint of a vertical dual edge, viewed in the wired primal graph. -/
@[simp] theorem wiredBoxTgt_verticalDualEdge (L : ℕ) (i : Fin (L + 1))
    (j : Fin L) :
    (wiredBoxGraph L).tgt (verticalDualEdge i j) =
      if h : i.val < L then some (⟨i.val, h⟩, j) else none := by
  simp only [wiredBoxGraph, wiredBoxTgt, verticalDualEdge, verticalPrimalTgt,
    verticalFaceY_verticalDualEdgeData, verticalDualEdgeData_fst]

/-- Reflection sends a horizontal crossed edge to the edge with reversed first coordinate. -/
@[simp] theorem wiredBoxReflectEdge_horizontalDual (L : ℕ) (i : Fin L)
    (j : Fin (L + 1)) :
    wiredBoxReflectEdge L (horizontalDualEdge i j) = horizontalDualEdge i.rev j := by
  simp only [wiredBoxReflectEdge, horizontalDualEdge,
    horizontalFaceX_horizontalDualEdgeData, horizontalDualEdgeData_snd]

/-- Reflection sends a vertical crossed edge to the edge with reversed boundary coordinate. -/
@[simp] theorem wiredBoxReflectEdge_verticalDual (L : ℕ) (i : Fin (L + 1))
    (j : Fin L) :
    wiredBoxReflectEdge L (verticalDualEdge i j) = verticalDualEdge i.rev j := by
  simp only [wiredBoxReflectEdge, verticalDualEdge,
    verticalFaceY_verticalDualEdgeData, verticalDualEdgeData_fst]
/-- Reflection preserves the endpoints of horizontal dual edges. -/
theorem wiredBoxReflect_horizontal_endpoints (L : ℕ) (i : Fin L)
    (j : Fin (L + 1)) :
    ((wiredBoxGraph L).src (wiredBoxReflectEdge L (horizontalDualEdge i j)) =
        wiredSquareReflection L ((wiredBoxGraph L).src (horizontalDualEdge i j)) ∧
      (wiredBoxGraph L).tgt (wiredBoxReflectEdge L (horizontalDualEdge i j)) =
        wiredSquareReflection L ((wiredBoxGraph L).tgt (horizontalDualEdge i j))) := by
  simp only [wiredBoxReflectEdge_horizontalDual, wiredBoxSrc_horizontalDualEdge,
    wiredBoxTgt_horizontalDualEdge]
  constructor
  · by_cases h : j.val < L
    · simp [h]
    · simp [h]
  · by_cases h : j.val = 0
    · simp only [dite_eq_left h, wiredSquareReflection_none]
    · simp only [dite_eq_right h, wiredSquareReflection_some]

/-- Reflection reverses the endpoints of vertical dual edges. -/
theorem wiredBoxReflect_vertical_endpoints (L : ℕ) (i : Fin (L + 1))
    (j : Fin L) :
    ((wiredBoxGraph L).src (wiredBoxReflectEdge L (verticalDualEdge i j)) =
        wiredSquareReflection L ((wiredBoxGraph L).tgt (verticalDualEdge i j)) ∧
      (wiredBoxGraph L).tgt (wiredBoxReflectEdge L (verticalDualEdge i j)) =
        wiredSquareReflection L ((wiredBoxGraph L).src (verticalDualEdge i j))) := by
  simp only [wiredBoxReflectEdge_verticalDual, wiredBoxSrc_verticalDualEdge,
    wiredBoxTgt_verticalDualEdge]
  constructor
  · by_cases hside : i.val < L
    · simp [wiredSquareReflection, hside, Fin.val_rev, Fin.ext_iff]; omega
    · have hlast : i.val = L := by have h := i.isLt; omega
      simp [wiredSquareReflection, hlast, Fin.val_rev]
  · by_cases hzero : i.val = 0
    · simp [wiredSquareReflection, hzero, Fin.val_rev]
    · have hpos : 0 < i.val := by omega
      simp [wiredSquareReflection, hzero, hpos, Fin.val_rev, Fin.ext_iff]; omega

/-- Coordinate swap sends a horizontal crossed edge to the corresponding vertical edge. -/
@[simp] theorem wiredBoxSwapEdge_horizontalDual (L : ℕ) (i : Fin L)
    (j : Fin (L + 1)) :
  wiredBoxSwapEdge L (horizontalDualEdge i j) = verticalDualEdge j i := by
  simp only [wiredBoxSwapEdge, horizontalDualEdge, verticalDualEdge,
    horizontalFaceX_horizontalDualEdgeData, horizontalDualEdgeData_snd]

/-- Coordinate swap sends a vertical crossed edge to the corresponding horizontal edge. -/
@[simp] theorem wiredBoxSwapEdge_verticalDual (L : ℕ) (i : Fin (L + 1))
    (j : Fin L) :
  wiredBoxSwapEdge L (verticalDualEdge i j) = horizontalDualEdge j i := by
  simp only [wiredBoxSwapEdge, horizontalDualEdge, verticalDualEdge,
    verticalFaceY_verticalDualEdgeData, verticalDualEdgeData_fst]

/-- The swapped vertical edge reverses the endpoints of a horizontal crossed edge. -/
theorem wiredBoxSwap_horizontal_endpoints (L : ℕ) (i : Fin L)
    (j : Fin (L + 1)) :
    ((wiredBoxGraph L).src (wiredBoxSwapEdge L (horizontalDualEdge i j)) =
        wiredSquareSwap L ((wiredBoxGraph L).tgt (horizontalDualEdge i j)) ∧
      (wiredBoxGraph L).tgt (wiredBoxSwapEdge L (horizontalDualEdge i j)) =
        wiredSquareSwap L ((wiredBoxGraph L).src (horizontalDualEdge i j))) := by
  simp only [wiredBoxSwapEdge_horizontalDual, wiredBoxSrc_verticalDualEdge,
    wiredBoxTgt_verticalDualEdge, wiredBoxSrc_horizontalDualEdge,
    wiredBoxTgt_horizontalDualEdge]
  constructor
  · by_cases hzero : j.val = 0
    · simp [hzero]
    · have hpos : 0 < j.val := by omega
      simp [hzero]
  · by_cases hside : j.val < L
    · simp [hside]
    · have hlast : j.val = L := by have h := j.isLt; omega
      simp [hlast]

/-- The swapped horizontal edge reverses the endpoints of a vertical crossed edge. -/
theorem wiredBoxSwap_vertical_endpoints (L : ℕ) (i : Fin (L + 1))
    (j : Fin L) :
    ((wiredBoxGraph L).src (wiredBoxSwapEdge L (verticalDualEdge i j)) =
        wiredSquareSwap L ((wiredBoxGraph L).tgt (verticalDualEdge i j)) ∧
      (wiredBoxGraph L).tgt (wiredBoxSwapEdge L (verticalDualEdge i j)) =
        wiredSquareSwap L ((wiredBoxGraph L).src (verticalDualEdge i j))) := by
  simp only [wiredBoxSwapEdge_verticalDual, wiredBoxSrc_horizontalDualEdge,
    wiredBoxTgt_horizontalDualEdge, wiredBoxSrc_verticalDualEdge,
    wiredBoxTgt_verticalDualEdge]
  constructor
  · by_cases hside : i.val < L
    · simp [hside]
    · have hlast : i.val = L := by have h := i.isLt; omega
      simp [hlast]
  · by_cases hzero : i.val = 0
    · simp [hzero]
    · have hpos : 0 < i.val := by omega
      simp [hzero]

/-- Reflection is a multigraph automorphism of the internal wired square. -/
def wiredBoxReflectionIsomorphism (L : ℕ) :
    Multigraph.Isomorphism (wiredBoxGraph L) (wiredBoxGraph L) where
  vertices := wiredSquareReflection L
  edges := wiredBoxReflectEdgeEquiv L
  endpoints := by
    intro e
    cases e with
    | inl e =>
        exact Or.inl (wiredBoxReflect_horizontal_endpoints L (horizontalFaceX e) e.2)
    | inr e =>
        exact Or.inr (wiredBoxReflect_vertical_endpoints L e.1 (verticalFaceY e))

/-- Coordinate swap is a multigraph automorphism of the internal wired square. -/
def wiredBoxSwapIsomorphism (L : ℕ) :
    Multigraph.Isomorphism (wiredBoxGraph L) (wiredBoxGraph L) where
  vertices := wiredSquareSwap L
  edges := wiredBoxSwapEdgeEquiv L
  endpoints := by
    intro e
    cases e with
    | inl e =>
        exact Or.inr (wiredBoxSwap_horizontal_endpoints L (horizontalFaceX e) e.2)
    | inr e =>
        exact Or.inr (wiredBoxSwap_vertical_endpoints L e.1 (verticalFaceY e))

/-- Reflection preserves the internal rooted Villain cosine expectation. -/
theorem wiredBoxReflection_villainCosExpectation (L : ℕ) (β : ℝ) (hβ : 0 < β)
    (site : SquareFreeVertex L) :
    Villain.villainCosExpectation (wiredBoxGraph L) none β
        ⟨some (site.1.rev, site.2), Option.some_ne_none _⟩ =
      Villain.villainCosExpectation (wiredBoxGraph L) none β
        ⟨some site, Option.some_ne_none _⟩ := by
  simpa [wiredBoxReflectionIsomorphism, wiredSquareReflection_some,
    Villain.rootedVertexEquiv] using
    Villain.villainCosExpectation_rootedAutomorphism (wiredBoxGraph L) none β hβ
      (wiredBoxReflectionIsomorphism L) (by rfl)
      ⟨some site, Option.some_ne_none _⟩

/-- Coordinate swap preserves the internal rooted Villain cosine expectation. -/
theorem wiredBoxSwap_villainCosExpectation (L : ℕ) (β : ℝ) (hβ : 0 < β)
    (site : SquareFreeVertex L) :
    Villain.villainCosExpectation (wiredBoxGraph L) none β
        ⟨some (site.2, site.1), Option.some_ne_none _⟩ =
      Villain.villainCosExpectation (wiredBoxGraph L) none β
        ⟨some site, Option.some_ne_none _⟩ := by
  simpa [wiredBoxSwapIsomorphism, wiredSquareSwap_some,
    Villain.rootedVertexEquiv] using
    Villain.villainCosExpectation_rootedAutomorphism (wiredBoxGraph L) none β hβ
      (wiredBoxSwapIsomorphism L) (by rfl)
      ⟨some site, Option.some_ne_none _⟩

/-- The reflection automorphism preserves the internal normalized rooted Villain measure. -/
theorem wiredBoxReflection_preservesVillainMeasure (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    MeasureTheory.Measure.map
        (Villain.rootedAngleMeasurableEquiv (wiredBoxGraph L) none
          (wiredBoxReflectionIsomorphism L) (by rfl))
        (Villain.rootedVillainMeasure (wiredBoxGraph L) none β hβ) =
      Villain.rootedVillainMeasure (wiredBoxGraph L) none β hβ := by
  exact Villain.rootedVillainMeasure_map_rootedAngleMeasurableEquiv
    (wiredBoxGraph L) none β hβ (wiredBoxReflectionIsomorphism L) (by rfl)

/-- Coordinate swap preserves the internal normalized rooted Villain measure. -/
theorem wiredBoxSwap_preservesVillainMeasure (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    MeasureTheory.Measure.map
        (Villain.rootedAngleMeasurableEquiv (wiredBoxGraph L) none
          (wiredBoxSwapIsomorphism L) (by rfl))
        (Villain.rootedVillainMeasure (wiredBoxGraph L) none β hβ) =
      Villain.rootedVillainMeasure (wiredBoxGraph L) none β hβ := by
  exact Villain.rootedVillainMeasure_map_rootedAngleMeasurableEquiv
    (wiredBoxGraph L) none β hβ (wiredBoxSwapIsomorphism L) (by rfl)

/-- KP Proposition 6.1 stated directly as a cosine integral against the normalized internal
rooted Villain measure (KP §6.1, pp. 33–34). -/
theorem wiredBox_rootedVillainMeasure_eq_kpProposition61 (L : ℕ) (hL : 1 < L)
    (β : ℝ) (hβ : 0 < β) (site : SquareFreeVertex L) :
    (∫ θ : Villain.FreeAngles (WiredVertex L) none,
      Real.cos (θ ⟨some site, Option.some_ne_none _⟩)
        ∂Villain.rootedVillainMeasure (wiredBoxGraph L) none β hβ) =
      igffExpectation (dualBoxGraph L) (dualBoxGraph_connected (by omega)) (1 / β)
        (one_div_pos.mpr hβ) (dualBoxRoot L)
        (kpPrintedLineSourceObservable β site) := by
  rw [Villain.rootedVillainMeasure_cosIntegral_eq_villainCosExpectation]
  exact villainCosExpectation_eq_kpProposition61 hL β hβ site

/-- A cosine lower bound on the right-side nearest-point class extends to every free vertex of
the internal wired square. Its distance profile is expressed by the boundary depth, which is the
root distance minus one (KP Theorem 1.3, p. 4). -/
theorem wiredBox_allFree_villainCosExpectation_bound_of_rightSide
    (L : ℕ) (β C : ℝ) (hβ : 0 < β)
    (hside : ∀ site : SquareFreeVertex L, wiredRightSide L site →
      ((wiredBoundaryDepth L site + 2 : ℝ) ^ (-C / β) ≤
        Villain.villainCosExpectation (wiredBoxGraph L) none β
          ⟨some site, Option.some_ne_none _⟩))
    (site : SquareFreeVertex L) :
    ((wiredBoundaryDepth L site + 2 : ℝ) ^ (-C / β) ≤
      Villain.villainCosExpectation (wiredBoxGraph L) none β
        ⟨some site, Option.some_ne_none _⟩) := by
  rcases exists_wiredRightSide_representative L site with h | h | h | h
  · exact hside site h
  · have hb := hside (site.1.rev, site.2) h
    rw [wiredBoundaryDepth_reflection L site,
      wiredBoxReflection_villainCosExpectation L β hβ site] at hb
    exact hb
  · have hb := hside (site.2, site.1) h
    rw [wiredBoundaryDepth_swap L site,
      wiredBoxSwap_villainCosExpectation L β hβ site] at hb
    exact hb
  · have hb := hside (site.2.rev, site.1) h
    rw [wiredBoundaryDepth_reflection L (site.2, site.1),
      wiredBoundaryDepth_swap L site,
      wiredBoxReflection_villainCosExpectation L β hβ (site.2, site.1),
      wiredBoxSwap_villainCosExpectation L β hβ site] at hb
    exact hb

/-- The same right-side reduction for cosine integrals against the normalized internal Villain
measure. -/
theorem wiredBox_allFree_villainMeasure_bound_of_rightSide
    (L : ℕ) (β C : ℝ) (hβ : 0 < β)
    (hside : ∀ site : SquareFreeVertex L, wiredRightSide L site →
      ((wiredBoundaryDepth L site + 2 : ℝ) ^ (-C / β) ≤
        ∫ θ : Villain.FreeAngles (WiredVertex L) none,
          Real.cos (θ ⟨some site, Option.some_ne_none _⟩)
            ∂Villain.rootedVillainMeasure (wiredBoxGraph L) none β hβ))
    (site : SquareFreeVertex L) :
    ((wiredBoundaryDepth L site + 2 : ℝ) ^ (-C / β) ≤
      ∫ θ : Villain.FreeAngles (WiredVertex L) none,
        Real.cos (θ ⟨some site, Option.some_ne_none _⟩)
          ∂Villain.rootedVillainMeasure (wiredBoxGraph L) none β hβ) := by
  have hside' : ∀ x : SquareFreeVertex L, wiredRightSide L x →
      ((wiredBoundaryDepth L x + 2 : ℝ) ^ (-C / β) ≤
        Villain.villainCosExpectation (wiredBoxGraph L) none β
          ⟨some x, Option.some_ne_none _⟩) := by
    intro x hx
    rw [← Villain.rootedVillainMeasure_cosIntegral_eq_villainCosExpectation
      (wiredBoxGraph L) none β hβ ⟨some x, Option.some_ne_none _⟩]
    exact hside x hx
  have hall := wiredBox_allFree_villainCosExpectation_bound_of_rightSide
    L β C hβ hside' site
  rw [Villain.rootedVillainMeasure_cosIntegral_eq_villainCosExpectation
    (wiredBoxGraph L) none β hβ ⟨some site, Option.some_ne_none _⟩]
  exact hall

/-! Reflection endpoint calculations. -/

end FroehlichSpencer.BKT.Duality

end
