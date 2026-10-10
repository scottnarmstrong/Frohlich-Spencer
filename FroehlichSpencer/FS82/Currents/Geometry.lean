/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.Current
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic

/-!
# Euclidean geometry of finite dual links

The carrier is `LambdaStarLinks`.

The coordinate chart is the square-cover
physical embedding into the bumped primal box: dual points gain one in their
integer coordinate and dual intervals retain their base index.

Distances are
computed on the corresponding closed unit segments.
-/

public section

namespace FroehlichSpencer.FS82.Currents

open Cubical
noncomputable section
open Classical

abbrev Point := EuclideanSpace ℝ (Fin 4)

/-- Bumped primal box used for the C1 physical placement of the dual box. -/
@[expose] def bumpedBox (B : Cubical.Box 4) : Cubical.Box 4 :=
  fun i => B i + 1

/-- The unique direction of a dual link, obtained from its degree-one proof. -/
noncomputable def axis {B : Cubical.Box 4} (e : Link B) : Fin 4 :=
  Classical.choose (Finset.card_eq_one.mp (show
    (Cubical.dualCellAxes e.1).card = 1 by
      simpa [Cubical.dualCellDegree] using e.2))

theorem axes_eq_singleton {B : Cubical.Box 4} (e : Link B) :
    Cubical.dualCellAxes e.1 = {axis e} :=
  Classical.choose_spec (Finset.card_eq_one.mp (show
    (Cubical.dualCellAxes e.1).card = 1 by
      simpa [Cubical.dualCellDegree] using e.2))

namespace Link

abbrev axis {B : Cubical.Box 4} (e : Link B) := Currents.axis e

end Link

@[expose] def coordToBumpedAnchor {B : Cubical.Box 4} {i : Fin 4}
    (x : Cubical.DualCoord B i) : Fin (B i + 2) :=
  match x with
  | Sum.inl v => ⟨v.val + 1, by omega⟩
  | Sum.inr t => ⟨t.val, by omega⟩

/-- The lower corner of the unit link in the C1 bumped-box coordinates. -/
@[expose] def base {B : Cubical.Box 4} (e : Link B) :
    Cubical.Anchor 4 (bumpedBox B) :=
  fun i => coordToBumpedAnchor (e.1 i)

namespace Link

abbrev base {B : Cubical.Box 4} (e : Link B) := Currents.base e

end Link

theorem axis_coord_isRight {B : Cubical.Box 4} (e : Link B) :
    (e.1 (axis e)).isRight = true := by
  have hm : axis e ∈ Cubical.dualCellAxes e.1 := by
    rw [axes_eq_singleton]
    simp
  exact (Finset.mem_filter.mp hm).2

theorem axis_coord_exists {B : Cubical.Box 4} (e : Link B) :
    ∃ t : Fin (B (axis e) + 1), e.1 (axis e) = Sum.inr t := by
  cases h : e.1 (axis e) with
  | inl v =>
      have hf : False := by simpa [h] using axis_coord_isRight e
      exact False.elim hf
  | inr t => exact ⟨t, rfl⟩

theorem base_axis_lt {B : Cubical.Box 4} (e : Link B) :
    (base e (axis e)).val < B (axis e) + 1 := by
  obtain ⟨t, ht⟩ := axis_coord_exists e
  simpa [base, ht, coordToBumpedAnchor] using t.isLt

/-- The head vertex of an oriented dual link. -/
@[expose] noncomputable def targetVertex {B : Cubical.Box 4} (e : Link B) :
    Cubical.Anchor 4 (bumpedBox B) :=
  Function.update (base e) (axis e)
    ⟨(base e (axis e)).val + 1, Nat.succ_lt_succ (base_axis_lt e)⟩

@[expose] noncomputable def vertexPoint {B : Cubical.Box 4}
    (v : Cubical.Anchor 4 (bumpedBox B)) : Point :=
  WithLp.toLp 2 fun i : Fin 4 => (v i).val

/-- A point on the oriented unit segment representing a dual link. -/
@[expose] noncomputable def linkPointAt {B : Cubical.Box 4} (e : Link B) (t : ℝ) : Point :=
  WithLp.toLp 2 (Function.update (fun i : Fin 4 => (base e i).val) (axis e) t)

/-- Closed geometric support of a finite dual link. -/
@[expose] def linkSegment {B : Cubical.Box 4} (e : Link B) : Set Point :=
  {x | ∃ t : ℝ,
    (base e (axis e)).val ≤ t ∧ t ≤ (base e (axis e)).val + 1 ∧
      x = linkPointAt e t}

/-- Euclidean distance between two closed dual-link segments. -/
@[expose] noncomputable def linkDistance {B : Cubical.Box 4} (e f : Link B) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ linkSegment e, ∃ y ∈ linkSegment f, r = dist x y}

theorem linkPointAt_base {B : Cubical.Box 4} (e : Link B) :
    linkPointAt e (base e (axis e)).val = vertexPoint (base e) := by
  apply congrArg (WithLp.toLp 2)
  funext i
  by_cases h : i = axis e
  · subst i
    simp
  · simp [Function.update_of_ne h]

theorem linkPointAt_target {B : Cubical.Box 4} (e : Link B) :
    linkPointAt e ((base e (axis e)).val + 1) = vertexPoint (targetVertex e) := by
  apply congrArg (WithLp.toLp 2)
  funext i
  by_cases h : i = axis e
  · subst i
    simp [targetVertex]
  · simp [targetVertex, Function.update_of_ne h]

theorem sourcePoint_mem_linkSegment {B : Cubical.Box 4} (e : Link B) :
    vertexPoint (base e) ∈ linkSegment e := by
  refine ⟨(base e (axis e)).val, le_rfl, ?_, ?_⟩
  · exact_mod_cast Nat.le_add_right (base e (axis e)).val 1
  · rw [← linkPointAt_base]

theorem targetPoint_mem_linkSegment {B : Cubical.Box 4} (e : Link B) :
    vertexPoint (targetVertex e) ∈ linkSegment e := by
  refine ⟨(base e (axis e)).val + 1, ?_, le_rfl, ?_⟩
  · exact_mod_cast Nat.le_add_right (base e (axis e)).val 1
  · rw [← linkPointAt_target]

theorem linkDistance_nonneg {B : Cubical.Box 4} (e f : Link B) :
    0 ≤ linkDistance e f := by
  apply le_csInf
  · refine ⟨dist (vertexPoint (base e)) (vertexPoint (base f)), ?_⟩
    exact ⟨vertexPoint (base e), sourcePoint_mem_linkSegment e,
      vertexPoint (base f), sourcePoint_mem_linkSegment f, rfl⟩
  · rintro r ⟨x, hx, y, hy, rfl⟩
    exact dist_nonneg

theorem linkDistance_le_dist {B : Cubical.Box 4} (e f : Link B)
    {x y : Point} (hx : x ∈ linkSegment e) (hy : y ∈ linkSegment f) :
    linkDistance e f ≤ dist x y := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨a, ha, b, hb, rfl⟩
    exact dist_nonneg
  · exact ⟨x, hx, y, hy, rfl⟩

theorem linkDistance_symm {B : Cubical.Box 4} (e f : Link B) :
    linkDistance e f = linkDistance f e := by
  unfold linkDistance
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨y, hy, x, hx, by rw [dist_comm]⟩
  · rintro ⟨y, hy, x, hx, rfl⟩
    exact ⟨x, hx, y, hy, by rw [dist_comm]⟩

theorem linkDistance_zero_of_shared_vertex {B : Cubical.Box 4}
    (e f : Link B) (v : Cubical.Anchor 4 (bumpedBox B))
    (he : v = base e ∨ v = targetVertex e)
    (hf : v = base f ∨ v = targetVertex f) :
    linkDistance e f = 0 := by
  have hmemE : vertexPoint v ∈ linkSegment e := by
    rcases he with h | h
    · subst v
      exact sourcePoint_mem_linkSegment e
    · subst v
      exact targetPoint_mem_linkSegment e
  have hmemF : vertexPoint v ∈ linkSegment f := by
    rcases hf with h | h
    · subst v
      exact sourcePoint_mem_linkSegment f
    · subst v
      exact targetPoint_mem_linkSegment f
  have hle := linkDistance_le_dist e f hmemE hmemF
  rw [dist_self] at hle
  exact le_antisymm hle (linkDistance_nonneg e f)


end

end FroehlichSpencer.FS82.Currents

end
