/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Splitting a closed edge field across a contour

If every plaquette meeting a selected edge set contains no nonzero edge outside that set, a
closed field splits into closed inside and outside fields. The statement only uses finite
plaquette boundary sums, so it applies to any edge type and any additive commutative monoid.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

/-- Restrict an edge field to a selected finite edge set, setting it to zero elsewhere. -/
def restrictEdgeField {E A : Type*} [DecidableEq E] [Zero A]
    (S : Finset E) (η : E → A) : E → A :=
  fun e => if e ∈ S then η e else 0

/-- Restrict an edge field to the complement of a selected finite edge set. -/
def restrictEdgeFieldOutside {E A : Type*} [DecidableEq E] [Zero A]
    (S : Finset E) (η : E → A) : E → A :=
  fun e => if e ∈ S then 0 else η e

/-- An edge field is closed for a family of finite plaquette boundaries when its sum on every
boundary vanishes. -/
def edgeFieldClosedOn {E P A : Type*} [AddCommMonoid A]
    (boundary : P → Finset E) (η : E → A) : Prop :=
  ∀ p, ∑ e ∈ boundary p, η e = 0

/-- A closed edge field splits into closed restrictions when every plaquette meeting `S` has all
of its nonzero edges in `S`. -/
theorem edgeFieldClosedOn_restrict_split
    {E P A : Type*} [DecidableEq E] [AddCommMonoid A]
    (boundary : P → Finset E) (η : E → A) (S : Finset E)
    (hclosed : edgeFieldClosedOn boundary η)
    (hcontained : ∀ p, (∃ e ∈ boundary p, e ∈ S) →
      ∀ e ∈ boundary p, η e ≠ 0 → e ∈ S) :
    edgeFieldClosedOn boundary (restrictEdgeField S η) ∧
      edgeFieldClosedOn boundary (restrictEdgeFieldOutside S η) := by
  classical
  constructor
  · intro p
    by_cases hmeet : ∃ e ∈ boundary p, e ∈ S
    · have hsum :
          (∑ e ∈ boundary p, restrictEdgeField S η e) =
            ∑ e ∈ boundary p, η e := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases heS : e ∈ S
        · simp [restrictEdgeField, heS]
        · have hzero : η e = 0 := by
            by_contra hne
            exact heS (hcontained p hmeet e he hne)
          simp [restrictEdgeField, heS, hzero]
      rw [hsum, hclosed p]
    · apply Finset.sum_eq_zero
      intro e he
      have heS : e ∉ S := by
        intro hs
        exact hmeet ⟨e, he, hs⟩
      simp [restrictEdgeField, heS]
  · intro p
    by_cases hmeet : ∃ e ∈ boundary p, e ∈ S
    · apply Finset.sum_eq_zero
      intro e he
      by_cases heS : e ∈ S
      · simp [restrictEdgeFieldOutside, heS]
      · have hzero : η e = 0 := by
          by_contra hne
          exact heS (hcontained p hmeet e he hne)
        simp [restrictEdgeFieldOutside, heS, hzero]
    · have hsum :
          (∑ e ∈ boundary p, restrictEdgeFieldOutside S η e) =
            ∑ e ∈ boundary p, η e := by
        apply Finset.sum_congr rfl
        intro e he
        have heS : e ∉ S := by
          intro hs
          exact hmeet ⟨e, he, hs⟩
        simp [restrictEdgeFieldOutside, heS]
      rw [hsum, hclosed p]

end FroehlichSpencer.BKT.Clock.Peierls

end
