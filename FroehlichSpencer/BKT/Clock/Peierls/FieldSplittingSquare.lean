/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.ContourField
public import FroehlichSpencer.BKT.Clock.Peierls.GenericGradient
import Mathlib.Tactic

/-! # Splitting a closed square edge field across a saturated edge set

For each unit square, if it meets the selected set then every nonzero boundary edge lies in the
set. The restricted field and its complement therefore separately have zero square circulation.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls.GenericGradient

open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Clock.Peierls

/-- The four positively oriented edges in the boundary of a coordinate plaquette. -/
def squareFreePlaquetteEdges {L : ℕ} (i j : ℕ)
    (hi : i + 1 < L) (hj : j + 1 < L) : Finset (SquareFreeEdge L) :=
  insert (squareFreeHorizontalEdgeAt i j hi (by omega))
    (insert (squareFreeVerticalEdgeAt (i + 1) j (by omega) hj)
      (insert (squareFreeVerticalEdgeAt i j (by omega) hj)
        {squareFreeHorizontalEdgeAt i (j + 1) hi (by omega)}))

/-- Local plaquette saturation: any plaquette meeting `S` has every nonzero boundary field value
supported in `S`. -/
def squareFreePlaquetteSaturated {L : ℕ} {G : Type*} [Zero G]
    (η : SquareFreeEdge L → G) (S : Finset (SquareFreeEdge L)) : Prop :=
  ∀ i j (hi : i + 1 < L) (hj : j + 1 < L),
    (∃ e ∈ squareFreePlaquetteEdges i j hi hj, e ∈ S) →
      ∀ e ∈ squareFreePlaquetteEdges i j hi hj, η e = 0 ∨ e ∈ S

private theorem horizontalValue_restrict_eq {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (S : Finset (SquareFreeEdge L)) (i j : ℕ)
    (hi : i + 1 < L) (hj : j < L)
    (hη : η (squareFreeHorizontalEdgeAt i j hi hj) = 0 ∨
      squareFreeHorizontalEdgeAt i j hi hj ∈ S) :
    squareFreeHorizontalValue (restrictEdgeField S η) i j =
      squareFreeHorizontalValue η i j := by
  simp only [squareFreeHorizontalValue, dite_eq_left hi, dite_eq_left hj]
  rcases hη with hzero | hmem
  · by_cases hS : squareFreeHorizontalEdgeAt i j hi hj ∈ S
    · simp [restrictEdgeField, hS]
    · simp [restrictEdgeField, hS, hzero]
  · simp [restrictEdgeField, hmem]

private theorem verticalValue_restrict_eq {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (S : Finset (SquareFreeEdge L)) (i j : ℕ)
    (hi : i < L) (hj : j + 1 < L)
    (hη : η (squareFreeVerticalEdgeAt i j hi hj) = 0 ∨
      squareFreeVerticalEdgeAt i j hi hj ∈ S) :
    squareFreeVerticalValue (restrictEdgeField S η) i j =
      squareFreeVerticalValue η i j := by
  simp only [squareFreeVerticalValue, dite_eq_left hi, dite_eq_left hj]
  rcases hη with hzero | hmem
  · by_cases hS : squareFreeVerticalEdgeAt i j hi hj ∈ S
    · simp [restrictEdgeField, hS]
    · simp [restrictEdgeField, hS, hzero]
  · simp [restrictEdgeField, hmem]

private theorem horizontalValue_restrict_zero {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (S : Finset (SquareFreeEdge L)) (i j : ℕ)
    (hi : i + 1 < L) (hj : j < L)
    (hnot : squareFreeHorizontalEdgeAt i j hi hj ∉ S) :
    squareFreeHorizontalValue (restrictEdgeField S η) i j = 0 := by
  simp only [squareFreeHorizontalValue, dite_eq_left hi, dite_eq_left hj]
  simp [restrictEdgeField, hnot]

private theorem verticalValue_restrict_zero {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (S : Finset (SquareFreeEdge L)) (i j : ℕ)
    (hi : i < L) (hj : j + 1 < L)
    (hnot : squareFreeVerticalEdgeAt i j hi hj ∉ S) :
    squareFreeVerticalValue (restrictEdgeField S η) i j = 0 := by
  simp only [squareFreeVerticalValue, dite_eq_left hi, dite_eq_left hj]
  simp [restrictEdgeField, hnot]

private theorem horizontalValue_outside_eq {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (S : Finset (SquareFreeEdge L)) (i j : ℕ)
    (hi : i + 1 < L) (hj : j < L)
    (hnot : squareFreeHorizontalEdgeAt i j hi hj ∉ S) :
    squareFreeHorizontalValue (restrictEdgeFieldOutside S η) i j =
      squareFreeHorizontalValue η i j := by
  simp only [squareFreeHorizontalValue, dite_eq_left hi, dite_eq_left hj]
  simp [restrictEdgeFieldOutside, hnot]

private theorem verticalValue_outside_eq {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (S : Finset (SquareFreeEdge L)) (i j : ℕ)
    (hi : i < L) (hj : j + 1 < L)
    (hnot : squareFreeVerticalEdgeAt i j hi hj ∉ S) :
    squareFreeVerticalValue (restrictEdgeFieldOutside S η) i j =
      squareFreeVerticalValue η i j := by
  simp only [squareFreeVerticalValue, dite_eq_left hi, dite_eq_left hj]
  simp [restrictEdgeFieldOutside, hnot]

private theorem horizontalValue_outside_zero_of_saturated {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (S : Finset (SquareFreeEdge L)) (i j : ℕ)
    (hi : i + 1 < L) (hj : j < L)
    (hη : η (squareFreeHorizontalEdgeAt i j hi hj) = 0 ∨
      squareFreeHorizontalEdgeAt i j hi hj ∈ S) :
    squareFreeHorizontalValue (restrictEdgeFieldOutside S η) i j = 0 := by
  simp only [squareFreeHorizontalValue, dite_eq_left hi, dite_eq_left hj]
  rcases hη with hzero | hmem
  · by_cases hS : squareFreeHorizontalEdgeAt i j hi hj ∈ S
    · simp [restrictEdgeFieldOutside, hS]
    · simp [restrictEdgeFieldOutside, hS, hzero]
  · simp [restrictEdgeFieldOutside, hmem]

private theorem verticalValue_outside_zero_of_saturated {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : SquareFreeEdge L → G) (S : Finset (SquareFreeEdge L)) (i j : ℕ)
    (hi : i < L) (hj : j + 1 < L)
    (hη : η (squareFreeVerticalEdgeAt i j hi hj) = 0 ∨
      squareFreeVerticalEdgeAt i j hi hj ∈ S) :
    squareFreeVerticalValue (restrictEdgeFieldOutside S η) i j = 0 := by
  simp only [squareFreeVerticalValue, dite_eq_left hi, dite_eq_left hj]
  rcases hη with hzero | hmem
  · by_cases hS : squareFreeVerticalEdgeAt i j hi hj ∈ S
    · simp [restrictEdgeFieldOutside, hS]
    · simp [restrictEdgeFieldOutside, hS, hzero]
  · simp [restrictEdgeFieldOutside, hmem]

/-- A plaquette-closed field splits into two plaquette-closed fields whenever every plaquette
meeting the selected set has all its nonzero boundary edges in that set. -/
theorem squareFreePlaquetteClosed_restrict_split
    {L : ℕ} {G : Type*} [AddCommGroup G] (η : SquareFreeEdge L → G)
    (S : Finset (SquareFreeEdge L))
    (hclosed : squareFreePlaquetteClosed η)
    (hsaturated : squareFreePlaquetteSaturated η S) :
    squareFreePlaquetteClosed (restrictEdgeField S η) ∧
      squareFreePlaquetteClosed (restrictEdgeFieldOutside S η) := by
  classical
  constructor
  · intro i j hi hj
    let eBottom := squareFreeHorizontalEdgeAt i j hi (by omega)
    let eRight := squareFreeVerticalEdgeAt (i + 1) j (by omega) hj
    let eLeft := squareFreeVerticalEdgeAt i j (by omega) hj
    let eTop := squareFreeHorizontalEdgeAt i (j + 1) hi (by omega)
    by_cases hmeet : ∃ e ∈ squareFreePlaquetteEdges i j hi hj, e ∈ S
    · have hsat := hsaturated i j hi hj hmeet
      have hb := hsat eBottom (by simp [squareFreePlaquetteEdges, eBottom])
      have hr := hsat eRight (by simp [squareFreePlaquetteEdges, eRight])
      have hl := hsat eLeft (by simp [squareFreePlaquetteEdges, eLeft])
      have ht := hsat eTop (by simp [squareFreePlaquetteEdges, eTop])
      have hbval : squareFreeHorizontalValue (restrictEdgeField S η) i j =
          squareFreeHorizontalValue η i j := by
        exact horizontalValue_restrict_eq η S i j hi (by omega) (by simpa [eBottom] using hb)
      have hrval : squareFreeVerticalValue (restrictEdgeField S η) (i + 1) j =
          squareFreeVerticalValue η (i + 1) j := by
        exact verticalValue_restrict_eq η S (i + 1) j (by omega) hj
          (by simpa [eRight] using hr)
      have hlval : squareFreeVerticalValue (restrictEdgeField S η) i j =
          squareFreeVerticalValue η i j := by
        exact verticalValue_restrict_eq η S i j (by omega) hj
          (by simpa [eLeft] using hl)
      have htval : squareFreeHorizontalValue (restrictEdgeField S η) i (j + 1) =
          squareFreeHorizontalValue η i (j + 1) := by
        exact horizontalValue_restrict_eq η S i (j + 1) hi (by omega)
          (by simpa [eTop] using ht)
      rw [hbval, hrval, hlval, htval]
      exact hclosed i j hi hj
    · have hbnot : eBottom ∉ S := by
        intro hS
        exact hmeet ⟨eBottom, by simp [squareFreePlaquetteEdges, eBottom], hS⟩
      have hrnot : eRight ∉ S := by
        intro hS
        exact hmeet ⟨eRight, by simp [squareFreePlaquetteEdges, eRight], hS⟩
      have hlnot : eLeft ∉ S := by
        intro hS
        exact hmeet ⟨eLeft, by simp [squareFreePlaquetteEdges, eLeft], hS⟩
      have htnot : eTop ∉ S := by
        intro hS
        exact hmeet ⟨eTop, by simp [squareFreePlaquetteEdges, eTop], hS⟩
      have hbval : squareFreeHorizontalValue (restrictEdgeField S η) i j = 0 :=
        horizontalValue_restrict_zero η S i j hi (by omega) (by simpa [eBottom] using hbnot)
      have hrval : squareFreeVerticalValue (restrictEdgeField S η) (i + 1) j = 0 :=
        verticalValue_restrict_zero η S (i + 1) j (by omega) hj (by simpa [eRight] using hrnot)
      have hlval : squareFreeVerticalValue (restrictEdgeField S η) i j = 0 :=
        verticalValue_restrict_zero η S i j (by omega) hj (by simpa [eLeft] using hlnot)
      have htval : squareFreeHorizontalValue (restrictEdgeField S η) i (j + 1) = 0 :=
        horizontalValue_restrict_zero η S i (j + 1) hi (by omega)
          (by simpa [eTop] using htnot)
      rw [hbval, hrval, hlval, htval]
  · intro i j hi hj
    let eBottom := squareFreeHorizontalEdgeAt i j hi (by omega)
    let eRight := squareFreeVerticalEdgeAt (i + 1) j (by omega) hj
    let eLeft := squareFreeVerticalEdgeAt i j (by omega) hj
    let eTop := squareFreeHorizontalEdgeAt i (j + 1) hi (by omega)
    by_cases hmeet : ∃ e ∈ squareFreePlaquetteEdges i j hi hj, e ∈ S
    · have hsat := hsaturated i j hi hj hmeet
      have hb := hsat eBottom (by simp [squareFreePlaquetteEdges, eBottom])
      have hr := hsat eRight (by simp [squareFreePlaquetteEdges, eRight])
      have hl := hsat eLeft (by simp [squareFreePlaquetteEdges, eLeft])
      have ht := hsat eTop (by simp [squareFreePlaquetteEdges, eTop])
      have hbval : squareFreeHorizontalValue (restrictEdgeFieldOutside S η) i j = 0 :=
        horizontalValue_outside_zero_of_saturated η S i j hi (by omega)
          (by simpa [eBottom] using hb)
      have hrval : squareFreeVerticalValue (restrictEdgeFieldOutside S η) (i + 1) j = 0 := by
        exact verticalValue_outside_zero_of_saturated η S (i + 1) j (by omega) hj
          (by simpa [eRight] using hr)
      have hlval : squareFreeVerticalValue (restrictEdgeFieldOutside S η) i j = 0 := by
        exact verticalValue_outside_zero_of_saturated η S i j (by omega) hj
          (by simpa [eLeft] using hl)
      have htval : squareFreeHorizontalValue (restrictEdgeFieldOutside S η) i (j + 1) = 0 := by
        exact horizontalValue_outside_zero_of_saturated η S i (j + 1) hi (by omega)
          (by simpa [eTop] using ht)
      rw [hbval, hrval, hlval, htval]
    · have hbnot : eBottom ∉ S := by
        intro hS
        exact hmeet ⟨eBottom, by simp [squareFreePlaquetteEdges, eBottom], hS⟩
      have hrnot : eRight ∉ S := by
        intro hS
        exact hmeet ⟨eRight, by simp [squareFreePlaquetteEdges, eRight], hS⟩
      have hlnot : eLeft ∉ S := by
        intro hS
        exact hmeet ⟨eLeft, by simp [squareFreePlaquetteEdges, eLeft], hS⟩
      have htnot : eTop ∉ S := by
        intro hS
        exact hmeet ⟨eTop, by simp [squareFreePlaquetteEdges, eTop], hS⟩
      have hbval : squareFreeHorizontalValue (restrictEdgeFieldOutside S η) i j =
          squareFreeHorizontalValue η i j :=
        horizontalValue_outside_eq η S i j hi (by omega) (by simpa [eBottom] using hbnot)
      have hrval : squareFreeVerticalValue (restrictEdgeFieldOutside S η) (i + 1) j =
          squareFreeVerticalValue η (i + 1) j :=
        verticalValue_outside_eq η S (i + 1) j (by omega) hj (by simpa [eRight] using hrnot)
      have hlval : squareFreeVerticalValue (restrictEdgeFieldOutside S η) i j =
          squareFreeVerticalValue η i j :=
        verticalValue_outside_eq η S i j (by omega) hj (by simpa [eLeft] using hlnot)
      have htval : squareFreeHorizontalValue (restrictEdgeFieldOutside S η) i (j + 1) =
          squareFreeHorizontalValue η i (j + 1) :=
        horizontalValue_outside_eq η S i (j + 1) hi (by omega) (by simpa [eTop] using htnot)
      rw [hbval, hrval, hlval, htval]
      exact hclosed i j hi hj

end FroehlichSpencer.BKT.Clock.Peierls.GenericGradient

end
