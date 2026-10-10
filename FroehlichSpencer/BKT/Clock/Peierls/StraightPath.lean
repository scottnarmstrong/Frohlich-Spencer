/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.ConfigurationField
public import FroehlichSpencer.BKT.Clock.Peierls.GenericGradient
import Mathlib.Tactic

/-! # Generic path flux and the explicit frame detour -/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Lattice2D

/-- Sum of a group-valued edge field along a horizontal segment, in the positive coordinate
direction. -/
def squareFreeHorizontalSegmentSum {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : Lattice2D.SquareFreeEdge L → G) (y x : ℕ) : ℕ → G
  | 0 => 0
  | r + 1 => squareFreeHorizontalSegmentSum η y x r +
      GenericGradient.squareFreeHorizontalValue η (x + r) y

/-- Sum of a group-valued edge field along a vertical segment, in the positive coordinate
direction. -/
def squareFreeVerticalSegmentSum {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : Lattice2D.SquareFreeEdge L → G) (x y : ℕ) : ℕ → G
  | 0 => 0
  | r + 1 => squareFreeVerticalSegmentSum η x y r +
      GenericGradient.squareFreeVerticalValue η x (y + r)

/-- A graph gradient's horizontal segment sum telescopes to the endpoint difference. -/
theorem squareFreeHorizontalSegmentSum_grad {L : ℕ} {G : Type*} [AddCommGroup G]
    (f : Lattice2D.SquareFreeVertex L → G) (y x r : ℕ)
    (hy : y < L) (hx : x + r < L) :
    squareFreeHorizontalSegmentSum ((squareFreeGraph L).grad f) y x r =
      f (⟨x, by omega⟩, ⟨y, hy⟩) - f (⟨x + r, hx⟩, ⟨y, hy⟩) := by
  induction r with
  | zero =>
      simp [squareFreeHorizontalSegmentSum]
  | succ r ih =>
      have hxr : x + r < L := by omega
      rw [squareFreeHorizontalSegmentSum, ih hxr]
      simp only [GenericGradient.squareFreeHorizontalValue,
        dite_eq_left (by omega : x + r + 1 < L),
        dite_eq_left (by omega : y < L),
        GenericGradient.squareFreeHorizontalEdgeAt, Multigraph.grad, squareFreeGraph]
      abel

/-- A graph gradient's vertical segment sum telescopes to the endpoint difference. -/
theorem squareFreeVerticalSegmentSum_grad {L : ℕ} {G : Type*} [AddCommGroup G]
    (f : Lattice2D.SquareFreeVertex L → G) (x y r : ℕ)
    (hx : x < L) (hy : y + r < L) :
    squareFreeVerticalSegmentSum ((squareFreeGraph L).grad f) x y r =
      f (⟨x, hx⟩, ⟨y, by omega⟩) - f (⟨x, hx⟩, ⟨y + r, hy⟩) := by
  induction r with
  | zero =>
      simp [squareFreeVerticalSegmentSum]
  | succ r ih =>
      have hyr : y + r < L := by omega
      rw [squareFreeVerticalSegmentSum, ih hyr]
      simp only [GenericGradient.squareFreeVerticalValue,
        dite_eq_left (by omega : x < L),
        dite_eq_left (by omega : y + r + 1 < L),
        GenericGradient.squareFreeVerticalEdgeAt, Multigraph.grad, squareFreeGraph]
      abel

/-- The flux along the five explicit axis/frame segments in the detour route. -/
def squareFreeFrameDetourFlux {L : ℕ} {G : Type*} [AddCommGroup G]
    (η : Lattice2D.SquareFreeEdge L → G) (R j k : ℕ) : G :=
  squareFreeHorizontalSegmentSum η 0 0 (j - (k + 3)) +
    squareFreeVerticalSegmentSum η (j - (k + 3)) 0 (k + 3) +
    squareFreeHorizontalSegmentSum η (k + 3) (j - (k + 3)) (2 * (k + 3)) -
    squareFreeVerticalSegmentSum η (j + (k + 3)) 0 (k + 3) +
    squareFreeHorizontalSegmentSum η 0 (j + (k + 3)) (R - (j + (k + 3)))

/-- A closed square field with values in any additive commutative group has the same flux on the
axis path and the explicit frame detour. -/
theorem squareFreeHorizontalSegmentSum_eq_frameDetourFlux_of_closed {L : ℕ}
    {G : Type*} [AddCommGroup G] (η : Lattice2D.SquareFreeEdge L → G)
    (hclosed : GenericGradient.squareFreePlaquetteClosed η) (R j k : ℕ)
    (hleft : k + 3 < j) (hright : k + 3 < R - j)
    (hL : R < L) (hH : k + 3 < L) :
    squareFreeHorizontalSegmentSum η 0 0 R = squareFreeFrameDetourFlux η R j k := by
  have hJ : j + (k + 3) < R := by omega
  have hXcross : j - (k + 3) + 2 * (k + 3) = j + (k + 3) := by omega
  have hX1R : j + (k + 3) + (R - (j + (k + 3))) = R := by omega
  obtain ⟨f, hf⟩ := GenericGradient.squareFreeEdgeField_isGradient η hclosed
  have hη : η = (squareFreeGraph L).grad f := funext fun e => (hf e).symm
  rw [hη]
  unfold squareFreeFrameDetourFlux
  rw [squareFreeHorizontalSegmentSum_grad f 0 0 R (by omega) (by omega),
    squareFreeHorizontalSegmentSum_grad f 0 0 (j - (k + 3)) (by omega) (by omega),
    squareFreeVerticalSegmentSum_grad f (j - (k + 3)) 0 (k + 3) (by omega) (by omega),
    squareFreeHorizontalSegmentSum_grad f (k + 3) (j - (k + 3)) (2 * (k + 3))
      (by omega) (by omega),
    squareFreeVerticalSegmentSum_grad f (j + (k + 3)) 0 (k + 3) (by omega) (by omega),
    squareFreeHorizontalSegmentSum_grad f 0 (j + (k + 3)) (R - (j + (k + 3)))
      (by omega) (by omega)]
  simp only [Nat.zero_add, hXcross, hX1R]
  abel

/-- Specialization of the generic path-flux formula to the clock difference field: its horizontal
segment flux is the initial spin minus the final spin in `ZMod n`. -/
theorem clockConfigurationSegmentSum_eq_endpoints {L n : ℕ} [NeZero n]
    (σ : Lattice2D.SquareFreeVertex L → Fin n) (y x r : ℕ)
    (hy : y < L) (hx : x + r < L) :
    squareFreeHorizontalSegmentSum (clockConfigurationField σ) y x r =
      clockConfigurationZMod σ (⟨x, by omega⟩, ⟨y, hy⟩) -
        clockConfigurationZMod σ (⟨x + r, hx⟩, ⟨y, hy⟩) := by
  exact squareFreeHorizontalSegmentSum_grad (clockConfigurationZMod σ) y x r hy hx

/-- Specialization of the generic path-flux formula to a vertical clock segment. -/
theorem clockConfigurationVerticalSegmentSum_eq_endpoints {L n : ℕ} [NeZero n]
    (σ : Lattice2D.SquareFreeVertex L → Fin n) (x y r : ℕ)
    (hx : x < L) (hy : y + r < L) :
    squareFreeVerticalSegmentSum (clockConfigurationField σ) x y r =
      clockConfigurationZMod σ (⟨x, hx⟩, ⟨y, by omega⟩) -
        clockConfigurationZMod σ (⟨x, hx⟩, ⟨y + r, hy⟩) := by
  exact squareFreeVerticalSegmentSum_grad (clockConfigurationZMod σ) x y r hx hy

end FroehlichSpencer.BKT.Clock.Peierls

end
