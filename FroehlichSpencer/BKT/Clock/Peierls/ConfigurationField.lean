/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.Gradient
public import FroehlichSpencer.BKT.Clock.Peierls.EnergyGap
public import FroehlichSpencer.BKT.Clock.Compact.TwoPoint
import Mathlib.Tactic

/-! # Difference fields of finite clock configurations -/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Clock.Compact

/-- Interpret each `Fin n` clock state as its residue in `ZMod n`. -/
def clockConfigurationZMod {L n : ℕ} [NeZero n]
    (σ : Lattice2D.SquareFreeVertex L → Fin n) :
    Lattice2D.SquareFreeVertex L → ZMod n :=
  fun v => ZMod.finEquiv n (σ v)

/-- The oriented clock difference field, using the source-minus-target graph convention. -/
def clockConfigurationField {L n : ℕ} [NeZero n]
    (σ : Lattice2D.SquareFreeVertex L → Fin n) :
    Lattice2D.SquareFreeEdge L → ZMod n :=
  (squareFreeGraph L).grad (clockConfigurationZMod σ)

/-- Edges on which the clock configuration changes. -/
def clockConfigurationBadEdges {L n : ℕ} [NeZero n]
    (σ : Lattice2D.SquareFreeVertex L → Fin n) :
    Finset (Lattice2D.SquareFreeEdge L) :=
  Finset.univ.filter fun e => clockConfigurationField σ e ≠ 0

/-- The difference field of any clock configuration has zero circulation around every unit
plaquette. -/
theorem clockConfigurationField_closed {L n : ℕ} [NeZero n]
    (σ : Lattice2D.SquareFreeVertex L → Fin n) :
    squareFreePlaquetteClosed (clockConfigurationField σ) := by
  intro i j hi hj
  simp only [squareFreeHorizontalValue, squareFreeVerticalValue,
    dite_eq_left (by omega : i + 1 < L), dite_eq_left (by omega : j < L),
    dite_eq_left (by omega : i < L), dite_eq_left (by omega : j + 1 < L),
    squareFreeHorizontalEdgeAt, squareFreeVerticalEdgeAt,
    clockConfigurationField, Multigraph.grad, squareFreeGraph]
  abel

/-- The clock difference is nonzero exactly when the endpoint clock states differ. -/
theorem clockConfigurationField_ne_zero_iff {L n : ℕ} [NeZero n]
    (σ : Lattice2D.SquareFreeVertex L → Fin n) (e : Lattice2D.SquareFreeEdge L) :
    clockConfigurationField σ e ≠ 0 ↔
      σ ((squareFreeGraph L).src e) ≠ σ ((squareFreeGraph L).tgt e) := by
  unfold clockConfigurationField Multigraph.grad clockConfigurationZMod
  rw [sub_ne_zero]
  exact (ZMod.finEquiv n).injective.ne_iff

end FroehlichSpencer.BKT.Clock.Peierls

end
