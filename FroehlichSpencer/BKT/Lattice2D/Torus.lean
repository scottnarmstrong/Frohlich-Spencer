/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Internal square tori

The torus carrier is `(ZMod n) × (ZMod n)`. Each vertex contributes one
rightward and one upward edge, so every unoriented nearest-neighbour edge is
represented exactly once when `n ≥ 3`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Lattice2D

/-- Vertices of the discrete square torus of side length `n`. -/
abbrev TorusVertex (n : ℕ) := ZMod n × ZMod n

/-- A torus edge is based at a vertex and points either right or up. -/
abbrev TorusEdge (n : ℕ) := TorusVertex n × Bool

/-- The right or upward unit step on a discrete square torus. -/
def torusStep (n : ℕ) (direction : Bool) (p : TorusVertex n) : TorusVertex n :=
  if direction then (p.1, p.2 + 1) else (p.1 + 1, p.2)

/-- The oriented nearest-neighbour multigraph on the square torus. Each edge
is represented once by its initial vertex and its right/up direction. -/
def torusGraph (n : ℕ) (hn : 2 < n) : Multigraph (TorusVertex n) (TorusEdge n) := by
  letI : NeZero n := ⟨by omega⟩
  exact {
    src := Prod.fst
    tgt := fun e => torusStep n e.2 e.1
    src_ne_tgt := by
      intro e he
      rcases e with ⟨⟨x, y⟩, direction⟩
      cases direction with
      | false =>
        have hx : x = x + 1 := congrArg Prod.fst he
        have hx' : x + 0 = x + 1 := by simpa using hx
        have hz : (0 : ZMod n) = 1 := add_left_cancel hx'
        have hone : (1 : ZMod n) = 0 := hz.symm
        have hcast : ((1 : ℕ) : ZMod n) = 0 := by simpa using hone
        have hdiv : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp hcast
        have hnle : n ≤ 1 := Nat.le_of_dvd (by omega) hdiv
        omega
      | true =>
        have hy : y = y + 1 := congrArg Prod.snd he
        have hy' : y + 0 = y + 1 := by simpa using hy
        have hz : (0 : ZMod n) = 1 := add_left_cancel hy'
        have hone : (1 : ZMod n) = 0 := hz.symm
        have hcast : ((1 : ℕ) : ZMod n) = 0 := by simpa using hone
        have hdiv : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp hcast
        have hnle : n ≤ 1 := Nat.le_of_dvd (by omega) hdiv
        omega
  }

@[simp]
theorem torusGraph_src (n : ℕ) (hn : 2 < n) (e : TorusEdge n) :
    (torusGraph n hn).src e = e.1 := rfl

@[simp]
theorem torusGraph_tgt (n : ℕ) (hn : 2 < n) (e : TorusEdge n) :
    (torusGraph n hn).tgt e = torusStep n e.2 e.1 := rfl

/-- A rightward step is an edge of the torus graph. -/
theorem torus_right_adj (n : ℕ) (hn : 2 < n) (x y : ZMod n) :
    (torusGraph n hn).toSimpleGraph.Adj (x, y) (x + 1, y) := by
  have hne : (x, y) ≠ (x + 1, y) := by
    intro h
    exact (torusGraph n hn).src_ne_tgt ((x, y), false) (by simpa [torusStep] using h)
  change (x, y) ≠ (x + 1, y) ∧
    ((torusGraph n hn).Adj (x, y) (x + 1, y) ∨
      (torusGraph n hn).Adj (x + 1, y) (x, y))
  exact ⟨hne, Or.inl ⟨((x, y), false), Or.inl ⟨rfl, rfl⟩⟩⟩

/-- An upward step is an edge of the torus graph. -/
theorem torus_up_adj (n : ℕ) (hn : 2 < n) (x y : ZMod n) :
    (torusGraph n hn).toSimpleGraph.Adj (x, y) (x, y + 1) := by
  have hne : (x, y) ≠ (x, y + 1) := by
    intro h
    exact (torusGraph n hn).src_ne_tgt ((x, y), true) (by simpa [torusStep] using h)
  change (x, y) ≠ (x, y + 1) ∧
    ((torusGraph n hn).Adj (x, y) (x, y + 1) ∨
      (torusGraph n hn).Adj (x, y + 1) (x, y))
  exact ⟨hne, Or.inl ⟨((x, y), true), Or.inl ⟨rfl, rfl⟩⟩⟩

/-- A path which takes `k` successive rightward torus edges. -/
def torusRightWalk (n : ℕ) (hn : 2 < n) (x y : ZMod n) :
    (k : ℕ) → (torusGraph n hn).toSimpleGraph.Walk (x, y) (x + k, y)
  | 0 => by simpa using (SimpleGraph.Walk.nil : (torusGraph n hn).toSimpleGraph.Walk (x, y) (x, y))
  | k + 1 => by
      have hend : (x + 1) + k = x + (k + 1) := by ring
      simp only [Nat.cast_succ]
      rw [← hend]
      exact SimpleGraph.Walk.cons (torus_right_adj n hn x y)
        (torusRightWalk n hn (x + 1) y k)

/-- A path which takes `k` successive upward torus edges. -/
def torusUpWalk (n : ℕ) (hn : 2 < n) (x y : ZMod n) :
    (k : ℕ) → (torusGraph n hn).toSimpleGraph.Walk (x, y) (x, y + k)
  | 0 => by simpa using (SimpleGraph.Walk.nil : (torusGraph n hn).toSimpleGraph.Walk (x, y) (x, y))
  | k + 1 => by
      have hend : (y + 1) + k = y + (k + 1) := by ring
      simp only [Nat.cast_succ]
      rw [← hend]
      exact SimpleGraph.Walk.cons (torus_up_adj n hn x y)
        (torusUpWalk n hn x (y + 1) k)

/-- The right/up torus graph is connected for side lengths at least three. -/
theorem torusGraph_connected (n : ℕ) (hn : 2 < n) [NeZero n] :
    (torusGraph n hn).Connected := by
  apply (torusGraph n hn).toSimpleGraph.connected_iff_exists_forall_reachable.mpr
  refine ⟨(0, 0), fun p => ?_⟩
  rcases p with ⟨x, y⟩
  have hright : (torusGraph n hn).toSimpleGraph.Reachable (0, 0) (x, 0) := by
    have hw := (torusRightWalk n hn 0 0 x.val).reachable
    simpa [ZMod.natCast_zmod_val] using hw
  have hup : (torusGraph n hn).toSimpleGraph.Reachable (x, 0) (x, y) := by
    have hw := (torusUpWalk n hn x 0 y.val).reachable
    simpa [ZMod.natCast_zmod_val] using hw
  exact hright.trans hup

/-- The real dipole source with `+1` at `p` and `-1` at `q`. -/
def dipole {V : Type*} [DecidableEq V] (p q : V) : V → ℝ :=
  fun v => (if v = p then 1 else 0) - (if v = q then 1 else 0)

/-- The unit point source at `p`. -/
def deltaAt {V : Type*} [DecidableEq V] (p : V) : V → ℝ :=
  fun v => if v = p then 1 else 0

/-- A point source has total mass one. -/
theorem sum_deltaAt_eq_one {V : Type*} [Fintype V] [DecidableEq V] (p : V) :
    ∑ v, deltaAt p v = 1 := by
  classical
  simp [deltaAt]

/-- Pairing against a point source evaluates the other function. -/
theorem pairing_deltaAt_left {V : Type*} [Fintype V] [DecidableEq V]
    (p : V) (f : V → ℝ) :
    Multigraph.pairing (deltaAt p) f = f p := by
  classical
  simp [Multigraph.pairing, deltaAt]

/-- A dipole source always has total mass zero. -/
theorem sum_dipole_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (p q : V) : ∑ v, dipole p q v = 0 := by
  simp [dipole, Finset.sum_sub_distrib]

end FroehlichSpencer.BKT.Lattice2D

end
