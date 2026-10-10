/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.SquareFree
public import FroehlichSpencer.BKT.Lattice2D.Torus
public import FroehlichSpencer.BKT.Lattice2D.LogLowerBound
public import FroehlichSpencer.BKT.Surface.SquareFree
public import FroehlichSpencer.BKT.Surface.SquarePeriodic
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
public import FroehlichSpencer.BKT.Potential.Transport
public import FroehlichSpencer.BKT.Bridge.LogBoundTransport

/-!
# Canonical equivalences for free and periodic square carriers

The square domains list lexicographically sorted endpoint pairs.

This
module classifies those pairs as positive coordinate steps and constructs
isomorphisms to the internal oriented carriers.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

open Multigraph

/--
Every  free-square edge is the positive horizontal or vertical
unit step determined by its lexicographically ordered endpoints (KP p. 2).
-/
theorem squareFreeEdge_classification {L : ℕ} (e : SquareFreeEdge L) :
    (e.1.1.2 = e.1.2.2 ∧ e.1.1.1.val + 1 = e.1.2.1.val) ∨
      (e.1.1.1 = e.1.2.1 ∧ e.1.1.2.val + 1 = e.1.2.2.val) := by
  rcases e with ⟨⟨p, q⟩, hlex, hpair⟩
  change (p.2 = q.2 ∧ p.1.val + 1 = q.1.val) ∨
    (p.1 = q.1 ∧ p.2.val + 1 = q.2.val)
  let dx : ℤ := |(p.1.val : ℤ) - q.1.val|
  let dy : ℤ := |(p.2.val : ℤ) - q.2.val|
  have hzeroMem : (0 : ℤ) ∈ ({dx, dy} : Finset ℤ) := by
    dsimp [dx, dy]
    rw [hpair]
    simp
  have honeMem : (1 : ℤ) ∈ ({dx, dy} : Finset ℤ) := by
    dsimp [dx, dy]
    rw [hpair]
    simp
  have hzero : dx = 0 ∨ dy = 0 := by
    rcases (show 0 = dx ∨ 0 = dy by simpa using hzeroMem) with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hone : dx = 1 ∨ dy = 1 := by
    rcases (show 1 = dx ∨ 1 = dy by simpa using honeMem) with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hlex' : p.1 < q.1 ∨ p.1 = q.1 ∧ p.2 < q.2 := by
    simpa only [Prod.Lex.toLex_lt_toLex] using hlex
  rcases hzero with hx0 | hy0 <;> rcases hone with hx1 | hy1
  · dsimp [dx] at hx0 hx1
    omega
  · right
    have hxyval : p.1.val = q.1.val := by
      have h := (abs_eq_zero.mp (by simpa [dx] using hx0 :
        |(p.1.val : ℤ) - q.1.val| = 0))
      omega
    have hxy : p.1 = q.1 := Fin.ext hxyval
    have hylt : p.2 < q.2 := by
      rcases hlex' with h | ⟨h, hlt⟩
      · have : p.1 < q.1 := h
        rw [hxy] at this
        exact (lt_irrefl _ this).elim
      · exact hlt
    have hdy : |(p.2.val : ℤ) - q.2.val| = 1 := by
      simpa [dy] using hy1
    have hvals : p.2.val + 1 = q.2.val := by
      have hltv : (p.2.val : ℤ) < q.2.val := by exact_mod_cast Fin.lt_def.mp hylt
      have harg : (p.2.val : ℤ) - q.2.val ≤ 0 := by omega
      rw [abs_of_nonpos harg] at hdy
      omega
    exact ⟨hxy, hvals⟩
  · left
    have hdyval : p.2.val = q.2.val := by
      have h := (abs_eq_zero.mp (by simpa [dy] using hy0 :
        |(p.2.val : ℤ) - q.2.val| = 0))
      omega
    have hdy0 : p.2 = q.2 := Fin.ext hdyval
    have hxlt : p.1 < q.1 := by
      rcases hlex' with h | ⟨h, hlt⟩
      · exact h
      · have : p.1 = q.1 := h
        have hvals : p.1.val = q.1.val := congrArg Fin.val this
        have hdx : |(p.1.val : ℤ) - q.1.val| = 1 := by
          simpa [dx] using hx1
        rw [hvals, sub_self] at hdx
        norm_num at hdx
    have hxabs : |(p.1.val : ℤ) - q.1.val| = 1 := by
      simpa [dx] using hx1
    have hxvals : p.1.val + 1 = q.1.val := by
      have hltv : (p.1.val : ℤ) < q.1.val := by exact_mod_cast Fin.lt_def.mp hxlt
      have harg : (p.1.val : ℤ) - q.1.val ≤ 0 := by omega
      rw [abs_of_nonpos harg] at hxabs
      omega
    exact ⟨hdy0, hxvals⟩
  · dsimp [dy] at hy0 hy1
    omega

/--
Convert a positive coordinate step to the sorted-pair edge carrier.
-/
def squareFreeEdgeOfInternal (L : ℕ) :
    Lattice2D.SquareFreeEdge L → SquareFreeEdge L
  | .inl e => by
      let i := e.1.1
      let j := e.2
      let i' : Fin L := ⟨i.val + 1, e.1.2⟩
      refine ⟨((i, j), (i', j)), ?_⟩
      constructor
      · apply Prod.Lex.toLex_lt_toLex.mpr
        left
        exact Fin.lt_def.mpr (by dsimp [i']; omega)
      · have hdx : |(i.val : ℤ) - i'.val| = 1 := by
          dsimp [i']
          ring_nf
          norm_num
        apply Finset.ext
        intro z
        simp [hdx, or_comm]
  | .inr e => by
      let i := e.1
      let j := e.2.1
      let j' : Fin L := ⟨j.val + 1, e.2.2⟩
      refine ⟨((i, j), (i, j')), ?_⟩
      constructor
      · apply Prod.Lex.toLex_lt_toLex.mpr
        right
        constructor
        · rfl
        · exact Fin.lt_def.mpr (by dsimp [j']; omega)
      · have hdy : |(j.val : ℤ) - j'.val| = 1 := by
          dsimp [j']
          ring_nf
          norm_num
        apply Finset.ext
        intro z
        simp [hdy]

/--
Read a  free-square edge as its canonical positive coordinate step.
-/
def squareFreeEdgeToInternal {L : ℕ} (e : SquareFreeEdge L) :
    Lattice2D.SquareFreeEdge L := by
  by_cases hh : e.1.1.2 = e.1.2.2
  · exact .inl (⟨e.1.1.1, by
      rcases squareFreeEdge_classification e with h | h
      · have hq := e.1.2.1.isLt
        omega
      · have hval := congrArg Fin.val hh
        omega⟩, e.1.1.2)
  · exact .inr (e.1.1.1, ⟨e.1.1.2, by
      rcases squareFreeEdge_classification e with h | h
      · exact (hh h.1).elim
      · have hq := e.1.2.2.isLt
        omega⟩)

/--
The and internal free-square edge carriers are equivalent.
-/
def squareFreeEdgeEquiv (L : ℕ) :
    Lattice2D.SquareFreeEdge L ≃ SquareFreeEdge L where
  toFun := squareFreeEdgeOfInternal L
  invFun := squareFreeEdgeToInternal
  left_inv e := by
    cases e with
    | inl e =>
        simp [squareFreeEdgeToInternal, squareFreeEdgeOfInternal]
    | inr e =>
        have hneq : e.2.1 ≠ (⟨e.2.1.val + 1, e.2.2⟩ : Fin L) := by
          intro h
          have hv : e.2.1.val = e.2.1.val + 1 := by
            simpa using congrArg Fin.val h
          omega
        simp [squareFreeEdgeToInternal, squareFreeEdgeOfInternal, hneq]
  right_inv e := by
    apply Subtype.ext
    by_cases hh : e.1.1.2 = e.1.2.2
    · have h := squareFreeEdge_classification e
      rcases h with h | h
      · simp only [squareFreeEdgeToInternal, dite_eq_left hh, squareFreeEdgeOfInternal]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact Fin.ext h.2
          · exact h.1
      · have hval := congrArg Fin.val hh
        omega
    · have h := squareFreeEdge_classification e
      rcases h with h | h
      · exact (hh h.1).elim
      · simp only [squareFreeEdgeToInternal, dite_eq_right hh, squareFreeEdgeOfInternal]
        apply Prod.ext
        · apply Prod.ext
          · rfl
          · rfl
        · apply Prod.ext
          · exact h.1
          · exact Fin.ext h.2

/--
The free-square graph and its positive-step model are isomorphic.
-/
def squareFreeGraphIsomorphism (L : ℕ) :
    Multigraph.Isomorphism (Lattice2D.squareFreeGraph L) (squareFree L) where
  vertices := Equiv.refl _
  edges := squareFreeEdgeEquiv L
  endpoints e := by
    cases e with
    | inl e =>
        left
        constructor <;> simp [squareFreeEdgeEquiv, squareFreeEdgeOfInternal,
          squareFree, Lattice2D.squareFreeGraph]
    | inr e =>
        left
        constructor <;> simp [squareFreeEdgeEquiv, squareFreeEdgeOfInternal,
        squareFree, Lattice2D.squareFreeGraph]

/--
The requested isomorphism from the sorted-pair carrier to its
positive-step graph.
-/
def squareFreeSourceGraphIsomorphism (L : ℕ) :
    Multigraph.Isomorphism (squareFree L) (Lattice2D.squareFreeGraph L) := by
  let I := squareFreeGraphIsomorphism L
  refine {
    vertices := I.vertices.symm
    edges := I.edges.symm
    endpoints := ?_ }
  intro e
  have he : I.edges (I.edges.symm e) = e := I.edges.apply_symm_apply e
  rcases I.endpoints (I.edges.symm e) with h | h
  · left
    have hs : (squareFree L).src e =
        I.vertices ((Lattice2D.squareFreeGraph L).src (I.edges.symm e)) := by
      calc
        (squareFree L).src e =
            (squareFree L).src (I.edges (I.edges.symm e)) :=
          congrArg (squareFree L).src he.symm
        _ = _ := h.1
    have ht : (squareFree L).tgt e =
        I.vertices ((Lattice2D.squareFreeGraph L).tgt (I.edges.symm e)) := by
      calc
        (squareFree L).tgt e =
            (squareFree L).tgt (I.edges (I.edges.symm e)) :=
          congrArg (squareFree L).tgt he.symm
        _ = _ := h.2
    constructor
    · calc
        (Lattice2D.squareFreeGraph L).src (I.edges.symm e) =
            I.vertices.symm
              (I.vertices ((Lattice2D.squareFreeGraph L).src (I.edges.symm e))) :=
          (I.vertices.symm_apply_apply _).symm
        _ = I.vertices.symm ((squareFree L).src e) := by rw [← hs]
        _ = _ := rfl
    · calc
        (Lattice2D.squareFreeGraph L).tgt (I.edges.symm e) =
            I.vertices.symm
              (I.vertices ((Lattice2D.squareFreeGraph L).tgt (I.edges.symm e))) :=
          (I.vertices.symm_apply_apply _).symm
        _ = I.vertices.symm ((squareFree L).tgt e) := by rw [← ht]
        _ = _ := rfl
  · right
    have hs : (squareFree L).src e =
        I.vertices ((Lattice2D.squareFreeGraph L).tgt (I.edges.symm e)) := by
      calc
        (squareFree L).src e =
            (squareFree L).src (I.edges (I.edges.symm e)) :=
          congrArg (squareFree L).src he.symm
        _ = _ := h.1
    have ht : (squareFree L).tgt e =
        I.vertices ((Lattice2D.squareFreeGraph L).src (I.edges.symm e)) := by
      calc
        (squareFree L).tgt e =
            (squareFree L).tgt (I.edges (I.edges.symm e)) :=
          congrArg (squareFree L).tgt he.symm
        _ = _ := h.2
    constructor
    · calc
        (Lattice2D.squareFreeGraph L).src (I.edges.symm e) =
            I.vertices.symm
              (I.vertices ((Lattice2D.squareFreeGraph L).src (I.edges.symm e))) :=
          (I.vertices.symm_apply_apply _).symm
        _ = I.vertices.symm ((squareFree L).tgt e) := by rw [← ht]
        _ = _ := rfl
    · calc
        (Lattice2D.squareFreeGraph L).tgt (I.edges.symm e) =
            I.vertices.symm
              (I.vertices ((Lattice2D.squareFreeGraph L).tgt (I.edges.symm e))) :=
          (I.vertices.symm_apply_apply _).symm
        _ = I.vertices.symm ((squareFree L).src e) := by rw [← hs]
        _ = _ := rfl

/--
The logarithmic Green dipole bound transfers to the free-square graph.
-/
theorem squareFree_source_pairing_dipole_ge_log {L : ℕ} (hL : 1 < L)
    (p q : Fin L × Fin L) :
    (1 / 24 : ℝ) * Real.log
        (↑(((squareFree L).toSimpleGraph.dist p q) + 1) : ℝ) ≤
      Multigraph.pairing (pointDipole p q)
        (Neg.neg ((squareFree L).greenOp (squareFree_connected L hL) (pointDipole p q))) := by
  let I := squareFreeGraphIsomorphism L
  have hsource := Lattice2D.squareFree_pairing_dipole_ge_log
    (by omega : 0 < L) p q
  have htrans := I.dipole_ge_log_of_dipole_ge_log
    (Lattice2D.squareFreeGraph_connected (by omega : 0 < L)) p q hsource
  exact htrans

def squarePeriodicAdjTwo (p q : Fin 2 × Fin 2) : Prop :=
  (p.1 = q.1 ∧
      (((p.2 : ℕ) : ℤ) ≡ (q.2 : ℕ) + 1 [ZMOD 2] ∨
        ((q.2 : ℕ) : ℤ) ≡ (p.2 : ℕ) + 1 [ZMOD 2])) ∨
    (p.2 = q.2 ∧
      (((p.1 : ℕ) : ℤ) ≡ (q.1 : ℕ) + 1 [ZMOD 2] ∨
        ((q.1 : ℕ) : ℤ) ≡ (p.1 : ℕ) + 1 [ZMOD 2]))

def squareFreeAdjTwo (p q : Fin 2 × Fin 2) : Prop :=
  ({|((p.1 : ℕ) : ℤ) - (q.1 : ℕ)|,
    |((p.2 : ℕ) : ℤ) - (q.2 : ℕ)|} : Finset ℤ) = {0, 1}

theorem squarePeriodicAdjTwo_iff_free (p q : Fin 2 × Fin 2) :
    squarePeriodicAdjTwo p q ↔ squareFreeAdjTwo p q := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [squarePeriodicAdjTwo, squareFreeAdjTwo, Int.ModEq, Finset.pair_comm]
  all_goals decide

theorem squarePeriodicEdge_two_free_property (e : SquarePeriodicEdge 2) :
    squareFreeAdjTwo e.1.1 e.1.2 := by
  exact (squarePeriodicAdjTwo_iff_free e.1.1 e.1.2).mp e.2.2

theorem squareFreeEdge_two_periodic_property (e : SquareFreeEdge 2) :
    squarePeriodicAdjTwo e.1.1 e.1.2 := by
  exact (squarePeriodicAdjTwo_iff_free e.1.1 e.1.2).mpr e.2.2

/--
At side length two, the periodic and free edge carriers are the
same four-cycle edge set (KP p. 2).
-/
def squarePeriodicEdgeEquivTwo : SquarePeriodicEdge 2 ≃ SquareFreeEdge 2 where
  toFun e := ⟨e.1, ⟨e.2.1, squarePeriodicEdge_two_free_property e⟩⟩
  invFun e := ⟨e.1, ⟨e.2.1, squareFreeEdge_two_periodic_property e⟩⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

/--
The periodic 2×2 four-cycle is isomorphic to the free
2×2 square.
-/
def squarePeriodicTwoIsomorphism :
    Multigraph.Isomorphism (squareFree 2) (squarePeriodic 2) where
  vertices := Equiv.refl _
  edges := squarePeriodicEdgeEquivTwo.symm
  endpoints e := by
    left
    constructor <;> simp [squarePeriodicEdgeEquivTwo, squareFree, squarePeriodic]

/-- The `L = 2` periodic logarithmic estimate follows from the free four-cycle
calculation, without using the duplicated right/up torus carrier. -/
theorem squarePeriodic_two_source_pairing_dipole_ge_log
    (p q : Fin 2 × Fin 2) :
    (1 / 24 : ℝ) * Real.log
        (↑(((squarePeriodic 2).toSimpleGraph.dist p q) + 1) : ℝ) ≤
      Multigraph.pairing (pointDipole p q)
        (Neg.neg ((squarePeriodic 2).greenOp
          (squarePeriodic_connected 2 (by omega)) (pointDipole p q))) := by
  have hfree := squareFree_source_pairing_dipole_ge_log (by omega : 1 < 2) p q
  have htrans := squarePeriodicTwoIsomorphism.dipole_ge_log_of_dipole_ge_log
    (squareFree_connected 2 (by omega)) p q hfree
  exact htrans

/-- The finite coordinate carrier and its residue-class presentation. -/
def squareTorusVertexEquiv (L : ℕ) [NeZero L] :
    (Fin L × Fin L) ≃ Lattice2D.TorusVertex L :=
  Equiv.prodCongr (ZMod.finEquiv L).toEquiv (ZMod.finEquiv L).toEquiv

private theorem finToZMod_eq_val {L : ℕ} [NeZero L] (a : Fin L) :
    ZMod.finEquiv L a = (a.val : ZMod L) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      simp only [ZMod.finEquiv]
      exact (Fin.cast_val_eq_self a).symm

theorem finModEq_to_zmod {L : ℕ} [NeZero L] (a b : Fin L)
    (h : ((a : ℕ) : ℤ) ≡ (b : ℕ) + 1 [ZMOD L]) :
    ZMod.finEquiv L a = ZMod.finEquiv L b + 1 := by
  have hn : a.val ≡ b.val + 1 [MOD L] := by
    apply Int.natCast_modEq_iff.mp
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hz : (a.val : ZMod L) = (b.val : ZMod L) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff a.val (b.val + 1) L).2 hn
  rw [finToZMod_eq_val a, finToZMod_eq_val b]
  exact hz

theorem zmod_to_finModEq {L : ℕ} [NeZero L] (a b : Fin L)
    (h : ZMod.finEquiv L a = ZMod.finEquiv L b + 1) :
    ((a : ℕ) : ℤ) ≡ (b : ℕ) + 1 [ZMOD L] := by
  rw [finToZMod_eq_val a, finToZMod_eq_val b] at h
  have hn : a.val ≡ b.val + 1 [MOD L] := by
    apply (ZMod.natCast_eq_natCast_iff a.val (b.val + 1) L).1
    simpa only [Nat.cast_add, Nat.cast_one] using h
  apply Int.natCast_modEq_iff.mpr
  simpa only [Nat.cast_add, Nat.cast_one] using hn

/-- A periodic edge, after the coordinate conversion, is exactly one positive
horizontal or vertical torus step, with either endpoint as its initial point. -/
theorem squarePeriodicEdge_classification {L : ℕ} [NeZero L]
    (e : SquarePeriodicEdge L) :
    (squareTorusVertexEquiv L e.1.1).1 =
        (squareTorusVertexEquiv L e.1.2).1 ∧
      ((squareTorusVertexEquiv L e.1.2).2 =
          (squareTorusVertexEquiv L e.1.1).2 + 1 ∨
        (squareTorusVertexEquiv L e.1.1).2 =
          (squareTorusVertexEquiv L e.1.2).2 + 1) ∨
    (squareTorusVertexEquiv L e.1.1).2 =
        (squareTorusVertexEquiv L e.1.2).2 ∧
      ((squareTorusVertexEquiv L e.1.2).1 =
          (squareTorusVertexEquiv L e.1.1).1 + 1 ∨
        (squareTorusVertexEquiv L e.1.1).1 =
          (squareTorusVertexEquiv L e.1.2).1 + 1) := by
  rcases e.2.2 with h | h
  · left
    constructor
    · exact congrArg (ZMod.finEquiv L) h.1
    · rcases h.2 with hp | hq
      · exact Or.inr (finModEq_to_zmod _ _ hp)
      · exact Or.inl (finModEq_to_zmod _ _ hq)
  · right
    constructor
    · exact congrArg (ZMod.finEquiv L) h.1
    · rcases h.2 with hp | hq
      · exact Or.inr (finModEq_to_zmod _ _ hp)
      · exact Or.inl (finModEq_to_zmod _ _ hq)

/--
A  periodic edge has the same unordered endpoints as a
right/up edge of the internal torus.
-/
def squarePeriodicEdgeRepresents {L : ℕ} [NeZero L]
    (e : SquarePeriodicEdge L) (t : Lattice2D.TorusEdge L) : Prop :=
  (squareTorusVertexEquiv L e.1.1 = t.1 ∧
    squareTorusVertexEquiv L e.1.2 = Lattice2D.torusStep L t.2 t.1) ∨
  (squareTorusVertexEquiv L e.1.1 = Lattice2D.torusStep L t.2 t.1 ∧
    squareTorusVertexEquiv L e.1.2 = t.1)

/--
Existence of the internal torus edge represented by a  periodic
edge.
-/
theorem squarePeriodicEdgeRepresents_exists {L : ℕ} [NeZero L]
    (e : SquarePeriodicEdge L) :
    ∃ t : Lattice2D.TorusEdge L, squarePeriodicEdgeRepresents e t := by
  rcases squarePeriodicEdge_classification e with hh | hv
  · rcases hh.2 with hq | hp
    · refine ⟨((squareTorusVertexEquiv L e.1.1), true), Or.inl ?_⟩
      constructor
      · rfl
      · have hpq : squareTorusVertexEquiv L e.1.2 =
            ((squareTorusVertexEquiv L e.1.1).1,
              (squareTorusVertexEquiv L e.1.1).2 + 1) :=
          Prod.ext hh.1.symm hq
        simpa [Lattice2D.torusStep] using hpq
    · refine ⟨((squareTorusVertexEquiv L e.1.2), true), Or.inr ?_⟩
      constructor
      · have hpq : squareTorusVertexEquiv L e.1.1 =
            ((squareTorusVertexEquiv L e.1.2).1,
              (squareTorusVertexEquiv L e.1.2).2 + 1) :=
          Prod.ext hh.1 hp
        simpa [Lattice2D.torusStep] using hpq
      · rfl
  · rcases hv.2 with hq | hp
    · refine ⟨((squareTorusVertexEquiv L e.1.1), false), Or.inl ?_⟩
      constructor
      · rfl
      · have hpq : squareTorusVertexEquiv L e.1.2 =
            ((squareTorusVertexEquiv L e.1.1).1 + 1,
              (squareTorusVertexEquiv L e.1.1).2) :=
          Prod.ext hq hv.1.symm
        simpa [Lattice2D.torusStep] using hpq
    · refine ⟨((squareTorusVertexEquiv L e.1.2), false), Or.inr ?_⟩
      constructor
      · have hpq : squareTorusVertexEquiv L e.1.1 =
            ((squareTorusVertexEquiv L e.1.2).1 + 1,
              (squareTorusVertexEquiv L e.1.2).2) :=
          Prod.ext hp hv.1
        simpa [Lattice2D.torusStep] using hpq
      · rfl

/--
Read a  periodic edge as a right/up edge on residue-class
coordinates.
-/
noncomputable def squarePeriodicEdgeToTorus {L : ℕ} [NeZero L]
    (e : SquarePeriodicEdge L) : Lattice2D.TorusEdge L :=
  Classical.choose (squarePeriodicEdgeRepresents_exists e)

/--
The chosen torus edge has the same unordered endpoints as the
periodic edge.
-/
theorem squarePeriodicEdgeToTorus_endpoints {L : ℕ} [NeZero L]
    (e : SquarePeriodicEdge L) : squarePeriodicEdgeRepresents e
      (squarePeriodicEdgeToTorus e) :=
  Classical.choose_spec (squarePeriodicEdgeRepresents_exists e)

theorem squarePeriodicEdge_eq_of_sorted_endpoints {L : ℕ}
    (e f : SquarePeriodicEdge L)
    (h : (e.1.1 = f.1.1 ∧ e.1.2 = f.1.2) ∨
      (e.1.1 = f.1.2 ∧ e.1.2 = f.1.1)) : e = f := by
  rcases e with ⟨⟨p, q⟩, hp⟩
  rcases f with ⟨⟨r, s⟩, hr⟩
  change (⟨(p, q), hp⟩ : SquarePeriodicEdge L) = ⟨(r, s), hr⟩
  rcases h with h | h
  · apply Subtype.ext
    exact Prod.ext h.1 h.2
  · have hrev : toLex q < toLex p := by
      calc
        toLex q = toLex r := congrArg toLex h.2
        _ < toLex s := hr.1
        _ = toLex p := congrArg toLex h.1.symm
    exact (lt_asymm hp.1 hrev).elim

theorem squarePeriodicAdj_symm {L : ℕ} (p q : Fin L × Fin L)
    (h : (p.1 = q.1 ∧ (((p.2 : ℕ) : ℤ) ≡ (q.2 : ℕ) + 1 [ZMOD L] ∨
        ((q.2 : ℕ) : ℤ) ≡ (p.2 : ℕ) + 1 [ZMOD L])) ∨
      (p.2 = q.2 ∧ (((p.1 : ℕ) : ℤ) ≡ (q.1 : ℕ) + 1 [ZMOD L] ∨
        ((q.1 : ℕ) : ℤ) ≡ (p.1 : ℕ) + 1 [ZMOD L]))) :
    (q.1 = p.1 ∧ (((q.2 : ℕ) : ℤ) ≡ (p.2 : ℕ) + 1 [ZMOD L] ∨
        ((p.2 : ℕ) : ℤ) ≡ (q.2 : ℕ) + 1 [ZMOD L])) ∨
      (q.2 = p.2 ∧ (((q.1 : ℕ) : ℤ) ≡ (p.1 : ℕ) + 1 [ZMOD L] ∨
        ((p.1 : ℕ) : ℤ) ≡ (q.1 : ℕ) + 1 [ZMOD L])) := by
  rcases h with h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.1.symm, h.2.symm⟩

private theorem zmod_one_ne_zero_of_three_le {L : ℕ} (hL : 2 < L) :
    (1 : ZMod L) ≠ 0 := by
  intro h
  have hc : ((1 : ℕ) : ZMod L) = 0 := by simpa using h
  have hdvd : L ∣ 1 := (ZMod.natCast_eq_zero_iff 1 L).mp hc
  have hle : L ≤ 1 := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem zmod_two_ne_zero_of_three_le {L : ℕ} (hL : 2 < L) :
    (2 : ZMod L) ≠ 0 := by
  intro h
  have hc : ((2 : ℕ) : ZMod L) = 0 := by simpa using h
  have hdvd : L ∣ 2 := (ZMod.natCast_eq_zero_iff 2 L).mp hc
  have hle : L ≤ 2 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Right/up torus edges are determined by their unordered endpoints for
side length at least three. -/
theorem torusEdge_eq_of_unordered_endpoints {L : ℕ} (hL : 2 < L)
    [NeZero L] (t u : Lattice2D.TorusEdge L)
    (h : (t.1 = u.1 ∧ Lattice2D.torusStep L t.2 t.1 =
        Lattice2D.torusStep L u.2 u.1) ∨
      (t.1 = Lattice2D.torusStep L u.2 u.1 ∧
        Lattice2D.torusStep L t.2 t.1 = u.1)) : t = u := by
  rcases t with ⟨p, d⟩
  rcases u with ⟨q, c⟩
  rcases h with h | h
  · rcases h with ⟨hpq, hstep⟩
    change p = q at hpq
    subst q
    cases d <;> cases c
    · rfl
    · have hx : p.1 + 1 = p.1 := by
        simpa [Lattice2D.torusStep] using congrArg Prod.fst hstep
      have hz : (1 : ZMod L) = 0 := by
        have hx' : p.1 + 1 = p.1 + 0 := by simpa using hx
        exact add_left_cancel hx'
      exact (zmod_one_ne_zero_of_three_le hL hz).elim
    · have hy : p.2 + 1 = p.2 := by
        simpa [Lattice2D.torusStep] using congrArg Prod.snd hstep
      have hz : (1 : ZMod L) = 0 := by
        have hy' : p.2 + 1 = p.2 + 0 := by simpa using hy
        exact add_left_cancel hy'
      exact (zmod_one_ne_zero_of_three_le hL hz).elim
    · rfl
  · rcases h with ⟨hpq, hstep⟩
    change p = Lattice2D.torusStep L c q at hpq
    change Lattice2D.torusStep L d p = q at hstep
    cases d <;> cases c
    · have hx := congrArg Prod.fst hstep
      have hp : p.1 = q.1 + 1 := by simpa [Lattice2D.torusStep] using congrArg Prod.fst hpq
      have htwo : q.1 + (1 + 1) = q.1 := by
        calc
          q.1 + (1 + 1) = (q.1 + 1) + 1 := by ring
          _ = p.1 + 1 := by rw [hp]
          _ = q.1 := by simpa [Lattice2D.torusStep] using hx
      have hz : (2 : ZMod L) = 0 := by
        have htwo' : q.1 + (1 + 1) = q.1 + 0 := by simpa using htwo
        have hsum : (1 : ZMod L) + 1 = 0 := add_left_cancel htwo'
        norm_num at hsum ⊢
        exact hsum
      exact (zmod_two_ne_zero_of_three_le hL hz).elim
    · have hp : p.1 = q.1 := by
        simpa [Lattice2D.torusStep] using congrArg Prod.fst hpq
      have hx := congrArg Prod.fst hstep
      have hone : (1 : ZMod L) = 0 := by
        have h : q.1 + 1 = q.1 := by
          calc
            q.1 + 1 = p.1 + 1 := by rw [hp]
            _ = q.1 := by simpa [Lattice2D.torusStep] using hx
        have h' : q.1 + 1 = q.1 + 0 := by simpa using h
        exact add_left_cancel h'
      exact (zmod_one_ne_zero_of_three_le hL hone).elim
    · have hp : p.2 = q.2 := by
        simpa [Lattice2D.torusStep] using congrArg Prod.snd hpq
      have hy := congrArg Prod.snd hstep
      have hone : (1 : ZMod L) = 0 := by
        have h : q.2 + 1 = q.2 := by
          calc
            q.2 + 1 = p.2 + 1 := by rw [hp]
            _ = q.2 := by simpa [Lattice2D.torusStep] using hy
        have h' : q.2 + 1 = q.2 + 0 := by simpa using h
        exact add_left_cancel h'
      exact (zmod_one_ne_zero_of_three_le hL hone).elim
    · have hy := congrArg Prod.snd hstep
      have hp : p.2 = q.2 + 1 := by simpa [Lattice2D.torusStep] using congrArg Prod.snd hpq
      have htwo : q.2 + (1 + 1) = q.2 := by
        calc
          q.2 + (1 + 1) = (q.2 + 1) + 1 := by ring
          _ = p.2 + 1 := by rw [hp]
          _ = q.2 := by simpa [Lattice2D.torusStep] using hy
      have hz : (2 : ZMod L) = 0 := by
        have htwo' : q.2 + (1 + 1) = q.2 + 0 := by simpa using htwo
        have hsum : (1 : ZMod L) + 1 = 0 := add_left_cancel htwo'
        norm_num at hsum ⊢
        exact hsum
      exact (zmod_two_ne_zero_of_three_le hL hz).elim

/--
Convert a positively oriented torus edge into the carrier by
sorting its endpoint pair.
-/
def squarePeriodicEdgeOfTorus {L : ℕ} [NeZero L] (hL : 2 < L)
    (t : Lattice2D.TorusEdge L) : SquarePeriodicEdge L := by
  let p := (squareTorusVertexEquiv L).symm t.1
  let q := (squareTorusVertexEquiv L).symm
    (Lattice2D.torusStep L t.2 t.1)
  have hp : squareTorusVertexEquiv L p = t.1 :=
    Equiv.apply_symm_apply (squareTorusVertexEquiv L) t.1
  have hq : squareTorusVertexEquiv L q = Lattice2D.torusStep L t.2 t.1 :=
    Equiv.apply_symm_apply (squareTorusVertexEquiv L) _
  have hne : p ≠ q := by
    intro hpq
    have heq : t.1 = Lattice2D.torusStep L t.2 t.1 := by
      calc
        t.1 = squareTorusVertexEquiv L p := hp.symm
        _ = squareTorusVertexEquiv L q := congrArg _ hpq
        _ = Lattice2D.torusStep L t.2 t.1 := hq
    exact (Lattice2D.torusGraph L hL).src_ne_tgt t heq
  have hadj :
      (p.1 = q.1 ∧ (((p.2 : ℕ) : ℤ) ≡ (q.2 : ℕ) + 1 [ZMOD L] ∨
          ((q.2 : ℕ) : ℤ) ≡ (p.2 : ℕ) + 1 [ZMOD L])) ∨
        (p.2 = q.2 ∧ (((p.1 : ℕ) : ℤ) ≡ (q.1 : ℕ) + 1 [ZMOD L] ∨
          ((q.1 : ℕ) : ℤ) ≡ (p.1 : ℕ) + 1 [ZMOD L])) := by
    cases hd : t.2
    · right
      constructor
      · have hcoord : (squareTorusVertexEquiv L p).2 =
            (squareTorusVertexEquiv L q).2 := by
          rw [hp, hq]
          simp [Lattice2D.torusStep, hd]
        apply (ZMod.finEquiv L).injective
        exact hcoord
      · right
        apply zmod_to_finModEq
        calc
          ZMod.finEquiv L q.1 = (squareTorusVertexEquiv L q).1 := rfl
          _ = (Lattice2D.torusStep L t.2 t.1).1 := congrArg Prod.fst hq
          _ = t.1.1 + 1 := by simp [Lattice2D.torusStep, hd]
          _ = (squareTorusVertexEquiv L p).1 + 1 := by rw [hp]
          _ = ZMod.finEquiv L p.1 + 1 := rfl
    · left
      constructor
      · have hcoord : (squareTorusVertexEquiv L p).1 =
            (squareTorusVertexEquiv L q).1 := by
          rw [hp, hq]
          simp [Lattice2D.torusStep, hd]
        apply (ZMod.finEquiv L).injective
        exact hcoord
      · right
        apply zmod_to_finModEq
        calc
          ZMod.finEquiv L q.2 = (squareTorusVertexEquiv L q).2 := rfl
          _ = (Lattice2D.torusStep L t.2 t.1).2 := congrArg Prod.snd hq
          _ = t.1.2 + 1 := by simp [Lattice2D.torusStep, hd]
          _ = (squareTorusVertexEquiv L p).2 + 1 := by rw [hp]
          _ = ZMod.finEquiv L p.2 + 1 := rfl
  have hlexne : toLex p ≠ toLex q := by
    intro h
    exact hne (by simpa using h)
  by_cases hpq : toLex p < toLex q
  · exact ⟨(p, q), hpq, hadj⟩
  · have hqp : toLex q < toLex p := by
      rcases lt_or_gt_of_ne hlexne with h | h
      · exact (hpq h).elim
      · exact h
    exact ⟨(q, p), hqp, squarePeriodicAdj_symm p q hadj⟩

theorem squarePeriodicEdgeOfTorus_represents {L : ℕ} [NeZero L]
    (hL : 2 < L) (t : Lattice2D.TorusEdge L) :
    squarePeriodicEdgeRepresents (squarePeriodicEdgeOfTorus hL t) t := by
  classical
  unfold squarePeriodicEdgeOfTorus
  dsimp
  split_ifs with h
  · change (squareTorusVertexEquiv L
        ((squareTorusVertexEquiv L).symm t.1) = t.1 ∧
      squareTorusVertexEquiv L
        ((squareTorusVertexEquiv L).symm (Lattice2D.torusStep L t.2 t.1)) =
          Lattice2D.torusStep L t.2 t.1) ∨ _
    exact Or.inl ⟨Equiv.apply_symm_apply _ _, Equiv.apply_symm_apply _ _⟩
  · change _ ∨ (squareTorusVertexEquiv L
        ((squareTorusVertexEquiv L).symm (Lattice2D.torusStep L t.2 t.1)) =
          Lattice2D.torusStep L t.2 t.1 ∧
      squareTorusVertexEquiv L
        ((squareTorusVertexEquiv L).symm t.1) = t.1)
    exact Or.inr ⟨Equiv.apply_symm_apply _ _, Equiv.apply_symm_apply _ _⟩

theorem squarePeriodicEdgeRepresents_unique {L : ℕ} [NeZero L]
    (hL : 2 < L) {e : SquarePeriodicEdge L} {t u : Lattice2D.TorusEdge L}
    (ht : squarePeriodicEdgeRepresents e t)
    (hu : squarePeriodicEdgeRepresents e u) : t = u := by
  rcases ht with ht | ht <;> rcases hu with hu | hu
  · apply torusEdge_eq_of_unordered_endpoints hL
    exact Or.inl ⟨ht.1.symm.trans hu.1, ht.2.symm.trans hu.2⟩
  · apply torusEdge_eq_of_unordered_endpoints hL
    exact Or.inr ⟨ht.1.symm.trans hu.1, ht.2.symm.trans hu.2⟩
  · apply torusEdge_eq_of_unordered_endpoints hL
    exact Or.inr ⟨ht.2.symm.trans hu.2, ht.1.symm.trans hu.1⟩
  · apply torusEdge_eq_of_unordered_endpoints hL
    exact Or.inl ⟨ht.2.symm.trans hu.2, ht.1.symm.trans hu.1⟩

theorem squarePeriodicEdgeToTorus_edgeOfTorus {L : ℕ} [NeZero L]
    (hL : 2 < L) (t : Lattice2D.TorusEdge L) :
    squarePeriodicEdgeToTorus (squarePeriodicEdgeOfTorus hL t) = t := by
  exact (squarePeriodicEdgeRepresents_unique hL
    (squarePeriodicEdgeOfTorus_represents hL t)
    (squarePeriodicEdgeToTorus_endpoints _)).symm

theorem squarePeriodicEdge_eq_of_same_torus_representation {L : ℕ} [NeZero L]
    {e f : SquarePeriodicEdge L} {t : Lattice2D.TorusEdge L}
    (he : squarePeriodicEdgeRepresents e t)
    (hf : squarePeriodicEdgeRepresents f t) : e = f := by
  rcases he with he | he <;> rcases hf with hf | hf
  · apply squarePeriodicEdge_eq_of_sorted_endpoints
    exact Or.inl ⟨(squareTorusVertexEquiv _).injective (he.1.trans hf.1.symm),
      (squareTorusVertexEquiv _).injective (he.2.trans hf.2.symm)⟩
  · apply squarePeriodicEdge_eq_of_sorted_endpoints
    exact Or.inr ⟨(squareTorusVertexEquiv _).injective (he.1.trans hf.2.symm),
      (squareTorusVertexEquiv _).injective (he.2.trans hf.1.symm)⟩
  · apply squarePeriodicEdge_eq_of_sorted_endpoints
    exact Or.inr ⟨(squareTorusVertexEquiv _).injective (he.1.trans hf.2.symm),
      (squareTorusVertexEquiv _).injective (he.2.trans hf.1.symm)⟩
  · apply squarePeriodicEdge_eq_of_sorted_endpoints
    exact Or.inl ⟨(squareTorusVertexEquiv _).injective (he.1.trans hf.1.symm),
      (squareTorusVertexEquiv _).injective (he.2.trans hf.2.symm)⟩

theorem squarePeriodicEdgeOfTorus_edgeToTorus {L : ℕ} [NeZero L]
    (hL : 2 < L) (e : SquarePeriodicEdge L) :
    squarePeriodicEdgeOfTorus hL (squarePeriodicEdgeToTorus e) = e := by
  apply squarePeriodicEdge_eq_of_same_torus_representation
    (squarePeriodicEdgeOfTorus_represents hL _)
  exact squarePeriodicEdgeToTorus_endpoints e

/--
Isomorphism from the right/up torus carrier to the sorted-pair
periodic square.
-/
noncomputable def torusGraphToSquarePeriodicIso {L : ℕ} [NeZero L] (hL : 2 < L) :
    Multigraph.Isomorphism (Lattice2D.torusGraph L hL) (squarePeriodic L) where
  vertices := (squareTorusVertexEquiv L).symm
  edges := {
    toFun := squarePeriodicEdgeOfTorus hL
    invFun := squarePeriodicEdgeToTorus
    left_inv := squarePeriodicEdgeToTorus_edgeOfTorus hL
    right_inv := squarePeriodicEdgeOfTorus_edgeToTorus hL }
  endpoints t := by
    rcases squarePeriodicEdgeOfTorus_represents hL t with h | h
    · left
      constructor
      · simpa [squarePeriodic, Lattice2D.torusGraph_src] using
          congrArg (squareTorusVertexEquiv L).symm h.1
      · simpa [squarePeriodic, Lattice2D.torusGraph_tgt] using
          congrArg (squareTorusVertexEquiv L).symm h.2
    · right
      constructor
      · simpa [squarePeriodic, Lattice2D.torusGraph_tgt] using
          congrArg (squareTorusVertexEquiv L).symm h.1
      · simpa [squarePeriodic, Lattice2D.torusGraph_src] using
          congrArg (squareTorusVertexEquiv L).symm h.2

/--
The requested -to-internal periodic carrier isomorphism.
-/
noncomputable def squarePeriodicTorusIsomorphism {L : ℕ} [NeZero L] (hL : 2 < L) :
    Multigraph.Isomorphism (squarePeriodic L) (Lattice2D.torusGraph L hL) := by
  refine {
    vertices := squareTorusVertexEquiv L
    edges := {
      toFun := squarePeriodicEdgeToTorus
      invFun := squarePeriodicEdgeOfTorus hL
      left_inv := squarePeriodicEdgeOfTorus_edgeToTorus hL
      right_inv := squarePeriodicEdgeToTorus_edgeOfTorus hL }
    endpoints := ?_ }
  intro e
  rcases squarePeriodicEdgeToTorus_endpoints e with h | h
  · left
    constructor
    · exact h.1.symm
    · exact h.2.symm
  · right
    constructor
    · exact h.2.symm
    · exact h.1.symm

/-- The periodic carrier equivalence applies in particular to every side
length at least four (the regime used for even periodic boxes in KP p. 2). -/
noncomputable def squarePeriodicTorusIsomorphism_of_four {L : ℕ}
    (hL : 4 ≤ L) :
    Multigraph.Isomorphism (squarePeriodic L)
      (Lattice2D.torusGraph L (by omega)) := by
  letI : NeZero L := ⟨by omega⟩
  exact squarePeriodicTorusIsomorphism (by omega)

/--
Transfer the torus logarithmic dipole estimate to the periodic
square carrier (KP p. 3).
-/
theorem squarePeriodic_source_pairing_dipole_ge_log {L : ℕ} [NeZero L]
    (hL : 2 < L) (p q : Fin L × Fin L) :
    (1 / 24 : ℝ) * Real.log
        (↑(((squarePeriodic L).toSimpleGraph.dist p q) + 1) : ℝ) ≤
      Multigraph.pairing (pointDipole p q)
        (-(squarePeriodic L).greenOp (squarePeriodic_connected L (by omega))
          (pointDipole p q)) := by
  let I := torusGraphToSquarePeriodicIso hL
  let p' := squareTorusVertexEquiv L p
  let q' := squareTorusVertexEquiv L q
  have htorus := Lattice2D.torus_pairing_dipole_ge_log hL p' q'
  have hconnected := Lattice2D.torusGraph_connected L hL
  have htrans := I.dipole_ge_log_of_dipole_ge_log hconnected p' q' htorus
  have hp' : I.vertices p' = p := by
    exact Equiv.symm_apply_apply (squareTorusVertexEquiv L) p
  have hq' : I.vertices q' = q := by
    exact Equiv.symm_apply_apply (squareTorusVertexEquiv L) q
  rw [hp', hq'] at htrans
  exact htrans

/--
The periodic logarithmic estimate for every KP even side length,
including the two-by-two four-cycle (KP pp. 2–3).
-/
theorem squarePeriodic_even_source_pairing_dipole_ge_log {L : ℕ}
    (hL : 1 < L) (hEven : Even L) (p q : Fin L × Fin L) :
    (1 / 24 : ℝ) * Real.log
        (↑(((squarePeriodic L).toSimpleGraph.dist p q) + 1) : ℝ) ≤
      Multigraph.pairing (pointDipole p q)
        (-(squarePeriodic L).greenOp (squarePeriodic_connected L hL)
          (pointDipole p q)) := by
  by_cases hTwo : L = 2
  · subst L
    exact squarePeriodic_two_source_pairing_dipole_ge_log p q
  · rcases hEven with ⟨k, hk⟩
    have h4 : 4 ≤ L := by omega
    exact @squarePeriodic_source_pairing_dipole_ge_log L ⟨by omega⟩
      (by omega : 2 < L) p q

end FroehlichSpencer.BKT

end
