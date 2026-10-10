/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Potential.Transport
public import FroehlichSpencer.BKT.Potential.NashWilliams
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Transport of logarithmic Green lower bounds

The logarithmic dipole estimate cited in KP Theorem 1.1 (p. 3) is invariant
under endpoint-pair isomorphisms of finite multigraphs.

This module records the
transport step used when comparing the internal square and torus carriers with
the surface carriers.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

open Multigraph

universe u v w x

variable {V : Type u} {E : Type v} {W : Type w} {F : Type x}
variable {G : Multigraph V E} {H : Multigraph W F}

/-- Connected-graph distance is preserved by a multigraph isomorphism. -/
theorem Multigraph.Isomorphism.dist_eq (I : Multigraph.Isomorphism G H)
    [Fintype V] [Fintype E] [DecidableEq V]
    [Fintype W] [Fintype F] [DecidableEq W]
    (hG : G.Connected) (p q : V) :
    H.toSimpleGraph.dist (I.vertices p) (I.vertices q) =
      G.toSimpleGraph.dist p q := by
  apply Nat.le_antisymm
  · have hpq : G.toSimpleGraph.Reachable p q := by
      have hconn : G.toSimpleGraph.Connected := hG
      exact hconn.preconnected p q
    obtain ⟨w, hw⟩ := hpq.exists_walk_length_eq_dist
    calc
      H.toSimpleGraph.dist (I.vertices p) (I.vertices q) ≤
          (w.map I.simpleGraphIso.toHom).length := SimpleGraph.dist_le _
      _ = G.toSimpleGraph.dist p q := by rw [SimpleGraph.Walk.length_map, hw]
  · have hH : H.Connected := I.connected_iff.mp hG
    have hpq : H.toSimpleGraph.Reachable (I.vertices p) (I.vertices q) := by
      have hconn : H.toSimpleGraph.Connected := hH
      exact hconn.preconnected (I.vertices p) (I.vertices q)
    obtain ⟨w, hw⟩ := hpq.exists_walk_length_eq_dist
    have hstart : I.simpleGraphIso.symm.toHom (I.vertices p) = p := by
      change I.vertices.symm (I.vertices p) = p
      exact I.vertices.symm_apply_apply p
    have hfinish : I.simpleGraphIso.symm.toHom (I.vertices q) = q := by
      change I.vertices.symm (I.vertices q) = q
      exact I.vertices.symm_apply_apply q
    calc
      G.toSimpleGraph.dist p q ≤
          (w.map I.simpleGraphIso.symm.toHom).length := by
        simpa only [hstart, hfinish] using
          SimpleGraph.dist_le (w.map I.simpleGraphIso.symm.toHom)
      _ = H.toSimpleGraph.dist (I.vertices p) (I.vertices q) := by
        rw [SimpleGraph.Walk.length_map]
        simpa using hw

/-- The dipole Green pairing is invariant under a multigraph isomorphism. -/
theorem Multigraph.Isomorphism.pairing_dipole_greenOp_eq
    (I : Multigraph.Isomorphism G H)
    [Fintype V] [Fintype E] [DecidableEq V]
    [Fintype W] [Fintype F] [DecidableEq W]
    (hG : G.Connected) (p q : V) :
    pairing (pointDipole (I.vertices p) (I.vertices q))
        (-(H.greenOp (I.connected_iff.mp hG)
          (pointDipole (I.vertices p) (I.vertices q)))) =
      pairing (pointDipole p q) (-(G.greenOp hG (pointDipole p q))) := by
  have hdipole : I.pushField (pointDipole p q) =
      pointDipole (I.vertices p) (I.vertices q) := by
    funext w
    have hwp : I.vertices.symm w = p ↔ w = I.vertices p := by
      constructor
      · intro h
        calc
          w = I.vertices (I.vertices.symm w) := (I.vertices.apply_symm_apply w).symm
          _ = I.vertices p := congrArg I.vertices h
      · intro h
        apply I.vertices.injective
        simpa using h
    have hwq : I.vertices.symm w = q ↔ w = I.vertices q := by
      constructor
      · intro h
        calc
          w = I.vertices (I.vertices.symm w) := (I.vertices.apply_symm_apply w).symm
          _ = I.vertices q := congrArg I.vertices h
      · intro h
        apply I.vertices.injective
        simpa using h
    simp only [pointDipole, Multigraph.Isomorphism.pushField, hwp, hwq]
  have hgreen := I.greenOp_transport hG (pointDipole p q)
  have hpushed : I.pushField (G.greenOp hG (pointDipole p q)) =
      H.greenOp (I.connected_iff.mp hG)
        (pointDipole (I.vertices p) (I.vertices q)) := by
    simpa [hdipole] using hgreen
  have hgreenNeg : I.pushField (-(G.greenOp hG (pointDipole p q))) =
      -(H.greenOp (I.connected_iff.mp hG)
        (pointDipole (I.vertices p) (I.vertices q))) := by
    funext w
    change -(G.greenOp hG (pointDipole p q)) (I.vertices.symm w) = _
    exact congrArg Neg.neg (congrFun hpushed w)
  calc
    pairing (pointDipole (I.vertices p) (I.vertices q))
        (-(H.greenOp (I.connected_iff.mp hG)
          (pointDipole (I.vertices p) (I.vertices q)))) =
      pairing (I.pushField (pointDipole p q))
        (I.pushField (-(G.greenOp hG (pointDipole p q)))) := by rw [hdipole, hgreenNeg]
    _ = pairing (pointDipole p q) (-(G.greenOp hG (pointDipole p q))) :=
      I.pairing_transport (pointDipole p q) (-(G.greenOp hG (pointDipole p q)))

/-- A logarithmic Green dipole lower bound transfers through a connected graph
isomorphism, including the graph distance in its logarithm. -/
theorem Multigraph.Isomorphism.dipole_ge_log_of_dipole_ge_log
    (I : Multigraph.Isomorphism G H)
    [Fintype V] [Fintype E] [DecidableEq V]
    [Fintype W] [Fintype F] [DecidableEq W]
    (hG : G.Connected) (p q : V) {c : ℝ}
    (hbound : c * Real.log (↑(G.toSimpleGraph.dist p q + 1) : ℝ) ≤
      pairing (pointDipole p q) (-(G.greenOp hG (pointDipole p q)))) :
    c * Real.log (↑(H.toSimpleGraph.dist (I.vertices p) (I.vertices q) + 1) : ℝ) ≤
      pairing (pointDipole (I.vertices p) (I.vertices q))
        (-(H.greenOp (I.connected_iff.mp hG)
          (pointDipole (I.vertices p) (I.vertices q)))) := by
  rw [I.dist_eq hG p q, I.pairing_dipole_greenOp_eq hG p q]
  exact hbound

end FroehlichSpencer.BKT

end
