/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.Claim42

/-! # Path orderings for Claim 4.2 clusters of size two or three -/

@[expose] public section

namespace FroehlichSpencer.BKT

private theorem walk_length_two_edges {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hlen : p.length = 2) :
    ∃ w, G.Adj u w ∧ G.Adj w v := by
  cases p with
  | nil => simp at hlen
  | @cons a b c hab q =>
      cases q with
      | nil => simp at hlen
      | @cons b c d hbc r =>
          cases r with
          | nil => exact ⟨b, hab, hbc⟩
          | @cons c d e hcd t => simp at hlen

/-- A connected two-vertex set is an adjacent pair. -/
theorem exists_adjacent_pair_of_connected_card_two {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (s : Finset V) (hcard : s.card = 2)
    (hconn : IsConnectedVertexSet G s) :
    ∃ u v, u ≠ v ∧ s = {u, v} ∧ G.Adj u v := by
  classical
  rcases (Finset.card_eq_two.mp hcard) with ⟨u, v, huv, rfl⟩
  let H := G.induce ({u, v} : Finset V)
  have hconn' : H.Connected := by simpa [H, IsConnectedVertexSet] using hconn
  let u' : {x // x ∈ ({u, v} : Finset V)} := ⟨u, by simp⟩
  let v' : {x // x ∈ ({u, v} : Finset V)} := ⟨v, by simp⟩
  obtain ⟨p, hp⟩ := hconn'.exists_isPath u' v'
  have hsubcard : Fintype.card {x // x ∈ ({u, v} : Finset V)} = 2 := by
    simp [huv]
  have hlenlt : p.length < 2 := by
    rw [← hsubcard]
    exact hp.length_lt
  have hlen0 : p.length ≠ 0 := by
    intro hzero
    have heq : u' = v' := SimpleGraph.Walk.eq_of_length_eq_zero hzero
    exact huv (congrArg Subtype.val heq)
  have hlen : p.length = 1 := by omega
  have hadj' : H.Adj u' v' :=
    (SimpleGraph.Walk.exists_length_eq_one_iff).mp ⟨p, hlen⟩
  have hadj : G.Adj u v := by
    simpa [H, SimpleGraph.induce_adj] using hadj'
  exact ⟨u, v, huv, rfl, hadj⟩

/-- A connected three-vertex set has an ordering that is a two-edge path.
This is the exact local input needed for the coordinate-span argument. -/
theorem exists_path_ordering_of_connected_card_three {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (s : Finset V) (hcard : s.card = 3)
    (hconn : IsConnectedVertexSet G s) :
    ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ s = {u, v, w} ∧
      G.Adj u v ∧ G.Adj v w := by
  classical
  rcases (Finset.card_eq_three.mp hcard) with ⟨u, v, w, huv, huw, hvw, rfl⟩
  let H := G.induce ({u, v, w} : Finset V)
  have hconn' : H.Connected := by simpa [H, IsConnectedVertexSet] using hconn
  let u' : {x // x ∈ ({u, v, w} : Finset V)} := ⟨u, by simp⟩
  let v' : {x // x ∈ ({u, v, w} : Finset V)} := ⟨v, by simp⟩
  let w' : {x // x ∈ ({u, v, w} : Finset V)} := ⟨w, by simp⟩
  obtain ⟨p, hp⟩ := hconn'.exists_isPath u' v'
  have hsubcard : Fintype.card {x // x ∈ ({u, v, w} : Finset V)} = 3 := by
    simp [huv, huw, hvw]
  have hlenlt : p.length < 3 := by
    rw [← hsubcard]
    exact hp.length_lt
  have hlen0 : p.length ≠ 0 := by
    intro hzero
    have heq : u' = v' := SimpleGraph.Walk.eq_of_length_eq_zero hzero
    exact huv (congrArg Subtype.val heq)
  have hlenCases : p.length = 1 ∨ p.length = 2 := by omega
  rcases hlenCases with hpone | hptwo
  · have huv' : H.Adj u' v' :=
      (SimpleGraph.Walk.exists_length_eq_one_iff).mp ⟨p, hpone⟩
    have huvG : G.Adj u v := by
      simpa [H, SimpleGraph.induce_adj] using huv'
    obtain ⟨q, hq⟩ := hconn'.exists_isPath w' u'
    have hqlt : q.length < 3 := by
      rw [← hsubcard]
      exact hq.length_lt
    have hq0 : q.length ≠ 0 := by
      intro hzero
      have heq : w' = u' := SimpleGraph.Walk.eq_of_length_eq_zero hzero
      exact huw (congrArg Subtype.val heq).symm
    have hqCases : q.length = 1 ∨ q.length = 2 := by omega
    rcases hqCases with hqone | hqtwo
    · have hwu' : H.Adj w' u' :=
        (SimpleGraph.Walk.exists_length_eq_one_iff).mp ⟨q, hqone⟩
      have hwu : G.Adj w u := by
        simpa [H, SimpleGraph.induce_adj] using hwu'
      have hset : ({u, v, w} : Finset V) = {v, u, w} := Finset.insert_comm u v {w}
      exact ⟨v, u, w, huv.symm, hvw, huw, hset,
        huvG.symm, hwu.symm⟩
    · obtain ⟨m, hwm', hmu'⟩ := walk_length_two_edges q hq hqtwo
      have hm_mem : (m : V) ∈ ({u, v, w} : Finset V) := m.property
      have hmval : (m : V) = v := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm_mem
        rcases hm_mem with hmu | hmv | hmw
        · change G.Adj (m : V) u at hmu'
          have hfalse : False := by simp [hmu] at hmu'
          exact hfalse.elim
        · exact hmv
        · change G.Adj w (m : V) at hwm'
          have hfalse : False := by simp [hmw] at hwm'
          exact hfalse.elim
      have hwv : H.Adj w' v' := by
        have hmEq : m = v' := Subtype.ext hmval
        simpa [hmEq] using hwm'
      have hwvG : G.Adj w v := by
        simpa [H, SimpleGraph.induce_adj] using hwv
      have hset : ({u, v, w} : Finset V) = {w, v, u} := by
        rw [Finset.insert_comm u v, Finset.pair_comm u w, Finset.insert_comm v w]
      exact ⟨w, v, u, hvw.symm, huw.symm, huv.symm, hset,
        hwvG, huvG.symm⟩
  · obtain ⟨m, hum', hmv'⟩ := walk_length_two_edges p hp hptwo
    have hm_mem : (m : V) ∈ ({u, v, w} : Finset V) := m.property
    have hmval : (m : V) = w := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm_mem
      rcases hm_mem with hmu | hmv | hmw
      · change G.Adj u (m : V) at hum'
        have hfalse : False := by simp [hmu] at hum'
        exact hfalse.elim
      · change G.Adj (m : V) v at hmv'
        have hfalse : False := by simp [hmv] at hmv'
        exact hfalse.elim
      · exact hmw
    have huw' : H.Adj u' w' := by
      have hmEq : m = w' := Subtype.ext hmval
      simpa [hmEq] using hum'
    have hwv' : H.Adj w' v' := by
      have hmEq : m = w' := Subtype.ext hmval
      simpa [hmEq] using hmv'
    have huwG : G.Adj u w := by
      simpa [H, SimpleGraph.induce_adj] using huw'
    have hwvG : G.Adj w v := by
      simpa [H, SimpleGraph.induce_adj] using hwv'
    have hset : ({u, v, w} : Finset V) = {u, w, v} := by
      rw [Finset.pair_comm v w]
    exact ⟨u, w, v, huw, huv, hvw.symm, hset, huwG, hwvG⟩

/-- The pair-or-path interface for any Claim 4.2 set. -/
theorem exists_c42_path_ordering {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (s : Finset V) (hs : IsC42Set G s) :
    (∃ u v, u ≠ v ∧ s = {u, v} ∧ G.Adj u v) ∨
    (∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ s = {u, v, w} ∧
      G.Adj u v ∧ G.Adj v w) := by
  rcases hs.1 with h2 | h3
  · exact Or.inl (exists_adjacent_pair_of_connected_card_two G s h2 hs.2)
  · exact Or.inr (exists_path_ordering_of_connected_card_three G s h3 hs.2)

end FroehlichSpencer.BKT

end
