/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerMain
public import FroehlichSpencer.BKT.Charges.DensityRouting
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds
public import FroehlichSpencer.BKT.Surface.SquareZeroConnected
public import FroehlichSpencer.BKT.Bridge.WiredBoxCarrier

/-!
* `l1`: the `ℓ¹` distance of bounded faces; site–site edges of `squareZero` are lattice steps
  (`l1_of_edge`), so a walk avoiding the wired root moves at most one `ℓ¹` unit per step
  (`l1_le_length_of_root_free`).
* `path_site_local`: every bounded face on a **path** from a bounded face `a` lies within `ℓ¹`
  distance `length` of `a` or of the other endpoint (the root is visited at most once).
* `dist_some_le_l1`: graph distance between bounded faces is at most their `ℓ¹` distance.
* `card_incident_le_four`: every bounded face meets at most four edges.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Duality

variable {L : ℕ}

/-- The `ℓ¹` distance of two bounded faces. -/
def l1 (x y : Site L) : ℕ :=
  Int.natAbs ((x.1.val : ℤ) - y.1.val) + Int.natAbs ((x.2.val : ℤ) - y.2.val)

theorem l1_comm (x y : Site L) : l1 x y = l1 y x := by
  unfold l1
  omega

theorem l1_triangle (x y z : Site L) : l1 x z ≤ l1 x y + l1 y z := by
  unfold l1
  omega

theorem l1_self (x : Site L) : l1 x x = 0 := by
  simp [l1]

/-- A free-square edge is a lattice step. -/
theorem l1_freeEdge (e : SquareFreeEdge L) : l1 e.1.1 e.1.2 = 1 := by
  obtain ⟨-, h⟩ := e.2
  set a := |((e.1.1.1 : ℕ) : ℤ) - (e.1.2.1 : ℕ)|
  set b := |((e.1.1.2 : ℕ) : ℤ) - (e.1.2.2 : ℕ)|
  have ha : a ∈ ({0, 1} : Finset ℤ) := h ▸ by simp
  have hb : b ∈ ({0, 1} : Finset ℤ) := h ▸ by simp
  have h0 : (0 : ℤ) ∈ ({a, b} : Finset ℤ) := h.symm ▸ by simp
  have h1 : (1 : ℤ) ∈ ({a, b} : Finset ℤ) := h.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb h0 h1
  have hsum : a + b = 1 := by omega
  unfold l1
  have e1 : (Int.natAbs (((e.1.1.1 : ℕ) : ℤ) - (e.1.2.1 : ℕ)) : ℤ) = a := Int.natCast_natAbs _
  have e2 : (Int.natAbs (((e.1.1.2 : ℕ) : ℤ) - (e.1.2.2 : ℕ)) : ℤ) = b := Int.natCast_natAbs _
  omega

/-- A `squareZero` edge joining two bounded faces is a lattice step. -/
theorem l1_of_edge {e : SquareZeroBond L} {x y : Site L} (hs : (squareZero L).src e = some x)
    (ht : (squareZero L).tgt e = some y) : l1 x y = 1 := by
  cases e with
  | inl f =>
    simp only [squareZero, Sum.elim_inl, Option.some.injEq] at hs ht
    subst hs ht
    exact l1_freeEdge f
  | inr b => simp [squareZero] at ht

theorem l1_of_adj {x y : Site L} (h : (squareZero L).toSimpleGraph.Adj (some x) (some y)) :
    l1 x y = 1 := by
  rw [Multigraph.toSimpleGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, ⟨e, he | he⟩ | ⟨e, he | he⟩⟩ := h
  · exact l1_of_edge he.1 he.2
  · rw [l1_comm]; exact l1_of_edge he.1 he.2
  · rw [l1_comm]; exact l1_of_edge he.1 he.2
  · exact l1_of_edge he.1 he.2

/-- A walk avoiding the wired root moves at most one `ℓ¹` unit per step. -/
theorem l1_le_length_of_root_free {u v : RotatorDualFace L}
    (w : (squareZero L).toSimpleGraph.Walk u v) (hw : none ∉ w.support) :
    ∀ x y, u = some x → v = some y → l1 x y ≤ w.length := by
  induction w with
  | nil =>
    intro x y hx hy
    rw [hx, Option.some.injEq] at hy
    subst hy
    simp [l1_self]
  | @cons a b c h p ih =>
    intro x y hx hy
    have hb : b ≠ none := fun hb =>
      hw (List.mem_cons_of_mem _ (hb ▸ p.start_mem_support))
    obtain ⟨z, rfl⟩ := Option.ne_none_iff_exists'.mp hb
    have hp : none ∉ p.support := fun h' => hw (List.mem_cons_of_mem _ h')
    subst hx
    have h1 := l1_of_adj h
    have h2 := ih hp z y rfl hy
    have := l1_triangle x z y
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- **Path locality.** A bounded face on a path from the bounded face `a` lies within `ℓ¹`
distance `length` of `a` or of the other endpoint. -/
theorem path_site_local {a : Site L} {b : RotatorDualFace L}
    (w : (squareZero L).toSimpleGraph.Walk (some a) b) (hw : w.IsPath) {y : Site L}
    (hy : some y ∈ w.support) :
    l1 a y ≤ w.length ∨ ∃ b', b = some b' ∧ l1 y b' ≤ w.length := by
  classical
  set p := w.takeUntil (some y) hy
  set q := w.dropUntil (some y) hy
  have hspec : p.append q = w := w.take_spec hy
  have hplen : p.length ≤ w.length := w.length_takeUntil_le_length hy
  have hqlen : q.length ≤ w.length := w.length_dropUntil_le_length hy
  by_cases hp : none ∈ p.support
  · right
    have hnodup : w.support.Nodup := hw.support_nodup
    rw [← hspec, SimpleGraph.Walk.support_append] at hnodup
    have hq : none ∉ q.support := by
      intro hq
      rw [← SimpleGraph.Walk.cons_tail_support] at hq
      rcases List.mem_cons.mp hq with h' | h'
      · exact Option.some_ne_none y h'.symm
      · exact List.disjoint_of_nodup_append hnodup hp h'
    have hb : b ≠ none := fun hb => hq (hb ▸ q.end_mem_support)
    obtain ⟨b', rfl⟩ := Option.ne_none_iff_exists'.mp hb
    exact ⟨b', rfl, (l1_le_length_of_root_free q hq y b' rfl rfl).trans hqlen⟩
  · left
    exact (l1_le_length_of_root_free p hp a y rfl rfl).trans hplen

/-- The free square maps into the wired carrier. -/
def freeToZero (L : ℕ) : (squareFree L).toSimpleGraph →g (squareZero L).toSimpleGraph where
  toFun := some
  map_rel' := by
    intro x y h
    rw [Multigraph.toSimpleGraph, SimpleGraph.fromRel_adj] at h ⊢
    obtain ⟨hne, ⟨e, he | he⟩ | ⟨e, he | he⟩⟩ := h
    all_goals refine ⟨fun h' => hne (Option.some_injective _ h'), ?_⟩
    · exact Or.inl ⟨Sum.inl e, Or.inl ⟨by simp [squareZero, he.1], by simp [squareZero, he.2]⟩⟩
    · exact Or.inl ⟨Sum.inl e, Or.inr ⟨by simp [squareZero, he.1], by simp [squareZero, he.2]⟩⟩
    · exact Or.inr ⟨Sum.inl e, Or.inl ⟨by simp [squareZero, he.1], by simp [squareZero, he.2]⟩⟩
    · exact Or.inr ⟨Sum.inl e, Or.inr ⟨by simp [squareZero, he.1], by simp [squareZero, he.2]⟩⟩

/-- Graph distance between bounded faces is at most their `ℓ¹` distance. -/
theorem dist_some_le_l1 (x y : Site L) :
    (squareZero L).toSimpleGraph.dist (some x) (some y) ≤ l1 x y := by
  have hfree := freeDistance_le_coordinateSum L x y
  have hconv : (if x.1.val ≤ y.1.val then y.1.val - x.1.val else x.1.val - y.1.val) +
      (if x.2.val ≤ y.2.val then y.2.val - x.2.val else x.2.val - y.2.val) = l1 x y := by
    unfold l1
    split_ifs <;> omega
  rw [hconv] at hfree
  by_cases hr : (squareFree L).toSimpleGraph.Reachable x y
  · obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
    have := SimpleGraph.dist_le (w.map (freeToZero L))
    rw [SimpleGraph.Walk.length_map, hw] at this
    exact this.trans (by simpa [latticeDistance] using hfree)
  · by_cases hxy : x = y
    · subst hxy; simp
    · -- in a disconnected free square (`L ≤ 1`) all sites coincide
      exfalso
      apply hxy
      have hL : L ≤ 1 := by
        by_contra hL
        exact hr ((squareFree_connected L (by omega)).preconnected x y)
      exact Prod.ext (Fin.ext (by have := x.1.isLt; have := y.1.isLt; omega))
        (Fin.ext (by have := x.2.isLt; have := y.2.isLt; omega))

/-- Every bounded face meets at most four `squareZero` edges. -/
theorem card_incident_le_four (m : Site L) :
    (Finset.univ.filter fun e : SquareZeroBond L =>
      (squareZero L).src e = some m ∨ (squareZero L).tgt e = some m).card ≤ 4 := by
  classical
  have hdeg : squareZeroFreeDegree L m ≤ 4 := by
    have h1 := wiredInteriorIncidentEdge_card L m
    have h2 := Fintype.card_congr (wiredInteriorIncidentEquiv L m)
    have h3 : Fintype.card (WiredInteriorIncidentWithin L m) ≤ Fintype.card (WiredIncidentEdge L m) :=
      Fintype.card_subtype_le _
    have h4 : Fintype.card (WiredIncidentEdge L m) = 4 :=
      Fintype.card_congr (wiredBoxIncidentEdgeEquiv L m).symm
    omega
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp only [squareZero, Sum.elim_inl, Sum.elim_inr, Option.some.injEq, reduceCtorEq, or_false]
  rw [Fintype.sum_sigma]
  have hfree : (∑ f : SquareFreeEdge L,
      if (squareFree L).src f = m ∨ (squareFree L).tgt f = m then 1 else 0) =
      squareZeroFreeDegree L m := by
    rw [← Finset.card_filter]
    rfl
  rw [hfree]
  have hbd : (∑ j : Fin L × Fin L, ∑ _i : Fin (4 - (Finset.univ.filter fun e : SquareFreeEdge L =>
      (squareFree L).src e = j ∨ (squareFree L).tgt e = j).card), if j = m then 1 else 0) =
      4 - squareZeroFreeDegree L m := by
    rw [Finset.sum_eq_single m (fun j _ hj => by simp [hj]) (by simp)]
    simp [squareZeroFreeDegree]
  rw [hbd]
  omega

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
