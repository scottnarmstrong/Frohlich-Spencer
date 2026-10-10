/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Renormalization3

/-!
# the conflict neighbourhood of a set of dual links in three dimensions

Two dual links that lie in one dual plaquette have base points at coordinate distance at most
one, so the collision relation `Expansion3.currentNear` of the current expansion is contained in
`Expansion3.linkBaseNear`.

A dual link is determined by its direction and its base point.

Hence a
link has at most `3 · 3³ = 81` neighbours, itself included, and the conflict neighbourhood of a
set `P` has at most `81 |P|` links.

This is the count `N₁(supp ϱ)` of FS82 (4.31) ii).
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.XY.Renormalization3

variable {B : Dual3Box}

/-- A dual link is determined by its direction and its base point. -/
theorem link_ext_of_direction_base {e f : Dual3Links B}
    (hd : linkDirection e = linkDirection f)
    (hb : ∀ i, Expansion3.linkBaseCoordinate e i = Expansion3.linkBaseCoordinate f i) :
    e = f := by
  apply Subtype.ext
  funext i
  have h := hb i
  unfold Expansion3.linkBaseCoordinate at h
  by_cases hi : i = linkDirection e
  · have he : (e.1 i).isRight = true := (linkCoord_isRight_iff e i).mpr hi
    have hf : (f.1 i).isRight = true := (linkCoord_isRight_iff f i).mpr (hi.trans hd)
    cases hei : e.1 i with
    | inl v => simp [hei] at he
    | inr v =>
      cases hfi : f.1 i with
      | inl w => simp [hfi] at hf
      | inr w =>
        rw [hei, hfi] at h
        exact congrArg Sum.inr (Fin.ext h)
  · obtain ⟨v, hv⟩ := linkCoord_isLeft_of_ne_direction e hi
    obtain ⟨w, hw⟩ := linkCoord_isLeft_of_ne_direction f (fun h => hi (h.trans hd.symm))
    rw [hv, hw] at h ⊢
    exact congrArg Sum.inl (Fin.ext (by simpa using h))

theorem incident_update_form {e : Dual3Links B} {p : Dual3Plaquettes B}
    (he : Expansion3.dual3LinkIncidentPlaquette e p) :
    ∃ (i : Fin 3) (v : Fin (B i)) (a : Fin (B i + 1)), e.1 i = Sum.inl v ∧
      (a.val = v.val + 1 ∨ a.val = v.val) ∧ p.1 = Function.update e.1 i (Sum.inr a) := by
  obtain ⟨i, v, hiv, hp | hp⟩ := he
  · exact ⟨i, v, _, hiv, Or.inl rfl, hp⟩
  · exact ⟨i, v, _, hiv, Or.inr rfl, hp⟩

/-- Two links of one dual plaquette have base points at coordinate distance at most one. -/
theorem linkBaseNear_of_sharedPlaquette {e f : Dual3Links B} (p : Dual3Plaquettes B)
    (he : Expansion3.dual3LinkIncidentPlaquette e p)
    (hf : Expansion3.dual3LinkIncidentPlaquette f p) :
    Expansion3.linkBaseNear e f := by
  obtain ⟨i, v, a, hiv, ha, hpe⟩ := incident_update_form he
  obtain ⟨j, w, b, hjw, hb, hpf⟩ := incident_update_form hf
  intro k
  have hk := congrFun (hpe.symm.trans hpf) k
  unfold Expansion3.linkBaseCoordinate
  by_cases hki : k = i
  · subst hki
    by_cases hkj : k = j
    · subst hkj
      rw [Function.update_self, Function.update_self] at hk
      have hab : a = b := Sum.inr.inj hk
      rw [hiv, hjw]
      have : a.val = b.val := congrArg Fin.val hab
      constructor <;> simp only <;> omega
    · rw [Function.update_self, Function.update_of_ne hkj] at hk
      rw [hiv, ← hk]
      constructor <;> simp only <;> omega
  · by_cases hkj : k = j
    · subst hkj
      rw [Function.update_of_ne hki, Function.update_self] at hk
      rw [hjw, hk]
      constructor <;> simp only <;> omega
    · rw [Function.update_of_ne hki, Function.update_of_ne hkj] at hk
      rw [hk]
      constructor <;> omega

theorem currentNear_imp_linkBaseNear {e f : Dual3Links B} (h : Expansion3.currentNear e f) :
    Expansion3.linkBaseNear e f := by
  rcases h with h | ⟨p, he, hf⟩
  · exact h
  · exact linkBaseNear_of_sharedPlaquette p he hf

theorem linkBaseNear_refl (e : Dual3Links B) : Expansion3.linkBaseNear e e :=
  fun _ => ⟨Nat.le_succ _, Nat.le_succ _⟩

/-- The code of a link relative to a base link: its direction and its base-point offsets. -/
noncomputable def nearCode (e f : Dual3Links B) : Fin 3 × (Fin 3 → Fin 3) :=
  (linkDirection f, fun i =>
    ⟨(Expansion3.linkBaseCoordinate f i + 1 - Expansion3.linkBaseCoordinate e i) % 3,
      Nat.mod_lt _ (by norm_num)⟩)

open Classical in
/-- A dual link has at most `81` base-point neighbours. -/
theorem card_linkBaseNear_le (e : Dual3Links B) :
    (Finset.univ.filter fun f : Dual3Links B => Expansion3.linkBaseNear f e).card ≤ 81 := by
  classical
  have hcard : Fintype.card (Fin 3 × (Fin 3 → Fin 3)) = 81 := by
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (nearCode e) (fun _ _ => Finset.mem_univ _) ?_
  intro f hf g hg hcode
  have hfn : Expansion3.linkBaseNear f e := (Finset.mem_filter.mp hf).2
  have hgn : Expansion3.linkBaseNear g e := (Finset.mem_filter.mp hg).2
  have hdir : linkDirection f = linkDirection g := congrArg Prod.fst hcode
  refine link_ext_of_direction_base hdir fun i => ?_
  have hi := congrArg Fin.val (congrFun (congrArg Prod.snd hcode) i)
  simp only [nearCode] at hi
  have h1 := hfn i
  have h2 := hgn i
  omega

/-- **The conflict neighbourhood of a set of dual links has at most `81` times its size.** -/
theorem card_activityNeighborhood_le (P : Finset (Dual3Links B)) :
    (ActivityLineage.activityNeighborhood Finset.univ P Expansion3.currentNear).card ≤
      81 * P.card := by
  classical
  have hsub : ActivityLineage.activityNeighborhood Finset.univ P Expansion3.currentNear ⊆
      P.biUnion fun p => Finset.univ.filter fun f : Dual3Links B =>
        Expansion3.linkBaseNear f p := by
    intro q hq
    simp only [ActivityLineage.activityNeighborhood, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hq with hq | ⟨p, hp, hnear⟩
    · exact ⟨q, hq, linkBaseNear_refl q⟩
    · exact ⟨p, hp, currentNear_imp_linkBaseNear hnear⟩
  calc (ActivityLineage.activityNeighborhood Finset.univ P Expansion3.currentNear).card
      ≤ (P.biUnion fun p => Finset.univ.filter fun f : Dual3Links B =>
          Expansion3.linkBaseNear f p).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, (Finset.univ.filter fun f : Dual3Links B =>
          Expansion3.linkBaseNear f p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, 81 := Finset.sum_le_sum fun p _ => card_linkBaseNear_le p
    _ = 81 * P.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end FroehlichSpencer.FS82.XY

end
