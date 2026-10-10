/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.TreeGauge
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Order

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Poisson

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace RootedTreeGauge

/-- The incoming-minus-outgoing divergence of a chord field at a vertex. -/
def chordDivergence {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R) (v : V) : R :=
  (∑ c : T.Chord, if T.edgeTarget c.1 = v then q c else 0) -
    ∑ c : T.Chord, if T.edgeSource c.1 = v then q c else 0

/-- Children of a vertex in the selected rooted tree. -/
abbrev children (T : RootedTreeGauge V E) (v : V) :=
  {w : {x : V // x ≠ T.root} // T.parent w.1 = v}

/-- The unique tree current that cancels a prescribed chord
divergence. The recursion sums the currents entering from the child subtrees. -/
noncomputable def treeCurrent {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R) : V → R
  | v => if _hv : v = T.root then 0 else
      -chordDivergence T q v +
        ∑ w : T.children v, treeCurrent T q w.1.1
termination_by v => T.height - T.depth v
decreasing_by
  have hdepth := T.depth_parent w.1.property
  rw [w.property] at hdepth
  have hw := T.depth_le_height w.1.1
  have hinc : T.depth v < T.depth w.1.1 := by omega
  have htop : T.depth v < T.height := lt_of_lt_of_le hinc hw
  exact Nat.sub_lt_sub_left htop hinc


theorem treeCurrent_eq {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R)
    {v : V} (hv : v ≠ T.root) :
    treeCurrent T q v = -chordDivergence T q v +
      ∑ w : T.children v, treeCurrent T q w.1.1 := by
  rw [treeCurrent]
  simp [hv]

/-- Extend a chord current by its uniquely determined tree current. -/
noncomputable def cycleExtension {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R) : E → R :=
  fun e => match edgeSplitEquiv T e with
    | Sum.inl c => q c
    | Sum.inr x => treeCurrent T q x.1

omit [Fintype V] [Fintype E] in
@[simp] theorem edgeSplit_treeEdge (T : RootedTreeGauge V E)
    (x : {x : V // x ≠ T.root}) :
    edgeSplitEquiv T (T.treeEdge x) = Sum.inr x := by
  have h := (edgeSplitEquiv T).apply_symm_apply (Sum.inr x)
  simpa using h

omit [Fintype V] [Fintype E] in
@[simp] theorem edgeSplit_chord (T : RootedTreeGauge V E) (c : T.Chord) :
    edgeSplitEquiv T c.1 = Sum.inl c := by
  have h := (edgeSplitEquiv T).apply_symm_apply (Sum.inl c)
  simpa using h

@[simp] theorem cycleExtension_treeEdge {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R) (x : {x : V // x ≠ T.root}) :
    cycleExtension T q (T.treeEdge x) = treeCurrent T q x.1 := by
  simp [cycleExtension]

@[simp] theorem cycleExtension_chord {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R) (c : T.Chord) :
    cycleExtension T q c.1 = q c := by
  simp [cycleExtension]

/-- Incoming-minus-outgoing incidence divergence of an integer edge field. -/
def divergence {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (j : E → R) (v : V) : R :=
  (∑ e : E, if T.edgeTarget e = v then j e else 0) -
    ∑ e : E, if T.edgeSource e = v then j e else 0

/-- Co-closed edge fields, with the ground divergence determined by total
conservation. -/
def CoClosed {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (j : E → R) : Prop :=
  ∀ v, v ≠ T.root → divergence T j v = 0

/-- Discrete integration by parts for the chosen edge orientation. -/
theorem pairing_coboundary_eq_sum_divergence (T : RootedTreeGauge V E)
    (j : E → ℝ) (p : V → ℝ) :
    (∑ e : E, j e * T.coboundary p e) =
      ∑ v : V, p v * divergence T j v := by
  classical
  have htarget : (∑ e : E, j e * p (T.edgeTarget e)) =
      ∑ v : V, p v * ∑ e : E, if T.edgeTarget e = v then j e else 0 := by
    calc
      _ = ∑ e : E, ∑ v : V,
          if T.edgeTarget e = v then j e * p v else 0 := by
            congr 1
            funext e
            simp
      _ = ∑ v : V, ∑ e : E,
          if T.edgeTarget e = v then j e * p v else 0 := by
            rw [Finset.sum_comm]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e he
            by_cases h : T.edgeTarget e = v <;> simp [h, mul_comm]
  have hsource : (∑ e : E, j e * p (T.edgeSource e)) =
      ∑ v : V, p v * ∑ e : E, if T.edgeSource e = v then j e else 0 := by
    calc
      _ = ∑ e : E, ∑ v : V,
          if T.edgeSource e = v then j e * p v else 0 := by
            congr 1
            funext e
            simp
      _ = ∑ v : V, ∑ e : E,
          if T.edgeSource e = v then j e * p v else 0 := by
            rw [Finset.sum_comm]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e he
            by_cases h : T.edgeSource e = v <;> simp [h, mul_comm]
  unfold RootedTreeGauge.coboundary divergence
  calc
    _ = ∑ e : E, (j e * p (T.edgeTarget e) -
        j e * p (T.edgeSource e)) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [mul_sub]
    _ = (∑ e : E, j e * p (T.edgeTarget e)) -
        ∑ e : E, j e * p (T.edgeSource e) := by rw [Finset.sum_sub_distrib]
    _ = (∑ v : V, p v * ∑ e : E,
          if T.edgeTarget e = v then j e else 0) -
        ∑ v : V, p v * ∑ e : E,
          if T.edgeSource e = v then j e else 0 := by rw [htarget, hsource]
    _ = ∑ v : V, p v *
        ((∑ e : E, if T.edgeTarget e = v then j e else 0) -
          ∑ e : E, if T.edgeSource e = v then j e else 0) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro v hv
          rw [mul_sub]

/-- Orthogonality to all real coboundaries, the inner-product form of
co-closedness. -/
def OrthogonalToCoboundaries (T : RootedTreeGauge V E) (j : E → ℝ) : Prop :=
  ∀ p : V → ℝ, ∑ e : E, j e * T.coboundary p e = 0

/-- For this finite incidence graph, vanishing divergence away from the
ground vertex is equivalent to orthogonality to gradients. -/
theorem coClosed_iff_orthogonalToCoboundaries (T : RootedTreeGauge V E)
    (j : E → ℝ) : CoClosed T j ↔ OrthogonalToCoboundaries T j := by
  constructor
  · intro hj p
    let q : V → ℝ := fun v => p v - p T.root
    have hcob : T.coboundary q = T.coboundary p := by
      funext e
      simp [q, RootedTreeGauge.coboundary]
    rw [← hcob, pairing_coboundary_eq_sum_divergence]
    apply Finset.sum_eq_zero
    intro v hv
    by_cases hroot : v = T.root
    · simp [q, hroot]
    · simp [q, hj v hroot]
  · intro hj v hv
    have h := hj (Pi.single v (1 : ℝ))
    rw [pairing_coboundary_eq_sum_divergence] at h
    simpa [divergence, Pi.single_apply, hv] using h

private theorem sum_edges_split {R : Type*} [AddCommMonoid R]
    (T : RootedTreeGauge V E) (f : E → R) :
    (∑ e : E, f e) =
      (∑ c : T.Chord, f c.1) +
        ∑ x : {x : V // x ≠ T.root}, f (T.treeEdge x) := by
  classical
  calc
    (∑ e : E, f e) =
        ∑ s : T.Chord ⊕ {x : V // x ≠ T.root}, f ((edgeSplitEquiv T).symm s) :=
          (Equiv.sum_comp (edgeSplitEquiv T).symm f).symm
    _ = _ := by
          rw [Fintype.sum_sum_type]
          simp

omit [Fintype E] in
private theorem incoming_tree_values (T : RootedTreeGauge V E)
    {R : Type*} [AddCommMonoid R] (J : {x : V // x ≠ T.root} → R)
    {v : V} (hv : v ≠ T.root) :
    (∑ x : {x : V // x ≠ T.root},
      if x.1 = v then J x else 0) = J ⟨v, hv⟩ := by
  classical
  let xv : {x : V // x ≠ T.root} := ⟨v, hv⟩
  have heq (x : {x : V // x ≠ T.root}) : x.1 = v ↔ x = xv := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp [heq, xv]

private theorem incoming_tree_current {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R) {v : V} (hv : v ≠ T.root) :
    (∑ x : {x : V // x ≠ T.root},
      if x.1 = v then treeCurrent T q x.1 else 0) = treeCurrent T q v := by
  simpa using incoming_tree_values T (fun x => treeCurrent T q x.1) hv

omit [Fintype E] in
private theorem outgoing_tree_values (T : RootedTreeGauge V E)
    {R : Type*} [AddCommMonoid R] (J : {x : V // x ≠ T.root} → R) (v : V) :
    (∑ x : {x : V // x ≠ T.root},
      if T.parent x.1 = v then J x else 0) =
      ∑ w : T.children v, J w.1 := by
  classical
  let p : {x : V // x ≠ T.root} → Prop := fun x => T.parent x.1 = v
  let f : {x : V // x ≠ T.root} → R := fun x =>
    if p x then J x else 0
  have hfirst : (∑ x : T.children v, f x.1) =
      ∑ x : T.children v, J x.1 := by
    apply Fintype.sum_congr
    intro x
    simp [f, p, x.property]
  have hsecond :
      (∑ x : {x : {x : V // x ≠ T.root} // ¬p x}, f x.1) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [f, x.property]
  have hsum := Fintype.sum_subtype_add_sum_subtype p f
  change (∑ x : T.children v, f x.1) +
      (∑ x : {x : {x : V // x ≠ T.root} // ¬p x}, f x.1) =
      (∑ x : {x : V // x ≠ T.root}, f x) at hsum
  rw [hfirst, hsecond] at hsum
  simpa [f, p] using hsum.symm

omit [Fintype V] [Fintype E] in
private theorem child_measure_lt (T : RootedTreeGauge V E) {v : V}
    (w : T.children v) :
    T.height - T.depth w.1.1 < T.height - T.depth v := by
  have hdepth := T.depth_parent w.1.property
  rw [w.property] at hdepth
  have hw := T.depth_le_height w.1.1
  have hinc : T.depth v < T.depth w.1.1 := by omega
  have htop : T.depth v < T.height := lt_of_lt_of_le hinc hw
  exact Nat.sub_lt_sub_left htop hinc

/-- The bottom-up recurrence uniquely determines the integer tree current. -/
theorem treeCurrent_unique {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R)
    (J : {x : V // x ≠ T.root} → R)
    (hJ : ∀ x, J x = -chordDivergence T q x.1 +
      ∑ w : T.children x.1, J w.1) :
    ∀ x, J x = treeCurrent T q x.1 := by
  have hmain : ∀ n, ∀ x : {x : V // x ≠ T.root},
      T.height - T.depth x.1 = n → J x = treeCurrent T q x.1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hx
        rw [hJ x, treeCurrent_eq T q x.property]
        congr 1
        apply Fintype.sum_congr
        intro w
        apply ih (T.height - T.depth w.1.1) ?_ w.1 rfl
        rw [← hx]
        exact child_measure_lt T w
  intro x
  exact hmain _ x rfl

/-- Co-closed integer edge fields, with the ground potential fixed at zero. -/
private theorem coClosed_treeRecurrence (T : RootedTreeGauge V E)
    {R : Type*} [AddCommGroup R] (j : E → R) (hj : CoClosed T j)
    (v : V) (hv : v ≠ T.root) :
    j (T.treeEdge ⟨v, hv⟩) =
      -chordDivergence T (T.restrictChord j) v +
        ∑ w : T.children v, j (T.treeEdge w.1) := by
  classical
  have hin :
      (∑ e : E, if T.edgeTarget e = v then j e else 0) =
        (∑ c : T.Chord, if T.edgeTarget c.1 = v then j c.1 else 0) +
          j (T.treeEdge ⟨v, hv⟩) := by
    rw [sum_edges_split T (fun e => if T.edgeTarget e = v then j e else 0)]
    simp only [T.treeEdge_target]
    rw [incoming_tree_values T (fun x => j (T.treeEdge x)) hv]
  have hout :
      (∑ e : E, if T.edgeSource e = v then j e else 0) =
        (∑ c : T.Chord, if T.edgeSource c.1 = v then j c.1 else 0) +
          ∑ w : T.children v, j (T.treeEdge w.1) := by
    rw [sum_edges_split T (fun e => if T.edgeSource e = v then j e else 0)]
    simp only [T.treeEdge_source]
    rw [outgoing_tree_values T (fun x => j (T.treeEdge x)) v]
  have hdiv := hj v hv
  unfold divergence at hdiv
  rw [hin, hout] at hdiv
  simp only [chordDivergence, restrictChord] at hdiv ⊢
  let u : R := ∑ c : T.Chord, if T.edgeTarget c.1 = v then j c.1 else 0
  let d : R := ∑ c : T.Chord, if T.edgeSource c.1 = v then j c.1 else 0
  have hsum : u + j (T.treeEdge ⟨v, hv⟩) =
      d + ∑ w : T.children v, j (T.treeEdge w.1) := by
    simpa [u, d] using sub_eq_zero.mp hdiv
  calc
    j (T.treeEdge ⟨v, hv⟩) = -u + (u + j (T.treeEdge ⟨v, hv⟩)) := by abel
    _ = -u + (d + ∑ w : T.children v, j (T.treeEdge w.1)) := by rw [hsum]
    _ = -(u - d) + ∑ w : T.children v, j (T.treeEdge w.1) := by abel

theorem divergence_cycleExtension_eq_zero {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R) {v : V} (hv : v ≠ T.root) :
    divergence T (cycleExtension T q) v = 0 := by
  classical
  have hin :
      (∑ e : E, if T.edgeTarget e = v then cycleExtension T q e else 0) =
        (∑ c : T.Chord, if T.edgeTarget c.1 = v then q c else 0) +
          treeCurrent T q v := by
    rw [sum_edges_split T (fun e =>
      if T.edgeTarget e = v then cycleExtension T q e else 0)]
    simp only [cycleExtension_chord, cycleExtension_treeEdge, T.treeEdge_target]
    rw [incoming_tree_current T q hv]
  have hout :
      (∑ e : E, if T.edgeSource e = v then cycleExtension T q e else 0) =
        (∑ c : T.Chord, if T.edgeSource c.1 = v then q c else 0) +
          ∑ w : T.children v, treeCurrent T q w.1.1 := by
    rw [sum_edges_split T (fun e =>
      if T.edgeSource e = v then cycleExtension T q e else 0)]
    simp only [cycleExtension_chord, cycleExtension_treeEdge, T.treeEdge_source]
    simpa using outgoing_tree_values T (fun x => treeCurrent T q x.1) v
  rw [divergence, hin, hout, treeCurrent_eq T q hv]
  unfold chordDivergence
  abel_nf

theorem cycleExtension_isCoClosed {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R) : CoClosed T (cycleExtension T q) := by
  intro v hv
  exact divergence_cycleExtension_eq_zero T q hv

theorem restrict_cycleExtension {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) (q : T.Chord → R) :
    T.restrictChord (cycleExtension T q) = q := by
  funext c
  simp [RootedTreeGauge.restrictChord]

theorem cycleExtension_restrict_of_coClosed {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) {j : E → R} (hj : CoClosed T j) :
    cycleExtension T (T.restrictChord j) = j := by
  classical
  let q := T.restrictChord j
  have htree : ∀ x : {x : V // x ≠ T.root},
      j (T.treeEdge x) = treeCurrent T q x.1 := by
    apply treeCurrent_unique T q (fun x => j (T.treeEdge x))
    intro x
    simpa [q] using coClosed_treeRecurrence T j hj x.1 x.property
  funext e
  cases hsplit : (edgeSplitEquiv T) e with
  | inl c =>
      have hinv := (edgeSplitEquiv T).symm_apply_apply e
      rw [hsplit] at hinv
      have he : c.1 = e := by simpa using hinv
      rw [← he]
      simp [cycleExtension, RootedTreeGauge.restrictChord]
  | inr x =>
      have hinv := (edgeSplitEquiv T).symm_apply_apply e
      rw [hsplit] at hinv
      have he : T.treeEdge x = e := by simpa using hinv
      rw [← he]
      simpa using (htree x).symm

/-- Integral circulations are in bijection with integer chord data. This is
the graph's fundamental-cycle lattice duality, constructed by an integer
bottom-up solve on the rooted tree. -/
noncomputable def circulationEquiv {R : Type*} [AddCommGroup R]
    (T : RootedTreeGauge V E) :
    (T.Chord → R) ≃ {j : E → R // CoClosed T j} where
  toFun q := ⟨cycleExtension T q, cycleExtension_isCoClosed T q⟩
  invFun j := T.restrictChord j.1
  left_inv q := restrict_cycleExtension T q
  right_inv j := by
    apply Subtype.ext
    exact cycleExtension_restrict_of_coClosed T j.2

/-- Pairing a tree-gauge representative with an integral circulation only
uses the chord coordinates. -/
theorem pairing_eq_chordPairing {R : Type*} [CommRing R]
    (T : RootedTreeGauge V E) {a : E → R} (ha : InTreeGauge T a)
    (j : {j : E → R // CoClosed T j}) :
    (∑ e : E, j.1 e * a e) =
      ∑ c : T.Chord, j.1 c.1 * a c.1 := by
  classical
  rw [sum_edges_split T (fun e => j.1 e * a e)]
  have htree :
      (∑ x : {x : V // x ≠ T.root}, j.1 (T.treeEdge x) * a (T.treeEdge x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [ha x]
  rw [htree, add_zero]

end RootedTreeGauge

end FroehlichSpencer.FS82.Poisson
