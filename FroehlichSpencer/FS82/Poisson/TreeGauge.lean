/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-!
# Tree gauge on a rooted finite incidence graph

The rooted tree is presented by its parent map and depth.  This is the
combinatorial spanning-tree input; all normalization and uniqueness claims
below are proved from it.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

universe u v

variable {V : Type u} {E : Type v}
variable [DecidableEq V] [DecidableEq E]

/-- A finite oriented graph with a chosen rooted spanning tree.  Each
non-root vertex labels exactly one tree link, oriented from its parent to the
vertex. -/
structure RootedTreeGauge (V E : Type*) [DecidableEq V] [DecidableEq E] where
  root : V
  parent : V → V
  depth : V → ℕ
  /-- A finite recursion bound for the tree depth. -/
  height : ℕ
  depth_le_height : ∀ x, depth x ≤ height
  edgeSource : E → V
  edgeTarget : E → V
  treeEdge : {x : V // x ≠ root} → E
  treeEdge_injective : Function.Injective treeEdge
  treeEdge_source (x : {x : V // x ≠ root}) : edgeSource (treeEdge x) = parent x
  treeEdge_target (x : {x : V // x ≠ root}) : edgeTarget (treeEdge x) = x
  depth_root : depth root = 0
  depth_pos {x : V} (hx : x ≠ root) : 0 < depth x
  depth_parent {x : V} (hx : x ≠ root) : depth (parent x) + 1 = depth x

namespace RootedTreeGauge

/-- The coboundary of a vertex potential on an oriented link. -/
def coboundary (T : RootedTreeGauge V E) {R : Type*} [AddGroup R]
    (p : V → R) (e : E) : R :=
  p (T.edgeTarget e) - p (T.edgeSource e)

/-- Integrate an edge field along the rooted tree. The root potential is zero. -/
noncomputable def treePotential (T : RootedTreeGauge V E) {R : Type*}
    [AddGroup R] (a : E → R) : V → R :=
  fun x => if hx : x = T.root then 0 else
    a (T.treeEdge ⟨x, hx⟩) + treePotential T a (T.parent x)
termination_by x => T.depth x
decreasing_by
  have hdepth := T.depth_parent (by assumption)
  omega

@[simp] theorem treePotential_root (T : RootedTreeGauge V E) {R : Type*}
    [AddGroup R] (a : E → R) :
    treePotential T a T.root = 0 := by
  rw [treePotential.eq_1 T a T.root]
  simp

theorem treePotential_parent (T : RootedTreeGauge V E) {R : Type*}
    [AddGroup R] (a : E → R)
    {x : V} (hx : x ≠ T.root) :
  treePotential T a x = a (T.treeEdge ⟨x, hx⟩) +
      treePotential T a (T.parent x) := by
  rw [treePotential.eq_1 T a x]
  simp [hx]

/-- Integrating along the tree recovers every field on a tree edge. -/
theorem treePotential_coboundary_treeEdge (T : RootedTreeGauge V E)
    {R : Type*} [AddGroup R]
    (a : E → R) (x : {x : V // x ≠ T.root}) :
    T.coboundary (treePotential T a) (T.treeEdge x) = a (T.treeEdge x) := by
  simp only [coboundary, T.treeEdge_target, T.treeEdge_source]
  rw [treePotential_parent T a x.property]
  exact add_sub_cancel_right _ _

/-- If a potential has zero coboundary on each rooted-tree edge, it is
constant on every vertex. -/
theorem potential_constant_of_tree_zero (T : RootedTreeGauge V E)
    {R : Type*} [AddGroup R] (p : V → R)
    (hp : ∀ x : {x : V // x ≠ T.root},
      T.coboundary p (T.treeEdge x) = 0) :
    ∀ x, p x = p T.root := by
  have hdepth : ∀ n, ∀ x, T.depth x = n → p x = p T.root := by
    intro n
    induction n with
    | zero =>
        intro x hx
        by_cases hroot : x = T.root
        · simp [hroot]
        · have hpos := T.depth_pos hroot
          omega
    | succ n ih =>
        intro x hx
        by_cases hroot : x = T.root
        · simp [hroot]
        · have hparent := T.depth_parent hroot
          have hparentDepth : T.depth (T.parent x) = n := by omega
          have hrec := ih (T.parent x) hparentDepth
          have hedge := hp ⟨x, hroot⟩
          have hzero : p x - p (T.parent x) = 0 := by
            simpa [coboundary, T.treeEdge_target, T.treeEdge_source] using hedge
          exact (sub_eq_zero.mp hzero).trans hrec
  intro x
  exact hdepth (T.depth x) x rfl

/-- A field is in tree gauge when it vanishes on the selected tree links. -/
def InTreeGauge (T : RootedTreeGauge V E) {R : Type*} [Zero R]
    (a : E → R) : Prop :=
  ∀ x : {x : V // x ≠ T.root}, a (T.treeEdge x) = 0

/-- The unique representative obtained by subtracting the rooted tree
potential. -/
noncomputable def normalize (T : RootedTreeGauge V E) (a : E → ℤ) : E → ℤ :=
  fun e => a e - T.coboundary (treePotential T a) e

theorem normalize_mem (T : RootedTreeGauge V E) {a : E → ℤ} :
    InTreeGauge T (normalize T a) := by
  intro x
  simp [normalize, treePotential_coboundary_treeEdge]

/-- Integer gauge equivalence with the ground potential fixed to zero. -/
def GaugeEquivalent (T : RootedTreeGauge V E) (a b : E → ℤ) : Prop :=
  ∃ p : V → ℤ, p T.root = 0 ∧ ∀ e, b e = a e - T.coboundary p e

theorem normalize_gaugeEquivalent (T : RootedTreeGauge V E) (a : E → ℤ) :
    GaugeEquivalent T a (normalize T a) := by
  refine ⟨treePotential T a, treePotential_root T a, ?_⟩
  intro e
  rfl

private theorem treeConstant_of_tree_coboundary_zero (T : RootedTreeGauge V E)
    (p : V → ℤ)
    (hp : ∀ x : {x : V // x ≠ T.root},
      T.coboundary p (T.treeEdge x) = 0) :
    ∀ x, p x = p T.root := by
  have hdepth : ∀ n, ∀ x, T.depth x = n → p x = p T.root := by
    intro n
    induction n with
    | zero =>
        intro x hx
        by_cases hroot : x = T.root
        · simp [hroot]
        · have hpos := T.depth_pos hroot
          omega
    | succ n ih =>
        intro x hx
        by_cases hroot : x = T.root
        · simp [hroot]
        · have hparent := T.depth_parent hroot
          have hparentDepth : T.depth (T.parent x) = n := by omega
          have hrec := ih (T.parent x) hparentDepth
          have hedge := hp ⟨x, hroot⟩
          simp only [coboundary, T.treeEdge_target, T.treeEdge_source] at hedge
          linarith
  intro x
  exact hdepth (T.depth x) x rfl

/-- A tree-gauge representative is unique in its integer gauge class. -/
theorem normalize_unique (T : RootedTreeGauge V E) {a b : E → ℤ}
    (ha : InTreeGauge T a) (hb : InTreeGauge T b)
    (hab : GaugeEquivalent T a b) : a = b := by
  rcases hab with ⟨p, hpRoot, hp⟩
  have hpTree : ∀ x : {x : V // x ≠ T.root},
      T.coboundary p (T.treeEdge x) = 0 := by
    intro x
    have h := hp (T.treeEdge x)
    rw [ha x, hb x] at h
    omega
  have hconstant := treeConstant_of_tree_coboundary_zero T p hpTree
  funext e
  have hpDiff : T.coboundary p e = 0 := by
    unfold coboundary
    rw [hconstant (T.edgeTarget e), hconstant (T.edgeSource e), hpRoot]
    simp
  rw [hp e, hpDiff]
  simp

/-- Chords are precisely the links omitted by the rooted tree. -/
abbrev Chord (T : RootedTreeGauge V E) :=
  {e : E // e ∉ Set.range T.treeEdge}

/-- Extend integer chord data by zero on the tree. -/
noncomputable def extendChord {R : Type*} [Zero R] (T : RootedTreeGauge V E)
    (x : T.Chord → R) : E → R := by
  classical
  exact fun e => if he : e ∈ Set.range T.treeEdge then 0 else x ⟨e, he⟩

/-- Restrict an edge field to its chord coordinates. -/
def restrictChord {R : Type*} (T : RootedTreeGauge V E) (a : E → R) :
    T.Chord → R := fun e => a e

/-- Split every edge into its unique chord or rooted-tree coordinate. -/
noncomputable def edgeSplitEquiv (T : RootedTreeGauge V E) :
    E ≃ (T.Chord ⊕ {x : V // x ≠ T.root}) := by
  classical
  refine
    { toFun := fun e => if he : e ∈ Set.range T.treeEdge then
        Sum.inr (Classical.choose (show ∃ x, T.treeEdge x = e from he))
      else Sum.inl ⟨e, he⟩
      invFun := fun
        | Sum.inl c => c.1
        | Sum.inr x => T.treeEdge x
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    by_cases he : e ∈ Set.range T.treeEdge
    · simp only [dite_eq_left he]
      exact Classical.choose_spec (show ∃ x, T.treeEdge x = e from he)
    · simp only [dite_eq_right he]
  · intro s
    cases s with
    | inl c =>
        simp only [dite_eq_right c.property]
    | inr x =>
        have he : T.treeEdge x ∈ Set.range T.treeEdge := ⟨x, rfl⟩
        simp only [dite_eq_left he]
        apply congrArg (fun y : {x : V // x ≠ T.root} => Sum.inr y)
        apply Subtype.ext
        exact congrArg Subtype.val <| T.treeEdge_injective <|
          (Classical.choose_spec (show ∃ y, T.treeEdge y = T.treeEdge x from he)).trans rfl.symm

@[simp] theorem edgeSplitEquiv_symm_inl (T : RootedTreeGauge V E)
    (c : T.Chord) : (edgeSplitEquiv T).symm (Sum.inl c) = c.1 := rfl

@[simp] theorem edgeSplitEquiv_symm_inr (T : RootedTreeGauge V E)
    (x : {x : V // x ≠ T.root}) :
    (edgeSplitEquiv T).symm (Sum.inr x) = T.treeEdge x := rfl

/-- Summing a tree-gauge field over all links is the same as summing its
chord coordinates. -/
theorem sum_eq_sum_chords_of_treeGauge (T : RootedTreeGauge V E)
    [Fintype V] [Fintype E] {a : E → ℤ} (ha : InTreeGauge T a) :
    (∑ e : E, a e) = ∑ c : T.Chord, a c.1 := by
  classical
  calc
    (∑ e : E, a e) =
        ∑ s : T.Chord ⊕ {x : V // x ≠ T.root}, a ((edgeSplitEquiv T).symm s) :=
          (Equiv.sum_comp (edgeSplitEquiv T).symm a).symm
    _ = (∑ c : T.Chord, a c.1) +
        ∑ x : {x : V // x ≠ T.root}, a (T.treeEdge x) := by
          rw [Fintype.sum_sum_type]
          simp
    _ = ∑ c : T.Chord, a c.1 := by
          rw [Finset.sum_eq_zero (fun x hx => ha x)]
          simp

theorem restrict_extendChord {R : Type*} [Zero R]
    (T : RootedTreeGauge V E) (x : T.Chord → R) :
    T.restrictChord (T.extendChord x) = x := by
  funext e
  simp [restrictChord, extendChord, e.property]

theorem extend_restrictChord {R : Type*} [Zero R] (T : RootedTreeGauge V E)
    {a : E → R}
    (ha : InTreeGauge T a) :
    T.extendChord (T.restrictChord a) = a := by
  classical
  funext e
  by_cases he : e ∈ Set.range T.treeEdge
  · rcases he with ⟨x, rfl⟩
    simpa [extendChord] using (ha x).symm
  · simp [extendChord, restrictChord, he]

/-- Exact equivalence between integer chord data and tree-gauge fields. -/
noncomputable def chordGaugeEquiv {R : Type*} [Zero R] (T : RootedTreeGauge V E) :
    (T.Chord → R) ≃ {a : E → R // InTreeGauge T a} where
  toFun x := ⟨T.extendChord x, by
    intro y
    classical
    simp [extendChord]⟩
  invFun a := T.restrictChord a
  left_inv := T.restrict_extendChord
  right_inv a := Subtype.ext (T.extend_restrictChord a.property)

end RootedTreeGauge

end FroehlichSpencer.FS82.Poisson
