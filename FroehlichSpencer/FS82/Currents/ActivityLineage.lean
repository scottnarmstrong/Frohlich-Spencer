/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
/- Abstract branch-history arithmetic for the FS82 factor-three activity
bound. Support and activity arithmetic for the Lemma 2 expansion. -/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import FroehlichSpencer.FS82.Currents.Current

/-!
# FS82 current activity lineages

Branch histories record original links, active links, current values, and
factor-three activity multipliers for Lemma 2.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents

inductive ActivityLineage (Cell : Type*) where
  | leaf (cell : Cell)
  | add (left right : ActivityLineage Cell)
  | sub (left right : ActivityLineage Cell)
  | keepLeft (left right : ActivityLineage Cell)
  | keepRight (left right : ActivityLineage Cell)
  deriving DecidableEq, Repr

namespace ActivityLineage

@[expose] def active {Cell : Type*} [DecidableEq Cell] : ActivityLineage Cell → Finset Cell
  | .leaf e => {e}
  | .add l r => active l ∪ active r
  | .sub l r => active l ∪ active r
  | .keepLeft l _ => active l
  | .keepRight _ r => active r

@[expose] def all {Cell : Type*} [DecidableEq Cell] : ActivityLineage Cell → Finset Cell
  | .leaf e => {e}
  | .add l r => all l ∪ all r
  | .sub l r => all l ∪ all r
  | .keepLeft l r => all l ∪ all r
  | .keepRight l r => all l ∪ all r

@[expose] def mergeCount {Cell : Type*} : ActivityLineage Cell → ℕ
  | .leaf _ => 0
  | .add l r => mergeCount l + mergeCount r + 1
  | .sub l r => mergeCount l + mergeCount r + 1
  | .keepLeft l _ => mergeCount l
  | .keepRight _ r => mergeCount r

@[expose] def keepCount {Cell : Type*} : ActivityLineage Cell → ℕ
  | .leaf _ => 0
  | .add l r => keepCount l + keepCount r
  | .sub l r => keepCount l + keepCount r
  | .keepLeft l _ => keepCount l + 1
  | .keepRight _ r => keepCount r + 1

@[expose] def multiplierCount {Cell : Type*} : ActivityLineage Cell → ℕ
  | .leaf _ => 0
  | .add l r => multiplierCount l + multiplierCount r + 1
  | .sub l r => multiplierCount l + multiplierCount r + 1
  | .keepLeft l _ => multiplierCount l + 1
  | .keepRight _ r => multiplierCount r + 1

@[expose] def value {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (q : Cell → ℤ) : ActivityLineage Cell → Cell → ℤ
  | .leaf e => fun x => if x = e then q e else 0
  | .add l r => value q l + value q r
  | .sub l r => value q l - value q r
  | .keepLeft l _ => value q l
  | .keepRight _ r => value q r

@[expose] def coefficient {Cell : Type*} (z : Cell → ℝ) : ActivityLineage Cell → ℝ
  | .leaf e => z e
  | .add l r => 3 * coefficient z l * coefficient z r
  | .sub l r => 3 * coefficient z l * coefficient z r
  | .keepLeft l _ => 3 * coefficient z l
  | .keepRight _ r => 3 * coefficient z r

theorem multiplierCount_eq_merge_add_keep {Cell : Type*}
    (h : ActivityLineage Cell) :
    h.multiplierCount = h.mergeCount + h.keepCount := by
  induction h <;> simp [multiplierCount, mergeCount, keepCount, *] <;> omega

inductive Good {Cell : Type*} [DecidableEq Cell] (near : Cell → Cell → Prop) :
    ActivityLineage Cell → Prop where
  | leaf (e : Cell) : Good near (.leaf e)
  | add {l r : ActivityLineage Cell} (hl : Good near l) (hr : Good near r)
      (hdisj : Disjoint l.all r.all)
      (hbridge : ∃ a ∈ l.active, ∃ b ∈ r.active, near a b) :
      Good near (.add l r)
  | sub {l r : ActivityLineage Cell} (hl : Good near l) (hr : Good near r)
      (hdisj : Disjoint l.all r.all)
      (hbridge : ∃ a ∈ l.active, ∃ b ∈ r.active, near a b) :
      Good near (.sub l r)
  | keepLeft {l r : ActivityLineage Cell} (hl : Good near l) (hr : Good near r)
      (hdisj : Disjoint l.all r.all)
      (hbridge : ∃ a ∈ l.active, ∃ b ∈ r.active, near a b) :
      Good near (.keepLeft l r)
  | keepRight {l r : ActivityLineage Cell} (hl : Good near l) (hr : Good near r)
      (hdisj : Disjoint l.all r.all)
      (hbridge : ∃ a ∈ l.active, ∃ b ∈ r.active, near a b) :
      Good near (.keepRight l r)

@[simp] theorem active_subset_all {Cell : Type*} [DecidableEq Cell]
    (h : ActivityLineage Cell) : h.active ⊆ h.all := by
  induction h with
  | leaf e => simp [active, all]
  | add l r ihl ihr | sub l r ihl ihr =>
      intro x hx
      simp only [active, all, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihl hx)
      · exact Or.inr (ihr hx)
  | keepLeft l r ihl ihr =>
      intro x hx
      exact Finset.mem_union_left _ (ihl hx)
  | keepRight l r ihl ihr =>
      intro x hx
      exact Finset.mem_union_right _ (ihr hx)

theorem currentSupport_value_eq_active {Cell : Type*} [Fintype Cell]
    [DecidableEq Cell] {near : Cell → Cell → Prop}
    {h : ActivityLineage Cell} (hg : Good near h) (q : Cell → ℤ)
    (hq : ∀ e ∈ h.all, q e ≠ 0) :
    currentSupport (value q h) = h.active := by
  induction hg with
  | leaf e =>
      ext x
      simp [value, currentSupport, active, hq e (by simp [all])]
  | @add l r hl hr hdisj hbridge ihl ihr =>
      have hqL : ∀ e ∈ l.all, q e ≠ 0 := by
        intro e he
        exact hq e (by simp [all, he])
      have hqR : ∀ e ∈ r.all, q e ≠ 0 := by
        intro e he
        exact hq e (by simp [all, he])
      have hdisjActive : Disjoint l.active r.active := by
        apply Finset.disjoint_left.mpr
        intro e heL heR
        exact (Finset.disjoint_left.mp hdisj)
          (l.active_subset_all heL) (r.active_subset_all heR)
      change currentSupport (value q l + value q r) = l.active ∪ r.active
      rw [currentSupport_add_disjoint]
      · rw [ihl hqL, ihr hqR]
      · rw [ihl hqL, ihr hqR]
        exact hdisjActive
  | @sub l r hl hr hdisj hbridge ihl ihr =>
      have hqL : ∀ e ∈ l.all, q e ≠ 0 := by
        intro e he
        exact hq e (by simp [all, he])
      have hqR : ∀ e ∈ r.all, q e ≠ 0 := by
        intro e he
        exact hq e (by simp [all, he])
      have hdisjActive : Disjoint l.active r.active := by
        apply Finset.disjoint_left.mpr
        intro e heL heR
        exact (Finset.disjoint_left.mp hdisj)
          (l.active_subset_all heL) (r.active_subset_all heR)
      change currentSupport (value q l - value q r) = l.active ∪ r.active
      rw [currentSupport_sub_disjoint]
      · rw [ihl hqL, ihr hqR]
      · rw [ihl hqL, ihr hqR]
        exact hdisjActive
  | @keepLeft l r hl hr hdisj hbridge ihl ihr =>
      have hqL : ∀ e ∈ l.all, q e ≠ 0 := by
        intro e he
        exact hq e (by simp [all, he])
      change currentSupport (value q l) = l.active
      exact ihl hqL
  | @keepRight l r hl hr hdisj hbridge ihl ihr =>
      have hqR : ∀ e ∈ r.all, q e ≠ 0 := by
        intro e he
        exact hq e (by simp [all, he])
      change currentSupport (value q r) = r.active
      exact ihr hqR

theorem value_abs_eq_input_abs_on_active {Cell : Type*} [Fintype Cell]
    [DecidableEq Cell] {near : Cell → Cell → Prop}
    {h : ActivityLineage Cell} (hg : Good near h) (q : Cell → ℤ)
    (hq : ∀ e ∈ h.all, q e ≠ 0) {e : Cell} (he : e ∈ h.active) :
    |value q h e| = |q e| := by
  induction hg generalizing e with
  | leaf a =>
      have heq : e = a := by simpa [active] using he
      subst e
      simp [value]
  | @add l r hl hr hdisj hbridge ihl ihr =>
      have hqL : ∀ x ∈ l.all, q x ≠ 0 := by
        intro x hx
        exact hq x (by simp [all, hx])
      have hqR : ∀ x ∈ r.all, q x ≠ 0 := by
        intro x hx
        exact hq x (by simp [all, hx])
      have hdisjActive : Disjoint l.active r.active := by
        apply Finset.disjoint_left.mpr
        intro x hxL hxR
        exact (Finset.disjoint_left.mp hdisj)
          (l.active_subset_all hxL) (r.active_subset_all hxR)
      have heCases : e ∈ l.active ∨ e ∈ r.active := by
        simpa [active] using he
      rcases heCases with heL | heR
      · have hzeroR : value q r e = 0 := by
          by_contra hne
          have hmem : e ∈ currentSupport (value q r) := by
            simp [currentSupport, hne]
          rw [currentSupport_value_eq_active hr q hqR] at hmem
          exact (Finset.disjoint_left.mp hdisjActive) heL hmem
        change |value q l e + value q r e| = |q e|
        rw [hzeroR, add_zero]
        exact ihl hqL heL
      · have hzeroL : value q l e = 0 := by
          by_contra hne
          have hmem : e ∈ currentSupport (value q l) := by
            simp [currentSupport, hne]
          rw [currentSupport_value_eq_active hl q hqL] at hmem
          exact (Finset.disjoint_left.mp hdisjActive.symm) heR hmem
        change |value q l e + value q r e| = |q e|
        rw [hzeroL, zero_add]
        exact ihr hqR heR
  | @sub l r hl hr hdisj hbridge ihl ihr =>
      have hqL : ∀ x ∈ l.all, q x ≠ 0 := by
        intro x hx
        exact hq x (by simp [all, hx])
      have hqR : ∀ x ∈ r.all, q x ≠ 0 := by
        intro x hx
        exact hq x (by simp [all, hx])
      have hdisjActive : Disjoint l.active r.active := by
        apply Finset.disjoint_left.mpr
        intro x hxL hxR
        exact (Finset.disjoint_left.mp hdisj)
          (l.active_subset_all hxL) (r.active_subset_all hxR)
      have heCases : e ∈ l.active ∨ e ∈ r.active := by
        simpa [active] using he
      rcases heCases with heL | heR
      · have hzeroR : value q r e = 0 := by
          by_contra hne
          have hmem : e ∈ currentSupport (value q r) := by
            simp [currentSupport, hne]
          rw [currentSupport_value_eq_active hr q hqR] at hmem
          exact (Finset.disjoint_left.mp hdisjActive) heL hmem
        change |value q l e - value q r e| = |q e|
        rw [hzeroR, sub_zero]
        exact ihl hqL heL
      · have hzeroL : value q l e = 0 := by
          by_contra hne
          have hmem : e ∈ currentSupport (value q l) := by
            simp [currentSupport, hne]
          rw [currentSupport_value_eq_active hl q hqL] at hmem
          exact (Finset.disjoint_left.mp hdisjActive.symm) heR hmem
        change |value q l e - value q r e| = |q e|
        rw [hzeroL, zero_sub, abs_neg]
        exact ihr hqR heR
  | @keepLeft l r hl hr hdisj hbridge ihl ihr =>
      have hqL : ∀ x ∈ l.all, q x ≠ 0 := by
        intro x hx
        exact hq x (by simp [all, hx])
      change |value q l e| = |q e|
      exact ihl hqL he
  | @keepRight l r hl hr hdisj hbridge ihl ihr =>
      have hqR : ∀ x ∈ r.all, q x ≠ 0 := by
        intro x hx
        exact hq x (by simp [all, hx])
      change |value q r e| = |q e|
      exact ihr hqR he

theorem Good.active_card_eq_mergeCount_add_one {Cell : Type*} [DecidableEq Cell]
    {near : Cell → Cell → Prop} {h : ActivityLineage Cell} (hg : Good near h) :
    h.active.card = h.mergeCount + 1 := by
  induction hg with
  | leaf e => simp [active, mergeCount]
  | @add l r hl hr hdisj hbridge ihl ihr
  | @sub l r hl hr hdisj hbridge ihl ihr =>
      have hactiveDisj : Disjoint l.active r.active := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (Finset.disjoint_left.mp hdisj) (l.active_subset_all hx) (r.active_subset_all hy)
      rw [active, Finset.card_union_of_disjoint hactiveDisj, mergeCount, ihl, ihr]
      omega
  | @keepLeft l r hl hr hdisj hbridge ihl ihr =>
      simpa [active, mergeCount] using ihl
  | @keepRight l r hl hr hdisj hbridge ihl ihr =>
      simpa [active, mergeCount] using ihr

theorem Good.existsKeepCharges {Cell : Type*} [DecidableEq Cell]
    {near : Cell → Cell → Prop} (hsymm : ∀ a b, near a b → near b a)
    {h : ActivityLineage Cell} (hg : Good near h) :
    ∃ H : Finset Cell,
      H ⊆ h.all ∧ Disjoint H h.active ∧ H.card = h.keepCount ∧
        ∀ q ∈ H, ∃ p ∈ h.active, near q p := by
  induction hg with
  | leaf e =>
      refine ⟨∅, ?_, ?_, ?_, ?_⟩ <;> simp [active, all, keepCount]
  | @add l r hl hr hdisj hbridge ihl ihr
  | @sub l r hl hr hdisj hbridge ihl ihr =>
      obtain ⟨Hl, hHll, hHldisj, hHlcard, hHlnear⟩ := ihl
      obtain ⟨Hr, hHrl, hHrdisj, hHrcard, hHrnear⟩ := ihr
      have hHdisj : Disjoint Hl Hr := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (Finset.disjoint_left.mp hdisj) (hHll hx) (hHrl hy)
      refine ⟨Hl ∪ Hr, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact Finset.mem_union_left _ (hHll hx)
        · exact Finset.mem_union_right _ (hHrl hx)
      · apply Finset.disjoint_left.mpr
        intro x hxH hxP
        simp only [Finset.mem_union] at hxH
        simp only [active, Finset.mem_union] at hxP
        rcases hxH with hxL | hxR
        · rcases hxP with hxPL | hxPR
          · exact (Finset.disjoint_left.mp hHldisj) hxL hxPL
          · exact (Finset.disjoint_left.mp hdisj) (hHll hxL) (r.active_subset_all hxPR)
        · rcases hxP with hxPL | hxPR
          · exact (Finset.disjoint_left.mp hdisj.symm) (hHrl hxR) (l.active_subset_all hxPL)
          · exact (Finset.disjoint_left.mp hHrdisj) hxR hxPR
      · rw [Finset.card_union_of_disjoint hHdisj, keepCount, hHlcard, hHrcard]
      · intro q hq
        simp only [Finset.mem_union] at hq
        rcases hq with hqL | hqR
        · obtain ⟨p, hp, hnear⟩ := hHlnear q hqL
          exact ⟨p, Finset.mem_union_left _ hp, hnear⟩
        · obtain ⟨p, hp, hnear⟩ := hHrnear q hqR
          exact ⟨p, Finset.mem_union_right _ hp, hnear⟩
  | @keepLeft l r hl hr hdisj hbridge ihl ihr =>
      obtain ⟨H, hHsub, hHdisj, hHcard, hHnear⟩ := ihl
      obtain ⟨a, ha, b, hb, hab⟩ := hbridge
      have hbAll : b ∈ r.all := r.active_subset_all hb
      have hHnotB : b ∉ H := by
        intro hbH
        exact (Finset.disjoint_left.mp hdisj) (hHsub hbH) hbAll
      have hBnotActive : b ∉ l.active := by
        intro hbL
        exact (Finset.disjoint_left.mp hdisj) (l.active_subset_all hbL) hbAll
      refine ⟨H ∪ {b}, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Finset.mem_union_left _ (hHsub hx)
        · exact Finset.mem_union_right _ hbAll
      · apply Finset.disjoint_left.mpr
        intro x hx hxA
        simp only [Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact (Finset.disjoint_left.mp hHdisj) hx hxA
        · exact hBnotActive hxA
      · rw [Finset.card_union_of_disjoint (by
            apply Finset.disjoint_left.mpr
            intro x hx hb'
            simp only [Finset.mem_singleton] at hb'
            subst x
            exact hHnotB hx), Finset.card_singleton, keepCount, hHcard]
      · intro q hq
        simp only [Finset.mem_union, Finset.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hHnear q hq
        · exact ⟨a, ha, hsymm _ _ hab⟩
  | @keepRight l r hl hr hdisj hbridge ihl ihr =>
      obtain ⟨H, hHsub, hHdisj, hHcard, hHnear⟩ := ihr
      obtain ⟨a, ha, b, hb, hab⟩ := hbridge
      have haAll : a ∈ l.all := l.active_subset_all ha
      have hHnotA : a ∉ H := by
        intro haH
        exact (Finset.disjoint_left.mp hdisj.symm) (hHsub haH) haAll
      have hAnotActive : a ∉ r.active := by
        intro haR
        exact (Finset.disjoint_left.mp hdisj) haAll (r.active_subset_all haR)
      refine ⟨H ∪ {a}, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Finset.mem_union_right _ (hHsub hx)
        · exact Finset.mem_union_left _ haAll
      · apply Finset.disjoint_left.mpr
        intro x hx hxA
        simp only [Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact (Finset.disjoint_left.mp hHdisj) hx hxA
        · exact hAnotActive hxA
      · rw [Finset.card_union_of_disjoint (by
            apply Finset.disjoint_left.mpr
            intro x hx ha'
            simp only [Finset.mem_singleton] at ha'
            subst x
            exact hHnotA hx), Finset.card_singleton, keepCount, hHcard]
      · intro q hq
        simp only [Finset.mem_union, Finset.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hHnear q hq
        · exact ⟨b, hb, hab⟩

/-- The conflict neighborhood charged by the factor-three recurrence. Active
leaves belong by the explicit left disjunct; keep partners belong by `near`. -/
@[expose] noncomputable def activityNeighborhood {Cell : Type*} [DecidableEq Cell]
    (E P : Finset Cell) (near : Cell → Cell → Prop) : Finset Cell := by
  classical
  exact E.filter fun q => q ∈ P ∨ ∃ p ∈ P, near q p

theorem multiplierCount_le_neighborhood_card_sub_one
    {Cell : Type*} [DecidableEq Cell] {near : Cell → Cell → Prop}
    {h : ActivityLineage Cell} (hg : Good near h)
    (hsymm : ∀ a b, near a b → near b a)
    (E : Finset Cell) (hE : h.all ⊆ E) :
    h.multiplierCount ≤ (activityNeighborhood E h.active near).card - 1 := by
  obtain ⟨H, hHsub, hHdisj, hHcard, hHnear⟩ :=
    hg.existsKeepCharges hsymm
  let N := activityNeighborhood E h.active near
  have hPsub : h.active ⊆ N := by
    intro a ha
    simp only [N, activityNeighborhood, Finset.mem_filter]
    exact ⟨hE (h.active_subset_all ha), Or.inl ha⟩
  have hHsubN : H ⊆ N \ h.active := by
    intro a ha
    rw [Finset.mem_sdiff]
    constructor
    ·
      simp only [N, activityNeighborhood, Finset.mem_filter]
      exact ⟨hE (hHsub ha), Or.inr (hHnear a ha)⟩
    · intro haP
      exact (Finset.disjoint_left.mp hHdisj) ha haP
  have hPne : h.active.Nonempty := by
    have hcard : 0 < h.active.card := by
      rw [hg.active_card_eq_mergeCount_add_one]
      omega
    exact Finset.card_pos.mp hcard
  have hm : h.multiplierCount = h.active.card - 1 + H.card := by
    rw [h.multiplierCount_eq_merge_add_keep, hHcard]
    have hcard := hg.active_card_eq_mergeCount_add_one
    omega
  have hdisj : Disjoint h.active H := hHdisj.symm
  have hunionCard : (h.active ∪ H).card = h.active.card + H.card :=
    Finset.card_union_of_disjoint hdisj
  have hunionSub : h.active ∪ H ⊆ N := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hPsub ha
    · exact (Finset.mem_sdiff.mp (hHsubN ha)).1
  have hle : h.active.card + H.card ≤ N.card := by
    rw [← hunionCard]
    exact Finset.card_le_card hunionSub
  have hPcard : 1 ≤ h.active.card := Finset.card_pos.mpr hPne
  change h.multiplierCount ≤ N.card - 1
  omega

theorem factorThree_multiplier_bound
    {Cell : Type*} [DecidableEq Cell] {near : Cell → Cell → Prop}
    {h : ActivityLineage Cell} (hg : Good near h)
    (hsymm : ∀ a b, near a b → near b a)
    (E : Finset Cell) (hE : h.all ⊆ E) :
    (3 : ℝ) ^ h.multiplierCount ≤
      3 ^ (activityNeighborhood E h.active near).card := by
  have hm := multiplierCount_le_neighborhood_card_sub_one hg hsymm E hE
  have hmn : h.multiplierCount ≤ (activityNeighborhood E h.active near).card := by omega
  exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 3) hmn

theorem coefficient_eq_multiplier_activityProduct
    {Cell : Type*} [DecidableEq Cell] {near : Cell → Cell → Prop}
    {h : ActivityLineage Cell} (hg : Good near h) (z : Cell → ℝ) :
    coefficient z h = (3 : ℝ) ^ h.multiplierCount * ∏ e ∈ h.active, z e := by
  induction hg with
  | leaf e => simp [coefficient, multiplierCount, active]
  | @add l r hl hr hdisj hbridge ihl ihr
  | @sub l r hl hr hdisj hbridge ihl ihr =>
      have hactiveDisj : Disjoint l.active r.active := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (Finset.disjoint_left.mp hdisj) (l.active_subset_all hx) (r.active_subset_all hy)
      simp only [coefficient, multiplierCount, active]
      rw [Finset.prod_union hactiveDisj, ihl, ihr, pow_add, pow_succ]
      ring
  | @keepLeft l r hl hr hdisj hbridge ihl ihr =>
      simp only [coefficient, multiplierCount, active, ihl, pow_succ]
      ring
  | @keepRight l r hl hr hdisj hbridge ihl ihr =>
      simp only [coefficient, multiplierCount, active, ihr, pow_succ]
      ring

theorem coefficient_le_three_pow_activityNeighborhood
    {Cell : Type*} [DecidableEq Cell] {near : Cell → Cell → Prop}
    {h : ActivityLineage Cell} (hg : Good near h)
    (hsymm : ∀ a b, near a b → near b a)
    (E : Finset Cell) (hE : h.all ⊆ E) (z : Cell → ℝ)
    (hz : ∀ e, 0 ≤ z e) :
    coefficient z h ≤
      3 ^ (activityNeighborhood E h.active near).card * ∏ e ∈ h.active, z e := by
  rw [coefficient_eq_multiplier_activityProduct hg z]
  have hthree := factorThree_multiplier_bound hg hsymm E hE
  have hprod : 0 ≤ ∏ e ∈ h.active, z e := by
    apply Finset.prod_nonneg
    intro e he
    exact hz e
  exact mul_le_mul_of_nonneg_right hthree hprod

end ActivityLineage
end FroehlichSpencer.FS82.Currents
