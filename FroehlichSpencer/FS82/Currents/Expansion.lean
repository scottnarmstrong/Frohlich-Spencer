/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
/- Recursive finite current-factor expansion for FS82 Lemma 2.
   Finite fixed-frequency current expansion for FS82 Lemma 2. -/
module

public import FroehlichSpencer.FS82.Currents.Current
public import FroehlichSpencer.FS82.Currents.ActivityLineage
public import FroehlichSpencer.FS82.Currents.Geometry
public import FroehlichSpencer.FS82.Currents.Separation
public import FroehlichSpencer.FS82.Currents.Activity
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# FS82 finite current expansion

For a fixed finite integer frequency assignment, recursively apply the
four-branch cosine identity until all current supports are `√2`-separated.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents

open FroehlichSpencer.FS82.Cubical

abbrev ExpansionLineage (B : Cubical.Box 4) :=
  ActivityLineage (Link B)

abbrev CurrentState (B : Cubical.Box 4) :=
  Finset (ExpansionLineage B)

/-- The local collision relation in Lemma 2: two current supports have
Euclidean link distance at most one. -/
@[expose] def currentNear {B : Cubical.Box 4} (e f : Link B) : Prop :=
  linkDistance e f ≤ 1

/-- The coefficient carried by a lineage after its recursive pair rewrites. -/
@[expose] noncomputable def lineageCoefficient {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (t : ExpansionLineage B) : ℝ :=
  ActivityLineage.coefficient (fun e => z (abs (q e))) t

/-- The current represented by a lineage, evaluated at the original frequency
assignment. -/
@[expose] noncomputable def lineageCurrent {B : Cubical.Box 4}
    (q : Link B → ℤ) (t : ExpansionLineage B) : Link B → ℤ :=
  ActivityLineage.value q t

@[expose] noncomputable def currentFactor {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (t : ExpansionLineage B) : ℝ :=
  1 + lineageCoefficient q z t *
    Real.cos (currentPhase φ (lineageCurrent q t))

@[expose] noncomputable def currentStateProduct {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (s : CurrentState B) : ℝ :=
  ∏ t ∈ s, currentFactor q z φ t

@[expose] noncomputable def sourceCurrentProduct {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ) : ℝ :=
  (Finset.univ : Finset (Link B)).prod fun e : Link B =>
    1 + z (abs (q e)) * Real.cos (φ e * (q e : ℝ))

structure CurrentExpansionTerm (B : Cubical.Box 4) where
  state : CurrentState B
  weight : ℝ

@[expose] noncomputable def currentExpansionSum {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (T : List (CurrentExpansionTerm B)) : ℝ :=
  (T.map fun t => t.weight * currentStateProduct q z φ t.state).sum

@[expose] noncomputable def scaleCurrentExpansion {B : Cubical.Box 4} (c : ℝ)
    (T : List (CurrentExpansionTerm B)) : List (CurrentExpansionTerm B) :=
  T.map fun t => { t with weight := c * t.weight }

@[expose] noncomputable def removeCurrentPair {B : Cubical.Box 4}
    (s : CurrentState B) (l r : ExpansionLineage B) : CurrentState B :=
  (s.erase l).erase r

@[expose] noncomputable def replaceCurrentPair {B : Cubical.Box 4}
    (s : CurrentState B) (l r t : ExpansionLineage B) : CurrentState B :=
  insert t (removeCurrentPair s l r)

@[expose] noncomputable def updateKeepLeft {B : Cubical.Box 4}
    (s : CurrentState B) (l r : ExpansionLineage B) : CurrentState B :=
  replaceCurrentPair s l r (.keepLeft l r)

@[expose] noncomputable def updateKeepRight {B : Cubical.Box 4}
    (s : CurrentState B) (l r : ExpansionLineage B) : CurrentState B :=
  replaceCurrentPair s l r (.keepRight l r)

@[expose] noncomputable def updateSubtract {B : Cubical.Box 4}
    (s : CurrentState B) (l r : ExpansionLineage B) : CurrentState B :=
  replaceCurrentPair s l r (.sub l r)

@[expose] noncomputable def updateAdd {B : Cubical.Box 4}
    (s : CurrentState B) (l r : ExpansionLineage B) : CurrentState B :=
  replaceCurrentPair s l r (.add l r)

/-- Every live factor is a valid connected lineage on nonzero original
frequencies, and distinct live factors have disjoint original ancestry. -/
@[expose] def IsValidCurrentState {B : Cubical.Box 4}
    (q : Link B → ℤ) (s : CurrentState B) : Prop :=
  (∀ t ∈ s, ActivityLineage.Good (currentNear) t ∧
    ∀ e ∈ t.all, q e ≠ 0) ∧
  (∀ t ∈ s, ∀ u ∈ s, t ≠ u → Disjoint t.all u.all)

/-- Terminal 1-ensemble separation: distinct factors have link-support distance
at least √2. The local rewrite still acts at distance at most one; `Gap`
identifies these predicates on the discrete cubical link metric. -/
@[expose] def IsSeparatedCurrentState {B : Cubical.Box 4}
    (q : Link B → ℤ) (s : CurrentState B) : Prop :=
  ∀ t ∈ s, ∀ u ∈ s, t ≠ u →
    ∀ e ∈ currentSupport (lineageCurrent q t),
    ∀ f ∈ currentSupport (lineageCurrent q u), Real.sqrt 2 ≤ linkDistance e f

@[expose] noncomputable def initialCurrentState {B : Cubical.Box 4}
    (q : Link B → ℤ) : CurrentState B :=
  (Finset.univ.filter fun e : Link B => q e ≠ 0).image ActivityLineage.leaf

/-- The fixed-assignment terminal family, including the exact identity, convex
weights, and the factorwise lineage activity bound. -/
@[expose] def IsFixedFrequencyCurrentExpansion {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ)
    (T : List (CurrentExpansionTerm B)) : Prop :=
  T ≠ [] ∧
  (∀ t ∈ T, IsSeparatedCurrentState q t.state) ∧
  (∀ t ∈ T, IsValidCurrentState q t.state) ∧
  (∀ t ∈ T, 0 < t.weight) ∧
  (T.map CurrentExpansionTerm.weight).sum = 1 ∧
  (∀ φ, sourceCurrentProduct q z φ = currentExpansionSum q z φ T) ∧
  (∀ t ∈ T, ∀ h ∈ t.state, 0 < lineageCoefficient q z h) ∧
  (∀ t ∈ T, ∀ h ∈ t.state,
    lineageCoefficient q z h ≤
      (3 : ℝ) ^ (oneNeighborSet
        (currentSupport (lineageCurrent q h))).card *
        ∏ e ∈ currentSupport (lineageCurrent q h),
          z (abs (lineageCurrent q h e)))


@[simp] theorem ActivityLineage.all_nonempty {B : Cubical.Box 4}
    (t : ExpansionLineage B) : t.all.Nonempty := by
  induction t with
  | leaf e => exact ⟨e, by simp [ActivityLineage.all]⟩
  | add l r ihl ihr | sub l r ihl ihr =>
      rcases ihl with ⟨e, he⟩
      exact ⟨e, by simp [ActivityLineage.all, he]⟩
  | keepLeft l r ihl ihr | keepRight l r ihl ihr =>
      rcases ihl with ⟨e, he⟩
      exact ⟨e, by simp [ActivityLineage.all, he]⟩

private theorem currentState_eq_pair_insert {B : Cubical.Box 4}
    {s : CurrentState B} {l r : ExpansionLineage B}
    (hl : l ∈ s) (hr : r ∈ s) (hlr : l ≠ r) :
    s = insert l (insert r (removeCurrentPair s l r)) := by
  have hr' : r ∈ s.erase l := Finset.mem_erase.mpr ⟨hlr.symm, hr⟩
  have hEraseR : insert r ((s.erase l).erase r) = s.erase l :=
    Finset.insert_erase hr'
  have hEraseL : insert l (s.erase l) = s := Finset.insert_erase hl
  calc
    s = insert l (s.erase l) := (Finset.insert_erase hl).symm
    _ = insert l (insert r (removeCurrentPair s l r)) := by
      rw [removeCurrentPair]
      exact congrArg (insert l) hEraseR.symm

private theorem currentStateProduct_initial_eq_source {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (hq : ∀ e, q e ≠ 0) :
    currentStateProduct q z φ (initialCurrentState q) = sourceCurrentProduct q z φ := by
  classical
  have hinj : Set.InjOn (ActivityLineage.leaf : Link B → ExpansionLineage B)
      ↑(Finset.univ.filter fun e : Link B => q e ≠ 0) := by
    intro a ha b hb heq
    cases heq
    rfl
  have hfilter : Finset.univ.filter (fun e : Link B => q e ≠ 0) = Finset.univ := by
    ext e
    simp [hq e]
  unfold currentStateProduct initialCurrentState sourceCurrentProduct
  rw [Finset.prod_image hinj, hfilter]
  apply Finset.prod_congr rfl
  intro e he
  have hphase : currentPhase φ (ActivityLineage.value q (.leaf e)) =
      φ e * (q e : ℝ) := by
    simp [currentPhase, ActivityLineage.value]
  change 1 + z (abs (q e)) *
      Real.cos (currentPhase φ (ActivityLineage.value q (.leaf e))) =
    1 + z (abs (q e)) * Real.cos (φ e * (q e : ℝ))
  rw [hphase]

private theorem currentState_initial_valid {B : Cubical.Box 4}
    {q : Link B → ℤ} :
    IsValidCurrentState q (initialCurrentState q) := by
  classical
  constructor
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨e, he, rfl⟩
    have hqe : q e ≠ 0 := (Finset.mem_filter.mp he).2
    constructor
    · exact ActivityLineage.Good.leaf e
    · intro x hx
      simp only [ActivityLineage.all, Finset.mem_singleton] at hx
      subst x
      exact hqe
  · intro t ht u hu htu
    rcases Finset.mem_image.mp ht with ⟨e, he, rfl⟩
    rcases Finset.mem_image.mp hu with ⟨f, hf, rfl⟩
    have hne : e ≠ f := by
      intro hef
      subst f
      exact htu rfl
    exact Finset.disjoint_singleton.mpr hne

private theorem separated_or_closePair {B : Cubical.Box 4}
    (q : Link B → ℤ) (s : CurrentState B) :
    IsSeparatedCurrentState q s ∨
      ∃ l ∈ s, ∃ r ∈ s, l ≠ r ∧
        ∃ e ∈ currentSupport (lineageCurrent q l),
        ∃ f ∈ currentSupport (lineageCurrent q r), linkDistance e f ≤ 1 := by
  classical
  by_cases hsep : IsSeparatedCurrentState q s
  · exact Or.inl hsep
  · right
    unfold IsSeparatedCurrentState at hsep
    push Not at hsep
    rcases hsep with ⟨l, hl, r, hr, hlr, e, he, f, hf, hnot⟩
    have hnear : linkDistance e f ≤ 1 := by
      by_contra hgt
      exact (not_lt_of_ge (linkDistance_gt_one_implies_sqrt_two_le e f
        (lt_of_not_ge hgt))) hnot
    exact ⟨l, hl, r, hr, hlr, e, he, f, hf, hnear⟩

private theorem currentPairBranches_good {B : Cubical.Box 4}
    {q : Link B → ℤ} {s : CurrentState B} {l r : ExpansionLineage B}
    (hs : IsValidCurrentState q s) (hl : l ∈ s) (hr : r ∈ s) (hlr : l ≠ r)
    {e f : Link B} (he : e ∈ currentSupport (lineageCurrent q l))
    (hf : f ∈ currentSupport (lineageCurrent q r)) (hnear : currentNear e f) :
    (ActivityLineage.Good currentNear (.keepLeft l r) ∧
      (∀ x ∈ (ActivityLineage.keepLeft l r).all, q x ≠ 0)) ∧
    (ActivityLineage.Good currentNear (.keepRight l r) ∧
      (∀ x ∈ (ActivityLineage.keepRight l r).all, q x ≠ 0)) ∧
    (ActivityLineage.Good currentNear (.sub l r) ∧
      (∀ x ∈ (ActivityLineage.sub l r).all, q x ≠ 0)) ∧
    (ActivityLineage.Good currentNear (.add l r) ∧
      (∀ x ∈ (ActivityLineage.add l r).all, q x ≠ 0)) := by
  obtain ⟨hFactors, hdisj⟩ := hs
  obtain ⟨hGoodL, hqL⟩ := hFactors l hl
  obtain ⟨hGoodR, hqR⟩ := hFactors r hr
  have hdisjLR : Disjoint l.all r.all := hdisj l hl r hr hlr
  have hsupportL := ActivityLineage.currentSupport_value_eq_active hGoodL q hqL
  have hsupportR := ActivityLineage.currentSupport_value_eq_active hGoodR q hqR
  have hbridge : ∃ a ∈ l.active, ∃ b ∈ r.active, currentNear a b := by
    change e ∈ currentSupport (ActivityLineage.value q l) at he
    change f ∈ currentSupport (ActivityLineage.value q r) at hf
    rw [hsupportL] at he
    rw [hsupportR] at hf
    exact ⟨e, he, f, hf, hnear⟩
  have hqUnion : ∀ x ∈ l.all ∪ r.all, q x ≠ 0 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hqL x hx
    · exact hqR x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨ActivityLineage.Good.keepLeft hGoodL hGoodR hdisjLR hbridge, ?_⟩
    simpa [ActivityLineage.all] using hqUnion
  · refine ⟨ActivityLineage.Good.keepRight hGoodL hGoodR hdisjLR hbridge, ?_⟩
    simpa [ActivityLineage.all] using hqUnion
  · refine ⟨ActivityLineage.Good.sub hGoodL hGoodR hdisjLR hbridge, ?_⟩
    simpa [ActivityLineage.all] using hqUnion
  · refine ⟨ActivityLineage.Good.add hGoodL hGoodR hdisjLR hbridge, ?_⟩
    simpa [ActivityLineage.all] using hqUnion

private theorem replaceCurrentPair_not_mem {B : Cubical.Box 4}
    {q : Link B → ℤ} {s : CurrentState B} {l r b : ExpansionLineage B}
    (hs : IsValidCurrentState q s) (hl : l ∈ s)
    (hbAll : b.all = l.all ∪ r.all) :
    b ∉ removeCurrentPair s l r := by
  classical
  obtain ⟨_, hdisj⟩ := hs
  have hlR : l ∉ removeCurrentPair s l r := by simp [removeCurrentPair]
  intro hb
  have hbl : b ≠ l := by
    intro heq
    subst b
    exact hlR hb
  have hbS : b ∈ s :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)
  have hcross := hdisj l hl b hbS hbl.symm
  obtain ⟨e, he⟩ := ActivityLineage.all_nonempty (B := B) l
  have heB : e ∈ b.all := by rw [hbAll]; exact Finset.mem_union_left _ he
  exact (Finset.disjoint_left.mp hcross) he heB

private theorem replaceCurrentPair_card_lt {B : Cubical.Box 4}
    {q : Link B → ℤ} {s : CurrentState B} {l r b : ExpansionLineage B}
    (hs : IsValidCurrentState q s) (hl : l ∈ s) (hr : r ∈ s) (hlr : l ≠ r)
    (hbAll : b.all = l.all ∪ r.all) :
    (replaceCurrentPair s l r b).card < s.card := by
  classical
  have hnew := replaceCurrentPair_not_mem hs hl hbAll
  have hr' : r ∈ s.erase l := Finset.mem_erase.mpr ⟨hlr.symm, hr⟩
  have hcardGE : 2 ≤ s.card := by
    have hp : 0 < (s.erase l).card := Finset.card_pos.mpr ⟨r, hr'⟩
    rw [Finset.card_erase_of_mem hl] at hp
    omega
  have hcardRest : (removeCurrentPair s l r).card = s.card - 2 := by
    rw [removeCurrentPair, Finset.card_erase_of_mem hr',
      Finset.card_erase_of_mem hl]
    omega
  rw [replaceCurrentPair, Finset.card_insert_of_notMem hnew, hcardRest]
  omega

private theorem replaceCurrentPair_card_succ {B : Cubical.Box 4}
    {q : Link B → ℤ} {s : CurrentState B} {l r b : ExpansionLineage B}
    (hs : IsValidCurrentState q s) (hl : l ∈ s) (hr : r ∈ s) (hlr : l ≠ r)
    (hbAll : b.all = l.all ∪ r.all) :
    (replaceCurrentPair s l r b).card + 1 = s.card := by
  classical
  have hnew := replaceCurrentPair_not_mem hs hl hbAll
  have hr' : r ∈ s.erase l := Finset.mem_erase.mpr ⟨hlr.symm, hr⟩
  have hcardGE : 2 ≤ s.card := by
    have hp : 0 < (s.erase l).card := Finset.card_pos.mpr ⟨r, hr'⟩
    rw [Finset.card_erase_of_mem hl] at hp
    omega
  have hcardRest : (removeCurrentPair s l r).card = s.card - 2 := by
    rw [removeCurrentPair, Finset.card_erase_of_mem hr',
      Finset.card_erase_of_mem hl]
    omega
  rw [replaceCurrentPair, Finset.card_insert_of_notMem hnew, hcardRest]
  omega

private theorem replaceCurrentPair_valid {B : Cubical.Box 4}
    {q : Link B → ℤ} {s : CurrentState B} {l r b : ExpansionLineage B}
    (hs : IsValidCurrentState q s) (hl : l ∈ s) (hr : r ∈ s)
    (hbGood : ActivityLineage.Good currentNear b)
    (hbq : ∀ e ∈ b.all, q e ≠ 0)
    (hbAll : b.all = l.all ∪ r.all) :
    IsValidCurrentState q (replaceCurrentPair s l r b) := by
  classical
  obtain ⟨hFactors, hdisj⟩ := hs
  let R := removeCurrentPair s l r
  have hlR : l ∉ R := by simp [R, removeCurrentPair]
  have hrR : r ∉ R := by simp [R, removeCurrentPair]
  have hbR : b ∉ R := by
    intro hb
    have hbl : b ≠ l := by
      intro heq
      subst b
      exact hlR hb
    have hbS : b ∈ s := by
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)
    have hcross := hdisj l hl b hbS hbl.symm
    obtain ⟨e, he⟩ := ActivityLineage.all_nonempty (B := B) l
    have heB : e ∈ b.all := by rw [hbAll]; exact Finset.mem_union_left _ he
    exact (Finset.disjoint_left.mp hcross) he heB
  constructor
  · intro t ht
    simp only [replaceCurrentPair, Finset.mem_insert] at ht
    rcases ht with rfl | htR
    · exact ⟨hbGood, hbq⟩
    · have htS : t ∈ s := by
        exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase htR)
      exact hFactors t htS
  · intro t ht u hu htu
    simp only [replaceCurrentPair, Finset.mem_insert] at ht hu
    rcases ht with rfl | htR
    · rcases hu with rfl | huR
      · exact (htu rfl).elim
      · have huS : u ∈ s := by
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase huR)
        have hlu : l ≠ u := by
          intro heq
          subst u
          exact hlR huR
        have hru : r ≠ u := by
          intro heq
          subst u
          exact hrR huR
        have hluD := hdisj l hl u huS hlu
        have hruD := hdisj r hr u huS hru
        rw [hbAll]
        exact Finset.disjoint_union_left.mpr ⟨hluD, hruD⟩
    · rcases hu with rfl | huR
      · have htS : t ∈ s := by
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase htR)
        have hlt : l ≠ t := by
          intro heq
          subst t
          exact hlR htR
        have hrt : r ≠ t := by
          intro heq
          subst t
          exact hrR htR
        have htlD := hdisj l hl t htS hlt
        have hrtD := hdisj r hr t htS hrt
        rw [hbAll]
        exact (Finset.disjoint_union_left.mpr ⟨htlD, hrtD⟩).symm
      · have htS : t ∈ s := by
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase htR)
        have huS : u ∈ s := by
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase huR)
        exact hdisj t htS u huS htu

private theorem currentStateProduct_insert {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (t : ExpansionLineage B) (s : CurrentState B) (ht : t ∉ s) :
    currentStateProduct q z φ (insert t s) =
      currentFactor q z φ t * currentStateProduct q z φ s := by
  simp [currentStateProduct, Finset.prod_insert, ht]

private theorem currentStateProduct_pair {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    {s : CurrentState B} {l r : ExpansionLineage B}
    (hl : l ∈ s) (hr : r ∈ s) (hlr : l ≠ r) :
    currentStateProduct q z φ s =
      currentFactor q z φ l * currentFactor q z φ r *
        currentStateProduct q z φ (removeCurrentPair s l r) := by
  have hEq := currentState_eq_pair_insert hl hr hlr
  have hRnot : r ∉ removeCurrentPair s l r := by
    simp [removeCurrentPair]
  have hLnot : l ∉ insert r (removeCurrentPair s l r) := by
    simp [removeCurrentPair, hlr]
  have hRemove : removeCurrentPair
      (insert l (insert r (removeCurrentPair s l r))) l r =
      removeCurrentPair s l r := by
    simp [removeCurrentPair, hlr]
  calc
    currentStateProduct q z φ s =
        currentStateProduct q z φ
          (insert l (insert r (removeCurrentPair s l r))) :=
      congrArg (currentStateProduct q z φ) hEq
    _ = currentFactor q z φ l * currentFactor q z φ r *
        currentStateProduct q z φ (removeCurrentPair s l r) := by
      change (∏ t ∈ insert l (insert r (removeCurrentPair s l r)),
          currentFactor q z φ t) = _
      rw [Finset.prod_insert hLnot, Finset.prod_insert hRnot]
      simp only [currentStateProduct]
      ring

private theorem currentFactor_fourBranchIdentity {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (l r : ExpansionLineage B) :
    currentFactor q z φ l * currentFactor q z φ r =
      (1 / 3 : ℝ) * currentFactor q z φ (.keepLeft l r) +
        (1 / 3 : ℝ) * currentFactor q z φ (.keepRight l r) +
        (1 / 6 : ℝ) * currentFactor q z φ (.sub l r) +
        (1 / 6 : ℝ) * currentFactor q z φ (.add l r) := by
  have hid := fixedFrequency_cosinePair_rewrite φ
    (lineageCurrent q l) (lineageCurrent q r)
    (lineageCoefficient q z l) (lineageCoefficient q z r)
  have hcoeffL : lineageCoefficient q z (.keepLeft l r) =
      3 * lineageCoefficient q z l := rfl
  have hcoeffR : lineageCoefficient q z (.keepRight l r) =
      3 * lineageCoefficient q z r := rfl
  have hcoeffS : lineageCoefficient q z (.sub l r) =
      3 * lineageCoefficient q z l * lineageCoefficient q z r := rfl
  have hcoeffA : lineageCoefficient q z (.add l r) =
      3 * lineageCoefficient q z l * lineageCoefficient q z r := rfl
  have hphaseL : currentPhase φ (lineageCurrent q (.keepLeft l r)) =
      currentPhase φ (lineageCurrent q l) := rfl
  have hphaseR : currentPhase φ (lineageCurrent q (.keepRight l r)) =
      currentPhase φ (lineageCurrent q r) := rfl
  have hphaseS : currentPhase φ (lineageCurrent q (.sub l r)) =
      currentPhase φ (lineageCurrent q l) - currentPhase φ (lineageCurrent q r) := by
    simp only [lineageCurrent, ActivityLineage.value]
    exact currentPhase_sub φ (ActivityLineage.value q l) (ActivityLineage.value q r)
  have hphaseA : currentPhase φ (lineageCurrent q (.add l r)) =
      currentPhase φ (lineageCurrent q l) + currentPhase φ (lineageCurrent q r) := by
    simp only [lineageCurrent, ActivityLineage.value]
    exact currentPhase_add φ (ActivityLineage.value q l) (ActivityLineage.value q r)
  unfold currentFactor
  rw [hcoeffL, hcoeffR, hcoeffS, hcoeffA,
    hphaseL, hphaseR, hphaseS, hphaseA]
  rw [currentPhase_sub, currentPhase_add] at hid
  exact hid

private theorem currentStateProduct_fourBranchIdentity {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    {s : CurrentState B} {l r : ExpansionLineage B}
    (hl : l ∈ s) (hr : r ∈ s) (hlr : l ≠ r)
    (hleft : .keepLeft l r ∉ removeCurrentPair s l r)
    (hright : .keepRight l r ∉ removeCurrentPair s l r)
    (hsub : .sub l r ∉ removeCurrentPair s l r)
    (hadd : .add l r ∉ removeCurrentPair s l r) :
    currentStateProduct q z φ s =
      (1 / 3 : ℝ) * currentStateProduct q z φ (updateKeepLeft s l r) +
      (1 / 3 : ℝ) * currentStateProduct q z φ (updateKeepRight s l r) +
      (1 / 6 : ℝ) * currentStateProduct q z φ (updateSubtract s l r) +
      (1 / 6 : ℝ) * currentStateProduct q z φ (updateAdd s l r) := by
  let P := currentStateProduct q z φ (removeCurrentPair s l r)
  have hL := currentStateProduct_insert q z φ (.keepLeft l r)
    (removeCurrentPair s l r) hleft
  have hR := currentStateProduct_insert q z φ (.keepRight l r)
    (removeCurrentPair s l r) hright
  have hS := currentStateProduct_insert q z φ (.sub l r)
    (removeCurrentPair s l r) hsub
  have hA := currentStateProduct_insert q z φ (.add l r)
    (removeCurrentPair s l r) hadd
  calc
    currentStateProduct q z φ s =
        currentFactor q z φ l * currentFactor q z φ r * P :=
      currentStateProduct_pair q z φ hl hr hlr
    _ = ((1 / 3 : ℝ) * currentFactor q z φ (.keepLeft l r) +
          (1 / 3 : ℝ) * currentFactor q z φ (.keepRight l r) +
          (1 / 6 : ℝ) * currentFactor q z φ (.sub l r) +
          (1 / 6 : ℝ) * currentFactor q z φ (.add l r)) * P := by
      rw [currentFactor_fourBranchIdentity]
    _ = (1 / 3 : ℝ) * currentStateProduct q z φ (updateKeepLeft s l r) +
        (1 / 3 : ℝ) * currentStateProduct q z φ (updateKeepRight s l r) +
        (1 / 6 : ℝ) * currentStateProduct q z φ (updateSubtract s l r) +
        (1 / 6 : ℝ) * currentStateProduct q z φ (updateAdd s l r) := by
      dsimp [updateKeepLeft, updateKeepRight, updateSubtract, updateAdd,
        replaceCurrentPair]
      rw [hL, hR, hS, hA]
      dsimp [P]
      ring


@[expose] def IsCurrentStateExpansion {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B)
    (T : List (CurrentExpansionTerm B)) : Prop :=
  T ≠ [] ∧
  (∀ t ∈ T, IsSeparatedCurrentState q t.state) ∧
  (∀ t ∈ T, IsValidCurrentState q t.state) ∧
  (∀ t ∈ T, 0 < t.weight) ∧
  (T.map CurrentExpansionTerm.weight).sum = 1 ∧
  (∀ φ, currentStateProduct q z φ s = currentExpansionSum q z φ T)

private theorem currentExpansionWeightSum_append {B : Cubical.Box 4}
    (T U : List (CurrentExpansionTerm B)) :
    ((T ++ U).map CurrentExpansionTerm.weight).sum =
      (T.map CurrentExpansionTerm.weight).sum +
        (U.map CurrentExpansionTerm.weight).sum := by
  simp [List.map_append]

private theorem currentExpansionWeightSum_scale {B : Cubical.Box 4}
    (c : ℝ) (T : List (CurrentExpansionTerm B)) :
    ((scaleCurrentExpansion c T).map CurrentExpansionTerm.weight).sum =
      c * (T.map CurrentExpansionTerm.weight).sum := by
  induction T with
  | nil => simp [scaleCurrentExpansion]
  | cons t T ih =>
      change c * t.weight +
          ((scaleCurrentExpansion c T).map CurrentExpansionTerm.weight).sum =
        c * (t.weight + (T.map CurrentExpansionTerm.weight).sum)
      rw [ih]
      ring

private theorem currentExpansionSum_append {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (T U : List (CurrentExpansionTerm B)) :
    currentExpansionSum q z φ (T ++ U) =
      currentExpansionSum q z φ T + currentExpansionSum q z φ U := by
  simp [currentExpansionSum, List.map_append]

private theorem currentExpansionSum_scale {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) (φ : Link B → ℝ)
    (c : ℝ) (T : List (CurrentExpansionTerm B)) :
    currentExpansionSum q z φ (scaleCurrentExpansion c T) =
      c * currentExpansionSum q z φ T := by
  induction T with
  | nil => simp [currentExpansionSum, scaleCurrentExpansion]
  | cons t T ih =>
      change c * t.weight * currentStateProduct q z φ t.state +
          currentExpansionSum q z φ (scaleCurrentExpansion c T) =
        c * (t.weight * currentStateProduct q z φ t.state +
          currentExpansionSum q z φ T)
      rw [ih]
      ring

private theorem currentExpansion_scaled_nonempty {B : Cubical.Box 4}
    (c : ℝ) (T : List (CurrentExpansionTerm B)) :
    scaleCurrentExpansion c T ≠ [] ↔ T ≠ [] := by
  simp [scaleCurrentExpansion]

private theorem currentExpansion_scaled_positive {B : Cubical.Box 4}
    {c : ℝ} (hc : 0 < c) {T : List (CurrentExpansionTerm B)}
    (hT : ∀ t ∈ T, 0 < t.weight) :
    ∀ t ∈ scaleCurrentExpansion c T, 0 < t.weight := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  simpa [scaleCurrentExpansion] using mul_pos hc (hT u hu)

private theorem currentExpansion_scaled_stateProperty {B : Cubical.Box 4}
    (P : CurrentState B → Prop) {c : ℝ} {T : List (CurrentExpansionTerm B)}
    (hP : ∀ t ∈ T, P t.state) :
    ∀ t ∈ scaleCurrentExpansion c T, P t.state := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hP u hu

private theorem currentExpansion_scaled_weightLower {B : Cubical.Box 4}
    (k : ℕ) {c : ℝ} (hc : 1 ≤ 6 * c)
    {T : List (CurrentExpansionTerm B)}
    (hT : ∀ t ∈ T, (6 : ℝ) ^ k * t.weight ≥ 1) :
    ∀ t ∈ scaleCurrentExpansion c T,
      (6 : ℝ) ^ (k + 1) * t.weight ≥ 1 := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hweight := hT u hu
  have hnonneg : 0 ≤ (6 : ℝ) ^ k * u.weight := by linarith
  have hscaled : (6 : ℝ) ^ k * u.weight ≤
      (6 * c) * ((6 : ℝ) ^ k * u.weight) := by
    calc
      (6 : ℝ) ^ k * u.weight = 1 * ((6 : ℝ) ^ k * u.weight) := by ring
      _ ≤ (6 * c) * ((6 : ℝ) ^ k * u.weight) :=
        mul_le_mul_of_nonneg_right hc hnonneg
  calc
    1 ≤ (6 : ℝ) ^ k * u.weight := hweight
    _ ≤ (6 * c) * ((6 : ℝ) ^ k * u.weight) := hscaled
    _ = (6 : ℝ) ^ (k + 1) * (c * u.weight) := by
      rw [pow_succ]
      ring

private theorem exists_currentStateExpansion {B : Cubical.Box 4}
    (q : Link B → ℤ) (z : ℤ → ℝ) :
    ∀ n, ∀ s : CurrentState B, s.card = n → IsValidCurrentState q s →
      ∃ T : List (CurrentExpansionTerm B),
        IsCurrentStateExpansion q z s T ∧
          ∀ t ∈ T, (6 : ℝ) ^ n * t.weight ≥ 1 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hcard hs
    rcases separated_or_closePair q s with hsep | hconflict
    · refine ⟨[{ state := s, weight := 1 }], ?_⟩
      refine ⟨?_, ?_⟩
      · refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
        · intro t ht
          simp only [List.mem_singleton] at ht
          subst t
          exact hsep
        · intro t ht
          simp only [List.mem_singleton] at ht
          subst t
          exact hs
        · intro t ht
          simp only [List.mem_singleton] at ht
          subst t
          norm_num
        · simp
        · intro φ
          simp [currentExpansionSum]
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst t
        have hn : 1 ≤ (6 : ℝ) ^ n :=
          one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 6)
        simpa using hn
    · obtain ⟨l, hl, r, hr, hlr, e, he, f, hf, hnear⟩ := hconflict
      obtain ⟨⟨hGL, hqL⟩, ⟨hGR, hqR⟩, ⟨hGS, hqS⟩, ⟨hGA, hqA⟩⟩ :=
        currentPairBranches_good hs hl hr hlr he hf hnear
      let sL := updateKeepLeft s l r
      let sR := updateKeepRight s l r
      let sS := updateSubtract s l r
      let sA := updateAdd s l r
      have hvalidL : IsValidCurrentState q sL := by
        exact replaceCurrentPair_valid hs hl hr hGL hqL (by simp [ActivityLineage.all])
      have hvalidR : IsValidCurrentState q sR := by
        exact replaceCurrentPair_valid hs hl hr hGR hqR (by simp [ActivityLineage.all])
      have hvalidS : IsValidCurrentState q sS := by
        exact replaceCurrentPair_valid hs hl hr hGS hqS (by simp [ActivityLineage.all])
      have hvalidA : IsValidCurrentState q sA := by
        exact replaceCurrentPair_valid hs hl hr hGA hqA (by simp [ActivityLineage.all])
      have hcardL : sL.card < s.card := by
        exact replaceCurrentPair_card_lt hs hl hr hlr (by simp [ActivityLineage.all])
      have hcardR : sR.card < s.card := by
        exact replaceCurrentPair_card_lt hs hl hr hlr (by simp [ActivityLineage.all])
      have hcardS : sS.card < s.card := by
        exact replaceCurrentPair_card_lt hs hl hr hlr (by simp [ActivityLineage.all])
      have hcardA : sA.card < s.card := by
        exact replaceCurrentPair_card_lt hs hl hr hlr (by simp [ActivityLineage.all])
      have hsuccL : sL.card + 1 = s.card :=
        replaceCurrentPair_card_succ hs hl hr hlr (by simp [ActivityLineage.all])
      have hsuccR : sR.card + 1 = s.card :=
        replaceCurrentPair_card_succ hs hl hr hlr (by simp [ActivityLineage.all])
      have hsuccS : sS.card + 1 = s.card :=
        replaceCurrentPair_card_succ hs hl hr hlr (by simp [ActivityLineage.all])
      have hsuccA : sA.card + 1 = s.card :=
        replaceCurrentPair_card_succ hs hl hr hlr (by simp [ActivityLineage.all])
      obtain ⟨TL, hTL, hTLmin⟩ := ih sL.card (by omega) sL rfl hvalidL
      obtain ⟨TR, hTR, hTRmin⟩ := ih sR.card (by omega) sR rfl hvalidR
      obtain ⟨TS, hTS, hTSmin⟩ := ih sS.card (by omega) sS rfl hvalidS
      obtain ⟨TA, hTA, hTAmin⟩ := ih sA.card (by omega) sA rfl hvalidA
      let TL' := scaleCurrentExpansion (1 / 3 : ℝ) TL
      let TR' := scaleCurrentExpansion (1 / 3 : ℝ) TR
      let TS' := scaleCurrentExpansion (1 / 6 : ℝ) TS
      let TA' := scaleCurrentExpansion (1 / 6 : ℝ) TA
      let T := TL' ++ (TR' ++ (TS' ++ TA'))
      have hTL' : TL' ≠ [] := by
        exact currentExpansion_scaled_nonempty (1 / 3 : ℝ) TL |>.2 hTL.1
      have hTne : T ≠ [] := by simp [T, hTL']
      have hLnot : ActivityLineage.keepLeft l r ∉ removeCurrentPair s l r := by
        exact replaceCurrentPair_not_mem hs hl (by simp [ActivityLineage.all])
      have hRnot : ActivityLineage.keepRight l r ∉ removeCurrentPair s l r := by
        exact replaceCurrentPair_not_mem hs hl (by simp [ActivityLineage.all])
      have hSnot : ActivityLineage.sub l r ∉ removeCurrentPair s l r := by
        exact replaceCurrentPair_not_mem hs hl (by simp [ActivityLineage.all])
      have hAnot : ActivityLineage.add l r ∉ removeCurrentPair s l r := by
        exact replaceCurrentPair_not_mem hs hl (by simp [ActivityLineage.all])
      have hterminal : ∀ t ∈ T, IsSeparatedCurrentState q t.state := by
        intro t ht
        change t ∈ TL' ++ (TR' ++ (TS' ++ TA')) at ht
        rw [List.mem_append] at ht
        rcases ht with htL | htRest
        · exact currentExpansion_scaled_stateProperty
            (IsSeparatedCurrentState q) hTL.2.1 t htL
        · rw [List.mem_append] at htRest
          rcases htRest with htR | htRest
          · exact currentExpansion_scaled_stateProperty
              (IsSeparatedCurrentState q) hTR.2.1 t htR
          · rw [List.mem_append] at htRest
            rcases htRest with htS | htA
            · exact currentExpansion_scaled_stateProperty
                (IsSeparatedCurrentState q) hTS.2.1 t htS
            · exact currentExpansion_scaled_stateProperty
                (IsSeparatedCurrentState q) hTA.2.1 t htA
      have hvalid : ∀ t ∈ T, IsValidCurrentState q t.state := by
        intro t ht
        change t ∈ TL' ++ (TR' ++ (TS' ++ TA')) at ht
        rw [List.mem_append] at ht
        rcases ht with htL | htRest
        · exact currentExpansion_scaled_stateProperty
            (IsValidCurrentState q) hTL.2.2.1 t htL
        · rw [List.mem_append] at htRest
          rcases htRest with htR | htRest
          · exact currentExpansion_scaled_stateProperty
              (IsValidCurrentState q) hTR.2.2.1 t htR
          · rw [List.mem_append] at htRest
            rcases htRest with htS | htA
            · exact currentExpansion_scaled_stateProperty
                (IsValidCurrentState q) hTS.2.2.1 t htS
            · exact currentExpansion_scaled_stateProperty
                (IsValidCurrentState q) hTA.2.2.1 t htA
      have hpositive : ∀ t ∈ T, 0 < t.weight := by
        intro t ht
        change t ∈ TL' ++ (TR' ++ (TS' ++ TA')) at ht
        rw [List.mem_append] at ht
        rcases ht with htL | htRest
        · exact currentExpansion_scaled_positive (by norm_num : (0 : ℝ) < 1 / 3)
            hTL.2.2.2.1 t htL
        · rw [List.mem_append] at htRest
          rcases htRest with htR | htRest
          · exact currentExpansion_scaled_positive (by norm_num : (0 : ℝ) < 1 / 3)
              hTR.2.2.2.1 t htR
          · rw [List.mem_append] at htRest
            rcases htRest with htS | htA
            · exact currentExpansion_scaled_positive (by norm_num : (0 : ℝ) < 1 / 6)
                hTS.2.2.2.1 t htS
            · exact currentExpansion_scaled_positive (by norm_num : (0 : ℝ) < 1 / 6)
                hTA.2.2.2.1 t htA
      have hnorm : (T.map CurrentExpansionTerm.weight).sum = 1 := by
        simp only [T, TL', TR', TS', TA', currentExpansionWeightSum_append]
        rw [currentExpansionWeightSum_scale, currentExpansionWeightSum_scale,
          currentExpansionWeightSum_scale, currentExpansionWeightSum_scale,
          hTL.2.2.2.2.1, hTR.2.2.2.2.1, hTS.2.2.2.2.1, hTA.2.2.2.2.1]
        norm_num
      have hidentity : ∀ φ,
          currentStateProduct q z φ s = currentExpansionSum q z φ T := by
        intro φ
        have hstep := currentStateProduct_fourBranchIdentity q z φ hl hr hlr
          hLnot hRnot hSnot hAnot
        calc
          currentStateProduct q z φ s =
              (1 / 3 : ℝ) * currentStateProduct q z φ sL +
              (1 / 3 : ℝ) * currentStateProduct q z φ sR +
              (1 / 6 : ℝ) * currentStateProduct q z φ sS +
              (1 / 6 : ℝ) * currentStateProduct q z φ sA := by
                simpa [sL, sR, sS, sA] using hstep
          _ = (1 / 3 : ℝ) * currentExpansionSum q z φ TL +
              (1 / 3 : ℝ) * currentExpansionSum q z φ TR +
              (1 / 6 : ℝ) * currentExpansionSum q z φ TS +
              (1 / 6 : ℝ) * currentExpansionSum q z φ TA := by
                rw [hTL.2.2.2.2.2 φ, hTR.2.2.2.2.2 φ,
                  hTS.2.2.2.2.2 φ, hTA.2.2.2.2.2 φ]
          _ = currentExpansionSum q z φ T := by
                simp [T, TL', TR', TS', TA', currentExpansionSum_append,
                  currentExpansionSum_scale]
                ring
      have hminT : ∀ t ∈ T, (6 : ℝ) ^ n * t.weight ≥ 1 := by
        intro t ht
        change t ∈ TL' ++ (TR' ++ (TS' ++ TA')) at ht
        rw [List.mem_append] at ht
        rcases ht with htL | htRest
        · have h := currentExpansion_scaled_weightLower sL.card
            (by norm_num : (1 : ℝ) ≤ 6 * (1 / 3 : ℝ)) hTLmin t htL
          simpa [hsuccL, hcard] using h
        · rw [List.mem_append] at htRest
          rcases htRest with htR | htRest
          · have h := currentExpansion_scaled_weightLower sR.card
              (by norm_num : (1 : ℝ) ≤ 6 * (1 / 3 : ℝ)) hTRmin t htR
            simpa [hsuccR, hcard] using h
          · rw [List.mem_append] at htRest
            rcases htRest with htS | htA
            · have h := currentExpansion_scaled_weightLower sS.card
                (by norm_num : (1 : ℝ) ≤ 6 * (1 / 6 : ℝ)) hTSmin t htS
              simpa [hsuccS, hcard] using h
            · have h := currentExpansion_scaled_weightLower sA.card
                (by norm_num : (1 : ℝ) ≤ 6 * (1 / 6 : ℝ)) hTAmin t htA
              simpa [hsuccA, hcard] using h
      exact ⟨T, ⟨hTne, hterminal, hvalid, hpositive, hnorm, hidentity⟩, hminT⟩


private theorem lineageCoefficient_pos_of_good {B : Cubical.Box 4}
    {q : Link B → ℤ} {z : ℤ → ℝ} {t : ExpansionLineage B}
    (hg : ActivityLineage.Good currentNear t)
    (hz : ∀ e ∈ t.all, 0 < z (abs (q e))) :
    0 < lineageCoefficient q z t := by
  induction hg with
  | leaf e =>
      exact hz e (by simp [ActivityLineage.all])
  | @add l r hl hr hdisj hbridge ihl ihr =>
      have hzL : ∀ e ∈ l.all, 0 < z (abs (q e)) := by
        intro e he
        exact hz e (Finset.mem_union.mpr (Or.inl he))
      have hzR : ∀ e ∈ r.all, 0 < z (abs (q e)) := by
        intro e he
        exact hz e (Finset.mem_union.mpr (Or.inr he))
      change 0 < 3 * lineageCoefficient q z l * lineageCoefficient q z r
      exact mul_pos (mul_pos (by norm_num) (ihl hzL)) (ihr hzR)
  | @sub l r hl hr hdisj hbridge ihl ihr =>
      have hzL : ∀ e ∈ l.all, 0 < z (abs (q e)) := by
        intro e he
        exact hz e (Finset.mem_union.mpr (Or.inl he))
      have hzR : ∀ e ∈ r.all, 0 < z (abs (q e)) := by
        intro e he
        exact hz e (Finset.mem_union.mpr (Or.inr he))
      change 0 < 3 * lineageCoefficient q z l * lineageCoefficient q z r
      exact mul_pos (mul_pos (by norm_num) (ihl hzL)) (ihr hzR)
  | @keepLeft l r hl hr hdisj hbridge ihl ihr =>
      have hzL : ∀ e ∈ l.all, 0 < z (abs (q e)) := by
        intro e he
        exact hz e (Finset.mem_union.mpr (Or.inl he))
      change 0 < 3 * lineageCoefficient q z l
      exact mul_pos (by norm_num) (ihl hzL)
  | @keepRight l r hl hr hdisj hbridge ihl ihr =>
      have hzR : ∀ e ∈ r.all, 0 < z (abs (q e)) := by
        intro e he
        exact hz e (Finset.mem_union.mpr (Or.inr he))
      change 0 < 3 * lineageCoefficient q z r
      exact mul_pos (by norm_num) (ihr hzR)

private theorem expansionList_length_bound {B : Cubical.Box 4}
    (w : CurrentExpansionTerm B → ℝ) (T : List (CurrentExpansionTerm B))
    (C : ℝ) (hLower : ∀ t ∈ T, 1 ≤ C * w t) :
    (T.length : ℝ) ≤ C * (T.map w).sum := by
  induction T with
  | nil => simp
  | cons t T ih =>
      have ht := hLower t (by simp)
      have htail : ∀ u ∈ T, 1 ≤ C * w u := by
        intro u hu
        exact hLower u (by simp [hu])
      have hrest := ih htail
      simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_succ]
      nlinarith

private theorem initialCurrentState_card_eq_links {B : Cubical.Box 4}
    (q : Link B → ℤ) (hq : ∀ e, q e ≠ 0) :
    (initialCurrentState q).card = Fintype.card (Link B) := by
  classical
  have hfilter : (Finset.univ.filter fun e : Link B => q e ≠ 0) = Finset.univ := by
    ext e
    simp [hq e]
  have hleaf : Function.Injective (ActivityLineage.leaf : Link B → ExpansionLineage B) := by
    intro a b hab
    cases hab
    rfl
  unfold initialCurrentState
  rw [hfilter, Finset.card_image_of_injective _ hleaf]
  simp

private theorem currentExpansion_length_le_six_pow {B : Cubical.Box 4}
    {q : Link B → ℤ} {z : ℤ → ℝ} {s : CurrentState B}
    {T : List (CurrentExpansionTerm B)} {n : ℕ}
    (hExp : IsCurrentStateExpansion q z s T)
    (hmin : ∀ t ∈ T, (6 : ℝ) ^ n * t.weight ≥ 1) :
    T.length ≤ 6 ^ n := by
  have hsum := expansionList_length_bound CurrentExpansionTerm.weight T
    ((6 : ℝ) ^ n) (by
      intro t ht
      simpa [mul_comm] using hmin t ht)
  have hnorm : (T.map CurrentExpansionTerm.weight).sum = 1 := hExp.2.2.2.2.1
  have hReal : (T.length : ℝ) ≤ (6 : ℝ) ^ n := by
    simpa [hnorm] using hsum
  exact_mod_cast hReal

theorem exists_fixedFrequencySeparatedCurrentExpansion_withLineageActivity
    {B : Cubical.Box 4} (q : Link B → ℤ) (z : ℤ → ℝ)
    (hq : ∀ e, q e ≠ 0) (hz : ∀ n, 0 ≤ z n)
    (hzpos : ∀ n, 0 < n → 0 < z n) :
    ∃ T : List (CurrentExpansionTerm B),
      IsFixedFrequencyCurrentExpansion q z T ∧
        T.length ≤ 6 ^ Fintype.card (Link B) := by
  classical
  let s₀ := initialCurrentState q
  obtain ⟨T, hT, hTmin⟩ := exists_currentStateExpansion q z s₀.card s₀ rfl
    (currentState_initial_valid)
  refine ⟨T, ?_, ?_⟩
  · refine ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1,
      hT.2.2.2.2.1, ?_, ?_, ?_⟩
    · intro φ
      have hsourceφ := currentStateProduct_initial_eq_source q z φ hq
      calc
        sourceCurrentProduct q z φ = currentStateProduct q z φ s₀ := by
          simpa [s₀] using hsourceφ.symm
        _ = currentExpansionSum q z φ T := by
          simpa [s₀] using hT.2.2.2.2.2 φ
    · intro t ht h hh
      have hstate := hT.2.2.1 t ht
      obtain ⟨hGood, hqLineage⟩ := hstate.1 h hh
      have hzLineage : ∀ e ∈ h.all, 0 < z (abs (q e)) := by
        intro e he
        have hqE := hqLineage e he
        have habs : 0 < abs (q e) := abs_pos.mpr hqE
        exact hzpos (abs (q e)) habs
      exact lineageCoefficient_pos_of_good hGood hzLineage
    · intro t ht h hh
      have hstate := hT.2.2.1 t ht
      obtain ⟨hGood, hqLineage⟩ := hstate.1 h hh
      simpa [lineageCoefficient, lineageCurrent, currentNear] using
        cubical_currentActivity_bound hGood q hqLineage z hz
  · have hlen := currentExpansion_length_le_six_pow hT hTmin
    have hcard : s₀.card = Fintype.card (Link B) := by
      simpa [s₀] using initialCurrentState_card_eq_links q hq
    simpa [hcard] using hlen

end FroehlichSpencer.FS82.Currents
