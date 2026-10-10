/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.SourceLatticeChain

/-!
# Connected components of finite co-closed currents

Components use incidence at the finite `Λ*` vertex carrier. Exterior endpoints
are deliberately absent from the incidence relation.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents

open Cubical
open FroehlichSpencer.FS82.Gaussian
noncomputable section
open Classical

/-- A link is incident to a finite `Λ*` vertex when its one-link divergence
coefficient there is nonzero. This is the (a) vertex incidence; exterior
endpoints do not occur in this predicate. -/
@[expose] def linkIncidentAt {B : Box 4} (e : Link B)
    (v : SourceDualZeroCells B) : Prop :=
  currentDivergence (Finsupp.single e (1 : ℤ)) v ≠ 0

/-- Two links are adjacent exactly when they share a finite `Λ*` vertex. -/
@[expose] def linksShareFiniteVertex {B : Box 4} (e f : Link B) : Prop :=
  ∃ v : SourceDualZeroCells B, linkIncidentAt e v ∧ linkIncidentAt f v

/-- The incidence relation restricted to the support of one current. -/
@[expose] def currentLinkStep {B : Box 4} (j : IntegerCurrent B)
    (e f : Link B) : Prop :=
  e ∈ j.support ∧ f ∈ j.support ∧ linksShareFiniteVertex e f

/-- The quotient class of a link in the equivalence closure of support-link
incidence. For supported links these are precisely the connected components. -/
abbrev CurrentComponentClass {B : Box 4} (j : IntegerCurrent B) :=
  Quotient (Relation.EqvGen.setoid (currentLinkStep j))

@[expose] def currentComponentOf {B : Box 4} (j : IntegerCurrent B)
    (e : Link B) : CurrentComponentClass j :=
  Quotient.mk _ e

@[expose] def currentComponents {B : Box 4} (j : IntegerCurrent B) :
    Finset (CurrentComponentClass j) :=
  j.support.image (currentComponentOf j)

@[expose] def currentComponentSupport {B : Box 4} (j : IntegerCurrent B)
    (c : CurrentComponentClass j) : Finset (Link B) :=
  j.support.filter fun e => currentComponentOf j e = c

@[expose] def currentComponentCurrent {B : Box 4} (j : IntegerCurrent B)
    (c : CurrentComponentClass j) : IntegerCurrent B :=
  j.filter fun e => currentComponentOf j e = c

theorem currentComponentOf_eq_iff {B : Box 4}
    (j : IntegerCurrent B) (e f : Link B) :
    currentComponentOf j e = currentComponentOf j f ↔
      Relation.EqvGen (currentLinkStep j) e f := by
  constructor
  · exact Quotient.exact
  · intro h
    change Quotient.mk _ e = Quotient.mk _ f
    exact Quotient.sound h

theorem currentComponentSupport_rep {B : Box 4}
    (j : IntegerCurrent B) (e : Link B) (he : e ∈ j.support) :
    e ∈ currentComponentSupport j (currentComponentOf j e) := by
  exact Finset.mem_filter.mpr ⟨he, rfl⟩

theorem currentComponentSupport_nonempty {B : Box 4}
    (j : IntegerCurrent B) {c : CurrentComponentClass j}
    (hc : c ∈ currentComponents j) :
    (currentComponentSupport j c).Nonempty := by
  rcases Finset.mem_image.mp hc with ⟨e, he, rfl⟩
  exact ⟨e, currentComponentSupport_rep j e he⟩

@[simp] theorem currentComponentCurrent_apply {B : Box 4}
    (j : IntegerCurrent B) (c : CurrentComponentClass j) (e : Link B) :
    currentComponentCurrent j c e =
      if currentComponentOf j e = c then j e else 0 := by
  simp [currentComponentCurrent, Finsupp.filter_apply]

theorem currentComponentCurrent_support {B : Box 4}
    (j : IntegerCurrent B) (c : CurrentComponentClass j) :
    (currentComponentCurrent j c).support = currentComponentSupport j c := by
  rw [currentComponentCurrent, Finsupp.support_filter]
  rfl

theorem currentComponentSupport_subset {B : Box 4}
    (j : IntegerCurrent B) (c : CurrentComponentClass j) :
    currentComponentSupport j c ⊆ j.support := by
  intro e he
  exact (Finset.mem_filter.mp he).1

theorem currentComponentOf_eq_of_shareVertex {B : Box 4}
    (j : IntegerCurrent B) {e f : Link B}
    (he : e ∈ j.support) (hf : f ∈ j.support)
    (hshare : linksShareFiniteVertex e f) :
    currentComponentOf j e = currentComponentOf j f := by
  apply Quotient.sound
  exact Relation.EqvGen.rel e f ⟨he, hf, hshare⟩

theorem currentComponentSupport_biUnion {B : Box 4}
    (j : IntegerCurrent B) :
    (currentComponents j).biUnion (currentComponentSupport j) = j.support := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_biUnion.mp he with ⟨c, hc, hce⟩
    exact (Finset.mem_filter.mp hce).1
  · intro he
    apply Finset.mem_biUnion.mpr
    refine ⟨currentComponentOf j e,
      Finset.mem_image.mpr ⟨e, he, rfl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨he, rfl⟩

theorem currentComponentSupport_pairwiseDisjoint {B : Box 4}
    (j : IntegerCurrent B) :
    (↑(currentComponents j) : Set (CurrentComponentClass j)).PairwiseDisjoint
      (currentComponentSupport j) := by
  intro c hc d hd hne
  apply Finset.disjoint_left.mpr
  intro e hec hed
  have h₁ : currentComponentOf j e = c := (Finset.mem_filter.mp hec).2
  have h₂ : currentComponentOf j e = d := (Finset.mem_filter.mp hed).2
  exact hne (h₁.symm.trans h₂)

theorem currentComponentCurrent_sum_apply {B : Box 4}
    (j : IntegerCurrent B) (e : Link B) :
    (∑ c ∈ currentComponents j, currentComponentCurrent j c) e =
      ∑ c ∈ currentComponents j, currentComponentCurrent j c e := by
  classical
  have hEval :
      (∑ c ∈ currentComponents j, currentComponentCurrent j c) e =
        ∑ c ∈ currentComponents j, currentComponentCurrent j c e := by
    induction currentComponents j using Finset.induction_on with
    | empty => simp
    | @insert c S hc ih =>
        simp only [Finset.sum_insert hc, Finsupp.add_apply, ih]
  exact hEval

theorem currentComponentCurrent_sum {B : Box 4}
    (j : IntegerCurrent B) :
    (∑ c ∈ currentComponents j, currentComponentCurrent j c) = j := by
  classical
  ext e
  rw [currentComponentCurrent_sum_apply]
  simp only [currentComponentCurrent_apply]
  rw [Finset.sum_ite_eq]
  by_cases he : j e = 0
  · simp [he]
  · have hmem : currentComponentOf j e ∈ currentComponents j :=
      Finset.mem_image.mpr ⟨e, Finsupp.mem_support_iff.mpr he, rfl⟩
    simp [hmem]

theorem integerCurrent_univ_sum_single {B : Box 4}
    (j : IntegerCurrent B) :
    j = ∑ e : Link B, Finsupp.single e (j e) := by
  classical
  ext f
  simp

theorem currentDivergence_zero {B : Box 4}
    (v : SourceDualZeroCells B) :
    currentDivergence (0 : IntegerCurrent B) v = 0 := by
  have h := currentDivergence_add (0 : IntegerCurrent B) 0 v
  have h' : currentDivergence (0 : IntegerCurrent B) v =
      currentDivergence (0 : IntegerCurrent B) v +
        currentDivergence (0 : IntegerCurrent B) v := by
    simpa using h
  linarith

theorem currentDivergence_finset_sum {B : Box 4} {ι : Type*}
    (S : Finset ι) (q : ι → IntegerCurrent B)
    (v : SourceDualZeroCells B) :
    currentDivergence (∑ i ∈ S, q i) v =
      ∑ i ∈ S, currentDivergence (q i) v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [currentDivergence_zero]
  | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      rw [currentDivergence_add, ih]

theorem currentDivergence_eq_sum_single {B : Box 4}
    (j : IntegerCurrent B) (v : SourceDualZeroCells B) :
    currentDivergence j v =
      ∑ e : Link B, currentDivergence (Finsupp.single e (j e)) v := by
  calc
    currentDivergence j v =
        currentDivergence (∑ e : Link B, Finsupp.single e (j e)) v := by
          congr 1
          exact integerCurrent_univ_sum_single j
    _ = ∑ e : Link B, currentDivergence (Finsupp.single e (j e)) v :=
      currentDivergence_finset_sum Finset.univ
        (fun e : Link B => Finsupp.single e (j e)) v

@[expose] def currentLinkDivergenceContribution {B : Box 4}
    (j : IntegerCurrent B) (e : Link B) (v : SourceDualZeroCells B) : ℝ :=
  ((j e : ℤ) : ℝ) * currentDivergence (Finsupp.single e (1 : ℤ)) v

theorem currentDivergence_single_scale {B : Box 4}
    (e : Link B) (n : ℤ) (v : SourceDualZeroCells B) :
    currentDivergence (Finsupp.single e n) v =
      ((n : ℤ) : ℝ) * currentDivergence (Finsupp.single e (1 : ℤ)) v := by
  rw [currentDivergence_single, currentDivergence_single]
  ring

theorem currentDivergence_single_zero {B : Box 4}
    (e : Link B) (v : SourceDualZeroCells B) :
    currentDivergence (Finsupp.single e (0 : ℤ)) v = 0 := by
  rw [currentDivergence_single_scale]
  simp

theorem currentDivergence_single_current_eq_zero_of_contribution_eq_zero
    {B : Box 4} (j : IntegerCurrent B) (e : Link B)
    (v : SourceDualZeroCells B)
    (hzero : currentLinkDivergenceContribution j e v = 0) :
    currentDivergence (Finsupp.single e (j e)) v = 0 := by
  rw [currentDivergence_single_scale]
  simpa [currentLinkDivergenceContribution] using hzero


theorem currentComponentOf_eq_of_nonzero_contributions
    {B : Box 4} (j : IntegerCurrent B) {e f : Link B}
    (v : SourceDualZeroCells B)
    (he : currentLinkDivergenceContribution j e v ≠ 0)
    (hf : currentLinkDivergenceContribution j f v ≠ 0) :
    currentComponentOf j e = currentComponentOf j f := by
  have hje : j e ≠ 0 := by
    intro h
    apply he
    simp [currentLinkDivergenceContribution, h]
  have hjf : j f ≠ 0 := by
    intro h
    apply hf
    simp [currentLinkDivergenceContribution, h]
  have hincE : linkIncidentAt e v := by
    intro hzero
    apply he
    simp [currentLinkDivergenceContribution, hzero]
  have hincF : linkIncidentAt f v := by
    intro hzero
    apply hf
    simp [currentLinkDivergenceContribution, hzero]
  exact currentComponentOf_eq_of_shareVertex j
    (Finsupp.mem_support_iff.mpr hje)
    (Finsupp.mem_support_iff.mpr hjf) ⟨v, hincE, hincF⟩

theorem currentComponentCurrent_divergence_eq_zero_of_divergence_eq_zero
    {B : Box 4} (j : IntegerCurrent B) (c : CurrentComponentClass j)
    (hdiv : currentDivergence j = 0) :
    currentDivergence (currentComponentCurrent j c) = 0 := by
  classical
  funext v
  by_cases hex : ∃ e : Link B,
      currentLinkDivergenceContribution j e v ≠ 0 ∧
        currentComponentOf j e = c
  · obtain ⟨e₀, he₀, he₀c⟩ := hex
    have hEq : currentDivergence (currentComponentCurrent j c) v =
        currentDivergence j v := by
      rw [currentDivergence_eq_sum_single, currentDivergence_eq_sum_single]
      apply Finset.sum_congr rfl
      intro e he
      rw [currentComponentCurrent_apply]
      by_cases hclass : currentComponentOf j e = c
      · simp [hclass]
      · have hterm : currentLinkDivergenceContribution j e v = 0 := by
          by_contra hne
          have heclass := currentComponentOf_eq_of_nonzero_contributions
            j v hne he₀
          exact hclass (heclass.trans he₀c)
        simp only [hclass, ite_false]
        rw [currentDivergence_single_zero,
          currentDivergence_single_current_eq_zero_of_contribution_eq_zero
            j e v hterm]
    calc
      currentDivergence (currentComponentCurrent j c) v = currentDivergence j v := hEq
      _ = 0 := congrFun hdiv v
  · rw [currentDivergence_eq_sum_single]
    apply Finset.sum_eq_zero
    intro e he
    rw [currentComponentCurrent_apply]
    by_cases hclass : currentComponentOf j e = c
    · have hterm : currentLinkDivergenceContribution j e v = 0 := by
          by_contra hne
          exact hex ⟨e, hne, hclass⟩
      simp only [hclass, ite_true]
      exact currentDivergence_single_current_eq_zero_of_contribution_eq_zero
        j e v hterm
    · simp only [hclass, ite_false]
      exact currentDivergence_single_zero e v


theorem currentComponentLength_additive {B : Box 4}
    (j : IntegerCurrent B) :
    j.support.card =
      ∑ c ∈ currentComponents j, (currentComponentSupport j c).card := by
  rw [← currentComponentSupport_biUnion j,
    Finset.card_biUnion (currentComponentSupport_pairwiseDisjoint j)]

@[expose] def currentL1Norm {B : Box 4} (j : IntegerCurrent B) : ℝ :=
  ∑ e ∈ j.support, |((j e : ℤ) : ℝ)|

@[expose] def currentEnergy {B : Box 4} (j : IntegerCurrent B) : ℝ :=
  ∑ e ∈ j.support, ((j e : ℤ) : ℝ)^2

@[expose] def currentLength {B : Box 4} (j : IntegerCurrent B) : ℝ :=
  (j.support.card : ℝ)

theorem currentLength_additive {B : Box 4} (j : IntegerCurrent B) :
    currentLength j =
      ∑ c ∈ currentComponents j,
        ((currentComponentSupport j c).card : ℝ) := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (currentComponentLength_additive j)
  simpa [currentLength, Nat.cast_sum] using h

theorem currentEnergy_nonneg {B : Box 4} (j : IntegerCurrent B) :
    0 ≤ currentEnergy j := by
  unfold currentEnergy
  exact Finset.sum_nonneg fun e he => sq_nonneg ((j e : ℤ) : ℝ)

theorem currentComponentL1Norm_additive {B : Box 4}
    (j : IntegerCurrent B) :
    currentL1Norm j =
      ∑ c ∈ currentComponents j, currentL1Norm (currentComponentCurrent j c) := by
  classical
  unfold currentL1Norm
  rw [← currentComponentSupport_biUnion j,
    Finset.sum_biUnion (currentComponentSupport_pairwiseDisjoint j)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [currentComponentCurrent_support]
  apply Finset.sum_congr rfl
  intro e he
  rw [currentComponentCurrent_apply]
  have heclass := (Finset.mem_filter.mp he).2
  simp [heclass]

theorem currentEnergy_additive {B : Box 4}
    (j : IntegerCurrent B) :
    currentEnergy j =
      ∑ c ∈ currentComponents j, currentEnergy (currentComponentCurrent j c) := by
  classical
  unfold currentEnergy
  rw [← currentComponentSupport_biUnion j,
    Finset.sum_biUnion (currentComponentSupport_pairwiseDisjoint j)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [currentComponentCurrent_support]
  apply Finset.sum_congr rfl
  intro e he
  rw [currentComponentCurrent_apply]
  have heclass := (Finset.mem_filter.mp he).2
  simp [heclass]

theorem currentComponentEnergy_ge_length {B : Box 4}
    (j : IntegerCurrent B) (c : CurrentComponentClass j) :
    ((currentComponentSupport j c).card : ℝ) ≤
      currentEnergy (currentComponentCurrent j c) := by
  classical
  rw [currentEnergy, currentComponentCurrent_support]
  calc
    ((currentComponentSupport j c).card : ℝ) =
        ∑ e ∈ currentComponentSupport j c, (1 : ℝ) := by simp
    _ ≤ ∑ e ∈ currentComponentSupport j c,
          ((currentComponentCurrent j c e : ℤ) : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro e he
      have hne : currentComponentCurrent j c e ≠ 0 :=
        Finsupp.mem_support_iff.mp (by simpa [currentComponentCurrent_support] using he)
      have hpos : 1 ≤ Int.natAbs (currentComponentCurrent j c e) :=
        Int.natAbs_pos.mpr hne
      have hreal : (1 : ℝ) ≤
          (Int.natAbs (currentComponentCurrent j c e) : ℝ) := by
        exact_mod_cast hpos
      rw [Nat.cast_natAbs, Int.cast_abs] at hreal
      by_cases hsign : 0 ≤ ((currentComponentCurrent j c e : ℤ) : ℝ)
      · rw [abs_of_nonneg hsign] at hreal
        nlinarith
      · rw [abs_of_neg (lt_of_not_ge hsign)] at hreal
        nlinarith

theorem currentPhase_finset_sum {B : Box 4} {ι : Type*}
    (φ : Link B → ℝ) (S : Finset ι) (q : ι → Link B → ℤ) :
    currentPhase φ (∑ i ∈ S, q i) = ∑ i ∈ S, currentPhase φ (q i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [currentPhase]
  | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      rw [currentPhase_add, ih]

theorem currentPhase_eq_sum_components {B : Box 4}
    (φ : Link B → ℝ) (j : IntegerCurrent B) :
    currentPhase φ j =
      ∑ c ∈ currentComponents j, currentPhase φ (currentComponentCurrent j c) := by
  calc
    currentPhase φ j =
        currentPhase φ (∑ c ∈ currentComponents j,
          fun e => currentComponentCurrent j c e) := by
          congr 1
          funext e
          calc
            j e = (∑ c ∈ currentComponents j, currentComponentCurrent j c) e :=
              congrArg (fun q : IntegerCurrent B => q e)
                (currentComponentCurrent_sum j).symm
            _ = ∑ c ∈ currentComponents j, currentComponentCurrent j c e :=
              currentComponentCurrent_sum_apply j e
            _ = (∑ c ∈ currentComponents j,
                fun e => currentComponentCurrent j c e) e := by
              symm
              exact Finset.sum_apply e (currentComponents j)
                (fun c e => currentComponentCurrent j c e)
    _ = ∑ c ∈ currentComponents j,
          currentPhase φ (currentComponentCurrent j c) :=
      currentPhase_finset_sum φ (currentComponents j)
        (fun c e => currentComponentCurrent j c e)


end
end FroehlichSpencer.FS82.Currents

end
