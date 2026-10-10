/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.BasicLemmaAncestryCertificates
public import FroehlichSpencer.BKT.Charges.PatchIsolation

/-! # Leaves of certified merge histories

For a certified merge history of Lemma 4.3, the output charge equals each active leaf up to
sign on that leaf's support, and the active leaves are connected by conflict edges.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

private theorem squareDistance_realized {L : ℕ} (boundary : SquareBoundary)
    (s t : Finset (Fin L × Fin L)) (hs : s.Nonempty) (ht : t.Nonempty) :
    ∃ x ∈ s, ∃ y ∈ t, squareDistance boundary L s t = latticeDistance boundary L x y := by
  have hne : (s.product t).Nonempty := by
    obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ := ht
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  have hmem := Finset.min'_mem
    ((s.product t).image fun p => latticeDistance boundary L p.1 p.2)
    (Finset.image_nonempty.mpr hne)
  obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.mp hmem
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  refine ⟨p.1, hp1, p.2, hp2, ?_⟩
  unfold squareDistance
  split_ifs
  exact hpeq.symm

private theorem leaf_support_zero {L : ℕ} {boundary : SquareBoundary} {k : ℕ}
    {E : ChargeEnsemble L} (hE : IsBKTEnsemble E) {ρ σ : ChargeDensity L}
    (hρ : ChargeMergeHistory boundary k E ρ) (hσ : ChargeMergeHistory boundary k E σ)
    (gσ : hσ.Good) (hdisj : Disjoint hρ.allLeaves hσ.allLeaves)
    {b : ChargeDensity L} (hb : b ∈ hρ.leaves) :
    ∀ x ∈ chargeSupport b, σ x = 0 := by
  intro x hx
  by_contra hσx
  have hxσ : x ∈ chargeSupport σ :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ x, hσx⟩
  rw [hσ.good_support_eq_activeLeaves gσ hE] at hxσ
  obtain ⟨b', hb', hxb'⟩ := Finset.mem_biUnion.mp hxσ
  have hne : b ≠ b' := by
    intro heq
    subst heq
    exact (Finset.disjoint_left.mp hdisj) (hρ.leaves_subset_allLeaves hb)
      (hσ.leaves_subset_allLeaves hb')
  exact (Set.disjoint_left.mp (hE.2 b (hρ.leaves_subset hb) b' (hσ.leaves_subset hb') hne))
    (by simpa [chargeSupport, Function.mem_support] using hx)
    (by simpa [chargeSupport, Function.mem_support] using hxb')

private theorem conflict_edge {L : ℕ} {boundary : SquareBoundary} {k : ℕ}
    {E : ChargeEnsemble L} (hE : IsBKTEnsemble E) {ρ σ : ChargeDensity L}
    (hρ : ChargeMergeHistory boundary k E ρ) (hσ : ChargeMergeHistory boundary k E σ)
    (gρ : hρ.Good) (gσ : hσ.Good) (hconflict : densityDistance boundary L ρ σ ≤ 2 ^ k) :
    ∃ a ∈ hρ.leaves, ∃ b ∈ hσ.leaves,
      densityDistance boundary L a b ≤ 2 ^ k ∧ densityDistance boundary L b a ≤ 2 ^ k := by
  have hne : ∀ {τ : ChargeDensity L} (hτ : ChargeMergeHistory boundary k E τ), hτ.Good →
      (chargeSupport τ).Nonempty := by
    intro τ hτ gτ
    obtain ⟨a, ha⟩ := hτ.leaves_nonempty
    have ha0 : a ≠ 0 := hE.1 a (hτ.leaves_subset ha)
    obtain ⟨x, hx⟩ := Function.ne_iff.mp ha0
    refine ⟨x, ?_⟩
    rw [hτ.good_support_eq_activeLeaves gτ hE]
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    squareDistance_realized boundary _ _ (hne hρ gρ) (hne hσ gσ)
  have hx' := hx
  have hy' := hy
  rw [hρ.good_support_eq_activeLeaves gρ hE] at hx'
  rw [hσ.good_support_eq_activeLeaves gσ hE] at hy'
  obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx'
  obtain ⟨b, hb, hyb⟩ := Finset.mem_biUnion.mp hy'
  have hdd : densityDistance boundary L ρ σ = latticeDistance boundary L x y := hxy
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · exact (squareDistance_le_latticeDistance_of_mem boundary L _ _ x y hxa hyb).trans (hdd ▸ hconflict)
  · refine (squareDistance_le_latticeDistance_of_mem boundary L _ _ y x hyb hxa).trans ?_
    rw [latticeDistance_comm boundary L y x, ← hdd]
    exact hconflict

private theorem connected_union {α : Type*} [DecidableEq α] (R : α → α → Prop)
    (A B : Finset α) (hdisj : Disjoint A B)
    (hA : ∀ U ⊆ A, U.Nonempty → U ≠ A → ∃ b ∈ U, ∃ b' ∈ A, b' ∉ U ∧ R b b')
    (hB : ∀ U ⊆ B, U.Nonempty → U ≠ B → ∃ b ∈ U, ∃ b' ∈ B, b' ∉ U ∧ R b b')
    (hedge : ∃ a ∈ A, ∃ b ∈ B, R a b ∧ R b a) :
    ∀ U ⊆ A ∪ B, U.Nonempty → U ≠ A ∪ B → ∃ b ∈ U, ∃ b' ∈ A ∪ B, b' ∉ U ∧ R b b' := by
  intro U hU hUne hUne'
  by_cases hpa : (U ∩ A).Nonempty ∧ U ∩ A ≠ A
  · obtain ⟨b, hb, b', hb', hb'U, hR⟩ :=
      hA (U ∩ A) Finset.inter_subset_right hpa.1 hpa.2
    exact ⟨b, (Finset.mem_inter.mp hb).1, b', Finset.mem_union_left _ hb',
      fun h => hb'U (Finset.mem_inter.mpr ⟨h, hb'⟩), hR⟩
  by_cases hpb : (U ∩ B).Nonempty ∧ U ∩ B ≠ B
  · obtain ⟨b, hb, b', hb', hb'U, hR⟩ :=
      hB (U ∩ B) Finset.inter_subset_right hpb.1 hpb.2
    exact ⟨b, (Finset.mem_inter.mp hb).1, b', Finset.mem_union_right _ hb',
      fun h => hb'U (Finset.mem_inter.mpr ⟨h, hb'⟩), hR⟩
  obtain ⟨a, ha, b, hb, hab, hba⟩ := hedge
  have hAB : ∀ z, z ∈ A → z ∈ B → False := fun z h1 h2 =>
    (Finset.disjoint_left.mp hdisj) h1 h2
  have hca : U ∩ A = ∅ ∨ U ∩ A = A := by
    by_cases h : (U ∩ A).Nonempty
    · exact Or.inr (by_contra fun h' => hpa ⟨h, fun h'' => h' h''⟩)
    · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp h)
  have hcb : U ∩ B = ∅ ∨ U ∩ B = B := by
    by_cases h : (U ∩ B).Nonempty
    · exact Or.inr (by_contra fun h' => hpb ⟨h, fun h'' => h' h''⟩)
    · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp h)
  rcases hca with hca | hca <;> rcases hcb with hcb | hcb
  · exfalso
    obtain ⟨z, hz⟩ := hUne
    rcases Finset.mem_union.mp (hU hz) with h | h
    · have : z ∈ U ∩ A := Finset.mem_inter.mpr ⟨hz, h⟩
      rw [hca] at this; simp at this
    · have : z ∈ U ∩ B := Finset.mem_inter.mpr ⟨hz, h⟩
      rw [hcb] at this; simp at this
  · -- U = B
    have hUB : ∀ z, z ∈ U → z ∈ B := by
      intro z hz
      rcases Finset.mem_union.mp (hU hz) with h | h
      · have : z ∈ U ∩ A := Finset.mem_inter.mpr ⟨hz, h⟩
        rw [hca] at this; simp at this
      · exact h
    refine ⟨b, ?_, a, Finset.mem_union_left _ ha, ?_, hba⟩
    · have : b ∈ U ∩ B := by rw [hcb]; exact hb
      exact (Finset.mem_inter.mp this).1
    · intro h
      exact hAB a ha (hUB a h)
  · -- U = A
    have hUA : ∀ z, z ∈ U → z ∈ A := by
      intro z hz
      rcases Finset.mem_union.mp (hU hz) with h | h
      · exact h
      · have : z ∈ U ∩ B := Finset.mem_inter.mpr ⟨hz, h⟩
        rw [hcb] at this; simp at this
    refine ⟨a, ?_, b, Finset.mem_union_right _ hb, ?_, hab⟩
    · have : a ∈ U ∩ A := by rw [hca]; exact ha
      exact (Finset.mem_inter.mp this).1
    · intro h
      exact hAB b (hUA b h) hb
  · exfalso
    apply hUne'
    ext z
    constructor
    · exact fun h => hU h
    · intro hz
      rcases Finset.mem_union.mp hz with h | h
      · have : z ∈ U ∩ A := by rw [hca]; exact h
        exact (Finset.mem_inter.mp this).1
      · have : z ∈ U ∩ B := by rw [hcb]; exact h
        exact (Finset.mem_inter.mp this).1

/-- On the support of an active leaf, a certified history's output is that leaf up to sign. -/
theorem ChargeMergeHistory.good_sign_on_leaf {L : ℕ} {boundary : SquareBoundary} {k : ℕ}
    {E : ChargeEnsemble L} {ρ : ChargeDensity L} (h : ChargeMergeHistory boundary k E ρ)
    (hg : h.Good) (hE : IsBKTEnsemble E) :
    ∀ b ∈ h.leaves, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ x ∈ chargeSupport b, ρ x = s * b x := by
  induction hg with
  | leaf ρ hρ =>
      intro b hb
      have : b = ρ := by simpa [ChargeMergeHistory.leaves] using hb
      subst this
      exact ⟨1, Or.inl rfl, fun x _ => by simp⟩
  | @add ρ σ hρ hσ hconflict gρ gσ hdisj ihρ ihσ =>
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · obtain ⟨s, hs, hx⟩ := ihρ b hb
        refine ⟨s, hs, fun x hxb => ?_⟩
        have := leaf_support_zero hE hρ hσ gσ hdisj hb x hxb
        simp [Pi.add_apply, this, hx x hxb]
      · obtain ⟨s, hs, hx⟩ := ihσ b hb
        refine ⟨s, hs, fun x hxb => ?_⟩
        have := leaf_support_zero hE hσ hρ gρ hdisj.symm hb x hxb
        simp [Pi.add_apply, this, hx x hxb]
  | @sub ρ σ hρ hσ hconflict gρ gσ hdisj ihρ ihσ =>
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · obtain ⟨s, hs, hx⟩ := ihρ b hb
        refine ⟨s, hs, fun x hxb => ?_⟩
        have := leaf_support_zero hE hρ hσ gσ hdisj hb x hxb
        simp [Pi.sub_apply, this, hx x hxb]
      · obtain ⟨s, hs, hx⟩ := ihσ b hb
        refine ⟨-s, ?_, fun x hxb => ?_⟩
        · rcases hs with hs | hs
          · exact Or.inr (by simp [hs])
          · exact Or.inl (by simp [hs])
        have := leaf_support_zero hE hσ hρ gρ hdisj.symm hb x hxb
        simp [Pi.sub_apply, this, hx x hxb]
  | keepLeft hconflict gρ gσ hdisj ihρ ihσ => exact ihρ
  | keepRight hconflict gρ gσ hdisj ihρ ihσ => exact ihσ

/-- The active leaves of a certified history are connected by conflict edges: every proper
nonempty subset has a member within distance `2^k` of a leaf outside it. -/
theorem ChargeMergeHistory.good_leaves_connected {L : ℕ} {boundary : SquareBoundary} {k : ℕ}
    {E : ChargeEnsemble L} {ρ : ChargeDensity L} (h : ChargeMergeHistory boundary k E ρ)
    (hg : h.Good) (hE : IsBKTEnsemble E) :
    ∀ U ⊆ h.leaves, U.Nonempty → U ≠ h.leaves →
      ∃ b ∈ U, ∃ b' ∈ h.leaves, b' ∉ U ∧ densityDistance boundary L b b' ≤ 2 ^ k := by
  classical
  induction hg with
  | leaf ρ hρ =>
      intro U hU hne hne'
      exfalso
      apply hne'
      obtain ⟨z, hz⟩ := hne
      have hzρ : z = ρ := by simpa [ChargeMergeHistory.leaves] using hU hz
      subst hzρ
      ext y
      simp only [ChargeMergeHistory.leaves, Finset.mem_singleton]
      exact ⟨fun hy => by simpa [ChargeMergeHistory.leaves] using hU hy,
        fun hy => hy ▸ hz⟩
  | @add ρ σ hρ hσ hconflict gρ gσ hdisj ihρ ihσ =>
      refine connected_union _ hρ.leaves hσ.leaves ?_ ihρ ihσ
        (conflict_edge hE hρ hσ gρ gσ hconflict)
      exact Finset.disjoint_left.mpr fun a ha hb => (Finset.disjoint_left.mp hdisj)
        (hρ.leaves_subset_allLeaves ha) (hσ.leaves_subset_allLeaves hb)
  | @sub ρ σ hρ hσ hconflict gρ gσ hdisj ihρ ihσ =>
      refine connected_union _ hρ.leaves hσ.leaves ?_ ihρ ihσ
        (conflict_edge hE hρ hσ gρ gσ hconflict)
      exact Finset.disjoint_left.mpr fun a ha hb => (Finset.disjoint_left.mp hdisj)
        (hρ.leaves_subset_allLeaves ha) (hσ.leaves_subset_allLeaves hb)
  | keepLeft hconflict gρ gσ hdisj ihρ ihσ => exact ihρ
  | keepRight hconflict gρ gσ hdisj ihρ ihσ => exact ihσ

end FroehlichSpencer.BKT

end
