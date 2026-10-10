/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Obstacles

/-!
# First-exit regions inside an arbitrary parent

FS83 Lemma 3.3 / Appendix D.
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

private theorem nnComponent_mono {ν : ℕ} {S S' : Set (Site ν)} (h : S ⊆ S') (x : Site ν) :
    nnComponent S x ⊆ nnComponent S' x := by
  rintro y ⟨hx, hy⟩
  exact ⟨h hx, Relation.ReflTransGen.mono
    (fun a b (hab : chainStep (siteDist ν) S (5 / 4) a b) => ⟨h hab.1, h hab.2.1, hab.2.2⟩)
    _ _ hy⟩

private theorem mem_obstacleUnion_of {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {n j : ℕ}
    {C : Set (Site ν)} {c x : Site ν} (hj : j < n) (hC : C ∈ G j) (hc : c ∈ C)
    (hx : siteDist ν x c ≤ 4 * scaleD K₀ j + 2) : x ∈ obstacleUnion K₀ G n := by
  simp only [obstacleUnion, Set.mem_iUnion, Finset.mem_range]
  exact ⟨j, hj, C, hC, c, hc, hx⟩

/-- The relative fill inside `A` of the ball `D₀ = A ∩ B(p, r)`: `D₀` together with the
nearest-neighbour components, inside `U_A = A ∩ U`, of the points of `D₀ ∩ U_A`. -/
private def relFill {ν : ℕ} (K₀ : ℝ) (G : ℕ → Set (Set (Site ν))) (n : ℕ) (A : Set (Site ν))
    (p : Site ν) (r : ℝ) : Set (Site ν) :=
  {y | y ∈ A ∧ siteDist ν p y ≤ r} ∪
    ⋃ a ∈ {y | y ∈ A ∧ siteDist ν p y ≤ r} ∩ (A ∩ obstacleUnion K₀ G n),
      nnComponent (A ∩ obstacleUnion K₀ G n) a

private theorem relFill_subset {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {n : ℕ}
    {A : Set (Site ν)} {p : Site ν} {r : ℝ} : relFill K₀ G n A p r ⊆ A := by
  intro y hy
  rcases hy with hy | hy
  · exact hy.1
  · obtain ⟨a, -, hy⟩ := Set.mem_iUnion₂.1 hy
    exact (chainCluster_subset a hy).1

private theorem relFill_finite {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {n : ℕ}
    {A : Set (Site ν)} (hA : A.Finite) (p : Site ν) (r : ℝ) :
    (relFill K₀ G n A p r).Finite := hA.subset relFill_subset

private theorem relFill_dist {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) {A : Set (Site ν)}
    {p : Site ν} {r : ℝ} {w : Site ν} (hw : w ∈ relFill K₀ G (k + 1) A p r) :
    siteDist ν p w ≤ r + 10 * scaleD K₀ k := by
  have hd := scaleD_pos K₀ k
  rcases hw with hw | hw
  · linarith [hw.2]
  · obtain ⟨a, ⟨haD, haU⟩, hw⟩ := Set.mem_iUnion₂.1 hw
    have h1 : a ∈ nnComponent (obstacleUnion K₀ G (k + 1)) a := mem_chainCluster_self haU.2
    have h2 := diam_nnComponent_obstacleUnion_lt hK hG k h1
      (nnComponent_mono Set.inter_subset_right a hw)
    have h3 := siteDist_triangle ν p w a
    have h4 := siteDist_comm ν w a
    linarith [haD.2]

private theorem relFill_closed {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} {n : ℕ}
    {A : Set (Site ν)} {p : Site ν} {r : ℝ} {a b : Site ν} (ha : a ∈ relFill K₀ G n A p r)
    (haU : a ∈ A ∩ obstacleUnion K₀ G n) (hbU : b ∈ A ∩ obstacleUnion K₀ G n)
    (hab : siteDist ν a b = 1) : b ∈ relFill K₀ G n A p r := by
  have hlt : siteDist ν a b < 5 / 4 := by rw [hab]; norm_num
  rcases ha with ha | ha
  · refine Or.inr (Set.mem_iUnion₂.2 ⟨a, ⟨ha, haU⟩, ?_⟩)
    exact mem_chainCluster_of_lt (mem_chainCluster_self haU) hbU hlt
  · obtain ⟨a', ha', ha⟩ := Set.mem_iUnion₂.1 ha
    exact Or.inr (Set.mem_iUnion₂.2 ⟨a', ha', mem_chainCluster_of_lt ha hbU hlt⟩)

private theorem relFill_admissible {ν : ℕ} {K₀ : ℝ} {G : ℕ → Set (Set (Site ν))} (k : ℕ)
    {A : Set (Site ν)} (hAadm : Admissible K₀ G (k + 1) A) (p : Site ν) (r : ℝ) :
    Admissible K₀ G (k + 1) (relFill K₀ G (k + 1) A p r) := by
  intro j hj C hC
  rw [Set.disjoint_left]
  rintro a ⟨haR, b, hab, hbR⟩ ⟨c, hc, hac⟩
  have aA : a ∈ A := relFill_subset haR
  by_cases hbA : b ∈ A
  · have h1 := siteDist_triangle ν b c a
    have h2 := siteDist_comm ν a b
    have haU : a ∈ A ∩ obstacleUnion K₀ G (k + 1) :=
      ⟨aA, mem_obstacleUnion_of hj hC hc (by linarith)⟩
    have hbU : b ∈ A ∩ obstacleUnion K₀ G (k + 1) :=
      ⟨hbA, mem_obstacleUnion_of hj hC hc (by linarith)⟩
    exact hbR (relFill_closed haR haU hbU hab)
  · exact Set.disjoint_left.1 (hAadm j hj C hC) ⟨aA, b, hab, hbA⟩ ⟨c, hc, hac⟩

private theorem vertexBoundary_component_subset {ν : ℕ} {S : Set (Site ν)} {p : Site ν} :
    vertexBoundary (nnComponent S p) ⊆ vertexBoundary S := by
  rintro a ⟨ha, b, hab, hb⟩
  refine ⟨chainCluster_subset p ha, b, hab, fun hbS => hb ?_⟩
  exact mem_chainCluster_of_lt ha hbS (by rw [hab]; norm_num)

/--
The fill uses all of `D₀ ∩ U_A`
(not only the relative boundary), which is harmless and simplifies the argument.
-/
theorem exists_firstExitRegion {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) (k : ℕ) {A : Set (Site ν)}
    (hA : A.Finite) (hAadm : Admissible K₀ G (k + 1) A) {p : Site ν} (hp : p ∈ A) :
    ∃ R : Set (Site ν), R.Finite ∧ R ⊆ A ∧ p ∈ R ∧ (∀ x ∈ R, ∀ y ∈ R, y ∈ nnComponent R x) ∧
      Admissible K₀ G (k + 1) R ∧ DiamLE (siteDist ν) R (3 * scaleD K₀ (k + 1) / 2) ∧
      (∀ a ∈ vertexBoundary R \ vertexBoundary A, scaleD K₀ (k + 1) / 2 ≤ siteDist ν p a) ∧
      (∀ u ∈ R, ∀ u' ∈ A \ R, siteDist ν u u' = 1 → scaleD K₀ (k + 1) / 2 ≤ siteDist ν p u) := by
  have hd := scaleD_pos K₀ k
  have h6 : 10 * scaleD K₀ k + 3 ≤ scaleD K₀ (k + 1) / 4 := hK.2.2.2.2.2.2.1 k
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 3 * scaleD K₀ (k + 1) / 4 - 10 * scaleD K₀ k - 2 := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by linarith
  have hpF : p ∈ relFill K₀ G (k + 1) A p r :=
    Or.inl ⟨hp, by rw [siteDist_self]; exact hr0⟩
  obtain ⟨R, hR⟩ : ∃ R, R = nnComponent (relFill K₀ G (k + 1) A p r) p := ⟨_, rfl⟩
  have hpR : p ∈ R := by rw [hR]; exact mem_chainCluster_self hpF
  have hRF : R ⊆ relFill K₀ G (k + 1) A p r := by rw [hR]; exact chainCluster_subset p
  have hclose : ∀ a ∈ R, ∀ b ∈ relFill K₀ G (k + 1) A p r, siteDist ν a b = 1 → b ∈ R := by
    intro a ha b hb hab
    rw [hR] at ha ⊢
    exact mem_chainCluster_of_lt ha hb (by rw [hab]; norm_num)
  have key : ∀ a ∈ R, ∀ b ∈ A, siteDist ν a b = 1 → b ∉ R →
      scaleD K₀ (k + 1) / 2 ≤ siteDist ν p a := by
    intro a ha b hbA hab hbR
    have hbF : b ∉ relFill K₀ G (k + 1) A p r := fun h => hbR (hclose a ha b h hab)
    have h1 : r < siteDist ν p b := by
      by_contra h
      exact hbF (Or.inl ⟨hbA, not_lt.1 h⟩)
    have h2 := siteDist_triangle ν p b a
    have h3 := siteDist_comm ν a b
    linarith
  refine ⟨R, (relFill_finite hA p r).subset hRF, hRF.trans relFill_subset, hpR, ?_, ?_, ?_, ?_,
    ?_⟩
  · have hRcl : ∀ c ∈ R, Relation.ReflTransGen (chainStep (siteDist ν) R (5 / 4)) p c :=
      ((eq_chainCluster_iff (d := siteDist ν) (S := relFill K₀ G (k + 1) A p r) (ρ := 5 / 4)
        (C := R) hpR).1 hR).2.2
    intro x hx y hy
    have hx' : x ∈ nnComponent R p := ⟨hpR, hRcl x hx⟩
    have hy' : y ∈ nnComponent R p := ⟨hpR, hRcl y hy⟩
    have e := chainCluster_eq_of_mem (d := siteDist ν) (S := R) (ρ := 5 / 4)
      (siteDist_comm ν) hx'
    show y ∈ chainCluster (siteDist ν) R (5 / 4) x
    rw [e]
    exact hy'
  · intro j hj C hC
    have hvb : vertexBoundary R ⊆ vertexBoundary (relFill K₀ G (k + 1) A p r) := by
      rw [hR]; exact vertexBoundary_component_subset
    exact (relFill_admissible k hAadm p r j hj C hC).mono_left hvb
  · intro a ha b hb
    have h1 := relFill_dist hK hG k (hRF (by exact ha))
    have h2 := relFill_dist hK hG k (hRF hb)
    have h3 := siteDist_triangle ν a b p
    have h4 := siteDist_comm ν p a
    linarith
  · rintro a ⟨⟨haR, b, hab, hbR⟩, haN⟩
    have hbA : b ∈ A := by
      by_contra hbA
      exact haN ⟨relFill_subset (hRF haR), b, hab, hbA⟩
    exact key a haR b hbA hab hbR
  · rintro u hu u' ⟨hu'A, hu'R⟩ huu
    exact key u hu u' hu'A huu hu'R

end FroehlichSpencer.T12

end
