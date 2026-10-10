/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Obstacles
public import FroehlichSpencer.T12.Events

/-!
# Nested finite-level annuli
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale


def annulusRegion {ν : ℕ} (K₀ : ℝ) (G : ℕ → Set (Set (Site ν))) (n : ℕ) (a : Site ν) (l : ℝ) :
    Set (Site ν) :=
  obstacleFill K₀ G n {x | siteDist ν a x ≤ l / 2 + 2}

private theorem siteDist_eq_sqrt {ν : ℕ} (x y : Site ν) :
    siteDist ν x y = Real.sqrt (∑ j, (((x j - y j : ℤ)) : ℝ) ^ 2) := rfl

/-- A nearest-neighbour lattice step from `y` toward `a ≠ y` that does not increase the Euclidean
distance to `a` and strictly decreases the `ℓ¹` distance. -/
theorem exists_step {ν : ℕ} (a y : Site ν) (hy : y ≠ a) :
    ∃ y' : Site ν, siteDist ν y' y = 1 ∧ siteDist ν a y' ≤ siteDist ν a y ∧
      ∑ j, (y' j - a j).natAbs < ∑ j, (y j - a j).natAbs := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ a i := by
    by_contra h
    push Not at h
    exact hy (funext h)
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (s = 1 ∧ a i < y i) ∨ (s = -1 ∧ y i < a i) := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact ⟨-1, Or.inr ⟨rfl, h⟩⟩
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
  have hs2 : s ^ 2 = 1 := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  refine ⟨Function.update y i (y i - s), ?_, ?_, ?_⟩
  · rw [siteDist_eq_sqrt, Finset.sum_eq_single i]
    · simp only [Function.update_self]
      have : (((Function.update y i (y i - s)) i - y i : ℤ) : ℝ) ^ 2 = 1 := by
        simp only [Function.update_self]
        have : ((y i - s - y i : ℤ) : ℝ) ^ 2 = ((s ^ 2 : ℤ) : ℝ) := by push_cast; ring
        rw [this, hs2]; norm_num
      simpa using this
    · intro j _ hj
      simp [Function.update_of_ne hj]
    · simp
  · rw [siteDist_eq_sqrt, siteDist_eq_sqrt]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      have : (a j - (y j - s)) ^ 2 ≤ (a j - y j) ^ 2 := by
        rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> nlinarith only [h]
      exact_mod_cast this
    · simp [Function.update_of_ne hj]
  · apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega
      · simp [Function.update_of_ne hj]
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      simp only [Function.update_self]
      rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

/-- Lattice Euclidean balls around a lattice point are nearest-neighbour connected. -/
private theorem ball_nnConnected {ν : ℕ} (a : Site ν) (R : ℝ) :
    ∀ m : ℕ, ∀ y : Site ν, ∑ j, (y j - a j).natAbs ≤ m → siteDist ν a y ≤ R →
      y ∈ nnComponent {x | siteDist ν a x ≤ R} a := by
  intro m
  induction m with
  | zero =>
    intro y hm hy
    by_cases hya : y = a
    · subst hya
      exact mem_chainCluster_self hy
    · obtain ⟨y', -, -, h3⟩ := exists_step a y hya
      omega
  | succ m ih =>
    intro y hm hy
    by_cases hya : y = a
    · subst hya
      exact mem_chainCluster_self hy
    · obtain ⟨y', h1, h2, h3⟩ := exists_step a y hya
      have hy' : siteDist ν a y' ≤ R := h2.trans hy
      have := ih y' (by omega) hy'
      refine mem_chainCluster_of_lt this hy ?_
      rw [h1]; norm_num

private theorem chainCluster_mono {ν : ℕ} {S T : Set (Site ν)} (h : S ⊆ T) {x y : Site ν}
    (hy : y ∈ nnComponent S x) : y ∈ nnComponent T x := by
  obtain ⟨hx, hr⟩ := hy
  refine ⟨h hx, ?_⟩
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨h hbc.1, h hbc.2.1, hbc.2.2⟩

private theorem mem_ball_self {ν : ℕ} (a : Site ν) {R : ℝ} (hR : 0 ≤ R) :
    a ∈ {x : Site ν | siteDist ν a x ≤ R} := by
  simpa [siteDist_self] using hR


theorem exists_annulusLevel_sep : ∃ L₀ : ℝ, ∀ (K₀ l : ℝ) (k : ℕ), L₀ ≤ l →
    scaleD K₀ k / 5 ≤ l ^ (3 / 4 : ℝ) → k = 0 ∨ 10 * scaleD K₀ (k - 1) ≤ l / 2 - 2 := by
  refine ⟨100000, fun K₀ l k hl hk => ?_⟩
  rcases k with _ | m
  · exact Or.inl rfl
  right
  simp only [Nat.add_sub_cancel]
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hd := scaleD_pos K₀ m
  rw [← scaleR_eq_scaleD_succ] at hk
  unfold scaleR at hk
  have h4 : (scaleD K₀ m ^ (5 / 4 : ℝ) / 5) ^ 4 ≤ (l ^ (3 / 4 : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hk 4
  have e1 : (scaleD K₀ m ^ (5 / 4 : ℝ)) ^ 4 = scaleD K₀ m ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]; norm_num
  have e2 : (l ^ (3 / 4 : ℝ)) ^ 4 = l ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]; norm_num
  rw [div_pow, e1, e2] at h4
  have h5 : scaleD K₀ m ^ 5 ≤ 625 * l ^ 3 := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 5 ^ 4)).1 h4
    linarith only [this]
  by_contra hc
  push Not at hc
  have hlt : l / 21 < scaleD K₀ m := by linarith only [hl, hc]
  have h6 : (l / 21) ^ 5 < scaleD K₀ m ^ 5 :=
    pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
  have h7 : l ^ 5 < 21 ^ 5 * (625 * l ^ 3) := by
    have : (l / 21) ^ 5 = l ^ 5 / 21 ^ 5 := by rw [div_pow]
    rw [this, div_lt_iff₀ (by norm_num)] at h6
    nlinarith only [h5, h6]
  have hl3 : 0 < l ^ 3 := by positivity
  have h8 : l ^ 2 < 21 ^ 5 * 625 := by
    by_contra h
    push Not at h
    nlinarith only [h7, hl3, h]
  nlinarith only [hl, h8]


theorem annulusRegion_spec {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) {n : ℕ} (a : Site ν) {l : ℝ}
    (hl : 4 ≤ l) (hsep : n = 0 ∨ 10 * scaleD K₀ (n - 1) ≤ l / 2 - 2) :
    (annulusRegion K₀ G n a l).Finite ∧ a ∈ annulusRegion K₀ G n a l ∧
      (∀ x ∈ annulusRegion K₀ G n a l, ∀ y ∈ annulusRegion K₀ G n a l,
        y ∈ nnComponent (annulusRegion K₀ G n a l) x) ∧
      (∀ b ∈ vertexBoundary (annulusRegion K₀ G n a l),
        l / 2 ≤ siteDist ν a b ∧ siteDist ν a b ≤ l) ∧
      annulusRegion K₀ G n a l ⊆ {x | siteDist ν a x ≤ l} ∧
      Admissible K₀ G n (annulusRegion K₀ G n a l) := by
  set D₁ : Set (Site ν) := {x | siteDist ν a x ≤ l / 2 + 2} with hD₁
  set D₂ : Set (Site ν) := {x | siteDist ν a x ≤ l} with hD₂
  have hfin : D₁.Finite := finite_setOf_siteDist_le ν a _
  have h12 : D₁ ⊆ D₂ := fun x hx => by
    have : siteDist ν a x ≤ l / 2 + 2 := hx
    show siteDist ν a x ≤ l
    linarith only [hl, this]
  have hA : annulusRegion K₀ G n a l = obstacleFill K₀ G n D₁ := rfl
  obtain ⟨hF, hsub1, hsub2, hadm⟩ :
      (obstacleFill K₀ G n D₁).Finite ∧ D₁ ⊆ obstacleFill K₀ G n D₁ ∧
        obstacleFill K₀ G n D₁ ⊆ D₂ ∧ Admissible K₀ G n (obstacleFill K₀ G n D₁) := by
    rcases n with _ | k
    · have : obstacleFill K₀ G 0 D₁ = D₁ := by simp [obstacleFill, obstacleUnion]
      rw [this]
      exact ⟨hfin, subset_rfl, h12, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · have hs := hsep.resolve_left (Nat.succ_ne_zero _)
      refine obstacleFill_spec hK hG k hfin h12 ?_
      intro x hx y hy
      have hx' : siteDist ν a x ≤ l / 2 + 2 := hx
      have hy' : ¬ siteDist ν a y ≤ l := hy
      have := siteDist_triangle ν a y x
      have h2 := siteDist_comm ν x y
      simp only [Nat.add_sub_cancel] at hs
      linarith only [hx', this, hs, not_le.1 hy']
  rw [hA]
  have ha : a ∈ obstacleFill K₀ G n D₁ := hsub1 (mem_ball_self a (by linarith only [hl]))
  refine ⟨hF, ha, ?_, ?_, hsub2, hadm⟩
  · have key : ∀ x ∈ obstacleFill K₀ G n D₁,
        x ∈ nnComponent (obstacleFill K₀ G n D₁) a := by
      intro x hx
      rcases hx with hx | hx
      · exact chainCluster_mono hsub1 (ball_nnConnected a _ _ x le_rfl hx)
      · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 hx
        have hpD : p ∈ D₁ := hp.1.1
        have hpa : p ∈ nnComponent (obstacleFill K₀ G n D₁) a :=
          chainCluster_mono hsub1 (ball_nnConnected a _ _ p le_rfl hpD)
        have hxA : x ∈ nnComponent (obstacleFill K₀ G n D₁) p := by
          have hzA : ∀ z ∈ nnComponent (obstacleUnion K₀ G n) p, z ∈ obstacleFill K₀ G n D₁ :=
            fun z hz => Or.inr (Set.mem_iUnion₂.2 ⟨p, hp, hz⟩)
          obtain ⟨hpU, hr⟩ := hxp
          have : ∀ z, Relation.ReflTransGen
              (chainStep (siteDist ν) (obstacleUnion K₀ G n) (5 / 4) ) p z →
              z ∈ nnComponent (obstacleFill K₀ G n D₁) p := by
            intro z hz
            induction hz with
            | refl => exact mem_chainCluster_self (hsub1 hpD)
            | tail hab hbc ih =>
              exact mem_chainCluster_of_lt ih (hzA _ ⟨hpU, hab.tail hbc⟩) hbc.2.2
          exact this x hr
        have := chainCluster_eq_of_mem (siteDist_comm ν) hpa
        simp only [nnComponent] at hxA ⊢
        rw [this] at hxA
        exact hxA
    intro x hx y hy
    have hxa := key x hx
    have hya := key y hy
    have := chainCluster_eq_of_mem (siteDist_comm ν) hxa
    simp only [nnComponent] at hya ⊢
    rw [this]
    exact hya
  · intro b hb
    obtain ⟨hbA, c, hbc, hcA⟩ := hb
    have hb2 : siteDist ν a b ≤ l := hsub2 hbA
    refine ⟨?_, hb2⟩
    have hc : ¬ siteDist ν a c ≤ l / 2 + 2 := fun h => hcA (hsub1 h)
    have := siteDist_triangle ν a c b
    have h2 := siteDist_comm ν b c
    linarith only [hbc, this, not_le.1 hc]


theorem annulusRegion_subset {ν : ℕ} {K₀ : ℝ} (hK : ScaleConditions K₀)
    {G : ℕ → Set (Set (Site ν))} (hG : ObstacleFamily K₀ G) {n n' : ℕ} (a : Site ν) {l : ℝ}
    (hl : 4 ≤ l) (hsep : n = 0 ∨ 10 * scaleD K₀ (n - 1) ≤ l / 2 - 2) :
    annulusRegion K₀ G n a l ⊆ annulusRegion K₀ G n' a (4 * l) := by
  intro x hx
  have h := (annulusRegion_spec hK hG a hl hsep).2.2.2.2.1 hx
  have h' : siteDist ν a x ≤ l := h
  exact Or.inl (show siteDist ν a x ≤ 4 * l / 2 + 2 by linarith only [hl, h'])


theorem annulusRegion_disjoint_singularSetsIn {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) {n : ℕ} (a : Site ν) {l : ℝ} (hl : 2 ≤ l)
    (hball : ∀ x, siteDist ν a x ≤ l + 1 → x ∉ singularSetsIn P Λ v n) :
    ∀ x ∈ annulusRegion P.K₀ (gentleClasses P (fun B => B ∩ Λ) (singular0 P v ∩ Λ) v) n a l,
      x ∉ singularSetsIn P Λ v n := by
  intro x hx
  rcases hx with hx | hx
  · exact hball x (by have : siteDist ν a x ≤ l / 2 + 2 := hx; linarith only [hl, this])
  · obtain ⟨p, -, hxp⟩ := Set.mem_iUnion₂.1 hx
    have hxU := chainCluster_subset p hxp
    simp only [obstacleUnion, Set.mem_iUnion, Finset.mem_range, exists_prop] at hxU
    obtain ⟨i, hi, C, ⟨hC, hg⟩, c, hc, hxc⟩ := hxU
    intro hxS
    have hxi1 : x ∈ singularSetsIn P Λ v (i + 1) :=
      singularSetsGen_antitone P _ _ v (Nat.succ_le_of_lt hi) hxS
    have hxi1' := hxi1
    rw [singularSetsIn, singularSetsGen_succ] at hxi1'
    have hxC : x ∉ C := fun h => hxi1'.2 ⟨C, ⟨hC, hg⟩, h⟩
    have h1 := two_mul_scaleR_le_siteDist P hC hc hxi1'.1 hxC
    rw [scaleR_eq_scaleD_succ] at h1
    have h2 := siteDist_comm ν c x
    have := hK.2.2.2.2.2.2.2.2 i
    linarith only [hxc, h1, h2, this]

end FroehlichSpencer.T12

end
