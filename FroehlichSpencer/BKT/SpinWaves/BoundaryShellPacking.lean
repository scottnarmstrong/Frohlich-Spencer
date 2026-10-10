/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Lemma46Induction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# The boundary-shell packing step

The external boundary of a new component meeting `D⁺(ρ)` lies in the shell
`B = ∂ext D⁺(ρ)` (the graph sphere of radius `r = 2m+1` about the center of `ρ`) together with
the external boundaries of the old components that meet `B`.

The old components are grouped by
the dyadic class `k = ⌊log₄ d(ϱ_{E'})⌋` of their maximal densities.

By T2.2(b), the chosen shell
points of one class are pairwise at distance at least `2^15 8^k`.

The packing on the sphere uses integer offsets `δ = (δ₁, δ₂)` with `|δ₁| + |δ₂| = r`.

On each half
`δ₂ ≥ 0` or `δ₂ < 0` of the sphere, graph distance is at most twice the difference of `δ₁`.

A
one-dimensional interval count then bounds the class by `4r / 2^14 8^k + 2`.

This replaces the
four-path cover of  and needs no room hypothesis on `L`.

The coarser base `4` makes the class
scales natural numbers, since `(4^k)^{7/4} ≥ 8^k`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SpinWaves

namespace BoundaryShellPacking

universe u v

/-- One-dimensional packing: points with integer labels in a window of `n + 1` consecutive values,
pairwise at least `t` apart, number at most `(n + t) / t`. The half-open intervals
`[f p, f p + t)` are disjoint and lie in `[a, a + n + t)`. -/
theorem card_mul_le_of_intSeparated {α : Type*} (H : Finset α) (f : α → ℤ) (a : ℤ)
    (n t : ℕ) (hrange : ∀ p ∈ H, a ≤ f p ∧ f p ≤ a + n)
    (hsep : ∀ p ∈ H, ∀ q ∈ H, p ≠ q → (t : ℤ) ≤ |f p - f q|) :
    H.card * t ≤ n + t := by
  classical
  let J : α → Finset ℤ := fun p => Finset.Ico (f p) (f p + t)
  have hdisj : (H : Set α).PairwiseDisjoint J := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro z hzp hzq
    simp only [J, Finset.mem_Ico] at hzp hzq
    have hlt : |f p - f q| < t := abs_sub_lt_iff.mpr ⟨by omega, by omega⟩
    have := hsep p hp q hq hpq
    omega
  have hsub : H.biUnion J ⊆ Finset.Ico a (a + n + t) := by
    intro z hz
    simp only [Finset.mem_biUnion, J, Finset.mem_Ico] at hz
    obtain ⟨p, hp, h1, h2⟩ := hz
    have := hrange p hp
    simp only [Finset.mem_Ico]
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  simp only [J, Int.card_Ico] at hcard
  have h1 : ∀ p, (f p + (t : ℤ) - f p).toNat = t := fun p => by omega
  have h2 : (a + (n : ℤ) + t - a).toNat = n + t := by omega
  simp only [h1, h2] at hcard
  rwa [Finset.sum_const, smul_eq_mul] at hcard

/-- Packing on an offset sphere `|δ₁| + |δ₂| = r`. On each half `δ₂ ≥ 0` or `δ₂ < 0` the
second offset is determined by the first, so the offset `ℓ¹` distance is at most twice the
difference of first offsets; each half is then a one-dimensional packing in `[-r, r]`. -/
theorem card_mul_le_of_sphereSeparated {α : Type*} (P : Finset α) (δ : α → ℤ × ℤ)
    (r t : ℕ) (hsphere : ∀ p ∈ P, |(δ p).1| + |(δ p).2| = r)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      2 * (t : ℤ) - 1 ≤ |(δ p).1 - (δ q).1| + |(δ p).2 - (δ q).2|) :
    P.card * t ≤ 4 * r + 2 * t := by
  classical
  have hhalf : ∀ H ⊆ P, (∀ p ∈ H, ∀ q ∈ H,
      |(δ p).2 - (δ q).2| ≤ |(δ p).1 - (δ q).1|) → H.card * t ≤ 2 * r + t := by
    intro H hHP hH
    have := card_mul_le_of_intSeparated H (fun p => (δ p).1) (-(r : ℤ)) (2 * r) t
      (fun p hp => by
        have h := hsphere p (hHP hp)
        have h0 := abs_nonneg (δ p).2
        have h1 := abs_le.mp (show |(δ p).1| ≤ r by linarith)
        constructor <;> push_cast <;> linarith [h1.1, h1.2])
      (fun p hp q hq hpq => by
        have h := hsep p (hHP hp) q (hHP hq) hpq
        have h' := hH p hp q hq
        show (t : ℤ) ≤ |(δ p).1 - (δ q).1|
        omega)
    exact this
  let H₁ := P.filter fun p => 0 ≤ (δ p).2
  let H₂ := P.filter fun p => ¬ 0 ≤ (δ p).2
  have hP : H₁.card + H₂.card = P.card := Finset.card_filter_add_card_filter_not _
  have hc₁ : H₁.card * t ≤ 2 * r + t := by
    apply hhalf H₁ (Finset.filter_subset _ _)
    intro p hp q hq
    simp only [H₁, Finset.mem_filter] at hp hq
    have hp2 : (δ p).2 = r - |(δ p).1| := by
      have := hsphere p hp.1; rw [abs_of_nonneg hp.2] at this; linarith
    have hq2 : (δ q).2 = r - |(δ q).1| := by
      have := hsphere q hq.1; rw [abs_of_nonneg hq.2] at this; linarith
    rw [hp2, hq2, show (r : ℤ) - |(δ p).1| - (r - |(δ q).1|) = |(δ q).1| - |(δ p).1| by ring,
      abs_sub_comm (δ p).1]
    exact abs_abs_sub_abs_le_abs_sub _ _
  have hc₂ : H₂.card * t ≤ 2 * r + t := by
    apply hhalf H₂ (Finset.filter_subset _ _)
    intro p hp q hq
    simp only [H₂, Finset.mem_filter, not_le] at hp hq
    have hp2 : (δ p).2 = -(r - |(δ p).1|) := by
      have := hsphere p hp.1; rw [abs_of_neg hp.2] at this; linarith
    have hq2 : (δ q).2 = -(r - |(δ q).1|) := by
      have := hsphere q hq.1; rw [abs_of_neg hq.2] at this; linarith
    rw [hp2, hq2, show -((r : ℤ) - |(δ p).1|) - -(r - |(δ q).1|) = |(δ p).1| - |(δ q).1| by
      ring]
    exact abs_abs_sub_abs_le_abs_sub _ _
  rw [← hP, Nat.add_mul]
  omega

/-- The dyadic-class scale bound `(4^k)^{7/4} ≥ 8^k`, used for the T2.2(b) exponent. -/
theorem eight_pow_le_rpow {d k : ℕ} (h : 4 ^ k ≤ d) :
    (8 : ℝ) ^ k ≤ (d : ℝ) ^ (7 / 4 : ℝ) := by
  have h4 : (8 : ℝ) ^ k = ((4 : ℝ) ^ k) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      mul_comm, Real.rpow_mul (by norm_num)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hone : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hd : ((4 : ℝ) ^ k) ≤ (d : ℝ) := by exact_mod_cast h
  rw [h4]
  calc ((4 : ℝ) ^ k) ^ (3 / 2 : ℝ) ≤ ((4 : ℝ) ^ k) ^ (7 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
    _ ≤ (d : ℝ) ^ (7 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hd (by norm_num)

/-- A natural number at least one is at most its `7/4` power. -/
theorem le_rpow_seven_fourths {d : ℕ} (h : 1 ≤ d) : (d : ℝ) ≤ (d : ℝ) ^ (7 / 4 : ℝ) := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast h
  calc (d : ℝ) = (d : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (d : ℝ) ^ (7 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hd (by norm_num)

/-- Geometric summation over dyadic classes: if `2^k X_k ≤ C` for `k < K`, then
`∑_{k<K} X_k ≤ 2C`. -/
theorem sum_le_of_dyadic {K C : ℕ} (X : ℕ → ℕ) (hX : ∀ k < K, 2 ^ k * X k ≤ C) :
    ∑ k ∈ Finset.range K, X k ≤ 2 * C := by
  have hreal : (∑ k ∈ Finset.range K, (X k : ℝ)) ≤ 2 * C := by
    calc (∑ k ∈ Finset.range K, (X k : ℝ))
        ≤ ∑ k ∈ Finset.range K, (C : ℝ) * (1 / 2 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro k hk
          have h := hX k (Finset.mem_range.mp hk)
          have h' : (2 : ℝ) ^ k * X k ≤ C := by exact_mod_cast h
          have hpos : (0 : ℝ) < 2 ^ k := by positivity
          rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
          linarith
      _ = (C : ℝ) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
      _ ≤ (C : ℝ) * 2 := by
          apply mul_le_mul_of_nonneg_left (sum_geometric_two_le K) (by positivity)
      _ = 2 * C := by ring
  exact_mod_cast hreal


/-- Along a walk from a vertex satisfying `P` to one that does not, some edge leaves `P`; its
outer endpoint is reachable from the start. -/
theorem exists_adj_exit_of_walk {W : Type*} {H : SimpleGraph W} (P : W → Prop) {u v : W}
    (w : H.Walk u v) (hu : P u) (hv : ¬ P v) :
    ∃ p q, H.Adj p q ∧ P p ∧ ¬ P q ∧ H.Reachable u q := by
  induction w with
  | nil => exact (hv hu).elim
  | @cons a b c hab tail ih =>
    by_cases hb : P b
    · obtain ⟨p, q, hpq, hp, hq, hreach⟩ := ih hb hv
      exact ⟨p, q, hpq, hp, hq, hab.reachable.trans hreach⟩
    · exact ⟨a, b, hab, hu, hb, hab.reachable⟩

/-- Membership in the external boundary of a `D⁺` component. -/
theorem mem_externalBoundary {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (G : Multigraph V E) (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (c : DensityPlusComponent G N₀ centerOf) (x : V) :
    x ∈ densityPlusExternalBoundary G N₀ centerOf c ↔
      x ∉ densityPlusComponentVertices G N₀ centerOf c ∧
        ∃ y ∈ densityPlusComponentVertices G N₀ centerOf c, G.Adj x y := by
  simp [densityPlusExternalBoundary]

/-- Distinct components of the induced union have disjoint vertex sets. -/
theorem component_eq_of_mem_vertices {V : Type u} {E : Type v} [Fintype V]
    {G : Multigraph V E} {N₀ : Finset (V → ℤ)} {centerOf : (V → ℤ) → V}
    {c₁ c₂ : DensityPlusComponent G N₀ centerOf} {x : V}
    (h₁ : x ∈ densityPlusComponentVertices G N₀ centerOf c₁)
    (h₂ : x ∈ densityPlusComponentVertices G N₀ centerOf c₂) : c₁ = c₂ := by
  obtain ⟨_, e₁⟩ := (mem_densityPlusComponentVertices G N₀ centerOf c₁ x).1 h₁
  obtain ⟨_, e₂⟩ := (mem_densityPlusComponentVertices G N₀ centerOf c₂ x).1 h₂
  exact e₁.symm.trans e₂

/-- An old component that touches `D⁺(ρ)` and has a vertex outside it meets the shell
`∂ext D⁺(ρ)`. -/
theorem oldComponent_meets_shell {V : Type u} {E : Type v} [Fintype V] [DecidableEq V]
    {G : Multigraph V E} {I : Finset (V → ℤ)} {centerOf : (V → ℤ) → V} {ρ : V → ℤ}
    (c' : DensityPlusComponent G I centerOf) {a b y : V}
    (ha : a ∈ G.densityDomainPlus ρ (centerOf ρ))
    (hb : b ∈ densityPlusComponentVertices G I centerOf c')
    (hab : a = b ∨ G.toSimpleGraph.Adj a b)
    (hy : y ∈ densityPlusComponentVertices G I centerOf c')
    (hyA : y ∉ G.densityDomainPlus ρ (centerOf ρ)) :
    ∃ p ∈ densityDomainPlusExternalBoundary G ρ (centerOf ρ),
      p ∈ densityPlusComponentVertices G I centerOf c' := by
  by_cases hbA : b ∈ G.densityDomainPlus ρ (centerOf ρ)
  · obtain ⟨hbU, hbcls⟩ := (mem_densityPlusComponentVertices G I centerOf c' b).1 hb
    obtain ⟨hyU, hycls⟩ := (mem_densityPlusComponentVertices G I centerOf c' y).1 hy
    have hreach : (densityPlusInducedGraph G I centerOf).Reachable ⟨b, hbU⟩ ⟨y, hyU⟩ :=
      SimpleGraph.ConnectedComponent.exact (hbcls.trans hycls.symm)
    obtain ⟨w⟩ := hreach
    obtain ⟨p, q, hpq, hp, hq, hreach'⟩ := exists_adj_exit_of_walk
      (fun z : densityPlusUnion G I centerOf => z.1 ∈ G.densityDomainPlus ρ (centerOf ρ))
      w hbA hyA
    have hpqG : G.toSimpleGraph.Adj p.1 q.1 := SimpleGraph.induce_adj.mp hpq
    refine ⟨q.1, ?_, ?_⟩
    · exact (mem_densityDomainPlusExternalBoundary G ρ (centerOf ρ) q.1).2
        ⟨hq, p.1, hp, hpqG.symm⟩
    · exact (mem_densityPlusComponentVertices G I centerOf c' q.1).2
        ⟨q.2, (SimpleGraph.ConnectedComponent.sound hreach').symm.trans hbcls⟩
  · rcases hab with rfl | hadj
    · exact (hbA ha).elim
    · exact ⟨b, (mem_densityDomainPlusExternalBoundary G ρ (centerOf ρ) b).2
        ⟨hbA, a, ha, hadj.symm⟩, hb⟩

/-- The merge step on any connected carrier that admits integer offsets `δ` about every
center, with graph distance at most the offset `ℓ¹` distance and equal to it from the center. -/
theorem boundaryPackingStep_of_offsets {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq (V → ℤ)] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected)
    (hoff : ∀ j : V, ∃ δ : V → ℤ × ℤ,
      (∀ x y, (G.toSimpleGraph.dist x y : ℤ) ≤ |(δ x).1 - (δ y).1| + |(δ x).2 - (δ y).2|) ∧
        ∀ x, (G.toSimpleGraph.dist j x : ℤ) = |(δ x).1| + |(δ x).2|)
    (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V) :
    lemma46BoundaryPackingStep G N₀ centerOf := by
  classical
  intro I ρ m hI hρ hρnotI hρneutral hρcenter hneutral hcenter hsep hm hρdiam hρmax hOld c
    hmeet _hdiam
  obtain ⟨x₀, hx₀A, hx₀c⟩ := hmeet
  obtain ⟨δ, hδdist, hδsphere⟩ := hoff (centerOf ρ)
  have hdiamρ : 1 ≤ G.densityDiameter ρ := hρdiam ▸ hm
  have hBsphere : ∀ x ∈ densityDomainPlusExternalBoundary G ρ (centerOf ρ),
      G.toSimpleGraph.dist (centerOf ρ) x = 2 * m + 1 := by
    intro x hx
    have h := (mem_densityDomainPlusExternalBoundary_iff_dist_eq G hG ρ (centerOf ρ) x
      hdiamρ).1 hx
    rw [G.toSimpleGraph.dist_comm, h, hρdiam]
  have hAc : ∀ x ∈ G.densityDomainPlus ρ (centerOf ρ),
      x ∈ densityPlusComponentVertices G (insert ρ I) centerOf c :=
    densityDomainPlus_subset_componentVertices_of_mem G hG (insert ρ I) centerOf c
      (Finset.mem_insert_self ρ I) hρneutral hρcenter hx₀A hx₀c
  obtain ⟨S, hS⟩ : ∃ S : Finset (DensityPlusComponent G I centerOf),
      S = Finset.univ.filter fun c' => ∃ p ∈ densityDomainPlusExternalBoundary G ρ (centerOf ρ),
        p ∈ densityPlusComponentVertices G I centerOf c' := ⟨_, rfl⟩
  have hmemS : ∀ c', c' ∈ S ↔ ∃ p ∈ densityDomainPlusExternalBoundary G ρ (centerOf ρ),
      p ∈ densityPlusComponentVertices G I centerOf c' := by
    intro c'
    simp [hS]
  -- Decomposition of the new external boundary.
  have hdecomp : densityPlusExternalBoundary G (insert ρ I) centerOf c ⊆
      densityDomainPlusExternalBoundary G ρ (centerOf ρ) ∪
        S.biUnion fun c' => densityPlusExternalBoundary G I centerOf c' := by
    intro x hx
    obtain ⟨hxc, y, hyc, hxy⟩ := (mem_externalBoundary G (insert ρ I) centerOf c x).1 hx
    have hne : x ≠ y := fun h => hxc (h ▸ hyc)
    have hxyS : G.toSimpleGraph.Adj x y := by
      rw [Multigraph.toSimpleGraph_eq_fromRel_adj]
      exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl hxy⟩
    by_cases hyA : y ∈ G.densityDomainPlus ρ (centerOf ρ)
    · apply Finset.mem_union_left
      exact (mem_densityDomainPlusExternalBoundary G ρ (centerOf ρ) x).2
        ⟨fun hxA => hxc (hAc x hxA), y, hyA, hxyS⟩
    · obtain ⟨c', hyc', a, ha, b, hb, hab⟩ :=
        exists_adjacent_oldComponent_of_newComponent I centerOf ρ c hx₀A hx₀c hyc hyA
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨c', (hmemS c').2 (oldComponent_meets_shell c' ha hb hab hyc' hyA), ?_⟩
      have hsub := oldComponent_subset_newComponent_of_mem I centerOf ρ c' c hyc' hyc
      exact (mem_externalBoundary G I centerOf c' x).2 ⟨fun hxc' => hxc (hsub hxc'), y, hyc', hxy⟩
  have hcard₁ : (densityPlusExternalBoundary G (insert ρ I) centerOf c).card ≤
      (densityDomainPlusExternalBoundary G ρ (centerOf ρ)).card +
        ∑ c' ∈ S, (densityPlusExternalBoundary G I centerOf c').card :=
    (Finset.card_le_card hdecomp).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  -- The inductive maximal density of every old component.
  have hneutralI : ∀ σ ∈ I, ∑ x, σ x = 0 := fun σ hσ => hneutral σ (hI hσ)
  have hcenterI : ∀ σ ∈ I, G.IsDensityCenter σ (centerOf σ) := fun σ hσ => hcenter σ (hI hσ)
  have hτex : ∀ c' : DensityPlusComponent G I centerOf, ∃ τ : V → ℤ,
      τ ∈ densitiesContainedInComponent G I centerOf c' ∧
        densityPlusComponentDiameter G I centerOf c' ≤ 5 * G.densityDiameter τ ∧
        (densityPlusExternalBoundary G I centerOf c').card ≤ 16 * G.densityDiameter τ := by
    intro c'
    obtain ⟨τ, hτ, -, h₁, h₂⟩ :=
      hOld c' (densitiesContainedInComponent_nonempty hG I centerOf hneutralI hcenterI c')
    exact ⟨τ, hτ, h₁, h₂⟩
  choose τ hτmem hτdiam hτbd using hτex
  have hpex : ∀ c' : DensityPlusComponent G I centerOf, ∃ p : V, c' ∈ S →
      p ∈ densityDomainPlusExternalBoundary G ρ (centerOf ρ) ∧
        p ∈ densityPlusComponentVertices G I centerOf c' := by
    intro c'
    by_cases hc' : c' ∈ S
    · obtain ⟨p, hpB, hpc⟩ := (hmemS c').1 hc'
      exact ⟨p, fun _ => ⟨hpB, hpc⟩⟩
    · exact ⟨centerOf ρ, fun h => (hc' h).elim⟩
  choose p hp using hpex
  have hτI : ∀ c', τ c' ∈ I := fun c' =>
    ((mem_densitiesContainedInComponent G I centerOf c' (τ c')).1 (hτmem c')).1
  have hτcenter : ∀ c', centerOf (τ c') ∈ densityPlusComponentVertices G I centerOf c' :=
    fun c' => densitySupport_subset_componentVertices G hG I centerOf c' (hτmem c')
      (hneutralI _ (hτI c')) (hcenterI _ (hτI c')) (hcenterI _ (hτI c')).1
  have hDpos : ∀ c', 1 ≤ G.densityDiameter (τ c') := fun c' =>
    G.one_le_densityDiameter_of_neutral hG (τ c')
      (fun h => (hcenterI _ (hτI c')).1 (by simp [h])) (hneutralI _ (hτI c'))
  have hDle : ∀ c', G.densityDiameter (τ c') ≤ m := fun c' => hρmax _ (hτI c')
  have hM : (2 : ℝ) ^ 16 = 65536 := by norm_num
  -- T2.2(b) against `ρ`: the scale of a shell-meeting old component is tiny.
  have hS₁ : ∀ c' ∈ S, 65531 * 8 ^ Nat.log 4 (G.densityDiameter (τ c')) ≤ 2 * m + 1 := by
    intro c' hc'
    obtain ⟨hpB, hpc⟩ := hp c' hc'
    have hτne : ρ ≠ τ c' := fun h => hρnotI (h ▸ hτI c')
    have hpoint := hsep.neutral_support_distance hρ (hI (hτI c')) hτne hρcenter.1
      (hcenterI _ (hτI c')).1
    have hmin : min (G.densityDiameter ρ) (G.densityDiameter (τ c')) =
        G.densityDiameter (τ c') := by
      rw [hρdiam]
      exact min_eq_right (hDle c')
    rw [hmin, hM] at hpoint
    have hdist : G.toSimpleGraph.dist (centerOf ρ) (centerOf (τ c')) ≤
        2 * m + 1 + 5 * G.densityDiameter (τ c') := by
      have h₁ := hBsphere _ hpB
      have h₂ := dist_le_densityPlusComponentDiameter G I centerOf c' hpc (hτcenter c')
      have h₃ := hτdiam c'
      have htri := hG.dist_triangle (u := centerOf ρ) (v := p c') (w := centerOf (τ c'))
      omega
    have hdistR : ((G.toSimpleGraph.dist (centerOf ρ) (centerOf (τ c')) : ℕ) : ℝ) ≤
        ((2 * m + 1 : ℕ) : ℝ) + 5 * (G.densityDiameter (τ c') : ℝ) := by exact_mod_cast hdist
    have hlin := le_rpow_seven_fourths (hDpos c')
    have h8 := eight_pow_le_rpow (Nat.pow_log_le_self 4 (Nat.one_le_iff_ne_zero.mp (hDpos c')))
    have hreal : (65531 : ℝ) * 8 ^ Nat.log 4 (G.densityDiameter (τ c')) ≤
        ((2 * m + 1 : ℕ) : ℝ) := by linarith
    exact_mod_cast hreal
  -- T2.2(b) between two old components of one class: their shell points are far apart.
  have hS₂ : ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ →
      Nat.log 4 (G.densityDiameter (τ c₁)) = Nat.log 4 (G.densityDiameter (τ c₂)) →
      2 * (16384 * 8 ^ Nat.log 4 (G.densityDiameter (τ c₁))) ≤
        G.toSimpleGraph.dist (p c₁) (p c₂) := by
    intro c₁ hc₁ c₂ hc₂ hne hk
    obtain ⟨_, hp₁⟩ := hp c₁ hc₁
    obtain ⟨_, hp₂⟩ := hp c₂ hc₂
    have hτne : τ c₁ ≠ τ c₂ := by
      intro h
      have h₂ := hτcenter c₂
      rw [← h] at h₂
      exact hne (component_eq_of_mem_vertices (hτcenter c₁) h₂)
    have hpoint := hsep.neutral_support_distance (hI (hτI c₁)) (hI (hτI c₂)) hτne
      (hcenterI _ (hτI c₁)).1 (hcenterI _ (hτI c₂)).1
    rw [hM] at hpoint
    set k := Nat.log 4 (G.densityDiameter (τ c₁)) with hkdef
    have hlow₁ : 4 ^ k ≤ G.densityDiameter (τ c₁) :=
      Nat.pow_log_le_self 4 (Nat.one_le_iff_ne_zero.mp (hDpos c₁))
    have hlow₂ : 4 ^ k ≤ G.densityDiameter (τ c₂) := by
      rw [hk]
      exact Nat.pow_log_le_self 4 (Nat.one_le_iff_ne_zero.mp (hDpos c₂))
    have hup₁ : G.densityDiameter (τ c₁) < 4 * 4 ^ k := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) (G.densityDiameter (τ c₁))
      rw [← hkdef, pow_succ] at this
      omega
    have hup₂ : G.densityDiameter (τ c₂) < 4 * 4 ^ k := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) (G.densityDiameter (τ c₂))
      rw [← hk, pow_succ] at this
      omega
    have h8 := eight_pow_le_rpow (le_min hlow₁ hlow₂)
    have hreal : (65536 : ℝ) * 8 ^ k ≤
        ((G.toSimpleGraph.dist (centerOf (τ c₁)) (centerOf (τ c₂)) : ℕ) : ℝ) := by
      linarith
    have hnat : 65536 * 8 ^ k ≤ G.toSimpleGraph.dist (centerOf (τ c₁)) (centerOf (τ c₂)) := by
      exact_mod_cast hreal
    have hd₁ := dist_le_densityPlusComponentDiameter G I centerOf c₁ (hτcenter c₁) hp₁
    have hd₂ := dist_le_densityPlusComponentDiameter G I centerOf c₂ hp₂ (hτcenter c₂)
    have hdiam₁ := hτdiam c₁
    have hdiam₂ := hτdiam c₂
    have htri₁ := hG.dist_triangle (u := centerOf (τ c₁)) (v := p c₁) (w := centerOf (τ c₂))
    have htri₂ := hG.dist_triangle (u := p c₁) (v := p c₂) (w := centerOf (τ c₂))
    have h48 : 4 ^ k ≤ 8 ^ k := Nat.pow_le_pow_left (by norm_num) k
    omega
  -- The whole shell.
  have hBcard : (densityDomainPlusExternalBoundary G ρ (centerOf ρ)).card ≤
      4 * (2 * m + 1) + 2 := by
    have h := card_mul_le_of_sphereSeparated
      (densityDomainPlusExternalBoundary G ρ (centerOf ρ)) δ (2 * m + 1) 1
      (fun x hx => by
        have h₁ := hδsphere x
        rw [hBsphere x hx] at h₁
        exact h₁.symm)
      (fun x _ y _ hxy => by
        have h₁ := hδdist x y
        have h₂ := hG.pos_dist_of_ne hxy
        omega)
    simpa using h
  -- One dyadic class.
  have hclass : ∀ k, 2 ^ k * (16384 * ∑ c' ∈ S.filter
      (fun c' => Nat.log 4 (G.densityDiameter (τ c')) = k), G.densityDiameter (τ c')) ≤
        20 * (2 * m + 1) := by
    intro k
    by_cases hne : (S.filter fun c' => Nat.log 4 (G.densityDiameter (τ c')) = k).Nonempty
    · obtain ⟨c₀, hc₀⟩ := hne
      rw [Finset.mem_filter] at hc₀
      have hsk := hS₁ c₀ hc₀.1
      rw [hc₀.2] at hsk
      set Sk := S.filter fun c' => Nat.log 4 (G.densityDiameter (τ c')) = k with hSk
      have hSkS : ∀ c' ∈ Sk, c' ∈ S := fun c' hc' => (Finset.mem_filter.mp hc').1
      have hSkk : ∀ c' ∈ Sk, Nat.log 4 (G.densityDiameter (τ c')) = k :=
        fun c' hc' => (Finset.mem_filter.mp hc').2
      have hinj : Set.InjOn p Sk := by
        intro c₁ h₁ c₂ h₂ heq
        have hp₁ := (hp c₁ (hSkS c₁ h₁)).2
        have hp₂ := (hp c₂ (hSkS c₂ h₂)).2
        rw [heq] at hp₁
        exact component_eq_of_mem_vertices hp₁ hp₂
      have hcardImg : (Sk.image p).card = Sk.card := Finset.card_image_of_injOn hinj
      have hpack := card_mul_le_of_sphereSeparated (Sk.image p) δ (2 * m + 1)
        (16384 * 8 ^ k)
        (fun x hx => by
          obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hx
          have h₁ := hδsphere (p c')
          rw [hBsphere _ (hp c' (hSkS c' hc')).1] at h₁
          exact h₁.symm)
        (fun x hx y hy hxy => by
          obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_image.mp hy
          have hc : c₁ ≠ c₂ := fun h => hxy (h ▸ rfl)
          have h₁ := hS₂ c₁ (hSkS c₁ hc₁) c₂ (hSkS c₂ hc₂) hc
            ((hSkk c₁ hc₁).trans (hSkk c₂ hc₂).symm)
          rw [hSkk c₁ hc₁] at h₁
          have h₂ := hδdist (p c₁) (p c₂)
          generalize (8 : ℕ) ^ k = e at h₁ ⊢
          omega)
      rw [hcardImg] at hpack
      have hsum : ∑ c' ∈ Sk, G.densityDiameter (τ c') ≤ Sk.card * (4 * 4 ^ k) := by
        have h := Finset.sum_le_sum (s := Sk) (f := fun c' => G.densityDiameter (τ c'))
          (g := fun _ => 4 * 4 ^ k) (fun c' hc' => by
            have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) (G.densityDiameter (τ c'))
            rw [hSkk c' hc', pow_succ] at this
            omega)
        simpa [Finset.sum_const] using h
      have h84 : (8 : ℕ) ^ k = 4 ^ k * 2 ^ k := by
        rw [← mul_pow]
        norm_num
      have hpack' : Sk.card * (16384 * 8 ^ k) ≤ 5 * (2 * m + 1) := by
        generalize 8 ^ k = e at *
        omega
      calc 2 ^ k * (16384 * ∑ c' ∈ Sk, G.densityDiameter (τ c'))
          ≤ 2 ^ k * (16384 * (Sk.card * (4 * 4 ^ k))) := by gcongr
        _ = 4 * (Sk.card * (16384 * 8 ^ k)) := by rw [h84]; ring
        _ ≤ 4 * (5 * (2 * m + 1)) := by gcongr
        _ = 20 * (2 * m + 1) := by ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  -- Summation over the dyadic classes.
  have hrange : ∀ c' ∈ S, Nat.log 4 (G.densityDiameter (τ c')) ∈ Finset.range (m + 1) := by
    intro c' _
    rw [Finset.mem_range]
    have h₁ : Nat.log 4 (G.densityDiameter (τ c')) <
        4 ^ Nat.log 4 (G.densityDiameter (τ c')) := Nat.lt_pow_self (by norm_num)
    have h₂ := Nat.pow_log_le_self 4 (Nat.one_le_iff_ne_zero.mp (hDpos c'))
    have h₃ := hDle c'
    omega
  have hfiber := Finset.sum_fiberwise_of_maps_to hrange (fun c' => G.densityDiameter (τ c'))
  have htotal : 16384 * ∑ c' ∈ S, G.densityDiameter (τ c') ≤ 2 * (20 * (2 * m + 1)) := by
    have h := sum_le_of_dyadic (K := m + 1) (C := 20 * (2 * m + 1))
      (fun k => 16384 * ∑ c' ∈ S.filter
        (fun c' => Nat.log 4 (G.densityDiameter (τ c')) = k), G.densityDiameter (τ c'))
      (fun k _ => hclass k)
    rw [← Finset.mul_sum, hfiber] at h
    exact h
  have hext : ∑ c' ∈ S, (densityPlusExternalBoundary G I centerOf c').card ≤
      16 * ∑ c' ∈ S, G.densityDiameter (τ c') := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c' _ => hτbd c'
  omega

/-- `|a - b|` as an integer is the natural distance. -/
theorem natDist_cast (a b : ℕ) : ((Nat.dist a b : ℕ) : ℤ) = |(a : ℤ) - b| := by
  rcases abs_cases ((a : ℤ) - b) with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> unfold Nat.dist <;>
    omega

/-- Coordinate offsets on the free square: graph distance is the Manhattan distance. -/
theorem squareFree_offsets (L : ℕ) (hL : 1 < L) (j : Fin L × Fin L) :
    ∃ δ : Fin L × Fin L → ℤ × ℤ,
      (∀ x y, ((squareFree L).toSimpleGraph.dist x y : ℤ) ≤
        |(δ x).1 - (δ y).1| + |(δ x).2 - (δ y).2|) ∧
      ∀ x, ((squareFree L).toSimpleGraph.dist j x : ℤ) = |(δ x).1| + |(δ x).2| := by
  refine ⟨fun x => ((x.1.val : ℤ) - j.1.val, (x.2.val : ℤ) - j.2.val), ?_, ?_⟩
  · intro x y
    rw [squareFree_dist_eq_freeRadius hL]
    simp only [Lattice2D.freeRadius, Nat.cast_add, natDist_cast]
    apply le_of_eq
    congr 2 <;> ring
  · intro x
    rw [squareFree_dist_eq_freeRadius hL]
    simp only [Lattice2D.freeRadius, Nat.cast_add, natDist_cast]
    rw [abs_sub_comm (j.1.val : ℤ), abs_sub_comm (j.2.val : ℤ)]

/-- Cyclic offsets on the periodic square: graph distance is at most the offset `ℓ¹` distance,
with equality from the base point. -/
theorem squarePeriodic_offsets (L : ℕ) (hL : 1 < L) (j : Fin L × Fin L) :
    ∃ δ : Fin L × Fin L → ℤ × ℤ,
      (∀ x y, ((squarePeriodic L).toSimpleGraph.dist x y : ℤ) ≤
        |(δ x).1 - (δ y).1| + |(δ x).2 - (δ y).2|) ∧
      ∀ x, ((squarePeriodic L).toSimpleGraph.dist j x : ℤ) = |(δ x).1| + |(δ x).2| := by
  have hL0 : 0 < L := by omega
  have h₁ : ∀ x : Fin L × Fin L, ∃ t : ℤ, t ≡ (x.1.val : ℤ) - j.1.val [ZMOD L] ∧
      |t| = cyclicDist L j.1 x.1 := fun x => exists_abs_eq_cyclicDist L hL0 j.1 x.1
  have h₂ : ∀ x : Fin L × Fin L, ∃ t : ℤ, t ≡ (x.2.val : ℤ) - j.2.val [ZMOD L] ∧
      |t| = cyclicDist L j.2 x.2 := fun x => exists_abs_eq_cyclicDist L hL0 j.2 x.2
  choose t₁ ht₁ ht₁' using h₁
  choose t₂ ht₂ ht₂' using h₂
  refine ⟨fun x => (t₁ x, t₂ x), ?_, ?_⟩
  · intro x y
    rw [squarePeriodic_dist_eq_cyclicDist]
    have e₁ : t₁ y - t₁ x ≡ (y.1.val : ℤ) - x.1.val [ZMOD L] := by
      have h := (ht₁ y).sub (ht₁ x)
      rwa [sub_sub_sub_cancel_right] at h
    have e₂ : t₂ y - t₂ x ≡ (y.2.val : ℤ) - x.2.val [ZMOD L] := by
      have h := (ht₂ y).sub (ht₂ x)
      rwa [sub_sub_sub_cancel_right] at h
    have c₁ := cyclicDist_le_abs L hL0 x.1 y.1 (t₁ y - t₁ x) e₁
    have c₂ := cyclicDist_le_abs L hL0 x.2 y.2 (t₂ y - t₂ x) e₂
    rw [abs_sub_comm] at c₁ c₂
    push_cast
    exact add_le_add c₁ c₂
  · intro x
    rw [squarePeriodic_dist_eq_cyclicDist]
    push_cast
    rw [ht₁' x, ht₂' x]

/-- The merge step on the free square. -/
theorem squareFree_boundaryPackingInput (L : ℕ) (hL : 1 < L) :
    l46BoundaryPackingInput (squareFree L) := by
  intro centerOf _ N _ _ _ _ _
  exact boundaryPackingStep_of_offsets (squareFree L) (squareFree_connected L hL)
    (squareFree_offsets L hL) (neutralPart N) centerOf

/-- The merge step on the periodic square (evenness is not needed). -/
theorem squarePeriodic_boundaryPackingInput (L : ℕ) (hL : 1 < L) :
    l46BoundaryPackingInput (squarePeriodic L) := by
  intro centerOf _ N _ _ _ _ _
  exact boundaryPackingStep_of_offsets (squarePeriodic L) (squarePeriodic_connected L hL)
    (squarePeriodic_offsets L hL) (neutralPart N) centerOf

/-- KP Lemma 4.6, the exact statement `l46Statement`. -/
theorem l46Statement_holds : l46Statement :=
  l46Statement_of_boundaryPacking (fun L hL => squareFree_boundaryPackingInput L hL)
    (fun L hL _ => squarePeriodic_boundaryPackingInput L hL)

end BoundaryShellPacking

end FroehlichSpencer.BKT.SpinWaves

end
