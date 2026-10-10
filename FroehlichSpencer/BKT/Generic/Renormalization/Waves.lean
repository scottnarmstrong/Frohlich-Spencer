/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.SpinWave.Base
public import FroehlichSpencer.BKT.Generic.SpinWave.GradientBounds
public import FroehlichSpencer.BKT.Reduction.P24Assembly
public import FroehlichSpencer.BKT.SpinWaves.Prop47
import FroehlichSpencer.BKT.SpinWaves.ComponentCubeSum
import FroehlichSpencer.BKT.SpinWaves.LatticePacking
import FroehlichSpencer.BKT.Charges.DensityBall

/-!
# The all-scales graded spin wave (generic core)

* **Base pieces** (KP Lemma 4.5, scale `0`): the site sign waves `signBaseWave ϱ m` on the charged
  sites `m` of one bipartition class.

`squareProfile_facts` repeats the geometry of `SpinWaves.P47.p47Step_of_l46Step` (Lemma 4.6)
for the profile itself, and adds the two estimates the cost envelope needs:

* the sup-gradient bound `|∇ψ̃| ≤ 28 · 2^{-(3/7) k}` (`SpinWave.squareWaveProfile_grad_le` with the
  L4.6(2) diameter power bound `d^{7/4} ≤ 3·2^k/512`, so `d ≤ 2^{4k/7}`, at most `8` component
  boundaries meeting an edge, and the ramp width `≥ 2^k / 4`);
* the edge count `|{e : ∇ψ̃(e) ≠ 0}| ≤ 100 · 4^k` (support near `s`, the lattice ball count and
  degree four).

`exists_fullGradedSpinWave` assembles the family.

Pairwise gradient disjointness is , as in
`Reduction.p24Step_of_p47Step`: base/base pieces lie in one bipartition class, base/square and
square/square pieces use `IsSquareWave.grad_disjoint_base`, `IsSquareWave.grad_disjoint_of_far` and
`cross_scale_endpoints_near`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open SpinWaves SpinWaves.P47 Reduction

/-! ## Elementary counts and estimates -/

section Counts

variable {V : Type} [Fintype V] [DecidableEq V] {E : Type} [Fintype E]

omit [Fintype V] in
/-- Edges with a nonzero gradient of `f` touch the support of `f`: at most four per support
vertex in a graph of endpoint degree four. -/
theorem card_grad_ne_zero_le (G : Multigraph V E)
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4)
    (f : V → ℝ) (A : Finset V) (hA : ∀ j, f j ≠ 0 → j ∈ A) :
    (Finset.univ.filter fun e => G.grad f e ≠ 0).card ≤ 4 * A.card := by
  classical
  have hsub : (Finset.univ.filter fun e => G.grad f e ≠ 0) ⊆
      A.biUnion (fun x => Finset.univ.filter fun e => G.src e = x) ∪
        A.biUnion (fun x => Finset.univ.filter fun e => G.tgt e = x) := by
    intro e he
    have hne : G.grad f e ≠ 0 := (Finset.mem_filter.mp he).2
    rcases ne_zero_of_grad_ne_zero G f e hne with h | h
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨_, hA _ h, by simp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, hA _ h, by simp⟩)
  calc (Finset.univ.filter fun e => G.grad f e ≠ 0).card
      ≤ (A.biUnion (fun x => Finset.univ.filter fun e => G.src e = x)).card +
          (A.biUnion (fun x => Finset.univ.filter fun e => G.tgt e = x)).card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    _ ≤ ∑ x ∈ A, (Finset.univ.filter fun e => G.src e = x).card +
          ∑ x ∈ A, (Finset.univ.filter fun e => G.tgt e = x).card :=
        Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ = ∑ x ∈ A, ((Finset.univ.filter fun e => G.src e = x).card +
          (Finset.univ.filter fun e => G.tgt e = x).card) := (Finset.sum_add_distrib).symm
    _ ≤ ∑ _x ∈ A, 4 := Finset.sum_le_sum fun x _ => hdeg x
    _ = 4 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- A vertex lies in the external boundary of at most four `D⁺` components: each such component
contains the far endpoint of a different edge at that vertex. -/
theorem card_components_externalBoundary_le (G : Multigraph V E)
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4)
    (N₁ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (R : Finset (DensityPlusComponent G N₁ centerOf)) (x : V) :
    (R.filter fun c => x ∈ densityPlusExternalBoundary G N₁ centerOf c).card ≤ 4 := by
  classical
  rcases isEmpty_or_nonempty E with hE | hE
  · have h0 : R.filter (fun c => x ∈ densityPlusExternalBoundary G N₁ centerOf c) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun c _ hx => ?_
      simp only [densityPlusExternalBoundary, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx
      obtain ⟨-, y, -, e, -⟩ := hx
      exact hE.elim e
    rw [h0, Finset.card_empty]
    exact Nat.zero_le 4
  have : Nonempty V := ⟨x⟩
  have hnb : ∀ c ∈ R.filter (fun c => x ∈ densityPlusExternalBoundary G N₁ centerOf c),
      ∃ e ∈ (Finset.univ.filter fun e => G.src e = x) ∪
          (Finset.univ.filter fun e => G.tgt e = x), ∃ y,
        y ∈ densityPlusComponentVertices G N₁ centerOf c ∧
          ((G.src e = x ∧ G.tgt e = y) ∨ (G.src e = y ∧ G.tgt e = x)) := by
    intro c hc
    have hx := (Finset.mem_filter.mp hc).2
    simp only [densityPlusExternalBoundary, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨-, y, hy, e, he⟩ := hx
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨e, Finset.mem_union_left _ (by simp [h1]), y, hy, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨e, Finset.mem_union_right _ (by simp [h2]), y, hy, Or.inr ⟨h1, h2⟩⟩
  choose! g hg yf hyf hor using hnb
  have hinj : Set.InjOn g
      (((R.filter fun c => x ∈ densityPlusExternalBoundary G N₁ centerOf c) :
        Finset (DensityPlusComponent G N₁ centerOf)) : Set (DensityPlusComponent G N₁ centerOf)) := by
    intro c hc c' hc' hcc'
    have hy : yf c = yf c' := by
      have h := hor c hc
      have h' := hor c' hc'
      rw [hcc'] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact h2.symm.trans h2'
      · exact absurd (h1.trans h2'.symm) (G.src_ne_tgt _)
      · exact absurd (h1'.trans h2.symm) (G.src_ne_tgt _)
      · exact h1.symm.trans h1'
    obtain ⟨hx1, hc1⟩ := (mem_densityPlusComponentVertices G N₁ centerOf c (yf c)).mp (hyf c hc)
    obtain ⟨hx2, hc2⟩ :=
      (mem_densityPlusComponentVertices G N₁ centerOf c' (yf c')).mp (hyf c' hc')
    rw [← hc1, ← hc2]
    congr 1
    exact Subtype.ext hy
  calc (R.filter fun c => x ∈ densityPlusExternalBoundary G N₁ centerOf c).card
      = ((R.filter fun c => x ∈ densityPlusExternalBoundary G N₁ centerOf c).image g).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((Finset.univ.filter fun e => G.src e = x) ∪
          (Finset.univ.filter fun e => G.tgt e = x)).card :=
        Finset.card_le_card (Finset.image_subset_iff.mpr hg)
    _ ≤ (Finset.univ.filter fun e => G.src e = x).card +
          (Finset.univ.filter fun e => G.tgt e = x).card := Finset.card_union_le _ _
    _ ≤ 4 := hdeg x

/-- The edge form: at most eight components have an endpoint of `e` in their external
boundary. -/
theorem card_components_externalBoundary_edge_le (G : Multigraph V E)
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4)
    (N₁ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (R : Finset (DensityPlusComponent G N₁ centerOf)) (e : E) :
    ((R.filter fun c => G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
        G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) ≤ 8 := by
  classical
  rw [Finset.filter_or]
  have h := (Finset.card_union_le _ _).trans (Nat.add_le_add
    (card_components_externalBoundary_le G hdeg N₁ centerOf R (G.src e))
    (card_components_externalBoundary_le G hdeg N₁ centerOf R (G.tgt e)))
  exact_mod_cast h

end Counts

/-- The algebra of the gradient estimate: with `y ≥ 1`, `y^7 ≤ 4δ` and `A ≤ 36 y^8`,
`√(A/δ²) ≤ 28 / y³`. -/
theorem sqrt_div_sq_le_of_pow {y δ A : ℝ} (hy : 1 ≤ y) (hδ : y ^ 7 ≤ 4 * δ)
    (hA : A ≤ 36 * y ^ 8) : Real.sqrt (A / δ ^ 2) ≤ 28 * (y ^ 3)⁻¹ := by
  have hy0 : 0 < y := by linarith
  have hy7 : 0 < y ^ 7 := pow_pos hy0 7
  have hδ0 : 0 < δ := by linarith
  have hsq : (y ^ 7) ^ 2 ≤ (4 * δ) ^ 2 := pow_le_pow_left₀ hy7.le hδ 2
  rw [Real.sqrt_le_left (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  have hy6 : 0 < y ^ 6 := pow_pos hy0 6
  have key : (28 * (y ^ 3)⁻¹) ^ 2 * δ ^ 2 = 784 * δ ^ 2 / y ^ 6 := by
    field_simp
    ring
  rw [key, le_div_iff₀ hy6]
  nlinarith only [hA, hsq, hy6, pow_pos hy0 8]

/-! ## One separated-square profile -/

/-- The `β`-free P4.7 profile of a separated square `s` at scale `k` (Lemma 4.6) and
the two estimates the cost envelope needs: the sup-gradient decay `28 · 2^{-(1 - 1/α) k}`
(`α = 7/4`) and the edge count `100 · 4^k`. -/
theorem squareProfile_facts (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L) {E : Type}
    [Fintype E] (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (hdeg : ∀ j, (Finset.univ.filter fun e => Λ.src e = j).card +
      (Finset.univ.filter fun e => Λ.tgt e = j).card ≤ 4)
    (h46 : L46Step boundary Λ) (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    (N : Finset (Fin L × Fin L → ℤ)) (hens : IsChargeEnsemble N) (hNa : AtMostOneNonNeutral N)
    (hNb : IsScaleSeparated boundary L N) (hNc : NeutralSplitsAreCharged boundary L N)
    (ϱstar : Fin L × Fin L → ℤ) (hϱstar : ϱstar ∈ neutralPart N) (k : {k : ℕ // 1 ≤ k})
    (C : {C : Finset (Finset (Fin L × Fin L)) // IsMinimumSquareCover boundary L k.val ϱstar C})
    (s : Finset (Fin L × Fin L)) (hs : s ∈ separatedSquares boundary L ϱstar k C) :
    (∀ j, squareWaveProfile Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf s k.val j ≠
        0 → setDist Λ s j ≤ 2 ^ (k.val - 1)) ∧
    (∀ j, setDist Λ s j ≤ 2 ^ (k.val - 3) →
        squareWaveProfile Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf s k.val j = 1) ∧
    (∀ ϱ' ∈ Λ.comparableDensities (neutralPart N) ϱstar, ∃ c : ℝ,
        ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'),
          squareWaveProfile Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf s k.val j =
            c) ∧
    Multigraph.pairing (squareWaveProfile Λ (Λ.comparableDensities (neutralPart N) ϱstar)
        centerOf s k.val) (fun j => (ϱstar j : ℝ)) = ((∑ j ∈ s, ϱstar j : ℤ) : ℝ) ∧
    ∑ j ∈ s, ϱstar j ≠ 0 ∧
    Λ.energy (squareWaveProfile Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf s
        k.val) ≤ 4096 ∧
    (∀ e, |Λ.grad (squareWaveProfile Λ (Λ.comparableDensities (neutralPart N) ϱstar) centerOf s
        k.val) e| ≤ 28 * (2 : ℝ) ^ (-(1 - 1 / (7 / 4 : ℝ)) * (k.val : ℝ))) ∧
    ((Finset.univ.filter fun e => Λ.grad (squareWaveProfile Λ
        (Λ.comparableDensities (neutralPart N) ϱstar) centerOf s k.val) e ≠ 0).card : ℝ) ≤
      100 * 4 ^ k.val := by
  classical
  obtain ⟨hϱN, hneutral⟩ := mem_neutralPart.mp hϱstar
  set N₁ := Λ.comparableDensities (neutralPart N) ϱstar with hN₁
  set n : ℕ := 2 ^ k.val with hn
  set S : ℕ := 2 ^ (k.val - 1) with hS
  set r : ℕ := 2 ^ (k.val - 3) with hr
  have hk := k.property
  have hnpos : 0 < n := Nat.two_pow_pos _
  have hSn : 2 * S = n := by
    rw [hS, hn, ← pow_succ']
    congr 1
    omega
  -- the patch and the square geometry
  obtain ⟨z, hz⟩ := separatedSquare_patch_nonempty boundary L ϱstar k C s hs
  obtain ⟨hzs, hzsupp⟩ := Finset.mem_inter.mp hz
  have hz0 : ϱstar z ≠ 0 := (Finset.mem_filter.mp hzsupp).2
  have hsne : s.Nonempty := ⟨z, hzs⟩
  have hq : ∑ j ∈ s, ϱstar j ≠ 0 := patchCharge_ne_zero boundary hL hNc hϱN hneutral hs
  have hsdiam : ∀ x ∈ s, ∀ y ∈ s, Λ.toSimpleGraph.dist x y ≤ 2 * (n - 1) := by
    intro x hx y hy
    rw [← hdist]
    exact latticeDistance_le_of_mem_separatedSquare boundary hL hs hx hy
  -- members of `𝒩₀(ϱ*)`
  have hN₁mem : ∀ ϱ ∈ N₁, ϱ ≠ 0 ∧ ∑ x, ϱ x = 0 ∧ Λ.IsDensityCenter ϱ (centerOf ϱ) := by
    intro ϱ hϱ
    have hϱ0 := (Λ.mem_comparableDensities.mp hϱ).1
    obtain ⟨hϱN', hϱn⟩ := mem_neutralPart.mp hϱ0
    have hne := hens.1 ϱ hϱN'
    exact ⟨hne, hϱn, hcenter ϱ hne⟩
  have hdiam1 := one_le_componentDiameter Λ N₁ centerOf hΛ hN₁mem
  have hL46 := h46 centerOf hcenter N hens hNa hNb hNc ϱstar hϱstar
  have hM128 : (chargeCoverScale : ℝ) / 128 = 512 := by norm_num [chargeCoverScale]
  have hM25 : (chargeCoverScale : ℝ) / 25 = 2 ^ 16 / 25 := by norm_num [chargeCoverScale]
  have hα : chargeCoverExponent = (7 / 4 : ℝ) := rfl
  -- distance from a point near `s` to the patch point `z`
  have hnear : ∀ p, setDist Λ s p ≤ S + 1 → Λ.toSimpleGraph.dist p z ≤ S + 1 + 2 * (n - 1) := by
    intro p hp
    obtain ⟨y, hy, hpy⟩ := exists_setDist_eq Λ hsne p
    have h1 := hΛ.dist_triangle (u := p) (v := y) (w := z)
    have h2 := hsdiam y hy z hzs
    omega
  -- relevant components are small (L4.6(2) with the repaired  bound)
  have hroot : ∀ c ∈ relevantComponents Λ N₁ centerOf s S,
      (2 ^ 16 / 128 : ℝ) * (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ) ^ (7 / 4 : ℝ) ≤
        5 / 2 * (n : ℝ) + densityPlusComponentDiameter Λ N₁ centerOf c := by
    intro c hc
    obtain ⟨-, p, hp, hpS⟩ := Finset.mem_filter.mp hc
    have h2 := (hL46 c).2.1
    have hle := componentRootDistance_le Λ N₁ centerOf c hp hz0
    have hpz := hnear p hpS
    have hrd : (densityPlusComponentRootDistance Λ N₁ centerOf c ϱstar : ℝ) ≤ 5 / 2 * n := by
      have : densityPlusComponentRootDistance Λ N₁ centerOf c ϱstar ≤ S + 1 + 2 * (n - 1) :=
        hle.trans hpz
      have h' : S + 1 + 2 * (n - 1) ≤ 5 * S := by omega
      have : (densityPlusComponentRootDistance Λ N₁ centerOf c ϱstar : ℝ) ≤ 5 * S := by
        exact_mod_cast this.trans h'
      have hSR : (2 * S : ℝ) = n := by exact_mod_cast hSn
      linarith only [this, hSR]
    rw [hM128, hα] at h2
    have hd0 : (0 : ℝ) ≤ densityPlusComponentDiameter Λ N₁ centerOf c := Nat.cast_nonneg _
    have : (2 ^ 16 / 128 : ℝ) = 512 := by norm_num
    rw [this]
    linarith only [h2, hrd]
  have hsmall200 : ∀ c ∈ relevantComponents Λ N₁ centerOf s S,
      200 * densityPlusComponentDiameter Λ N₁ centerOf c ≤ n := by
    intro c hc
    have h := hroot c hc
    have hd1 : (1 : ℝ) ≤ densityPlusComponentDiameter Λ N₁ centerOf c := by
      exact_mod_cast hdiam1 c
    have hself := Real.self_le_rpow_of_one_le hd1 (by norm_num : (1 : ℝ) ≤ 7 / 4)
    have : (200 * densityPlusComponentDiameter Λ N₁ centerOf c : ℕ) ≤ (n : ℝ) := by
      push_cast
      nlinarith only [h, hself]
    exact_mod_cast this
  have hsmall : ∀ c ∈ relevantComponents Λ N₁ centerOf s S,
      densityPlusComponentDiameter Λ N₁ centerOf c + r < S + 1 := by
    intro c hc
    have h200 := hsmall200 c hc
    have hd1 := hdiam1 c
    have hk8 : 8 ≤ k.val := by
      by_contra hlt
      have : n ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h8r : 8 * r = n := by
      rw [hr, hn, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  -- components avoid the support of `ϱ*`
  have hoff : ∀ j, ϱstar j ≠ 0 → j ∉ densityPlusUnion Λ N₁ centerOf := by
    intro j hj hjU
    set c := componentOf Λ N₁ centerOf j hjU
    have hjc := mem_componentVertices_componentOf Λ N₁ centerOf j hjU
    have h2 := (hL46 c).2.1
    have hle := componentRootDistance_le Λ N₁ centerOf c hjc hj
    rw [SimpleGraph.dist_self, Nat.le_zero] at hle
    rw [hle, Nat.cast_zero] at h2
    have hd1 : (1 : ℝ) ≤ densityPlusComponentDiameter Λ N₁ centerOf c := by
      exact_mod_cast hdiam1 c
    have hpos : 0 < (chargeCoverScale : ℝ) / 128 *
        (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ) ^ chargeCoverExponent := by
      have : (0 : ℝ) < chargeCoverScale := by norm_num [chargeCoverScale]
      have : (0 : ℝ) < (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ) ^ chargeCoverExponent :=
        Real.rpow_pos_of_pos (by linarith only [hd1]) _
      positivity
    linarith only [h2, hpos]
  -- the rest of the support is far from `s`
  have hfar : ∀ j, ϱstar j ≠ 0 → j ∉ s → S + 1 ≤ setDist Λ s j := by
    intro j hj hjs
    obtain ⟨y, hy, hjy⟩ := exists_setDist_eq Λ hsne j
    have h := thirtyTwo_mul_lt_latticeDistance boundary hs hy hj hjs
    rw [hdist, SimpleGraph.dist_comm, ← hjy] at h
    omega
  have hpair := pairing_squareWaveProfile Λ N₁ centerOf k.val hoff hfar
  -- the near-set count
  have hA : ((Finset.univ.filter fun j => setDist Λ s j ≤ S + 1).card : ℝ) ≤
      25 * (n : ℝ) ^ 2 := by
    have hsub : (Finset.univ.filter fun j => setDist Λ s j ≤ S + 1) ⊆
        Finset.univ.filter fun j => latticeDistance boundary L j z ≤ S + 1 + 2 * (n - 1) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [hdist]
      exact hnear j hj
    have hball := card_latticeDistance_le_le boundary L (S + 1 + 2 * (n - 1)) z
    have hcard := (Finset.card_le_card hsub).trans hball
    have hbound : (2 * (S + 1 + 2 * (n - 1)) + 1) ≤ 5 * n := by omega
    have : ((Finset.univ.filter fun j => setDist Λ s j ≤ S + 1).card : ℝ) ≤
        ((5 * n) ^ 2 : ℕ) := by
      exact_mod_cast hcard.trans (Nat.pow_le_pow_left hbound 2)
    push_cast at this
    linarith only [this]
  have hwidth : (n : ℝ) ≤ 4 * ((S + 1 - r : ℕ) : ℝ) := by
    have : n ≤ 4 * (S + 1 - r) := by
      rcases Nat.lt_or_ge k.val 3 with hk3 | hk3
      · have hr1 : r = 1 := by rw [hr, show k.val - 3 = 0 by omega, pow_zero]
        omega
      · have h8r : 8 * r = n := by
          rw [hr, hn, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
          congr 1
          omega
        omega
    exact_mod_cast this
  have hbdry : ∀ c ∈ relevantComponents Λ N₁ centerOf s S,
      ((densityPlusExternalBoundary Λ N₁ centerOf c).card : ℝ) ≤
        64 * densityPlusComponentDiameter Λ N₁ centerOf c := by
    intro c _
    exact_mod_cast (hL46 c).2.2
  -- the cube sum, from L4.6(1)–(2) and the lattice packing count
  have hcube : ∑ c ∈ relevantComponents Λ N₁ centerOf s S,
      (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 / 50 := by
    have : Nonempty (Fin L × Fin L) := ⟨z⟩
    choose! pt hpt hptS using fun c (hc : c ∈ relevantComponents Λ N₁ centerOf s S) =>
      (Finset.mem_filter.mp hc).2
    refine sum_cube_le_of_scale_separation (relevantComponents Λ N₁ centerOf s S)
      (fun c => densityPlusComponentDiameter Λ N₁ centerOf c)
      (fun c c' => densityPlusComponentDistance Λ N₁ centerOf c c') (n : ℝ)
      (by exact_mod_cast hnpos) (3 * n) (by push_cast; linarith only) (fun c _ => hdiam1 c) hroot
      ?_ ?_
    · intro c _ c' _ hcc'
      have h1 := (hL46 c).1 c' hcc'
      rw [hM25, hα] at h1
      exact h1
    · intro J hJ m hm hJsep
      have hinj : Set.InjOn pt (J : Set (DensityPlusComponent Λ N₁ centerOf)) := by
        intro c hc c' hc' heq
        by_contra hne
        have h := hJsep c hc c' hc' hne
        have hle := densityPlusComponentDistance_le Λ N₁ centerOf c c' (hpt c (hJ hc))
          (hpt c' (hJ hc'))
        rw [heq, SimpleGraph.dist_self] at hle
        omega
      rw [← Finset.card_image_of_injOn hinj]
      refine card_le_of_pairwise_latticeDistance_ge boundary hL z (3 * n) m hm (J.image pt) ?_ ?_
      · intro p hp
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
        rw [hdist]
        have := hnear (pt c) (hptS c (hJ hc))
        omega
      · intro p hp p' hp' hpp'
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hp'
        have hcc' : c ≠ c' := fun h => hpp' (h ▸ rfl)
        rw [hdist]
        exact (hJsep c hc c' hc' hcc').trans
          (densityPlusComponentDistance_le Λ N₁ centerOf c c' (hpt c (hJ hc)) (hpt c' (hJ hc')))
  have henergy := energy_squareWaveProfile_le Λ N₁ centerOf hΛ hdeg hsne k.val (n : ℝ)
    (by exact_mod_cast hnpos) hA hwidth hbdry (fun c _ => hdiam1 c) hcube
  -- support and plateau
  have hsupp : ∀ j, squareWaveProfile Λ N₁ centerOf s k.val j ≠ 0 →
      setDist Λ s j ≤ 2 ^ (k.val - 1) := fun j hj =>
    squareWaveProfile_support Λ N₁ centerOf hΛ hsne k.val hsmall hj
  -- the sup-gradient bound
  set y : ℝ := (2 : ℝ) ^ ((k.val : ℝ) / 7) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow (by norm_num) (by positivity)
  have hy0 : 0 < y := by linarith only [hy1]
  have hy7 : y ^ 7 = (n : ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), hn]
    have h7 : (k.val : ℝ) / 7 * ((7 : ℕ) : ℝ) = ((k.val : ℕ) : ℝ) := by push_cast; ring
    rw [h7, Real.rpow_natCast]
    push_cast
    ring
  have hy3 : (y ^ 3)⁻¹ = (2 : ℝ) ^ (-(1 - 1 / (7 / 4 : ℝ)) * (k.val : ℝ)) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  have hdiamy : ∀ c ∈ relevantComponents Λ N₁ centerOf s S,
      (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ) + 1 ≤ y ^ 4 + 1 := by
    intro c hc
    have hroot' := hroot c hc
    have h200 : (200 * (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ)) ≤ n := by
      exact_mod_cast hsmall200 c hc
    set d : ℝ := (densityPlusComponentDiameter Λ N₁ centerOf c : ℝ)
    have hd0 : 0 ≤ d := Nat.cast_nonneg _
    have hpow : d ^ (7 / 4 : ℝ) ≤ y ^ 7 := by
      rw [hy7]
      have : (2 ^ 16 / 128 : ℝ) = 512 := by norm_num
      rw [this] at hroot'
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith only [hroot', h200, hn0]
    have hdy : d ≤ y ^ 4 := by
      by_contra hlt
      push Not at hlt
      have h1 := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ y ^ 4) hlt
        (by norm_num : (0 : ℝ) < 7 / 4)
      have h2 : (y ^ 4) ^ (7 / 4 : ℝ) = y ^ 7 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le, ← Real.rpow_natCast]
        norm_num
      linarith only [h1, h2, hpow]
    linarith only [hdy]
  have hgrad : ∀ e, |Λ.grad (squareWaveProfile Λ N₁ centerOf s k.val) e| ≤
      28 * (2 : ℝ) ^ (-(1 - 1 / (7 / 4 : ℝ)) * (k.val : ℝ)) := by
    intro e
    have h := SpinWave.squareWaveProfile_grad_le Λ N₁ centerOf hΛ hsne k.val (y ^ 4 + 1) 8
      hdiamy (fun e' => card_components_externalBoundary_edge_le Λ hdeg N₁ centerOf _ e') e
    rw [← hy3]
    refine h.trans (sqrt_div_sq_le_of_pow hy1 ?_ ?_)
    · rw [hy7]; exact hwidth
    · have h4 : 1 ≤ y ^ 4 := one_le_pow₀ hy1
      have h8 : y ^ 8 = (y ^ 4) ^ 2 := by ring
      rw [h8]
      nlinarith only [h4]
  -- the edge count
  have hcount : ((Finset.univ.filter fun e =>
      Λ.grad (squareWaveProfile Λ N₁ centerOf s k.val) e ≠ 0).card : ℝ) ≤ 100 * 4 ^ k.val := by
    have hc := card_grad_ne_zero_le Λ hdeg (squareWaveProfile Λ N₁ centerOf s k.val)
      (Finset.univ.filter fun j => setDist Λ s j ≤ S + 1) (fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hsupp j hj).trans (Nat.le_succ _))
    have hc' : ((Finset.univ.filter fun e =>
        Λ.grad (squareWaveProfile Λ N₁ centerOf s k.val) e ≠ 0).card : ℝ) ≤
        4 * ((Finset.univ.filter fun j => setDist Λ s j ≤ S + 1).card : ℝ) := by
      exact_mod_cast hc
    have hn2 : (n : ℝ) ^ 2 = 4 ^ k.val := by
      rw [hn]; push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [← hn2]
    linarith only [hc', hA]
  refine ⟨hsupp, fun j hj => squareWaveProfile_plateau Λ N₁ centerOf k.val hj, ?_, hpair, hq,
    henergy, hgrad, hcount⟩
  intro ϱ' hϱ'
  obtain ⟨-, hn', hc'⟩ := hN₁mem ϱ' hϱ'
  exact squareWaveProfile_const_densityDomainPlus Λ N₁ centerOf hΛ k.val hϱ' hn' hc'

/-! ## The linear-mass colour class -/

/-- One of the two colour classes carries at least half of the linear charge mass. -/
theorem exists_linearMassColor {V : Type} [Fintype V] (color : V → Bool) (ϱ : V → ℤ) :
    ∃ b : Bool, (1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤
      ∑ j, if color j = b then |(ϱ j : ℝ)| else 0 := by
  have hsplit : ∑ j, |(ϱ j : ℝ)| = (∑ j, if color j = true then |(ϱ j : ℝ)| else 0) +
      ∑ j, if color j = false then |(ϱ j : ℝ)| else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases color j <;> simp
  by_cases h : (1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤ ∑ j, if color j = true then |(ϱ j : ℝ)| else 0
  · exact ⟨true, h⟩
  · refine ⟨false, ?_⟩
    push Not at h
    linarith only [h, hsplit]

/-- A nonzero integer has absolute value at least one in `ℝ`. -/
theorem one_le_abs_intCast {q : ℤ} (hq : q ≠ 0) : 1 ≤ |(q : ℝ)| := by
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hq

/-! ## The full family -/

/-- **The all-scales graded spin wave** of a neutral density `ϱ` of a KP Theorem 2.2 ensemble on a
square domain: the sign waves on the linear-mass colour class (scale `0`) together with the
`β`-free P4.7 profiles of all separated squares of the shared minimum-cover selection
(scales `k ≥ 1`), with `α = 7/4`, `K₀ = 4096`, `K₁ = 28`. The base pieces carry at least half of
the linear charge mass, there is one square piece per separated square, and a piece at scale `k`
has at most `100 · 4^k` edges with a nonzero gradient. -/
theorem exists_fullGradedSpinWave (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L) {E : Type}
    [Fintype E] (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    (N : Finset (Fin L × Fin L → ℤ)) (hens : IsChargeEnsemble N) (hNa : AtMostOneNonNeutral N)
    (hNb : IsScaleSeparated boundary L N) (hNc : NeutralSplitsAreCharged boundary L N)
    (ϱ : Fin L × Fin L → ℤ) (hϱ : ϱ ∈ neutralPart N) :
    ∃ Wv : SpinWave.GradedSpinWave.{0, 0, 0} Λ (neutralPart N) centerOf ϱ,
      Wv.alpha = 7 / 4 ∧ Wv.K₀ = 4096 ∧ Wv.K₁ = 28 ∧
      ((1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤
        ∑ t ∈ (letI := Wv.finite; Finset.univ.filter fun t => Wv.scale t = 0), |Wv.charge t|) ∧
      ((letI := Wv.finite; (Finset.univ.filter fun t => 1 ≤ Wv.scale t).card) =
        separatedSquareTotal boundary L
          (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) ϱ) ∧
      ∀ t, ((Finset.univ.filter fun e => Λ.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤
        100 * 4 ^ Wv.scale t := by
  classical
  have hL0 : 0 < L := by omega
  have hdeg := B.endpointDegree_le_four
  obtain ⟨hϱN, hneutral⟩ := mem_neutralPart.mp hϱ
  have hϱ0 : ϱ ≠ 0 := hens.1 ϱ hϱN
  set N₁ := Λ.comparableDensities (neutralPart N) ϱ with hN₁
  -- the base colour class
  obtain ⟨b, hb⟩ := exists_linearMassColor B.color ϱ
  set Sb := SpinWave.signBaseSites Λ B ϱ b with hSb
  have hsep := initialWaveSeparation_of_scaleSeparated boundary Λ hdist hΛ hens hNb centerOf
    hcenter hϱ
  -- the separated squares, scale `k + 1` for `k < L`
  set sep : ℕ → Finset (Finset (Fin L × Fin L)) := fun k =>
    separatedSquares boundary L ϱ ⟨k + 1, by omega⟩
      (sharedMinimumSquareCover boundary L ϱ hL0 ⟨k + 1, by omega⟩) with hsepdef
  set T : Finset (Σ _ : ℕ, Finset (Fin L × Fin L)) := (Finset.range L).sigma sep with hT
  have hsepmem : ∀ t ∈ T, t.2 ∈ separatedSquares boundary L ϱ ⟨t.1 + 1, by omega⟩
      (sharedMinimumSquareCover boundary L ϱ hL0 ⟨t.1 + 1, by omega⟩) :=
    fun t ht => (Finset.mem_sigma.mp ht).2
  -- the profile of a square
  set ψ : (Σ _ : ℕ, Finset (Fin L × Fin L)) → Fin L × Fin L → ℝ :=
    fun t => squareWaveProfile Λ N₁ centerOf t.2 (t.1 + 1) with hψ
  have hF := fun t (ht : t ∈ T) => squareProfile_facts boundary hL Λ hΛ hdist hdeg h46 centerOf
    hcenter N hens hNa hNb hNc ϱ hϱ ⟨t.1 + 1, by omega⟩
    (sharedMinimumSquareCover boundary L ϱ hL0 ⟨t.1 + 1, by omega⟩) t.2 (hsepmem t ht)
  have hsne : ∀ t ∈ T, t.2.Nonempty := by
    intro t ht
    obtain ⟨z, hz⟩ := separatedSquare_patch_nonempty boundary L ϱ _ _ t.2 (hsepmem t ht)
    exact ⟨z, (Finset.mem_inter.mp hz).1⟩
  have hw : ∀ t ∈ T, IsSquareWave Λ t.2 (t.1 + 1) (ψ t) := by
    intro t ht
    refine ⟨fun j hj => (setDist_le_iff Λ (hsne t ht) j _).mp ((hF t ht).1 j hj),
      ⟨1, fun j hj => (hF t ht).2.1 j ((setDist_le_iff Λ (hsne t ht) j _).mpr hj)⟩⟩
  have hnearD : ∀ t ∈ T, ∀ j y, y ∈ t.2 → Λ.toSimpleGraph.dist j y ≤ 2 ^ t.1 + 1 →
      j ∈ Λ.densityDomain ϱ (centerOf ϱ) := by
    intro t ht j y hy hjy
    exact mem_densityDomain_of_near_separatedSquare boundary hL Λ hdist hΛ (hcenter ϱ hϱ0)
      (by omega) (hsepmem t ht) hy (by simpa using hjy)
  -- the base/square far-support fact
  have hbasefar : ∀ t ∈ T, ∀ x, ϱ x ≠ 0 → x ∉ t.2 → ∀ y ∈ t.2,
      2 ^ (t.1 + 1 - 1) + 1 < Λ.toSimpleGraph.dist x y := by
    intro t ht x hx hxs y hy
    have h : 32 * 2 ^ (t.1 + 1) < latticeDistance boundary L y x :=
      thirtyTwo_mul_lt_latticeDistance boundary (hsepmem t ht) hy hx hxs
    rw [hdist, SimpleGraph.dist_comm] at h
    simp only [Nat.add_sub_cancel]
    have h1 : 1 ≤ 2 ^ t.1 := Nat.one_le_two_pow
    omega
  -- two squares
  have hpair : ∀ e, ∀ t ∈ T, ∀ t' ∈ T, t.1 < t'.1 →
      Λ.grad (ψ t) e = 0 ∨ Λ.grad (ψ t') e = 0 := by
    intro e t ht t' ht' hlt
    by_contra hc
    push Not at hc
    obtain ⟨x, hx, hwx⟩ : ∃ x, (x = Λ.src e ∨ x = Λ.tgt e) ∧ ψ t x ≠ 0 := by
      rcases ne_zero_of_grad_ne_zero Λ (ψ t) e hc.1 with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    obtain ⟨x', hx', hwx'⟩ : ∃ x', (x' = Λ.src e ∨ x' = Λ.tgt e) ∧ ψ t' x' ≠ 0 := by
      rcases ne_zero_of_grad_ne_zero Λ (ψ t') e hc.2 with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    obtain ⟨y, hy, hxy⟩ := (hw t ht).supp x hwx
    obtain ⟨y', hy', hxy'⟩ := (hw t' ht').supp x' hwx'
    obtain ⟨hsrc, htgt⟩ := cross_scale_endpoints_near boundary hL Λ hdist hΛ ϱ
      (by omega : 1 ≤ t.1 + 1) (by omega : t.1 + 1 < t'.1 + 1) (hsepmem t ht)
      (hsepmem t' ht') e hx hx' hy hxy hy' hxy'
    exact hc.2 ((hw t' ht').grad_eq_zero Λ e hsrc htgt)
  have hsame : ∀ e, ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → t.1 = t'.1 →
      Λ.grad (ψ t) e = 0 ∨ Λ.grad (ψ t') e = 0 := by
    intro e t ht t' ht' htt' heq
    have hs2 : t.2 ≠ t'.2 := fun h => htt' (Sigma.ext heq (heq_of_eq h))
    refine IsSquareWave.grad_disjoint_of_far Λ hΛ (hw t ht) (hw t' ht') ?_ e
    intro y hy y' hy'
    have hsC : t'.2 ∈ (sharedMinimumSquareCover boundary L ϱ hL0
        ⟨t.1 + 1, by omega⟩).val := by
      have := (Finset.mem_filter.mp (hsepmem t' ht')).1
      rwa [show (⟨t'.1 + 1, by omega⟩ : {k : ℕ // 1 ≤ k}) = ⟨t.1 + 1, by omega⟩ from
        Subtype.ext (by simp [heq])] at this
    have h32' : 32 * 2 ^ (t.1 + 1) < Λ.toSimpleGraph.dist y y' := by
      rw [← hdist]
      exact thirtyTwo_mul_lt_latticeDistance_of_mem_cover boundary (hsepmem t ht) hsC
        (Ne.symm hs2) hy hy'
    simp only [Nat.add_sub_cancel]
    rw [← heq]
    have : 2 ^ t.1 ≤ 2 ^ (t.1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ t.1 := Nat.one_le_two_pow
    omega
  -- membership facts for base sites
  have hSbmem : ∀ m ∈ Sb, ϱ m ≠ 0 ∧ B.color m = b := fun m hm => by
    simpa [hSb, SpinWave.signBaseSites] using hm
  have hbase_supp : ∀ m (j : Fin L × Fin L), SpinWave.signBaseWave ϱ m j ≠ 0 → ϱ j ≠ 0 ∧ j = m :=
    fun m j hj => by
      have hjm : j = m := by
        by_contra hne
        exact hj (SpinWave.signBaseWave_eq_zero_of_ne ϱ m j hne)
      subst hjm
      refine ⟨fun h0 => hj ?_, rfl⟩
      simp [SpinWave.signBaseWave, SpinWave.signUnit, h0]
  -- the index type and the family
  let ι := {m // m ∈ Sb} ⊕ {t // t ∈ T}
  let sc : ι → ℕ := Sum.elim (fun _ => 0) (fun t => t.val.1 + 1)
  let pc : ι → Fin L × Fin L → ℝ :=
    Sum.elim (fun m => SpinWave.signBaseWave ϱ m.val) (fun t => ψ t.val)
  let ch : ι → ℝ := Sum.elim (fun m => |(ϱ m.val : ℝ)|) (fun t => ((∑ j ∈ t.val.2, ϱ j : ℤ) : ℝ))
  let Wv : SpinWave.GradedSpinWave Λ (neutralPart N) centerOf ϱ := {
    ι := ι
    finite := inferInstance
    alpha := 7 / 4
    alpha_gt_one := by norm_num
    K₀ := 4096
    K₀_nonneg := by norm_num
    K₁ := 28
    K₁_nonneg := by norm_num
    scale := sc
    piece := pc
    charge := ch
    countPerScale := fun k => ((Finset.univ.filter fun t : ι => sc t = k).card : ℝ)
    countPerScale_nonneg := fun _ => Nat.cast_nonneg _
    count := fun _ => le_rfl
    grad_disjoint := by
      intro t t' htt' e
      rcases t with m | t <;> rcases t' with m' | t'
      · have hm := hSbmem m.val m.property
        have hm' := hSbmem m'.val m'.property
        have hne : m.val ≠ m'.val := fun h => htt' (congrArg Sum.inl (Subtype.ext h))
        exact SpinWave.grad_disjoint_signBaseWave Λ B ϱ hm.1 hm'.1 (hm.2.trans hm'.2.symm) hne e
      · exact IsSquareWave.grad_disjoint_base Λ hΛ (hw t'.val t'.property)
          (fun j hj => (hbase_supp m.val j hj).1) (hbasefar t'.val t'.property) e
      · exact (IsSquareWave.grad_disjoint_base Λ hΛ (hw t.val t.property)
          (fun j hj => (hbase_supp m'.val j hj).1) (hbasefar t.val t.property) e).symm
      · have hne : t.val ≠ t'.val := fun h => htt' (congrArg Sum.inr (Subtype.ext h))
        rcases lt_trichotomy t.val.1 t'.val.1 with hlt | heq | hgt
        · exact hpair e t.val t.property t'.val t'.property hlt
        · exact hsame e t.val t.property t'.val t'.property hne heq
        · exact (hpair e t'.val t'.property t.val t.property hgt).symm
    const_plus := by
      intro t ϱ' hϱ'
      rcases t with m | t
      · exact ⟨0, fun j hj => SpinWave.signBaseWave_eq_zero_on_densityDomainPlus Λ
          (neutralPart N) centerOf ϱ m.val (hSbmem m.val m.property).1 hsep hϱ' hj⟩
      · exact (hF t.val t.property).2.2.1 ϱ' hϱ'
    supp := by
      intro t j hj
      rcases t with m | t
      · obtain ⟨hj0, -⟩ := hbase_supp m.val j hj
        exact Λ.mem_densityDomain_of_center hΛ hneutral (hcenter ϱ hϱ0) hj0
      · obtain ⟨y, hy, hjy⟩ := (hw t.val t.property).supp j hj
        exact hnearD t.val t.property j y hy (by simp only [Nat.add_sub_cancel] at hjy; omega)
    pairing := by
      intro t
      rcases t with m | t
      · exact SpinWave.pairing_signBaseWave ϱ m.val (hSbmem m.val m.property).1
      · exact (hF t.val t.property).2.2.2.1
    charge_ge_one := by
      intro t
      rcases t with m | t
      · show 1 ≤ |(|(ϱ m.val : ℝ)|)|
        rw [abs_abs]
        exact one_le_abs_intCast (hSbmem m.val m.property).1
      · exact one_le_abs_intCast (hF t.val t.property).2.2.2.2.1
    energy_le := by
      intro t
      rcases t with m | t
      · have h := SpinWave.energy_signBaseWave_le Λ B ϱ m.val (hSbmem m.val m.property).1
        show Λ.energy (SpinWave.signBaseWave ϱ m.val) ≤ 4096 * |(ϱ m.val : ℝ)| ^ 2
        nlinarith only [h, sq_nonneg |(ϱ m.val : ℝ)|]
      · have h := (hF t.val t.property).2.2.2.2.2.1
        have hq := one_le_abs_intCast (hF t.val t.property).2.2.2.2.1
        show Λ.energy (ψ t.val) ≤ 4096 * ((∑ j ∈ t.val.2, ϱ j : ℤ) : ℝ) ^ 2
        have hq2 : 1 ≤ ((∑ j ∈ t.val.2, ϱ j : ℤ) : ℝ) ^ 2 := by
          rw [← sq_abs]; nlinarith only [hq]
        nlinarith only [h, hq2]
    grad_le := by
      intro t e
      rcases t with m | t
      · have h := SpinWave.abs_grad_signBaseWave_le Λ ϱ m.val (hSbmem m.val m.property).1 e
        show |Λ.grad (SpinWave.signBaseWave ϱ m.val) e| ≤
          28 * (2 : ℝ) ^ (-(1 - 1 / (7 / 4 : ℝ)) * ((0 : ℕ) : ℝ))
        rw [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
        linarith only [h]
      · exact (hF t.val t.property).2.2.2.2.2.2.1 e }
  refine ⟨Wv, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · -- the base pieces carry half the linear mass
    show (1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤
      ∑ t ∈ Finset.univ.filter (fun t : ι => sc t = 0), |ch t|
    rw [Finset.sum_filter, Fintype.sum_sum_type]
    simp only [sc, ch, Sum.elim_inl, Sum.elim_inr, abs_abs, Nat.add_one_ne_zero, ite_true,
      ite_false, Finset.sum_const_zero, add_zero]
    refine hb.trans (le_of_eq ?_)
    rw [Finset.sum_coe_sort Sb (fun m => |(ϱ m : ℝ)|), hSb, SpinWave.signBaseSites,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : ϱ j = 0
    · simp [hj]
    · simp [hj]
  · -- one square piece per separated square
    show (Finset.univ.filter fun t : ι => 1 ≤ sc t).card = _
    rw [Finset.card_filter, Fintype.sum_sum_type]
    have h1 : ∀ m : {m // m ∈ Sb}, (if 1 ≤ sc (Sum.inl m) then 1 else 0) = 0 :=
      fun m => ite_eq_right (by simp [sc])
    have h2 : ∀ t : {t // t ∈ T}, (if 1 ≤ sc (Sum.inr t) then 1 else 0) = 1 :=
      fun t => ite_eq_left (by simp [sc])
    simp only [h1, h2, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_univ]
    rw [Fintype.card_coe, hT, Finset.card_sigma]
    rfl
  · -- the edge counts
    intro t
    rcases t with m | t
    · have h := card_grad_ne_zero_le Λ hdeg (SpinWave.signBaseWave ϱ m.val) {m.val}
        (fun j hj => by rw [(hbase_supp m.val j hj).2]; exact Finset.mem_singleton_self _)
      show ((Finset.univ.filter fun e => Λ.grad (SpinWave.signBaseWave ϱ m.val) e ≠ 0).card :
        ℝ) ≤ 100 * 4 ^ (0 : ℕ)
      rw [Finset.card_singleton] at h
      have h' : ((Finset.univ.filter fun e =>
          Λ.grad (SpinWave.signBaseWave ϱ m.val) e ≠ 0).card : ℝ) ≤ 4 := by exact_mod_cast h
      calc _ ≤ (4 : ℝ) := h'
        _ ≤ 100 * 4 ^ (0 : ℕ) := by norm_num
    · exact (hF t.val t.property).2.2.2.2.2.2.2

end FroehlichSpencer.BKT.Generic

end
