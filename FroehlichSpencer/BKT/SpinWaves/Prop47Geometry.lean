/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Prop47Statements
public import FroehlichSpencer.BKT.SpinWaves.FlattenedWave
import FroehlichSpencer.BKT.Charges.SeparatedPatch
import FroehlichSpencer.BKT.Charges.PatchIsolation
import FroehlichSpencer.BKT.Charges.ParentScaleEstimates
import FroehlichSpencer.BKT.Charges.SquareDiameterBounds
import FroehlichSpencer.BKT.Charges.DensityRouting
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Geometry of separated squares and `D⁺` components for KP Proposition 4.7

For a separated square `s ∈ 𝒮_k^sep(ϱ*)`:

* `s` has graph diameter at most `2(2^k - 1)` (`dist_le_of_mem_separatedSquare`), and every
  support point of `ϱ*` outside `s` is at distance at least `R_k = 2M 2^{α(k+1)} > 32·2^k` from
  `s` (`thirtyTwo_mul_lt_setDist`);
* the patch charge `q = ∑_{j ∈ s} ϱ*(j)` is nonzero (`patchCharge_ne_zero`, , from
  Theorem 2.2(c));
* every component of `⋃_{ϱ' ∈ 𝒩₀(ϱ*)} D⁺(ϱ')` contains each `D⁺(ϱ')` it meets
  (`densityDomainPlus_subset_component`) and has diameter at least one
  (`one_le_componentDiameter`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SpinWaves.P47

open Reduction

/-! ## Separated squares -/

section Square

variable (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L) {ϱ : ChargeDensity L}
  {k : {k : ℕ // 1 ≤ k}}
  {C : {C : Finset (Finset (Fin L × Fin L)) // IsMinimumSquareCover boundary L k.val ϱ C}}
  {s : Finset (Fin L × Fin L)}

include hL in
/-- A separated square has graph diameter at most `2(2^k - 1)`. -/
theorem latticeDistance_le_of_mem_separatedSquare (hs : s ∈ separatedSquares boundary L ϱ k C)
    {x y : Fin L × Fin L} (hx : x ∈ s) (hy : y ∈ s) :
    latticeDistance boundary L x y ≤ 2 * (2 ^ k.val - 1) := by
  have hsC : s ∈ C.val := (Finset.mem_filter.mp hs).1
  have hsq : s ∈ kpSquares boundary L k.val := C.property.1.1 hsC
  have hdiam : squareDiameter boundary L s ≤ 2 * (squareSide k.val - 1) := by
    cases boundary with
    | free => exact free_squareDiameter_le_all L k.val s hsq
    | periodic => exact periodic_squareDiameter_le L k.val hL s hsq
  exact (latticeDistance_le_squareDiameter_of_mem boundary L s x y hx hy).trans hdiam

/-- Support points of `ϱ` outside a separated square are at distance more than `32·2^k` from
every point of the square (KP (2.4); `R_k > 32·2^k`,  -/
theorem thirtyTwo_mul_lt_latticeDistance (hs : s ∈ separatedSquares boundary L ϱ k C)
    {x y : Fin L × Fin L} (hx : x ∈ s) (hy : ϱ y ≠ 0) (hys : y ∉ s) :
    32 * 2 ^ k.val < latticeDistance boundary L x y := by
  have hsep := pointwise_separation_of_separatedSquare boundary L ϱ k C s hs x hx y
    (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, hys⟩)
  have h32 := squareSeparationThreshold_gt_32_side k
  have : (32 * 2 ^ k.val : ℕ) < (latticeDistance boundary L x y : ℝ) := by
    push_cast
    simp only [squareSide] at h32
    push_cast at h32
    linarith
  exact_mod_cast this

/-- Distinct members `s, t` of one minimum cover with `s` separated are more than `32·2^k`
apart (KP (2.4)). -/
theorem thirtyTwo_mul_lt_latticeDistance_of_mem_cover
    (hs : s ∈ separatedSquares boundary L ϱ k C) {t : Finset (Fin L × Fin L)} (ht : t ∈ C.val)
    (hts : t ≠ s) {x y : Fin L × Fin L} (hx : x ∈ s) (hy : y ∈ t) :
    32 * 2 ^ k.val < latticeDistance boundary L x y := by
  have hs' : s ∈ C.val ∧ 1 < C.val.card ∧
      ∀ t ∈ C.val, t ≠ s →
        (2 * (chargeCoverScale : ℝ)) * (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) ≤
          (squareDistance boundary L s t : ℝ) := by
    simpa [separatedSquares] using hs
  have hsep : squareSeparationThreshold k ≤ (latticeDistance boundary L x y : ℝ) :=
    (hs'.2.2 t ht hts).trans
      (squareDistance_le_latticeDistance_real_of_mem boundary L s t x y hx hy)
  have h32 := squareSeparationThreshold_gt_32_side k
  have : (32 * 2 ^ k.val : ℕ) < (latticeDistance boundary L x y : ℝ) := by
    push_cast
    simp only [squareSide] at h32
    push_cast at h32
    linarith
  exact_mod_cast this

/-- A separated square has a support point of `ϱ` outside it (the minimum cover has another
square, which meets the support away from `s`;  (2)). -/
theorem exists_support_not_mem_separatedSquare (hs : s ∈ separatedSquares boundary L ϱ k C) :
    ∃ y, ϱ y ≠ 0 ∧ y ∉ s := by
  classical
  have hs' : s ∈ C.val ∧ 1 < C.val.card ∧
      ∀ t ∈ C.val, t ≠ s →
        (2 * (chargeCoverScale : ℝ)) * (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) ≤
          (squareDistance boundary L s t : ℝ) := by
    simpa [separatedSquares] using hs
  obtain ⟨t, ht, hts⟩ : ∃ t ∈ C.val, t ≠ s := by
    by_contra h
    push Not at h
    have : C.val ⊆ {s} := fun t ht => Finset.mem_singleton.mpr (h t ht)
    have := Finset.card_le_card this
    rw [Finset.card_singleton] at this
    omega
  obtain ⟨y, hy⟩ := supportPatch_nonempty_of_mem_minimumSquareCover boundary L k.val ϱ C.val
    C.property t ht
  obtain ⟨hyt, hysupp⟩ := Finset.mem_inter.mp hy
  refine ⟨y, (Finset.mem_filter.mp hysupp).2, fun hys => ?_⟩
  have hR := hs'.2.2 t ht hts
  have hzero : squareDistance boundary L s t ≤ latticeDistance boundary L y y :=
    squareDistance_le_latticeDistance_of_mem boundary L s t y y hys hyt
  have hyy : latticeDistance boundary L y y = 0 := by
    cases boundary <;> exact SimpleGraph.dist_self
  rw [hyy, Nat.le_zero] at hzero
  rw [hzero, Nat.cast_zero] at hR
  have hpos : 0 < (2 * (chargeCoverScale : ℝ)) * (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) := by
    have : (0 : ℝ) < chargeCoverScale := by norm_num [chargeCoverScale]
    positivity
  linarith

/-- The restriction `s ∩ ϱ` of KP (2.8). -/
def patch (s : Finset (Fin L × Fin L)) (ϱ : ChargeDensity L) : ChargeDensity L :=
  fun j => if j ∈ s then ϱ j else 0

include hL in
/-- : the patch of a separated square of a neutral density of an ensemble with property (c)
of Theorem 2.2 is non-neutral. -/
theorem patchCharge_ne_zero {N : Finset (ChargeDensity L)}
    (hN : NeutralSplitsAreCharged boundary L N) (hϱN : ϱ ∈ N) (hneutral : ∑ j, ϱ j = 0)
    (hs : s ∈ separatedSquares boundary L ϱ k C) : ∑ j ∈ s, ϱ j ≠ 0 := by
  classical
  set ϱ₁ := patch s ϱ with hϱ₁
  set ϱ₂ : ChargeDensity L := fun j => if j ∈ s then 0 else ϱ j with hϱ₂
  obtain ⟨x, hx⟩ := separatedSquare_patch_nonempty boundary L ϱ k C s hs
  obtain ⟨hxs, hxsupp⟩ := Finset.mem_inter.mp hx
  have hx0 : ϱ x ≠ 0 := (Finset.mem_filter.mp hxsupp).2
  obtain ⟨y, hy0, hys⟩ := exists_support_not_mem_separatedSquare boundary hs
  have h₁ : ϱ₁ ≠ 0 := fun h => hx0 (by
    have := congrFun h x
    simpa [hϱ₁, patch, hxs] using this)
  have h₂ : ϱ₂ ≠ 0 := fun h => hy0 (by
    have := congrFun h y
    simpa [hϱ₂, hys] using this)
  have hdisj : Disjoint (Function.support ϱ₁) (Function.support ϱ₂) := by
    rw [Function.disjoint_support_iff]
    intro j hj
    by_cases hjs : j ∈ s
    · simp [hϱ₂, hjs]
    · exact absurd (by simp [hϱ₁, patch, hjs]) hj
  have hsum : ϱ = ϱ₁ + ϱ₂ := by
    funext j
    by_cases hjs : j ∈ s <;> simp [hϱ₁, hϱ₂, patch, hjs]
  -- the separation hypothesis of property (c)
  have hsupp₁ : ∀ j, ϱ₁ j ≠ 0 → j ∈ s := fun j hj => by
    by_contra hjs
    exact hj (by simp [hϱ₁, patch, hjs])
  have hsupp₂ : ∀ j, ϱ₂ j ≠ 0 → ϱ j ≠ 0 ∧ j ∉ s := fun j hj => by
    by_cases hjs : j ∈ s
    · exact absurd (by simp [hϱ₂, hjs]) hj
    · refine ⟨fun h => hj (by simp [hϱ₂, hjs, h]), hjs⟩
  have hR := squareSeparationThreshold_gt_32_side k
  have hdistlow : squareSeparationThreshold k ≤ (densityDistance boundary L ϱ₁ ϱ₂ : ℝ) := by
    have hne : ((chargeSupport ϱ₁).product (chargeSupport ϱ₂)).Nonempty := by
      refine ⟨(x, y), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩⟩
      · simpa [hϱ₁, patch, hxs] using hx0
      · simpa [hϱ₂, hys] using hy0
    unfold densityDistance squareDistance
    rw [dite_eq_left hne]
    obtain ⟨⟨a, b⟩, hab, hmin⟩ := Finset.mem_image.mp
      (Finset.min'_mem (((chargeSupport ϱ₁).product (chargeSupport ϱ₂)).image
        fun p : (Fin L × Fin L) × (Fin L × Fin L) => latticeDistance boundary L p.1 p.2)
        (Finset.image_nonempty.mpr hne))
    rw [← hmin]
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hb0, hbs⟩ := hsupp₂ b (Finset.mem_filter.mp hb).2
    exact pointwise_separation_of_separatedSquare boundary L ϱ k C s hs a
      (hsupp₁ a (Finset.mem_filter.mp ha).2) b
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0⟩, hbs⟩)
  have hdiam₁ : chargeDiameter boundary L ϱ₁ ≤ 2 * (2 ^ k.val - 1) := by
    unfold chargeDiameter squareDiameter
    split_ifs with hne
    · refine Finset.max'_le _ _ _ fun d hd => ?_
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact latticeDistance_le_of_mem_separatedSquare boundary hL hs
        (hsupp₁ a (Finset.mem_filter.mp ha).2) (hsupp₁ b (Finset.mem_filter.mp hb).2)
    · exact Nat.zero_le _
  have hsmall : 2 * (chargeCoverScale : ℝ) *
      ((min (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂) : ℕ) : ℝ) ^
        chargeCoverExponent < squareSeparationThreshold k := by
    have hmin : ((min (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂) : ℕ) : ℝ) ≤
        ((2 : ℝ) ^ (k.val + 1)) := by
      have h1 : min (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂) ≤
          2 * (2 ^ k.val - 1) := (min_le_left _ _).trans hdiam₁
      have h2 : 2 * (2 ^ k.val - 1) < 2 ^ (k.val + 1) := by
        have := Nat.one_le_two_pow (n := k.val)
        rw [pow_succ]
        omega
      exact_mod_cast (h1.trans h2.le)
    have hα : (0 : ℝ) < chargeCoverExponent := by norm_num [chargeCoverExponent]
    have hM : (0 : ℝ) < chargeCoverScale := by norm_num [chargeCoverScale]
    -- strictness from `min < 2^(k+1)`
    have hstrict : ((min (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂) : ℕ) : ℝ)
        ^ chargeCoverExponent < (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) := by
      have h1 : min (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂) <
          2 ^ (k.val + 1) := by
        have := Nat.one_le_two_pow (n := k.val)
        have h3 := (min_le_left (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂)).trans
          hdiam₁
        rw [pow_succ]
        omega
      have h1R : ((min (chargeDiameter boundary L ϱ₁) (chargeDiameter boundary L ϱ₂) : ℕ) : ℝ) <
          (2 : ℝ) ^ (k.val + 1) := by exact_mod_cast h1
      calc _ < ((2 : ℝ) ^ (k.val + 1)) ^ chargeCoverExponent :=
            Real.rpow_lt_rpow (Nat.cast_nonneg _) h1R hα
        _ = (2 : ℝ) ^ (chargeCoverExponent * (k.val + 1 : ℕ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
    unfold squareSeparationThreshold
    have := mul_lt_mul_of_pos_left hstrict (by positivity : (0 : ℝ) < 2 * chargeCoverScale)
    exact this
  have hc := (hN ϱ hϱN hneutral ϱ₁ ϱ₂ h₁ h₂ hdisj hsum
    (hsmall.le.trans hdistlow)).1
  have hrw : ∑ j, ϱ₁ j = ∑ j ∈ s, ϱ j := by
    simp only [hϱ₁, patch]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rwa [hrw] at hc

end Square

/-! ## `D⁺` components -/

section Components

variable {V : Type} {E : Type} [Fintype V] [DecidableEq V] (G : Multigraph V E)

/-- The induced graph on `D⁺_j(ϱ)` of a neutral density with an admissible center is connected:
every point is next to the centered ball, and a shortest path to the center stays in it. -/
theorem densityDomainPlus_induce_connected' (hG : G.toSimpleGraph.Connected) (ϱ : V → ℤ)
    (center : V) (hneutral : ∑ x, ϱ x = 0) (hcenter : G.IsDensityCenter ϱ center) :
    (G.toSimpleGraph.induce (G.densityDomainPlus ϱ center)).Connected := by
  classical
  have hdiam : 1 ≤ G.densityDiameter ϱ :=
    G.one_le_densityDiameter_of_neutral hG ϱ (fun h => hcenter.1 (by simp [h])) hneutral
  have hcenterD : center ∈ G.densityDomain ϱ center := by
    change G.toSimpleGraph.dist center center < 2 * G.densityDiameter ϱ
    rw [SimpleGraph.dist_self]
    omega
  have hcenterA : center ∈ G.densityDomainPlus ϱ center :=
    G.densityDomain_subset_densityDomainPlus ϱ center hcenterD
  have hreach (x : G.densityDomainPlus ϱ center) :
      (G.toSimpleGraph.induce (G.densityDomainPlus ϱ center)).Reachable x ⟨center, hcenterA⟩ := by
    obtain ⟨m, hmD, hxm⟩ := G.mem_densityDomainPlus.mp x.2
    have hmA : m ∈ G.densityDomainPlus ϱ center :=
      G.densityDomain_subset_densityDomainPlus ϱ center hmD
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist m center
    have hpSupport : ∀ z ∈ p.support, z ∈ G.densityDomainPlus ϱ center := by
      intro z hz
      have hlen := SimpleGraph.Walk.length_dropUntil_le_length p hz
      have hdist : G.toSimpleGraph.dist z center ≤ (p.dropUntil z hz).length :=
        SimpleGraph.dist_le (p.dropUntil z hz)
      have hzD : z ∈ G.densityDomain ϱ center := by
        change G.toSimpleGraph.dist z center < 2 * G.densityDiameter ϱ
        change G.toSimpleGraph.dist m center < 2 * G.densityDiameter ϱ at hmD
        omega
      exact G.densityDomain_subset_densityDomainPlus ϱ center hzD
    have hpath : (G.toSimpleGraph.induce (G.densityDomainPlus ϱ center)).Reachable
        ⟨m, hmA⟩ ⟨center, hcenterA⟩ := ⟨p.induce _ hpSupport⟩
    have hxm' : (G.toSimpleGraph.induce (G.densityDomainPlus ϱ center)).Reachable x ⟨m, hmA⟩ := by
      rcases hxm with hxm | hxm
      · have : x = ⟨m, hmA⟩ := Subtype.ext hxm
        rw [this]
      · exact (SimpleGraph.induce_adj.mpr hxm).reachable
    exact hxm'.trans hpath
  exact { preconnected := fun x y => (hreach x).trans (hreach y).symm,
          nonempty := ⟨⟨center, hcenterA⟩⟩ }

variable (N₁ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)

/-- A `D⁺` domain of a member density lies in one component of the union. -/
theorem densityDomainPlus_subset_component (hG : G.toSimpleGraph.Connected) {ϱ : V → ℤ}
    (hϱ : ϱ ∈ N₁) (hneutral : ∑ x, ϱ x = 0) (hcenter : G.IsDensityCenter ϱ (centerOf ϱ))
    {c : DensityPlusComponent G N₁ centerOf} {x : V}
    (hx : x ∈ G.densityDomainPlus ϱ (centerOf ϱ))
    (hxc : x ∈ densityPlusComponentVertices G N₁ centerOf c) :
    G.densityDomainPlus ϱ (centerOf ϱ) ⊆ densityPlusComponentVertices G N₁ centerOf c := by
  have hA := densityDomainPlus_induce_connected' G hG ϱ (centerOf ϱ) hneutral hcenter
  have hsub : G.densityDomainPlus ϱ (centerOf ϱ) ⊆ (densityPlusUnion G N₁ centerOf : Set V) :=
    fun y hy => (mem_densityPlusUnion G N₁ centerOf y).2 ⟨ϱ, hϱ, hy⟩
  intro y hy
  have hyU : y ∈ densityPlusUnion G N₁ centerOf := hsub hy
  have hxU : x ∈ densityPlusUnion G N₁ centerOf := hsub hx
  have hreach := (hA.preconnected ⟨x, hx⟩ ⟨y, hy⟩).map
    (G.toSimpleGraph.induceHomOfLE hsub).toHom
  obtain ⟨_, hxc'⟩ := (mem_densityPlusComponentVertices G N₁ centerOf c x).1 hxc
  have hcomp : (densityPlusInducedGraph G N₁ centerOf).connectedComponentMk ⟨y, hyU⟩ =
      (densityPlusInducedGraph G N₁ centerOf).connectedComponentMk ⟨x, hxU⟩ :=
    (SimpleGraph.ConnectedComponent.sound hreach).symm
  exact (mem_densityPlusComponentVertices G N₁ centerOf c y).2 ⟨hyU, hcomp.trans hxc'⟩

/-- Every component of the union has diameter at least one, when the member densities are
nonzero, neutral and have admissible centers. -/
theorem one_le_componentDiameter (hG : G.toSimpleGraph.Connected)
    (hN₁ : ∀ ϱ ∈ N₁, ϱ ≠ 0 ∧ ∑ x, ϱ x = 0 ∧ G.IsDensityCenter ϱ (centerOf ϱ))
    (c : DensityPlusComponent G N₁ centerOf) :
    1 ≤ densityPlusComponentDiameter G N₁ centerOf c := by
  obtain ⟨x, hx⟩ := componentVertices_nonempty G N₁ centerOf c
  obtain ⟨hxU, -⟩ := (mem_densityPlusComponentVertices G N₁ centerOf c x).1 hx
  obtain ⟨ϱ, hϱ, hxϱ⟩ := (mem_densityPlusUnion G N₁ centerOf x).1 hxU
  obtain ⟨hϱ0, hneutral, hcenter⟩ := hN₁ ϱ hϱ
  have hsub := densityDomainPlus_subset_component G N₁ centerOf hG hϱ hneutral hcenter hxϱ hx
  obtain ⟨hc0, y, hy0, hdy⟩ := hcenter
  have hcD := G.mem_densityDomainPlus_of_center hG hneutral ⟨hc0, y, hy0, hdy⟩ hc0
  have hyD := G.mem_densityDomainPlus_of_center hG hneutral ⟨hc0, y, hy0, hdy⟩ hy0
  have hd := dist_le_densityPlusComponentDiameter G N₁ centerOf c (hsub hcD) (hsub hyD)
  have h1 := G.one_le_densityDiameter_of_neutral hG ϱ hϱ0 hneutral
  omega

/-- A support point of `ϱ*` at which the root distance of a component vanishes lies in the
component; contrapositively, root separation keeps components off the support. -/
theorem componentRootDistance_le {ϱstar : V → ℤ} (c : DensityPlusComponent G N₁ centerOf)
    {x y : V} (hx : x ∈ densityPlusComponentVertices G N₁ centerOf c) (hy : ϱstar y ≠ 0) :
    densityPlusComponentRootDistance G N₁ centerOf c ϱstar ≤ G.toSimpleGraph.dist x y := by
  classical
  have hmem : G.toSimpleGraph.dist x y ∈
      ((densityPlusComponentVertices G N₁ centerOf c) ×ˢ
        (Finset.univ.filter fun y => ϱstar y ≠ 0)).image fun p => G.toSimpleGraph.dist p.1 p.2 :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, by simpa using hy⟩, rfl⟩
  unfold densityPlusComponentRootDistance
  simp only
  rw [dite_eq_left ⟨_, hmem⟩]
  exact Finset.min'_le _ _ hmem

end Components

end FroehlichSpencer.BKT.SpinWaves.P47

end
