/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3Support

/-! # Component geometry for collapsed terminal profiles

This module isolates the metric consequences of the max-scale component estimate used in the
repaired support-control argument.  It proves the local neighborhood diameter and the parent and
inter-component separation estimates from a component-to-maximizer path bound.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The length metric of the nearest-neighbor square lattice, written in coordinates. -/
def profileA3GraphLength (x y : Site L) : ℝ :=
  |(x.1.val : ℝ) - y.1.val| + |(x.2.val : ℝ) - y.2.val|

theorem profileA3GraphLength_nonneg (x y : Site L) :
    0 ≤ profileA3GraphLength x y := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem profileA3GraphLength_comm (x y : Site L) :
    profileA3GraphLength x y = profileA3GraphLength y x := by
  simp [profileA3GraphLength, abs_sub_comm]

theorem euclideanSiteDistance_le_profileA3GraphLength (x y : Site L) :
    euclideanSiteDistance x y ≤ profileA3GraphLength x y := by
  let a : ℝ := |(x.1.val : ℝ) - y.1.val|
  let b : ℝ := |(x.2.val : ℝ) - y.2.val|
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hsqx : ((x.1.val : ℝ) - y.1.val) ^ 2 = a ^ 2 := by
    dsimp [a]
    exact (sq_abs _).symm
  have hsqy : ((x.2.val : ℝ) - y.2.val) ^ 2 = b ^ 2 := by
    dsimp [b]
    exact (sq_abs _).symm
  have hrad : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
  have htriangle : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  rw [euclideanSiteDistance, hsqx, hsqy]
  have hsqrt : Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b) ^ 2) :=
    Real.sqrt_le_sqrt htriangle
  have hab : Real.sqrt ((a + b) ^ 2) = a + b := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (add_nonneg ha hb)]
  simpa [profileA3GraphLength, a, b] using hsqrt.trans_eq hab

theorem profileA3GraphLength_triangle (x y z : Site L) :
    profileA3GraphLength x z ≤ profileA3GraphLength x y + profileA3GraphLength y z := by
  unfold profileA3GraphLength
  calc
    |(x.1.val : ℝ) - z.1.val| + |(x.2.val : ℝ) - z.2.val| ≤
        (|(x.1.val : ℝ) - y.1.val| + |(y.1.val : ℝ) - z.1.val|) +
          (|(x.2.val : ℝ) - y.2.val| + |(y.2.val : ℝ) - z.2.val|) :=
      add_le_add (abs_sub_le _ _ _) (abs_sub_le _ _ _)
    _ = (|(x.1.val : ℝ) - y.1.val| + |(x.2.val : ℝ) - y.2.val|) +
        (|(y.1.val : ℝ) - z.1.val| + |(y.2.val : ℝ) - z.2.val|) := by ring

/-- The coordinate length is at most `10/7` times Euclidean length.  The rational constant is
chosen so the neighborhood diameter estimate stays below `30 d` without decimal approximations. -/
theorem profileA3GraphLength_le_euclidean_mul
    (x y : Site L) :
    profileA3GraphLength x y ≤ (10 / 7 : ℝ) * euclideanSiteDistance x y := by
  let a : ℝ := |(x.1.val : ℝ) - y.1.val|
  let b : ℝ := |(x.2.val : ℝ) - y.2.val|
  let r := euclideanSiteDistance x y
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsqx : ((x.1.val : ℝ) - y.1.val) ^ 2 = a ^ 2 := by
    dsimp [a]
    exact (sq_abs _).symm
  have hsqy : ((x.2.val : ℝ) - y.2.val) ^ 2 = b ^ 2 := by
    dsimp [b]
    exact (sq_abs _).symm
  have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [r, euclideanSiteDistance]
    rw [hsqx, hsqy, Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  have hsum : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have hconst : (2 : ℝ) ≤ (10 / 7) ^ 2 := by norm_num
  have hsq : (a + b) ^ 2 ≤ ((10 / 7 : ℝ) * r) ^ 2 := by
    rw [mul_pow, hr2]
    nlinarith
  have hfinal := (sq_le_sq₀ (add_nonneg ha hb) (mul_nonneg (by norm_num) hr)).mp hsq
  simpa [profileA3GraphLength, a, r] using hfinal

/-- Every point of an expanded support neighborhood is within graph length `30 d` of every
other point of that neighborhood, for a nonzero neutral density of adjusted size at least one. -/
theorem profileA3_neutralNeighborhood_graph_diameter
    (σ : ChargeDensity L) (hd : 1 ≤ boundaryAdjustedSize σ)
    {x y : Site L}
    (hx : x ∈ profileA3NeutralNeighborhood σ)
    (hy : y ∈ profileA3NeutralNeighborhood σ) :
    profileA3GraphLength x y ≤ 30 * boundaryAdjustedSize σ := by
  let d := boundaryAdjustedSize σ
  let R := 8 * d + 2
  obtain ⟨a, ha, hax⟩ := (mem_boundaryEnergyNeighborhood_iff R (chargeSupport σ) x).mp (by
    simpa [profileA3NeutralNeighborhood, R, d] using hx)
  obtain ⟨b, hb, hby⟩ := (mem_boundaryEnergyNeighborhood_iff R (chargeSupport σ) y).mp (by
    simpa [profileA3NeutralNeighborhood, R, d] using hy)
  have hxa : euclideanSiteDistance x a ≤ R := by
    rw [siteDist_comm]
    exact hax
  have hyb : euclideanSiteDistance b y ≤ R := hby
  have hab : euclideanSiteDistance a b ≤ d := by
    exact (siteDist_le_diam ha hb).trans (chargeEuclideanDiameter_le_boundaryAdjustedSize σ)
  have hgraph : profileA3GraphLength x y ≤
      profileA3GraphLength x a + profileA3GraphLength a b + profileA3GraphLength b y := by
    calc
      profileA3GraphLength x y ≤ profileA3GraphLength x a + profileA3GraphLength a y :=
        profileA3GraphLength_triangle x a y
      _ ≤ profileA3GraphLength x a +
          (profileA3GraphLength a b + profileA3GraphLength b y) := by
        linarith [profileA3GraphLength_triangle a b y]
      _ = profileA3GraphLength x a + profileA3GraphLength a b +
          profileA3GraphLength b y := by ring
  have h1 := profileA3GraphLength_le_euclidean_mul x a
  have h2 := profileA3GraphLength_le_euclidean_mul a b
  have h3 := profileA3GraphLength_le_euclidean_mul b y
  have hbound : profileA3GraphLength x a + profileA3GraphLength a b +
      profileA3GraphLength b y ≤ (10 / 7 : ℝ) * (2 * R + d) := by
    nlinarith [h1, h2, h3, hxa, hab, hyb]
  dsimp [R, d] at hbound ⊢
  have hscale : (10 / 7 : ℝ) * (17 * boundaryAdjustedSize σ + 4) ≤
      30 * boundaryAdjustedSize σ := by nlinarith [hd]
  linarith

/-- The scale ratio in the max-scale induction: for `D≥1`, the high threshold `D/10` still
produces a separation larger than `40D` at Appendix-D parameters. -/
theorem profileA3_highThreshold_power_lower (D : ℝ) (hD : 1 ≤ D) :
    D / 100 ≤ (D / 10) ^ (7 / 4 : ℝ) := by
  have hDpow : D ≤ D ^ (7 / 4 : ℝ) :=
    Real.self_le_rpow_of_one_le hD (by norm_num)
  have hten : (10 : ℝ) ^ (7 / 4 : ℝ) < 100 := by
    calc
      (10 : ℝ) ^ (7 / 4 : ℝ) < (10 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ = 100 := by norm_num [Real.rpow_natCast]
  rw [Real.div_rpow (by positivity) (by norm_num) (7 / 4 : ℝ)]
  rw [div_le_div_iff₀ (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)]
  calc
    D * 10 ^ (7 / 4 : ℝ) ≤ D * 100 :=
      mul_le_mul_of_nonneg_left hten.le (by positivity)
    _ ≤ D ^ (7 / 4 : ℝ) * 100 :=
      mul_le_mul_of_nonneg_right hDpow (by norm_num)

/-- Two high neighborhoods cannot be joined through a low-only component whose diameter is at
most `4D`: the resulting support path would contradict pairwise Appendix-D separation. -/
theorem profileA3_high_pair_bridge_impossible
    (D d d' dist : ℝ) (hD : 1 ≤ D)
    (hd : D / 10 ≤ d) (hd' : D / 10 ≤ d')
    (hsep : (65536 : ℝ) * min d d' ^ (7 / 4 : ℝ) ≤ dist)
    (hbridge : dist ≤ 26 * D) : False := by
  have hmin : D / 10 ≤ min d d' := le_min hd hd'
  have hminpow : (D / 10) ^ (7 / 4 : ℝ) ≤ min d d' ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hmin (by norm_num)
  have hscale := profileA3_highThreshold_power_lower D hD
  have hlarge : 26 * D < (65536 : ℝ) * min d d' ^ (7 / 4 : ℝ) := by
    nlinarith [hminpow, hscale]
  linarith

/-- The abstract output of the finite max-scale induction: each point in a collapsed component is
within its graph diameter bound of a maximizing support. -/
def ProfileA3ComponentRootedAt {L : ℕ} (C : Finset (Site L))
    (σ : ChargeDensity L) (D : ℝ) : Prop :=
  (chargeSupport σ).Nonempty ∧
    boundaryAdjustedSize σ = D ∧
    ∀ x ∈ C, ∃ a ∈ chargeSupport σ,
      profileA3GraphLength x a ≤ 40 * D

/-- Gluing the unique maximum neighborhood to attached low-scale pieces gives the component's
`40D` diameter and root-distance bounds. The finite max-scale induction supplies this cover, the
`4D` low-piece diameters, and one attachment point for each low piece. -/
theorem profileA3_component_bounds_of_uniqueMax_decomposition
    (σ : ChargeDensity L) (hσ : σ ≠ 0)
    (C H : Finset (Site L)) (lowPieces : Finset (Finset (Site L)))
    (hH : H = profileA3NeutralNeighborhood σ)
    (hcover : C = H ∪ lowPieces.biUnion id)
    (hlowDiam : ∀ S ∈ lowPieces, ∀ x ∈ S, ∀ y ∈ S,
      profileA3GraphLength x y ≤ 4 * boundaryAdjustedSize σ)
    (hlowAttach : ∀ S ∈ lowPieces, ∃ z ∈ S, ∃ u ∈ H,
      profileA3GraphLength z u ≤ 1) :
    ProfileA3ComponentRootedAt C σ (boundaryAdjustedSize σ) ∧
      ∀ x ∈ C, ∀ y ∈ C,
        profileA3GraphLength x y ≤ 40 * boundaryAdjustedSize σ := by
  classical
  let D := boundaryAdjustedSize σ
  have hD : 1 ≤ D := one_le_boundaryAdjustedSize hσ
  have hsupp : (chargeSupport σ).Nonempty :=
    chargeSupport_nonempty_of_ne_zero σ hσ
  have hHroot : ∀ u ∈ H, ∃ a ∈ chargeSupport σ,
      profileA3GraphLength u a ≤ 30 * D := by
    intro u hu
    obtain ⟨a, ha⟩ := hsupp
    have haH : a ∈ H := by
      rw [hH]
      change a ∈ boundaryEnergyNeighborhood (8 * D + 2) (chargeSupport σ)
      rw [mem_boundaryEnergyNeighborhood_iff]
      exact ⟨a, ha, by simpa [euclideanSiteDistance] using (show (0 : ℝ) ≤ 8 * D + 2 by positivity)⟩
    refine ⟨a, ha, ?_⟩
    have h := profileA3_neutralNeighborhood_graph_diameter σ hD
      (by simpa [hH] using hu) (by simpa [hH] using haH)
    simpa [D] using h
  have hHdiam : ∀ x ∈ H, ∀ y ∈ H,
      profileA3GraphLength x y ≤ 30 * D := by
    intro x hx y hy
    have h := profileA3_neutralNeighborhood_graph_diameter σ hD
      (by simpa [hH] using hx) (by simpa [hH] using hy)
    simpa [D] using h
  have hnearH : ∀ x ∈ C, ∃ u ∈ H,
      profileA3GraphLength x u ≤ 4 * D + 1 := by
    intro x hx
    rw [hcover] at hx
    rcases Finset.mem_union.mp hx with hxH | hxLow
    · refine ⟨x, hxH, ?_⟩
      simp [profileA3GraphLength]
      nlinarith [hD]
    · rcases Finset.mem_biUnion.mp hxLow with ⟨S, hS, hxS⟩
      obtain ⟨z, hz, u, hu, hzu⟩ := hlowAttach S hS
      refine ⟨u, hu, ?_⟩
      calc
        profileA3GraphLength x u ≤ profileA3GraphLength x z +
            profileA3GraphLength z u := profileA3GraphLength_triangle x z u
        _ ≤ 4 * D + 1 := by
          have h := hlowDiam S hS x hxS z hz
          simpa [D] using add_le_add h hzu
  have hCne : C.Nonempty := by
    rw [hcover]
    obtain ⟨a, ha⟩ := hsupp
    refine ⟨a, Finset.mem_union.mpr (Or.inl ?_)⟩
    rw [hH]
    change a ∈ boundaryEnergyNeighborhood (8 * D + 2) (chargeSupport σ)
    rw [mem_boundaryEnergyNeighborhood_iff]
    exact ⟨a, ha, by simpa [euclideanSiteDistance] using (show (0 : ℝ) ≤ 8 * D + 2 by positivity)⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hsupp, rfl, ?_⟩
    intro x hx
    obtain ⟨u, hu, hxu⟩ := hnearH x hx
    obtain ⟨a, ha, hua⟩ := hHroot u hu
    refine ⟨a, ha, ?_⟩
    calc
      profileA3GraphLength x a ≤ profileA3GraphLength x u +
          profileA3GraphLength u a := profileA3GraphLength_triangle x u a
      _ ≤ (4 * D + 1) + 30 * D := add_le_add hxu hua
      _ ≤ 40 * D := by nlinarith [hD]
  · intro x hx y hy
    obtain ⟨u, hu, hxu⟩ := hnearH x hx
    obtain ⟨v, hv, hyv⟩ := hnearH y hy
    have huv := hHdiam u hu v hv
    have hyv' : profileA3GraphLength v y ≤ 4 * D + 1 := by
      rw [profileA3GraphLength_comm]
      exact hyv
    calc
      profileA3GraphLength x y ≤ profileA3GraphLength x u +
          profileA3GraphLength u v + profileA3GraphLength v y := by
        calc
          profileA3GraphLength x y ≤ profileA3GraphLength x u +
              profileA3GraphLength u y := profileA3GraphLength_triangle x u y
          _ ≤ profileA3GraphLength x u +
              (profileA3GraphLength u v + profileA3GraphLength v y) := by
            exact add_le_add_right (profileA3GraphLength_triangle u v y) _
          _ = profileA3GraphLength x u + profileA3GraphLength u v +
              profileA3GraphLength v y := by ring
      _ ≤ (4 * D + 1) + 30 * D + (4 * D + 1) := by
        nlinarith [hxu, huv, hyv']
      _ ≤ 40 * D := by nlinarith [hD]

/-- Parent separation after the component diameter is absorbed. -/
theorem profileA3_parent_component_separation
    (M α dρ D : ℝ) (ρ σ : ChargeDensity L)
    (K C : Finset (Site L))
    (hsep : M * min dρ D ^ α ≤ euclideanSetDistance (chargeSupport ρ) (chargeSupport σ))
    (hroot : ProfileA3ComponentRootedAt C σ D)
    (hK : K ⊆ chargeSupport ρ) (hKne : K.Nonempty) (hCne : C.Nonempty) :
    M * min dρ D ^ α - 40 * D ≤ euclideanSetDistance K C := by
  rcases hroot with ⟨hσne, hσD, hroot⟩
  apply le_setDist hKne hCne
  intro x hx y hy
  obtain ⟨a, ha, hya⟩ := hroot y hy
  have hset := setDist_le_siteDist (hK hx) ha
  have hbase : M * min dρ D ^ α ≤ euclideanSiteDistance x a := hsep.trans hset
  have hya' : euclideanSiteDistance y a ≤ 40 * D :=
    (euclideanSiteDistance_le_profileA3GraphLength y a).trans hya
  have htri := euclideanSiteDistance_triangle x y a
  linarith

/-- The parent-component separation becomes a linear path-budget bound when the parent scale
dominates the component scale. -/
theorem profileA3_parent_budget_from_separation
    (D dρ parentDistance P : ℝ)
    (hD : 1 ≤ D) (horder : D ≤ dρ)
    (hsep : (65536 : ℝ) * min dρ D ^ (7 / 4 : ℝ) - 40 * D ≤ parentDistance)
    (hpath : parentDistance ≤ P) :
    (65536 - 40 : ℝ) * D ≤ P := by
  have hmin : min dρ D = D := min_eq_right horder
  have hpow : D ≤ D ^ (7 / 4 : ℝ) :=
    Real.self_le_rpow_of_one_le hD (by norm_num)
  rw [hmin] at hsep
  nlinarith

/-- Inter-component separation after the max-scale component diameters are absorbed. -/
theorem profileA3_distinct_components_separation
    (M α D D' : ℝ) (σ τ : ChargeDensity L)
    (C C' : Finset (Site L))
    (hsep : M * min D D' ^ α ≤ euclideanSetDistance (chargeSupport σ) (chargeSupport τ))
    (hroot : ProfileA3ComponentRootedAt C σ D)
    (hroot' : ProfileA3ComponentRootedAt C' τ D')
    (hCne : C.Nonempty) (hC'ne : C'.Nonempty) :
    M * min D D' ^ α - 40 * (D + D') ≤ euclideanSetDistance C C' := by
  rcases hroot with ⟨hσne, hσD, hroot⟩
  rcases hroot' with ⟨hτne, hτD, hroot'⟩
  apply le_setDist hCne hC'ne
  intro x hx y hy
  obtain ⟨a, ha, hax⟩ := hroot x hx
  obtain ⟨b, hb, hby⟩ := hroot' y hy
  have hbase : M * min D D' ^ α ≤ euclideanSiteDistance a b :=
    hsep.trans (setDist_le_siteDist ha hb)
  have hxa : euclideanSiteDistance x a ≤ 40 * D := by
    exact (euclideanSiteDistance_le_profileA3GraphLength x a).trans hax
  have hyb : euclideanSiteDistance y b ≤ 40 * D' := by
    exact (euclideanSiteDistance_le_profileA3GraphLength y b).trans hby
  have htri₁ := euclideanSiteDistance_triangle a x b
  have htri₂ := euclideanSiteDistance_triangle x y b
  have hsym₁ := siteDist_comm a x
  have hyb' : euclideanSiteDistance b y ≤ 40 * D' := by
    have h := (euclideanSiteDistance_le_profileA3GraphLength y b).trans hby
    simpa [siteDist_comm] using h
  have hsym₂ := siteDist_comm y b
  have hxy : euclideanSiteDistance a b ≤ 40 * D + euclideanSiteDistance x y + 40 * D' := by
    calc
      euclideanSiteDistance a b ≤ euclideanSiteDistance a x + euclideanSiteDistance x b := htri₁
      _ ≤ euclideanSiteDistance a x + (euclideanSiteDistance x y + euclideanSiteDistance y b) := by
        nlinarith [htri₂]
      _ ≤ 40 * D + (euclideanSiteDistance x y + 40 * D') := by
        rw [hsym₁]
        nlinarith [hxa, hyb]
      _ = 40 * D + euclideanSiteDistance x y + 40 * D' := by ring
  linarith

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
