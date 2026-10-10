/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyOverlap
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRoutineLocal

/-! # Local geometry for the collapsed profile metric

This file records the elementary geometry of the neutral neighborhoods used by the
scale-`j` collapsed metric.  The component and path amortization are separated from
these local estimates: in particular, distinct neutral neighborhoods are allowed to
overlap.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The neutral neighborhood collapsed by the scale-`j` profile. -/
def profileA3NeutralNeighborhood (σ : ChargeDensity L) : Finset (Site L) :=
  boundaryEnergyNeighborhood (8 * boundaryAdjustedSize σ + 2) (chargeSupport σ)

/-- The quantitative collapsed-distance estimate sufficient for the scale-`j` ramp.
The factor `9/8` is the allowed savings margin in TW1G §3. -/
def ProfileA3CollapsedSupportControl (j : ℕ) (K : Finset (Site L))
    (d : Site L → ℝ) : Prop :=
  ∀ x, d x < (2 : ℝ) ^ (j + 1) →
    euclideanSetDistance K {x} ≤ (9 / 8 : ℝ) * d x

/-- The neighborhood has diameter at most `17 d + 4`: two radii and the support diameter. -/
theorem profileA3_neutralNeighborhood_diameter (σ : ChargeDensity L)
    (hσ : σ ≠ 0) :
    euclideanSetDiameter (profileA3NeutralNeighborhood σ) ≤
      17 * boundaryAdjustedSize σ + 4 := by
  classical
  let S := chargeSupport σ
  let E := profileA3NeutralNeighborhood σ
  let r := 8 * boundaryAdjustedSize σ + 2
  have hS : S.Nonempty := chargeSupport_nonempty_of_ne_zero σ hσ
  have hsize0 : 0 ≤ boundaryAdjustedSize σ :=
    (SelectionG.diam_nonneg (chargeSupport σ)).trans
      (chargeEuclideanDiameter_le_boundaryAdjustedSize σ)
  have hE : E.Nonempty := by
    obtain ⟨x, hx⟩ := hS
    refine ⟨x, ?_⟩
    change x ∈ boundaryEnergyNeighborhood (8 * boundaryAdjustedSize σ + 2)
      (chargeSupport σ)
    rw [mem_boundaryEnergyNeighborhood_iff]
    refine ⟨x, hx, ?_⟩
    have hr : 0 ≤ 8 * boundaryAdjustedSize σ + 2 := by positivity
    simpa [euclideanSiteDistance] using hr
  have hpair (x y : Site L) (hx : x ∈ E) (hy : y ∈ E) :
      euclideanSiteDistance x y ≤ 17 * boundaryAdjustedSize σ + 4 := by
    obtain ⟨a, ha, hax⟩ := (mem_boundaryEnergyNeighborhood_iff r S x).mp (by
      simpa [E, r, profileA3NeutralNeighborhood] using hx)
    obtain ⟨b, hb, hby⟩ := (mem_boundaryEnergyNeighborhood_iff r S y).mp (by
      simpa [E, r, profileA3NeutralNeighborhood] using hy)
    have hxa : euclideanSiteDistance x a ≤ r := by
      rw [siteDist_comm]
      exact hax
    have hyb : euclideanSiteDistance b y ≤ r := hby
    have hab : euclideanSiteDistance a b ≤ chargeEuclideanDiameter σ := by
      change euclideanSiteDistance a b ≤ euclideanSetDiameter S
      exact siteDist_le_diam ha hb
    have htri₁ := euclideanSiteDistance_triangle x a y
    have htri₂ := euclideanSiteDistance_triangle a b y
    have hxy : euclideanSiteDistance x y ≤ r + chargeEuclideanDiameter σ + r := by
      calc
        euclideanSiteDistance x y ≤ euclideanSiteDistance x a + euclideanSiteDistance a y := htri₁
        _ ≤ r + (euclideanSiteDistance a b + euclideanSiteDistance b y) := by
          nlinarith [hxa, htri₂]
        _ ≤ r + (chargeEuclideanDiameter σ + r) := by nlinarith [hab, hyb]
        _ = r + chargeEuclideanDiameter σ + r := by ring
    have hsize : chargeEuclideanDiameter σ ≤ boundaryAdjustedSize σ := by
      unfold boundaryAdjustedSize
      split_ifs
      · rfl
      · exact le_max_right _ _
    dsimp [r] at hxy
    nlinarith [hxy, hsize]
  have hprod : (E.product E).Nonempty := by
    obtain ⟨x, hx⟩ := hE
    exact ⟨(x, x), Finset.mem_product.mpr ⟨hx, hx⟩⟩
  unfold euclideanSetDiameter
  rw [dite_eq_left hprod]
  apply Finset.max'_le
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact hpair p.1 p.2 (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2

/-- Expanding both sets by radii can reduce their separation by at most the sum of radii. -/
theorem profileA3_neighborhood_distance_add_radii
    (s t : Finset (Site L)) (r q : ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hr : 0 ≤ r) (hq : 0 ≤ q) :
    euclideanSetDistance s t ≤
      euclideanSetDistance (boundaryEnergyNeighborhood r s)
        (boundaryEnergyNeighborhood q t) + r + q := by
  classical
  let Es := boundaryEnergyNeighborhood r s
  let Et := boundaryEnergyNeighborhood q t
  have hEs : Es.Nonempty := by
    obtain ⟨x, hx⟩ := hs
    refine ⟨x, ?_⟩
    rw [mem_boundaryEnergyNeighborhood_iff]
    exact ⟨x, hx, by simpa [euclideanSiteDistance] using hr⟩
  have hEt : Et.Nonempty := by
    obtain ⟨y, hy⟩ := ht
    refine ⟨y, ?_⟩
    rw [mem_boundaryEnergyNeighborhood_iff]
    exact ⟨y, hy, by simpa [euclideanSiteDistance] using hq⟩
  have hpairs {x y : Site L} (hx : x ∈ Es) (hy : y ∈ Et) :
      euclideanSetDistance s t ≤ euclideanSiteDistance x y + r + q := by
    obtain ⟨a, ha, hax⟩ := (mem_boundaryEnergyNeighborhood_iff r s x).mp (by
      simpa [Es] using hx)
    obtain ⟨b, hb, hby⟩ := (mem_boundaryEnergyNeighborhood_iff q t y).mp (by
      simpa [Et] using hy)
    have hbase : euclideanSetDistance s t ≤ euclideanSiteDistance a b :=
      setDist_le_siteDist ha hb
    have hyb : euclideanSiteDistance y b ≤ q := by
      rw [siteDist_comm]
      exact hby
    have hxy : euclideanSiteDistance a b ≤ r + euclideanSiteDistance x y + q := by
      calc
        euclideanSiteDistance a b ≤ euclideanSiteDistance a x + euclideanSiteDistance x b :=
          euclideanSiteDistance_triangle a x b
        _ ≤ r + (euclideanSiteDistance x y + euclideanSiteDistance y b) := by
          have h := euclideanSiteDistance_triangle x y b
          nlinarith [hax, h]
        _ ≤ r + (euclideanSiteDistance x y + q) := by nlinarith [hyb]
        _ = r + euclideanSiteDistance x y + q := by ring
    linarith
  have hprod : (Es.product Et).Nonempty := by
    obtain ⟨x, hx⟩ := hEs
    obtain ⟨y, hy⟩ := hEt
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  let D := (Es.product Et).image fun p : Site L × Site L => euclideanSiteDistance p.1 p.2
  have hD : D.Nonempty := Finset.image_nonempty.mpr hprod
  obtain ⟨p, hp, hvalue⟩ := Finset.mem_image.mp (Finset.min'_mem D hD)
  have hdist : euclideanSetDistance Es Et = euclideanSiteDistance p.1 p.2 := by
    unfold euclideanSetDistance
    rw [dite_eq_left hprod]
    simpa [D] using hvalue.symm
  have h := hpairs (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
  rw [← hdist] at h
  exact h

/-- Appendix-D separation survives the neighborhood expansion with its exact radius loss. -/
theorem profileA3_separated_neighborhoods
    (M α : ℝ) (σ τ : ChargeDensity L) (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    (hsep : M * min (boundaryAdjustedSize σ) (boundaryAdjustedSize τ) ^ α ≤
      euclideanSetDistance (chargeSupport σ) (chargeSupport τ)) :
    M * min (boundaryAdjustedSize σ) (boundaryAdjustedSize τ) ^ α ≤
      euclideanSetDistance (profileA3NeutralNeighborhood σ)
        (profileA3NeutralNeighborhood τ) +
        (8 * boundaryAdjustedSize σ + 2) + (8 * boundaryAdjustedSize τ + 2) := by
  have hσsup : (chargeSupport σ).Nonempty := chargeSupport_nonempty_of_ne_zero σ hσ
  have hτsup : (chargeSupport τ).Nonempty := chargeSupport_nonempty_of_ne_zero τ hτ
  have hradσ : 0 ≤ 8 * boundaryAdjustedSize σ + 2 := by
    have h := (SelectionG.diam_nonneg (chargeSupport σ)).trans
      (chargeEuclideanDiameter_le_boundaryAdjustedSize σ)
    positivity
  have hradτ : 0 ≤ 8 * boundaryAdjustedSize τ + 2 := by
    have h := (SelectionG.diam_nonneg (chargeSupport τ)).trans
      (chargeEuclideanDiameter_le_boundaryAdjustedSize τ)
    positivity
  have hdist := profileA3_neighborhood_distance_add_radii
    (chargeSupport σ) (chargeSupport τ) (8 * boundaryAdjustedSize σ + 2)
    (8 * boundaryAdjustedSize τ + 2) hσsup hτsup hradσ hradτ
  unfold profileA3NeutralNeighborhood
  linarith

/-- If a neutral neighborhood meets a Euclidean ball of radius `R` about a parent support,
Appendix-D separation bounds its scale by the corresponding power threshold. -/
theorem profileA3_near_neutral_scale_bound
    (M α R dσ : ℝ) (hα : 1 ≤ α) (hdσ : 1 ≤ dσ)
    (hsep : M * dσ ^ α ≤ R + 8 * dσ + 2) :
    (M - 10) * dσ ^ α ≤ R := by
  have hpow : dσ ≤ dσ ^ α := by
    calc
      dσ = dσ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ dσ ^ α :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hα
  have hten : 8 * dσ + 2 ≤ 10 * dσ ^ α := by
    nlinarith [hpow]
  linarith

/-- A small neutral density whose expanded neighborhood reaches the `R`-ball
about a separated parent has scale at most the Appendix-D power threshold.
This is the non-circular local input needed before any collapsed-path
amortization: only ordinary Euclidean distance is used in the hypothesis. -/
theorem profileA3_nearby_neutral_scale_bound
    (M α R : ℝ) (F : Finset (ChargeDensity L)) (ρ σ : ChargeDensity L)
    (K : Finset (Site L))
    (hF : IsBoundarySeparated M α F) (hρ : ρ ∈ F) (hσ : σ ∈ F)
    (hne : ρ ≠ σ) (hσ0 : σ ≠ 0)
    (hK : K ⊆ chargeSupport ρ)
    (horder : boundaryAdjustedSize σ ≤ boundaryAdjustedSize ρ)
    (hα : 1 ≤ α)
    (hnear : (profileA3NeutralNeighborhood σ ∩
      boundaryEnergyNeighborhood R K).Nonempty) :
    (M - 10) * boundaryAdjustedSize σ ^ α ≤ R := by
  obtain ⟨x, hx⟩ := hnear
  obtain ⟨a, ha, hax⟩ := (mem_boundaryEnergyNeighborhood_iff
    (8 * boundaryAdjustedSize σ + 2) (chargeSupport σ) x).mp (by
      simpa [profileA3NeutralNeighborhood] using (Finset.mem_inter.mp hx).1)
  obtain ⟨b, hb, hbx⟩ := (mem_boundaryEnergyNeighborhood_iff R
    K x).mp (Finset.mem_inter.mp hx).2
  have hdσ : 1 ≤ boundaryAdjustedSize σ :=
    one_le_boundaryAdjustedSize (ρ := σ) hσ0
  have hsym : euclideanSiteDistance x b = euclideanSiteDistance b x := siteDist_comm _ _
  have hab : euclideanSiteDistance a b ≤
      (8 * boundaryAdjustedSize σ + 2) + R := by
    calc
      euclideanSiteDistance a b ≤ euclideanSiteDistance a x + euclideanSiteDistance x b :=
        euclideanSiteDistance_triangle a x b
      _ ≤ (8 * boundaryAdjustedSize σ + 2) + R := by
        rw [hsym]
        nlinarith [hax, hbx]
  have hdist : euclideanSetDistance (chargeSupport ρ) (chargeSupport σ) ≤
      (8 * boundaryAdjustedSize σ + 2) + R := by
    rw [setDist_comm]
    exact (setDist_le_siteDist ha (hK hb)).trans hab
  have hsep := hF ρ hρ σ hσ hne
  rw [min_eq_right horder] at hsep
  have hpow := profileA3_near_neutral_scale_bound M α R
    (boundaryAdjustedSize σ) hα hdσ (by linarith [hsep, hdist])
  exact hpow

/-- The ramp's strict support threshold is `3·2^(j-1)`.  Once the collapsed
distance has the quantitative support-control estimate from §3, this support
and every edge with nonzero ramp gradient lie in the Euclidean
`2^(j+1)`-neighborhood of the selected cluster. -/
theorem profileA3_ramp_support_in_two_scale_neighborhood
    (j : ℕ) (K : Finset (Site L)) (d : Site L → ℝ)
    (hcontrol : ProfileA3CollapsedSupportControl j K d)
    (hj : 1 ≤ j)
    {x : Site L}
    (hx : d x < (3 : ℝ) * (2 : ℝ) ^ (j - 1)) :
    euclideanSetDistance K {x} ≤ (2 : ℝ) ^ (j + 1) := by
  have hpow : 0 < (2 : ℝ) ^ (j - 1) := pow_pos (by norm_num) _
  have hexp : j - 1 + 2 = j + 1 := by omega
  have hthreshold : (3 : ℝ) * (2 : ℝ) ^ (j - 1) < (2 : ℝ) ^ (j + 1) := by
    rw [← hexp, pow_add]
    norm_num
    nlinarith
  have hdx : d x < (2 : ℝ) ^ (j + 1) := lt_trans hx hthreshold
  calc
    euclideanSetDistance K {x} ≤ (9 / 8 : ℝ) * d x := hcontrol x hdx
    _ ≤ (2 : ℝ) ^ (j + 1) := by
      have hpow0 : 0 ≤ (2 : ℝ) ^ (j - 1) := by positivity
      have hdouble : (2 : ℝ) ^ (j + 1) = 4 * (2 : ℝ) ^ (j - 1) := by
        rw [← hexp, pow_add]
        norm_num
        ring
      rw [hdouble]
      nlinarith [hx, hpow0]

/-- A point that is Euclidean-farther than the quantitative control radius
cannot lie at collapsed distance below `2^(j+1)`. -/
theorem profileA3_far_site_collapsed_distance_lower_bound
    (j : ℕ) (K : Finset (Site L)) (d : Site L → ℝ) (R : ℝ)
    (hcontrol : ProfileA3CollapsedSupportControl j K d)
    {x : Site L}
    (hfar : R ≤ euclideanSetDistance K {x})
    (hR : (9 / 8 : ℝ) * (2 : ℝ) ^ (j + 1) < R) :
    (2 : ℝ) ^ (j + 1) ≤ d x := by
  by_contra h
  have hd : d x < (2 : ℝ) ^ (j + 1) := lt_of_not_ge h
  have hc := hcontrol x hd
  have hp : (9 / 8 : ℝ) * d x ≤ (9 / 8 : ℝ) * (2 : ℝ) ^ (j + 1) := by
    exact mul_le_mul_of_nonneg_left (le_of_lt hd) (by norm_num)
  linarith

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
