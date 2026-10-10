/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import FroehlichSpencer.BKT.Generic.PinnedCharges.Geometry

/-! # Boundary-depth estimates for constituent cuts

The boundary depth of a subset can increase by at most the diameter of the
parent support. This file proves the Euclidean finite-support form used in the
cut-to-history analysis. -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

def siteCoordinateGap (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

private theorem gap_bounds (a b : ℕ) : a ≤ b + siteCoordinateGap a b ∧ b ≤ a + siteCoordinateGap a b := by
  by_cases h : a ≤ b
  · simp [siteCoordinateGap, h]
    omega
  · simp [siteCoordinateGap, h]
    omega

private theorem min4_le_min4_add {a b c d a' b' c' d' r : ℕ}
    (ha : a ≤ a' + r) (hb : b ≤ b' + r)
    (hc : c ≤ c' + r) (hd : d ≤ d' + r) :
    min a (min b (min c d)) ≤ min a' (min b' (min c' d')) + r := by
  have hinner : min b (min c d) ≤ min (b' + r) (min (c' + r) (d' + r)) := by
    exact min_le_min hb (min_le_min hc hd)
  have hmain : min a (min b (min c d)) ≤ min (a' + r) (min (b' + r) (min (c' + r) (d' + r))) := by
    exact min_le_min ha hinner
  simpa [Nat.add_min_add_right] using hmain

theorem siteBoundaryDepth_le_add_coordGap {L : ℕ} (x y : Site L) :
    siteBoundaryDepth x ≤ siteBoundaryDepth y +
      max (siteCoordinateGap x.1.val y.1.val) (siteCoordinateGap x.2.val y.2.val) := by
  let r := max (siteCoordinateGap x.1.val y.1.val) (siteCoordinateGap x.2.val y.2.val)
  have hxgap := gap_bounds x.1.val y.1.val
  have hygap := gap_bounds x.2.val y.2.val
  have hx1 : x.1.val ≤ y.1.val + r := (hxgap.1).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  have hx1' : y.1.val ≤ x.1.val + r := (hxgap.2).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  have hy1 : x.2.val ≤ y.2.val + r := (hygap.1).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
  have hy1' : y.2.val ≤ x.2.val + r := (hygap.2).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
  have h1 : x.1.val + 1 ≤ y.1.val + 1 + r := by omega
  have h2 : L - x.1.val ≤ L - y.1.val + r := by omega
  have h3 : x.2.val + 1 ≤ y.2.val + 1 + r := by omega
  have h4 : L - x.2.val ≤ L - y.2.val + r := by omega
  simpa [siteBoundaryDepth, r] using
    min4_le_min4_add h1 h2 h3 h4

private theorem siteCoordinateGap_comm (a b : ℕ) :
    siteCoordinateGap a b = siteCoordinateGap b a := by
  by_cases h : a ≤ b
  · by_cases h' : b ≤ a
    · have hab : a = b := Nat.le_antisymm h h'
      subst b
      simp [siteCoordinateGap]
    · simp [siteCoordinateGap, h, h']
  · have h' : b ≤ a := by omega
    simp [siteCoordinateGap, h, h']

private theorem siteCoordinateGap_cast (a b : ℕ) :
    (siteCoordinateGap a b : ℝ) = |(a : ℝ) - b| := by
  by_cases h : a ≤ b
  · rw [siteCoordinateGap, ite_eq_left h, Nat.cast_sub h]
    have hR : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [abs_of_nonpos (sub_nonpos.mpr hR)]
    ring
  · have h' : b ≤ a := by omega
    rw [siteCoordinateGap, ite_eq_right h, Nat.cast_sub h']
    have hR : (b : ℝ) ≤ a := by exact_mod_cast h'
    rw [abs_of_nonneg (sub_nonneg.mpr hR)]

theorem siteBoundaryDepth_lipschitz {L : ℕ} (x y : Site L) :
    |(siteBoundaryDepth x : ℝ) - siteBoundaryDepth y| ≤ euclideanSiteDistance x y := by
  let r := max (siteCoordinateGap x.1.val y.1.val) (siteCoordinateGap x.2.val y.2.val)
  have hxy := siteBoundaryDepth_le_add_coordGap x y
  have hyx := siteBoundaryDepth_le_add_coordGap y x
  have hNat : siteBoundaryDepth x ≤ siteBoundaryDepth y + r := by
    simpa [r] using hxy
  have hgap1 := siteCoordinateGap_comm y.1.val x.1.val
  have hgap2 := siteCoordinateGap_comm y.2.val x.2.val
  have hNat' : siteBoundaryDepth y ≤ siteBoundaryDepth x + r := by
    calc
      siteBoundaryDepth y ≤ siteBoundaryDepth x +
          max (siteCoordinateGap y.1.val x.1.val) (siteCoordinateGap y.2.val x.2.val) := hyx
      _ = siteBoundaryDepth x + r := by
        dsimp [r]
        rw [hgap1, hgap2]
  have hNatR : (siteBoundaryDepth x : ℝ) ≤ (siteBoundaryDepth y : ℝ) + (r : ℝ) := by
    exact_mod_cast hNat
  have hNatR' : (siteBoundaryDepth y : ℝ) ≤ (siteBoundaryDepth x : ℝ) + (r : ℝ) := by
    exact_mod_cast hNat'
  have hxyR : (siteBoundaryDepth x : ℝ) - siteBoundaryDepth y ≤ r := by
    linarith
  have hyxR : (siteBoundaryDepth y : ℝ) - siteBoundaryDepth x ≤ r := by
    linarith
  have hgap : (r : ℝ) = max |(x.1.val : ℝ) - y.1.val| |(x.2.val : ℝ) - y.2.val| := by
    simp [r, siteCoordinateGap_cast]
  have hmax : max |(x.1.val : ℝ) - y.1.val| |(x.2.val : ℝ) - y.2.val| ≤ euclideanSiteDistance x y := by
    dsimp [euclideanSiteDistance]
    apply max_le
    · calc
        |(x.1.val : ℝ) - y.1.val| = Real.sqrt (((x.1.val : ℝ) - y.1.val) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (((x.1.val : ℝ) - y.1.val) ^ 2 + ((x.2.val : ℝ) - y.2.val) ^ 2) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
    · calc
        |(x.2.val : ℝ) - y.2.val| = Real.sqrt (((x.2.val : ℝ) - y.2.val) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (((x.1.val : ℝ) - y.1.val) ^ 2 + ((x.2.val : ℝ) - y.2.val) ^ 2) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  have hmaxR : (r : ℝ) ≤ euclideanSiteDistance x y := by
    rw [hgap]
    exact hmax
  rw [abs_le]
  constructor
  · have h := hyxR.trans hmaxR
    linarith
  · exact hxyR.trans hmaxR

private theorem euclideanSiteDistance_comm {L : ℕ} (x y : Site L) :
    euclideanSiteDistance x y = euclideanSiteDistance y x := by
  unfold euclideanSiteDistance
  apply congrArg Real.sqrt
  ring

private theorem euclideanSiteDistance_le_euclideanSetDiameter {L : ℕ}
    (s : Finset (Site L)) {x y : Site L} (hx : x ∈ s) (hy : y ∈ s) :
    euclideanSiteDistance x y ≤ euclideanSetDiameter s := by
  have hsprod : (s.product s).Nonempty := ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  rw [euclideanSetDiameter, dite_eq_left hsprod]
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

theorem euclideanSetDiameter_subset_le {L : ℕ}
    (s t : Finset (Site L)) (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) : euclideanSetDiameter s ≤ euclideanSetDiameter t := by
  have hsprod : (s.product s).Nonempty := ⟨(hs.choose, hs.choose),
    Finset.mem_product.mpr ⟨hs.choose_spec, hs.choose_spec⟩⟩
  have htprod : (t.product t).Nonempty := ⟨(ht.choose, ht.choose),
    Finset.mem_product.mpr ⟨ht.choose_spec, ht.choose_spec⟩⟩
  rw [euclideanSetDiameter, dite_eq_left hsprod, euclideanSetDiameter, dite_eq_left htprod]
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  have hp' : p ∈ t.product t := Finset.mem_product.mpr
    ⟨hst (Finset.mem_product.mp hp).1, hst (Finset.mem_product.mp hp).2⟩
  exact Finset.le_max'
    ((t.product t).image (fun q : Site L × Site L => euclideanSiteDistance q.1 q.2))
    (euclideanSiteDistance p.1 p.2)
    (Finset.mem_image.mpr ⟨p, hp', rfl⟩)

theorem euclideanBoundaryDistance_subset_le {L : ℕ}
    (s t : Finset (Site L)) (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) :
    euclideanBoundaryDistance s ≤ euclideanBoundaryDistance t + euclideanSetDiameter t := by
  let f : Site L → ℝ := fun x => (siteBoundaryDepth x : ℝ)
  have hsImg : (s.image f).Nonempty := Finset.image_nonempty.mpr hs
  have htImg : (t.image f).Nonempty := Finset.image_nonempty.mpr ht
  obtain ⟨x, hx, hxval⟩ := Finset.mem_image.mp (Finset.min'_mem (t.image f) htImg)
  obtain ⟨y, hy, hyval⟩ := Finset.mem_image.mp (Finset.min'_mem (s.image f) hsImg)
  have hxt : x ∈ t := hx
  have hys : y ∈ s := hy
  have hyt : y ∈ t := hst hys
  have hdepth : f y ≤ f x + euclideanSiteDistance x y := by
    change (siteBoundaryDepth y : ℝ) ≤ (siteBoundaryDepth x : ℝ) +
      euclideanSiteDistance x y
    have h := siteBoundaryDepth_lipschitz y x
    rw [abs_le] at h
    rw [euclideanSiteDistance_comm] at h
    linarith [h.2]
  have hdiam := euclideanSiteDistance_le_euclideanSetDiameter t hxt hyt
  rw [euclideanBoundaryDistance, dite_eq_left hs, euclideanBoundaryDistance, dite_eq_left ht]
  rw [← hxval, ← hyval]
  linarith

theorem chargeBoundaryDistance_le_add_diameter_of_support_subset {L : ℕ}
    (child parent : ChargeDensity L) (hchild : child ≠ 0)
    (hsub : chargeSupport child ⊆ chargeSupport parent) :
    chargeBoundaryDistance child ≤ chargeBoundaryDistance parent + chargeEuclideanDiameter parent := by
  have hs : (chargeSupport child).Nonempty := chargeSupport_nonempty_of_ne_zero child hchild
  have ht : (chargeSupport parent).Nonempty := hs.mono hsub
  simpa [chargeBoundaryDistance, chargeEuclideanDiameter] using
    euclideanBoundaryDistance_subset_le (chargeSupport child) (chargeSupport parent) hs ht hsub

theorem chargeEuclideanDiameter_le_of_support_subset {L : ℕ}
    (child parent : ChargeDensity L) (hchild : child ≠ 0)
    (hsub : chargeSupport child ⊆ chargeSupport parent) :
    chargeEuclideanDiameter child ≤ chargeEuclideanDiameter parent := by
  have hs : (chargeSupport child).Nonempty := chargeSupport_nonempty_of_ne_zero child hchild
  have ht : (chargeSupport parent).Nonempty := hs.mono hsub
  exact euclideanSetDiameter_subset_le (chargeSupport child) (chargeSupport parent) hs ht hsub

theorem boundaryAdjustedSize_child_le_two_parent_of_both_charged {L : ℕ}
    (child parent : ChargeDensity L) (hchild : child ≠ 0)
    (hsub : chargeSupport child ⊆ chargeSupport parent)
    (hc : totalCharge child ≠ 0) (hp : totalCharge parent ≠ 0) :
    boundaryAdjustedSize child ≤ 2 * boundaryAdjustedSize parent := by
  rw [boundaryAdjustedSize_of_charged child hc,
      boundaryAdjustedSize_of_charged parent hp]
  have hdepth := chargeBoundaryDistance_le_add_diameter_of_support_subset
    child parent hchild hsub
  have hdiam := chargeEuclideanDiameter_le_of_support_subset child parent hchild hsub
  have hparent : parent ≠ 0 := by
    intro hzero
    subst parent
    obtain ⟨x, hx⟩ := chargeSupport_nonempty_of_ne_zero child hchild
    have hx' : x ∈ chargeSupport (0 : ChargeDensity L) := hsub hx
    simp [chargeSupport] at hx'
  have hδ : 0 ≤ chargeBoundaryDistance parent :=
    le_of_lt (chargeBoundaryDistance_pos_of_ne_zero parent hparent)
  have hd : 0 ≤ chargeEuclideanDiameter parent := by
    unfold chargeEuclideanDiameter euclideanSetDiameter
    have hp' : (chargeSupport parent).Nonempty := chargeSupport_nonempty_of_ne_zero parent hparent
    have hprod : (chargeSupport parent).product (chargeSupport parent) |>.Nonempty :=
      ⟨(hp'.choose, hp'.choose), Finset.mem_product.mpr ⟨hp'.choose_spec, hp'.choose_spec⟩⟩
    rw [dite_eq_left hprod]
    let d : Site L × Site L → ℝ := fun p => euclideanSiteDistance p.1 p.2
    have hmem : d (hp'.choose, hp'.choose) ∈
        Finset.image d ((chargeSupport parent).product (chargeSupport parent)) :=
      Finset.mem_image.mpr ⟨(hp'.choose, hp'.choose),
        Finset.mem_product.mpr ⟨hp'.choose_spec, hp'.choose_spec⟩, rfl⟩
    have hle := Finset.le_max' _ _ hmem
    have hzero : d (hp'.choose, hp'.choose) = 0 := by simp [d, euclideanSiteDistance]
    linarith
  have hmax : chargeBoundaryDistance parent + chargeEuclideanDiameter parent ≤
      2 * max (chargeBoundaryDistance parent) (chargeEuclideanDiameter parent) := by
    have hδ' := le_max_left (chargeBoundaryDistance parent) (chargeEuclideanDiameter parent)
    have hd' := le_max_right (chargeBoundaryDistance parent) (chargeEuclideanDiameter parent)
    linarith
  apply max_le
  · exact hdepth.trans hmax
  · exact hdiam.trans (by
      have hd' := le_max_right (chargeBoundaryDistance parent) (chargeEuclideanDiameter parent)
      linarith)

end FroehlichSpencer.BKT.Generic.PinnedCharges
