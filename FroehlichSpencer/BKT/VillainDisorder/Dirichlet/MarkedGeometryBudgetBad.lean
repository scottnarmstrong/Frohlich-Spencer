/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryProxyCut
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileBCombinatorics
import Mathlib.Tactic

/-!
# The bad selected squares under the charged half of isolation (D2G3b)

`badSelectedBound_proof` bounds the selected squares with neutral restriction ("bad" squares) of a
comb-terminal density by its `ℓ¹` norm.

The bound uses comb-terminal geometry at one point only:
a selected square whose restriction has diameter at most `2^j` is charged
(`selectedRestriction_charged_of_diameter_le_scale`).

This file repeats the laminar-family argument under that hypothesis; the rooted marked
proxy has it (`hasFarConstituentCharge_rootedMarkedProxy`).

* **`badSelectedSum_le_card_of_far`**: `|bad selected squares| ≤ |supp ϱ|faces|`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer.FarCharge

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.VillainDisorder

variable {L : ℕ}

/-- A child of a selected square of side `2^j` with diameter at most `2^j` is boundary-far. -/
theorem far_of_scaleBoundaryMargin (j : ℕ) {child : ChargeDensity L} {s : Finset (Site L)}
    (hsub : chargeSupport child ⊆ s) (hne : (chargeSupport child).Nonempty)
    (hmargin : scaleBoundaryMargin j ≤ euclideanBoundaryDistance s)
    (hdiam : chargeEuclideanDiameter child ≤ (2 : ℝ) ^ j) :
    chargeEuclideanDiameter child <
      (chargeCoverScale : ℝ) * chargeBoundaryDistance child ^ chargeCoverExponent := by
  have hb : (2 : ℝ) ^ (j + 2) ≤ chargeBoundaryDistance child := by
    have h1 : scaleBoundaryMargin j = (2 : ℝ) ^ (j + 2) := rfl
    rw [← h1]
    exact hmargin.trans (Dirichlet.euclideanBoundaryDistance_anti hne hsub)
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 2) := one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ) ^ (j + 2) ≤ chargeBoundaryDistance child ^ chargeCoverExponent := by
    calc (2 : ℝ) ^ (j + 2) = ((2 : ℝ) ^ (j + 2)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((2 : ℝ) ^ (j + 2)) ^ chargeCoverExponent :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num [chargeCoverExponent])
      _ ≤ chargeBoundaryDistance child ^ chargeCoverExponent :=
          Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hb (by norm_num [chargeCoverExponent])
  have hM : (1 : ℝ) ≤ (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
  have hj : (2 : ℝ) ^ j < (2 : ℝ) ^ (j + 2) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hpos : 0 ≤ chargeBoundaryDistance child ^ chargeCoverExponent :=
    Real.rpow_nonneg ((pow_nonneg (by norm_num) _).trans hb) _
  nlinarith

/-- At a selected scale, if the restricted cluster's diameter is no larger than the nominal side,
the charged half of Appendix D isolation on boundary-far constituents makes its total charge
nonzero (the selected square is boundary-far). -/
theorem selectedRestriction_charged_of_far
    (j : ℕ) (ρ : ChargeDensity L)
    (hfar : Dirichlet.HasFarConstituentCharge (chargeCoverScale : ℝ) chargeCoverExponent ρ)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (s : Finset (Site L))
    (hs : s ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ C)
    (hdiam : chargeEuclideanDiameter (chargeRestriction ρ s) ≤ (2 : ℝ) ^ j) :
    totalCharge (chargeRestriction ρ s) ≠ 0 := by
  classical
  let child := chargeRestriction ρ s
  have hsC : s ∈ C := pinnedPPrime_mem_of_minimumCover
    chargeCoverScale chargeCoverExponent j ρ C hC hs |>.1
  have hchildconst : IsConstituent ρ child := by
    simpa [child] using boundaryEnergy_squareRestriction_isConstituent j ρ C hC hsC
  by_cases hsingle : C.card = 1
  · have hkeep : totalCharge ρ ≠ 0 ∧
        singletonBoundaryMargin j ≤ chargeBoundaryDistance ρ := by
      by_contra hkeep
      have hempty := pinnedPPrime_eq_empty_of_singleton_exception_fails
        (chargeCoverScale : ℝ) chargeCoverExponent j ρ C hsingle hkeep
      rw [hempty] at hs
      exact Finset.notMem_empty _ hs
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsingle
    have hus : s = u := by simpa [hu] using hsC
    have hsupport : chargeSupport ρ ⊆ s := by
      intro x hx
      obtain ⟨t, ht, hxt⟩ := hC.1.2 x hx
      have htu : t = u := by simpa [hu] using ht
      simpa [hus, htu] using hxt
    have hsame : child = ρ := by
      funext x
      by_cases hxs : x ∈ s
      · simp [child, chargeRestriction, hxs]
      · have hxzero : ρ x = 0 := by
          by_contra hxne
          exact hxs (hsupport (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne⟩))
        simp [child, chargeRestriction, hxs, hxzero]
    change totalCharge child ≠ 0
    rw [hsame]
    exact hkeep.1
  · have hsdata := (mem_pinnedPPrime_of_cover_card_ne_one
        (chargeCoverScale : ℝ) chargeCoverExponent j ρ C hsingle s).1 hs
    rcases hsdata with ⟨hsC, hsep, hboundary⟩
    obtain ⟨x₀, hx₀ρ, hx₀s, _⟩ :=
      minimumCover_square_has_private_support_site j ρ C hC hsC
    let residual : ChargeDensity L := fun x => ρ x - child x
    have hchildne : child ≠ 0 := hchildconst.1
    have hresne : residual ≠ 0 := by
      obtain ⟨t, ht, hts⟩ : ∃ t ∈ C, t ≠ s := by
        by_contra h
        have hall : ∀ t ∈ C, t = s := by
          intro u hu
          by_contra hne
          exact h ⟨u, hu, hne⟩
        have hcard : C.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
          (hall a ha).trans (hall b hb).symm
        have hpos : 0 < C.card := Finset.card_pos.mpr ⟨s, hsC⟩
        omega
      obtain ⟨x₁, hx₁ρ, hx₁t, hprivate₁⟩ :=
        minimumCover_square_has_private_support_site j ρ C hC ht
      have hx₁s : x₁ ∉ s := by
        intro hx
        exact hprivate₁ s hsC (Ne.symm hts) hx
      have hρx₁ : ρ x₁ ≠ 0 := (Finset.mem_filter.mp hx₁ρ).2
      have hval : residual x₁ ≠ 0 := by
        simpa [residual, child, chargeRestriction, hx₁s] using hρx₁
      exact fun hz => hval (congrFun hz x₁)
    have hresOutside : ∀ x ∈ chargeSupport residual, x ∉ s := by
      intro x hx hxs
      have hxzero : residual x = 0 := by simp [residual, child, chargeRestriction, hxs]
      exact (Finset.mem_filter.mp hx).2 hxzero
    have hpairEvery {x y : Site L} (hx : x ∈ chargeSupport child)
        (hy : y ∈ chargeSupport residual) :
        2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ j) ^ chargeCoverExponent ≤
          euclideanSiteDistance x y := by
      have hxs : x ∈ s := (mem_chargeSupport_restriction_iff ρ s x).mp hx |>.1
      have hys : y ∉ s := hresOutside y hy
      have hρy : ρ y ≠ 0 := by
        simpa [residual, child, chargeRestriction, hys] using
          (Finset.mem_filter.mp hy).2
      obtain ⟨t, ht, hyt⟩ := hC.1.2 y
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρy⟩)
      have hts : t ≠ s := by
        intro h
        subst t
        exact hys hyt
      have hscale : ((2 : ℝ) ^ j) ^ chargeCoverExponent =
          (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) := by
        calc
          ((2 : ℝ) ^ j) ^ chargeCoverExponent =
              (2 : ℝ) ^ ((j : ℝ) * chargeCoverExponent) := by
                rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
          _ = (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) :=
            congrArg (fun z : ℝ => (2 : ℝ) ^ z) (by ring)
      calc
        2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ j) ^ chargeCoverExponent =
            2 * (chargeCoverScale : ℝ) *
              (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) := by rw [hscale]
        _ ≤ euclideanSetDistance s t := hsep t ht hts
        _ ≤ euclideanSiteDistance x y := SelectionG.setDist_le_siteDist hxs hyt
    have hdist : 2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ j) ^ chargeCoverExponent ≤
        euclideanSetDistance (chargeSupport child) (chargeSupport residual) :=
      SelectionG.le_setDist (chargeSupport_nonempty_of_ne_zero child hchildne)
        (chargeSupport_nonempty_of_ne_zero residual hresne) (fun x hx y hy => hpairEvery hx hy)
    have hdiamPow : chargeEuclideanDiameter child ^ chargeCoverExponent ≤
        ((2 : ℝ) ^ j) ^ chargeCoverExponent :=
      Real.rpow_le_rpow (SelectionG.diam_nonneg _) hdiam (by norm_num [chargeCoverExponent])
    have htrigger : 2 * (chargeCoverScale : ℝ) *
        chargeEuclideanDiameter child ^ chargeCoverExponent ≤
        euclideanSetDistance (chargeSupport child) (chargeSupport residual) := by
      calc
        2 * (chargeCoverScale : ℝ) * chargeEuclideanDiameter child ^ chargeCoverExponent ≤
            2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ j) ^ chargeCoverExponent :=
          mul_le_mul_of_nonneg_left hdiamPow (by positivity)
        _ ≤ euclideanSetDistance (chargeSupport child) (chargeSupport residual) := hdist
    have hsub : chargeSupport child ⊆ s := fun x hx =>
      ((mem_chargeSupport_restriction_iff ρ s x).mp hx).1
    exact hfar child hchildconst (by simpa [residual] using htrigger)
      (far_of_scaleBoundaryMargin j hsub (chargeSupport_nonempty_of_ne_zero child hchildne)
        hboundary hdiam)


/-- If a fine bad cluster meets a coarser bad cluster, it is contained in the coarser one. -/
theorem badSelectedCluster_overlap_nested_far (ϱ : RotatorDualFace L → ℤ)
    (j k : ℕ) (hjk : j ≤ k)
    (s t : Finset (Site L)) (hs : s ∈ badSelectedSquares ϱ j)
    (ht : t ∈ badSelectedSquares ϱ k)
    (hoverlap : (chargeSupport (chargeRestriction (siteRestrict ϱ) s) ∩
      chargeSupport (chargeRestriction (siteRestrict ϱ) t)).Nonempty) :
    chargeSupport (chargeRestriction (siteRestrict ϱ) s) ⊆
      chargeSupport (chargeRestriction (siteRestrict ϱ) t) := by
  classical
  let ρ := siteRestrict ϱ
  let C := boundaryEntropyMinimumCover ρ k
  have hC : IsMinimumSquareCover .free L k ρ C :=
    boundaryEntropyMinimumCover_isMinimum ρ k
  have htSelected : t ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent k ρ C := by
    simpa [C, selectedSquares] using (Finset.mem_filter.mp ht).1
  rcases badSelectedCluster_data ϱ k ht with
    ⟨hchildne, _hneutral, _hsub, _hcard, _hdiam, hCne⟩
  have htData := (mem_pinnedPPrime_of_cover_card_ne_one
    (chargeCoverScale : ℝ) chargeCoverExponent k ρ C hCne t).1 htSelected
  rcases htData with ⟨htC, hsep, _hboundary⟩
  obtain ⟨y, hy⟩ := hoverlap
  have hyS : y ∈ chargeSupport (chargeRestriction ρ s) :=
    (Finset.mem_inter.mp hy).1
  have hyT : y ∈ chargeSupport (chargeRestriction ρ t) :=
    (Finset.mem_inter.mp hy).2
  have hdiamS := (badSelectedCluster_data ϱ j hs).2.2.2.2.1
  have hsChildSub : chargeSupport (chargeRestriction ρ s) ⊆ chargeSupport ρ :=
    (badSelectedCluster_data ϱ j hs).2.2.1
  have htChildSub : chargeSupport (chargeRestriction ρ t) ⊆ chargeSupport ρ :=
    (badSelectedCluster_data ϱ k ht).2.2.1
  intro x hx
  by_contra hxT
  have hxρ : x ∈ chargeSupport ρ := hsChildSub hx
  have hxNotSquare : x ∉ t := by
    intro hxt
    exact hxT ((mem_chargeSupport_restriction_iff ρ t x).2 ⟨hxt, hxρ⟩)
  obtain ⟨u, hu, hxu⟩ := hC.1.2 x hxρ
  have hne : u ≠ t := by
    intro hut
    subst u
    exact hxNotSquare hxu
  have hySquare : y ∈ t :=
    (mem_chargeSupport_restriction_iff ρ t y).mp hyT |>.1
  have hyFine : y ∈ chargeSupport (chargeRestriction ρ s) := hyS
  have hsep' := hsep u hu hne
  have hscale : ((2 : ℝ) ^ k) ^ chargeCoverExponent =
      (2 : ℝ) ^ (chargeCoverExponent * (k : ℝ)) := by
    calc
      ((2 : ℝ) ^ k) ^ chargeCoverExponent =
          (2 : ℝ) ^ ((k : ℝ) * chargeCoverExponent) := by
            rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      _ = (2 : ℝ) ^ (chargeCoverExponent * (k : ℝ)) :=
        congrArg (fun z : ℝ => (2 : ℝ) ^ z) (by ring)
  rw [← hscale] at hsep'
  have hset := SelectionG.setDist_le_siteDist hySquare hxu
  have hsite := SelectionG.siteDist_le_diam hyFine hx
  have hjkPow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hjk
  have hbase : 1 ≤ (2 : ℝ) ^ k :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hpow : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ chargeCoverExponent := by
    calc
      (2 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((2 : ℝ) ^ k) ^ chargeCoverExponent :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num [chargeCoverExponent])
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hradius : Real.sqrt 2 * (2 : ℝ) ^ j <
      2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent := by
    calc
      Real.sqrt 2 * (2 : ℝ) ^ j ≤ Real.sqrt 2 * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hjkPow (Real.sqrt_nonneg _)
      _ < 2 * (2 : ℝ) ^ k := mul_lt_mul_of_pos_right hsqrt (by positivity)
      _ ≤ 2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent := by
        have hM : (1 : ℝ) ≤ (chargeCoverScale : ℝ) := by
          norm_num [chargeCoverScale]
        calc
          2 * (2 : ℝ) ^ k ≤
              2 * (chargeCoverScale : ℝ) * (2 : ℝ) ^ k := by
            have hmul : (2 : ℝ) ^ k ≤
                (chargeCoverScale : ℝ) * (2 : ℝ) ^ k :=
              by
                simpa using mul_le_mul_of_nonneg_right hM
                  (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
            nlinarith
          _ ≤ 2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
  have hdiam' := hdiamS
  have hchain :
      2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent ≤
        Real.sqrt 2 * (2 : ℝ) ^ j := by
    calc
      2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent ≤
          euclideanSetDistance t u := hsep'
      _ ≤ euclideanSiteDistance y x := hset
      _ ≤ chargeEuclideanDiameter (chargeRestriction ρ s) := hsite
      _ ≤ Real.sqrt 2 * (2 : ℝ) ^ j := hdiam'
  exact (not_lt_of_ge hchain) hradius


/-- A neutral selected cluster cannot be the same at two different scales. -/
theorem badSelectedCluster_eq_forces_scale_eq_far (ϱ : RotatorDualFace L → ℤ)
    (hfar : Dirichlet.HasFarConstituentCharge (chargeCoverScale : ℝ) chargeCoverExponent
      (siteRestrict ϱ))
    (j k : ℕ)
    (s t : Finset (Site L)) (hs : s ∈ badSelectedSquares ϱ j)
    (ht : t ∈ badSelectedSquares ϱ k)
    (heq : chargeSupport (chargeRestriction (siteRestrict ϱ) s) =
      chargeSupport (chargeRestriction (siteRestrict ϱ) t)) : j = k := by
  classical
  by_contra hjk
  rcases lt_or_gt_of_ne hjk with hjk | hjk
  · let ρ := siteRestrict ϱ
    let C := boundaryEntropyMinimumCover ρ k
    have hC : IsMinimumSquareCover .free L k ρ C := boundaryEntropyMinimumCover_isMinimum ρ k
    have htSelected : t ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent k ρ C := by
      simpa [ρ, C, selectedSquares] using (Finset.mem_filter.mp ht).1
    have htData := badSelectedCluster_data ϱ k ht
    have hCne := htData.2.2.2.2.2
    have hdiamT : chargeEuclideanDiameter (chargeRestriction ρ t) ≤
        Real.sqrt 2 * (2 : ℝ) ^ j := by
      have hdiamS := (badSelectedCluster_data ϱ j hs).2.2.2.2.1
      unfold chargeEuclideanDiameter at hdiamS ⊢
      rw [heq] at hdiamS
      exact hdiamS
    have hsqrt : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hpow : (2 : ℝ) ^ j * 2 ≤ (2 : ℝ) ^ k := by
      calc
        (2 : ℝ) ^ j * 2 = (2 : ℝ) ^ (j + 1) := by rw [pow_succ]
        _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hjk)
    have hdiamStrict : chargeEuclideanDiameter (chargeRestriction ρ t) < (2 : ℝ) ^ k := by
      calc
        chargeEuclideanDiameter (chargeRestriction ρ t) ≤ Real.sqrt 2 * (2 : ℝ) ^ j := hdiamT
        _ < 2 * (2 : ℝ) ^ j := mul_lt_mul_of_pos_right hsqrt (by positivity)
        _ ≤ (2 : ℝ) ^ k := by simpa [mul_comm] using hpow
    have hdiam : chargeEuclideanDiameter (chargeRestriction ρ t) ≤ (2 : ℝ) ^ k :=
      hdiamStrict.le
    have hcharged := selectedRestriction_charged_of_far k ρ hfar C hC t htSelected hdiam
    exact hcharged htData.2.1
  · let ρ := siteRestrict ϱ
    let C := boundaryEntropyMinimumCover ρ j
    have hC : IsMinimumSquareCover .free L j ρ C := boundaryEntropyMinimumCover_isMinimum ρ j
    have hsSelected : s ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ C := by
      simpa [ρ, C, selectedSquares] using (Finset.mem_filter.mp hs).1
    have hsData := badSelectedCluster_data ϱ j hs
    have hCne := hsData.2.2.2.2.2
    have hdiamS : chargeEuclideanDiameter (chargeRestriction ρ s) ≤
        Real.sqrt 2 * (2 : ℝ) ^ k := by
      have hdiamT := (badSelectedCluster_data ϱ k ht).2.2.2.2.1
      unfold chargeEuclideanDiameter at hdiamT ⊢
      rw [heq]
      exact hdiamT
    have hsqrt : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hpow : (2 : ℝ) ^ k * 2 ≤ (2 : ℝ) ^ j := by
      calc
        (2 : ℝ) ^ k * 2 = (2 : ℝ) ^ (k + 1) := by rw [pow_succ]
        _ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hjk)
    have hdiamStrict : chargeEuclideanDiameter (chargeRestriction ρ s) < (2 : ℝ) ^ j := by
      calc
        chargeEuclideanDiameter (chargeRestriction ρ s) ≤ Real.sqrt 2 * (2 : ℝ) ^ k := hdiamS
        _ < 2 * (2 : ℝ) ^ k := mul_lt_mul_of_pos_right hsqrt (by positivity)
        _ ≤ (2 : ℝ) ^ j := by simpa [mul_comm] using hpow
    have hdiam : chargeEuclideanDiameter (chargeRestriction ρ s) ≤ (2 : ℝ) ^ j :=
      hdiamStrict.le
    have hcharged := selectedRestriction_charged_of_far j ρ hfar C hC s hsSelected hdiam
    exact hcharged hsData.2.1

/-- Two bad occurrences with the same cluster have the same scale and square. -/
theorem badSelectedCluster_injective_on_univ_far (ϱ : RotatorDualFace L → ℤ)
    (hfar : Dirichlet.HasFarConstituentCharge (chargeCoverScale : ℝ) chargeCoverExponent
      (siteRestrict ϱ)) :
    Set.InjOn (badSelectedCluster ϱ) Set.univ := by
  classical
  intro i _ i' _ heq
  rcases i with ⟨⟨j, hj⟩, ⟨s, hs⟩⟩
  rcases i' with ⟨⟨k, hk⟩, ⟨t, ht⟩⟩
  change chargeSupport (chargeRestriction (siteRestrict ϱ) s) =
    chargeSupport (chargeRestriction (siteRestrict ϱ) t) at heq
  have hscale := badSelectedCluster_eq_forces_scale_eq_far ϱ hfar j k s t hs ht heq
  subst k
  have hsquare := badSelectedSquare_eq_of_same_cluster ϱ j hs ht heq
  subst t
  rfl

/-- Neutral selected clusters form a laminar family. -/
theorem badSelectedClusterFamily_laminar_far (ϱ : RotatorDualFace L → ℤ) :
    IsLaminarFamily (badSelectedClusterFamily ϱ) := by
  classical
  intro A hA B hB hAB
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨i', _hi', rfl⟩ := Finset.mem_image.mp hB
  by_cases hdisj : Disjoint (badSelectedCluster ϱ i) (badSelectedCluster ϱ i')
  · exact Or.inl hdisj
  · have hoverlap : (badSelectedCluster ϱ i ∩ badSelectedCluster ϱ i').Nonempty := by
      rw [Finset.not_disjoint_iff] at hdisj
      rcases hdisj with ⟨x, hx, hx'⟩
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, hx'⟩⟩
    obtain ⟨x, hx⟩ := hoverlap
    have hs : i.2.1 ∈ badSelectedSquares ϱ i.1.1 := i.2.2
    have ht : i'.2.1 ∈ badSelectedSquares ϱ i'.1.1 := i'.2.2
    rcases le_total i.1.1 i'.1.1 with hik | hki
    · apply Or.inr (Or.inl ?_)
      exact badSelectedCluster_overlap_nested_far ϱ i.1.1 i'.1.1 hik
        i.2.1 i'.2.1 hs ht ⟨x, hx⟩
    · apply Or.inr (Or.inr ?_)
      exact badSelectedCluster_overlap_nested_far ϱ i'.1.1 i.1.1 hki
        i'.2.1 i.2.1 ht hs ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2,
          (Finset.mem_inter.mp hx).1⟩⟩


/-- **The bad selected squares are at most the face support** under the charged half of
isolation on boundary-far constituents. -/
theorem badSelectedSum_le_card_of_far (ϱ : RotatorDualFace L → ℤ)
    (hfar : Dirichlet.HasFarConstituentCharge (chargeCoverScale : ℝ) chargeCoverExponent
      (siteRestrict ϱ)) :
    badSelectedSum ϱ ≤ ((chargeSupport (siteRestrict ϱ)).card : ℝ) := by
  classical
  let ρ := siteRestrict ϱ
  let F := badSelectedClusterFamily ϱ
  have hInject := badSelectedCluster_injective_on_univ_far ϱ hfar
  have hCard : F.card = Fintype.card (BadSelectedIndex ϱ) := by
    dsimp [F, badSelectedClusterFamily]
    rw [Finset.card_image_iff.mpr (by simpa using hInject)]
    simp
  have hData := badSelectedClusterFamily_data ϱ
  have hLaminar := badSelectedClusterFamily_laminar_far ϱ
  have hFamilyCard : F.card ≤ (chargeSupport ρ).card :=
    laminarFamily_card_le_universe (chargeSupport ρ) F
      (by simpa [ρ] using hData.1) (by simpa [ρ] using hData.2) hLaminar
  rw [badSelectedSum_eq_index_card ϱ]
  calc
    (Fintype.card (BadSelectedIndex ϱ) : ℝ) = (F.card : ℝ) := by
      exact_mod_cast hCard.symm
    _ ≤ ((chargeSupport ρ).card : ℝ) := by exact_mod_cast hFamilyCard

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer.FarCharge

end
