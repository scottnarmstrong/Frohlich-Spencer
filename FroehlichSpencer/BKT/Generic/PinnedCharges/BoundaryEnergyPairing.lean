/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyGeometry
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGGeometry

/-! # Charge pairings and boundary clearance at selected scales

The selected-square separation is used with a slightly larger parameter than
the isolation constant.  This pays for the `sqrt 2` diameter of a square and
lets isolation apply to the charge restricted to one selected square.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

private theorem minimumCover_eq_singleton_of_mem {A : Type} [DecidableEq A]
    {C : Finset (Finset A)} {s : Finset A}
    (hcard : C.card = 1) (hs : s ∈ C) : C = {s} := by
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  have hts : s = t := by simpa [ht] using hs
  rw [ht, hts]

private theorem one_le_two_pow_real (j : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      nlinarith

/-- The boundary depth of any point of a finite set is at least the minimum
boundary depth of that set. -/
theorem euclideanBoundaryDistance_le_siteDepth_of_mem
    (s : Finset (Site L)) (hs : s.Nonempty) {x : Site L} (hx : x ∈ s) :
    euclideanBoundaryDistance s ≤ (siteBoundaryDepth x : ℝ) := by
  rw [euclideanBoundaryDistance, dite_eq_left hs]
  change (s.image fun y => (siteBoundaryDepth y : ℝ)).min' _ ≤ _
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- Restriction to a cover square of a minimum support cover is a nonzero
constituent of the original charge. -/
theorem boundaryEnergy_squareRestriction_isConstituent
    (j : ℕ) (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C)
    {s : Finset (Site L)} (hs : s ∈ C) :
    IsConstituent ρ (chargeRestriction ρ s) := by
  obtain ⟨x, hxρ, hxs, _⟩ := minimumCover_square_has_private_support_site j ρ C hC hs
  exact chargeRestriction_constituent ρ s ⟨x, hxρ, hxs⟩

/-- Every selected square has a charged restriction.  For nonsingleton covers
the Appendix-D isolation clause is applied after the scale factor pays for
the square's Euclidean diameter; for singleton covers this is exactly the
separate charged-singleton rule in `pinnedPPrime`. -/
theorem boundaryEnergy_selectedSquare_charge
    (Miso Msel α : ℝ) (hMiso : 0 < Miso) (hα : 0 < α)
    (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    (j : ℕ) (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation Miso α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L))) (hC : IsMinimumSquareCover .free L j ρ C)
    (s : Finset (Site L)) (hs : s ∈ pinnedPPrime Msel α j ρ C) :
    totalCharge (chargeRestriction ρ s) ≠ 0 := by
  classical
  by_cases hsingle : C.card = 1
  · have hkeep : totalCharge ρ ≠ 0 ∧
        singletonBoundaryMargin j ≤ chargeBoundaryDistance ρ := by
      by_contra hkeep
      have hempty := pinnedPPrime_eq_empty_of_singleton_exception_fails
        Msel α j ρ C hsingle hkeep
      rw [hempty] at hs
      exact Finset.notMem_empty _ hs
    have hsC : s ∈ C := by
      rw [pinnedPPrime_eq_self_of_singleton_exception Msel α j ρ C hsingle
        hkeep.1 hkeep.2] at hs
      exact hs
    have hsupport : chargeSupport ρ ⊆ s := by
      intro x hx
      obtain ⟨t, ht, hxt⟩ := hC.1.2 x hx
      have hts : t = s := by
        have hcard : C = {s} := minimumCover_eq_singleton_of_mem hsingle hsC
        rw [hcard] at ht
        simpa using ht
      simpa [hts] using hxt
    have hsame : chargeRestriction ρ s = ρ := by
      funext x
      by_cases hxs : x ∈ s
      · simp [chargeRestriction, hxs]
      · have hxzero : ρ x = 0 := by
          by_contra hxne
          exact hxs (hsupport (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne⟩))
        simp [chargeRestriction, hxs, hxzero]
    simpa [hsame] using hkeep.1
  · have hsdata := (mem_pinnedPPrime_of_cover_card_ne_one Msel α j ρ C hsingle s).1 hs
    rcases hsdata with ⟨hsC, hsep, _hboundary⟩
    obtain ⟨x₀, hx₀ρ, hx₀s, hprivate₀⟩ :=
      minimumCover_square_has_private_support_site j ρ C hC hsC
    let child := chargeRestriction ρ s
    let residual : ChargeDensity L := fun x => ρ x - child x
    have hchildne : child ≠ 0 := by
      intro hz
      have hxval : child x₀ ≠ 0 := by
        simpa [child, chargeRestriction, hx₀s] using
          (Finset.mem_filter.mp hx₀ρ).2
      exact hxval (congrFun hz x₀)
    have hchildconst : IsConstituent ρ child := by
      simpa [child] using chargeRestriction_constituent ρ s ⟨x₀, hx₀ρ, hx₀s⟩
    have hchildsub : chargeSupport child ⊆ s := by
      intro x hx
      exact (mem_chargeSupport_restriction_iff ρ s x).mp hx |>.1
    have hchilddiam : chargeEuclideanDiameter child ≤
        Real.sqrt 2 * (2 : ℝ) ^ j := by
      have hchildsupp : (chargeSupport child).Nonempty :=
        chargeSupport_nonempty_of_ne_zero child hchildne
      have hsnonempty : s.Nonempty := ⟨x₀, hx₀s⟩
      have hdiam := euclideanSetDiameter_subset_le
        (chargeSupport child) s hchildsupp hsnonempty hchildsub
      calc
        chargeEuclideanDiameter child = euclideanSetDiameter (chargeSupport child) := rfl
        _ ≤ euclideanSetDiameter s := hdiam
        _ ≤ Real.sqrt 2 * (2 : ℝ) ^ j :=
          freeSquare_euclideanDiameter_le (hC.1.1 hsC)
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
      have hxzero : residual x = 0 := by
        simp [residual, child, chargeRestriction, hxs]
      exact (Finset.mem_filter.mp hx).2 hxzero
    have hpairEvery {x y : Site L} (hx : x ∈ chargeSupport child)
        (hy : y ∈ chargeSupport residual) :
        2 * Msel * ((2 : ℝ) ^ j) ^ α ≤ euclideanSiteDistance x y := by
      have hxs : x ∈ s := hchildsub hx
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
      have hst := hsep t ht hts
      have hscale : ((2 : ℝ) ^ j) ^ α =
          (2 : ℝ) ^ (α * (j : ℝ)) := by
        calc
          ((2 : ℝ) ^ j) ^ α = (2 : ℝ) ^ ((j : ℝ) * α) := by
            rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
          _ = (2 : ℝ) ^ (α * (j : ℝ)) :=
            congrArg (fun z : ℝ => (2 : ℝ) ^ z) (by ring)
      calc
        2 * Msel * ((2 : ℝ) ^ j) ^ α =
            2 * Msel * (2 : ℝ) ^ (α * (j : ℝ)) := by rw [hscale]
        _ ≤ euclideanSetDistance s t := hsep t ht hts
        _ ≤ euclideanSiteDistance x y := setDist_le_siteDist hxs hyt
    have hdist : 2 * Msel * ((2 : ℝ) ^ j) ^ α ≤
        euclideanSetDistance (chargeSupport child) (chargeSupport residual) :=
      le_setDist (chargeSupport_nonempty_of_ne_zero child hchildne)
        (chargeSupport_nonempty_of_ne_zero residual hresne)
        (fun x hx y hy => hpairEvery hx hy)
    have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hrpos : 0 < (2 : ℝ) ^ j := by positivity
    have hdiamPow : chargeEuclideanDiameter child ^ α ≤
        (Real.sqrt 2 * (2 : ℝ) ^ j) ^ α := by
      exact Real.rpow_le_rpow (SelectionG.diam_nonneg _) hchilddiam hα.le
    have hmulpow : (Real.sqrt 2 * (2 : ℝ) ^ j) ^ α =
        (Real.sqrt 2) ^ α * ((2 : ℝ) ^ j) ^ α :=
      Real.mul_rpow hrootpos.le hrpos.le
    have htrigger : 2 * Miso * chargeEuclideanDiameter child ^ α ≤
        euclideanSetDistance (chargeSupport child) (chargeSupport residual) := by
      calc
        2 * Miso * chargeEuclideanDiameter child ^ α ≤
            2 * Miso * (Real.sqrt 2 * (2 : ℝ) ^ j) ^ α :=
              mul_le_mul_of_nonneg_left hdiamPow (by positivity)
        _ = 2 * (Miso * (Real.sqrt 2) ^ α) * ((2 : ℝ) ^ j) ^ α := by
              rw [hmulpow]
              ring
        _ ≤ 2 * Msel * ((2 : ℝ) ^ j) ^ α := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              nlinarith [hmargin]
        _ ≤ euclideanSetDistance (chargeSupport child) (chargeSupport residual) := hdist
    have hresult := hN ρ hρ child hchildconst (by simpa [residual] using htrigger)
    exact hresult.1

/-- Selected-square charge support keeps the Appendix-D boundary margin.
This is the support clearance needed for zero-exterior tent profiles. -/
theorem boundaryEnergy_selectedSquare_boundaryClearance
    (M α : ℝ) (j : ℕ) (ρ : ChargeDensity L)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C)
    (s : Finset (Site L)) (hs : s ∈ pinnedPPrime M α j ρ C) :
    scaleBoundaryMargin j ≤
      euclideanBoundaryDistance (chargeSupport (chargeRestriction ρ s)) := by
  classical
  have hsC : s ∈ C :=
    (pinnedPPrime_mem_of_minimumCover M α j ρ C hC hs).1
  have hchildne : chargeRestriction ρ s ≠ 0 :=
    (boundaryEnergy_squareRestriction_isConstituent j ρ C hC hsC).1
  have hchildsupp : (chargeSupport (chargeRestriction ρ s)).Nonempty :=
    chargeSupport_nonempty_of_ne_zero _ hchildne
  have hchildsub : chargeSupport (chargeRestriction ρ s) ⊆ s := by
    intro x hx
    exact (mem_chargeSupport_restriction_iff ρ s x).mp hx |>.1
  by_cases hsingle : C.card = 1
  · have hkeep : totalCharge ρ ≠ 0 ∧
        singletonBoundaryMargin j ≤ chargeBoundaryDistance ρ := by
      by_contra hkeep
      have hempty := pinnedPPrime_eq_empty_of_singleton_exception_fails
        M α j ρ C hsingle hkeep
      rw [hempty] at hs
      exact Finset.notMem_empty _ hs
    have hsC : s ∈ C := by
      rw [pinnedPPrime_eq_self_of_singleton_exception M α j ρ C hsingle
        hkeep.1 hkeep.2] at hs
      exact hs
    have hsupport : chargeSupport ρ ⊆ s := by
      intro x hx
      obtain ⟨t, ht, hxt⟩ := hC.1.2 x hx
      have hEq : t = s := by
        have hcard : C = {s} := minimumCover_eq_singleton_of_mem hsingle hsC
        rw [hcard] at ht
        simpa using ht
      simpa [hEq] using hxt
    have hsame : chargeRestriction ρ s = ρ := by
      funext x
      by_cases hxs : x ∈ s
      · simp [chargeRestriction, hxs]
      · have hxzero : ρ x = 0 := by
          by_contra hxne
          exact hxs (hsupport (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne⟩))
        simp [chargeRestriction, hxs, hxzero]
    have hscale : scaleBoundaryMargin j ≤ singletonBoundaryMargin j := by
      unfold scaleBoundaryMargin singletonBoundaryMargin
      rw [pow_add, pow_add]
      norm_num
    have hbound : scaleBoundaryMargin j ≤ euclideanBoundaryDistance (chargeSupport ρ) :=
      hscale.trans (by simpa [chargeBoundaryDistance] using hkeep.2)
    simpa [hsame] using hbound
  · have hdata := (mem_pinnedPPrime_of_cover_card_ne_one M α j ρ C hsingle s).1 hs
    rcases hdata with ⟨hsC, _hsep, hmargin⟩
    have hsnonempty : s.Nonempty := hchildsupp.mono hchildsub
    have hminle : ∀ x ∈ s, euclideanBoundaryDistance s ≤ (siteBoundaryDepth x : ℝ) :=
      fun x hx => euclideanBoundaryDistance_le_siteDepth_of_mem s hsnonempty hx
    rw [euclideanBoundaryDistance, dite_eq_left hchildsupp]
    refine Finset.le_min' _ _ _ ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hmargin.trans (hminle x (hchildsub hx))

/-- A field that is one on a selected square and pairs trivially with all
charge outside it pairs exactly with the square restriction. -/
theorem boundaryEnergy_squarePairing_eq_restriction
    (ρ : ChargeDensity L) (s : Finset (Site L)) (φ : Site L → ℝ)
    (hplateau : ∀ x ∈ s, φ x = 1)
    (houtside : ∀ x, x ∉ s → φ x * (ρ x : ℝ) = 0) :
    (∑ x, φ x * (ρ x : ℝ)) =
      (totalCharge (chargeRestriction ρ s) : ℝ) := by
  classical
  calc
    (∑ x, φ x * (ρ x : ℝ)) =
        ∑ x, (chargeRestriction ρ s x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x ∈ s
          · rw [hplateau x hx]
            simp [chargeRestriction, hx]
          · have hchildzero : chargeRestriction ρ s x = 0 := by
              simp [chargeRestriction, hx]
            rw [houtside x hx, hchildzero]
            simp
    _ = (totalCharge (chargeRestriction ρ s) : ℝ) := by
          simp [totalCharge, Int.cast_sum]

/-- The signed local pairing of a selected-square plateau has magnitude at
least one whenever the isolation argument charges its restriction. -/
theorem boundaryEnergy_squarePairing_abs_ge_one
    (ρ : ChargeDensity L) (s : Finset (Site L)) (φ : Site L → ℝ)
    (hcharge : totalCharge (chargeRestriction ρ s) ≠ 0)
    (hplateau : ∀ x ∈ s, φ x = 1)
    (houtside : ∀ x, x ∉ s → φ x * (ρ x : ℝ) = 0) :
    1 ≤ |∑ x, φ x * (ρ x : ℝ)| := by
  rw [boundaryEnergy_squarePairing_eq_restriction ρ s φ hplateau houtside]
  rcases lt_or_gt_of_ne hcharge with hneg | hpos
  · rw [abs_of_neg]
    · exact_mod_cast (show (1 : ℤ) ≤ -totalCharge (chargeRestriction ρ s) by omega)
    · exact_mod_cast hneg
  · rw [abs_of_pos]
    · exact_mod_cast (show (1 : ℤ) ≤ totalCharge (chargeRestriction ρ s) by omega)
    · exact_mod_cast hpos

/--
A one-square-neighborhood profile pairs only with the charge restricted
to its selected square.
-/
theorem boundaryEnergy_selectedSquare_pairing_abs_ge_one
    (Miso Msel α : ℝ) (hMiso : 0 < Miso) (hαpos : 0 < α)
    (hα : 1 ≤ α) (hMsel : 1 ≤ Msel)
    (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    (j : ℕ) (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation Miso α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L))) (hC : IsMinimumSquareCover .free L j ρ C)
    (s : Finset (Site L)) (hs : s ∈ pinnedPPrime Msel α j ρ C)
    (φ : Site L → ℝ) (hplateau : ∀ x ∈ s, φ x = 1)
    (hlocal : ∀ x, x ∉ s →
      (∀ y ∈ s, (2 : ℝ) ^ j < euclideanSiteDistance y x) → φ x = 0) :
    1 ≤ |∑ x, φ x * (ρ x : ℝ)| := by
  have hcharge := boundaryEnergy_selectedSquare_charge Miso Msel α hMiso
    hαpos hmargin j ρ N hN hρ C hC s hs
  have houtside : ∀ x, x ∉ s → φ x * (ρ x : ℝ) = 0 := by
    intro x hxs
    by_cases hρx : ρ x = 0
    · simp [hρx]
    · have hxρ : x ∈ chargeSupport ρ := by simp [chargeSupport, hρx]
      obtain ⟨t, ht, hxt⟩ := hC.1.2 x hxρ
      have hts : t ≠ s := by
        intro h
        subst t
        exact hxs hxt
      have hsdata :=
        (mem_pinnedPPrime_of_cover_card_ne_one Msel α j ρ C (by
          intro hsingle
          -- The singleton exception has support contained in its only square,
          -- so it cannot contain an outside site.
          have hsC : s ∈ C :=
            (pinnedPPrime_mem_of_minimumCover Msel α j ρ C hC hs).1
          have hcard : C = {s} := minimumCover_eq_singleton_of_mem hsingle hsC
          exact hts (by simpa [hcard] using ht)) s).1 hs
      rcases hsdata with ⟨hsC, hsep, _⟩
      have hrpow : (2 : ℝ) ^ j ≤ ((2 : ℝ) ^ j) ^ α := by
        have hbase := one_le_two_pow_real j
        calc
          (2 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ (1 : ℝ) :=
            (Real.rpow_one _).symm
          _ ≤ ((2 : ℝ) ^ j) ^ α :=
            Real.rpow_le_rpow_of_exponent_le hbase hα
      have hradius : (2 : ℝ) ^ j <
          2 * Msel * ((2 : ℝ) ^ j) ^ α := by
        have hrpos : 0 < (2 : ℝ) ^ j := by positivity
        nlinarith [mul_nonneg (sub_nonneg.mpr hMsel)
          (Real.rpow_nonneg hrpos.le α)]
      have hscale : ((2 : ℝ) ^ j) ^ α =
          (2 : ℝ) ^ (α * (j : ℝ)) := by
        calc
          ((2 : ℝ) ^ j) ^ α = (2 : ℝ) ^ ((j : ℝ) * α) := by
            rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
          _ = (2 : ℝ) ^ (α * (j : ℝ)) :=
            congrArg (fun z : ℝ => (2 : ℝ) ^ z) (by ring)
      have hfar : ∀ y ∈ s, (2 : ℝ) ^ j < euclideanSiteDistance y x := by
        intro y hy
        have hsep' := hsep t ht hts
        have hdist := setDist_le_siteDist hy hxt
        have hR : 2 * Msel * ((2 : ℝ) ^ j) ^ α ≤
            euclideanSetDistance s t := by
          rw [hscale]
          exact hsep'
        exact lt_of_lt_of_le hradius (hR.trans hdist)
      rw [hlocal x hxs hfar]
      simp
  exact boundaryEnergy_squarePairing_abs_ge_one ρ s φ hcharge hplateau houtside

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
