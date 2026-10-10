/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.Selection
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryCutGeometry

/-! # Isolation forces a neighbor for a rejected cover square

On the literal Euclidean free-box carrier, a cover square that misses the
Appendix D boundary margin cannot be well separated from every other cover
square when the covered density has `HasBoundaryIsolation`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

/-- Restrict a charge density to a finite set of sites. -/
def chargeRestriction {L : ℕ} (ρ : ChargeDensity L) (s : Finset (Site L)) :
    ChargeDensity L := fun x => if x ∈ s then ρ x else 0

theorem mem_chargeSupport_restriction_iff {L : ℕ} (ρ : ChargeDensity L)
    (s : Finset (Site L)) (x : Site L) :
    x ∈ chargeSupport (chargeRestriction ρ s) ↔ x ∈ s ∧ x ∈ chargeSupport ρ := by
  simp [chargeSupport, chargeRestriction]

theorem chargeRestriction_constituent {L : ℕ} (ρ : ChargeDensity L)
    (s : Finset (Site L)) (hρs : ∃ x ∈ chargeSupport ρ, x ∈ s) :
    IsConstituent ρ (chargeRestriction ρ s) := by
  rcases hρs with ⟨x, hxρ, hxs⟩
  have hxρval : ρ x ≠ 0 := (Finset.mem_filter.mp hxρ).2
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hx : chargeRestriction ρ s x ≠ 0 := by
      simpa [chargeRestriction, hxs] using hxρval
    exact hx (congrFun hzero x)
  · intro x hx
    exact (mem_chargeSupport_restriction_iff ρ s x).mp hx |>.2
  · intro x hx
    have hxs' := (mem_chargeSupport_restriction_iff ρ s x).mp hx |>.1
    simp [chargeRestriction, hxs']

private theorem euclideanSetDistance_le_siteDistance {L : ℕ}
    (s t : Finset (Site L))
    {x y : Site L} (hx : x ∈ s) (hy : y ∈ t) :
    euclideanSetDistance s t ≤ euclideanSiteDistance x y := by
  have hprod : (s.product t).Nonempty :=
    ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  unfold euclideanSetDistance
  rw [dite_eq_left hprod]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩)

/-- The isolation clause forces a rejected boundary square to have another
cover square within the inflated radius. The hypotheses `hprivate` and
`hcover` are supplied by a minimum support cover. `hsdiam` is the elementary
Euclidean diameter bound for a side-`r` free square. -/
theorem boundaryIsolation_rejectedSquare_has_close_neighbor {L : ℕ}
    (M α r : ℝ) (hM : 0 < M) (hα : 0 < α) (hr : 0 < r)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L))) (s : Finset (Site L))
    (hcover : ∀ x ∈ chargeSupport ρ, ∃ t ∈ C, x ∈ t)
    (hs : s ∈ C) (hsingle : C.card ≠ 1)
    (hprivateAll : ∀ t ∈ C, ∃ x ∈ chargeSupport ρ, x ∈ t ∧
      ∀ u ∈ C, u ≠ t → x ∉ u)
    (hmargin : euclideanBoundaryDistance s < 4 * r)
    (hsdiam : euclideanSetDiameter s ≤ Real.sqrt 2 * r) :
    ∃ t ∈ C, t ≠ s ∧ euclideanSetDistance s t <
      2 * M * ((4 + Real.sqrt 2) * r) ^ α := by
  classical
  let child := chargeRestriction ρ s
  let R := 2 * M * ((4 + Real.sqrt 2) * r) ^ α
  by_contra hnoNeighbor
  have hseparated : ∀ u ∈ C, u ≠ s → R ≤ euclideanSetDistance s u := by
    intro u hu hus
    by_contra hnot
    exact hnoNeighbor ⟨u, hu, hus, lt_of_not_ge hnot⟩
  obtain ⟨x, hxρ, hxs, _hxprivate⟩ := hprivateAll s hs
  have hchildNonzero : child ≠ 0 := by
    intro hz
    have hx0 : child x ≠ 0 := by simpa [child, chargeRestriction, hxs] using
      (Finset.mem_filter.mp hxρ).2
    exact hx0 (congrFun hz x)
  have hsNonempty : s.Nonempty := ⟨x, hxs⟩
  have hchildSupport : chargeSupport child ⊆ s := by
    intro y hy
    exact (mem_chargeSupport_restriction_iff ρ s y).mp hy |>.1
  have hchildConstituent : IsConstituent ρ child := by
    simpa [child] using chargeRestriction_constituent ρ s ⟨x, hxρ, hxs⟩
  obtain ⟨t, ht, hts⟩ : ∃ t ∈ C, t ≠ s := by
    by_contra h
    have hall : ∀ t ∈ C, t = s := by
      intro u hu
      by_contra hne
      exact h ⟨u, hu, hne⟩
    have hcard : C.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
      (hall a ha).trans (hall b hb).symm
    have hpos : 0 < C.card := Finset.card_pos.mpr ⟨s, hs⟩
    exact hsingle (Nat.le_antisymm hcard (by omega))
  obtain ⟨y, hyρ, hyt, hyprivate⟩ := hprivateAll t ht
  have hys : y ∉ s := by
    intro hys
    exact hyprivate s hs (Ne.symm hts) hys
  have hyResidual : (ρ y - child y) ≠ 0 := by
    have hyρ' : ρ y ≠ 0 := (Finset.mem_filter.mp hyρ).2
    simp [child, chargeRestriction, hys, hyρ']
  let residual : ChargeDensity L := fun z => ρ z - child z
  have hresidualNonzero : residual ≠ 0 := by
    intro hz
    have hy0 : residual y = 0 := congrFun hz y
    exact hyResidual (by simpa [residual] using hy0)
  have hresidualSupportOutside : ∀ z ∈ chargeSupport residual, z ∉ s := by
    intro z hz hzs
    have hz0 : residual z = 0 := by simp [residual, child, chargeRestriction, hzs]
    exact (Finset.mem_filter.mp hz).2 hz0
  have hchildBoundary : chargeBoundaryDistance child < (4 + Real.sqrt 2) * r := by
    have hchildNonempty : (chargeSupport child).Nonempty :=
      chargeSupport_nonempty_of_ne_zero child hchildNonzero
    have hdirect := euclideanBoundaryDistance_subset_le
      (chargeSupport child) s hchildNonempty hsNonempty hchildSupport
    calc
      chargeBoundaryDistance child ≤ euclideanBoundaryDistance s +
          euclideanSetDiameter s := by simpa [chargeBoundaryDistance] using hdirect
      _ < (4 + Real.sqrt 2) * r := by nlinarith [hmargin, hsdiam, hr]
  have hchildDiameter : chargeEuclideanDiameter child ≤ Real.sqrt 2 * r := by
    have hchildNonempty : (chargeSupport child).Nonempty :=
      chargeSupport_nonempty_of_ne_zero child hchildNonzero
    simpa [chargeEuclideanDiameter] using
      (euclideanSetDiameter_subset_le (chargeSupport child) s hchildNonempty hsNonempty
        hchildSupport).trans hsdiam
  have hdiamNonneg : 0 ≤ chargeEuclideanDiameter child := by
    have hchildNonempty : (chargeSupport child).Nonempty :=
      chargeSupport_nonempty_of_ne_zero child hchildNonzero
    obtain ⟨z, hz⟩ := hchildNonempty
    have hprod : ((chargeSupport child).product (chargeSupport child)).Nonempty :=
      ⟨(z, z), Finset.mem_product.mpr ⟨hz, hz⟩⟩
    unfold chargeEuclideanDiameter euclideanSetDiameter
    rw [dite_eq_left hprod]
    have hmem : euclideanSiteDistance z z ∈
        Finset.image (fun p : Site L × Site L => euclideanSiteDistance p.1 p.2)
          ((chargeSupport child).product (chargeSupport child)) :=
      Finset.mem_image.mpr ⟨(z, z), Finset.mem_product.mpr ⟨hz, hz⟩, rfl⟩
    have hle := Finset.le_max' _ _ hmem
    have hzdist : euclideanSiteDistance z z = 0 := by
      simp [euclideanSiteDistance]
    calc
      0 = euclideanSiteDistance z z := hzdist.symm
      _ ≤ _ := hle
  have hpowDiam : chargeEuclideanDiameter child ^ α ≤
      ((4 + Real.sqrt 2) * r) ^ α := by
    apply Real.rpow_le_rpow hdiamNonneg
    · calc
        chargeEuclideanDiameter child ≤ Real.sqrt 2 * r := hchildDiameter
        _ ≤ (4 + Real.sqrt 2) * r := by nlinarith [hr]
    · exact hα.le
  have hsetChild : (chargeSupport child).Nonempty :=
    chargeSupport_nonempty_of_ne_zero child hchildNonzero
  have hsetResidual : (chargeSupport residual).Nonempty :=
    chargeSupport_nonempty_of_ne_zero residual hresidualNonzero
  have hprod : ((chargeSupport child).product (chargeSupport residual)).Nonempty :=
    ⟨(hsetChild.choose, hsetResidual.choose), Finset.mem_product.mpr
      ⟨hsetChild.choose_spec, hsetResidual.choose_spec⟩⟩
  have hmin := Finset.min'_mem
    (((chargeSupport child).product (chargeSupport residual)).image
      fun p : Site L × Site L => euclideanSiteDistance p.1 p.2)
    (Finset.image_nonempty.mpr hprod)
  obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hmin
  have ha := (Finset.mem_product.mp hab).1
  have hb := (Finset.mem_product.mp hab).2
  have has : a ∈ s := hchildSupport ha
  have hbs : b ∉ s := hresidualSupportOutside b hb
  have hρb : ρ b ≠ 0 := by
    simpa [residual, child, chargeRestriction, hbs] using
      (Finset.mem_filter.mp hb).2
  obtain ⟨u, hu, hbu⟩ := hcover b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρb⟩)
  have hus : u ≠ s := by
    intro hus
    subst u
    exact hbs hbu
  have hsetSep : R ≤ euclideanSetDistance s u := hseparated u hu hus
  have hpoint := euclideanSetDistance_le_siteDistance s u has hbu
  have hRpoint : R ≤ euclideanSiteDistance a b := hsetSep.trans hpoint
  have hRminVal : R ≤
      (((chargeSupport child).product (chargeSupport residual)).image
        fun p : Site L × Site L => euclideanSiteDistance p.1 p.2).min'
        (Finset.image_nonempty.mpr hprod) := by
    rw [← heq]
    exact hRpoint
  have hRmin : R ≤ euclideanSetDistance (chargeSupport child) (chargeSupport residual) := by
    simp only [euclideanSetDistance, dite_eq_left hprod]
    exact hRminVal
  have htrigger : 2 * M * chargeEuclideanDiameter child ^ α ≤
      euclideanSetDistance (chargeSupport child) (chargeSupport residual) := by
    calc
      2 * M * chargeEuclideanDiameter child ^ α ≤ R := by
        dsimp [R]
        exact mul_le_mul_of_nonneg_left hpowDiam (by positivity)
      _ ≤ euclideanSetDistance (chargeSupport child) (chargeSupport residual) := hRmin
  obtain ⟨-, hIsoBound⟩ := hN ρ hρ child hchildConstituent (by simpa [residual] using htrigger)
  have hdepthPow : chargeBoundaryDistance child ^ α <
      ((4 + Real.sqrt 2) * r) ^ α := by
    exact Real.rpow_lt_rpow
      (le_of_lt (chargeBoundaryDistance_pos_of_ne_zero child hchildNonzero))
      hchildBoundary hα
  have hIsoStrict : euclideanSetDistance (chargeSupport child) (chargeSupport residual) < R := by
    calc
      euclideanSetDistance (chargeSupport child) (chargeSupport residual) ≤
          2 * M * chargeBoundaryDistance child ^ α := by simpa [residual] using hIsoBound
      _ < 2 * M * ((4 + Real.sqrt 2) * r) ^ α :=
        mul_lt_mul_of_pos_left hdepthPow (by positivity)
  linarith [hRmin, hIsoStrict]

/-- Minimum-cover adapter for the rejected-square isolation lemma. The final
diameter bound is the elementary Euclidean estimate for a side-`r` free
square. -/
theorem boundaryIsolation_rejectedSquare_has_close_neighbor_of_minimumCover
    {L j : ℕ} (M α r : ℝ) (hM : 0 < M) (hα : 0 < α) (hr : 0 < r)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C)
    {s : Finset (Site L)} (hs : s ∈ C) (hsingle : C.card ≠ 1)
    (hmargin : euclideanBoundaryDistance s < 4 * r)
    (hsdiam : euclideanSetDiameter s ≤ Real.sqrt 2 * r) :
    ∃ t ∈ C, t ≠ s ∧ euclideanSetDistance s t <
      2 * M * ((4 + Real.sqrt 2) * r) ^ α := by
  have hprivateAll : ∀ t ∈ C, ∃ x ∈ chargeSupport ρ, x ∈ t ∧
      ∀ u ∈ C, u ≠ t → x ∉ u := by
    intro t ht
    exact minimumCover_square_has_private_support_site j ρ C hC ht
  exact boundaryIsolation_rejectedSquare_has_close_neighbor
    M α r hM hα hr ρ N hN hρ C s hC.1.2 hs hsingle hprivateAll hmargin hsdiam

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
