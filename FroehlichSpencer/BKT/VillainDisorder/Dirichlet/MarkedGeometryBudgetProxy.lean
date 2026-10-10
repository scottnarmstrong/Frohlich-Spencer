/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryBudgetEntropy
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryProxyCut
import Mathlib.Tactic

/-!
# Rejected-square neighbours of the rooted marked proxy (D2G3b)

The face part `p` of the rooted marked proxy is not known to satisfy Appendix D isolation. It does
satisfy the one consequence of isolation that the entropy estimate uses
(`Generic.PinnedCharges.Rejected.HasRejectedNeighbor`): a square of a nonsingleton minimum cover
that fails the boundary margin `d_bdry(s) < 2^{j+2}` and is far from every other cover square
cannot exist. Let `A = X(C) ∩ s` be its part of the composite support. Then:
* if `A` contains a mark face, the mark is within `(4 + √2)2^j` of the boundary. The buffer
  `2n ≤ R` then makes the inflated radius exceed the size of the square;
* if a cluster member straddles `s`, its piece in `s` is an isolated constituent of a branch
  density, hence close to the boundary at the member's scale, which contradicts the separation;
* otherwise `A` consists of whole members. The member of `A` adjacent to the rest of the cluster
  has `d_Λ < (4 + √2) 2^j`, which contradicts the separation.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges (euclideanSetDistance euclideanSetDiameter
  euclideanBoundaryDistance boundaryAdjustedSize totalCharge chargeEuclideanDiameter
  chargeBoundaryDistance IsConstituent AppendixDChargeGeometry neutralizeAtWiredRoot
  chargeRestriction siteBoundaryDepth euclideanSiteDistance pinnedPPrime)

section Geometry

variable {L : ℕ}

theorem euclideanBoundaryDistance_singleton (x : Fin L × Fin L) :
    euclideanBoundaryDistance {x} = (siteBoundaryDepth x : ℝ) := by
  unfold euclideanBoundaryDistance
  rw [dite_eq_left (Finset.singleton_nonempty x)]
  simp

end Geometry

variable {R n : ℕ}

/-- The two faces of the mark have boundary depth at least `R + 1 − n`. -/
theorem rootedMark_depth_ge (hn : n ≤ R) {x : Site R}
    (hx : x = center R ∨ x = axialSite R n hn) :
    R + 1 - n ≤ siteBoundaryDepth x := by
  rcases hx with rfl | rfl <;>
    simp only [siteBoundaryDepth, center, axialSite, sideLength] <;> omega

/-- **The core of the rejected-square property**: no square of a nonsingleton minimum cover of
the proxy fails the boundary margin while being at the inflated distance from every other
cover square. -/
theorem rootedMarkedProxy_not_isolated_rejected (hn : n ≤ R) (hRn : 2 * n ≤ R)
    {F : Finset (ChargeDensity (sideLength R))}
    (hgeo : AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hC : C ∈ clusters (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
      (F.image neutralizeAtWiredRoot))
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) {j : ℕ}
    {Cv : Finset (Finset (Site R))}
    (hCv : IsMinimumSquareCover .free (sideLength R) j
      (siteRestrict (rootedMarkedProxy R n hn C T)) Cv)
    (hcard : Cv.card ≠ 1) {s : Finset (Site R)} (hs : s ∈ Cv)
    (hmargin : euclideanBoundaryDistance s < 4 * (2 : ℝ) ^ j)
    (hfarAll : ∀ t ∈ Cv, t ≠ s → 2 * (chargeCoverScale : ℝ) *
      ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ chargeCoverExponent ≤ euclideanSetDistance s t) :
    False := by
  classical
  set M : ℝ := (chargeCoverScale : ℝ) with hMdef
  set α : ℝ := chargeCoverExponent with hαdef
  set p := siteRestrict (rootedMarkedProxy R n hn C T) with hp
  set X := rootedMarkedSupport R n hn C with hX
  set r : ℝ := (2 : ℝ) ^ j with hr
  set ρr : ℝ := 2 * M * ((4 + Real.sqrt 2) * r) ^ α with hρr
  have hM1 : (1 : ℝ) < M := by norm_num [hMdef, chargeCoverScale]
  have hM0 : (0 : ℝ) < M := by linarith
  have hα1 : (1 : ℝ) ≤ α := by norm_num [hαdef, chargeCoverExponent]
  have hα0 : (0 : ℝ) < α := by linarith
  have hr1 : 1 ≤ r := one_le_pow₀ (by norm_num)
  have hsq0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hCN := (mem_clusters.1 hC).1
  have hsuppP : chargeSupport p = X := chargeSupport_siteRestrict_rootedMarkedProxy hn hT
    (disjoint_siteRestrict_of_subset_image hgeo.ensemble hCN)
  have hsdiam : euclideanSetDiameter s ≤ Real.sqrt 2 * r :=
    Generic.PinnedCharges.freeSquare_euclideanDiameter_le (hCv.1.1 hs)
  obtain ⟨x₀, hx₀p, hx₀s, -⟩ :=
    Generic.PinnedCharges.minimumCover_square_has_private_support_site j p Cv hCv hs
  have hsne : s.Nonempty := ⟨x₀, hx₀s⟩
  obtain ⟨t, ht, hts⟩ : ∃ t ∈ Cv, t ≠ s := by
    by_contra h
    push Not at h
    have : Cv.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => (h a ha).trans (h b hb).symm
    have : 0 < Cv.card := Finset.card_pos.mpr ⟨s, hs⟩
    omega
  obtain ⟨y₀, hy₀p, hy₀t, hy₀priv⟩ :=
    Generic.PinnedCharges.minimumCover_square_has_private_support_site j p Cv hCv ht
  have hy₀s : y₀ ∉ s := hy₀priv s hs (Ne.symm hts)
  -- every point of `s` is at the inflated distance from the support outside `s`
  have hsep : ∀ x ∈ s, ∀ y ∈ X, y ∉ s → ρr ≤ euclideanSiteDistance x y := by
    intro x hx y hyX hys
    obtain ⟨u, hu, hyu⟩ := hCv.1.2 y (by rw [hsuppP]; exact hyX)
    have hus : u ≠ s := fun h => hys (h ▸ hyu)
    exact (hfarAll u hu hus).trans
      (Generic.PinnedCharges.SelectionG.setDist_le_siteDist hx hyu)
  have hbd : ∀ A ⊆ s, A.Nonempty → euclideanBoundaryDistance A < (4 + Real.sqrt 2) * r := by
    intro A hAs hA
    have h := Generic.PinnedCharges.euclideanBoundaryDistance_subset_le A s hA hsne hAs
    linarith
  have hlt : ∀ b : ℝ, 0 ≤ b → b < (4 + Real.sqrt 2) * r → M * b ^ α < ρr / 2 := by
    intro b hb hbr
    have h := Real.rpow_lt_rpow hb hbr hα0
    have : ρr / 2 = M * ((4 + Real.sqrt 2) * r) ^ α := by rw [hρr]; ring
    rw [this]
    exact mul_lt_mul_of_pos_left h hM0
  have hρr0 : 0 ≤ ρr := by positivity
  by_cases hmark : center R ∈ s ∨ axialSite R n hn ∈ s
  · -- a mark face near the boundary: the inflated radius exceeds the square
    obtain ⟨xm, hxm, hxms⟩ : ∃ xm, (xm = center R ∨ xm = axialSite R n hn) ∧ xm ∈ s := by
      rcases hmark with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    have hdepth := rootedMark_depth_ge hn hxm
    have hdepthR : (R : ℝ) / 2 + 1 ≤ siteBoundaryDepth xm := by
      have h1 : ((R + 1 - n : ℕ) : ℝ) ≤ (siteBoundaryDepth xm : ℝ) := by exact_mod_cast hdepth
      have h2 : ((R + 1 - n : ℕ) : ℝ) = (R : ℝ) + 1 - n := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have h3 : (2 * n : ℝ) ≤ R := by exact_mod_cast hRn
      linarith
    have hxmb := hbd {xm} (Finset.singleton_subset_iff.2 hxms) (Finset.singleton_nonempty xm)
    rw [euclideanBoundaryDistance_singleton] at hxmb
    have hbig : (R : ℝ) / 2 + 1 < (4 + Real.sqrt 2) * r := by linarith
    have hge1 : (1 : ℝ) ≤ (4 + Real.sqrt 2) * r := by
      have : (0 : ℝ) ≤ R / 2 := by positivity
      linarith
    have hpow : (4 + Real.sqrt 2) * r ≤ ((4 + Real.sqrt 2) * r) ^ α := by
      calc (4 + Real.sqrt 2) * r = ((4 + Real.sqrt 2) * r) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hge1 hα1
    have hdist := Generic.PinnedCharges.SelectionG.euclideanSiteDistance_le x₀ y₀
    have hy₀X : y₀ ∈ X := by rw [← hsuppP]; exact hy₀p
    have hsepx := hsep x₀ hx₀s y₀ hy₀X hy₀s
    have hL : ((sideLength R : ℕ) : ℝ) = 2 * R + 1 := by
      simp [sideLength]
    rw [hL] at hdist
    have hM65 : (65536 : ℝ) ≤ M := by norm_num [hMdef, chargeCoverScale]
    have hR0 : (0 : ℝ) ≤ R := by positivity
    nlinarith
  push Not at hmark
  by_cases hstr : ∃ m ∈ C, (∃ a ∈ s, m (some a) ≠ 0) ∧ ∃ b, b ∉ s ∧ m (some b) ≠ 0
  · -- a straddling member: its piece in `s` is isolated, hence near the boundary
    obtain ⟨m, hmC, ⟨a, has, ha⟩, ⟨b, hbs, hb⟩⟩ := hstr
    set ρ := siteRestrict m with hρ
    set child := chargeRestriction ρ s with hchild
    have hmF : ρ ∈ F := (siteRestrict_mem_of_mem_image (hCN hmC)).1
    have hconst : IsConstituent ρ child :=
      Generic.PinnedCharges.chargeRestriction_constituent ρ s
        ⟨a, mem_chargeSupport_siteRestrict.2 ha, has⟩
    have hsub₁ : chargeSupport child ⊆ s := fun z hz =>
      ((Generic.PinnedCharges.mem_chargeSupport_restriction_iff ρ s z).1 hz).1
    have hrest := Generic.PinnedCharges.SelectionG.chargeSupport_sub_constituent hconst
    have hne₁ : (chargeSupport child).Nonempty :=
      Generic.PinnedCharges.chargeSupport_nonempty_of_ne_zero _ hconst.1
    have hbρ : b ∈ chargeSupport ρ := mem_chargeSupport_siteRestrict.2 hb
    have hbchild : b ∉ chargeSupport child := fun h => hbs (hsub₁ h)
    have hne₂ : (chargeSupport (fun z => ρ z - child z)).Nonempty :=
      ⟨b, by rw [hrest]; exact Finset.mem_sdiff.2 ⟨hbρ, hbchild⟩⟩
    have hdist : ρr ≤ euclideanSetDistance (chargeSupport child)
        (chargeSupport (fun z => ρ z - child z)) := by
      refine Generic.PinnedCharges.SelectionG.le_setDist hne₁ hne₂ fun x hx y hy => ?_
      rw [hrest] at hy
      obtain ⟨hyρ, hyc⟩ := Finset.mem_sdiff.1 hy
      refine hsep x (hsub₁ hx) y (chargeSupport_subset_rootedMarkedSupport hn hmC hyρ) ?_
      intro hys
      exact hyc ((Generic.PinnedCharges.mem_chargeSupport_restriction_iff ρ s y).2 ⟨hys, hyρ⟩)
    have hdiam : chargeEuclideanDiameter child ≤ (4 + Real.sqrt 2) * r := by
      have h := Generic.PinnedCharges.euclideanSetDiameter_subset_le _ _ hne₁ hsne hsub₁
      change euclideanSetDiameter (chargeSupport child) ≤ _
      nlinarith
    have htrig : 2 * M * chargeEuclideanDiameter child ^ α ≤
        euclideanSetDistance (chargeSupport child) (chargeSupport (fun z => ρ z - child z)) := by
      refine le_trans ?_ hdist
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (Generic.PinnedCharges.SelectionG.diam_nonneg _) hdiam hα0.le) (by positivity)
    have hiso := (hgeo.isolated ρ hmF child hconst htrig).2
    have hb₁ := hbd _ hsub₁ hne₁
    have h := hlt _ (euclideanBoundaryDistance_nonneg _) hb₁
    change euclideanSetDistance (chargeSupport child) (chargeSupport (fun z => ρ z - child z)) ≤
      2 * M * euclideanBoundaryDistance (chargeSupport child) ^ α at hiso
    linarith
  · -- whole members only: the member adjacent to the rest of the cluster is too small
    push Not at hstr
    have hinside : ∀ m ∈ C, (∃ a ∈ s, m (some a) ≠ 0) →
        chargeSupport (siteRestrict m) ⊆ s := by
      intro m hm hmeet y hy
      by_contra hys
      exact (mem_chargeSupport_siteRestrict.1 hy) (hstr m hm hmeet y hys)
    have hx₀X : x₀ ∈ X := by rw [← hsuppP]; exact hx₀p
    obtain ⟨m₀, hm₀C, hm₀x⟩ : ∃ m ∈ C, m (some x₀) ≠ 0 := by
      rcases mem_rootedMarkedSupport.1 hx₀X with hm | h
      · rcases hm with rfl | rfl
        · exact absurd hx₀s hmark.1
        · exact absurd hx₀s hmark.2
      · exact h
    set CQ := C.filter fun m => chargeSupport (siteRestrict m) ⊆ s with hCQ
    have hm₀Q : m₀ ∈ CQ := Finset.mem_filter.2 ⟨hm₀C, hinside m₀ hm₀C ⟨x₀, hx₀s, hm₀x⟩⟩
    obtain ⟨m', hm'Q, hadj⟩ := exists_adj_sdiff_of_mem_clusters
      (rootedMarkAdjacent_monotone hM0.le hα0.le hn) hC (Finset.filter_subset _ _) ⟨m₀, hm₀Q⟩
    obtain ⟨hm'C, hm's⟩ := Finset.mem_filter.1 hm'Q
    have hY : ∀ y ∈ rootedMarkedSupport R n hn (C \ CQ), y ∈ X ∧ y ∉ s := by
      intro y hy
      refine ⟨rootedMarkedSupport_mono hn Finset.sdiff_subset hy, fun hys => ?_⟩
      rcases mem_rootedMarkedSupport.1 hy with hm | ⟨m, hm, hmy⟩
      · rcases hm with rfl | rfl
        · exact hmark.1 hys
        · exact hmark.2 hys
      · obtain ⟨hmC, hmQ⟩ := Finset.mem_sdiff.1 hm
        exact hmQ (Finset.mem_filter.2 ⟨hmC, hinside m hmC ⟨y, hys, hmy⟩⟩)
    have hne' := Generic.PinnedCharges.chargeSupport_nonempty_of_ne_zero _
      (hgeo.ensemble.1 _ (siteRestrict_mem_of_mem_image (hCN hm'C)).1)
    have hdist : ρr ≤ euclideanSetDistance (chargeSupport (siteRestrict m'))
        (rootedMarkedSupport R n hn (C \ CQ)) :=
      Generic.PinnedCharges.SelectionG.le_setDist hne' (rootedMarkedSupport_nonempty hn _)
        fun x hx y hy => hsep x (hm's hx) y (hY y hy).1 (hY y hy).2
    have hdΛ : boundaryAdjustedSize (siteRestrict m') < (4 + Real.sqrt 2) * r := by
      refine (boundaryAdjustedSize_le_max _).trans_lt (max_lt (hbd _ hm's hne') ?_)
      have h := Generic.PinnedCharges.euclideanSetDiameter_subset_le _ _ hne' hsne hm's
      change euclideanSetDiameter (chargeSupport (siteRestrict m')) < _
      have : 0 < 4 * r := by positivity
      linarith
    have hscale : rootedMarkScale R n hn m' (C \ CQ) ^ α ≤
        boundaryAdjustedSize (siteRestrict m') ^ α :=
      Real.rpow_le_rpow (rootedMarkScale_nonneg hn _ _) (min_le_left _ _) hα0.le
    have h := hlt _ (Generic.PinnedCharges.SelectionG.boundaryAdjustedSize_nonneg _) hdΛ
    unfold RootedMarkAdjacent at hadj
    nlinarith

/-- **The proxy has rejected-square neighbours** at every scale. -/
theorem hasRejectedNeighbor_rootedMarkedProxy (hn : n ≤ R) (hRn : 2 * n ≤ R)
    {F : Finset (ChargeDensity (sideLength R))}
    (hgeo : AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent F)
    {C : Finset (RotatorDualFace (sideLength R) → ℤ)}
    (hC : C ∈ clusters (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
      (F.image neutralizeAtWiredRoot))
    {T : Finset (RotatorDualFace (sideLength R) → ℤ)} (hT : T ⊆ C) :
    Generic.PinnedCharges.Rejected.HasRejectedNeighbor (chargeCoverScale : ℝ)
      chargeCoverExponent (siteRestrict (rootedMarkedProxy R n hn C T)) := by
  classical
  intro j Cv hCv hcard s hs hsout
  have hmem := Generic.PinnedCharges.mem_pinnedPPrime_of_cover_card_ne_one
    (chargeCoverScale : ℝ) chargeCoverExponent j (siteRestrict (rootedMarkedProxy R n hn C T))
    Cv hcard s
  have hα0 : (0 : ℝ) ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
  by_cases hsep : ∀ t ∈ Cv, t ≠ s → 2 * (chargeCoverScale : ℝ) *
      (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) ≤ euclideanSetDistance s t
  · have hmargin : euclideanBoundaryDistance s < 4 * (2 : ℝ) ^ j := by
      by_contra hm
      push Not at hm
      apply hsout
      refine hmem.2 ⟨hs, hsep, ?_⟩
      have : Generic.PinnedCharges.scaleBoundaryMargin j = 4 * (2 : ℝ) ^ j := by
        unfold Generic.PinnedCharges.scaleBoundaryMargin
        rw [pow_add]
        ring
      rw [this]
      exact hm
    by_contra hno
    push Not at hno
    exact rootedMarkedProxy_not_isolated_rejected hn hRn hgeo hC hT hCv hcard hs hmargin hno
  · push Not at hsep
    obtain ⟨t, ht, hts, hlt⟩ := hsep
    exact ⟨t, ht, hts, hlt.trans_le (Generic.PinnedCharges.boundarySourceThreshold_le_inflated
      (by norm_num [chargeCoverScale]) hα0 j)⟩

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
