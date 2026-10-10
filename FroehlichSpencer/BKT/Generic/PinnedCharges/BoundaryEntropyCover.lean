/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyGrouping

/-! # Coarse free-square covers of bounded groups

Coordinatewise minima statement one clipped free square around every finite set
whose coordinate spans are smaller than the target side. -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

/-- A nonempty finite site set with coordinate spans below the target side is
contained in one member of the literal free-square family. -/
theorem exists_freeSquare_covering_of_coordinateSpan_lt {L k : ℕ}
    (S : Finset (Site L)) (hS : S.Nonempty)
    (hspanX : ∀ x ∈ S, ∀ y ∈ S,
      |(x.1.val : ℝ) - y.1.val| < (squareSide k : ℝ))
    (hspanY : ∀ x ∈ S, ∀ y ∈ S,
      |(x.2.val : ℝ) - y.2.val| < (squareSide k : ℝ)) :
    ∃ q ∈ kpSquares .free L k, S ⊆ q := by
  classical
  by_cases hfits : squareSide k ≤ L
  · let X := S.image fun x : Site L => x.1.val
    let Y := S.image fun x : Site L => x.2.val
    have hX : X.Nonempty := Finset.image_nonempty.mpr hS
    have hY : Y.Nonempty := Finset.image_nonempty.mpr hS
    let xmin := X.min' hX
    let ymin := Y.min' hY
    obtain ⟨x₀, hx₀S, hx₀min⟩ := Finset.mem_image.mp (Finset.min'_mem X hX)
    obtain ⟨y₀, hy₀S, hy₀min⟩ := Finset.mem_image.mp (Finset.min'_mem Y hY)
    have hx₀val : x₀.1.val = xmin := by simpa [xmin] using hx₀min
    have hy₀val : y₀.2.val = ymin := by simpa [ymin] using hy₀min
    let a : Site L :=
      (⟨xmin, by rw [← hx₀val]; exact x₀.1.isLt⟩,
       ⟨ymin, by rw [← hy₀val]; exact y₀.2.isLt⟩)
    refine ⟨kpSquare .free L k a, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    · intro x hxS
      have hxMin : xmin ≤ x.1.val := by
        apply Finset.min'_le
        exact Finset.mem_image.mpr ⟨x, hxS, rfl⟩
      have hyMin : ymin ≤ x.2.val := by
        apply Finset.min'_le
        exact Finset.mem_image.mpr ⟨x, hxS, rfl⟩
      have hxSpan := hspanX x hxS x₀ hx₀S
      have hySpan := hspanY x hxS y₀ hy₀S
      have hxUpper : x.1.val < xmin + squareSide k := by
        have hxLowerR : (xmin : ℝ) ≤ x.1.val := by exact_mod_cast hxMin
        have hxGap : (x.1.val : ℝ) - xmin < squareSide k := by
          have hxabs := abs_lt.mp hxSpan
          rw [hx₀val] at hxabs
          exact hxabs.2
        have hxUpperR : (x.1.val : ℝ) < xmin + squareSide k := by linarith
        exact_mod_cast hxUpperR
      have hyUpper : x.2.val < ymin + squareSide k := by
        have hyLowerR : (ymin : ℝ) ≤ x.2.val := by exact_mod_cast hyMin
        have hyGap : (x.2.val : ℝ) - ymin < squareSide k := by
          have hyabs := abs_lt.mp hySpan
          rw [hy₀val] at hyabs
          exact hyabs.2
        have hyUpperR : (x.2.val : ℝ) < ymin + squareSide k := by linarith
        exact_mod_cast hyUpperR
      have hmem := (mem_kpSquare_free_iff L k hfits a x).2
      exact hmem ⟨by exact_mod_cast hxMin, hxUpper,
        by exact_mod_cast hyMin, hyUpper⟩
  · have hlarge : L < squareSide k := by omega
    obtain ⟨x, hx⟩ := hS
    refine ⟨kpSquare .free L k x, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    · intro y hy
      simp [kpSquare, hlarge]

/-- A close pair of fine squares bounds the coordinate gap between arbitrary
sites in the two squares. The two square diameters account for the endpoints,
and the set-distance bounds the bridge. -/
theorem boundaryCloseSquares_coordGap_le {L : ℕ}
    (R r : ℝ) (coord : Site L → ℝ)
    (s t : Finset (Site L)) (hs : s.Nonempty) (ht : t.Nonempty)
    (x : Site L) (hx : x ∈ s) (y : Site L) (hy : y ∈ t)
    (hwithinS : ∀ a ∈ s, ∀ b ∈ s, |coord a - coord b| ≤ r)
    (hwithinT : ∀ a ∈ t, ∀ b ∈ t, |coord a - coord b| ≤ r)
    (hcoord : ∀ a b, |coord a - coord b| ≤ euclideanSiteDistance a b)
    (hclose : IsBoundarySquareConflict R s t) :
    |coord x - coord y| ≤ 2 * r + R := by
  rcases hclose with hst | hts
  · obtain ⟨a, ha, b, hb, hab⟩ :=
      (euclideanSetDistance_lt_iff_exists_siteDistance_lt s t hs ht R).mp hst
    have hbridge := (hcoord a b).trans (le_of_lt hab)
    have htri1 := abs_sub_le (coord x) (coord a) (coord y)
    have htri2 := abs_sub_le (coord a) (coord b) (coord y)
    have hleft := hwithinS x hx a ha
    have hright := hwithinT b hb y hy
    calc
      |coord x - coord y| ≤ |coord x - coord a| + |coord a - coord y| := htri1
      _ ≤ r + (|coord a - coord b| + |coord b - coord y|) := by
        exact add_le_add hleft htri2
      _ ≤ 2 * r + R := by nlinarith [hleft, hright, hbridge]
  · obtain ⟨a, ha, b, hb, hab⟩ :=
      (euclideanSetDistance_lt_iff_exists_siteDistance_lt t s ht hs R).mp hts
    have hbridge := (hcoord a b).trans (le_of_lt hab)
    have hbridge' : |coord b - coord a| ≤ R := by
      have habs : |coord a - coord b| = |coord b - coord a| := abs_sub_comm _ _
      rw [← habs]
      exact hbridge
    have htri1 := abs_sub_le (coord x) (coord b) (coord y)
    have htri2 := abs_sub_le (coord b) (coord a) (coord y)
    have hleft := hwithinS x hx b hb
    have hright := hwithinT a ha y hy
    calc
      |coord x - coord y| ≤ |coord x - coord b| + |coord b - coord y| := htri1
      _ ≤ r + (|coord b - coord a| + |coord a - coord y|) := by
        exact add_le_add hleft htri2
      _ ≤ 2 * r + R := by nlinarith [hleft, hright, hbridge']

/-- Equality or a conflict link between two fine squares bounds every
cross-square coordinate gap by the same bridge estimate. -/
theorem boundarySquareLink_coordGap_le {L : ℕ}
    (R r : ℝ) (coord : Site L → ℝ)
    (s t : Finset (Site L)) (hs : s.Nonempty) (ht : t.Nonempty)
    (x : Site L) (hx : x ∈ s) (y : Site L) (hy : y ∈ t)
    (hwithinS : ∀ a ∈ s, ∀ b ∈ s, |coord a - coord b| ≤ r)
    (hwithinT : ∀ a ∈ t, ∀ b ∈ t, |coord a - coord b| ≤ r)
    (hcoord : ∀ a b, |coord a - coord b| ≤ euclideanSiteDistance a b)
    (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hlink : s = t ∨ IsBoundarySquareConflict R s t) :
    |coord x - coord y| ≤ 2 * r + R := by
  rcases hlink with hEq | hclose
  · subst t
    have hxy := hwithinS x hx y hy
    nlinarith [hxy, hR, hr]
  · exact boundaryCloseSquares_coordGap_le R r coord s t hs ht x hx y hy
      hwithinS hwithinT hcoord hclose

/-- Every group has coordinate spans bounded by three conflict bridges and
the four fine-square spans. -/
theorem boundaryGroup_coordSpan_le {L : ℕ}
    (Q V : Finset (Finset (Site L))) (M : Finset (Finset (Finset (Site L))))
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M)
    (i : BoundaryGroupIndex Q M) (R r : ℝ) (coord : Site L → ℝ)
    (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hwithin : ∀ s ∈ boundaryGroup Q V M owner i,
      ∀ a ∈ s, ∀ b ∈ s, |coord a - coord b| ≤ r)
    (hnonempty : ∀ s ∈ boundaryGroup Q V M owner i, s.Nonempty)
    (hlinks : ∀ s ∈ boundaryGroup Q V M owner i,
      ∃ a ∈ boundaryGroupBase Q M i, s = a ∨ IsBoundarySquareConflict R s a)
    (hbase : ∀ a ∈ boundaryGroupBase Q M i, ∀ b ∈ boundaryGroupBase Q M i,
      a = b ∨ IsBoundarySquareConflict R a b)
    (hcoord : ∀ a b, |coord a - coord b| ≤ euclideanSiteDistance a b)
    {x y : Site L} (hx : x ∈ (boundaryGroup Q V M owner i).biUnion id)
    (hy : y ∈ (boundaryGroup Q V M owner i).biUnion id) :
    |coord x - coord y| ≤ 6 * r + 3 * R := by
  classical
  obtain ⟨s, hsG, hxS⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨t, htG, hyT⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨a, haBase, hsa⟩ := hlinks s hsG
  obtain ⟨b, hbBase, htb⟩ := hlinks t htG
  have haG : a ∈ boundaryGroup Q V M owner i := Finset.mem_union.mpr (Or.inl haBase)
  have hbG : b ∈ boundaryGroup Q V M owner i := Finset.mem_union.mpr (Or.inl hbBase)
  obtain ⟨u, hu⟩ := hnonempty a haG
  obtain ⟨v, hv⟩ := hnonempty b hbG
  have hxa : |coord x - coord u| ≤ 2 * r + R :=
    boundarySquareLink_coordGap_le R r coord s a (hnonempty s hsG)
      (hnonempty a haG) x hxS u hu (hwithin s hsG) (hwithin a haG)
      hcoord hR hr hsa
  have huv : |coord u - coord v| ≤ 2 * r + R :=
    boundarySquareLink_coordGap_le R r coord a b (hnonempty a haG)
      (hnonempty b hbG) u hu v hv (hwithin a haG) (hwithin b hbG)
      hcoord hR hr (hbase a haBase b hbBase)
  have hby : |coord v - coord y| ≤ 2 * r + R := by
    have := boundarySquareLink_coordGap_le R r coord t b (hnonempty t htG)
      (hnonempty b hbG) y hyT v hv (hwithin t htG) (hwithin b hbG)
      hcoord hR hr htb
    simpa [abs_sub_comm] using this
  have htri1 := abs_sub_le (coord x) (coord u) (coord y)
  have htri2 := abs_sub_le (coord u) (coord v) (coord y)
  have hvy : |coord v - coord y| ≤ 2 * r + R := hby
  calc
    |coord x - coord y| ≤ |coord x - coord u| + |coord u - coord y| := htri1
    _ ≤ (2 * r + R) + (|coord u - coord v| + |coord v - coord y|) := by
      exact add_le_add hxa htri2
    _ ≤ 6 * r + 3 * R := by nlinarith [hxa, huv, hvy]

/-- One matching group fits inside one coarse clipped free square once its
three-bridge coordinate bound is below the target side. -/
theorem boundaryGroup_has_one_coarseSquare {L j k : ℕ}
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C)
    (Q V : Finset (Finset (Site L)))
    (M : Finset (Finset (Finset (Site L)))) (R : ℝ)
    (hQ : Q ⊆ C) (hV : V ⊆ C)
    (hmatch : IsBoundaryConflictMatching V (IsBoundarySquareConflict R) M)
    (hneighbor : ∀ x ∈ boundaryUnmatchedVertices V M,
      ∃ y ∈ Q ∪ boundaryConflictMatchedVertices M,
        IsBoundarySquareConflict R x y)
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M)
    (hownerDef : ∀ x, owner x =
      boundaryGroupOwner Q V M (IsBoundarySquareConflict R) hneighbor x)
    {i : BoundaryGroupIndex Q M} (hi : i ∈ boundaryGroupIndices Q M)
    (hR : 0 ≤ R)
    (hscale : 6 * (2 : ℝ) ^ j + 3 * R < (2 : ℝ) ^ k) :
    ∃ q ∈ kpSquares .free L k,
      (boundaryGroup Q V M owner i).biUnion id ⊆ q := by
  classical
  let G := boundaryGroup Q V M owner i
  have hGsub : G ⊆ C :=
    boundaryGroup_subset_of_partition C Q V M hQ hV hmatch owner i
  have hsquare : ∀ s ∈ G, s ∈ kpSquares .free L j := by
    intro s hs
    exact hC.1.1 (hGsub hs)
  have hnonempty : ∀ s ∈ G, s.Nonempty := by
    intro s hs
    obtain ⟨x, hxρ, hxs, -⟩ :=
      minimumCover_square_has_private_support_site j ρ C hC (hGsub hs)
    exact ⟨x, hxs⟩
  have hwithin : ∀ s ∈ G, ∀ a ∈ s, ∀ b ∈ s,
      |(a.1.val : ℝ) - b.1.val| ≤ (2 : ℝ) ^ j := by
    intro s hs a ha b hb
    simpa [squareSide] using
      (freeSquare_coordDiff_le_of_mem (hsquare s hs) a b ha hb).1
  have hwithinY : ∀ s ∈ G, ∀ a ∈ s, ∀ b ∈ s,
      |(a.2.val : ℝ) - b.2.val| ≤ (2 : ℝ) ^ j := by
    intro s hs a ha b hb
    simpa [squareSide] using
      (freeSquare_coordDiff_le_of_mem (hsquare s hs) a b ha hb).2
  have hlinks : ∀ s ∈ G,
      ∃ a ∈ boundaryGroupBase Q M i,
        s = a ∨ IsBoundarySquareConflict R s a := by
    intro s hs
    exact boundaryGroup_member_link_to_base Q V M (IsBoundarySquareConflict R)
      hneighbor owner hownerDef i hs
  have hbase : ∀ a ∈ boundaryGroupBase Q M i,
      ∀ b ∈ boundaryGroupBase Q M i,
        a = b ∨ IsBoundarySquareConflict R a b := by
    intro a ha b hb
    exact boundaryGroupBase_pair_eq_or_conflict Q V M hmatch i ha hb
  have hcoord : ∀ a b : Site L,
      |(a.1.val : ℝ) - b.1.val| ≤ euclideanSiteDistance a b :=
    fun a b => (euclideanSiteDistance_coordDiff_le a b).1
  have hcoordY : ∀ a b : Site L,
      |(a.2.val : ℝ) - b.2.val| ≤ euclideanSiteDistance a b :=
    fun a b => (euclideanSiteDistance_coordDiff_le a b).2
  have hr : 0 ≤ (2 : ℝ) ^ j := by positivity
  have hGnonempty : G.Nonempty := by
    simpa [G] using boundaryGroup_nonempty_of_validIndex Q V M hmatch owner hi
  let S := G.biUnion id
  have hS : S.Nonempty := by
    obtain ⟨s, hs⟩ := hGnonempty
    obtain ⟨x, hx⟩ := hnonempty s hs
    exact ⟨x, Finset.mem_biUnion.mpr ⟨s, hs, hx⟩⟩
  have hspanX : ∀ x ∈ S, ∀ y ∈ S,
      |(x.1.val : ℝ) - y.1.val| < (squareSide k : ℝ) := by
    intro x hx y hy
    have hbound := boundaryGroup_coordSpan_le (L := L) Q V M owner i R
      ((2 : ℝ) ^ j) (fun z => (z.1.val : ℝ)) hR hr hwithin hnonempty
      hlinks hbase hcoord hx hy
    have hlt := lt_of_le_of_lt hbound hscale
    simpa [squareSide] using hlt
  have hspanY : ∀ x ∈ S, ∀ y ∈ S,
      |(x.2.val : ℝ) - y.2.val| < (squareSide k : ℝ) := by
    intro x hx y hy
    have hbound := boundaryGroup_coordSpan_le (L := L) Q V M owner i R
      ((2 : ℝ) ^ j) (fun z => (z.2.val : ℝ)) hR hr hwithinY hnonempty
      hlinks hbase hcoordY hx hy
    have hlt := lt_of_le_of_lt hbound hscale
    simpa [squareSide] using hlt
  obtain ⟨q, hq, hSsub⟩ :=
    exists_freeSquare_covering_of_coordinateSpan_lt S hS hspanX hspanY
  exact ⟨q, hq, by simpa [G, S] using hSsub⟩

/-- Any finite family of bounded groups that covers a charge support induces
one coarse free square per group and hence a coarse cover with no more squares
than groups. -/
theorem exists_coarseCover_of_boundedGroupFamily {L k : ℕ}
    (ρ : ChargeDensity L) (G : Finset (Finset (Finset (Site L))))
    (hcover : ∀ x ∈ chargeSupport ρ,
      ∃ g ∈ G, ∃ s ∈ g, x ∈ s)
    (hcoarse : ∀ g ∈ G, ∃ q ∈ kpSquares .free L k, g.biUnion id ⊆ q) :
    ∃ D, IsSquareCover .free L k ρ D ∧ D.card ≤ G.card := by
  classical
  let chooseSquare : Finset (Finset (Site L)) → Finset (Site L) := fun g =>
    if hg : g ∈ G then Classical.choose (hcoarse g hg) else ∅
  have chooseSquare_spec : ∀ g ∈ G,
      chooseSquare g ∈ kpSquares .free L k ∧ g.biUnion id ⊆ chooseSquare g := by
    intro g hg
    simpa [chooseSquare, hg] using Classical.choose_spec (hcoarse g hg)
  let D := G.image chooseSquare
  refine ⟨D, ?_, ?_⟩
  · constructor
    · intro q hq
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hq
      exact (chooseSquare_spec g hg).1
    · intro x hx
      obtain ⟨g, hg, s, hs, hxs⟩ := hcover x hx
      refine ⟨chooseSquare g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, ?_⟩
      exact (chooseSquare_spec g hg).2 (Finset.mem_biUnion.mpr ⟨s, hs, hxs⟩)
  · simpa [D] using Finset.card_image_le

/-- The matching groups give a coarse cover with cardinality at most the
core size plus half the non-core size. -/
theorem exists_coarseCover_of_boundaryGroups {L j k : ℕ}
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C)
    (Q V : Finset (Finset (Site L))) (M : Finset (Finset (Finset (Site L))))
    (R : ℝ) (hR : 0 ≤ R)
    (hQ : Q ⊆ C) (hV : V ⊆ C)
    (hmatch : IsBoundaryConflictMatching V (IsBoundarySquareConflict R) M)
    (hneighbor : ∀ x ∈ boundaryUnmatchedVertices V M,
      ∃ y ∈ Q ∪ boundaryConflictMatchedVertices M,
        IsBoundarySquareConflict R x y)
    (owner : {x // x ∈ boundaryUnmatchedVertices V M} → BoundaryGroupIndex Q M)
    (hownerDef : ∀ x, owner x =
      boundaryGroupOwner Q V M (IsBoundarySquareConflict R) hneighbor x)
    (hcoverGroups : ∀ s ∈ C,
      ∃ G ∈ boundaryGroupFamily Q V M owner, s ∈ G)
    (hscale : 6 * (2 : ℝ) ^ j + 3 * R < (2 : ℝ) ^ k) :
    ∃ D, IsSquareCover .free L k ρ D ∧ D.card ≤ Q.card + V.card / 2 := by
  classical
  let G := boundaryGroupFamily Q V M owner
  have hgroupCoarse : ∀ g ∈ G,
      ∃ q ∈ kpSquares .free L k, g.biUnion id ⊆ q := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    exact boundaryGroup_has_one_coarseSquare ρ C hC Q V M R hQ hV hmatch
      hneighbor owner hownerDef hi hR hscale
  have hcover : ∀ x ∈ chargeSupport ρ, ∃ g ∈ G, ∃ s ∈ g, x ∈ s := by
    intro x hx
    obtain ⟨s, hsC, hxs⟩ := hC.1.2 x hx
    obtain ⟨g, hg, hsg⟩ := hcoverGroups s hsC
    exact ⟨g, hg, s, hsg, hxs⟩
  obtain ⟨D, hD, hDcard⟩ := exists_coarseCover_of_boundedGroupFamily ρ G hcover hgroupCoarse
  refine ⟨D, hD, ?_⟩
  calc
    D.card ≤ G.card := hDcard
    _ ≤ Q.card + V.card / 2 := by
      exact boundaryGroupFamily_card_le_half Q V M hmatch owner

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
