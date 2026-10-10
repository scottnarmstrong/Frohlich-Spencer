/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryIsolationNeighbor
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds

/-! # Literal square geometry for the boundary entropy argument

This module derives the fine-square diameter used by the isolation lemma from
the actual clipped `kpSquares .free` carrier. It also records the elementary
threshold comparison needed to use the Appendix D selected family as the
retained core.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

private theorem euclideanSiteDistance_le_sqrt_two_mul_of_coord_diff
    {L : ℕ} (x y : Site L) (r : ℝ)
    (hx : |(x.1.val : ℝ) - y.1.val| ≤ r)
    (hy : |(x.2.val : ℝ) - y.2.val| ≤ r) (hr : 0 ≤ r) :
    euclideanSiteDistance x y ≤ Real.sqrt 2 * r := by
  have hdx : ((x.1.val : ℝ) - y.1.val) ^ 2 ≤ r ^ 2 := by
    nlinarith [abs_le.mp hx]
  have hdy : ((x.2.val : ℝ) - y.2.val) ^ 2 ≤ r ^ 2 := by
    nlinarith [abs_le.mp hy]
  have hsum :
      ((x.1.val : ℝ) - y.1.val) ^ 2 + ((x.2.val : ℝ) - y.2.val) ^ 2 ≤
        2 * r ^ 2 := by nlinarith
  calc
    euclideanSiteDistance x y ≤ Real.sqrt (2 * r ^ 2) := by
      unfold euclideanSiteDistance
      exact Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * r := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hr]

/-- Each coordinate gap is bounded by Euclidean distance. -/
theorem euclideanSiteDistance_coordDiff_le {L : ℕ} (x y : Site L) :
    |(x.1.val : ℝ) - y.1.val| ≤ euclideanSiteDistance x y ∧
    |(x.2.val : ℝ) - y.2.val| ≤ euclideanSiteDistance x y := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs ((x.1.val : ℝ) - y.1.val), sq_nonneg ((x.2.val : ℝ) - y.2.val)]
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs ((x.2.val : ℝ) - y.2.val), sq_nonneg ((x.1.val : ℝ) - y.1.val)]

/-- A strict set-distance bound is witnessed by a pair of sites attaining the
finite minimum. -/
theorem euclideanSetDistance_lt_iff_exists_siteDistance_lt {L : ℕ}
    (s t : Finset (Site L)) (hs : s.Nonempty) (ht : t.Nonempty) (R : ℝ) :
    euclideanSetDistance s t < R ↔
      ∃ x ∈ s, ∃ y ∈ t, euclideanSiteDistance x y < R := by
  have hprod : (s.product t).Nonempty := by
    obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ := ht
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  let distances := (s.product t).image fun p : Site L × Site L =>
    euclideanSiteDistance p.1 p.2
  have hdistances : distances.Nonempty := Finset.image_nonempty.mpr hprod
  constructor
  · intro h
    have hmin : distances.min' hdistances < R := by
      unfold euclideanSetDistance at h
      rw [dite_eq_left hprod] at h
      simpa [distances] using h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp (Finset.min'_mem distances hdistances)
    have hdist : euclideanSiteDistance p.1 p.2 < R := by rw [heq]; exact hmin
    exact ⟨p.1, (Finset.mem_product.mp hp).1, p.2,
      (Finset.mem_product.mp hp).2, hdist⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hle : euclideanSetDistance s t ≤ euclideanSiteDistance x y := by
      unfold euclideanSetDistance
      rw [dite_eq_left hprod]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr
        ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩)
    exact lt_of_le_of_lt hle hxy

theorem freeSquare_coordDiff_le_of_mem {L j : ℕ}
    {s : Finset (Site L)} (hs : s ∈ kpSquares .free L j)
    (x y : Site L) (hx : x ∈ s) (hy : y ∈ s) :
    |(x.1.val : ℝ) - y.1.val| ≤ (squareSide j : ℝ) ∧
    |(x.2.val : ℝ) - y.2.val| ≤ (squareSide j : ℝ) := by
  rcases Finset.mem_image.mp hs with ⟨a, -, rfl⟩
  by_cases hside : squareSide j ≤ L
  · have hmem := mem_kpSquare_free_iff L j hside a
    have hxm := (hmem x).mp hx
    have hym := (hmem y).mp hy
    have hdxNat : x.1.val ≤ y.1.val + squareSide j ∧
        y.1.val ≤ x.1.val + squareSide j := by omega
    have hdyNat : x.2.val ≤ y.2.val + squareSide j ∧
        y.2.val ≤ x.2.val + squareSide j := by omega
    have hrealx1 : (x.1.val : ℝ) ≤ (y.1.val : ℝ) + squareSide j := by
      exact_mod_cast hdxNat.1
    have hrealx2 : (y.1.val : ℝ) ≤ (x.1.val : ℝ) + squareSide j := by
      exact_mod_cast hdxNat.2
    have hrealy1 : (x.2.val : ℝ) ≤ (y.2.val : ℝ) + squareSide j := by
      exact_mod_cast hdyNat.1
    have hrealy2 : (y.2.val : ℝ) ≤ (x.2.val : ℝ) + squareSide j := by
      exact_mod_cast hdyNat.2
    constructor
    · rw [abs_le]
      constructor
      · linarith
      · linarith
    · rw [abs_le]
      constructor
      · linarith
      · linarith
  · have hlarge : L < squareSide j := by omega
    have hx1 : x.1.val < L := x.1.isLt
    have hy1 : y.1.val < L := y.1.isLt
    have hx2 : x.2.val < L := x.2.isLt
    have hy2 : y.2.val < L := y.2.isLt
    have hcoord (u v : ℕ) (hu : u < L) (hv : v < L) :
        |(u : ℝ) - v| ≤ (squareSide j : ℝ) := by
      have hnat : u ≤ v + squareSide j ∧ v ≤ u + squareSide j := by omega
      have hreal1 : (u : ℝ) ≤ (v : ℝ) + squareSide j := by
        exact_mod_cast hnat.1
      have hreal2 : (v : ℝ) ≤ (u : ℝ) + squareSide j := by
        exact_mod_cast hnat.2
      rw [abs_le]
      constructor <;> linarith
    exact ⟨hcoord x.1.val y.1.val hx1 hy1,
      hcoord x.2.val y.2.val hx2 hy2⟩

/-- Every literal free `kpSquare` has Euclidean diameter at most the diagonal
of its nominal side. The proof includes the clipped full-box case when the
nominal side is larger than `L`. -/
theorem euclideanSetDiameter_le_sqrt_two_squareSide {L j : ℕ}
    {s : Finset (Site L)} (hs : s ∈ kpSquares .free L j) :
    euclideanSetDiameter s ≤ Real.sqrt 2 * (squareSide j : ℝ) := by
  classical
  by_cases hprod : (s.product s).Nonempty
  · rw [euclideanSetDiameter, dite_eq_left hprod]
    apply Finset.max'_le
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
    obtain ⟨hcoordx, hcoordy⟩ := freeSquare_coordDiff_le_of_mem hs p.1 p.2 hx hy
    exact euclideanSiteDistance_le_sqrt_two_mul_of_coord_diff p.1 p.2
      (squareSide j : ℝ) hcoordx hcoordy (by positivity)
  · rw [euclideanSetDiameter, dite_eq_right hprod]
    positivity

/-- The elementary diameter hypothesis required by the isolation-neighbor
lemma follows from membership in the actual scale-`j` free-square carrier. -/
theorem freeSquare_euclideanDiameter_le {L j : ℕ}
    {s : Finset (Site L)} (hs : s ∈ kpSquares .free L j) :
    euclideanSetDiameter s ≤ Real.sqrt 2 * (2 : ℝ) ^ j := by
  simpa [squareSide] using euclideanSetDiameter_le_sqrt_two_squareSide hs

/-- The enlarged isolation radius dominates the Appendix D pair-separation
threshold at the fine scale. -/
theorem boundarySourceThreshold_le_inflated {M α : ℝ} (hM : 0 ≤ M)
    (hα : 0 ≤ α) (j : ℕ) :
    2 * M * (2 : ℝ) ^ (α * (j : ℝ)) ≤
      2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α := by
  have hscale : (2 : ℝ) ^ (α * (j : ℝ)) = ((2 : ℝ) ^ j) ^ α := by
    calc
      (2 : ℝ) ^ (α * (j : ℝ)) = (2 : ℝ) ^ ((j : ℝ) * α) := by
        congr 1
        ring
      _ = ((2 : ℝ) ^ j) ^ α := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ j := by positivity
  have hfactor : (2 : ℝ) ^ j ≤ (4 + Real.sqrt 2) * (2 : ℝ) ^ j := by
    have hfour : 1 ≤ 4 + Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    nlinarith
  rw [hscale]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hbase hfactor hα) (by positivity)

/-- When the minimum cover has at least two squares, every fine square outside
the literal Appendix D selected family has a close cover neighbor. A rejected
separation test gives a neighbor immediately; a rejected boundary margin is
handled by `HasBoundaryIsolation`. -/
theorem boundaryPPrime_complement_has_close_neighbor
    {L j : ℕ} (M α : ℝ) (hM : 0 < M) (hα : 0 < α)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hcard : C.card ≠ 1)
    {s : Finset (Site L)} (hs : s ∈ C)
    (hsout : s ∉ pinnedPPrime M α j ρ C) :
    ∃ t ∈ C, t ≠ s ∧ euclideanSetDistance s t <
      2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α := by
  have hmem := (mem_pinnedPPrime_of_cover_card_ne_one M α j ρ C hcard s)
  have hnot : ¬ ((∀ t ∈ C, t ≠ s →
        2 * M * (2 : ℝ) ^ (α * (j : ℝ)) ≤ euclideanSetDistance s t) ∧
      scaleBoundaryMargin j ≤ euclideanBoundaryDistance s) := by
    intro h
    exact hsout (hmem.mpr ⟨hs, h⟩)
  by_cases hsep : ∀ t ∈ C, t ≠ s →
      2 * M * (2 : ℝ) ^ (α * (j : ℝ)) ≤ euclideanSetDistance s t
  · have hmargin : ¬ scaleBoundaryMargin j ≤ euclideanBoundaryDistance s := by
      intro hm
      exact hnot ⟨hsep, hm⟩
    have hmargin' : euclideanBoundaryDistance s < 4 * (2 : ℝ) ^ j := by
      have hscale : scaleBoundaryMargin j = 4 * (2 : ℝ) ^ j := by
        unfold scaleBoundaryMargin
        rw [pow_add]
        norm_num
        ring
      rw [hscale] at hmargin
      exact lt_of_not_ge hmargin
    obtain ⟨t, ht, hts, hdist⟩ :=
      boundaryIsolation_rejectedSquare_has_close_neighbor_of_minimumCover
        M α ((2 : ℝ) ^ j) hM hα (by positivity) ρ N hN hρ C hC hs hcard hmargin'
        (freeSquare_euclideanDiameter_le (hC.1.1 hs))
    exact ⟨t, ht, hts, hdist⟩
  · have hsmall : ∃ t ∈ C, t ≠ s ∧
        ¬ (2 * M * (2 : ℝ) ^ (α * (j : ℝ)) ≤ euclideanSetDistance s t) := by
      by_contra hn
      apply hsep
      intro t ht hts
      by_contra hnotle
      exact hn ⟨t, ht, hts, hnotle⟩
    obtain ⟨t, ht, hts, hnotle⟩ := hsmall
    have hdist : euclideanSetDistance s t <
        2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α := by
      calc
        euclideanSetDistance s t < 2 * M * (2 : ℝ) ^ (α * (j : ℝ)) :=
          lt_of_not_ge hnotle
        _ ≤ 2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α :=
          boundarySourceThreshold_le_inflated (le_of_lt hM) (le_of_lt hα) j
    exact ⟨t, ht, hts, hdist⟩

private theorem singletonCover_supportDiameter_le {L j : ℕ}
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hsingle : C.card = 1)
    (hρ : ρ ≠ 0) :
    chargeEuclideanDiameter ρ ≤ Real.sqrt 2 * (2 : ℝ) ^ j := by
  classical
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hsingle
  have hsC : s ∈ C := by simp [hs]
  have hsub : chargeSupport ρ ⊆ s := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hC.1.2 x hx
    rw [hs] at ht
    simp only [Finset.mem_singleton] at ht
    simpa [ht] using hxt
  have hsupport : (chargeSupport ρ).Nonempty :=
    chargeSupport_nonempty_of_ne_zero ρ hρ
  have hsNonempty : s.Nonempty := hsupport.mono hsub
  have hdiam := euclideanSetDiameter_subset_le (chargeSupport ρ) s
    hsupport hsNonempty hsub
  calc
    chargeEuclideanDiameter ρ = euclideanSetDiameter (chargeSupport ρ) := rfl
    _ ≤ euclideanSetDiameter s := hdiam
    _ ≤ Real.sqrt 2 * (2 : ℝ) ^ j :=
      freeSquare_euclideanDiameter_le (hC.1.1 hsC)

/-- A neutral nonzero charge cannot have a one-square minimum cover on the
cutoff range `16·2^j ≤ d_Λ(ρ)`. This is the singleton-retention dichotomy's
neutral branch. -/
theorem neutralSingletonCover_impossible_below_cutoff {L j : ℕ}
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hsingle : C.card = 1)
    (hρ : ρ ≠ 0) (hneutral : totalCharge ρ = 0)
    (hcutoff : 16 * (2 : ℝ) ^ j ≤ boundaryAdjustedSize ρ) : False := by
  have hdiam := singletonCover_supportDiameter_le ρ C hC hsingle hρ
  have hscale : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hsqrt : Real.sqrt 2 < 16 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [boundaryAdjustedSize_of_neutral ρ hneutral] at hcutoff
  exact (not_lt_of_ge hcutoff)
    (lt_of_le_of_lt hdiam (by nlinarith [hscale, hsqrt]))

/-- In the charged branch, a one-square minimum cover on the cutoff range is
retained by the source's Appendix D singleton exception. -/
theorem chargedSingletonCover_retained_below_cutoff {L j : ℕ} (M α : ℝ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hsingle : C.card = 1)
    (hρ : ρ ≠ 0) (hcharged : totalCharge ρ ≠ 0)
    (hcutoff : 16 * (2 : ℝ) ^ j ≤ boundaryAdjustedSize ρ) :
    singletonBoundaryMargin j ≤ chargeBoundaryDistance ρ ∧
      pinnedPPrime M α j ρ C = C := by
  have hdiam := singletonCover_supportDiameter_le ρ C hC hsingle hρ
  have hscale : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hsqrt : Real.sqrt 2 < 16 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [boundaryAdjustedSize_of_charged ρ hcharged] at hcutoff
  have hmargin : 8 * (2 : ℝ) ^ j ≤ chargeBoundaryDistance ρ := by
    by_contra hnot
    have hδ : chargeBoundaryDistance ρ < 8 * (2 : ℝ) ^ j := lt_of_not_ge hnot
    have hdiam' : chargeEuclideanDiameter ρ < 16 * (2 : ℝ) ^ j := by
      nlinarith [hdiam, hscale, hsqrt]
    have hmax : max (chargeBoundaryDistance ρ) (chargeEuclideanDiameter ρ) <
        16 * (2 : ℝ) ^ j := max_lt_iff.mpr ⟨by nlinarith [hδ, hscale], hdiam'⟩
    exact (not_lt_of_ge hcutoff) hmax
  have hmargin' : singletonBoundaryMargin j ≤ chargeBoundaryDistance ρ := by
    have hEq : singletonBoundaryMargin j = 8 * (2 : ℝ) ^ j := by
      unfold singletonBoundaryMargin
      rw [pow_add]
      norm_num
      ring
    rw [hEq]
    exact hmargin
  exact ⟨hmargin', pinnedPPrime_eq_self_of_singleton_exception
    M α j ρ C hsingle hcharged hmargin'⟩

/-- The diameter premise is no longer external when applying the rejected
square isolation lemma to an actual minimum free-square cover. -/
theorem boundaryIsolation_rejectedSquare_has_close_neighbor_of_minimumCover_auto
    {L j : ℕ} (M α : ℝ) (hM : 0 < M) (hα : 0 < α)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C)
    {s : Finset (Site L)} (hs : s ∈ C) (hsingle : C.card ≠ 1)
    (hmargin : euclideanBoundaryDistance s < 4 * (2 : ℝ) ^ j) :
    ∃ t ∈ C, t ≠ s ∧ euclideanSetDistance s t <
      2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α := by
  exact boundaryIsolation_rejectedSquare_has_close_neighbor_of_minimumCover
    M α ((2 : ℝ) ^ j) hM hα (by positivity) ρ N hN hρ C hC hs hsingle
    hmargin (freeSquare_euclideanDiameter_le (hC.1.1 hs))

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
