/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerAssembly
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyApplication
import Mathlib.Tactic

/-!
# The Appendix D entropy estimate from rejected-square neighbours (D2G3b)

The finite-volume entropy estimate `pinned_boundary_entropy_chargeCutoff` and the cover-cost
bound `layerA_le` are stated for densities with Appendix D isolation (`HasBoundaryIsolation`).
Their proofs use isolation at one point only: every square of a nonsingleton minimum cover
outside the selected family `P'_j` has another cover square within the inflated radius
`2M((4 + √2)2^j)^α` (`boundaryPPrime_complement_has_close_neighbor`). This file isolates that
property as `HasRejectedNeighbor` and repeats the entropy chain under it. The proofs are those of
`BoundaryEntropyGrouping`, `BoundaryEntropyRecurrence`, `BoundaryEntropyApplication` and
`LayerAssembly`; only the hypothesis is weakened.

* `hasRejectedNeighbor_of_isolation`: isolation implies the property;
* `rejected_boundary_entropy_chargeCutoff`: the entropy estimate through the charge cutoff;
* **`layerCoverSum_le_of_rejected`**: `A_cover(ϱ) ≤ (29 + |C_T|) ‖ϱ|faces‖₁ + (196/3) |P'|`.

The rooted marked proxy has the property without being isolated
(`MarkedGeometryBudgetProxy.lean`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Rejected

open FroehlichSpencer.BKT

/-- **Rejected squares have close neighbours**: in every nonsingleton minimum cover, every square
outside the Appendix D selected family has another cover square within the inflated radius. -/
def HasRejectedNeighbor {L : ℕ} (M α : ℝ) (ρ : ChargeDensity L) : Prop :=
  ∀ (j : ℕ) (C : Finset (Finset (Site L))), IsMinimumSquareCover .free L j ρ C → C.card ≠ 1 →
    ∀ s ∈ C, s ∉ pinnedPPrime M α j ρ C →
      ∃ t ∈ C, t ≠ s ∧ euclideanSetDistance s t <
        2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α

/-- Appendix D isolation gives rejected-square neighbours. -/
theorem hasRejectedNeighbor_of_isolation {L : ℕ} {M α : ℝ} (hM : 0 < M) (hα : 0 < α)
    {N : Finset (ChargeDensity L)} (hN : HasBoundaryIsolation M α N) {ρ : ChargeDensity L}
    (hρ : ρ ∈ N) : HasRejectedNeighbor M α ρ :=
  fun _ C hC hcard _ hs hsout =>
    boundaryPPrime_complement_has_close_neighbor M α hM hα ρ N hN hρ C hC hcard hs hsout

/-- The Appendix D selected family is an independent core. `HasRejectedNeighbor` gives a
close neighbor for every rejected square, and a maximum matching plus the
owner construction groups all cover squares with at most
`|P'_j| + |V_j|/2` groups. -/
theorem exists_boundaryPPrime_matching_groups_of_rejected {L j : ℕ}
    (M α : ℝ)
    (ρ : ChargeDensity L) (hrej : HasRejectedNeighbor M α ρ)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hcard : C.card ≠ 1) :
    let Q := pinnedPPrime M α j ρ C
    let V := C \ Q
    ∃ (matching : Finset (Finset (Finset (Site L))))
      (owner : {x // x ∈ boundaryUnmatchedVertices V matching} →
        BoundaryGroupIndex Q matching),
      IsBoundaryConflictMatching V (IsBoundarySquareConflict
        (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α)) matching ∧
      (∃ hneighbor : ∀ x ∈ boundaryUnmatchedVertices V matching,
          ∃ y ∈ Q ∪ boundaryConflictMatchedVertices matching,
            IsBoundarySquareConflict
              (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α) x y,
        owner = boundaryGroupOwner Q V matching
          (IsBoundarySquareConflict
            (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α)) hneighbor ∧
        (∀ x ∈ C, ∃ G ∈ boundaryGroupFamily Q V matching owner, x ∈ G) ∧
        (boundaryGroupFamily Q V matching owner).card ≤ Q.card + V.card / 2) := by
  classical
  dsimp
  let Q := pinnedPPrime M α j ρ C
  let V := C \ Q
  let R := 2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α
  have hQsub : Q ⊆ C := pinnedPPrime_subset_cover M α j ρ C
  have hCV : C = Q ∪ V := by
    ext x
    simp only [V, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hq : x ∈ Q
      · exact Or.inl hq
      · exact Or.inr ⟨hx, hq⟩
    · rintro (hq | ⟨hc, _⟩)
      · exact hQsub hq
      · exact hc
  let conflict : Finset (Site L) → Finset (Site L) → Prop :=
    IsBoundarySquareConflict R
  have hsymm : ∀ x y, conflict x y → conflict y x := by
    intro x y hxy
    exact boundarySquareConflict_symmetric R x y hxy
  have hclose : ∀ s ∈ V, ∃ t ∈ C, t ≠ s ∧ conflict s t := by
    intro s hs
    have hsC : s ∈ C := (Finset.mem_sdiff.mp hs).1
    have hsQ : s ∉ Q := (Finset.mem_sdiff.mp hs).2
    obtain ⟨t, ht, hts, hdist⟩ :=
      hrej j C hC hcard s hsC hsQ
    exact ⟨t, ht, hts, Or.inl hdist⟩
  obtain ⟨matching, hmatching, hmax, _hmatchingCard⟩ :=
    exists_maximumBoundaryConflictMatching V conflict hsymm
  have hneighbor : ∀ x ∈ boundaryUnmatchedVertices V matching,
      ∃ y ∈ Q ∪ boundaryConflictMatchedVertices matching, conflict x y := by
    intro x hx
    have hxV : x ∈ V := (Finset.mem_sdiff.mp hx).1
    have hxUnmatched : x ∉ boundaryConflictMatchedVertices matching :=
      (Finset.mem_sdiff.mp hx).2
    obtain ⟨y, hy, hxy⟩ :=
      unmatchedBoundaryConflictNeighbor_mem_core_or_matched C Q V conflict hCV
        matching hmax hclose (x := x) hxV hxUnmatched
    exact ⟨y, hy, hxy⟩
  let owner := boundaryGroupOwner Q V matching conflict hneighbor
  have howner : ∀ x (hx : x ∈ boundaryUnmatchedVertices V matching),
      owner ⟨x, hx⟩ ∈ boundaryGroupIndices Q matching := by
    intro x hx
    exact boundaryGroupOwner_mem_indices Q V matching conflict hneighbor ⟨x, hx⟩
  have hcover := boundaryGroupFamily_covers_of_partition C Q V matching hCV owner howner
  have hgroups := boundaryGroupFamily_card_le_half Q V matching hmatching owner
  exact ⟨matching, owner, hmatching, hneighbor, rfl, hcover, hgroups⟩


/-- The minimum free-square cover numbers obey the Appendix-D one-step
recurrence under the explicit scale inequality and cutoff. -/
theorem boundarySquareCoverNumber_recurrence_of_rejected {L j k : ℕ}
    (M α : ℝ) (hM : 0 < M)
    (ρ : ChargeDensity L) (hrej : HasRejectedNeighbor M α ρ)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C)
    (hneutral : totalCharge ρ = 0)
    (hcutoff : 16 * (2 : ℝ) ^ j ≤ boundaryAdjustedSize ρ)
    (hscale : 6 * (2 : ℝ) ^ j +
      3 * (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α) < (2 : ℝ) ^ k) :
    squareCoverNumber .free L k ρ ≤
      squareCoverNumber .free L j ρ / 2 +
        (pinnedPPrime M α j ρ C).card := by
  classical
  have hCcard : C.card = squareCoverNumber .free L j ρ :=
    card_eq_squareCoverNumber_of_isMinimumSquareCover .free L j ρ C hC
  have hρne : ρ ≠ 0 := by
    intro hzero
    rw [boundaryAdjustedSize_of_neutral ρ hneutral] at hcutoff
    have hdiam : chargeEuclideanDiameter ρ = 0 := by
      simp [chargeEuclideanDiameter, euclideanSetDiameter, hzero, chargeSupport]
    rw [hdiam] at hcutoff
    have hpos : 0 < (16 : ℝ) * (2 : ℝ) ^ j := by positivity
    linarith
  have hnotSingle : C.card ≠ 1 := by
    intro hsingle
    exact neutralSingletonCover_impossible_below_cutoff ρ C hC hsingle
      hρne hneutral hcutoff
  let Q := pinnedPPrime M α j ρ C
  let V := C \ Q
  let R := 2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α
  have hQ : Q ⊆ C := by
    exact pinnedPPrime_subset_cover M α j ρ C
  have hV : V ⊆ C := by
    intro s hs
    exact (Finset.mem_sdiff.mp hs).1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  obtain ⟨matching, owner, hmatching, hrest⟩ :=
    exists_boundaryPPrime_matching_groups_of_rejected M α ρ hrej C hC hnotSingle
  rcases hrest with ⟨hneighbor, hownerEq, hgroupCover, hgroupCard⟩
  have hownerDef : ∀ x, owner x =
      boundaryGroupOwner Q V matching (IsBoundarySquareConflict R) hneighbor x := by
    intro x
    simpa [Q, V, R] using congrFun hownerEq x
  have hgroupCover' : ∀ s ∈ C,
      ∃ G ∈ boundaryGroupFamily Q V matching owner, s ∈ G := by
    simpa [Q, V, R] using hgroupCover
  have hgroupCard' : (boundaryGroupFamily Q V matching owner).card ≤
      Q.card + V.card / 2 := by
    simpa [Q, V, R] using hgroupCard
  obtain ⟨D, hD, hDcard⟩ := exists_coarseCover_of_boundaryGroups ρ C hC
    Q V matching R hR hQ hV (by simpa [Q, V, R] using hmatching)
    (by simpa [Q, V, R] using hneighbor) owner hownerDef hgroupCover'
    (by simpa [R] using hscale)
  have hVcard : V.card ≤ C.card := Finset.card_le_card hV
  have hDcard' : D.card ≤ Q.card + C.card / 2 := by
    calc
      D.card ≤ Q.card + V.card / 2 := hDcard
      _ ≤ Q.card + C.card / 2 := Nat.add_le_add_left (Nat.div_le_div_right hVcard) _
  have hAk : squareCoverNumber .free L k ρ ≤ D.card :=
    squareCoverNumber_le .free L k ρ D hD
  dsimp [Q] at hDcard'
  calc
    squareCoverNumber .free L k ρ ≤ D.card := hAk
    _ ≤ (pinnedPPrime M α j ρ C).card + C.card / 2 := by
      simpa [Q, Nat.add_comm] using hDcard'
    _ = squareCoverNumber .free L j ρ / 2 +
        (pinnedPPrime M α j ρ C).card := by rw [hCcard]; omega

/-- On the Appendix-D cutoff range, a charged one-square minimum cover is
retained in the selected family `P'_j`. -/
theorem rejected_chargedSingleton_is_in_pinnedPPrime {L j : ℕ}
    (M α : ℝ) (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hsingle : C.card = 1)
    (hρ : ρ ≠ 0) (hcharged : totalCharge ρ ≠ 0)
    (hcutoff : 16 * (2 : ℝ) ^ j ≤ boundaryAdjustedSize ρ) :
    pinnedPPrime M α j ρ C = C := by
  exact (chargedSingletonCover_retained_below_cutoff M α ρ C hC hsingle
    hρ hcharged hcutoff).2

/-- Matching groups give the same recurrence for any nonsingleton minimum
cover, whether or not the density is neutral. -/
theorem boundarySquareCoverNumber_recurrence_of_rejected_of_not_singleton
    {L j k : ℕ} (M α : ℝ) (hM : 0 < M)
    (ρ : ChargeDensity L) (hrej : HasRejectedNeighbor M α ρ)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hnotSingle : C.card ≠ 1)
    (hscale : 6 * (2 : ℝ) ^ j +
      3 * (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α) < (2 : ℝ) ^ k) :
    squareCoverNumber .free L k ρ ≤
      squareCoverNumber .free L j ρ / 2 +
        (pinnedPPrime M α j ρ C).card := by
  classical
  have hCcard : C.card = squareCoverNumber .free L j ρ :=
    card_eq_squareCoverNumber_of_isMinimumSquareCover .free L j ρ C hC
  let Q := pinnedPPrime M α j ρ C
  let V := C \ Q
  let R := 2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α
  have hQ : Q ⊆ C := pinnedPPrime_subset_cover M α j ρ C
  have hV : V ⊆ C := by
    intro s hs
    exact (Finset.mem_sdiff.mp hs).1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨matching, owner, hmatching, hrest⟩ :=
    exists_boundaryPPrime_matching_groups_of_rejected M α ρ hrej C hC hnotSingle
  rcases hrest with ⟨hneighbor, hownerEq, hgroupCover, hgroupCard⟩
  have hownerDef : ∀ x, owner x =
      boundaryGroupOwner Q V matching (IsBoundarySquareConflict R) hneighbor x := by
    intro x
    simpa [Q, V, R] using congrFun hownerEq x
  have hgroupCover' : ∀ s ∈ C,
      ∃ G ∈ boundaryGroupFamily Q V matching owner, s ∈ G := by
    simpa [Q, V, R] using hgroupCover
  have hgroupCard' : (boundaryGroupFamily Q V matching owner).card ≤
      Q.card + V.card / 2 := by
    simpa [Q, V, R] using hgroupCard
  obtain ⟨D, hD, hDcard⟩ := exists_coarseCover_of_boundaryGroups ρ C hC
    Q V matching R hR hQ hV (by simpa [Q, V, R] using hmatching)
    (by simpa [Q, V, R] using hneighbor) owner hownerDef hgroupCover'
    (by simpa [R] using hscale)
  have hVcard : V.card ≤ C.card := Finset.card_le_card hV
  have hDcard' : D.card ≤ Q.card + C.card / 2 := by
    calc
      D.card ≤ Q.card + V.card / 2 := hDcard
      _ ≤ Q.card + C.card / 2 := Nat.add_le_add_left (Nat.div_le_div_right hVcard) _
  have hAk : squareCoverNumber .free L k ρ ≤ D.card :=
    squareCoverNumber_le .free L k ρ D hD
  dsimp [Q] at hDcard'
  calc
    squareCoverNumber .free L k ρ ≤ D.card := hAk
    _ ≤ (pinnedPPrime M α j ρ C).card + C.card / 2 := by
      simpa [Q, Nat.add_comm] using hDcard'
    _ = squareCoverNumber .free L j ρ / 2 +
        (pinnedPPrime M α j ρ C).card := by rw [hCcard]; omega

/-- Full one-step recurrence on the pinned free box. Neutral singleton covers
are impossible below the cutoff. A charged singleton is retained in P'_j;
all remaining covers follow the matching-group construction. -/
theorem boundarySquareCoverNumber_recurrence_of_rejected_allCharges
    {L j k : ℕ} (M α : ℝ) (hM : 0 < M)
    (ρ : ChargeDensity L) (hrej : HasRejectedNeighbor M α ρ)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hjk : j ≤ k)
    (hcutoff : 16 * (2 : ℝ) ^ j ≤ boundaryAdjustedSize ρ)
    (hscale : 6 * (2 : ℝ) ^ j +
      3 * (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α) < (2 : ℝ) ^ k) :
    squareCoverNumber .free L k ρ ≤
      squareCoverNumber .free L j ρ / 2 +
        (pinnedPPrime M α j ρ C).card := by
  by_cases hneutral : totalCharge ρ = 0
  · exact boundarySquareCoverNumber_recurrence_of_rejected
      M α hM ρ hrej C hC hneutral hcutoff hscale
  · by_cases hsingle : C.card = 1
    · have hρne : ρ ≠ 0 := by
        intro hzero
        apply hneutral
        simp [hzero, totalCharge]
      have hret := rejected_chargedSingleton_is_in_pinnedPPrime M α ρ C hC
        hsingle hρne hneutral hcutoff
      have hCcard : C.card = squareCoverNumber .free L j ρ :=
        card_eq_squareCoverNumber_of_isMinimumSquareCover .free L j ρ C hC
      have hL : 0 < L := by
        by_contra hL
        have hL0 : L = 0 := by omega
        subst L
        apply hρne
        funext x
        exact Fin.elim0 x.1
      have hmonoAux : ∀ d, squareCoverNumber .free L (j + d) ρ ≤
          squareCoverNumber .free L j ρ := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
            rw [Nat.add_succ]
            exact (squareCoverNumber_succ_le .free L (j + d) hL ρ).trans ih
      have hmono : squareCoverNumber .free L k ρ ≤
          squareCoverNumber .free L j ρ := by
        have hdecomp : j + (k - j) = k := Nat.add_sub_of_le hjk
        rw [← hdecomp]
        exact hmonoAux (k - j)
      have hcoverj : squareCoverNumber .free L j ρ = 1 :=
        hCcard.symm.trans hsingle
      rw [hret, hcoverj, hsingle]
      rw [hcoverj] at hmono
      omega
    · exact boundarySquareCoverNumber_recurrence_of_rejected_of_not_singleton
        M α hM ρ hrej C hC hsingle hscale


private theorem rejected_boundaryEntropyGamma_cutoff_of_chargeCutoff {L : ℕ}
    (ρ : ChargeDensity L) (hd : 1 ≤ boundaryAdjustedSize ρ)
    (k : ℕ) (hk : 29 ≤ k)
    (hkcut : k ≤ boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ) :
    16 * (2 : ℝ) ^ boundaryEntropyGamma k ≤ boundaryAdjustedSize ρ := by
  let d := boundaryAdjustedSize ρ
  let X := (chargeCoverScale : ℝ) * d ^ chargeCoverExponent
  have hd' : 1 ≤ d := hd
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd'
  have hαnonneg : 0 ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
  have hdpow : 1 ≤ d ^ chargeCoverExponent := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hd' hαnonneg
    simpa [chargeCoverExponent] using h
  have hMone : 1 ≤ (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
  have hXone : 1 ≤ X := by
    dsimp [X]
    calc
      1 = 1 * 1 := by ring
      _ ≤ (chargeCoverScale : ℝ) * d ^ chargeCoverExponent :=
        mul_le_mul hMone hdpow (by positivity) (by norm_num)
  have hlognonneg : 0 ≤ Real.logb 2 X :=
    Real.logb_nonneg (by norm_num) hXone
  have hkceil : (k : ℝ) ≤
      (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ : ℝ) := by
    exact_mod_cast hkcut
  have hceil : (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ : ℝ) <
      Real.logb 2 X + 1 := by
    exact Nat.ceil_lt_add_one hlognonneg
  have hklog : (k : ℝ) < Real.logb 2 X + 1 := hkceil.trans_lt hceil
  obtain ⟨hγcast, _⟩ := boundaryEntropyGamma_spec k hk
  have hrecUpper := (recurrenceGamma_bounds ((k : ℤ) + 8)).2
  have hrecUpperR : (recurrenceGamma ((k : ℤ) + 8) : ℝ) ≤
      (4 / 7 : ℝ) * ((k : ℝ) + 8) - 83 / 7 := by
    simpa using hrecUpper
  have hγupper : (boundaryEntropyGamma k : ℝ) ≤
      (4 / 7 : ℝ) * (k : ℝ) - 107 / 7 := by
    rw [hγcast]
    nlinarith only [hrecUpperR]
  have hγlog : (boundaryEntropyGamma k : ℝ) ≤
      (4 / 7 : ℝ) * Real.logb 2 X - 103 / 7 := by
    nlinarith only [hγupper, hklog]
  have hexp : 4 + (boundaryEntropyGamma k : ℝ) ≤
      (4 / 7 : ℝ) * Real.logb 2 X - 75 / 7 := by linarith
  have hpow : (2 : ℝ) ^ (4 + (boundaryEntropyGamma k : ℝ)) ≤
      (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X - 75 / 7) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hnatpow : (2 : ℝ) ^ boundaryEntropyGamma k =
      (2 : ℝ) ^ (boundaryEntropyGamma k : ℝ) := by
    rw [Real.rpow_natCast]
  have hleft : 16 * (2 : ℝ) ^ boundaryEntropyGamma k =
      (2 : ℝ) ^ (4 + (boundaryEntropyGamma k : ℝ)) := by
    rw [hnatpow]
    calc
      16 * (2 : ℝ) ^ (boundaryEntropyGamma k : ℝ) =
          (2 : ℝ) ^ (4 : ℕ) * (2 : ℝ) ^ (boundaryEntropyGamma k : ℝ) := by norm_num
      _ = (2 : ℝ) ^ (4 + (boundaryEntropyGamma k : ℝ)) := by
        rw [(Real.rpow_natCast (2 : ℝ) 4).symm]
        exact (Real.rpow_add (x := (2 : ℝ)) (by norm_num)
          (4 : ℝ) (boundaryEntropyGamma k : ℝ)).symm
  have hlogpow :
      (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X) = X ^ (4 / 7 : ℝ) := by
    calc
      (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X) =
          (2 : ℝ) ^ (Real.logb 2 X * (4 / 7 : ℝ)) := by
            exact congrArg (fun t : ℝ => (2 : ℝ) ^ t) (by ring)
      _ = ((2 : ℝ) ^ Real.logb 2 X) ^ (4 / 7 : ℝ) := by
        rw [Real.rpow_mul (by norm_num)]
      _ = X ^ (4 / 7 : ℝ) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (lt_of_lt_of_le
          (by norm_num) hXone)]
  have hXeq : X ^ (4 / 7 : ℝ) =
      (2 : ℝ) ^ (64 / 7 : ℝ) * d := by
    dsimp [X]
    have hM : (chargeCoverScale : ℝ) = (2 : ℝ) ^ (16 : ℕ) := by
      norm_num [chargeCoverScale]
    have hfirst : ((2 : ℝ) ^ (16 : ℕ)) ^ (4 / 7 : ℝ) =
        (2 : ℝ) ^ (64 / 7 : ℝ) := by
      calc
        ((2 : ℝ) ^ (16 : ℕ)) ^ (4 / 7 : ℝ) =
            (2 : ℝ) ^ ((16 : ℝ) * (4 / 7 : ℝ)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
              have h16 : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
              rw [h16]
        _ = (2 : ℝ) ^ (64 / 7 : ℝ) := by
          have hExp : ((16 : ℕ) : ℝ) * (4 / 7 : ℝ) = 64 / 7 := by norm_num
          exact congrArg (fun t : ℝ => (2 : ℝ) ^ t) hExp
    have hdexp : (d ^ chargeCoverExponent) ^ (4 / 7 : ℝ) = d := by
      rw [← Real.rpow_mul (by positivity)]
      norm_num [chargeCoverExponent]
    calc
      ((chargeCoverScale : ℝ) * d ^ chargeCoverExponent) ^ (4 / 7 : ℝ) =
          ((2 : ℝ) ^ (16 : ℕ)) ^ (4 / 7 : ℝ) *
            (d ^ chargeCoverExponent) ^ (4 / 7 : ℝ) := by
              rw [hM]
              exact Real.mul_rpow (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (64 / 7 : ℝ) * d := by rw [hfirst, hdexp]
  have hconst : (2 : ℝ) ^ (-75 / 7 : ℝ) *
      (2 : ℝ) ^ (64 / 7 : ℝ) = (2 : ℝ) ^ (-11 / 7 : ℝ) := by
    calc
      _ = (2 : ℝ) ^ ((-75 / 7 : ℝ) + 64 / 7) :=
        (Real.rpow_add (x := (2 : ℝ)) (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ (-11 / 7 : ℝ) := by
        rw [show (-75 / 7 : ℝ) + 64 / 7 = -11 / 7 by norm_num]
  have hcoeff' : (2 : ℝ) ^ (-11 / 7 : ℝ) ≤ (2 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
      (y := (-11 / 7 : ℝ)) (z := (0 : ℝ)) (by norm_num) (by norm_num)
  have hcoeff : (2 : ℝ) ^ (-11 / 7 : ℝ) ≤ 1 := by simpa using hcoeff'
  calc
    16 * (2 : ℝ) ^ boundaryEntropyGamma k =
        (2 : ℝ) ^ (4 + (boundaryEntropyGamma k : ℝ)) := hleft
    _ ≤ (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X - 75 / 7) := hpow
    _ = (2 : ℝ) ^ (-75 / 7 : ℝ) *
        (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X) := by
          rw [show (4 / 7 : ℝ) * Real.logb 2 X - 75 / 7 =
            (-75 / 7 : ℝ) + (4 / 7 : ℝ) * Real.logb 2 X by ring,
            Real.rpow_add (by norm_num)]
    _ = (2 : ℝ) ^ (-75 / 7 : ℝ) *
        ((2 : ℝ) ^ (64 / 7 : ℝ) * d) := by rw [hlogpow, hXeq]
    _ = (2 : ℝ) ^ (-11 / 7 : ℝ) * d := by rw [← mul_assoc, hconst]
    _ ≤ d := by
      simpa using mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ d)

/-- The finite-volume Appendix-D entropy estimate.
Rejected-square neighbours supply the local recurrence, while the explicit cutoff hypothesis
ensures each coarse scale uses a fine scale meeting the volume condition. -/
theorem rejected_boundary_entropy_scale_uniform
    {L : ℕ} (M α : ℝ) (hM : 0 < M)
    (hMscale : M = chargeCoverScale) (hαscale : α = chargeCoverExponent)
    (ρ : ChargeDensity L) (hrej : HasRejectedNeighbor M α ρ)
    (n : ℕ) (hn : 29 ≤ n)
    (hcutoff : ∀ k, 29 ≤ k → k ≤ n →
      16 * (2 : ℝ) ^ boundaryEntropyGamma k ≤ boundaryAdjustedSize ρ) :
    (∑ j ∈ Finset.range (n + 1),
      (squareCoverNumber .free L j ρ : ℝ)) ≤
      (∑' k : ℕ, boundaryEntropyTerminalWeight k) *
        (squareCoverNumber .free L 0 ρ : ℝ) +
      (196 / 3 : ℝ) *
        (∑ j ∈ Finset.Icc 1 n, boundaryEntropySelectedCount M α ρ j) := by
  classical
  let A : ℕ → ℝ := fun k =>
    if k ≤ n then (squareCoverNumber .free L k ρ : ℝ) else 0
  let P : ℕ → ℝ := boundaryEntropySelectedProfile M α ρ n
  have hstep : ∀ k, 29 ≤ k →
      A k ≤ (1 / 2 : ℝ) * A (boundaryEntropyGamma k) +
        P (boundaryEntropyGamma k) := by
    intro k hk29
    by_cases hkn : k ≤ n
    · obtain ⟨hγcast, hγgap⟩ := boundaryEntropyGamma_spec k hk29
      have hγle : boundaryEntropyGamma k ≤ n := by omega
      have hγleK : boundaryEntropyGamma k ≤ k := by omega
      have hγposR : (1 : ℝ) ≤ (boundaryEntropyGamma k : ℝ) := by
        have hlow := (recurrenceGamma_bounds ((k : ℤ) + 8)).1
        have hkR : (29 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk29
        have hlow' : (4 / 7 : ℝ) * ((k : ℝ) + 8) -
            83 / 7 - 1 ≤ (recurrenceGamma ((k : ℤ) + 8) : ℝ) := by
          simpa using hlow
        have hγint_gt : (8 : ℝ) < (recurrenceGamma ((k : ℤ) + 8) : ℝ) := by
          norm_num at hlow'
          nlinarith only [hlow', hkR]
        have hγint : 9 ≤ recurrenceGamma ((k : ℤ) + 8) := by
          exact_mod_cast hγint_gt
        rw [hγcast]
        have hγintR : (9 : ℝ) ≤ (recurrenceGamma ((k : ℤ) + 8) : ℝ) := by
          exact_mod_cast hγint
        linarith
      have hγpos : 0 < boundaryEntropyGamma k := by exact_mod_cast hγposR
      have hcutγ := hcutoff k hk29 hkn
      have hscaleFixed := boundaryEntropyGamma_matchingScale k hk29
      have hscale : 6 * (2 : ℝ) ^ boundaryEntropyGamma k +
          3 * (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ boundaryEntropyGamma k) ^ α) <
            (2 : ℝ) ^ k := by
        simpa [hMscale, hαscale, chargeCoverExponent] using hscaleFixed
      let C := boundaryEntropyMinimumCover ρ (boundaryEntropyGamma k)
      have hC := boundaryEntropyMinimumCover_isMinimum ρ (boundaryEntropyGamma k)
      have hrec := boundarySquareCoverNumber_recurrence_of_rejected_allCharges
        (L := L) (j := boundaryEntropyGamma k) (k := k)
        M α hM ρ hrej C hC hγleK hcutγ hscale
      have hrecR : (squareCoverNumber .free L k ρ : ℝ) ≤
          ((squareCoverNumber .free L (boundaryEntropyGamma k) ρ / 2 +
            (pinnedPPrime M α (boundaryEntropyGamma k) ρ C).card : ℕ) : ℝ) := by
        exact_mod_cast hrec
      have hdiv : ((squareCoverNumber .free L (boundaryEntropyGamma k) ρ / 2 : ℕ) : ℝ) ≤
          (squareCoverNumber .free L (boundaryEntropyGamma k) ρ : ℝ) / 2 :=
        Nat.cast_div_le
      have hPγ : P (boundaryEntropyGamma k) =
          ((pinnedPPrime M α (boundaryEntropyGamma k) ρ C).card : ℝ) := by
        have hγle1 : 1 ≤ boundaryEntropyGamma k := by omega
        unfold P boundaryEntropySelectedProfile
        rw [ite_eq_left ⟨hγle1, hγle⟩]
        simp [boundaryEntropySelectedCount, C, boundaryEntropyMinimumCover]
      calc
        A k = (squareCoverNumber .free L k ρ : ℝ) := by simp [A, hkn]
        _ ≤ ((squareCoverNumber .free L (boundaryEntropyGamma k) ρ / 2 : ℕ) : ℝ) +
              (pinnedPPrime M α (boundaryEntropyGamma k) ρ C).card := by
                simpa only [Nat.cast_add] using hrecR
        _ ≤ (1 / 2 : ℝ) *
              (squareCoverNumber .free L (boundaryEntropyGamma k) ρ : ℝ) +
              (pinnedPPrime M α (boundaryEntropyGamma k) ρ C).card := by
                exact add_le_add
                  (by simpa [div_eq_mul_inv, mul_comm] using hdiv) le_rfl
        _ = (1 / 2 : ℝ) * A (boundaryEntropyGamma k) +
              P (boundaryEntropyGamma k) := by
                simp [A, hγle, hPγ]
    · have hAk : A k = 0 := by simp [A, hkn]
      have hAnonneg : 0 ≤ A (boundaryEntropyGamma k) := by
        unfold A
        split_ifs <;> positivity
      have hPnonneg : 0 ≤ P (boundaryEntropyGamma k) :=
        boundaryEntropySelectedProfile_nonneg M α ρ n _
      rw [hAk]
      positivity
  have hdepth : ∀ k, 0 < boundaryEntropyDepth k →
      29 ≤ k ∧ boundaryEntropyDepth (boundaryEntropyGamma k) + 1 =
        boundaryEntropyDepth k := by
    intro k hk
    exact ⟨boundaryEntropyDepth_pos_lower hk,
      (boundaryEntropyDepth_gamma k (boundaryEntropyDepth_pos_lower hk)).symm⟩
  have hphiZero : ∀ q : ℤ, q ≤ 8 → boundaryEntropyPhi q = 0 := by
    intro q hq
    unfold boundaryEntropyPhi
    rw [Int.toNat_of_nonpos (by omega)]
  have hphiCast : ∀ q : ℤ, 8 ≤ q →
      (boundaryEntropyPhi q : ℤ) = q - 8 := by
    intro q hq
    unfold boundaryEntropyPhi
    exact Int.toNat_of_nonneg (by omega)
  have hstop : ∀ k,
      boundaryEntropyIterate boundaryEntropyGamma (boundaryEntropyDepth k) k < 29 := by
    intro k
    have hrelation := boundaryEntropyIterate_eq_phi (boundaryEntropyDepth k)
      ((k : ℤ) + 8)
    have hstart : boundaryEntropyPhi ((k : ℤ) + 8) = k := by
      unfold boundaryEntropyPhi
      have hsub : (k : ℤ) + 8 - 8 = (k : ℤ) := by omega
      rw [hsub]
      simp
    rw [hstart] at hrelation
    have hsource := boundaryEntropyDepth_stops k
    have hsmall : boundaryEntropyPhi
        (recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8)) < 29 := by
      by_cases hq : recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8) ≤ 8
      · rw [hphiZero _ hq]
        omega
      · have hq8 : 8 ≤ recurrenceIterate (boundaryEntropyDepth k)
          ((k : ℤ) + 8) := by omega
        have hcast := hphiCast _ hq8
        have hreal : (boundaryEntropyPhi
            (recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8)) : ℤ) < 29 := by
          rw [hcast]
          omega
        exact_mod_cast hreal
    rw [hrelation]
    exact hsmall
  have hterminal : ∀ k, k < 29 → A k ≤ A 0 := by
    intro k hk
    have hkn : k ≤ n := by omega
    have hmono := squareCoverNumber_le_squareCoverNumber_zero .free L k ρ
    simpa [A, hkn] using (show
      (squareCoverNumber .free L k ρ : ℝ) ≤
        (squareCoverNumber .free L 0 ρ : ℝ) by exact_mod_cast hmono)
  have hAnonneg : ∀ k, 0 ≤ A k := by
    intro k
    unfold A
    split_ifs <;> positivity
  have hPnonneg : ∀ j, 0 ≤ P j :=
    boundaryEntropySelectedProfile_nonneg M α ρ n
  have hweights :
      (∑ k ∈ Finset.range (n + 1),
        (1 / 2 : ℝ) ^ boundaryEntropyDepth k) ≤
      ∑' k : ℕ, boundaryEntropyTerminalWeight k := by
    simpa [boundaryEntropyTerminalWeight] using boundaryEntropyTerminalWeight_sum_le n
  have hfiber : ∀ m,
      (∑ k ∈ Finset.range (n + 1),
        P (boundaryEntropyIterate boundaryEntropyGamma (m + 1) k)) ≤
        (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℕ, P j := by
    intro m
    exact boundaryEntropy_nat_layer_sum_bound n m P
      (boundaryEntropySelectedProfile_zero M α ρ n)
      (boundaryEntropySelectedProfile_tail M α ρ n)
      hPnonneg
  have hbound := boundaryEntropy_sum_bound_of_iteration_fibers
    A P boundaryEntropyGamma boundaryEntropyDepth 29 n hstep hdepth hstop
    hterminal hAnonneg hPnonneg
    (∑' k : ℕ, boundaryEntropyTerminalWeight k) hweights hfiber
  have hAfinite :
      (∑ k ∈ Finset.range (n + 1),
        (squareCoverNumber .free L k ρ : ℝ)) =
      ∑ k ∈ Finset.range (n + 1), A k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by
      simp only [Finset.mem_range] at hk
      omega
    simp [A, hkn]
  rw [hAfinite]
  have hprofile := boundaryEntropySelectedProfile_tsum_eq M α ρ n
  calc
    (∑ k ∈ Finset.range (n + 1), A k) ≤
        (∑' k : ℕ, boundaryEntropyTerminalWeight k) * A 0 +
          (196 / 3 : ℝ) * ∑' j : ℕ, P j := hbound
    _ = (∑' k : ℕ, boundaryEntropyTerminalWeight k) *
          (squareCoverNumber .free L 0 ρ : ℝ) +
        (196 / 3 : ℝ) *
          (∑ j ∈ Finset.Icc 1 n, boundaryEntropySelectedCount M α ρ j) := by
      rw [hprofile]
      simp [A]

/-- The entropy estimate through the Appendix-D charge cutoff. The scale
inequality needed by every recurrence step follows from the logarithmic
definition of that cutoff and the fixed KP constants. -/
theorem rejected_boundary_entropy_chargeCutoff
    {L : ℕ} (ρ : ChargeDensity L)
    (hrej : HasRejectedNeighbor chargeCoverScale chargeCoverExponent ρ) (hρne : ρ ≠ 0)
    (hn : 29 ≤ boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ) :
    (∑ j ∈ Finset.range
        (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ + 1),
      (squareCoverNumber .free L j ρ : ℝ)) ≤
      (∑' k : ℕ, boundaryEntropyTerminalWeight k) *
        (squareCoverNumber .free L 0 ρ : ℝ) +
      (196 / 3 : ℝ) *
        (∑ j ∈ Finset.Icc 1
          (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
          boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j) := by
  apply rejected_boundary_entropy_scale_uniform
    (M := chargeCoverScale) (α := chargeCoverExponent)
    (by norm_num [chargeCoverScale]) rfl rfl
    ρ hrej
    (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ) hn
  intro k hk29 hkcut
  have hd : 1 ≤ boundaryAdjustedSize ρ := by
    by_cases hneutral : totalCharge ρ = 0
    · exact boundaryAdjustedSize_ge_one_of_neutral_ne_zero ρ hneutral hρne
    · exact one_le_boundaryAdjustedSize_of_charged_ne_zero ρ hneutral hρne
  exact rejected_boundaryEntropyGamma_cutoff_of_chargeCutoff ρ
    hd
    k hk29 hkcut


/-- **The cover-cost bound from rejected-square neighbours** (`layerA_le`'s cover part):
`A_cover(ϱ) ≤ (29 + |C_T|) ‖ϱ|faces‖₁ + (196/3) Σ_j |P'_j|`. -/
theorem layerCoverSum_le_of_rejected {L : ℕ} {ϱ : Rotator.RotatorDualFace L → ℤ}
    (hrej : HasRejectedNeighbor (chargeCoverScale : ℝ) chargeCoverExponent (Layer.siteRestrict ϱ))
    (hϱ0 : Layer.siteRestrict ϱ ≠ 0) :
    Layer.layerCoverSum ϱ ≤
      (29 + |∑' k : ℕ, boundaryEntropyTerminalWeight k|) *
          ∑ x, |(Layer.siteRestrict ϱ x : ℝ)| +
        196 / 3 * Layer.layerSelectedSum ϱ := by
  set ρ := Layer.siteRestrict ϱ with hρ
  set CT := ∑' k : ℕ, boundaryEntropyTerminalWeight k
  set m := ∑ x, |(ρ x : ℝ)|
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hp0 : 0 ≤ Layer.layerSelectedSum ϱ := Layer.layerSelectedSum_nonneg _
  unfold Layer.layerCoverSum Layer.layerCutoff
  have hA : ∀ j, (squareCoverNumber .free L j ρ : ℝ) ≤ m :=
    fun j => (Layer.squareCoverNumber_le_card j ρ).trans (Layer.card_support_le_norm ρ)
  by_cases hn : 29 ≤ boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ
  · have hX := rejected_boundary_entropy_chargeCutoff ρ hrej hϱ0 hn
    have hsel : (∑ j ∈ Finset.Icc 1
        (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ),
        boundaryEntropySelectedCount (chargeCoverScale : ℝ) chargeCoverExponent ρ j) =
          Layer.layerSelectedSum ϱ := by
      simp [Layer.layerSelectedSum, Layer.layerCutoff, ρ]
    have h0 : CT * (squareCoverNumber .free L 0 ρ : ℝ) ≤ |CT| * m :=
      (mul_le_mul_of_nonneg_right (le_abs_self CT) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hA 0) (abs_nonneg CT))
    have : |CT| * m ≤ (29 + |CT|) * m := by nlinarith
    rw [hsel] at hX
    linarith
  · push Not at hn
    calc (∑ j ∈ Finset.range
          (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ + 1),
          (squareCoverNumber .free L j ρ : ℝ))
        ≤ ∑ _j ∈ Finset.range
          (boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ + 1), m :=
          Finset.sum_le_sum fun j _ => hA j
      _ = ((boundaryChargeCutoff (chargeCoverScale : ℝ) chargeCoverExponent ρ + 1 : ℕ) : ℝ)
          * m := by simp
      _ ≤ 29 * m := by
          apply mul_le_mul_of_nonneg_right _ hm0
          exact_mod_cast hn
      _ ≤ (29 + |CT|) * m + 196 / 3 * Layer.layerSelectedSum ϱ := by
          nlinarith [abs_nonneg CT]

end FroehlichSpencer.BKT.Generic.PinnedCharges.Rejected

end
