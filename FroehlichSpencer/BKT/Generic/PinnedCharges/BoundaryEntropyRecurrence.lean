/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyCover
public import FroehlichSpencer.BKT.Charges.ScaleMonotonicity

/-! # The one-step boundary entropy recurrence

On the isolation locus, a minimum fine cover can be grouped into bounded
matching groups. A coarse square covers each group, giving the recurrence
`A_k ≤ A_j / 2 + |P'_j|` whenever the geometric scale inequality holds.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

/-- The minimum free-square cover numbers obey the Appendix-D one-step
recurrence under the explicit scale inequality and cutoff. -/
theorem boundarySquareCoverNumber_recurrence_of_isolation {L j k : ℕ}
    (M α : ℝ) (hM : 0 < M) (hα : 0 < α)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) (hρ : ρ ∈ N)
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
    exists_boundaryPPrime_matching_groups M α hM hα ρ N hN hρ C hC hnotSingle
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
theorem chargedSingleton_is_in_pinnedPPrime {L j : ℕ}
    (M α : ℝ) (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hsingle : C.card = 1)
    (hρ : ρ ≠ 0) (hcharged : totalCharge ρ ≠ 0)
    (hcutoff : 16 * (2 : ℝ) ^ j ≤ boundaryAdjustedSize ρ) :
    pinnedPPrime M α j ρ C = C := by
  exact (chargedSingletonCover_retained_below_cutoff M α ρ C hC hsingle
    hρ hcharged hcutoff).2

/-- Matching groups give the same recurrence for any nonsingleton minimum
cover, whether or not the density is neutral. -/
theorem boundarySquareCoverNumber_recurrence_of_isolation_of_not_singleton
    {L j k : ℕ} (M α : ℝ) (hM : 0 < M) (hα : 0 < α)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) (hρ : ρ ∈ N)
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
    exists_boundaryPPrime_matching_groups M α hM hα ρ N hN hρ C hC hnotSingle
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
theorem boundarySquareCoverNumber_recurrence_of_isolation_allCharges
    {L j k : ℕ} (M α : ℝ) (hM : 0 < M) (hα : 0 < α)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) (hρ : ρ ∈ N)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (hjk : j ≤ k)
    (hcutoff : 16 * (2 : ℝ) ^ j ≤ boundaryAdjustedSize ρ)
    (hscale : 6 * (2 : ℝ) ^ j +
      3 * (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ j) ^ α) < (2 : ℝ) ^ k) :
    squareCoverNumber .free L k ρ ≤
      squareCoverNumber .free L j ρ / 2 +
        (pinnedPPrime M α j ρ C).card := by
  by_cases hneutral : totalCharge ρ = 0
  · exact boundarySquareCoverNumber_recurrence_of_isolation
      M α hM hα ρ N hN hρ C hC hneutral hcutoff hscale
  · by_cases hsingle : C.card = 1
    · have hρne : ρ ≠ 0 := by
        intro hzero
        apply hneutral
        simp [hzero, totalCharge]
      have hret := chargedSingleton_is_in_pinnedPPrime M α ρ C hC
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
    · exact boundarySquareCoverNumber_recurrence_of_isolation_of_not_singleton
        M α hM hα ρ N hN hρ C hC hsingle hscale

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
