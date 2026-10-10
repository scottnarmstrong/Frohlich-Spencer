/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.Geometry
public import FroehlichSpencer.BKT.Charges.SupportCover

/-! # Minimum-cover facts for the Appendix D selected family

`P'_k` is a subfamily selected from a minimum cover; it is not itself asserted
to cover the support. These lemmas retain the minimum-cover witness while
making the cardinality consequence of the selection explicit.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

def CoversChargeSupport {L : ℕ} (ρ : ChargeDensity L)
    (C : Finset (Finset (Site L))) : Prop :=
  ∀ x ∈ chargeSupport ρ, ∃ s ∈ C, x ∈ s

/-- A minimum cover in an arbitrary specified family of allowed squares.
Keeping the allowed-square predicate outside this definition avoids silently
identifying FS81's translates with KP's anchored square family. -/
def IsAllowedMinimumSupportCover {L : ℕ} (Allowed : Finset (Site L) → Prop)
    (ρ : ChargeDensity L)
    (C : Finset (Finset (Site L))) : Prop :=
  (∀ s ∈ C, Allowed s) ∧ CoversChargeSupport ρ C ∧
    ∀ D, (∀ s ∈ D, Allowed s) → CoversChargeSupport ρ D → C.card ≤ D.card

theorem minimumSupportCover_square_has_private_site {L : ℕ}
    (Allowed : Finset (Site L) → Prop) (ρ : ChargeDensity L)
    (C : Finset (Finset (Site L)))
    (hC : IsAllowedMinimumSupportCover Allowed ρ C)
    {s : Finset (Site L)} (hs : s ∈ C) :
    ∃ x ∈ chargeSupport ρ, x ∈ s ∧ ∀ t ∈ C, t ≠ s → x ∉ t := by
  classical
  by_contra hnot
  have hnoPrivate : ∀ x ∈ chargeSupport ρ, x ∈ s →
      ∃ t ∈ C, t ≠ s ∧ x ∈ t := by
    intro x hx hxS
    by_contra h
    apply hnot
    refine ⟨x, hx, hxS, ?_⟩
    intro t ht hts hxt
    exact h ⟨t, ht, hts, hxt⟩
  have heraseCover : CoversChargeSupport ρ (C.erase s) := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hC.2.1 x hx
    by_cases hts : t = s
    · subst t
      obtain ⟨u, hu, hus, hxu⟩ := hnoPrivate x hx hxt
      exact ⟨u, Finset.mem_erase.mpr ⟨hus, hu⟩, hxu⟩
    · exact ⟨t, Finset.mem_erase.mpr ⟨hts, ht⟩, hxt⟩
  have heraseAllowed : ∀ t ∈ C.erase s, Allowed t := by
    intro t ht
    exact hC.1 t (Finset.mem_of_mem_erase ht)
  have hcard := hC.2.2 (C.erase s) heraseAllowed heraseCover
  rw [Finset.card_erase_of_mem hs] at hcard
  have hlt : C.card - 1 < C.card :=
    Nat.sub_lt (Finset.card_pos.mpr ⟨s, hs⟩) (by decide)
  exact (not_lt_of_ge hcard hlt)

theorem pinnedPPrime_subset_cover {L : ℕ} (M α : ℝ) (k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L))) :
    pinnedPPrime M α k ρ C ⊆ C := by
  classical
  intro s hs
  by_cases hsingle : C.card = 1
  · by_cases hkeep : totalCharge ρ ≠ 0 ∧
        singletonBoundaryMargin k ≤ chargeBoundaryDistance ρ
    · rw [pinnedPPrime_eq_self_of_singleton_exception M α k ρ C hsingle
          hkeep.1 hkeep.2] at hs
      exact hs
    · rw [pinnedPPrime_eq_empty_of_singleton_exception_fails M α k ρ C
          hsingle hkeep] at hs
      exact (Finset.notMem_empty _ hs).elim
  · exact ((mem_pinnedPPrime_of_cover_card_ne_one M α k ρ C hsingle s).1 hs).1

theorem pinnedPPrime_card_le_coverCard {L : ℕ} (M α : ℝ) (k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L))) :
    (pinnedPPrime M α k ρ C).card ≤ C.card :=
  Finset.card_le_card (pinnedPPrime_subset_cover M α k ρ C)

theorem minimumCover_square_has_private_support_site {L : ℕ} (k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L k ρ C)
    {s : Finset (Site L)} (hs : s ∈ C) :
    ∃ x ∈ chargeSupport ρ, x ∈ s ∧
      ∀ t ∈ C, t ≠ s → x ∉ t := by
  exact minimumSupportCover_square_has_private_site (fun s => s ∈ kpSquares .free L k)
    ρ C ⟨fun s hs => hC.1.1 hs, hC.1.2, fun D hAllowed hCover =>
      hC.2 D ⟨hAllowed, hCover⟩⟩ hs

theorem pinnedPPrime_mem_of_minimumCover {L : ℕ} (M α : ℝ) (k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L k ρ C)
    {s : Finset (Site L)} (hs : s ∈ pinnedPPrime M α k ρ C) :
    s ∈ C ∧ s ∈ kpSquares .free L k := by
  classical
  by_cases hsingle : C.card = 1
  · by_cases hkeep : totalCharge ρ ≠ 0 ∧
        singletonBoundaryMargin k ≤ chargeBoundaryDistance ρ
    · rw [pinnedPPrime_eq_self_of_singleton_exception M α k ρ C hsingle
          hkeep.1 hkeep.2] at hs
      exact ⟨hs, hC.1.1 hs⟩
    · rw [pinnedPPrime_eq_empty_of_singleton_exception_fails M α k ρ C
          hsingle hkeep] at hs
      exact (Finset.notMem_empty _ hs).elim
  · have hsC := (mem_pinnedPPrime_of_cover_card_ne_one M α k ρ C hsingle s).1 hs |>.1
    exact ⟨hsC, hC.1.1 hsC⟩

theorem minimumCover_card_eq_number {L : ℕ} (k : ℕ) (ρ : ChargeDensity L)
    (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L k ρ C) :
    C.card = squareCoverNumber .free L k ρ := by
  apply le_antisymm
  · obtain ⟨D, hD, hDcard⟩ := exists_squareCover_attaining_number .free L k ρ
    rw [← hDcard]
    exact hC.2 D hD
  · exact squareCoverNumber_le .free L k ρ C hC.1

theorem pinnedPPrime_card_le_minimumCoverNumber {L : ℕ} (M α : ℝ) (k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L k ρ C) :
    (pinnedPPrime M α k ρ C).card ≤ squareCoverNumber .free L k ρ := by
  have hsub : pinnedPPrime M α k ρ C ⊆ C := by
    intro s hs
    exact (pinnedPPrime_mem_of_minimumCover M α k ρ C hC hs).1
  exact (Finset.card_le_card hsub).trans (minimumCover_card_eq_number k ρ C hC).le

theorem pinnedPPrime_card_le_supportCard {L : ℕ} (M α : ℝ) (k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L k ρ C) :
    (pinnedPPrime M α k ρ C).card ≤ (chargeSupport ρ).card := by
  exact (pinnedPPrime_card_le_minimumCoverNumber M α k ρ C hC).trans
    (squareCoverNumber_le_card_chargeSupport .free L k ρ)

theorem pinnedPPrime_card_singleton_cover {L : ℕ} (M α : ℝ) (k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L k ρ C) (hsingle : C.card = 1) :
    (pinnedPPrime M α k ρ C).card =
      if totalCharge ρ ≠ 0 ∧ singletonBoundaryMargin k ≤ chargeBoundaryDistance ρ
      then squareCoverNumber .free L k ρ else 0 := by
  classical
  by_cases hkeep : totalCharge ρ ≠ 0 ∧
      singletonBoundaryMargin k ≤ chargeBoundaryDistance ρ
  · rw [pinnedPPrime_eq_self_of_singleton_exception M α k ρ C hsingle hkeep.1 hkeep.2]
    simp [hkeep, minimumCover_card_eq_number k ρ C hC]
  · rw [pinnedPPrime_eq_empty_of_singleton_exception_fails M α k ρ C hsingle hkeep]
    simp [hkeep]

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
