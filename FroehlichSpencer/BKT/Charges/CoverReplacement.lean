/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ParentGeometry

/-! # Replacing the unique target square meeting a prescribed patch

These finite-cover lemmas isolate the minimum-cover part of  Once a
patch is isolated from the rest of the support, a prescribed allowed parent
can replace its unique target square without changing the cover number. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- A target square meets a support patch. -/
def SquareMeetsPatch {L : ℕ} (patch : Finset (Fin L × Fin L))
    (s : Finset (Fin L × Fin L)) : Prop := ∃ x ∈ patch, x ∈ s

/-- A square is local to a patch of the support when all support points it
contains belong to that patch. -/
def SquareLocalToPatch {L : ℕ} (support patch : Finset (Fin L × Fin L))
    (s : Finset (Fin L × Fin L)) : Prop :=
  ∀ x ∈ s, x ∈ support → x ∈ patch

/-- A nonempty isolated support patch meets exactly one member of a minimum
cover. The isolation hypothesis is the geometric input supplied by 's
diameter and separation estimates. -/
theorem existsUnique_squareMeetingPatch_of_minimum
    (boundary : SquareBoundary) (L k : ℕ) (ρ : ChargeDensity L)
    (C : Finset (Finset (Fin L × Fin L)))
    (hC : IsMinimumSquareCover boundary L k ρ C)
    (patch parent : Finset (Fin L × Fin L)) (hpatch : patch.Nonempty)
    (hpatchSupport : patch ⊆ chargeSupport ρ)
    (hparentAllowed : parent ∈ kpSquares boundary L k)
    (hpatchParent : patch ⊆ parent)
    (hlocal : ∀ s ∈ C, SquareMeetsPatch patch s →
      SquareLocalToPatch (chargeSupport ρ) patch s) :
    ∃! s, s ∈ C ∧ SquareMeetsPatch patch s := by
  classical
  let E := C.filter (SquareMeetsPatch patch)
  have hE_nonempty : E.Nonempty := by
    rcases hpatch with ⟨x, hx⟩
    obtain ⟨s, hsC, hxs⟩ := hC.1.2 x (hpatchSupport hx)
    exact ⟨s, Finset.mem_filter.mpr ⟨hsC, ⟨x, hx, hxs⟩⟩⟩
  have hE_sub : E ⊆ C := Finset.filter_subset _ _
  have hE_card : E.card = 1 := by
    by_contra hne
    have hcard : 2 ≤ E.card := by
      have hpos : 0 < E.card := Finset.card_pos.mpr hE_nonempty
      omega
    let D := insert parent (C \ E)
    have hparent_meets : SquareMeetsPatch patch parent := by
      rcases hpatch with ⟨x, hx⟩
      exact ⟨x, hx, hpatchParent hx⟩
    have hparent_not : parent ∉ C \ E := by
      intro hmem
      have hCparent : parent ∈ C := (Finset.mem_sdiff.mp hmem).1
      have hEparent : parent ∈ E :=
        Finset.mem_filter.mpr ⟨hCparent, by simpa using hparent_meets⟩
      exact (Finset.mem_sdiff.mp hmem).2 hEparent
    have hDcover : IsSquareCover boundary L k ρ D := by
      refine ⟨?_, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.mp hs with hs | hs
        · subst s
          exact hparentAllowed
        · exact hC.1.1 ((Finset.mem_sdiff.mp hs).1)
      · intro x hx
        by_cases hxp : x ∈ patch
        · exact ⟨parent, Finset.mem_insert_self _ _, hpatchParent hxp⟩
        · obtain ⟨s, hsC, hxs⟩ := hC.1.2 x hx
          have hsE : s ∉ E := by
            intro hsE
            have hlocal := hlocal s hsC (Finset.mem_filter.mp hsE).2
            exact hxp (hlocal x hxs hx)
          exact ⟨s, Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hsC, hsE⟩), hxs⟩
    have hDcard : D.card = (C \ E).card + 1 := by
      dsimp [D]
      exact Finset.card_insert_of_notMem hparent_not
    have hD_card : D.card < C.card := by
      have hsplit := Finset.card_sdiff_add_card_eq_card hE_sub
      rw [hDcard]
      omega
    have hmin := hC.2 D hDcover
    omega
  obtain ⟨s, hsEq⟩ := Finset.card_eq_one.mp hE_card
  refine ⟨s, ?_, ?_⟩
  · have hsE : s ∈ E := by rw [hsEq]; simp
    exact Finset.mem_filter.mp hsE
  · intro t ht
    have htE : t ∈ E := Finset.mem_filter.mpr ⟨ht.1, ht.2⟩
    rw [hsEq] at htE
    exact Finset.mem_singleton.mp htE

/-- Replace the unique target square meeting an isolated patch by its
prescribed allowed parent. The resulting cover is still minimum. -/
theorem replace_unique_squareMeetingPatch
    (boundary : SquareBoundary) (L k : ℕ) (ρ : ChargeDensity L)
    (C : Finset (Finset (Fin L × Fin L)))
    (hC : IsMinimumSquareCover boundary L k ρ C)
    (patch parent : Finset (Fin L × Fin L)) (old : Finset (Fin L × Fin L))
    (hpatch : patch.Nonempty)
    (hparentAllowed : parent ∈ kpSquares boundary L k)
    (hparentExact : parent ∩ chargeSupport ρ = patch)
    (hold : old ∈ C ∧ SquareMeetsPatch patch old)
    (hunique : ∀ s, s ∈ C → SquareMeetsPatch patch s → s = old)
    (hlocal : ∀ s ∈ C, SquareMeetsPatch patch s →
      SquareLocalToPatch (chargeSupport ρ) patch s) :
    IsMinimumSquareCover boundary L k ρ (insert parent (C.erase old)) := by
  classical
  let D := insert parent (C.erase old)
  have hparentPatch : patch ⊆ parent := by
    intro x hx
    exact (Finset.mem_inter.mp (hparentExact.symm ▸ hx)).1
  have hparent_not : parent ∉ C.erase old := by
    intro hp
    have hpC : parent ∈ C := (Finset.mem_erase.mp hp).2
    have hpm : SquareMeetsPatch patch parent := by
      rcases hpatch with ⟨x, hx⟩
      exact ⟨x, hx, hparentPatch hx⟩
    exact (Finset.mem_erase.mp hp).1 (hunique parent hpC hpm)
  have hDcard : D.card = C.card := by
    dsimp [D]
    rw [Finset.card_insert_of_notMem hparent_not]
    exact Finset.card_erase_add_one hold.1
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with hs | hs
      · subst s
        exact hparentAllowed
      · exact hC.1.1 (Finset.mem_erase.mp hs).2
    · intro x hx
      by_cases hxp : x ∈ patch
      · exact ⟨parent, Finset.mem_insert_self _ _, hparentPatch hxp⟩
      · obtain ⟨s, hsC, hxs⟩ := hC.1.2 x hx
        have hsne : s ≠ old := by
          intro heq
          subst s
          exact hxp ((hlocal old hold.1 hold.2) x hxs hx)
        exact ⟨s, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsne, hsC⟩), hxs⟩
  · intro D' hD'
    rw [hDcard]
    exact hC.2 D' hD'

end FroehlichSpencer.BKT

end
