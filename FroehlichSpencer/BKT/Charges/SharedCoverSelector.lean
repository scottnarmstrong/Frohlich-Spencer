/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.CoverReplacement

/-! # Simultaneous compatible parent prescriptions

This module proves the finite replacement step of  Pairwise disjoint
support patches can be imposed successively in minimum covers; each completed
parent remains present because later replacements only erase squares meeting
other patches. Duplicate prescriptions are removed before this theorem is
used, by indexing the constraints by their patch finsets. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Pairwise disjoint isolated patches admit a common minimum cover containing
all prescribed parents. The hypotheses state the isolation and compatibility
facts proved by the geometric part of  -/
theorem exists_minimumSquareCover_containing_parents
    (boundary : SquareBoundary) (L k : ℕ) (ρ : ChargeDensity L)
    (P : Finset (Finset (Fin L × Fin L)))
    (parent : Finset (Fin L × Fin L) → Finset (Fin L × Fin L))
    (C : Finset (Finset (Fin L × Fin L)))
    (hC : IsMinimumSquareCover boundary L k ρ C)
    (hnonempty : ∀ p ∈ P, p.Nonempty)
    (hsubsupport : ∀ p ∈ P, p ⊆ chargeSupport ρ)
    (hdisjoint : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q)
    (hallowed : ∀ p ∈ P, parent p ∈ kpSquares boundary L k)
    (hexact : ∀ p ∈ P, parent p ∩ chargeSupport ρ = p)
    (hlocal : ∀ p ∈ P, ∀ s ∈ C, SquareMeetsPatch p s →
      SquareLocalToPatch (chargeSupport ρ) p s) :
    ∃ C', IsMinimumSquareCover boundary L k ρ C' ∧
      (∀ p ∈ P, parent p ∈ C') ∧
      (∀ s ∈ C, (∀ p ∈ P, ¬ SquareMeetsPatch p s) → s ∈ C') := by
  classical
  revert C hC hnonempty hsubsupport hdisjoint hallowed hexact hlocal
  induction P using Finset.induction_on with
  | empty =>
      intro C hC hnonempty hsubsupport hdisjoint hallowed hexact hlocal
      exact ⟨C, hC, by simp, by simp⟩
  | @insert p P hp ih =>
      intro C hC hnonempty hsubsupport hdisjoint hallowed hexact hlocal
      obtain ⟨old, hold, huniq⟩ := existsUnique_squareMeetingPatch_of_minimum
        boundary L k ρ C hC p (parent p)
        (hnonempty p (Finset.mem_insert_self p P))
        (hsubsupport p (Finset.mem_insert_self p P))
        (hallowed p (Finset.mem_insert_self p P))
        (by
          intro x hx
          have hmemEq := congrArg (fun t : Finset (Fin L × Fin L) => x ∈ t)
            (hexact p (Finset.mem_insert_self p P))
          exact (Finset.mem_inter.mp
            (Eq.mp hmemEq.symm hx)).1)
        (hlocal p (Finset.mem_insert_self p P))
      have huniq' : ∀ s ∈ C, SquareMeetsPatch p s → s = old := by
        intro s hs hmeet
        exact huniq s ⟨hs, hmeet⟩
      have hC₁ := replace_unique_squareMeetingPatch boundary L k ρ C hC
        p (parent p) old (hnonempty p (Finset.mem_insert_self p P))
        (hallowed p (Finset.mem_insert_self p P))
        (hexact p (Finset.mem_insert_self p P)) hold huniq'
        (hlocal p (Finset.mem_insert_self p P))
      let C₁ := insert (parent p) (C.erase old)
      have hC₁' : IsMinimumSquareCover boundary L k ρ C₁ := by
        simpa [C₁] using hC₁
      have hlocal₁ : ∀ q ∈ P, ∀ s ∈ C₁, SquareMeetsPatch q s →
          SquareLocalToPatch (chargeSupport ρ) q s := by
        intro q hq s hs hmeet
        rcases Finset.mem_insert.mp hs with hs | hs
        · subst s
          rcases hmeet with ⟨x, hxq, hxparent⟩
          have hxSupport : x ∈ chargeSupport ρ :=
            hsubsupport q (Finset.mem_insert_of_mem hq) hxq
          have hxP : x ∈ p := by
            have hxInter : x ∈ parent p ∩ chargeSupport ρ :=
              Finset.mem_inter.mpr ⟨hxparent, hxSupport⟩
            have hmemEq := congrArg (fun t : Finset (Fin L × Fin L) => x ∈ t)
              (hexact p (Finset.mem_insert_self p P))
            exact Eq.mp hmemEq hxInter
          have hpq : p ≠ q := by
            intro heq
            subst q
            exact hp hq
          exact False.elim ((Finset.disjoint_left.mp (hdisjoint p
            (Finset.mem_insert_self p P) q (Finset.mem_insert_of_mem hq) hpq)) hxP hxq)
        · exact hlocal q (Finset.mem_insert_of_mem hq) s
            (Finset.mem_erase.mp hs).2 hmeet
      obtain ⟨C₂, hC₂, hparents₂, hretained₂⟩ := ih C₁ hC₁'
        (by intro q hq; exact hnonempty q (Finset.mem_insert_of_mem hq))
        (by intro q hq; exact hsubsupport q (Finset.mem_insert_of_mem hq))
        (by
          intro q hq r hr hqr
          exact hdisjoint q (Finset.mem_insert_of_mem hq)
            r (Finset.mem_insert_of_mem hr) hqr)
        (by intro q hq; exact hallowed q (Finset.mem_insert_of_mem hq))
        (by intro q hq; exact hexact q (Finset.mem_insert_of_mem hq))
        hlocal₁
      refine ⟨C₂, hC₂, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with hqp | hq
        · subst q
          apply hretained₂ (parent p) (Finset.mem_insert_self _ _)
          intro r hr hmeet
          rcases hmeet with ⟨x, hxr, hxParent⟩
          have hxSupport : x ∈ chargeSupport ρ :=
            hsubsupport r (Finset.mem_insert_of_mem hr) hxr
          have hxP : x ∈ p := by
            have hxInter : x ∈ parent p ∩ chargeSupport ρ :=
              Finset.mem_inter.mpr ⟨hxParent, hxSupport⟩
            have hmemEq := congrArg (fun t : Finset (Fin L × Fin L) => x ∈ t)
              (hexact p (Finset.mem_insert_self p P))
            exact Eq.mp hmemEq hxInter
          have hpr : p ≠ r := by
            intro heq
            subst r
            exact hp hr
          exact (Finset.disjoint_left.mp (hdisjoint p
            (Finset.mem_insert_self p P) r (Finset.mem_insert_of_mem hr) hpr)) hxP hxr
        · exact hparents₂ q hq
      · intro s hs hnotMeet
        have hsne : s ≠ old := by
          intro heq
          subst s
          exact hnotMeet p (Finset.mem_insert_self p P) hold.2
        have hsC₁ : s ∈ C₁ := by
          exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsne, hs⟩)
        apply hretained₂ s hsC₁
        intro q hq
        exact hnotMeet q (Finset.mem_insert_of_mem hq)

end FroehlichSpencer.BKT

end
