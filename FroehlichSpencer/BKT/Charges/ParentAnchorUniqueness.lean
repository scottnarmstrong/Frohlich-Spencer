/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ParentTransitivity

/-! # Canonical statement for free clipped squares

For free squares that have not collapsed to the whole domain, the lower-left
corner is recoverable from the square. This lets the explicit parent formula
compose through the repository's chosen-statement selector.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- A free clipped square of side at most `L` determines its statement uniquely. -/
theorem squareAnchor_eq_of_kpSquare_eq_free (L k : ℕ)
    (hside : squareSide k ≤ L) (a b : Fin L × Fin L)
    (hEq : kpSquare .free L k a = kpSquare .free L k b) : a = b := by
  have ha : a ∈ kpSquare .free L k a := anchor_mem_kpSquare .free L k a
  have hb : b ∈ kpSquare .free L k b := anchor_mem_kpSquare .free L k b
  have ha' : a ∈ kpSquare .free L k b := by rw [← hEq]; exact ha
  have hb' : b ∈ kpSquare .free L k a := by rw [hEq]; exact hb
  have hba := (mem_kpSquare_free_iff L k hside b a).1 ha'
  have hab := (mem_kpSquare_free_iff L k hside a b).1 hb'
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- The explicit free parents compose even after passing through the
chosen-statement selector. -/
theorem ancestorParent_free_trans_total (L : ℕ) (k : PositiveSquareScale)
    (i j : ParentOffset) (hij : i.val < j.val) (hL : 0 < L)
    (s : Finset (Fin L × Fin L)) :
    ancestorParent .free L (parentScaleShift k i)
        (parentOffsetDiff i j hij) hL
        (ancestorParent .free L k i hL s) = ancestorParent .free L k j hL s := by
  let a := squareAnchor .free L k.val hL s
  by_cases hi : ancestorSide k i ≤ L
  · have hmidmem : parentFromAnchor .free L k i hL a ∈
        kpSquares .free L (ancestorScale k i) :=
      parentFromAnchor_mem_kpSquares .free L k i hL a
    have hselected : kpSquare .free L (ancestorScale k i)
        (squareAnchor .free L (ancestorScale k i) hL
          (parentFromAnchor .free L k i hL a)) =
        parentFromAnchor .free L k i hL a :=
      kpSquare_eq_of_squareAnchor .free L (ancestorScale k i) hL
        (parentFromAnchor .free L k i hL a) hmidmem
    have hexplicit : parentFromAnchor .free L k i hL a =
        kpSquare .free L (ancestorScale k i) (ancestorAnchor .free L k i hL a) := rfl
    have hanchors : squareAnchor .free L (ancestorScale k i) hL
        (parentFromAnchor .free L k i hL a) = ancestorAnchor .free L k i hL a :=
      squareAnchor_eq_of_kpSquare_eq_free L (ancestorScale k i) hi _ _
        (by rw [hselected, hexplicit])
    change parentFromAnchor .free L (parentScaleShift k i)
        (parentOffsetDiff i j hij) hL
        (squareAnchor .free L (ancestorScale k i) hL
          (parentFromAnchor .free L k i hL a)) =
      parentFromAnchor .free L k j hL a
    rw [hanchors]
    exact parentFromAnchor_free_trans_total L k i j hij hL a
  · have hmid : L < ancestorSide k i := by omega
    have htarget : L < ancestorSide k j := by
      rw [← ancestorSide_trans k i j hij]
      rw [ancestorSide_eq]
      have hbase : squareSide (parentScaleShift k i).val = ancestorSide k i := rfl
      rw [hbase]
      omega
    have hmidSide : squareSide (ancestorScale k i) > L := hmid
    have htargetSide : squareSide (ancestorScale k j) > L := htarget
    have hcollapsed : parentFromAnchor .free L k i hL a = Finset.univ := by
      simp [parentFromAnchor, kpSquare, hmidSide]
    change parentFromAnchor .free L (parentScaleShift k i)
        (parentOffsetDiff i j hij) hL
        (squareAnchor .free L (ancestorScale k i) hL
          (parentFromAnchor .free L k i hL a)) =
      parentFromAnchor .free L k j hL a
    rw [hcollapsed]
    have hmidScale : ancestorScale (parentScaleShift k i)
        (parentOffsetDiff i j hij) = ancestorScale k j := by
      change k.val + i.val + (j.val - i.val) = k.val + j.val
      omega
    have hsecondSide : squareSide
        (ancestorScale (parentScaleShift k i) (parentOffsetDiff i j hij)) > L := by
      rw [hmidScale]
      exact htargetSide
    simp [parentFromAnchor, kpSquare, htargetSide, hsecondSide]

end FroehlichSpencer.BKT

end
