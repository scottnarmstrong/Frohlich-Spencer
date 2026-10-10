/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ParentAnchorUniqueness

/-! # Canonical statement for proper periodic squares

A proper cyclic interval has one start point. This identifies the selected
statement of every noncollapsed periodic square and lifts parent transitivity
through the chosen-statement selector.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

private def periodicPredecessor (L : ℕ) (hL : 0 < L) (x : Fin L) : Fin L :=
  ⟨(x.val + L - 1) % L, Nat.mod_lt _ hL⟩

private theorem periodicModSubOne (L n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    ((n % L + L - 1) % L) = (n - 1) % L := by
  have hsum : n % L + L ≡ n + L [MOD L] :=
    (Nat.mod_modEq n L).add_right L
  have hsub : n % L + L - 1 ≡ n + L - 1 [MOD L] :=
    Nat.ModEq.sub (by omega) (by omega) hsum Nat.ModEq.rfl
  have hshift : n + L - 1 ≡ n - 1 [MOD L] := by
    change (n + L - 1) % L = (n - 1) % L
    rw [show n + L - 1 = n - 1 + L by omega]
    simp
  exact hsub.trans hshift

private theorem periodicPred_eq_offset (L : ℕ) (hL : 0 < L)
    (b x : Fin L) (i : ℕ) (hi : 0 < i)
    (hxi : x.val = (b.val + i) % L) :
    (periodicPredecessor L hL x).val = (b.val + (i - 1)) % L := by
  dsimp [periodicPredecessor]
  rw [hxi]
  calc
    ((b.val + i) % L + L - 1) % L = (b.val + i - 1) % L :=
      periodicModSubOne L (b.val + i) hL (by omega)
    _ = (b.val + (i - 1)) % L := by congr 2; omega

private theorem periodicSquare_x_predecessor_not_mem (L k : ℕ)
    (hL : 1 < L) (hside : squareSide k < L) (a : Fin L × Fin L) :
    (periodicPredecessor L (by omega) a.1, a.2) ∉ kpSquare .periodic L k a := by
  intro hp
  obtain ⟨i, hi, j, hj, hx, _⟩ :=
    (mem_kpSquare_periodic_iff L k hside a
      (periodicPredecessor L (by omega) a.1, a.2)).1 hp
  have hcong : a.1.val + (L - 1) ≡ a.1.val + i [MOD L] := by
    change (a.1.val + (L - 1)) % L = (a.1.val + i) % L
    rw [show a.1.val + (L - 1) = a.1.val + L - 1 by omega]
    exact hx
  have hiEq := (Nat.ModEq.refl a.1.val).add_left_cancel hcong
  have hiBound := Finset.mem_range.mp hi
  have hiMax : L - 1 = i := hiEq.eq_of_lt_of_lt (by omega) (by omega)
  omega

private theorem periodicSquare_y_predecessor_not_mem (L k : ℕ)
    (hL : 1 < L) (hside : squareSide k < L) (a : Fin L × Fin L) :
    (a.1, periodicPredecessor L (by omega) a.2) ∉ kpSquare .periodic L k a := by
  intro hp
  obtain ⟨i, hi, j, hj, _, hy⟩ :=
    (mem_kpSquare_periodic_iff L k hside a
      (a.1, periodicPredecessor L (by omega) a.2)).1 hp
  have hcong : a.2.val + (L - 1) ≡ a.2.val + j [MOD L] := by
    change (a.2.val + (L - 1)) % L = (a.2.val + j) % L
    rw [show a.2.val + (L - 1) = a.2.val + L - 1 by omega]
    exact hy
  have hjBound := Finset.mem_range.mp hj
  have hjEq := (Nat.ModEq.refl a.2.val).add_left_cancel hcong
  have hjMax : L - 1 = j := hjEq.eq_of_lt_of_lt (by omega) (by omega)
  omega

/-- A proper periodic quotient square determines its statement uniquely. -/
theorem squareAnchor_eq_of_kpSquare_eq_periodic (L k : ℕ)
    (hL : 1 < L) (hside : squareSide k < L)
    (a b : Fin L × Fin L)
    (hEq : kpSquare .periodic L k a = kpSquare .periodic L k b) : a = b := by
  have ha : a ∈ kpSquare .periodic L k a := anchor_mem_kpSquare .periodic L k a
  have hb : b ∈ kpSquare .periodic L k b := anchor_mem_kpSquare .periodic L k b
  have ha' : a ∈ kpSquare .periodic L k b := by rw [← hEq]; exact ha
  have hb' : b ∈ kpSquare .periodic L k a := by rw [hEq]; exact hb
  obtain ⟨i, hi, j, hj, hax, hay⟩ :=
    (mem_kpSquare_periodic_iff L k hside b a).1 ha'
  have hix : i = 0 := by
    by_contra hi0
    have hiPos : 0 < i := by omega
    have hiBound : i < squareSide k := Finset.mem_range.mp hi
    let p : Fin L × Fin L := (periodicPredecessor L (by omega) a.1, a.2)
    have hp : p ∈ kpSquare .periodic L k b := by
      apply (mem_kpSquare_periodic_iff L k hside b p).2
      refine ⟨i - 1, Finset.mem_range.mpr (by omega), j, hj, ?_, hay⟩
      simpa [p] using periodicPred_eq_offset L (by omega) b.1 a.1 i hiPos hax
    have hp' : p ∈ kpSquare .periodic L k a := by rw [hEq]; exact hp
    exact periodicSquare_x_predecessor_not_mem L k hL hside a hp'
  have hjy : j = 0 := by
    by_contra hj0
    have hjPos : 0 < j := by omega
    have hjBound : j < squareSide k := Finset.mem_range.mp hj
    let p : Fin L × Fin L := (a.1, periodicPredecessor L (by omega) a.2)
    have hp : p ∈ kpSquare .periodic L k b := by
      apply (mem_kpSquare_periodic_iff L k hside b p).2
      refine ⟨i, hi, j - 1, Finset.mem_range.mpr (by omega), hax, ?_⟩
      simpa [p] using periodicPred_eq_offset L (by omega) b.2 a.2 j hjPos hay
    have hp' : p ∈ kpSquare .periodic L k a := by rw [hEq]; exact hp
    exact periodicSquare_y_predecessor_not_mem L k hL hside a hp'
  have haxEq : a.1.val = b.1.val := by
    simpa [hix, Nat.mod_eq_of_lt b.1.isLt] using hax
  have hayEq : a.2.val = b.2.val := by
    simpa [hjy, Nat.mod_eq_of_lt b.2.isLt] using hay
  apply Prod.ext <;> apply Fin.ext <;> assumption

/-- Periodic explicit parents compose through the chosen-statement selector,
including the scale at which the parent collapses to the whole torus. -/
theorem ancestorParent_periodic_trans_total (L : ℕ) (k : PositiveSquareScale)
    (i j : ParentOffset) (hij : i.val < j.val) (hL : 0 < L)
    (s : Finset (Fin L × Fin L)) :
    ancestorParent .periodic L (parentScaleShift k i)
        (parentOffsetDiff i j hij) hL
        (ancestorParent .periodic L k i hL s) = ancestorParent .periodic L k j hL s := by
  let a := squareAnchor .periodic L k.val hL s
  by_cases hi : ancestorSide k i < L
  · have hmidmem : parentFromAnchor .periodic L k i hL a ∈
        kpSquares .periodic L (ancestorScale k i) :=
      parentFromAnchor_mem_kpSquares .periodic L k i hL a
    have hselected : kpSquare .periodic L (ancestorScale k i)
        (squareAnchor .periodic L (ancestorScale k i) hL
          (parentFromAnchor .periodic L k i hL a)) =
        parentFromAnchor .periodic L k i hL a :=
      kpSquare_eq_of_squareAnchor .periodic L (ancestorScale k i) hL
        (parentFromAnchor .periodic L k i hL a) hmidmem
    have hexplicit : parentFromAnchor .periodic L k i hL a =
        kpSquare .periodic L (ancestorScale k i) (ancestorAnchor .periodic L k i hL a) := rfl
    have hLgt : 1 < L := by
      have hsource : 2 ≤ squareSide k.val := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k.val := Nat.pow_le_pow_right (by omega) k.property
      have hsourceLe : squareSide k.val ≤ ancestorSide k i := by
        dsimp [squareSide, ancestorSide, ancestorScale]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hanchors : squareAnchor .periodic L (ancestorScale k i) hL
        (parentFromAnchor .periodic L k i hL a) = ancestorAnchor .periodic L k i hL a :=
      squareAnchor_eq_of_kpSquare_eq_periodic L (ancestorScale k i) hLgt hi _ _
        (by rw [hselected, hexplicit])
    change parentFromAnchor .periodic L (parentScaleShift k i)
        (parentOffsetDiff i j hij) hL
        (squareAnchor .periodic L (ancestorScale k i) hL
          (parentFromAnchor .periodic L k i hL a)) =
      parentFromAnchor .periodic L k j hL a
    rw [hanchors]
    by_cases hj : ancestorSide k j < L
    · exact parentFromAnchor_periodic_trans L k i j hij hL a
    · have htarget : L ≤ ancestorSide k j := by omega
      have htargetSide : squareSide (ancestorScale k j) ≥ L := htarget
      have hsecondSide : squareSide
          (ancestorScale (parentScaleShift k i) (parentOffsetDiff i j hij)) ≥ L := by
        change L ≤ ancestorSide (parentScaleShift k i) (parentOffsetDiff i j hij)
        rw [ancestorSide_trans k i j hij]
        exact htarget
      simp [parentFromAnchor, kpSquare, htargetSide, hsecondSide]
  · have hmid : L ≤ ancestorSide k i := by omega
    have htarget : L ≤ ancestorSide k j := by
      rw [← ancestorSide_trans k i j hij]
      rw [ancestorSide_eq]
      have hbase : squareSide (parentScaleShift k i).val = ancestorSide k i := rfl
      rw [hbase]
      omega
    have hmidSide : squareSide (ancestorScale k i) ≥ L := hmid
    have htargetSide : squareSide (ancestorScale k j) ≥ L := htarget
    have hcollapsed : parentFromAnchor .periodic L k i hL a = Finset.univ := by
      simp [parentFromAnchor, kpSquare, hmidSide]
    have hsecondSide : squareSide
        (ancestorScale (parentScaleShift k i) (parentOffsetDiff i j hij)) ≥ L := by
      change L ≤ ancestorSide (parentScaleShift k i) (parentOffsetDiff i j hij)
      rw [ancestorSide_trans k i j hij]
      exact htarget
    change parentFromAnchor .periodic L (parentScaleShift k i)
        (parentOffsetDiff i j hij) hL
        (squareAnchor .periodic L (ancestorScale k i) hL
          (parentFromAnchor .periodic L k i hL a)) =
      parentFromAnchor .periodic L k j hL a
    rw [hcollapsed]
    simp [parentFromAnchor, kpSquare, htargetSide, hsecondSide]

/-- The selected explicit parents compose at all free and periodic scales. -/
theorem ancestorParent_trans_total (boundary : SquareBoundary) (L : ℕ)
    (k : PositiveSquareScale) (i j : ParentOffset) (hij : i.val < j.val)
    (hL : 0 < L) (s : Finset (Fin L × Fin L)) :
    ancestorParent boundary L (parentScaleShift k i)
        (parentOffsetDiff i j hij) hL (ancestorParent boundary L k i hL s) =
      ancestorParent boundary L k j hL s := by
  cases boundary with
  | free => exact ancestorParent_free_trans_total L k i j hij hL s
  | periodic => exact ancestorParent_periodic_trans_total L k i j hij hL s

end FroehlichSpencer.BKT

end
