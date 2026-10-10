/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Duality.WiredBox

/-!
# Integer heights and wired currents

This module records the square-grid cochain calculation behind KP §6.1, pp. 32–33. The edge
current on the wired box is identified with an integer 1-cochain on the side-`L+1` dual square.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Duality

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Villain

variable {L : ℕ}

/-- The dual coordinate with the same integer value, viewed in `Fin (L+1)`. -/
def lowIndex (i : Fin L) : Fin (L + 1) := ⟨i.val, by omega⟩

/-- The dual coordinate immediately above a free coordinate. -/
def highIndex (i : Fin L) : Fin (L + 1) := ⟨i.val + 1, by omega⟩

/-- An integer current on the horizontal dual edge at a specified free column and dual row. -/
def horizontalCurrent (q : WiredEdge L → ℤ) (i : Fin L) (j : Fin (L + 1)) : ℤ :=
  q (horizontalDualEdge i j)

/-- An integer current on the vertical dual edge at a specified dual column and free row. -/
def verticalCurrent (q : WiredEdge L → ℤ) (i : Fin (L + 1)) (j : Fin L) : ℤ :=
  q (verticalDualEdge i j)

/-- The discrete curl around one face of the dual square. With the chosen primal orientation it
equals the primal divergence at the corresponding free vertex. -/
def dualCurl (q : WiredEdge L → ℤ) (i j : Fin L) : ℤ :=
  horizontalCurrent q i (lowIndex j) - horizontalCurrent q i (highIndex j) -
    verticalCurrent q (lowIndex i) j + verticalCurrent q (highIndex i) j

/-- The unit current ray from a free site to the wired right boundary. It is supported on the
vertical dual edges crossing the horizontal primal path to the boundary. -/
def unitSourceRay (site : SquareFreeVertex L) : WiredEdge L → ℤ
  | .inl _ => 0
  | .inr e => if e.2.1.val = site.2.val ∧ site.1.val < e.1.val then 1 else 0

/-- A horizontal dual edge has its upper incident free face as primal source. -/
theorem horizontalPrimalSrc_eq_some_iff
    (e : SquareFreeHorizontalEdge (L + 1)) (i j : Fin L) :
    horizontalPrimalSrc e = some (i, j) ↔
      e = horizontalDualEdgeData i (lowIndex j) := by
  rcases e with ⟨⟨x, hx⟩, y⟩
  constructor
  · intro h
    have hy : y.val < L := by
      by_contra hnot
      simp [horizontalPrimalSrc, hnot] at h
    have hp : (horizontalFaceX (⟨x, hx⟩, y), ⟨y.val, hy⟩) = (i, j) := by
      simpa [horizontalPrimalSrc, hy] using h
    have hX := congrArg Prod.fst hp
    have hY := congrArg Prod.snd hp
    apply Prod.ext
    · apply Subtype.ext
      apply Fin.ext
      have hxv := congrArg Fin.val hX
      simpa [horizontalFaceX, horizontalDualEdgeData, Fin.val_castLE] using hxv
    · apply Fin.ext
      have hyv := congrArg Fin.val hY
      simpa [lowIndex, horizontalDualEdgeData, Fin.val_castLE] using hyv
  · intro h
    rw [h]
    simp [horizontalPrimalSrc, horizontalDualEdgeData, horizontalFaceX, lowIndex]

/-- A horizontal dual edge has its lower incident free face as primal target. -/
theorem horizontalPrimalTgt_eq_some_iff
    (e : SquareFreeHorizontalEdge (L + 1)) (i j : Fin L) :
    horizontalPrimalTgt e = some (i, j) ↔
      e = horizontalDualEdgeData i (highIndex j) := by
  rcases e with ⟨⟨x, hx⟩, y⟩
  constructor
  · intro h
    have hzero : y.val ≠ 0 := by
      intro hy
      simp [horizontalPrimalTgt, hy] at h
    have hp : (horizontalFaceX (⟨x, hx⟩, y),
        ⟨y.val - 1, by have hy := y.isLt; omega⟩) = (i, j) := by
      simpa [horizontalPrimalTgt, hzero] using h
    have hX := congrArg Prod.fst hp
    have hY := congrArg Prod.snd hp
    apply Prod.ext
    · apply Subtype.ext
      apply Fin.ext
      have hxv := congrArg Fin.val hX
      simpa [horizontalFaceX, horizontalDualEdgeData, Fin.val_castLE] using hxv
    · apply Fin.ext
      have hyv := congrArg Fin.val hY
      simp only at hyv
      simp only [highIndex, Fin.val_mk, horizontalDualEdgeData]
      omega
  · intro h
    rw [h]
    simp [horizontalPrimalTgt, horizontalDualEdgeData, horizontalFaceX, highIndex]

/-- A vertical dual edge has its left incident free face as primal source. -/
theorem verticalPrimalSrc_eq_some_iff
    (e : SquareFreeVerticalEdge (L + 1)) (i j : Fin L) :
    verticalPrimalSrc e = some (i, j) ↔
      e = verticalDualEdgeData (highIndex i) j := by
  rcases e with ⟨x, ⟨y, hy⟩⟩
  constructor
  · intro h
    have hzero : x.val ≠ 0 := by
      intro hx
      simp [verticalPrimalSrc, hx] at h
    have hp : (⟨x.val - 1, by have hx := x.isLt; omega⟩, verticalFaceY (x, ⟨y, hy⟩)) =
        (i, j) := by
      simpa [verticalPrimalSrc, hzero] using h
    have hX := congrArg Prod.fst hp
    have hY := congrArg Prod.snd hp
    apply Prod.ext
    · apply Fin.ext
      have hxv := congrArg Fin.val hX
      change x.val - 1 = i.val at hxv
      change x.val = i.val + 1
      omega
    · apply Subtype.ext
      apply Fin.ext
      have hyv := congrArg Fin.val hY
      have hyv' : y.val = j.val := by
        simpa [verticalFaceY] using hyv
      simpa [verticalDualEdgeData, Fin.val_castLE] using hyv'
  · intro h
    rw [h]
    simp [verticalPrimalSrc, verticalDualEdgeData, verticalFaceY, highIndex]

/-- A vertical dual edge has its right incident free face as primal target. -/
theorem verticalPrimalTgt_eq_some_iff
    (e : SquareFreeVerticalEdge (L + 1)) (i j : Fin L) :
    verticalPrimalTgt e = some (i, j) ↔
      e = verticalDualEdgeData (lowIndex i) j := by
  rcases e with ⟨x, ⟨y, hy⟩⟩
  constructor
  · intro h
    have hx : x.val < L := by
      by_contra hn
      simp [verticalPrimalTgt, hn] at h
    have hp : (⟨x.val, hx⟩, verticalFaceY (x, ⟨y, hy⟩)) = (i, j) := by
      simpa [verticalPrimalTgt, hx] using h
    have hX := congrArg Prod.fst hp
    have hY := congrArg Prod.snd hp
    apply Prod.ext
    · apply Fin.ext
      have hxv := congrArg Fin.val hX
      simpa [lowIndex, verticalDualEdgeData] using hxv
    · apply Subtype.ext
      apply Fin.ext
      have hyv := congrArg Fin.val hY
      have hyv' : y.val = j.val := by
        simpa [verticalFaceY] using hyv
      simpa [verticalDualEdgeData, Fin.val_castLE] using hyv'
  · intro h
    rw [h]
    simp [verticalPrimalTgt, verticalDualEdgeData, verticalFaceY, lowIndex]

/-- A finite sum supported at one characterized index collapses to its unique value. -/
private theorem sum_if_unique_index {α M : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid M] (P : α → Prop) [DecidablePred P] (a : α) (ha : P a)
    (hunique : ∀ b, P b → b = a) (f : α → M) :
    (∑ b, if P b then f b else 0) = f a := by
  rw [Fintype.sum_eq_single a]
  · simp [ha]
  · intro b hba
    by_cases hb : P b
    · have := hunique b hb
      exact (hba this).elim
    · simp [hb]

/-- The divergence of a wired primal current at a free vertex is the curl around its dual face.
This is the incidence calculation underlying the current-height correspondence in KP §6.1, p. 33.
-/
theorem wiredCurrentDivergence_eq_dualCurl (q : WiredEdge L → ℤ) (i j : Fin L) :
    Villain.currentDivergence (wiredBoxGraph L) q (some (i, j)) = dualCurl q i j := by
  classical
  unfold Villain.currentDivergence dualCurl
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hsH :
      (∑ e : SquareFreeHorizontalEdge (L + 1),
        if (wiredBoxGraph L).src (.inl e) = some (i, j) then q (.inl e) else 0) =
        horizontalCurrent q i (lowIndex j) := by
    calc
      _ = q (.inl (horizontalDualEdgeData i (lowIndex j))) := by
        apply sum_if_unique_index (fun e => (wiredBoxGraph L).src (.inl e) = some (i, j))
          (horizontalDualEdgeData i (lowIndex j))
        · simpa [wiredBoxGraph, wiredBoxSrc] using
            (horizontalPrimalSrc_eq_some_iff _ _ _).2 rfl
        · intro e he
          change horizontalPrimalSrc e = some (i, j) at he
          exact (horizontalPrimalSrc_eq_some_iff e i j).1 he
      _ = horizontalCurrent q i (lowIndex j) := rfl
  have hsV :
      (∑ e : SquareFreeVerticalEdge (L + 1),
        if (wiredBoxGraph L).src (.inr e) = some (i, j) then q (.inr e) else 0) =
        verticalCurrent q (highIndex i) j := by
    calc
      _ = q (.inr (verticalDualEdgeData (highIndex i) j)) := by
        apply sum_if_unique_index (fun e => (wiredBoxGraph L).src (.inr e) = some (i, j))
          (verticalDualEdgeData (highIndex i) j)
        · simpa [wiredBoxGraph, wiredBoxSrc] using
            (verticalPrimalSrc_eq_some_iff _ _ _).2 rfl
        · intro e he
          change verticalPrimalSrc e = some (i, j) at he
          exact (verticalPrimalSrc_eq_some_iff e i j).1 he
      _ = verticalCurrent q (highIndex i) j := rfl
  have htH :
      (∑ e : SquareFreeHorizontalEdge (L + 1),
        if (wiredBoxGraph L).tgt (.inl e) = some (i, j) then q (.inl e) else 0) =
        horizontalCurrent q i (highIndex j) := by
    calc
      _ = q (.inl (horizontalDualEdgeData i (highIndex j))) := by
        apply sum_if_unique_index (fun e => (wiredBoxGraph L).tgt (.inl e) = some (i, j))
          (horizontalDualEdgeData i (highIndex j))
        · simpa [wiredBoxGraph, wiredBoxTgt] using
            (horizontalPrimalTgt_eq_some_iff _ _ _).2 rfl
        · intro e he
          change horizontalPrimalTgt e = some (i, j) at he
          exact (horizontalPrimalTgt_eq_some_iff e i j).1 he
      _ = horizontalCurrent q i (highIndex j) := rfl
  have htV :
      (∑ e : SquareFreeVerticalEdge (L + 1),
        if (wiredBoxGraph L).tgt (.inr e) = some (i, j) then q (.inr e) else 0) =
        verticalCurrent q (lowIndex i) j := by
    calc
      _ = q (.inr (verticalDualEdgeData (lowIndex i) j)) := by
        apply sum_if_unique_index (fun e => (wiredBoxGraph L).tgt (.inr e) = some (i, j))
          (verticalDualEdgeData (lowIndex i) j)
        · simpa [wiredBoxGraph, wiredBoxTgt] using
            (verticalPrimalTgt_eq_some_iff _ _ _).2 rfl
        · intro e he
          change verticalPrimalTgt e = some (i, j) at he
          exact (verticalPrimalTgt_eq_some_iff e i j).1 he
      _ = verticalCurrent q (lowIndex i) j := rfl
  rw [hsH, hsV, htH, htV]
  ring

/-- A current is neutral off the wired root exactly when its dual curl vanishes on every free
face. -/
theorem wiredNeutral_iff_dualCurl_zero (q : WiredEdge L → ℤ) :
    Villain.neutralAwayFrom (wiredBoxGraph L) none q ↔
      ∀ i j : Fin L, dualCurl q i j = 0 := by
  constructor
  · intro h i j
    have hface := h (some (i, j)) (Option.some_ne_none _)
    rwa [wiredCurrentDivergence_eq_dualCurl] at hface
  · intro h v hv
    cases v with
    | none => exact (hv rfl).elim
    | some p =>
        rcases p with ⟨i, j⟩
        rw [wiredCurrentDivergence_eq_dualCurl]
        exact h i j

@[simp] theorem horizontalCurrent_unitSourceRay (site : SquareFreeVertex L)
    (i : Fin L) (j : Fin (L + 1)) :
    horizontalCurrent (unitSourceRay site) i j = 0 := by
  simp [horizontalCurrent, unitSourceRay, horizontalDualEdge]

@[simp] theorem verticalCurrent_unitSourceRay (site : SquareFreeVertex L)
    (i : Fin (L + 1)) (j : Fin L) :
    verticalCurrent (unitSourceRay site) i j =
      if j.val = site.2.val ∧ site.1.val < i.val then 1 else 0 := by
  simp [verticalCurrent, unitSourceRay, verticalDualEdge, verticalDualEdgeData,
    Fin.val_castLE]

/-- The right-boundary ray has divergence `+1` at its starting site and zero at every other free
face. -/
theorem dualCurl_unitSourceRay (site : SquareFreeVertex L) (i j : Fin L) :
    dualCurl (unitSourceRay site) i j = if (i, j) = site then 1 else 0 := by
  simp only [dualCurl, horizontalCurrent_unitSourceRay, zero_sub, sub_zero,
    verticalCurrent_unitSourceRay]
  by_cases hrow : j.val = site.2.val
  · have hj : j = site.2 := Fin.ext hrow
    rw [hj]
    by_cases hcol : i.val = site.1.val
    · have hi : i = site.1 := Fin.ext hcol
      subst i
      simp [highIndex, lowIndex]
    · have hine : i ≠ site.1 := fun h => hcol (congrArg Fin.val h)
      have hlt : site.1.val < i.val + 1 ↔ site.1.val < i.val := by omega
      have hpair : (i, site.2) ≠ site := by
        intro he
        exact hcol (congrArg (fun p : Fin L × Fin L => p.1.val) he)
      simp [highIndex, lowIndex, hlt, hpair]
  · have hrow' : j ≠ site.2 := fun h => hrow (congrArg Fin.val h)
    have hpair : (i, j) ≠ site := by
      intro he
      exact hrow (congrArg (fun p : Fin L × Fin L => p.2.val) he)
    simp [hrow, highIndex, lowIndex, hpair]

/-- The path-sum height: first move right along the bottom row, then move up in the selected
column. -/
def heightPotential (q : WiredEdge L → ℤ) (p : SquareFreeVertex (L + 1)) : ℤ :=
  (∑ k : Fin L, if k.val < p.1.val then
      horizontalCurrent q k ⟨0, by omega⟩ else 0) +
    ∑ k : Fin L, if k.val < p.2.val then verticalCurrent q p.1 k else 0

/-- The dual integer height field has an oriented edge current equal to its target-minus-source
increment. -/
def dualHeightGradient (m : SquareFreeVertex (L + 1) → ℤ) (e : WiredEdge L) : ℤ :=
  m ((dualBoxGraph L).tgt e) - m ((dualBoxGraph L).src e)

/-- Adding a pinned height gradient to the unit ray gives the associated source current. -/
def unitSourceHeightCurrent (site : SquareFreeVertex L)
    (m : SquareFreeVertex (L + 1) → ℤ) : WiredEdge L → ℤ :=
  fun e => unitSourceRay site e + dualHeightGradient m e

/-- The source-current formula in KP's height sign convention: the fixed path current plus the
source-minus-target height jump across each dual edge. -/
def unitSourceKPHeightCurrent (site : SquareFreeVertex L)
    (m : SquareFreeVertex (L + 1) → ℤ) : WiredEdge L → ℤ :=
  fun e => unitSourceRay site e - dualHeightGradient m e

/-- The corresponding identity with the two height conventions interchanged. -/
theorem unitSourceKPHeightCurrent_neg (site : SquareFreeVertex L)
    (m : SquareFreeVertex (L + 1) → ℤ) :
    unitSourceKPHeightCurrent site (fun p => -m p) = unitSourceHeightCurrent site m := by
  funext e
  simp [unitSourceHeightCurrent, unitSourceKPHeightCurrent, dualHeightGradient]
  ring

@[simp] theorem horizontalCurrent_dualHeightGradient
    (m : SquareFreeVertex (L + 1) → ℤ) (i : Fin L) (j : Fin (L + 1)) :
    horizontalCurrent (dualHeightGradient m) i j =
      m (highIndex i, j) - m (lowIndex i, j) := by
  simp [horizontalCurrent, dualHeightGradient, dualBoxGraph, squareFreeGraph,
    horizontalDualEdge, highIndex, lowIndex]
  congr 1

@[simp] theorem verticalCurrent_dualHeightGradient
    (m : SquareFreeVertex (L + 1) → ℤ) (i : Fin (L + 1)) (j : Fin L) :
    verticalCurrent (dualHeightGradient m) i j =
      m (i, highIndex j) - m (i, lowIndex j) := by
  simp [verticalCurrent, dualHeightGradient, dualBoxGraph, squareFreeGraph,
    verticalDualEdge, highIndex, lowIndex]
  congr 1

/-- A height gradient has zero discrete curl around every dual square. -/
theorem dualCurl_dualHeightGradient (m : SquareFreeVertex (L + 1) → ℤ)
    (i j : Fin L) : dualCurl (dualHeightGradient m) i j = 0 := by
  simp only [dualCurl]
  rw [horizontalCurrent_dualHeightGradient, horizontalCurrent_dualHeightGradient,
    verticalCurrent_dualHeightGradient, verticalCurrent_dualHeightGradient]
  ring

/-- The KP-sign source current (ray minus target-minus-source gradient) has the same unit curl as
the boundary ray. -/
theorem dualCurl_unitSourceKPHeightCurrent (site : SquareFreeVertex L)
    (m : SquareFreeVertex (L + 1) → ℤ) (i j : Fin L) :
    dualCurl (unitSourceKPHeightCurrent site m) i j = if (i, j) = site then 1 else 0 := by
  have hsub : dualCurl (unitSourceKPHeightCurrent site m) i j =
      dualCurl (unitSourceRay site) i j - dualCurl (dualHeightGradient m) i j := by
    simp [unitSourceKPHeightCurrent, dualCurl, horizontalCurrent, verticalCurrent]
    ring
  rw [hsub, dualCurl_unitSourceRay, dualCurl_dualHeightGradient]
  simp

/-- A KP-sign height current has divergence `+1` at its source and zero at every other free face.
-/
theorem unitSourceKPHeightCurrent_characterCurrent (site : SquareFreeVertex L)
    (m : SquareFreeVertex (L + 1) → ℤ) :
    Villain.characterCurrent (wiredBoxGraph L) none (some site)
      (unitSourceKPHeightCurrent site m) := by
  intro k hk
  cases k with
  | none => exact (hk rfl).elim
  | some p =>
      rcases p with ⟨i, j⟩
      rw [wiredCurrentDivergence_eq_dualCurl, dualCurl_unitSourceKPHeightCurrent]
      simp

/-- Adding one more coordinate to a truncated finite sum adds precisely its last term. -/
theorem sum_fin_if_lt_succ_sub (n : Fin L) (f : Fin L → ℤ) :
    (∑ k : Fin L, (if k.val < n.val + 1 then f k else 0)) -
      (∑ k : Fin L, (if k.val < n.val then f k else 0)) = f n := by
  rw [← Finset.sum_sub_distrib]
  have hpoint (k : Fin L) :
      (if k.val < n.val + 1 then f k else 0) -
        (if k.val < n.val then f k else 0) = if k = n then f k else 0 := by
    by_cases hkn : k = n
    · subst k
      simp
    · have hval : k.val ≠ n.val := fun h => hkn (Fin.ext h)
      have hlt : k.val < n.val + 1 ↔ k.val < n.val := by omega
      simp [hlt, hkn]
  calc
    _ = ∑ k : Fin L, if k = n then f k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hpoint k
    _ = f n := by simp

/-- Telescoping differences along the first `n` rows of a finite grid. -/
theorem sum_fin_if_lt_dual_diff (n : ℕ) (hn : n ≤ L)
    (f : Fin (L + 1) → ℤ) :
    (∑ k : Fin L, (if k.val < n then
      f ⟨k.val + 1, by have hk := k.isLt; omega⟩ -
        f ⟨k.val, by have hk := k.isLt; omega⟩ else 0)) =
      f ⟨n, by omega⟩ - f 0 := by
  revert hn
  induction n with
  | zero =>
      intro hn
      simp
  | succ n ih =>
      intro hn
      have hnL : n ≤ L := by omega
      let kn : Fin L := ⟨n, by omega⟩
      let delta : Fin L → ℤ := fun k =>
        f ⟨k.val + 1, by have hk := k.isLt; omega⟩ -
          f ⟨k.val, by have hk := k.isLt; omega⟩
      have hsplit :
          (∑ k : Fin L, (if k.val < n + 1 then delta k else 0)) =
            (∑ k : Fin L, (if k.val < n then delta k else 0)) + delta kn := by
        calc
          _ = ∑ k : Fin L,
                ((if k.val < n then delta k else 0) +
                  (if k = kn then delta k else 0)) := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hlt : k.val < n
            · have hne : k ≠ kn := by
                intro he
                have hv := congrArg Fin.val he
                simp [kn] at hv
                omega
              have hsucc : k.val < n + 1 := by omega
              simp [hlt, hsucc, hne]
            · by_cases heq : k.val = n
              · have hkn : k = kn := Fin.ext heq
                subst k
                simp [kn]
              · have hgt : n < k.val := by omega
                have hnot : ¬k.val < n + 1 := by omega
                have hne : k ≠ kn := by
                  intro he
                  have hv := congrArg Fin.val he
                  simp [kn] at hv
                  omega
                simp [hlt, hnot, hne]
          _ = _ := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [hsplit, ih hnL]
      simp only [delta]
      ring

/-- Integrating the gradient of an integer height recovers that height up to the selected additive
constant. -/
theorem heightPotential_dualHeightGradient (m : SquareFreeVertex (L + 1) → ℤ)
    (p : SquareFreeVertex (L + 1)) :
    heightPotential (dualHeightGradient m) p = m p - m (0, 0) := by
  have hx :
      (∑ k : Fin L, (if k.val < p.1.val then
        horizontalCurrent (dualHeightGradient m) k 0 else 0)) =
          m (p.1, 0) - m (0, 0) := by
    simp only [horizontalCurrent_dualHeightGradient]
    simpa [highIndex, lowIndex] using
      (sum_fin_if_lt_dual_diff (L := L) p.1.val (by omega)
        (fun k => m (k, 0)))
  have hy :
      (∑ k : Fin L, (if k.val < p.2.val then
        verticalCurrent (dualHeightGradient m) p.1 k else 0)) =
          m (p.1, p.2) - m (p.1, 0) := by
    simp only [verticalCurrent_dualHeightGradient]
    simpa [highIndex, lowIndex] using
      (sum_fin_if_lt_dual_diff (L := L) p.2.val (by omega)
        (fun k => m (p.1, k)))
  have hzero : (⟨0, by omega⟩ : Fin (L + 1)) = 0 := Fin.ext rfl
  unfold heightPotential
  rw [hzero, hx, hy]
  ring

/-- The second finite sum in a height potential adds the current on its last vertical edge. -/
theorem sum_fin_if_lt_succ_sub_vertical (q : WiredEdge L → ℤ) (i : Fin (L + 1))
    (j : Fin L) :
    (∑ k : Fin L, (if k.val < j.val + 1 then verticalCurrent q i k else 0)) -
      (∑ k : Fin L, (if k.val < j.val then verticalCurrent q i k else 0)) =
        verticalCurrent q i j :=
  sum_fin_if_lt_succ_sub j (fun k => verticalCurrent q i k)

/-- The discrete curl condition makes the row-first path sum have the prescribed horizontal
increments. -/
theorem heightPotential_horizontal_step (q : WiredEdge L → ℤ)
    (hcurl : ∀ i j : Fin L, dualCurl q i j = 0) (i : Fin L) (j : Fin (L + 1)) :
    heightPotential q (highIndex i, j) - heightPotential q (lowIndex i, j) =
      horizontalCurrent q i j := by
  have hbottom := sum_fin_if_lt_succ_sub i
    (fun k => horizontalCurrent q k 0)
  have hvertical :
      (∑ k : Fin L, (if k.val < j.val then verticalCurrent q (highIndex i) k else 0)) -
        (∑ k : Fin L, (if k.val < j.val then verticalCurrent q (lowIndex i) k else 0)) =
          horizontalCurrent q i j - horizontalCurrent q i 0 := by
    calc
      _ = ∑ k : Fin L,
            (if k.val < j.val then
              verticalCurrent q (highIndex i) k - verticalCurrent q (lowIndex i) k
             else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkj : k.val < j.val <;> simp [hkj]
      _ = ∑ k : Fin L,
            (if k.val < j.val then
              horizontalCurrent q i (highIndex k) - horizontalCurrent q i (lowIndex k)
             else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkj : k.val < j.val
        · have hc := hcurl i k
          dsimp [dualCurl] at hc
          simp only [horizontalCurrent, verticalCurrent, lowIndex, highIndex] at hc ⊢
          omega
        · simp [hkj]
      _ = horizontalCurrent q i j - horizontalCurrent q i 0 := by
        simpa [horizontalCurrent, highIndex, lowIndex, Fin.val_mk] using
          (sum_fin_if_lt_dual_diff (L := L) j.val (by omega)
            (fun k => horizontalCurrent q i k))
  have hzero : (⟨0, by omega⟩ : Fin (L + 1)) = 0 := Fin.ext rfl
  simp only [highIndex, lowIndex] at hbottom hvertical
  simp only [heightPotential, highIndex, lowIndex, Fin.val_mk, hzero]
  linear_combination hbottom + hvertical

/-- The rectangular path-sum height is zero at the lower-left dual face. -/
theorem heightPotential_root (q : WiredEdge L → ℤ) :
    heightPotential q (0, 0) = 0 := by
  simp [heightPotential]

/-- A vertical height increment records the current on the crossed dual edge. -/
theorem heightPotential_vertical_step (q : WiredEdge L → ℤ) (i : Fin (L + 1))
    (j : Fin L) :
    heightPotential q (i, highIndex j) - heightPotential q (i, lowIndex j) =
      verticalCurrent q i j := by
  simp only [heightPotential, highIndex, lowIndex, Fin.val_mk]
  rw [add_sub_add_left_eq_sub]
  exact sum_fin_if_lt_succ_sub_vertical q i j

/-- The path-sum height reconstructs every curl-free integer edge cochain. -/
theorem dualHeightGradient_heightPotential (q : WiredEdge L → ℤ)
    (hcurl : ∀ i j : Fin L, dualCurl q i j = 0) :
    dualHeightGradient (heightPotential q) = q := by
  funext e
  cases e with
  | inl e =>
      let i : Fin L := ⟨e.1.1.val, by have he := e.1.2; omega⟩
      have he : horizontalDualEdgeData i e.2 = e := by
        apply Prod.ext
        · apply Subtype.ext
          apply Fin.ext
          rfl
        · rfl
      have hstep := heightPotential_horizontal_step q hcurl i e.2
      simpa [dualHeightGradient, dualBoxGraph, squareFreeGraph, horizontalCurrent,
        horizontalDualEdge, horizontalDualEdgeData, highIndex, lowIndex, i, he] using hstep
  | inr e =>
      let j : Fin L := ⟨e.2.1.val, by have he := e.2.2; omega⟩
      have he : verticalDualEdgeData e.1 j = e := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          apply Fin.ext
          rfl
      have hstep := heightPotential_vertical_step q e.1 j
      simpa [dualHeightGradient, dualBoxGraph, squareFreeGraph, verticalCurrent,
        verticalDualEdge, verticalDualEdgeData, highIndex, lowIndex, j, he] using hstep

/-- Curl-free currents are in bijection with dual integer heights pinned at the lower-left face.
This is the cochain form of planar duality; identifying the curl with the wired graph divergence
is given by `wiredCurrentDivergence_eq_dualCurl`. -/
theorem dualCurlFree_iff_existsUnique_pinnedHeight (q : WiredEdge L → ℤ) :
    (∀ i j : Fin L, dualCurl q i j = 0) ↔
      ∃! m : SquareFreeVertex (L + 1) → ℤ,
        m (0, 0) = 0 ∧ dualHeightGradient m = q := by
  constructor
  · intro hcurl
    let m : SquareFreeVertex (L + 1) → ℤ := heightPotential q
    have hm : m (0, 0) = 0 ∧ dualHeightGradient m = q :=
      ⟨heightPotential_root q, dualHeightGradient_heightPotential q hcurl⟩
    refine ⟨m, hm, ?_⟩
    intro n hn
    funext p
    have hgrad : dualHeightGradient m = dualHeightGradient n :=
      (dualHeightGradient_heightPotential q hcurl).trans hn.2.symm
    have hpot := congrArg (fun r : WiredEdge L → ℤ => heightPotential r p) hgrad
    rw [heightPotential_dualHeightGradient, heightPotential_dualHeightGradient,
      hm.1, hn.1] at hpot
    simpa [m] using hpot.symm
  · intro hheight i j
    rcases hheight with ⟨m, hm, _⟩
    rw [← hm.2]
    exact dualCurl_dualHeightGradient m i j

/-- The wired divergence-free currents are in bijection with integer heights pinned at the
lower-left dual face. The root constraint follows from total divergence zero. -/
theorem wiredNeutral_iff_existsUnique_pinnedHeight (q : WiredEdge L → ℤ) :
    Villain.neutralAwayFrom (wiredBoxGraph L) none q ↔
      ∃! m : SquareFreeVertex (L + 1) → ℤ,
        m (0, 0) = 0 ∧ dualHeightGradient m = q := by
  rw [wiredNeutral_iff_dualCurl_zero, dualCurlFree_iff_existsUnique_pinnedHeight]

/-- The source-current condition is equivalent to a unique pinned height plus the fixed unit ray
to the wired boundary. This is the affine version of the planar current-height correspondence in
KP Proposition 6.1, pp. 33–34. -/
theorem wiredCharacterCurrent_iff_existsUnique_pinnedHeight (q : WiredEdge L → ℤ)
    (site : SquareFreeVertex L) :
    Villain.characterCurrent (wiredBoxGraph L) none (some site) q ↔
      ∃! m : SquareFreeVertex (L + 1) → ℤ,
        m (0, 0) = 0 ∧ q = unitSourceHeightCurrent site m := by
  constructor
  · intro hq
    let q₀ : WiredEdge L → ℤ := fun e => q e - unitSourceRay site e
    have hqcurl : ∀ i j : Fin L, dualCurl q i j = if (i, j) = site then 1 else 0 := by
      intro i j
      have hd := hq (some (i, j)) (Option.some_ne_none _)
      rw [wiredCurrentDivergence_eq_dualCurl] at hd
      simpa [Villain.characterCurrent] using hd
    have hq₀curl : ∀ i j : Fin L, dualCurl q₀ i j = 0 := by
      intro i j
      have hsub : dualCurl q₀ i j = dualCurl q i j - dualCurl (unitSourceRay site) i j := by
        simp [q₀, dualCurl, horizontalCurrent, verticalCurrent]
        ring
      rw [hsub, hqcurl i j, dualCurl_unitSourceRay]
      simp
    have hheight :=
      (dualCurlFree_iff_existsUnique_pinnedHeight q₀).1 hq₀curl
    rcases hheight with ⟨m, hm, hmunique⟩
    refine ⟨m, ?_, ?_⟩
    · constructor
      · exact hm.1
      · funext e
        have he := congrFun hm.2 e
        dsimp [q₀, unitSourceHeightCurrent] at he ⊢
        omega
    · intro n hn
      apply hmunique n
      refine ⟨hn.1, ?_⟩
      funext e
      have he := congrFun hn.2 e
      dsimp [q₀, unitSourceHeightCurrent] at he ⊢
      omega
  · rintro ⟨m, hm, _⟩
    intro k hk
    cases k with
    | none => exact (hk rfl).elim
    | some p =>
        rcases p with ⟨i, j⟩
        have hq : q = unitSourceHeightCurrent site m := hm.2
        rw [wiredCurrentDivergence_eq_dualCurl, hq]
        have hadd : dualCurl (unitSourceHeightCurrent site m) i j =
            dualCurl (unitSourceRay site) i j + dualCurl (dualHeightGradient m) i j := by
          simp [unitSourceHeightCurrent, dualCurl, horizontalCurrent, verticalCurrent]
          ring
        rw [hadd, dualCurl_unitSourceRay, dualCurl_dualHeightGradient]
        simp

/-- In KP's sign convention, unit-source currents equal the boundary ray plus the oriented
source-minus-target height jump. -/
theorem wiredCharacterCurrent_iff_existsUnique_pinnedKPHeight (q : WiredEdge L → ℤ)
    (site : SquareFreeVertex L) :
    Villain.characterCurrent (wiredBoxGraph L) none (some site) q ↔
      ∃! m : SquareFreeVertex (L + 1) → ℤ,
        m (0, 0) = 0 ∧ q = unitSourceKPHeightCurrent site m := by
  let P : (SquareFreeVertex (L + 1) → ℤ) → Prop := fun m =>
    m (0, 0) = 0 ∧ q = unitSourceHeightCurrent site m
  let Q : (SquareFreeVertex (L + 1) → ℤ) → Prop := fun m =>
    m (0, 0) = 0 ∧ q = unitSourceKPHeightCurrent site m
  have hneg (m : SquareFreeVertex (L + 1) → ℤ) : P m ↔ Q (fun p => -m p) := by
    change (m (0, 0) = 0 ∧ q = unitSourceHeightCurrent site m) ↔
      ((fun p => -m p) (0, 0) = 0 ∧
        q = unitSourceKPHeightCurrent site (fun p => -m p))
    constructor
    · rintro ⟨hm, hq⟩
      refine ⟨by simp [hm], ?_⟩
      simpa [unitSourceKPHeightCurrent_neg] using hq
    · rintro ⟨hm, hq⟩
      refine ⟨by simpa using hm, ?_⟩
      simpa [unitSourceKPHeightCurrent_neg] using hq
  have hP : (∃! m, P m) ↔ (∃! m, Q m) := by
    constructor
    · rintro ⟨m, hm, hmunique⟩
      refine ⟨fun p => -m p, (hneg m).mp hm, ?_⟩
      intro n hn
      have hnP : P (fun p => -n p) := by
        apply (hneg (fun p => -n p)).2
        simpa using hn
      have heq : (fun p => -n p) = m := hmunique _ hnP
      funext p
      have hp := congrFun heq p
      omega
    · rintro ⟨n, hn, hnunique⟩
      refine ⟨fun p => -n p, ?_, ?_⟩
      · apply (hneg (fun p => -n p)).2
        simpa using hn
      · intro m hm
        have hmQ : Q (fun p => -m p) := (hneg m).1 hm
        have heq : (fun p => -m p) = n := hnunique _ hmQ
        funext p
        have hp := congrFun heq p
        omega
  rw [wiredCharacterCurrent_iff_existsUnique_pinnedHeight]
  change (∃! m, P m) ↔ (∃! m, Q m)
  exact hP

end FroehlichSpencer.BKT.Duality

end
