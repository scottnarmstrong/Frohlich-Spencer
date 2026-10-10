/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.DualComplexD
public import FroehlichSpencer.FS82.Cubical.IntegerExactness

/-!
# the dual cells of a box of any dimension as cells of the bumped box

The dimension-generic form of `XY/Bump3.lean`.

A dual cell of the box `B` has, in each direction,
a dual vertex `v < B i` or a dual interval `e ≤ B i`.

Sending the dual vertex `v` to the vertex
`v + 1` and the dual interval `e` to the interval `e` of the box with sides `B i + 1` embeds the
dual cells as the cells none of whose vertex coordinates is extreme.

Under this embedding the dual
exterior difference is, up to the signs `sgnCell`, the transpose of the cubical boundary:

`stencil(c)(c') = −sgn(c) sgn(c') · ∂(bump c')(bump c)`.

This is the lattice form of Poincaré–Lefschetz duality used for relative fillings.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical

variable {d : ℕ} {B : Box d}

/-- The box whose cells are the dual cells of `B` and one outer layer. -/
def bumpedBoxD {d : ℕ} (B : Box d) : Box d := fun i => B i + 1

/-- A dual cell as a cell of the bumped box. -/
def bumpCell (c : DualCell d B) : Cell d (bumpedBoxD B) := fun i =>
  match c i with
  | Sum.inl v => Sum.inl ⟨v.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt v.isLt)⟩
  | Sum.inr e => Sum.inr ⟨e.val, e.isLt⟩

theorem bumpCell_inl {c : DualCell d B} {i : Fin d} {v : Fin (B i)} (h : c i = Sum.inl v) :
    bumpCell c i = Sum.inl ⟨v.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt v.isLt)⟩ := by
  simp only [bumpCell, h]

theorem bumpCell_inr {c : DualCell d B} {i : Fin d} {e : Fin (B i + 1)} (h : c i = Sum.inr e) :
    bumpCell c i = Sum.inr ⟨e.val, e.isLt⟩ := by
  simp only [bumpCell, h]

theorem bumpCell_coord_inj {c c' : DualCell d B} {i : Fin d} :
    bumpCell c i = bumpCell c' i ↔ c i = c' i := by
  constructor
  · intro h
    cases hc : c i with
    | inl v =>
      cases hc' : c' i with
      | inl w =>
        rw [bumpCell_inl hc, bumpCell_inl hc'] at h
        have hv : v.val + 1 = w.val + 1 := congrArg Fin.val (Sum.inl.inj h)
        exact congrArg Sum.inl (Fin.ext (by omega))
      | inr e =>
        rw [bumpCell_inl hc, bumpCell_inr hc'] at h
        exact absurd h (by simp)
    | inr e =>
      cases hc' : c' i with
      | inl w =>
        rw [bumpCell_inr hc, bumpCell_inl hc'] at h
        exact absurd h (by simp)
      | inr e' =>
        rw [bumpCell_inr hc, bumpCell_inr hc'] at h
        have he : e.val = e'.val := congrArg Fin.val (Sum.inr.inj h)
        exact congrArg Sum.inr (Fin.ext he)
  · intro h
    simp only [bumpCell, h]

theorem bumpCell_injective : Function.Injective (bumpCell (B := B)) :=
  fun _ _ h => funext fun i => bumpCell_coord_inj.mp (congrFun h i)

theorem coordIsEdge_bumpCell (c : DualCell d B) (i : Fin d) :
    coordIsEdge (bumpCell c i) ↔ (c i).isRight = true := by
  cases hc : c i with
  | inl v => simp [coordIsEdge, bumpCell_inl hc]
  | inr e => simp [coordIsEdge, bumpCell_inr hc]

/-! ## Signs -/

/-- The orientation sign of a dual cell: `(−1)` to the sum of its interval directions. -/
def sgnCell (c : DualCell d B) : ℤ := ∏ j ∈ dualCellAxes c, (-1 : ℤ) ^ j.val

theorem sgnCell_mul_self (c : DualCell d B) : sgnCell c * sgnCell c = 1 := by
  unfold sgnCell
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem sgnCell_sq_cast (c : DualCell d B) : ((sgnCell c : ℤ) : ℝ) * ((sgnCell c : ℤ) : ℝ) = 1 := by
  exact_mod_cast sgnCell_mul_self c

theorem sgnCell_of_insert {c c' : DualCell d B} {i : Fin d} {e : Fin (B i)}
    {e' : Fin (B i + 1)} (hc : c i = Sum.inl e) (hc' : c' i = Sum.inr e')
    (hP : ∀ j, j ≠ i → c j = c' j) :
    sgnCell c * sgnCell c' = (-1 : ℤ) ^ i.val := by
  have haxes : dualCellAxes c' = insert i (dualCellAxes c) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [dualCellAxes, hc']
    · simp [dualCellAxes, hP j hj, hj]
  have hi : i ∉ dualCellAxes c := by
    simp [dualCellAxes, hc]
  unfold sgnCell
  rw [haxes, Finset.prod_insert hi, mul_comm ((-1 : ℤ) ^ i.val), ← mul_assoc]
  have h := sgnCell_mul_self c
  unfold sgnCell at h
  rw [h, one_mul]

theorem rank_add_rank {c c' : DualCell d B} {i : Fin d}
    (hP : ∀ j, j ≠ i → c j = c' j) :
    dualVertexRankBefore c i + cellRankBefore (bumpCell c') i = i.val := by
  unfold dualVertexRankBefore cellRankBefore
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl (g := fun j : Fin d => if j < i then 1 else 0)
    fun j _ => ?_).trans ?_
  · by_cases hj : j < i
    · have hjP := hP j (ne_of_lt hj)
      by_cases hR : (c j).isRight = true
      · have hR' : coordIsEdge (bumpCell c' j) :=
          (coordIsEdge_bumpCell c' j).mpr (hjP ▸ hR)
        simp [hj, hR, hR']
      · have hR' : ¬ coordIsEdge (bumpCell c' j) := fun h =>
          hR (hjP ▸ (coordIsEdge_bumpCell c' j).mp h)
        simp [hj, hR, hR']
    · simp [hj]
  · rw [← Finset.card_filter]
    have hset : (Finset.univ.filter fun j : Fin d => j < i) = Finset.Iio i := by
      ext j
      simp
    rw [hset, Fin.card_Iio]

/-! ## The stencil and the boundary, axis by axis -/

/-- The contribution of direction `i` to the dual stencil coefficient. -/
noncomputable def stencilAxisTerm (c c' : DualCell d B) (i : Fin d) : ℝ :=
  match c i with
  | Sum.inl e => (-1 : ℝ) ^ dualVertexRankBefore c i *
      ((if dualUpperFace c i e = c' then 1 else 0) - (if dualLowerFace c i e = c' then 1 else 0))
  | Sum.inr _ => 0

theorem stencilBasis_apply (c c' : DualCell d B) :
    dualExteriorDifferenceStencilBasis c c' = ∑ i, stencilAxisTerm c c' i := by
  unfold dualExteriorDifferenceStencilBasis
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold stencilAxisTerm
  split <;> rename_i h <;> simp [h, Finsupp.single_apply]

/-- The contribution of direction `i` to the cubical boundary coefficient. -/
noncomputable def boundaryAxisTerm {B' : Box d} (c x : Cell d B') (i : Fin d) : ℤ :=
  match c i with
  | Sum.inl _ => 0
  | Sum.inr e => (-1 : ℤ) ^ cellRankBefore c i *
      ((if upperFace c i e = x then 1 else 0) - (if lowerFace c i e = x then 1 else 0))

theorem boundaryBasis_apply_eq_sum {B' : Box d} (c x : Cell d B') :
    boundaryBasis c x = ∑ i, boundaryAxisTerm c x i := by
  unfold boundaryBasis
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold boundaryAxisTerm
  split <;> rename_i h <;> simp [h, basisChain, Finsupp.single_apply]

theorem dualUpperFace_eq_iff {c c' : DualCell d B} {i : Fin d} {e : Fin (B i)}
    {e' : Fin (B i + 1)} (hc' : c' i = Sum.inr e') :
    dualUpperFace c i e = c' ↔ (∀ j, j ≠ i → c j = c' j) ∧ e'.val = e.val + 1 := by
  unfold dualUpperFace
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := congrFun h j
      rwa [Function.update_of_ne hj] at this
    · have := congrFun h i
      rw [Function.update_self, hc'] at this
      exact (congrArg Fin.val (Sum.inr.inj this)).symm
  · rintro ⟨hP, he⟩
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, hc']
      exact congrArg Sum.inr (Fin.ext he.symm)
    · rw [Function.update_of_ne hj, hP j hj]

theorem dualLowerFace_eq_iff {c c' : DualCell d B} {i : Fin d} {e : Fin (B i)}
    {e' : Fin (B i + 1)} (hc' : c' i = Sum.inr e') :
    dualLowerFace c i e = c' ↔ (∀ j, j ≠ i → c j = c' j) ∧ e'.val = e.val := by
  unfold dualLowerFace
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := congrFun h j
      rwa [Function.update_of_ne hj] at this
    · have := congrFun h i
      rw [Function.update_self, hc'] at this
      exact (congrArg Fin.val (Sum.inr.inj this)).symm
  · rintro ⟨hP, he⟩
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, hc']
      exact congrArg Sum.inr (Fin.ext he.symm)
    · rw [Function.update_of_ne hj, hP j hj]

theorem lowerFace_bump_eq_iff {c c' : DualCell d B} {i : Fin d} {e : Fin (B i)}
    (hc : c i = Sum.inl e) (ē : Fin (bumpedBoxD B i)) :
    lowerFace (bumpCell c') i ē = bumpCell c ↔
      (∀ j, j ≠ i → c j = c' j) ∧ ē.val = e.val + 1 := by
  unfold lowerFace vertexUpdate
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := congrFun h j
      rw [Function.update_of_ne hj] at this
      exact (bumpCell_coord_inj.mp this).symm
    · have := congrFun h i
      rw [Function.update_self, bumpCell_inl hc] at this
      exact congrArg Fin.val (Sum.inl.inj this)
  · rintro ⟨hP, he⟩
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, bumpCell_inl hc]
      exact congrArg Sum.inl (Fin.ext he)
    · rw [Function.update_of_ne hj]
      exact bumpCell_coord_inj.mpr (hP j hj).symm

theorem upperFace_bump_eq_iff {c c' : DualCell d B} {i : Fin d} {e : Fin (B i)}
    (hc : c i = Sum.inl e) (ē : Fin (bumpedBoxD B i)) :
    upperFace (bumpCell c') i ē = bumpCell c ↔
      (∀ j, j ≠ i → c j = c' j) ∧ ē.val = e.val := by
  unfold upperFace vertexUpdate
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := congrFun h j
      rw [Function.update_of_ne hj] at this
      exact (bumpCell_coord_inj.mp this).symm
    · have := congrFun h i
      rw [Function.update_self, bumpCell_inl hc] at this
      have hv := congrArg Fin.val (Sum.inl.inj this)
      simp only at hv
      omega
  · rintro ⟨hP, he⟩
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, bumpCell_inl hc]
      exact congrArg Sum.inl (Fin.ext (by simp only; omega))
    · rw [Function.update_of_ne hj]
      exact bumpCell_coord_inj.mpr (hP j hj).symm

/-- **The dual stencil is the transposed boundary of the bumped box, axis by axis.** -/
theorem stencilAxisTerm_eq (c c' : DualCell d B) (i : Fin d) :
    stencilAxisTerm c c' i =
      -((sgnCell c * sgnCell c' : ℤ) : ℝ) *
        ((boundaryAxisTerm (bumpCell c') (bumpCell c) i : ℤ) : ℝ) := by
  cases hc : c i with
  | inr u =>
    have hL : stencilAxisTerm c c' i = 0 := by simp only [stencilAxisTerm, hc]
    have hR : boundaryAxisTerm (bumpCell c') (bumpCell c) i = 0 := by
      cases hc' : c' i with
      | inl w => simp only [boundaryAxisTerm, bumpCell_inl hc']
      | inr e' =>
        simp only [boundaryAxisTerm, bumpCell_inr hc']
        have h1 : ¬ upperFace (bumpCell c') i ⟨e'.val, e'.isLt⟩ = bumpCell c := by
          intro h
          have := congrFun h i
          rw [bumpCell_inr hc] at this
          simp [upperFace, vertexUpdate] at this
        have h2 : ¬ lowerFace (bumpCell c') i ⟨e'.val, e'.isLt⟩ = bumpCell c := by
          intro h
          have := congrFun h i
          rw [bumpCell_inr hc] at this
          simp [lowerFace, vertexUpdate] at this
        simp [h1, h2]
    rw [hL, hR]
    simp
  | inl e =>
    cases hc' : c' i with
    | inl w =>
      have h1 : ¬ dualUpperFace c i e = c' := by
        intro h
        have := congrFun h i
        rw [hc'] at this
        simp [dualUpperFace] at this
      have h2 : ¬ dualLowerFace c i e = c' := by
        intro h
        have := congrFun h i
        rw [hc'] at this
        simp [dualLowerFace] at this
      have hL : stencilAxisTerm c c' i = 0 := by simp [stencilAxisTerm, hc, h1, h2]
      have hR : boundaryAxisTerm (bumpCell c') (bumpCell c) i = 0 := by
        simp only [boundaryAxisTerm, bumpCell_inl hc']
      rw [hL, hR]
      simp
    | inr e' =>
      by_cases hP : ∀ j, j ≠ i → c j = c' j
      · have hrank := rank_add_rank (i := i) hP
        have hsgn := sgnCell_of_insert hc hc' hP
        have hU : dualUpperFace c i e = c' ↔ e'.val = e.val + 1 :=
          (dualUpperFace_eq_iff hc').trans (and_iff_right hP)
        have hLo : dualLowerFace c i e = c' ↔ e'.val = e.val :=
          (dualLowerFace_eq_iff hc').trans (and_iff_right hP)
        have hUb : upperFace (bumpCell c') i ⟨e'.val, e'.isLt⟩ = bumpCell c ↔
            e'.val = e.val :=
          (upperFace_bump_eq_iff hc _).trans (and_iff_right hP)
        have hLb : lowerFace (bumpCell c') i ⟨e'.val, e'.isLt⟩ = bumpCell c ↔
            e'.val = e.val + 1 :=
          (lowerFace_bump_eq_iff hc _).trans (and_iff_right hP)
        have hL : stencilAxisTerm c c' i = (-1 : ℝ) ^ dualVertexRankBefore c i *
            ((if e'.val = e.val + 1 then 1 else 0) - (if e'.val = e.val then 1 else 0)) := by
          simp only [stencilAxisTerm, hc, hU, hLo]
        have hR : boundaryAxisTerm (bumpCell c') (bumpCell c) i =
            (-1 : ℤ) ^ cellRankBefore (bumpCell c') i *
              ((if e'.val = e.val then 1 else 0) - (if e'.val = e.val + 1 then 1 else 0)) := by
          simp only [boundaryAxisTerm, bumpCell_inr hc', hUb, hLb]
        rw [hL, hR, hsgn]
        have hpow : (-1 : ℝ) ^ dualVertexRankBefore c i =
            (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ cellRankBefore (bumpCell c') i := by
          rw [← pow_add, ← hrank, add_assoc, ← two_mul, pow_add, pow_mul]
          simp
        rw [hpow]
        push_cast
        ring
      · have hU : ¬ dualUpperFace c i e = c' := fun h =>
          hP ((dualUpperFace_eq_iff hc').mp h).1
        have hLo : ¬ dualLowerFace c i e = c' := fun h =>
          hP ((dualLowerFace_eq_iff hc').mp h).1
        have hUb : ¬ upperFace (bumpCell c') i ⟨e'.val, e'.isLt⟩ = bumpCell c := fun h =>
          hP ((upperFace_bump_eq_iff hc _).mp h).1
        have hLb : ¬ lowerFace (bumpCell c') i ⟨e'.val, e'.isLt⟩ = bumpCell c := fun h =>
          hP ((lowerFace_bump_eq_iff hc _).mp h).1
        have hL : stencilAxisTerm c c' i = 0 := by
          simp [stencilAxisTerm, hc, hU, hLo]
        have hR : boundaryAxisTerm (bumpCell c') (bumpCell c) i = 0 := by
          simp [boundaryAxisTerm, bumpCell_inr hc', hUb, hLb]
        rw [hL, hR]
        simp

/-- **The dual stencil is, up to orientation signs, the transposed boundary of the bumped box.** -/
theorem stencilBasis_eq_boundaryBasis (c c' : DualCell d B) :
    dualExteriorDifferenceStencilBasis c c' =
      -((sgnCell c * sgnCell c' : ℤ) : ℝ) *
        ((boundaryBasis (bumpCell c') (bumpCell c) : ℤ) : ℝ) := by
  rw [stencilBasis_apply, boundaryBasis_apply_eq_sum, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => stencilAxisTerm_eq c c' i

end FroehlichSpencer.FS82.XY.DualD

end
