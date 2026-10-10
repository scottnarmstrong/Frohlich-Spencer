/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawBoundaryPotentials
public import FroehlichSpencer.FS82.Wilson.AreaLawComponents
public import FroehlichSpencer.FS82.Wilson.AreaLawProjection

/-!
# A source-touching support component carries the rectangular boundary

Four plaquette curl tests read the four oriented sides of the rectangular
source. Their equality forces a component boundary that touches the source to
contain every source link.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

@[expose] def areaLawRectangleBottomLink {B : Box 4} {L : ℕ}
    (hL : L ≤ B 0) (i : Fin L) : Cell 4 B :=
  areaLawRectangleHorizontalLink (Fin.castLE hL i)
    ⟨0, Nat.zero_lt_succ (B 1)⟩

@[expose] def areaLawRectangleTopLink {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (i : Fin L) : Cell 4 B :=
  areaLawRectangleHorizontalLink (Fin.castLE hL i)
    ⟨T, Nat.lt_succ_of_le hT⟩

@[expose] def areaLawRectangleLeftLink {B : Box 4} {T : ℕ}
    (hT : T ≤ B 1) (j : Fin T) : Cell 4 B :=
  areaLawRectangleVerticalLink ⟨0, Nat.zero_lt_succ (B 0)⟩
    (Fin.castLE hT j)

@[expose] def areaLawRectangleRightLink {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (j : Fin T) : Cell 4 B :=
  areaLawRectangleVerticalLink ⟨L, Nat.lt_succ_of_le hL⟩
    (Fin.castLE hT j)

@[expose] noncomputable def areaLawRectanglePerimeterCells {B : Box 4}
    (L T : ℕ) (hL : L ≤ B 0) (hT : T ≤ B 1) : Finset (Cell 4 B) :=
  Finset.univ.image (areaLawRectangleBottomLink hL) ∪
    (Finset.univ.image (areaLawRectangleTopLink hL hT) ∪
      (Finset.univ.image (areaLawRectangleLeftLink hT) ∪
        Finset.univ.image (areaLawRectangleRightLink hL hT)))

private theorem row_support_subset_image {B : Box 4} {L : ℕ}
    (hL : L ≤ B 0) (y : Fin (B 1 + 1)) :
    (areaLawRectangleHorizontalRow L hL y).support ⊆
      Finset.univ.image (fun i : Fin L =>
        areaLawRectangleHorizontalLink (Fin.castLE hL i) y) := by
  classical
  intro c hc
  change c ∈ (∑ i : Fin L,
    basisChain (areaLawRectangleHorizontalLink (Fin.castLE hL i) y)).support at hc
  have hsum := Finsupp.support_finsetSum hc
  rcases Finset.mem_biUnion.mp hsum with ⟨i, hi, hterm⟩
  have hsingle : c = areaLawRectangleHorizontalLink (Fin.castLE hL i) y := by
    have hne : (basisChain
        (areaLawRectangleHorizontalLink (Fin.castLE hL i) y)) c ≠ 0 :=
      Finsupp.mem_support_iff.mp hterm
    by_contra h
    simp [basisChain, h] at hne
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hsingle.symm⟩

private theorem column_support_subset_image {B : Box 4} {_L : ℕ} {T : ℕ}
    (_hL : _L ≤ B 0) (hT : T ≤ B 1) (x : Fin (B 0 + 1)) :
    (areaLawRectangleVerticalColumn T hT x).support ⊆
      Finset.univ.image (fun j : Fin T =>
        areaLawRectangleVerticalLink x (Fin.castLE hT j)) := by
  classical
  intro c hc
  change c ∈ (∑ j : Fin T,
    basisChain (areaLawRectangleVerticalLink x (Fin.castLE hT j))).support at hc
  have hsum := Finsupp.support_finsetSum hc
  rcases Finset.mem_biUnion.mp hsum with ⟨j, hj, hterm⟩
  have hsingle : c = areaLawRectangleVerticalLink x (Fin.castLE hT j) := by
    have hne : (basisChain
        (areaLawRectangleVerticalLink x (Fin.castLE hT j)) c) ≠ 0 :=
      Finsupp.mem_support_iff.mp hterm
    by_contra h
    simp [basisChain, h] at hne
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hsingle.symm⟩

theorem wilsonRectangleLoop_support_subset_perimeter {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) :
    (wilsonRectangleLoop L T hL hT).support ⊆
      areaLawRectanglePerimeterCells L T hL hT := by
  classical
  rw [wilsonRectangleLoop_eq_perimeterRows]
  intro c hc
  let bot := areaLawRectangleHorizontalRow L hL
    ⟨0, Nat.zero_lt_succ (B 1)⟩
  let top := areaLawRectangleHorizontalRow L hL
    ⟨T, Nat.lt_succ_of_le hT⟩
  let right := areaLawRectangleVerticalColumn T hT
    ⟨L, Nat.lt_succ_of_le hL⟩
  let left := areaLawRectangleVerticalColumn T hT
    ⟨0, Nat.zero_lt_succ (B 0)⟩
  change c ∈ (bot - top + right - left).support at hc
  have hsupport : (bot - top + right - left).support ⊆
      (bot.support ∪ top.support) ∪ (right.support ∪ left.support) := by
    calc
      (bot - top + right - left).support = ((bot - top) + (right - left)).support := by
        congr 1
        abel
      _ ⊆ (bot - top).support ∪ (right - left).support := Finsupp.support_add
      _ ⊆ (bot.support ∪ top.support) ∪ (right.support ∪ left.support) := by
        exact Finset.union_subset_union Finsupp.support_sub Finsupp.support_sub
  rcases Finset.mem_union.mp (hsupport hc) with hrows | hcols
  · rcases Finset.mem_union.mp hrows with hbot | htop
    · exact Finset.mem_union_left _ (row_support_subset_image hL _ hbot)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (row_support_subset_image hL _ htop))
  · rcases Finset.mem_union.mp hcols with hright | hleft
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (column_support_subset_image hL hT _ hright)))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_left _ (column_support_subset_image hL hT _ hleft)))

@[simp] theorem areaLawRectangleHorizontalLink_axes {B : Box 4}
    (x : Fin (B 0)) (y : Fin (B 1 + 1)) :
    cellAxes (areaLawRectangleHorizontalLink x y) = {0} := by
  classical
  unfold areaLawRectangleHorizontalLink
  rw [cellAxes_edgeCell_eq_insert]
  have hv : cellAxes (vertexUpdate (wilsonRectangleBaseCell B) 1 y) = ∅ := by
    ext k
    simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases k <;>
      simp [coordIsEdge, vertexUpdate, wilsonRectangleBaseCell]
  rw [hv]
  simp

@[simp] theorem areaLawRectangleVerticalLink_axes {B : Box 4}
    (x : Fin (B 0 + 1)) (y : Fin (B 1)) :
    cellAxes (areaLawRectangleVerticalLink x y) = {1} := by
  classical
  unfold areaLawRectangleVerticalLink
  rw [cellAxes_edgeCell_eq_insert]
  have hv : cellAxes (vertexUpdate (wilsonRectangleBaseCell B) 0 x) = ∅ := by
    ext k
    simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases k <;>
      simp [coordIsEdge, vertexUpdate, wilsonRectangleBaseCell]
  rw [hv]
  simp

@[simp] theorem areaLawRectangleHorizontalLink_apply0 {B : Box 4}
    {L : ℕ} (hL : L ≤ B 0) (i : Fin L) (y : Fin (B 1 + 1)) :
    areaLawRectangleHorizontalLink (Fin.castLE hL i) y 0 =
      Sum.inr (Fin.castLE hL i) := by
  simp [areaLawRectangleHorizontalLink, edgeCell, vertexUpdate]

@[simp] theorem areaLawRectangleHorizontalLink_apply1 {B : Box 4}
    {L : ℕ}
    (hL : L ≤ B 0) (i : Fin L) (y : Fin (B 1 + 1)) :
    areaLawRectangleHorizontalLink (Fin.castLE hL i) y 1 =
      Sum.inl y := by
  simp [areaLawRectangleHorizontalLink, edgeCell, vertexUpdate]

@[simp] theorem areaLawRectangleVerticalLink_apply0 {B : Box 4}
    {T : ℕ}
    (x : Fin (B 0 + 1)) (hT : T ≤ B 1) (j : Fin T) :
    areaLawRectangleVerticalLink x (Fin.castLE hT j) 0 =
      Sum.inl x := by
  simp [areaLawRectangleVerticalLink, edgeCell, vertexUpdate]

@[simp] theorem areaLawRectangleVerticalLink_apply1 {B : Box 4}
    {T : ℕ}
    (x : Fin (B 0 + 1)) (hT : T ≤ B 1) (j : Fin T) :
    areaLawRectangleVerticalLink x (Fin.castLE hT j) 1 =
      Sum.inr (Fin.castLE hT j) := by
  simp [areaLawRectangleVerticalLink, edgeCell, vertexUpdate]


private theorem horizontalLink_injective {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (_hT : T ≤ B 1) :
    Function.Injective (fun x : Fin L × Fin (B 1 + 1) =>
      areaLawRectangleHorizontalLink (Fin.castLE hL x.1) x.2) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  change Sum.inr (Fin.castLE hL x.1) = Sum.inr (Fin.castLE hL y.1) at h0
  change Sum.inl x.2 = Sum.inl y.2 at h1
  have hix : Fin.castLE hL x.1 = Fin.castLE hL y.1 := Sum.inr.inj h0
  have hiy : x.2 = y.2 := Sum.inl.inj h1
  apply Prod.ext
  · apply Fin.ext
    have hv := congrArg Fin.val hix
    simpa using hv
  · exact hiy

private theorem verticalLink_injective {B : Box 4} {L T : ℕ}
    (_hL : L ≤ B 0) (hT : T ≤ B 1) :
    Function.Injective (fun x : Fin (B 0 + 1) × Fin T =>
      areaLawRectangleVerticalLink x.1 (Fin.castLE hT x.2)) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  change Sum.inl x.1 = Sum.inl y.1 at h0
  change Sum.inr (Fin.castLE hT x.2) = Sum.inr (Fin.castLE hT y.2) at h1
  have hix : x.1 = y.1 := Sum.inl.inj h0
  have hiy : Fin.castLE hT x.2 = Fin.castLE hT y.2 := Sum.inr.inj h1
  apply Prod.ext
  · exact hix
  · apply Fin.ext
    have hv := congrArg Fin.val hiy
    simpa using hv

private theorem horizontalLink_ne_verticalLink {B : Box 4}
    (x : Fin (B 0)) (y : Fin (B 1 + 1))
    (u : Fin (B 0 + 1)) (v : Fin (B 1)) :
    areaLawRectangleHorizontalLink x y ≠ areaLawRectangleVerticalLink u v := by
  intro h
  have h0 := congrFun h 0
  simp [areaLawRectangleHorizontalLink, areaLawRectangleVerticalLink,
    edgeCell, vertexUpdate] at h0

private theorem bottomLink_ne_topLink {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (hTpos : 0 < T)
    (i : Fin L) (j : Fin L) :
    areaLawRectangleBottomLink hL i ≠ areaLawRectangleTopLink hL hT j := by
  intro h
  have haxes := congrFun h 1
  simp only [areaLawRectangleBottomLink, areaLawRectangleTopLink,
    areaLawRectangleHorizontalLink_apply1] at haxes
  have hv : (0 : ℕ) = T := congrArg Fin.val (Sum.inl.inj haxes)
  omega

private theorem leftLink_ne_rightLink {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (hLpos : 0 < L)
    (i : Fin T) (j : Fin T) :
    areaLawRectangleLeftLink hT i ≠ areaLawRectangleRightLink hL hT j := by
  intro h
  have haxes := congrFun h 0
  simp only [areaLawRectangleLeftLink, areaLawRectangleRightLink,
    areaLawRectangleVerticalLink_apply0] at haxes
  have hv : (0 : ℕ) = L := congrArg Fin.val (Sum.inl.inj haxes)
  omega

theorem areaLawHorizontalPotentialBottom_onBottom {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (i : Fin L) :
    areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleBottomLink hL i) = if i = a then 1 else 0 := by
  simp [areaLawHorizontalPotentialBottom, areaLawRectangleBottomLink,
    cellDegree, areaLawRectangleHorizontalLink_axes, coordBase, Fin.ext_iff]

theorem areaLawHorizontalPotentialBottom_onTop {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (i : Fin L) :
    areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleTopLink hL hT i) = 0 := by
  simp [areaLawHorizontalPotentialBottom, areaLawRectangleTopLink,
    cellDegree, areaLawRectangleHorizontalLink_axes, coordBase]

theorem areaLawHorizontalPotentialBottom_onVertical {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (x : Fin (B 0 + 1)) (j : Fin T) :
    areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleVerticalLink x (Fin.castLE hT j)) = 0 := by
  simp [areaLawHorizontalPotentialBottom, cellDegree,
    areaLawRectangleVerticalLink_axes, coordBase]

theorem areaLawHorizontalPotentialTop_onTop {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (i : Fin L) :
    areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleTopLink hL hT i) = if i = a then -1 else 0 := by
  simp [areaLawHorizontalPotentialTop, areaLawRectangleTopLink,
    cellDegree, areaLawRectangleHorizontalLink_axes, coordBase, Fin.ext_iff]

theorem areaLawHorizontalPotentialTop_onBottom {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (i : Fin L) :
    areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleBottomLink hL i) = 0 := by
  simp [areaLawHorizontalPotentialTop, areaLawRectangleBottomLink,
    cellDegree, areaLawRectangleHorizontalLink_axes, coordBase]

theorem areaLawHorizontalPotentialTop_onVertical {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (x : Fin (B 0 + 1)) (j : Fin T) :
    areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleVerticalLink x (Fin.castLE hT j)) = 0 := by
  simp [areaLawHorizontalPotentialTop, cellDegree,
    areaLawRectangleVerticalLink_axes, coordBase]

theorem areaLawVerticalPotentialLeft_onLeft {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (j : Fin T) :
    areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleLeftLink hT j) = if j = b then -1 else 0 := by
  simp [areaLawVerticalPotentialLeft, areaLawRectangleLeftLink,
    cellDegree, areaLawRectangleVerticalLink_axes, coordBase, Fin.ext_iff]

theorem areaLawVerticalPotentialLeft_onRight {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (j : Fin T) :
    areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleRightLink hL hT j) = 0 := by
  simp [areaLawVerticalPotentialLeft, areaLawRectangleRightLink,
    cellDegree, areaLawRectangleVerticalLink_axes, coordBase]

theorem areaLawVerticalPotentialLeft_onHorizontal {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (i : Fin L) (y : Fin (B 1 + 1)) :
    areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleHorizontalLink (Fin.castLE hL i) y) = 0 := by
  simp [areaLawVerticalPotentialLeft, cellDegree,
    areaLawRectangleHorizontalLink_axes, coordBase]

theorem areaLocalPotential_onRight {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (j : Fin T) :
    areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleRightLink hL hT j) = if j = b then 1 else 0 := by
  simp [areaLocalPotential, areaLawRectangleRightLink,
    cellDegree, areaLawRectangleVerticalLink_axes, coordBase, Fin.ext_iff]

theorem areaLocalPotential_onLeft {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (j : Fin T) :
    areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleLeftLink hT j) = 0 := by
  simp [areaLocalPotential, areaLawRectangleLeftLink,
    cellDegree, areaLawRectangleVerticalLink_axes, coordBase]

theorem areaLocalPotential_onHorizontal {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (i : Fin L) (y : Fin (B 1 + 1)) :
    areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b)
      (areaLawRectangleHorizontalLink (Fin.castLE hL i) y) = 0 := by
  simp [areaLocalPotential, cellDegree,
    areaLawRectangleHorizontalLink_axes, coordBase]

theorem areaLawRectanglePerimeter_mem_cases {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (c : Cell 4 B)
    (hc : c ∈ areaLawRectanglePerimeterCells L T hL hT) :
    (∃ i : Fin L, c = areaLawRectangleBottomLink hL i) ∨
    (∃ i : Fin L, c = areaLawRectangleTopLink hL hT i) ∨
    (∃ j : Fin T, c = areaLawRectangleLeftLink hT j) ∨
    (∃ j : Fin T, c = areaLawRectangleRightLink hL hT j) := by
  classical
  rcases Finset.mem_union.mp hc with hb | hrest
  · obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp hb
    exact Or.inl ⟨i, hci.symm⟩
  · rcases Finset.mem_union.mp hrest with ht | hrest
    · obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp ht
      exact Or.inr (Or.inl ⟨i, hci.symm⟩)
    · rcases Finset.mem_union.mp hrest with hl | hr
      · obtain ⟨j, hj, hcj⟩ := Finset.mem_image.mp hl
        exact Or.inr (Or.inr (Or.inl ⟨j, hcj.symm⟩))
      · obtain ⟨j, hj, hcj⟩ := Finset.mem_image.mp hr
        exact Or.inr (Or.inr (Or.inr ⟨j, hcj.symm⟩))

private theorem integerCellPairing_eq_single_of_support_shape {B : Box 4}
    (f : Cell 4 B → ℤ) (q : Chain 4 B) (e : Cell 4 B) (v : ℤ)
    (hshape : ∀ c ∈ q.support,
      (c = e → f c = v) ∧ (c ≠ e → f c = 0)) :
    integerCellPairing f q = q e * v := by
  classical
  unfold integerCellPairing
  calc
    (∑ c : Cell 4 B, q c * f c) =
        ∑ c : Cell 4 B, if c = e then q c * v else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          by_cases hmem : c ∈ q.support
          · by_cases he : c = e
            · subst c
              simp [hshape e hmem]
            · simp [he, hshape c hmem]
          · have hzero : q c = 0 := Finsupp.notMem_support_iff.mp hmem
            simp [hzero]
    _ = q e * v := by simp

theorem areaLawHorizontalPotentialBottom_shape_onPerimeter
    {B : Box 4} {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (c : Cell 4 B)
    (hc : c ∈ areaLawRectanglePerimeterCells L T hL hT) :
    areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b) c =
      if c = areaLawRectangleBottomLink hL a then 1 else 0 := by
  obtain hbottom | hrest | hleft | hright :=
    areaLawRectanglePerimeter_mem_cases hL hT c hc
  · obtain ⟨i, rfl⟩ := hbottom
    by_cases hi : i = a
    · subst i
      rw [areaLawHorizontalPotentialBottom_onBottom hL hT a b a]
      simp
    · have hne : areaLawRectangleBottomLink hL i ≠
        areaLawRectangleBottomLink hL a := by
          intro heq
          let y0 : Fin (B 1 + 1) := ⟨0, Nat.zero_lt_succ (B 1)⟩
          have hlinkEq : areaLawRectangleHorizontalLink (Fin.castLE hL i) y0 =
              areaLawRectangleHorizontalLink (Fin.castLE hL a) y0 := by
            simpa [areaLawRectangleBottomLink, y0] using heq
          have hfunEq :
              (fun x : Fin L × Fin (B 1 + 1) =>
                areaLawRectangleHorizontalLink (Fin.castLE hL x.1) x.2) (i, y0) =
              (fun x : Fin L × Fin (B 1 + 1) =>
                areaLawRectangleHorizontalLink (Fin.castLE hL x.1) x.2) (a, y0) := by
            simpa using hlinkEq
          have heq' := horizontalLink_injective hL hT hfunEq
          exact hi (congrArg Prod.fst heq')
      rw [areaLawHorizontalPotentialBottom_onBottom hL hT a b i]
      simp [hi, hne]
  · obtain ⟨i, rfl⟩ := hrest
    have hb := b.isLt
    have hTpos : 0 < T := by omega
    have hne : areaLawRectangleTopLink hL hT i ≠
        areaLawRectangleBottomLink hL a :=
      (bottomLink_ne_topLink hL hT hTpos a i).symm
    rw [areaLawHorizontalPotentialBottom_onTop hL hT a b i]
    simp [hne]
  · obtain ⟨j, rfl⟩ := hleft
    have hne : areaLawRectangleLeftLink hT j ≠
        areaLawRectangleBottomLink hL a := by
      simpa [areaLawRectangleLeftLink, areaLawRectangleBottomLink] using
        (horizontalLink_ne_verticalLink _ _ _ _).symm
    have heval := areaLawHorizontalPotentialBottom_onVertical hL hT a b
      ⟨0, Nat.zero_lt_succ (B 0)⟩ j
    rw [show areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b)
        (areaLawRectangleLeftLink hT j) = 0 by
      simpa [areaLawRectangleLeftLink] using heval]
    simp [hne]
  · obtain ⟨j, rfl⟩ := hright
    have hne : areaLawRectangleRightLink hL hT j ≠
        areaLawRectangleBottomLink hL a := by
      simpa [areaLawRectangleRightLink, areaLawRectangleBottomLink] using
        (horizontalLink_ne_verticalLink _ _ _ _).symm
    have heval := areaLawHorizontalPotentialBottom_onVertical hL hT a b
      ⟨L, Nat.lt_succ_of_le hL⟩ j
    rw [show areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b)
        (areaLawRectangleRightLink hL hT j) = 0 by
      simpa [areaLawRectangleRightLink] using heval]
    simp [hne]

theorem areaLawHorizontalPotentialTop_shape_onPerimeter
    {B : Box 4} {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (c : Cell 4 B)
    (hc : c ∈ areaLawRectanglePerimeterCells L T hL hT) :
    areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b) c =
      if c = areaLawRectangleTopLink hL hT a then -1 else 0 := by
  obtain hbottom | hrest | hleft | hright :=
    areaLawRectanglePerimeter_mem_cases hL hT c hc
  · obtain ⟨i, rfl⟩ := hbottom
    have hb := b.isLt
    have hTpos : 0 < T := by omega
    have hne : areaLawRectangleBottomLink hL i ≠
        areaLawRectangleTopLink hL hT a :=
      bottomLink_ne_topLink hL hT hTpos i a
    rw [areaLawHorizontalPotentialTop_onBottom hL hT a b i]
    simp [hne]
  · obtain ⟨i, rfl⟩ := hrest
    by_cases hi : i = a
    · subst i
      rw [areaLawHorizontalPotentialTop_onTop hL hT a b a]
      simp
    · have hne : areaLawRectangleTopLink hL hT i ≠
        areaLawRectangleTopLink hL hT a := by
          intro heq
          let yT : Fin (B 1 + 1) := ⟨T, Nat.lt_succ_of_le hT⟩
          have hlinkEq : areaLawRectangleHorizontalLink (Fin.castLE hL i) yT =
              areaLawRectangleHorizontalLink (Fin.castLE hL a) yT := by
            simpa [areaLawRectangleTopLink, yT] using heq
          have hfunEq :
              (fun x : Fin L × Fin (B 1 + 1) =>
                areaLawRectangleHorizontalLink (Fin.castLE hL x.1) x.2) (i, yT) =
              (fun x : Fin L × Fin (B 1 + 1) =>
                areaLawRectangleHorizontalLink (Fin.castLE hL x.1) x.2) (a, yT) := by
            simpa using hlinkEq
          have heq' := horizontalLink_injective hL hT hfunEq
          exact hi (congrArg Prod.fst heq')
      rw [areaLawHorizontalPotentialTop_onTop hL hT a b i]
      simp [hi, hne]
  · obtain ⟨j, rfl⟩ := hleft
    have hne : areaLawRectangleLeftLink hT j ≠
        areaLawRectangleTopLink hL hT a := by
      simpa [areaLawRectangleLeftLink, areaLawRectangleTopLink] using
        (horizontalLink_ne_verticalLink _ _ _ _).symm
    have heval := areaLawHorizontalPotentialTop_onVertical hL hT a b
      ⟨0, Nat.zero_lt_succ (B 0)⟩ j
    rw [show areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b)
        (areaLawRectangleLeftLink hT j) = 0 by
      simpa [areaLawRectangleLeftLink] using heval]
    simp [hne]
  · obtain ⟨j, rfl⟩ := hright
    have hne : areaLawRectangleRightLink hL hT j ≠
        areaLawRectangleTopLink hL hT a := by
      simpa [areaLawRectangleRightLink, areaLawRectangleTopLink] using
        (horizontalLink_ne_verticalLink _ _ _ _).symm
    have heval := areaLawHorizontalPotentialTop_onVertical hL hT a b
      ⟨L, Nat.lt_succ_of_le hL⟩ j
    rw [show areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b)
        (areaLawRectangleRightLink hL hT j) = 0 by
      simpa [areaLawRectangleRightLink] using heval]
    simp [hne]

theorem areaLawVerticalPotentialLeft_shape_onPerimeter
    {B : Box 4} {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (c : Cell 4 B)
    (hc : c ∈ areaLawRectanglePerimeterCells L T hL hT) :
    areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b) c =
      if c = areaLawRectangleLeftLink hT b then -1 else 0 := by
  obtain hbottom | htop | hrest | hright :=
    areaLawRectanglePerimeter_mem_cases hL hT c hc
  · obtain ⟨i, rfl⟩ := hbottom
    have hne : areaLawRectangleBottomLink hL i ≠
        areaLawRectangleLeftLink hT b := by
      simpa [areaLawRectangleBottomLink, areaLawRectangleLeftLink] using
        horizontalLink_ne_verticalLink _ _ _ _
    have heval := areaLawVerticalPotentialLeft_onHorizontal hL hT a b i
      ⟨0, Nat.zero_lt_succ (B 1)⟩
    rw [show areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b)
        (areaLawRectangleBottomLink hL i) = 0 by
      simpa [areaLawRectangleBottomLink] using heval]
    simp [hne]
  · obtain ⟨i, rfl⟩ := htop
    have hne : areaLawRectangleTopLink hL hT i ≠
        areaLawRectangleLeftLink hT b := by
      simpa [areaLawRectangleTopLink, areaLawRectangleLeftLink] using
        horizontalLink_ne_verticalLink _ _ _ _
    have heval := areaLawVerticalPotentialLeft_onHorizontal hL hT a b i
      ⟨T, Nat.lt_succ_of_le hT⟩
    rw [show areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b)
        (areaLawRectangleTopLink hL hT i) = 0 by
      simpa [areaLawRectangleTopLink] using heval]
    simp [hne]
  · obtain ⟨j, rfl⟩ := hrest
    by_cases hj : j = b
    · subst j
      rw [areaLawVerticalPotentialLeft_onLeft hL hT a b b]
      simp
    · have hne : areaLawRectangleLeftLink hT j ≠
        areaLawRectangleLeftLink hT b := by
          intro heq
          let x0 : Fin (B 0 + 1) := ⟨0, Nat.zero_lt_succ (B 0)⟩
          have hlinkEq : areaLawRectangleVerticalLink x0 (Fin.castLE hT j) =
              areaLawRectangleVerticalLink x0 (Fin.castLE hT b) := by
            simpa [areaLawRectangleLeftLink, x0] using heq
          have hfunEq :
              (fun x : Fin (B 0 + 1) × Fin T =>
                areaLawRectangleVerticalLink x.1 (Fin.castLE hT x.2)) (x0, j) =
              (fun x : Fin (B 0 + 1) × Fin T =>
                areaLawRectangleVerticalLink x.1 (Fin.castLE hT x.2)) (x0, b) := by
            simpa using hlinkEq
          have heq' := verticalLink_injective hL hT hfunEq
          exact hj (congrArg Prod.snd heq')
      rw [areaLawVerticalPotentialLeft_onLeft hL hT a b j]
      simp [hj, hne]
  · obtain ⟨j, rfl⟩ := hright
    have ha := a.isLt
    have hLpos : 0 < L := by omega
    have hne : areaLawRectangleRightLink hL hT j ≠
        areaLawRectangleLeftLink hT b :=
      (leftLink_ne_rightLink hL hT hLpos b j).symm
    rw [areaLawVerticalPotentialLeft_onRight hL hT a b j]
    simp [hne]

theorem areaLocalPotential_shape_onPerimeter
    {B : Box 4} {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (c : Cell 4 B)
    (hc : c ∈ areaLawRectanglePerimeterCells L T hL hT) :
    areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b) c =
      if c = areaLawRectangleRightLink hL hT b then 1 else 0 := by
  obtain hbottom | htop | hleft | hrest :=
    areaLawRectanglePerimeter_mem_cases hL hT c hc
  · obtain ⟨i, rfl⟩ := hbottom
    have hne : areaLawRectangleBottomLink hL i ≠
        areaLawRectangleRightLink hL hT b := by
      simpa [areaLawRectangleBottomLink, areaLawRectangleRightLink] using
        horizontalLink_ne_verticalLink _ _ _ _
    have heval := areaLocalPotential_onHorizontal hL hT a b i
      ⟨0, Nat.zero_lt_succ (B 1)⟩
    rw [show areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b)
        (areaLawRectangleBottomLink hL i) = 0 by
      simpa [areaLawRectangleBottomLink] using heval]
    simp [hne]
  · obtain ⟨i, rfl⟩ := htop
    have hne : areaLawRectangleTopLink hL hT i ≠
        areaLawRectangleRightLink hL hT b := by
      simpa [areaLawRectangleTopLink, areaLawRectangleRightLink] using
        horizontalLink_ne_verticalLink _ _ _ _
    have heval := areaLocalPotential_onHorizontal hL hT a b i
      ⟨T, Nat.lt_succ_of_le hT⟩
    rw [show areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b)
        (areaLawRectangleTopLink hL hT i) = 0 by
      simpa [areaLawRectangleTopLink] using heval]
    simp [hne]
  · obtain ⟨j, rfl⟩ := hleft
    have ha := a.isLt
    have hLpos : 0 < L := by omega
    have hne : areaLawRectangleLeftLink hT j ≠
        areaLawRectangleRightLink hL hT b :=
      leftLink_ne_rightLink hL hT hLpos j b
    rw [areaLocalPotential_onLeft hL hT a b j]
    simp [hne]
  · obtain ⟨j, rfl⟩ := hrest
    by_cases hj : j = b
    · subst j
      rw [areaLocalPotential_onRight hL hT a b b]
      simp
    · have hne : areaLawRectangleRightLink hL hT j ≠
        areaLawRectangleRightLink hL hT b := by
          intro heq
          let xL : Fin (B 0 + 1) := ⟨L, Nat.lt_succ_of_le hL⟩
          have hlinkEq : areaLawRectangleVerticalLink xL (Fin.castLE hT j) =
              areaLawRectangleVerticalLink xL (Fin.castLE hT b) := by
            simpa [areaLawRectangleRightLink, xL] using heq
          have hfunEq :
              (fun x : Fin (B 0 + 1) × Fin T =>
                areaLawRectangleVerticalLink x.1 (Fin.castLE hT x.2)) (xL, j) =
              (fun x : Fin (B 0 + 1) × Fin T =>
                areaLawRectangleVerticalLink x.1 (Fin.castLE hT x.2)) (xL, b) := by
            simpa using hlinkEq
          have heq' := verticalLink_injective hL hT hfunEq
          exact hj (congrArg Prod.snd heq')
      rw [areaLocalPotential_onRight hL hT a b j]
      simp [hj, hne]

theorem integerCellPairing_horizontalBottom_eq_link {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (q : Chain 4 B)
    (hq : q.support ⊆ areaLawRectanglePerimeterCells L T hL hT) :
    integerCellPairing (areaLawHorizontalPotentialBottom
      (Fin.castLE hL a) (Fin.castLE hT b)) q =
      q (areaLawRectangleBottomLink hL a) := by
  have hshape : ∀ c ∈ q.support,
      (c = areaLawRectangleBottomLink hL a →
        areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b) c = 1) ∧
      (c ≠ areaLawRectangleBottomLink hL a →
        areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b) c = 0) := by
    intro c hc
    have hs := areaLawHorizontalPotentialBottom_shape_onPerimeter
      hL hT a b c (hq hc)
    constructor <;> intro he <;> rw [hs] <;> simp [he]
  simpa using integerCellPairing_eq_single_of_support_shape
    (areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b)) q
    (areaLawRectangleBottomLink hL a) 1 hshape

theorem integerCellPairing_horizontalTop_eq_link {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (q : Chain 4 B)
    (hq : q.support ⊆ areaLawRectanglePerimeterCells L T hL hT) :
    integerCellPairing (areaLawHorizontalPotentialTop
      (Fin.castLE hL a) (Fin.castLE hT b)) q =
      q (areaLawRectangleTopLink hL hT a) * (-1) := by
  have hshape : ∀ c ∈ q.support,
      (c = areaLawRectangleTopLink hL hT a →
        areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b) c = -1) ∧
      (c ≠ areaLawRectangleTopLink hL hT a →
        areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b) c = 0) := by
    intro c hc
    have hs := areaLawHorizontalPotentialTop_shape_onPerimeter
      hL hT a b c (hq hc)
    constructor <;> intro he <;> rw [hs] <;> simp [he]
  exact integerCellPairing_eq_single_of_support_shape
    (areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b)) q
    (areaLawRectangleTopLink hL hT a) (-1) hshape

theorem integerCellPairing_verticalLeft_eq_link {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (q : Chain 4 B)
    (hq : q.support ⊆ areaLawRectanglePerimeterCells L T hL hT) :
    integerCellPairing (areaLawVerticalPotentialLeft
      (Fin.castLE hL a) (Fin.castLE hT b)) q =
      q (areaLawRectangleLeftLink hT b) * (-1) := by
  have hshape : ∀ c ∈ q.support,
      (c = areaLawRectangleLeftLink hT b →
        areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b) c = -1) ∧
      (c ≠ areaLawRectangleLeftLink hT b →
        areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b) c = 0) := by
    intro c hc
    have hs := areaLawVerticalPotentialLeft_shape_onPerimeter
      hL hT a b c (hq hc)
    constructor <;> intro he <;> rw [hs] <;> simp [he]
  exact integerCellPairing_eq_single_of_support_shape
    (areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b)) q
    (areaLawRectangleLeftLink hT b) (-1) hshape

theorem integerCellPairing_verticalRight_eq_link {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (q : Chain 4 B)
    (hq : q.support ⊆ areaLawRectanglePerimeterCells L T hL hT) :
    integerCellPairing (areaLocalPotential
      (Fin.castLE hL a) (Fin.castLE hT b)) q =
      q (areaLawRectangleRightLink hL hT b) := by
  have hshape : ∀ c ∈ q.support,
      (c = areaLawRectangleRightLink hL hT b →
        areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b) c = 1) ∧
      (c ≠ areaLawRectangleRightLink hL hT b →
        areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b) c = 0) := by
    intro c hc
    have hs := areaLocalPotential_shape_onPerimeter hL hT a b c (hq hc)
    constructor <;> intro he <;> rw [hs] <;> simp [he]
  simpa using integerCellPairing_eq_single_of_support_shape
    (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b)) q
    (areaLawRectangleRightLink hL hT b) 1 hshape

theorem integerCellPairing_boundary_eq_of_same_plaquette_curl
    {B : Box 4} (f g : Cell 4 B → ℤ) (q : Chain 4 B)
    (hq : homogeneousSupport q 2)
    (hcurl : ∀ p : PrimalPlaquettes B,
      integerCellPairing f (boundary (basisChain p.1)) =
        integerCellPairing g (boundary (basisChain p.1))) :
    integerCellPairing f (boundary q) = integerCellPairing g (boundary q) := by
  rw [integerCellPairing_boundary_chain, integerCellPairing_boundary_chain]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hdeg : cellDegree c = 2
  · let p : PrimalPlaquettes B := ⟨c, hdeg⟩
    have hp := hcurl p
    simpa [p] using congrArg (fun z : ℤ => q c * z) hp
  · have hzero : q c = 0 := by
      by_contra hne
      exact hdeg (hq c (Finsupp.mem_support_iff.mpr hne))
    simp [hzero]

theorem areaLawBoundaryPotential_mode_pairings {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (m : PrimalPlaquettes B → ℤ) :
    integerCellPairing (areaLawHorizontalPotentialBottom
        (Fin.castLE hL a) (Fin.castLE hT b))
        (boundary (plaquetteModeChain m)) =
      integerCellPairing (areaLocalPotential
        (Fin.castLE hL a) (Fin.castLE hT b))
        (boundary (plaquetteModeChain m)) ∧
    integerCellPairing (areaLawHorizontalPotentialTop
        (Fin.castLE hL a) (Fin.castLE hT b))
        (boundary (plaquetteModeChain m)) =
      integerCellPairing (areaLocalPotential
        (Fin.castLE hL a) (Fin.castLE hT b))
        (boundary (plaquetteModeChain m)) ∧
    integerCellPairing (areaLawVerticalPotentialLeft
        (Fin.castLE hL a) (Fin.castLE hT b))
        (boundary (plaquetteModeChain m)) =
      integerCellPairing (areaLocalPotential
        (Fin.castLE hL a) (Fin.castLE hT b))
        (boundary (plaquetteModeChain m)) := by
  have hhom := plaquetteModeChain_homogeneousSupport m
  have hcurlBottom (p : PrimalPlaquettes B) :=
    areaLawHorizontalPotentialBottom_curl p
      (Fin.castLE hL a) (Fin.castLE hT b)
  have hcurlTop (p : PrimalPlaquettes B) :=
    areaLawHorizontalPotentialTop_curl p
      (Fin.castLE hL a) (Fin.castLE hT b)
  have hcurlLeft (p : PrimalPlaquettes B) :=
    areaLawVerticalPotentialLeft_curl p
      (Fin.castLE hL a) (Fin.castLE hT b)
  have hcurlRight (p : PrimalPlaquettes B) :=
    areaLocalPotential_curl p (Fin.castLE hL a) (Fin.castLE hT b)
  refine ⟨?_, ?_, ?_⟩
  · exact integerCellPairing_boundary_eq_of_same_plaquette_curl _ _ _ hhom
      (by intro p; rw [hcurlBottom p, hcurlRight p])
  · exact integerCellPairing_boundary_eq_of_same_plaquette_curl _ _ _ hhom
      (by intro p; rw [hcurlTop p, hcurlRight p])
  · exact integerCellPairing_boundary_eq_of_same_plaquette_curl _ _ _ hhom
      (by intro p; rw [hcurlLeft p, hcurlRight p])

end FroehlichSpencer.FS82.Wilson

end
