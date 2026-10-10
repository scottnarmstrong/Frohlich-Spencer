/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import FroehlichSpencer.FS82.Cubical.DualStencil

public import FroehlichSpencer.FS82.Poisson.SourceCarrier
public import FroehlichSpencer.FS82.Poisson.TreeGauge
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex

/-!
# The rooted source graph on the finite dual lattice
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

abbrev SourcePoissonVertex (B : Box 4) := Option (SourceDualZeroCells B)
abbrev SourcePoissonEdge (B : Box 4) := SourceDualOneCells B

def sourcePoissonAxis0 : Fin 4 := ⟨0, by decide⟩

theorem sourceDualZeroCell_axis_left {B : Box 4}
    (v : SourceDualZeroCells B) (i : Fin 4) :
    ∃ n : Fin (B i), v.1 i = Sum.inl n := by
  classical
  cases h : v.1 i with
  | inl n => exact ⟨n, rfl⟩
  | inr e =>
      have hi : i ∈ dualCellAxes v.1 := by simp [dualCellAxes, h]
      have hpos : 0 < (dualCellAxes v.1).card := Finset.card_pos.mpr ⟨i, hi⟩
      rw [show (dualCellAxes v.1).card = 0 from by
        simpa [dualCellDegree] using v.2] at hpos
      omega

noncomputable def sourcePoissonVertexCoord {B : Box 4}
    (v : SourceDualZeroCells B) (i : Fin 4) : Fin (B i) :=
  Classical.choose (sourceDualZeroCell_axis_left v i)

theorem sourcePoissonVertexCoord_spec {B : Box 4}
    (v : SourceDualZeroCells B) (i : Fin 4) :
    v.1 i = Sum.inl (sourcePoissonVertexCoord v i) :=
  Classical.choose_spec (sourceDualZeroCell_axis_left v i)


noncomputable def sourcePoissonEdgeAxis {B : Box 4}
    (e : SourceDualOneCells B) : Fin 4 := by
  classical
  exact if h : sourcePoissonAxis0 ∈ dualCellAxes e.1 then sourcePoissonAxis0 else
    (dualCellAxes e.1).min'
      (Finset.card_pos.mp (by
        have hpos : 0 < dualCellDegree e.1 := by rw [e.2]; norm_num
        exact hpos))

theorem sourcePoissonEdgeAxis_isRight {B : Box 4}
    (e : SourceDualOneCells B) : (e.1 (sourcePoissonEdgeAxis e)).isRight := by
  classical
  by_cases h : sourcePoissonAxis0 ∈ dualCellAxes e.1
  · have hm : sourcePoissonEdgeAxis e ∈ dualCellAxes e.1 := by
      simp [sourcePoissonEdgeAxis, h]
    exact (Finset.mem_filter.mp hm).2
  · have hm : sourcePoissonEdgeAxis e ∈ dualCellAxes e.1 := by
      simp [sourcePoissonEdgeAxis, h]
      exact Finset.min'_mem _ _
    exact (Finset.mem_filter.mp hm).2

theorem sourcePoissonEdgeAxis_mem {B : Box 4}
    (e : SourceDualOneCells B) : sourcePoissonEdgeAxis e ∈ dualCellAxes e.1 := by
  classical
  by_cases h : sourcePoissonAxis0 ∈ dualCellAxes e.1
  · simp [sourcePoissonEdgeAxis, h]
  · have hm : sourcePoissonEdgeAxis e ∈ dualCellAxes e.1 := by
      simp [sourcePoissonEdgeAxis, h]
      exact Finset.min'_mem _ _
    exact hm

theorem sourcePoissonEdgeAxis_unique {B : Box 4}
    (e : SourceDualOneCells B) {i j : Fin 4}
    (hi : (e.1 i).isRight) (hj : (e.1 j).isRight) : i = j := by
  by_contra hne
  have hcard : (dualCellAxes e.1).card = 1 := by
    simpa [dualCellDegree] using e.2
  have hpair : i ∈ dualCellAxes e.1 ∧ j ∈ dualCellAxes e.1 := by
    simp [dualCellAxes, hi, hj]
  have hsub : ({i, j} : Finset (Fin 4)) ⊆ dualCellAxes e.1 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hpair.1
    · exact hpair.2
  have htwo : ({i, j} : Finset (Fin 4)).card = 2 := by simp [hne]
  have := Finset.card_le_card hsub
  rw [htwo, hcard] at this
  omega

noncomputable def sourcePoissonEdgeAxisCoordAtZero {B : Box 4}
    (e : SourceDualOneCells B)
    (h : sourcePoissonAxis0 ∈ dualCellAxes e.1) : Fin (B sourcePoissonAxis0 + 1) :=
  Classical.choose (show ∃ n, e.1 sourcePoissonAxis0 = Sum.inr n from by
    cases hc : e.1 sourcePoissonAxis0 with
    | inl v =>
        have hright := (Finset.mem_filter.mp h).2
        rw [hc] at hright
        simp at hright
    | inr n => exact ⟨n, rfl⟩)

noncomputable def sourcePoissonEdgeAxisCoordElse {B : Box 4}
    (e : SourceDualOneCells B) : Fin (B (sourcePoissonEdgeAxis e) + 1) :=
  Classical.choose (show ∃ n, e.1 (sourcePoissonEdgeAxis e) = Sum.inr n from by
    cases hc : e.1 (sourcePoissonEdgeAxis e) with
    | inl v =>
        have hright := sourcePoissonEdgeAxis_isRight e
        rw [hc] at hright
        simp at hright
    | inr n => exact ⟨n, rfl⟩)

theorem sourcePoissonEdgeAxisCoordAtZero_spec {B : Box 4}
    (e : SourceDualOneCells B) (h : sourcePoissonAxis0 ∈ dualCellAxes e.1) :
    e.1 sourcePoissonAxis0 = Sum.inr (sourcePoissonEdgeAxisCoordAtZero e h) := by
  exact Classical.choose_spec (show ∃ n, e.1 sourcePoissonAxis0 = Sum.inr n from by
    cases hc : e.1 sourcePoissonAxis0 with
    | inl v =>
        have hright := (Finset.mem_filter.mp h).2
        rw [hc] at hright
        simp at hright
    | inr n => exact ⟨n, rfl⟩)

theorem sourcePoissonEdgeAxisCoordElse_spec {B : Box 4}
    (e : SourceDualOneCells B) :
    e.1 (sourcePoissonEdgeAxis e) = Sum.inr (sourcePoissonEdgeAxisCoordElse e) := by
  exact Classical.choose_spec (show ∃ n, e.1 (sourcePoissonEdgeAxis e) = Sum.inr n from by
    cases hc : e.1 (sourcePoissonEdgeAxis e) with
    | inl v =>
        have hright := sourcePoissonEdgeAxis_isRight e
        rw [hc] at hright
        simp at hright
    | inr n => exact ⟨n, rfl⟩)

noncomputable def sourcePoissonEdgeAxisIndex {B : Box 4}
    (e : SourceDualOneCells B) : ℕ :=
  (sourcePoissonEdgeAxisCoordElse e).val

theorem sourcePoissonEdgeAxisIndex_lt {B : Box 4}
    (e : SourceDualOneCells B) :
    sourcePoissonEdgeAxisIndex e < B (sourcePoissonEdgeAxis e) + 1 := by
  exact (sourcePoissonEdgeAxisCoordElse e).isLt

theorem sourcePoissonEdge_otherCoord_left {B : Box 4}
    (e : SourceDualOneCells B) {j : Fin 4}
    (hji : j ≠ sourcePoissonEdgeAxis e) :
    ∃ n : Fin (B j), e.1 j = Sum.inl n := by
  classical
  cases hj : e.1 j with
  | inl n => exact ⟨n, rfl⟩
  | inr n =>
      have hrightj : (e.1 j).isRight := by simp [hj]
      have hrighti := sourcePoissonEdgeAxis_isRight e
      have huniq := sourcePoissonEdgeAxis_unique e hrighti hrightj
      exact (hji huniq.symm).elim

theorem sourcePoissonEdge_otherCoord_left_of_mem {B : Box 4}
    (e : SourceDualOneCells B) {i j : Fin 4}
    (hi : i ∈ dualCellAxes e.1) (hji : j ≠ i) :
    ∃ n : Fin (B j), e.1 j = Sum.inl n := by
  classical
  cases hj : e.1 j with
  | inl n => exact ⟨n, rfl⟩
  | inr n =>
      have hrighti := (Finset.mem_filter.mp hi).2
      have hrightj : (e.1 j).isRight := by simp [hj]
      exact (hji (sourcePoissonEdgeAxis_unique e
        (i := i) (j := j) hrighti hrightj).symm).elim

noncomputable def sourcePoissonVertexOfEdgeCoordAtAxis {B : Box 4}
    (e : SourceDualOneCells B) (i : Fin 4)
    (hi : i ∈ dualCellAxes e.1) (n : Fin (B i)) :
    SourceDualZeroCells B :=
  ⟨Function.update e.1 i (Sum.inl n), by
    have haxes :
        dualCellAxes (Function.update e.1 i (Sum.inl n)) = ∅ := by
      ext j
      simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty]
      by_cases hji : j = i
      · subst j
        simp [Function.update]
      · obtain ⟨m, hm⟩ := sourcePoissonEdge_otherCoord_left_of_mem e hi hji
        rw [Function.update_of_ne hji]
        rw [hm]
        simp
    simp [dualCellDegree, haxes]⟩

@[simp] theorem sourcePoissonVertexOfEdgeCoordAtAxis_apply_axis {B : Box 4}
    (e : SourceDualOneCells B) (i : Fin 4) (hi : i ∈ dualCellAxes e.1)
    (n : Fin (B i)) :
    (sourcePoissonVertexOfEdgeCoordAtAxis e i hi n).1 i = Sum.inl n := by
  simp [sourcePoissonVertexOfEdgeCoordAtAxis]

@[simp] theorem sourcePoissonVertexOfEdgeCoordAtAxis_apply_ne {B : Box 4}
    (e : SourceDualOneCells B) (i j : Fin 4) (hi : i ∈ dualCellAxes e.1)
    (n : Fin (B i)) (hji : j ≠ i) :
    (sourcePoissonVertexOfEdgeCoordAtAxis e i hi n).1 j = e.1 j := by
  simp [sourcePoissonVertexOfEdgeCoordAtAxis, Function.update_of_ne hji]

noncomputable def sourcePoissonEdgeLowerVertex {B : Box 4}
    (e : SourceDualOneCells B) : SourcePoissonVertex B := by
  classical
  let k := sourcePoissonEdgeAxisIndex e
  exact if hk : k = 0 then none else
    some (sourcePoissonVertexOfEdgeCoordAtAxis e (sourcePoissonEdgeAxis e)
      (sourcePoissonEdgeAxis_mem e) ⟨k - 1, by
      have hklt := sourcePoissonEdgeAxisIndex_lt e
      omega⟩)

theorem sourcePoissonEdgeLowerVertex_of_index_ne_zero {B : Box 4}
    (e : SourceDualOneCells B) (hk : sourcePoissonEdgeAxisIndex e ≠ 0) :
    sourcePoissonEdgeLowerVertex e =
      some (sourcePoissonVertexOfEdgeCoordAtAxis e (sourcePoissonEdgeAxis e)
        (sourcePoissonEdgeAxis_mem e)
        ⟨sourcePoissonEdgeAxisIndex e - 1, by
          have hklt := sourcePoissonEdgeAxisIndex_lt e
          omega⟩) := by
  simp [sourcePoissonEdgeLowerVertex, hk]

noncomputable def sourcePoissonEdgeUpperVertex {B : Box 4}
    (e : SourceDualOneCells B) : SourcePoissonVertex B := by
  classical
  let k := sourcePoissonEdgeAxisIndex e
  exact if hk : k = B (sourcePoissonEdgeAxis e) then none else
    some (sourcePoissonVertexOfEdgeCoordAtAxis e (sourcePoissonEdgeAxis e)
      (sourcePoissonEdgeAxis_mem e) ⟨k, by
      have hklt := sourcePoissonEdgeAxisIndex_lt e
      omega⟩)

theorem sourcePoissonEdgeAxisCoord_spec {B : Box 4}
    (e : SourceDualOneCells B) :
    e.1 (sourcePoissonEdgeAxis e) =
      Sum.inr ⟨sourcePoissonEdgeAxisIndex e, sourcePoissonEdgeAxisIndex_lt e⟩ := by
  calc
    e.1 (sourcePoissonEdgeAxis e) =
        Sum.inr (sourcePoissonEdgeAxisCoordElse e) :=
          sourcePoissonEdgeAxisCoordElse_spec e
    _ = Sum.inr ⟨sourcePoissonEdgeAxisIndex e,
        sourcePoissonEdgeAxisIndex_lt e⟩ := by
      rfl

noncomputable def sourcePoissonTreeLinkCell {B : Box 4}
    (v : SourceDualZeroCells B) : DualCell 4 B :=
  Function.update v.1 sourcePoissonAxis0
    (Sum.inr ⟨(sourcePoissonVertexCoord v sourcePoissonAxis0).val,
      Nat.lt_succ_of_lt (sourcePoissonVertexCoord v sourcePoissonAxis0).isLt⟩)

theorem sourcePoissonTreeLinkCell_axes {B : Box 4}
    (v : SourceDualZeroCells B) :
    dualCellAxes (sourcePoissonTreeLinkCell v) = {sourcePoissonAxis0} := by
  ext j
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  by_cases hji : j = sourcePoissonAxis0
  · subst j
    simp [sourcePoissonTreeLinkCell, Function.update]
  · obtain ⟨m, hm⟩ := sourceDualZeroCell_axis_left v j
    constructor
    · intro hj
      rw [show sourcePoissonTreeLinkCell v j = v.1 j by
        simp [sourcePoissonTreeLinkCell, Function.update_of_ne hji], hm] at hj
      simp at hj
    · intro hj
      exact (hji hj).elim

noncomputable def sourcePoissonTreeLink {B : Box 4}
    (v : SourceDualZeroCells B) : SourceDualOneCells B :=
  ⟨sourcePoissonTreeLinkCell v, by
    change (dualCellAxes (sourcePoissonTreeLinkCell v)).card = 1
    rw [sourcePoissonTreeLinkCell_axes]
    simp⟩


@[simp] theorem sourcePoissonTreeLink_axis {B : Box 4}
    (v : SourceDualZeroCells B) :
    (sourcePoissonTreeLink v).1 sourcePoissonAxis0 =
      Sum.inr ⟨(sourcePoissonVertexCoord v sourcePoissonAxis0).val,
        Nat.lt_succ_of_lt (sourcePoissonVertexCoord v sourcePoissonAxis0).isLt⟩ := by
  simp [sourcePoissonTreeLink, sourcePoissonTreeLinkCell]


theorem sourcePoissonTreeLink_axis_selected {B : Box 4}
    (v : SourceDualZeroCells B) :
    sourcePoissonEdgeAxis (sourcePoissonTreeLink v) = sourcePoissonAxis0 := by
  classical
  unfold sourcePoissonEdgeAxis
  simp [sourcePoissonTreeLink, sourcePoissonTreeLinkCell_axes]

@[simp] theorem sourcePoissonEdgeAxis_treeLink {B : Box 4}
    (v : SourceDualZeroCells B) :
    sourcePoissonEdgeAxis (sourcePoissonTreeLink v) = sourcePoissonAxis0 :=
  sourcePoissonTreeLink_axis_selected v

theorem sourcePoissonTreeLink_axisCoord {B : Box 4}
    (v : SourceDualZeroCells B) :
    sourcePoissonEdgeAxisIndex (sourcePoissonTreeLink v) =
      (sourcePoissonVertexCoord v sourcePoissonAxis0).val := by
  have hmemCell : sourcePoissonAxis0 ∈ dualCellAxes (sourcePoissonTreeLinkCell v) := by
    rw [sourcePoissonTreeLinkCell_axes]
    simp
  have hmem : sourcePoissonAxis0 ∈ dualCellAxes (sourcePoissonTreeLink v).1 := by
    simpa [sourcePoissonTreeLink] using hmemCell
  have hSpec := sourcePoissonEdgeAxisCoordAtZero_spec (sourcePoissonTreeLink v) hmem
  rw [sourcePoissonTreeLink_axis] at hSpec
  have hCoord :
      sourcePoissonEdgeAxisCoordAtZero (sourcePoissonTreeLink v) hmem =
        ⟨(sourcePoissonVertexCoord v sourcePoissonAxis0).val,
          Nat.lt_succ_of_lt (sourcePoissonVertexCoord v sourcePoissonAxis0).isLt⟩ :=
    (Sum.inr.inj hSpec).symm
  change (if h : sourcePoissonAxis0 ∈
      dualCellAxes (sourcePoissonTreeLink v).1 then
    (sourcePoissonEdgeAxisCoordAtZero (sourcePoissonTreeLink v) h).val
    else (sourcePoissonEdgeAxisCoordElse (sourcePoissonTreeLink v)).val) = _
  rw [dite_eq_left hmem]
  exact congrArg Fin.val hCoord

theorem sourcePoissonTreeLink_upperVertex {B : Box 4}
    (v : SourceDualZeroCells B) :
    sourcePoissonEdgeUpperVertex (sourcePoissonTreeLink v) = some v := by
  classical
  have hindexLt : sourcePoissonEdgeAxisIndex (sourcePoissonTreeLink v) <
      B (sourcePoissonAxis0) := by
    rw [sourcePoissonTreeLink_axisCoord]
    exact (sourcePoissonVertexCoord v sourcePoissonAxis0).isLt
  have hindexNe : sourcePoissonEdgeAxisIndex (sourcePoissonTreeLink v) ≠
      B (sourcePoissonEdgeAxis (sourcePoissonTreeLink v)) := by
    rw [sourcePoissonEdgeAxis_treeLink, sourcePoissonTreeLink_axisCoord]
    exact ne_of_lt (sourcePoissonVertexCoord v sourcePoissonAxis0).isLt
  unfold sourcePoissonEdgeUpperVertex
  rw [dite_eq_right hindexNe]
  apply congrArg some
  apply Subtype.ext
  funext j
  by_cases hji : j = sourcePoissonAxis0
  · subst j
    change Function.update (sourcePoissonTreeLink v).1 sourcePoissonAxis0
      (Sum.inl ⟨sourcePoissonEdgeAxisIndex (sourcePoissonTreeLink v), hindexLt⟩)
      sourcePoissonAxis0 = v.1 sourcePoissonAxis0
    rw [sourcePoissonVertexCoord_spec]
    exact congrArg Sum.inl (Fin.ext (sourcePoissonTreeLink_axisCoord v))
  · change Function.update (sourcePoissonTreeLink v).1 sourcePoissonAxis0
      (Sum.inl ⟨sourcePoissonEdgeAxisIndex (sourcePoissonTreeLink v), hindexLt⟩)
      j = v.1 j
    simp [sourcePoissonTreeLink, sourcePoissonTreeLinkCell, hji]

theorem sourcePoissonTreeLink_lowerVertex {B : Box 4}
    (v : SourceDualZeroCells B) :
    sourcePoissonEdgeLowerVertex (sourcePoissonTreeLink v) =
      if (sourcePoissonVertexCoord v sourcePoissonAxis0).val = 0 then none
      else some (sourcePoissonVertexOfEdgeCoordAtAxis
        (sourcePoissonTreeLink v) sourcePoissonAxis0 (by
          change sourcePoissonAxis0 ∈ dualCellAxes (sourcePoissonTreeLinkCell v)
          rw [sourcePoissonTreeLinkCell_axes]
          simp)
        ⟨(sourcePoissonVertexCoord v sourcePoissonAxis0).val - 1, by
          have h := (sourcePoissonVertexCoord v sourcePoissonAxis0).isLt
          omega⟩) := by
  classical
  by_cases hzero : (sourcePoissonVertexCoord v sourcePoissonAxis0).val = 0
  · simp [sourcePoissonEdgeLowerVertex, sourcePoissonTreeLink_axisCoord,
      hzero]
  · rw [sourcePoissonEdgeLowerVertex_of_index_ne_zero _ (by
      rw [sourcePoissonTreeLink_axisCoord]
      exact hzero)]
    simp only [sourcePoissonTreeLink_axisCoord, ite_eq_right hzero]
    rfl

noncomputable def sourcePoissonTreeParent {B : Box 4}
    (x : SourcePoissonVertex B) : SourcePoissonVertex B :=
  match x with
  | none => none
  | some v => sourcePoissonEdgeLowerVertex (sourcePoissonTreeLink v)

noncomputable def sourcePoissonTreeDepth {B : Box 4}
    (x : SourcePoissonVertex B) : ℕ :=
  match x with
  | none => 0
  | some v => (sourcePoissonVertexCoord v sourcePoissonAxis0).val + 1

theorem sourcePoissonTreeDepth_le {B : Box 4} (x : SourcePoissonVertex B) :
    sourcePoissonTreeDepth x ≤ B sourcePoissonAxis0 := by
  cases x with
  | none => simp [sourcePoissonTreeDepth]
  | some v =>
    simp only [sourcePoissonTreeDepth]
    have h := (sourcePoissonVertexCoord v sourcePoissonAxis0).isLt
    omega

theorem sourcePoissonVertexCoord_ofEdgeCoordAtAxis {B : Box 4}
    (e : SourceDualOneCells B) (i : Fin 4)
    (hi : i ∈ dualCellAxes e.1) (n : Fin (B i)) :
    sourcePoissonVertexCoord (sourcePoissonVertexOfEdgeCoordAtAxis e i hi n) i = n := by
  have hspec := sourcePoissonVertexCoord_spec
    (sourcePoissonVertexOfEdgeCoordAtAxis e i hi n) i
  have haxis := sourcePoissonVertexOfEdgeCoordAtAxis_apply_axis e i hi n
  rw [haxis] at hspec
  exact (Sum.inl.inj hspec).symm

theorem sourcePoissonTree_depth_parent {B : Box 4}
    {x : SourcePoissonVertex B} (hx : x ≠ none) :
    sourcePoissonTreeDepth (sourcePoissonTreeParent x) + 1 =
      sourcePoissonTreeDepth x := by
  cases x with
  | none => exact (hx rfl).elim
  | some v =>
    simp only [sourcePoissonTreeParent, sourcePoissonTreeDepth]
    by_cases hzero : (sourcePoissonVertexCoord v sourcePoissonAxis0).val = 0
    · simp [sourcePoissonTreeLink_lowerVertex, hzero]
    · rw [sourcePoissonTreeLink_lowerVertex]
      simp only [hzero, ↓reduceIte]
      rw [sourcePoissonVertexCoord_ofEdgeCoordAtAxis]
      simp only
      omega

noncomputable def sourcePoissonTreeEdge {B : Box 4}
    (x : {x : SourcePoissonVertex B // x ≠ none}) : SourcePoissonEdge B := by
  rcases x with ⟨x, hx⟩
  cases x with
  | none => exact (hx rfl).elim
  | some v => exact sourcePoissonTreeLink v

theorem sourcePoissonTreeEdge_target {B : Box 4}
    (x : {x : SourcePoissonVertex B // x ≠ none}) :
    sourcePoissonEdgeUpperVertex (sourcePoissonTreeEdge x) = x.1 := by
  rcases x with ⟨x, hx⟩
  cases x with
  | none => exact (hx rfl).elim
  | some v => simpa [sourcePoissonTreeEdge] using sourcePoissonTreeLink_upperVertex v

theorem sourcePoissonTreeEdge_source {B : Box 4}
    (x : {x : SourcePoissonVertex B // x ≠ none}) :
    sourcePoissonEdgeLowerVertex (sourcePoissonTreeEdge x) = sourcePoissonTreeParent x.1 := by
  rcases x with ⟨x, hx⟩
  cases x with
  | none => exact (hx rfl).elim
  | some v => rfl

noncomputable def sourceRootedTree (B : Box 4) :
    RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B) where
  root := none
  parent := sourcePoissonTreeParent
  depth := sourcePoissonTreeDepth
  height := B sourcePoissonAxis0
  depth_le_height := sourcePoissonTreeDepth_le
  edgeSource := sourcePoissonEdgeLowerVertex
  edgeTarget := sourcePoissonEdgeUpperVertex
  treeEdge := sourcePoissonTreeEdge
  treeEdge_injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    apply Subtype.ext
    have hxy := congrArg sourcePoissonEdgeUpperVertex h
    have hleft := sourcePoissonTreeEdge_target ⟨x, hx⟩
    have hright := sourcePoissonTreeEdge_target ⟨y, hy⟩
    rw [hleft, hright] at hxy
    exact hxy
  treeEdge_source := sourcePoissonTreeEdge_source
  treeEdge_target := sourcePoissonTreeEdge_target
  depth_root := rfl
  depth_pos := by
    intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some v => simp [sourcePoissonTreeDepth]
  depth_parent := sourcePoissonTree_depth_parent

end FroehlichSpencer.FS82.Poisson
