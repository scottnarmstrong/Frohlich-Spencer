/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.SourceTree
public import FroehlichSpencer.FS82.Currents.SourceLinkColoring
public import FroehlichSpencer.FS82.Currents.SelectedLinkSelection

/-!
# Adaptive positive-orientation tree avoiding plaquette-separated links
-/

public section

namespace FroehlichSpencer.FS82.Currents.AdaptiveTree

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Currents.SelectedLinkSelection

variable {B : SourceBox}

/-- The natural coordinate value of a vertex or interval coordinate. -/
def dualCoordIndex {i : Fin 4} (c : DualCoord B i) : ℕ :=
  match c with
  | Sum.inl x => x.val
  | Sum.inr x => x.val

/-- The source-cell encoding of a positive link entering a source vertex. -/
noncomputable def incomingCell (v : SourceDualZeroCells B) (i : Fin 4) : DualCell 4 B :=
  Function.update v.1 i
    (Sum.inr ⟨(sourcePoissonVertexCoord v i).val,
      Nat.lt_succ_of_lt (sourcePoissonVertexCoord v i).isLt⟩)

theorem incomingCell_axes (v : SourceDualZeroCells B) (i : Fin 4) :
    dualCellAxes (incomingCell v i) = {i} := by
  ext j
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  by_cases hji : j = i
  · subst j
    simp [incomingCell]
  · obtain ⟨n, hn⟩ := sourceDualZeroCell_axis_left v j
    simp [incomingCell, hji, hn]

theorem incomingCell_apply_axis (v : SourceDualZeroCells B) (i : Fin 4) :
    incomingCell v i i = Sum.inr ⟨(sourcePoissonVertexCoord v i).val,
      Nat.lt_succ_of_lt (sourcePoissonVertexCoord v i).isLt⟩ := by
  simp [incomingCell]

theorem incomingCell_apply_ne (v : SourceDualZeroCells B) (i j : Fin 4)
    (hji : j ≠ i) : incomingCell v i j = Sum.inl (sourcePoissonVertexCoord v j) := by
  simp [incomingCell, Function.update_of_ne hji,
    sourcePoissonVertexCoord_spec]

/-- A link directed from the lower neighbor of a source vertex toward that
vertex, in any coordinate direction. -/
noncomputable def incomingLink (v : SourceDualZeroCells B) (i : Fin 4) :
    SourceDualOneCells B :=
  ⟨incomingCell v i, by
    change (dualCellAxes (incomingCell v i)).card = 1
    rw [incomingCell_axes]
    simp⟩

theorem incomingLink_axes (v : SourceDualZeroCells B) (i : Fin 4) :
    dualCellAxes (incomingLink v i).1 = {i} :=
  incomingCell_axes v i

theorem incomingLink_direction (v : SourceDualZeroCells B) (i : Fin 4) :
    sourcePoissonEdgeAxis (incomingLink v i) = i := by
  have hi : ((incomingLink v i).1 i).isRight := by
    simp [incomingLink, incomingCell]
  exact sourcePoissonEdgeAxis_unique (incomingLink v i)
    (sourcePoissonEdgeAxis_isRight _) hi

theorem incomingLink_baseDirection (v : SourceDualZeroCells B) (i : Fin 4) :
    linkDirection (incomingLink v i) = i := by
  have hi : linkDirection (incomingLink v i) ∈
      dualCellAxes (incomingLink v i).1 := by
    rw [linkAxes_eq_singleton]
    simp
  rw [incomingLink_axes] at hi
  exact Finset.mem_singleton.mp hi

theorem incomingLink_index (v : SourceDualZeroCells B) (i : Fin 4) :
    sourcePoissonEdgeAxisIndex (incomingLink v i) =
      (sourcePoissonVertexCoord v i).val := by
  let e : SourceDualOneCells B := incomingLink v i
  have hdir : sourcePoissonEdgeAxis e = i := by
    simpa [e] using incomingLink_direction v i
  have hspec := congrArg dualCoordIndex (sourcePoissonEdgeAxisCoord_spec e)
  have htransport : dualCoordIndex (e.1 (sourcePoissonEdgeAxis e)) =
      dualCoordIndex (e.1 i) :=
    congrArg (fun k : Fin 4 => dualCoordIndex (e.1 k)) hdir
  have hcell : dualCoordIndex (e.1 i) =
      (sourcePoissonVertexCoord v i).val := by
    rw [show e.1 i = incomingCell v i i by rfl, incomingCell_apply_axis]
    rfl
  calc
    sourcePoissonEdgeAxisIndex e = dualCoordIndex (e.1 (sourcePoissonEdgeAxis e)) :=
      hspec.symm
    _ = dualCoordIndex (e.1 i) := htransport
    _ = (sourcePoissonVertexCoord v i).val := hcell

theorem incomingLink_upperVertex (v : SourceDualZeroCells B) (i : Fin 4) :
    sourcePoissonEdgeUpperVertex (incomingLink v i) = some v := by
  classical
  let e : SourceDualOneCells B := incomingLink v i
  let a := sourcePoissonEdgeAxis e
  have hdir : a = i := by simpa [a, e] using incomingLink_direction v i
  have hidx : sourcePoissonEdgeAxisIndex e =
      (sourcePoissonVertexCoord v i).val := by
    simpa [e] using incomingLink_index v i
  have hlt : sourcePoissonEdgeAxisIndex e < B a := by
    rw [hdir, hidx]
    exact (sourcePoissonVertexCoord v i).isLt
  have hvertex : sourcePoissonVertexOfEdgeCoordAtAxis e a
      (sourcePoissonEdgeAxis_mem e)
      ⟨sourcePoissonEdgeAxisIndex e, hlt⟩ = v := by
    apply Subtype.ext
    change Function.update e.1 a
      (Sum.inl ⟨sourcePoissonEdgeAxisIndex e, hlt⟩) = v.1
    apply Function.update_eq_iff.mpr
    constructor
    · have hval : (sourcePoissonVertexCoord v a).val =
          sourcePoissonEdgeAxisIndex e := by
        rw [hdir, hidx]
      rw [sourcePoissonVertexCoord_spec v a]
      exact congrArg Sum.inl (Fin.ext hval.symm)
    · intro j hja
      have hji : j ≠ i := by
        simpa [hdir] using hja
      have heval : e.1 j = Sum.inl (sourcePoissonVertexCoord v j) := by
        simpa [e, incomingLink] using incomingCell_apply_ne v i j hji
      rw [heval, sourcePoissonVertexCoord_spec]
  unfold sourcePoissonEdgeUpperVertex
  rw [dite_eq_right (ne_of_lt hlt)]
  exact congrArg some hvertex

/-- The lower endpoint of an incoming link, written in its selected positive
coordinate. -/
theorem incomingLink_lowerVertex (v : SourceDualZeroCells B) (i : Fin 4) :
    sourcePoissonEdgeLowerVertex (incomingLink v i) =
      if h : sourcePoissonEdgeAxisIndex (incomingLink v i) = 0 then none else
        some (sourcePoissonVertexOfEdgeCoordAtAxis (incomingLink v i)
          (sourcePoissonEdgeAxis (incomingLink v i))
          (sourcePoissonEdgeAxis_mem (incomingLink v i))
          ⟨sourcePoissonEdgeAxisIndex (incomingLink v i) - 1, by
            have hi := sourcePoissonEdgeAxisIndex_lt (incomingLink v i)
            omega⟩) := by
  classical
  unfold sourcePoissonEdgeLowerVertex
  rfl

noncomputable def incomingParent (v : SourceDualZeroCells B) (i : Fin 4) :
    SourcePoissonVertex B :=
  sourcePoissonEdgeLowerVertex (incomingLink v i)

noncomputable def vertexRank (v : SourceDualZeroCells B) : ℕ :=
  ∑ i : Fin 4, (sourcePoissonVertexCoord v i).val

theorem incomingPredecessor_rank (v : SourceDualZeroCells B) (i : Fin 4)
    (hpos : sourcePoissonEdgeAxisIndex (incomingLink v i) ≠ 0) :
    vertexRank (sourcePoissonVertexOfEdgeCoordAtAxis (incomingLink v i)
      (sourcePoissonEdgeAxis (incomingLink v i))
      (sourcePoissonEdgeAxis_mem (incomingLink v i))
      ⟨sourcePoissonEdgeAxisIndex (incomingLink v i) - 1, by
        have hi := sourcePoissonEdgeAxisIndex_lt (incomingLink v i)
        omega⟩) + 1 = vertexRank v := by
  let e : SourceDualOneCells B := incomingLink v i
  let a := sourcePoissonEdgeAxis e
  let pred := sourcePoissonVertexOfEdgeCoordAtAxis e a
    (sourcePoissonEdgeAxis_mem e)
    ⟨sourcePoissonEdgeAxisIndex e - 1, by
      have hi := sourcePoissonEdgeAxisIndex_lt e
      have hp : sourcePoissonEdgeAxisIndex e ≠ 0 := by simpa [e] using hpos
      change sourcePoissonEdgeAxisIndex e - 1 < B (sourcePoissonEdgeAxis e)
      omega⟩
  have hdir : a = i := by simpa [a, e] using incomingLink_direction v i
  have hidx : sourcePoissonEdgeAxisIndex e =
      (sourcePoissonVertexCoord v i).val := by
    simpa [e] using incomingLink_index v i
  have hidxpos : sourcePoissonEdgeAxisIndex e ≠ 0 := by
    simpa [e] using hpos
  have hpredA : (sourcePoissonVertexCoord pred a).val + 1 =
      (sourcePoissonVertexCoord v a).val := by
    have hpred := sourcePoissonVertexCoord_ofEdgeCoordAtAxis e a
      (sourcePoissonEdgeAxis_mem e)
      ⟨sourcePoissonEdgeAxisIndex e - 1, by
        have hi := sourcePoissonEdgeAxisIndex_lt e
        have hp : sourcePoissonEdgeAxisIndex e ≠ 0 := by simpa [e] using hpos
        change sourcePoissonEdgeAxisIndex e - 1 < B (sourcePoissonEdgeAxis e)
        omega⟩
    have hcoord : (sourcePoissonVertexCoord v a).val =
        (sourcePoissonVertexCoord v i).val :=
      congrArg (fun k : Fin 4 => (sourcePoissonVertexCoord v k).val) hdir
    calc
      (sourcePoissonVertexCoord pred a).val + 1 =
          (sourcePoissonEdgeAxisIndex e - 1) + 1 := by
        exact congrArg Fin.val hpred ▸ rfl
      _ = (sourcePoissonVertexCoord v i).val := by
        rw [hidx]
        have hcoordpos : (sourcePoissonVertexCoord v i).val ≠ 0 := by
          simpa [hidx] using hidxpos
        omega
      _ = (sourcePoissonVertexCoord v a).val := hcoord.symm
  have hpredOther : ∀ j, j ≠ a →
      sourcePoissonVertexCoord pred j = sourcePoissonVertexCoord v j := by
    intro j hja
    have hji : j ≠ i := by simpa [hdir] using hja
    have hspec := sourcePoissonVertexCoord_spec pred j
    rw [sourcePoissonVertexOfEdgeCoordAtAxis_apply_ne _ _ _ _ _ hja] at hspec
    have heval : e.1 j = Sum.inl (sourcePoissonVertexCoord v j) := by
      simpa [e, incomingLink] using incomingCell_apply_ne v i j hji
    rw [heval] at hspec
    apply Fin.ext
    exact congrArg Fin.val (Sum.inl.inj hspec).symm
  have hpredRest :
      (∑ j ∈ Finset.univ.erase a, (sourcePoissonVertexCoord pred j).val) =
        ∑ j ∈ Finset.univ.erase a, (sourcePoissonVertexCoord v j).val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hpredOther j (Finset.mem_erase.mp hj).1]
  have hpredSum : vertexRank pred =
      (sourcePoissonVertexCoord pred a).val +
        ∑ j ∈ Finset.univ.erase a, (sourcePoissonVertexCoord pred j).val := by
    unfold vertexRank
    exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)).symm
  have hvSum : vertexRank v =
      (sourcePoissonVertexCoord v a).val +
        ∑ j ∈ Finset.univ.erase a, (sourcePoissonVertexCoord v j).val := by
    unfold vertexRank
    exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)).symm
  rw [hpredSum, hpredRest, hvSum]
  omega

theorem incomingParent_rank_eq {v : SourceDualZeroCells B} {i : Fin 4}
    {w : SourceDualZeroCells B} (hparent : incomingParent v i = some w) :
    vertexRank w + 1 = vertexRank v := by
  change sourcePoissonEdgeLowerVertex (incomingLink v i) = some w at hparent
  rw [incomingLink_lowerVertex] at hparent
  by_cases hzero : sourcePoissonEdgeAxisIndex (incomingLink v i) = 0
  · simp [hzero] at hparent
  · simp [hzero] at hparent
    subst w
    exact incomingPredecessor_rank v i hzero

/-- Selected links are pairwise independent across every contained source
plaquette. -/
def PlaquetteIndependent (S : Finset (SourceDualOneCells B)) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
    ¬ ∃ p : SourceDualTwoCells B,
      linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p

noncomputable def incomingPlaquette (v : SourceDualZeroCells B) (i j : Fin 4)
    (hij : i ≠ j) :
    SourceDualTwoCells B := by
  let c := dualLowerFace (incomingLink v i).1 j (sourcePoissonVertexCoord v j)
  have hdir : linkDirection (incomingLink v i) = i := incomingLink_baseDirection v i
  have haxes : dualCellAxes c = {i, j} := by
    rw [show c = dualLowerFace (incomingLink v i).1 j
      (sourcePoissonVertexCoord v j) by rfl, lowerFace_axes_eq, hdir]
  exact ⟨c, by
    change (dualCellAxes c).card = 2
    rw [haxes]
    simp [hij]⟩

theorem incomingLinks_share_plaquette (v : SourceDualZeroCells B)
    {i j : Fin 4} (hij : i ≠ j) :
    ∃ p : SourceDualTwoCells B,
      linkIncidentPlaquette (incomingLink v i) p ∧
      linkIncidentPlaquette (incomingLink v j) p := by
  let p := incomingPlaquette v i j hij
  have hcell : (incomingLink v i).1 j = Sum.inl (sourcePoissonVertexCoord v j) := by
    simpa [incomingLink] using incomingCell_apply_ne v i j hij.symm
  have hcell' : (incomingLink v j).1 i = Sum.inl (sourcePoissonVertexCoord v i) := by
    simpa [incomingLink] using incomingCell_apply_ne v j i hij
  have hplaquette : p.1 = dualLowerFace (incomingLink v j).1 i
      (sourcePoissonVertexCoord v i) := by
    change (incomingPlaquette v i j hij).1 = _
    unfold incomingPlaquette
    change dualLowerFace (incomingCell v i) j (sourcePoissonVertexCoord v j) =
      dualLowerFace (incomingCell v j) i (sourcePoissonVertexCoord v i)
    simpa [incomingCell, dualLowerFace] using
      (Function.update_comm hij
        (Sum.inr ⟨(sourcePoissonVertexCoord v i).val,
          Nat.lt_succ_of_lt (sourcePoissonVertexCoord v i).isLt⟩)
        (Sum.inr ⟨(sourcePoissonVertexCoord v j).val,
          Nat.lt_succ_of_lt (sourcePoissonVertexCoord v j).isLt⟩)
        v.1)
  refine ⟨p, ?_, ?_⟩
  · refine ⟨j, sourcePoissonVertexCoord v j, hcell, ?_⟩
    right
    rfl
  · refine ⟨i, sourcePoissonVertexCoord v i, hcell', ?_⟩
    rw [hplaquette]
    right
    rfl

theorem exists_incomingLink_not_mem (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S) (v : SourceDualZeroCells B) :
    ∃ i : Fin 4, incomingLink v i ∉ S := by
  by_contra h
  have h0 : incomingLink v ⟨0, by decide⟩ ∈ S := by
    by_contra hn
    exact h ⟨⟨0, by decide⟩, hn⟩
  have h1 : incomingLink v ⟨1, by decide⟩ ∈ S := by
    by_contra hn
    exact h ⟨⟨1, by decide⟩, hn⟩
  have hne : (⟨0, by decide⟩ : Fin 4) ≠ ⟨1, by decide⟩ := by decide
  have hlinks : incomingLink v ⟨0, by decide⟩ ≠ incomingLink v ⟨1, by decide⟩ := by
    intro heq
    have hd := congrArg sourcePoissonEdgeAxis heq
    rw [incomingLink_direction, incomingLink_direction] at hd
    exact hne hd
  exact hS _ h0 _ h1 hlinks (incomingLinks_share_plaquette v hne)

noncomputable def selectedIncomingAxis (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S) (v : SourceDualZeroCells B) : Fin 4 :=
  Classical.choose (exists_incomingLink_not_mem S hS v)

theorem selectedIncomingAxis_avoids (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S) (v : SourceDualZeroCells B) :
    incomingLink v (selectedIncomingAxis S hS v) ∉ S :=
  Classical.choose_spec (exists_incomingLink_not_mem S hS v)


noncomputable def adaptiveParent (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S) (x : SourcePoissonVertex B) :
    SourcePoissonVertex B :=
  match x with
  | none => none
  | some v => incomingParent v (selectedIncomingAxis S hS v)

noncomputable def vertexMeasure (x : SourcePoissonVertex B) : ℕ :=
  match x with
  | none => 0
  | some v => vertexRank v + 1

theorem adaptiveParent_measure_lt (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S) (v : SourceDualZeroCells B) :
    vertexMeasure (adaptiveParent S hS (some v)) < vertexRank v + 1 := by
  let i := selectedIncomingAxis S hS v
  cases hp : incomingParent v i with
  | none => simp [adaptiveParent, i, hp, vertexMeasure]
  | some w =>
    have hu := incomingParent_rank_eq hp
    simp [adaptiveParent, i, hp, vertexMeasure]
    omega

noncomputable def adaptiveDepth (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S) : SourcePoissonVertex B → ℕ
  | none => 0
  | some v => adaptiveDepth S hS (adaptiveParent S hS (some v)) + 1
termination_by x => vertexMeasure x
decreasing_by
  exact adaptiveParent_measure_lt S hS v

theorem adaptiveDepth_le_vertexMeasure (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S) (x : SourcePoissonVertex B) :
    adaptiveDepth S hS x ≤ vertexMeasure x := by
  have hbound : ∀ n, ∀ x, vertexMeasure x = n → adaptiveDepth S hS x ≤ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      cases x with
      | none => simp [adaptiveDepth, vertexMeasure] at *
      | some v =>
        have hlt : vertexMeasure (adaptiveParent S hS (some v)) < n := by
          have hparent := adaptiveParent_measure_lt S hS v
          simp only [vertexMeasure] at hx
          rw [← hx]
          exact hparent
        have hrec := ih _ hlt (adaptiveParent S hS (some v)) rfl
        have heq : adaptiveDepth S hS (some v) =
            adaptiveDepth S hS (adaptiveParent S hS (some v)) + 1 := by
          simp only [adaptiveDepth]
        rw [heq]
        omega
  exact hbound (vertexMeasure x) x rfl

theorem vertexRank_le_boxVolume (v : SourceDualZeroCells B) :
    vertexRank v ≤ ∑ i : Fin 4, B i := by
  unfold vertexRank
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.le_of_lt (sourcePoissonVertexCoord v i).isLt

theorem adaptiveDepth_le_height (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S) (x : SourcePoissonVertex B) :
    adaptiveDepth S hS x ≤ (∑ i : Fin 4, B i) + 1 := by
  cases x with
  | none => simp [adaptiveDepth]
  | some v =>
    have hdepth := adaptiveDepth_le_vertexMeasure S hS (some v)
    have hrank := vertexRank_le_boxVolume v
    have hsum : vertexRank v + 1 ≤ (∑ i : Fin 4, B i) + 1 := Nat.add_le_add_right hrank 1
    simpa using hdepth.trans hsum

theorem exists_vertex_of_nonroot
    (x : {x : SourcePoissonVertex B // x ≠ none}) :
    ∃ v : SourceDualZeroCells B, x.1 = some v := by
  cases hx : x.1 with
  | none => exact (x.2 hx).elim
  | some v => exact ⟨v, rfl⟩

noncomputable def nonrootVertex
    (x : {x : SourcePoissonVertex B // x ≠ none}) : SourceDualZeroCells B :=
  Classical.choose (exists_vertex_of_nonroot x)

theorem nonrootVertex_spec
    (x : {x : SourcePoissonVertex B // x ≠ none}) :
    x.1 = some (nonrootVertex x) :=
  Classical.choose_spec (exists_vertex_of_nonroot x)

noncomputable def adaptiveTreeEdge (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S)
    (x : {x : SourcePoissonVertex B // x ≠ none}) : SourcePoissonEdge B :=
  incomingLink (nonrootVertex x) (selectedIncomingAxis S hS (nonrootVertex x))

theorem adaptiveTreeEdge_source (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S)
    (x : {x : SourcePoissonVertex B // x ≠ none}) :
    sourcePoissonEdgeLowerVertex (adaptiveTreeEdge S hS x) =
      adaptiveParent S hS x.1 := by
  rw [nonrootVertex_spec x]
  rfl

theorem adaptiveTreeEdge_target (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S)
    (x : {x : SourcePoissonVertex B // x ≠ none}) :
      sourcePoissonEdgeUpperVertex (adaptiveTreeEdge S hS x) = x.1 := by
  rw [nonrootVertex_spec x]
  exact incomingLink_upperVertex (nonrootVertex x)
    (selectedIncomingAxis S hS (nonrootVertex x))

/-- A rooted spanning tree using unselected positive links, with the same
oriented endpoint maps as the source tree. -/
noncomputable def adaptiveRootedTree (B : SourceBox)
    (S : Finset (SourceDualOneCells B))
    (hS : PlaquetteIndependent S) :
    RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B) where
  root := none
  parent := adaptiveParent S hS
  depth := adaptiveDepth S hS
  height := (∑ i : Fin 4, B i) + 1
  depth_le_height := adaptiveDepth_le_height S hS
  edgeSource := sourcePoissonEdgeLowerVertex
  edgeTarget := sourcePoissonEdgeUpperVertex
  treeEdge := adaptiveTreeEdge S hS
  treeEdge_injective := by
    intro x y hxy
    apply Subtype.ext
    have htarget := congrArg sourcePoissonEdgeUpperVertex hxy
    rw [adaptiveTreeEdge_target, adaptiveTreeEdge_target] at htarget
    exact htarget
  treeEdge_source := adaptiveTreeEdge_source S hS
  treeEdge_target := adaptiveTreeEdge_target S hS
  depth_root := by simp [adaptiveDepth]
  depth_pos := by
    intro x hx
    cases hxv : x with
    | none => exact (hx hxv).elim
    | some v => simp only [adaptiveDepth]; omega
  depth_parent := by
    intro x hx
    cases hxv : x with
    | none => exact (hx hxv).elim
    | some v => simp only [adaptiveDepth]

theorem adaptiveRootedTree_endpointMaps (B : SourceBox)
    (S : Finset (SourceDualOneCells B)) (hS : PlaquetteIndependent S) :
    (adaptiveRootedTree B S hS).edgeSource = (sourceRootedTree B).edgeSource ∧
      (adaptiveRootedTree B S hS).edgeTarget = (sourceRootedTree B).edgeTarget :=
  ⟨by simp [adaptiveRootedTree, sourceRootedTree],
   by simp [adaptiveRootedTree, sourceRootedTree]⟩

theorem adaptiveRootedTree_avoids (B : SourceBox)
    (S : Finset (SourceDualOneCells B)) (hS : PlaquetteIndependent S) :
    ∀ x : {x : SourcePoissonVertex B // x ≠ (adaptiveRootedTree B S hS).root},
      (adaptiveRootedTree B S hS).treeEdge x ∉ S := by
  intro x
  have hxroot : x.1 ≠ none := by
    simpa [adaptiveRootedTree] using x.2
  let x' : {x : SourcePoissonVertex B // x ≠ none} := ⟨x.1, hxroot⟩
  have hvertex : nonrootVertex x' = nonrootVertex x := by
    apply congrArg nonrootVertex
    apply Subtype.ext
    rfl
  change adaptiveTreeEdge S hS x' ∉ S
  rw [adaptiveTreeEdge]
  rw [hvertex]
  exact selectedIncomingAxis_avoids S hS (nonrootVertex x)


theorem plaquetteIndependent_colorClass (A : Finset (SourceDualOneCells B))
    (c : Fin 8) : PlaquetteIndependent (colorClass A linkColor c) := by
  classical
  intro e he f hf hne hshare
  have hcolor := linkColor_ne_of_sharedPlaquette hne hshare
  have hec : linkColor e = c := (Finset.mem_filter.mp he).2
  have hfc : linkColor f = c := (Finset.mem_filter.mp hf).2
  exact hcolor (hec.trans hfc.symm)


end FroehlichSpencer.FS82.Currents.AdaptiveTree

end
