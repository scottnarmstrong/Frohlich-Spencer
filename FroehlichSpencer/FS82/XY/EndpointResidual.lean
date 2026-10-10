/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Poisson3
public import FroehlichSpencer.FS82.Wilson.CubeLoopField
public import FroehlichSpencer.FS82.Wilson.ShiftProfile
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Order.Chebyshev

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The endpoint residual in three dimensions

This file proves the finite-box, endpoint-uniform energy bound for the
projection residual associated with the XY endpoint path.

The source reading
of (4.39) is that for `S₀ = {x,y}`, its cell volume is at most two (one when
`x = y`), so the limiting residual energy is bounded by a constant independent
of the endpoint separation.

The journal states this for the exhaustion limit;
the finite-cube theorem below is the stronger estimate needed by the finite
volume argument.

Source: Fröhlich–Spencer (1982), (4.39)–(4.40).
-/

public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Wilson
open scoped InnerProductSpace

noncomputable section

/-! ### Coordinates for a one-sided tube in a finite cube -/

private theorem xySite_coord_vertex {B : Dual3Box} (x : XYSites B)
    (i : Fin 3) : ∃ v : Fin (B i + 1), x.1 i = Sum.inl v := by
  cases hcoord : x.1 i with
  | inl v => exact ⟨v, rfl⟩
  | inr e =>
      have hi : i ∈ cellAxes x.1 := by
        simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hcoord]
        rfl
      have hpos : 0 < cellDegree x.1 := Finset.card_pos.mpr ⟨i, hi⟩
      omega

private noncomputable def xySiteVertexIndex {B : Dual3Box}
    (x : XYSites B) (i : Fin 3) : Fin (B i + 1) :=
  Classical.choose (xySite_coord_vertex x i)

private theorem xySiteVertexIndex_spec {B : Dual3Box}
    (x : XYSites B) (i : Fin 3) :
    x.1 i = Sum.inl (xySiteVertexIndex x i) :=
  Classical.choose_spec (xySite_coord_vertex x i)

private def xyVertexCell {B : Dual3Box}
    (v : (i : Fin 3) → Fin (B i + 1)) : Cell 3 B := fun i => Sum.inl (v i)

private theorem xySite_eq_xyVertexCell {B : Dual3Box} (x : XYSites B) :
    x.1 = xyVertexCell (xySiteVertexIndex x) := by
  funext i
  exact xySiteVertexIndex_spec x i

private def xyAxisTransverseA (i : Fin 3) : Fin 3 :=
  if i.val = 0 then 1 else if i.val = 1 then 2 else 0

private def xyAxisTransverseB (i : Fin 3) : Fin 3 :=
  if i.val = 0 then 2 else if i.val = 1 then 0 else 1

private theorem xyAxisTransverseA_ne (i : Fin 3) : xyAxisTransverseA i ≠ i := by
  fin_cases i <;> norm_num [xyAxisTransverseA]

private theorem xyAxisTransverseB_ne (i : Fin 3) : xyAxisTransverseB i ≠ i := by
  fin_cases i <;> norm_num [xyAxisTransverseB]

private theorem xyAxisTransverseAB_ne (i : Fin 3) :
    xyAxisTransverseA i ≠ xyAxisTransverseB i := by
  fin_cases i <;> norm_num [xyAxisTransverseA, xyAxisTransverseB]

private theorem xyAxis_ne_transverseA (i : Fin 3) : i ≠ xyAxisTransverseA i :=
  (xyAxisTransverseA_ne i).symm

private theorem xyAxis_ne_transverseB (i : Fin 3) : i ≠ xyAxisTransverseB i :=
  (xyAxisTransverseB_ne i).symm

private theorem xyAxisTransverseBA_ne (i : Fin 3) :
    xyAxisTransverseB i ≠ xyAxisTransverseA i :=
  (xyAxisTransverseAB_ne i).symm


private noncomputable def xyBondRealChain {B : Dual3Box}
    (f : XYBonds B → ℝ) : RealChain 3 B :=
  ∑ b : XYBonds B, f b • Finsupp.single b.1 1

private theorem xyBondRealChain_apply {B : Dual3Box}
    (f : XYBonds B → ℝ) (b : XYBonds B) :
    xyBondRealChain f b.1 = f b := by
  classical
  have hsum : (∑ b' : XYBonds B, (f b') • Finsupp.single b'.1 (1 : ℝ)) b.1 = f b := by
    rw [Finsupp.finsetSum_apply]
    calc
      _ = ((f b) • Finsupp.single b.1 (1 : ℝ)) b.1 := by
        apply Fintype.sum_eq_single b
        intro b' hne
        have hcell : b'.1 ≠ b.1 := fun heq => hne (Subtype.ext heq)
        simp [hcell]
      _ = f b := by simp
  simpa [xyBondRealChain] using hsum

private theorem xyBondRealChain_homogeneous {B : Dual3Box}
    (f : XYBonds B → ℝ) :
    realHomogeneousSupport (xyBondRealChain f) 1 := by
  intro c hc
  rw [Finsupp.mem_support_iff] at hc
  by_contra hdeg
  have hc0 : xyBondRealChain f c = 0 := by
    unfold xyBondRealChain
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro b hb
    have hbc : b.1 ≠ c := by
      intro heq
      subst c
      exact hdeg b.2
    simp [hbc]
  exact hc hc0

private theorem xyBondRealChain_energy {B : Dual3Box}
    (f : XYBonds B → ℝ) :
    xyDual3BondEnergy (xyBondRealChain f) = ∑ b : XYBonds B, (f b) ^ 2 := by
  unfold xyDual3BondEnergy
  apply Finset.sum_congr rfl
  intro b hb
  rw [xyBondRealChain_apply]

private noncomputable def xyBondAxis {B : Dual3Box} (b : XYBonds B) : Fin 3 :=
  Classical.choose (Finset.card_eq_one.mp (by
    simpa [cellDegree] using b.2))

private theorem xyBondAxis_axes {B : Dual3Box} (b : XYBonds B) :
    cellAxes b.1 = {xyBondAxis b} :=
  Classical.choose_spec (Finset.card_eq_one.mp (by simpa [cellDegree] using b.2))

private theorem xyBondAxis_isEdge {B : Dual3Box} (b : XYBonds B) :
    coordIsEdge (b.1 (xyBondAxis b)) := by
  classical
  have hmem : xyBondAxis b ∈ cellAxes b.1 := by rw [xyBondAxis_axes]; simp
  exact (Finset.mem_filter.mp hmem).2

private theorem xyBondAxis_edge_exists {B : Dual3Box} (b : XYBonds B) :
    ∃ e : Fin (B (xyBondAxis b)), b.1 (xyBondAxis b) = Sum.inr e := by
  cases h : b.1 (xyBondAxis b) with
  | inl v =>
      have he := xyBondAxis_isEdge b
      simp [coordIsEdge, h] at he
  | inr e => exact ⟨e, rfl⟩

private noncomputable def xyBondAxisEdge {B : Dual3Box} (b : XYBonds B) :
    Fin (B (xyBondAxis b)) := Classical.choose (xyBondAxis_edge_exists b)

private theorem xyBondAxisEdge_spec {B : Dual3Box} (b : XYBonds B) :
    b.1 (xyBondAxis b) = Sum.inr (xyBondAxisEdge b) :=
  Classical.choose_spec (xyBondAxis_edge_exists b)

private theorem xyBondAxis_other_isVertex {B : Dual3Box} (b : XYBonds B)
    {i : Fin 3} (hi : i ≠ xyBondAxis b) :
    ¬ coordIsEdge (b.1 i) := by
  classical
  intro hed
  have hmem : i ∈ cellAxes b.1 := by simp [cellAxes, hed]
  rw [xyBondAxis_axes] at hmem
  simp at hmem
  exact hi hmem

private theorem xyBond_boundaryBasis {B : Dual3Box} (b : XYBonds B) :
    boundaryBasis b.1 =
      basisChain (upperFace b.1 (xyBondAxis b) (xyBondAxisEdge b)) -
      basisChain (lowerFace b.1 (xyBondAxis b) (xyBondAxisEdge b)) := by
  classical
  have hi := xyBondAxis_isEdge b
  cases hcoord : b.1 (xyBondAxis b) with
  | inl v => exact False.elim (by simp [coordIsEdge, hcoord] at hi)
  | inr e =>
      have he : e = xyBondAxisEdge b := by
        have hspec := xyBondAxisEdge_spec b
        rw [hcoord] at hspec
        exact Sum.inr.inj hspec
      subst e
      have hrank : cellRankBefore b.1 (xyBondAxis b) = 0 := by
        unfold cellRankBefore
        rw [Finset.card_eq_zero.mpr]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact xyBondAxis_other_isVertex b (ne_of_lt hj.1) (by simpa [hcoord] using hj.2)
      unfold boundaryBasis
      rw [Finset.sum_eq_single (xyBondAxis b)]
      · simp [hcoord, hrank, basisChain]
      · intro j hj hji
        have hnot : ¬ coordIsEdge (b.1 j) := xyBondAxis_other_isVertex b hji
        cases hjcoord : b.1 j with
        | inl v => simp
        | inr e =>
            have he : coordIsEdge (b.1 j) := by rw [hjcoord]; simp [coordIsEdge]
            exact False.elim (hnot he)
      · intro hnot
        exact (hnot (Finset.mem_univ (xyBondAxis b))).elim

private theorem xyBondRealBoundary_basis {B : Dual3Box} (b : XYBonds B) :
    realBoundary (Finsupp.single b.1 (1 : ℝ)) =
      Finsupp.single (upperFace b.1 (xyBondAxis b) (xyBondAxisEdge b)) 1 -
        Finsupp.single (lowerFace b.1 (xyBondAxis b) (xyBondAxisEdge b)) 1 := by
  rw [realBoundary, realifyLinearMap_single, boundary_basis, xyBond_boundaryBasis]
  rw [castIntegerChain_sub, castIntegerChain_basis, castIntegerChain_basis]
  simp only [one_smul]

private theorem xyBondRealBoundary_apply {B : Dual3Box}
    (f : XYBonds B → ℝ) (c : Cell 3 B) :
    realBoundary (xyBondRealChain f) c =
      ∑ b : XYBonds B,
        f b * ((Finsupp.single
          (upperFace b.1 (xyBondAxis b) (xyBondAxisEdge b)) (1 : ℝ) -
          Finsupp.single
          (lowerFace b.1 (xyBondAxis b) (xyBondAxisEdge b)) (1 : ℝ)) c) := by
  classical
  rw [realBoundary, xyBondRealChain, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [map_smul]
  change (f b • realBoundary (Finsupp.single b.1 (1 : ℝ))) c = _
  rw [xyBondRealBoundary_basis]
  simp [smul_eq_mul]

private theorem xyVertexCell_axes_empty {B : Dual3Box}
    (v : (i : Fin 3) → Fin (B i + 1)) : cellAxes (xyVertexCell v) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  simp [cellAxes, coordIsEdge, xyVertexCell] at hj

private theorem xyVertexCell_eq_iff {B : Dual3Box}
    (v w : (i : Fin 3) → Fin (B i + 1)) :
    xyVertexCell v = xyVertexCell w ↔ v = w := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    exact Sum.inl.inj hi
  · intro h
    exact congrArg xyVertexCell h

private theorem xyEndpointDelta_eval {α : Type*} [DecidableEq α]
    (v base finish : α) :
    (if v = base then (-1 : ℝ) else 0) +
        (if v = finish then 1 else 0) =
      (if finish = v then 1 else 0) - (if base = v then 1 else 0) := by
  by_cases hb : v = base
  · by_cases hf : v = finish
    · have hb' : base = v := hb.symm
      have hf' : finish = v := hf.symm
      rw [ite_eq_left hb, ite_eq_left hf, ite_eq_left hf', ite_eq_left hb']
      ring
    · have hb' : base = v := hb.symm
      have hfn : finish ≠ v := fun h => hf h.symm
      rw [ite_eq_left hb, ite_eq_right hf, ite_eq_right hfn, ite_eq_left hb']
      norm_num
  · by_cases hf : v = finish
    · have hfn : finish = v := hf.symm
      have hbn : base ≠ v := fun h => hb h.symm
      rw [ite_eq_right hb, ite_eq_left hf, ite_eq_left hfn, ite_eq_right hbn]
      norm_num
    · have hbn : base ≠ v := fun h => hb h.symm
      have hfn : finish ≠ v := fun h => hf h.symm
      rw [ite_eq_right hb, ite_eq_right hf, ite_eq_right hfn, ite_eq_right hbn]
      norm_num

private noncomputable def xyBondFromVertexEdge {B : Dual3Box}
    (v : (i : Fin 3) → Fin (B i + 1)) (i : Fin 3) (e : Fin (B i)) :
    XYBonds B := ⟨edgeCell (xyVertexCell v) i e, by
      rw [cellDegree, cellAxes_edgeCell_eq_insert, xyVertexCell_axes_empty]
      simp⟩

private theorem xyBond_eq_incident_of_upperFace_eq {B : Dual3Box}
    (b : XYBonds B) (v : (j : Fin 3) → Fin (B j + 1)) (i : Fin 3)
    (e : Fin (B i)) (hEdge : b.1 i = Sum.inr e)
    (hFace : upperFace b.1 i e = xyVertexCell v) :
    b = xyBondFromVertexEdge v i e := by
  apply Subtype.ext
  funext j
  by_cases hji : j = i
  · subst j
    change b.1 i = (edgeCell (xyVertexCell v) i e) i
    simp [edgeCell, hEdge]
  · have hFacej := congrFun hFace j
    rw [upperFace_apply_of_ne b.1 i j e hji] at hFacej
    simpa [xyBondFromVertexEdge, edgeCell, Function.update_of_ne hji] using hFacej

private theorem xyBond_eq_incident_of_lowerFace_eq {B : Dual3Box}
    (b : XYBonds B) (v : (j : Fin 3) → Fin (B j + 1)) (i : Fin 3)
    (e : Fin (B i)) (hEdge : b.1 i = Sum.inr e)
    (hFace : lowerFace b.1 i e = xyVertexCell v) :
    b = xyBondFromVertexEdge v i e := by
  apply Subtype.ext
  funext j
  by_cases hji : j = i
  · subst j
    change b.1 i = (edgeCell (xyVertexCell v) i e) i
    simp [edgeCell, hEdge]
  · have hFacej := congrFun hFace j
    rw [lowerFace_apply_of_ne b.1 i j e hji] at hFacej
    simpa [xyBondFromVertexEdge, edgeCell, Function.update_of_ne hji] using hFacej

private theorem xyBond_upperFace_incident {B : Dual3Box}
    (b : XYBonds B) (v : (j : Fin 3) → Fin (B j + 1)) (i : Fin 3)
    (e : Fin (B i)) (hEdge : b.1 i = Sum.inr e)
    (hFace : upperFace b.1 i e = xyVertexCell v) :
    0 < (v i).val ∧
      b = xyBondFromVertexEdge v i ⟨(v i).val - 1, by
        have hcoord := congrFun hFace i
        simp [upperFace, vertexUpdate, Function.update_self, xyVertexCell] at hcoord
        have he := e.isLt
        omega⟩ := by
  have hcoord := congrFun hFace i
  simp [upperFace, vertexUpdate, Function.update_self, xyVertexCell] at hcoord
  have hval : e.val + 1 = (v i).val := congrArg Fin.val hcoord
  have hp : 0 < (v i).val := by omega
  let ein : Fin (B i) := ⟨(v i).val - 1, by
    have he := e.isLt
    omega⟩
  have he : e = ein := by
    apply Fin.ext
    dsimp [ein]
    omega
  have hb := xyBond_eq_incident_of_upperFace_eq b v i e hEdge hFace
  refine ⟨hp, ?_⟩
  calc
    b = xyBondFromVertexEdge v i e := hb
    _ = xyBondFromVertexEdge v i ein := by rw [he]

private theorem xyBond_lowerFace_incident {B : Dual3Box}
    (b : XYBonds B) (v : (j : Fin 3) → Fin (B j + 1)) (i : Fin 3)
    (e : Fin (B i)) (hEdge : b.1 i = Sum.inr e)
    (hFace : lowerFace b.1 i e = xyVertexCell v) :
    (v i).val < B i ∧
      b = xyBondFromVertexEdge v i ⟨(v i).val, by
        have hcoord := congrFun hFace i
        simp [lowerFace, vertexUpdate, Function.update_self, xyVertexCell] at hcoord
        have hval : (v i).val = e.val := by
          exact (congrArg Fin.val hcoord).symm
        omega⟩ := by
  have hcoord := congrFun hFace i
  simp [lowerFace, vertexUpdate, Function.update_self, xyVertexCell] at hcoord
  have hval : e.val = (v i).val := congrArg Fin.val hcoord
  have hout : (v i).val < B i := by
    have he := e.isLt
    omega
  let eout : Fin (B i) := ⟨(v i).val, hout⟩
  have he : e = eout := by
    apply Fin.ext
    exact hval
  have hb := xyBond_eq_incident_of_lowerFace_eq b v i e hEdge hFace
  refine ⟨hout, ?_⟩
  calc
    b = xyBondFromVertexEdge v i e := hb
    _ = xyBondFromVertexEdge v i eout := by rw [he]

private theorem xyBond_upperFace_eq_of_incident {B : Dual3Box}
    (v : (j : Fin 3) → Fin (B j + 1)) (i : Fin 3) (e : Fin (B i))
    (he : e.val + 1 = (v i).val) :
    upperFace (xyBondFromVertexEdge v i e).1 i e = xyVertexCell v := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [upperFace, vertexUpdate, xyBondFromVertexEdge, edgeCell,
      Function.update_self]
    congr 1
    apply Fin.ext
    exact he
  · simp [upperFace, vertexUpdate, xyBondFromVertexEdge, edgeCell,
      Function.update_of_ne hji]

private theorem xyBond_lowerFace_eq_of_incident {B : Dual3Box}
    (v : (j : Fin 3) → Fin (B j + 1)) (i : Fin 3) (e : Fin (B i))
    (he : e.val = (v i).val) :
    lowerFace (xyBondFromVertexEdge v i e).1 i e = xyVertexCell v := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [lowerFace, vertexUpdate, xyBondFromVertexEdge, edgeCell,
      Function.update_self]
    congr 1
    apply Fin.ext
    exact he
  · simp [lowerFace, vertexUpdate, xyBondFromVertexEdge, edgeCell,
      Function.update_of_ne hji]

private theorem xyBondFromVertexEdge_axis {B : Dual3Box}
    (v : (i : Fin 3) → Fin (B i + 1)) (i : Fin 3) (e : Fin (B i)) :
    xyBondAxis (xyBondFromVertexEdge v i e) = i := by
  have haxes := xyBondAxis_axes (xyBondFromVertexEdge v i e)
  change cellAxes (edgeCell (xyVertexCell v) i e) = _ at haxes
  rw [cellAxes_edgeCell_eq_insert, xyVertexCell_axes_empty] at haxes
  simp only [Finset.insert_empty] at haxes
  exact (Finset.singleton_injective haxes).symm

private theorem xyBondIncoming_ne_outgoing {B : Dual3Box}
    (v : (i : Fin 3) → Fin (B i + 1)) (i : Fin 3)
    (hp : 0 < (v i).val) (hout : (v i).val < B i) :
    xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩ ≠
      xyBondFromVertexEdge v i ⟨(v i).val, hout⟩ := by
  intro h
  have hc := congrFun (congrArg Subtype.val h) i
  simp [xyBondFromVertexEdge, edgeCell] at hc
  omega

private def xyBondIncidenceAtVertex {B : Dual3Box}
    (b : XYBonds B) (v : (i : Fin 3) → Fin (B i + 1)) (i : Fin 3) : ℝ :=
  (if h : 0 < (v i).val then
      if b = xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩ then 1 else 0
    else 0) -
  (if h : (v i).val < B i then
      if b = xyBondFromVertexEdge v i ⟨(v i).val, h⟩ then 1 else 0
    else 0)

private theorem xyBondAxis_eq_of_eq_incident {B : Dual3Box}
    (b : XYBonds B) (v : (i : Fin 3) → Fin (B i + 1)
    ) (i : Fin 3) (e : Fin (B i))
    (h : b = xyBondFromVertexEdge v i e) : xyBondAxis b = i := by
  rw [h]
  exact xyBondFromVertexEdge_axis v i e

private theorem xyBondIncidenceAtVertex_zero_of_axis_ne {B : Dual3Box}
    (b : XYBonds B) (v : (i : Fin 3) → Fin (B i + 1)) (i : Fin 3)
    (haxis : i ≠ xyBondAxis b) : xyBondIncidenceAtVertex b v i = 0 := by
  by_cases hp : 0 < (v i).val
  · have hneIn : b ≠ xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩ := by
      intro heq
      exact haxis (xyBondAxis_eq_of_eq_incident b v i _ heq).symm
    by_cases hout : (v i).val < B i
    · have hneOut : b ≠ xyBondFromVertexEdge v i ⟨(v i).val, hout⟩ := by
        intro heq
        exact haxis (xyBondAxis_eq_of_eq_incident b v i _ heq).symm
      simp [xyBondIncidenceAtVertex, hp, hout, hneIn, hneOut]
    · simp [xyBondIncidenceAtVertex, hp, hout, hneIn]
  · by_cases hout : (v i).val < B i
    · have hneOut : b ≠ xyBondFromVertexEdge v i ⟨(v i).val, hout⟩ := by
        intro heq
        exact haxis (xyBondAxis_eq_of_eq_incident b v i _ heq).symm
      simp [xyBondIncidenceAtVertex, hp, hout, hneOut]
    · simp [xyBondIncidenceAtVertex, hp, hout]

private theorem xyBond_sum_if_eq {B : Dual3Box} (f : XYBonds B → ℝ)
    (e : XYBonds B) :
    (∑ b : XYBonds B, if b = e then f b else 0) = f e := by
  classical
  exact Fintype.sum_ite_eq' e f

private theorem xyBond_sum_mul_indicator {B : Dual3Box} (f : XYBonds B → ℝ)
    (e : XYBonds B) :
    (∑ b : XYBonds B, f b * (if b = e then (1 : ℝ) else 0)) = f e := by
  simpa only [mul_ite, mul_one, mul_zero] using xyBond_sum_if_eq f e

private theorem xyBondRealBoundaryBasis_apply_vertex {B : Dual3Box}
    (b : XYBonds B) (v : (i : Fin 3) → Fin (B i + 1)) :
    (Finsupp.single
        (upperFace b.1 (xyBondAxis b) (xyBondAxisEdge b)) (1 : ℝ) -
      Finsupp.single
        (lowerFace b.1 (xyBondAxis b) (xyBondAxisEdge b)) (1 : ℝ))
        (xyVertexCell v) =
      ∑ i : Fin 3, xyBondIncidenceAtVertex b v i := by
  classical
  let i := xyBondAxis b
  let e := xyBondAxisEdge b
  have hEdge : b.1 i = Sum.inr e := by simpa [i, e] using xyBondAxisEdge_spec b
  have hUpper : upperFace b.1 i e = xyVertexCell v ↔
      dite (0 < (v i).val)
        (fun hp => b = xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩)
        (fun _ => False) := by
    constructor
    · intro hface
      obtain ⟨hp, hb⟩ := xyBond_upperFace_incident b v i e hEdge hface
      simp [hp, hb]
    · intro hb
      by_cases hp : 0 < (v i).val
      · have hb' : b = xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩ := by
          simp [hp] at hb
          exact hb
        let ein : Fin (B i) := ⟨(v i).val - 1, by omega⟩
        have hEdge' : b.1 i = Sum.inr ein := by
          rw [hb']
          simp [xyBondFromVertexEdge, edgeCell, ein]
        have he : e = ein := Sum.inr.inj (hEdge.symm.trans hEdge')
        calc
          upperFace b.1 i e =
              upperFace (xyBondFromVertexEdge v i ein).1 i ein := by rw [hb', he]
          _ = xyVertexCell v := xyBond_upperFace_eq_of_incident v i ein (by
            dsimp [ein]
            omega)
      · simp [hp] at hb
  have hLower : lowerFace b.1 i e = xyVertexCell v ↔
      dite ((v i).val < B i)
        (fun hout => b = xyBondFromVertexEdge v i ⟨(v i).val, hout⟩)
        (fun _ => False) := by
    constructor
    · intro hface
      obtain ⟨hout, hb⟩ := xyBond_lowerFace_incident b v i e hEdge hface
      simp [hout, hb]
    · intro hb
      by_cases hout : (v i).val < B i
      · have hb' : b = xyBondFromVertexEdge v i ⟨(v i).val, hout⟩ := by
          simp [hout] at hb
          exact hb
        let eout : Fin (B i) := ⟨(v i).val, hout⟩
        have hEdge' : b.1 i = Sum.inr eout := by
          rw [hb']
          simp [xyBondFromVertexEdge, edgeCell, eout]
        have he : e = eout := Sum.inr.inj (hEdge.symm.trans hEdge')
        calc
          lowerFace b.1 i e =
          lowerFace (xyBondFromVertexEdge v i eout).1 i eout := by rw [hb', he]
          _ = xyVertexCell v := xyBond_lowerFace_eq_of_incident v i eout (by
            rfl)
      · simp [hout] at hb
  have hUpper' : upperFace b.1 (xyBondAxis b) (xyBondAxisEdge b) = xyVertexCell v ↔
      dite (0 < (v (xyBondAxis b)).val)
        (fun hp => b = xyBondFromVertexEdge v (xyBondAxis b)
          ⟨(v (xyBondAxis b)).val - 1, by omega⟩) (fun _ => False) := by
    simpa [i, e] using hUpper
  have hLower' : lowerFace b.1 (xyBondAxis b) (xyBondAxisEdge b) = xyVertexCell v ↔
      dite ((v (xyBondAxis b)).val < B (xyBondAxis b))
        (fun hout => b = xyBondFromVertexEdge v (xyBondAxis b)
          ⟨(v (xyBondAxis b)).val, hout⟩) (fun _ => False) := by
    simpa [i, e] using hLower
  rw [Finset.sum_eq_single i]
  · rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp only [hUpper', hLower']
    by_cases hp : 0 < (v (xyBondAxis b)).val
    · by_cases hout : (v (xyBondAxis b)).val < B (xyBondAxis b)
      · by_cases hin : b = xyBondFromVertexEdge v (xyBondAxis b)
            ⟨(v (xyBondAxis b)).val - 1, by omega⟩
        · by_cases houtEq : b = xyBondFromVertexEdge v (xyBondAxis b)
              ⟨(v (xyBondAxis b)).val, hout⟩
          · have hne := xyBondIncoming_ne_outgoing v (xyBondAxis b) hp hout
            exact (hne (hin.symm.trans houtEq)).elim
          · have hne := xyBondIncoming_ne_outgoing v (xyBondAxis b) hp hout
            simp [xyBondIncidenceAtVertex, i, hp, hout, hin,
              hne, xyBondFromVertexEdge_axis]
        · by_cases houtEq : b = xyBondFromVertexEdge v (xyBondAxis b)
              ⟨(v (xyBondAxis b)).val, hout⟩
          · have hne := xyBondIncoming_ne_outgoing v (xyBondAxis b) hp hout
            simp [xyBondIncidenceAtVertex, i, hp, hout, houtEq,
              xyBondFromVertexEdge_axis]
          · simp [xyBondIncidenceAtVertex, i, hp, hout, hin, houtEq]
      · by_cases hin : b = xyBondFromVertexEdge v (xyBondAxis b)
            ⟨(v (xyBondAxis b)).val - 1, by omega⟩
        · simp [xyBondIncidenceAtVertex, i, hp, hout, hin,
            xyBondFromVertexEdge_axis]
        · simp [xyBondIncidenceAtVertex, i, hp, hout, hin]
    · by_cases hout : (v (xyBondAxis b)).val < B (xyBondAxis b)
      · by_cases houtEq : b = xyBondFromVertexEdge v (xyBondAxis b)
            ⟨(v (xyBondAxis b)).val, hout⟩
        · simp [xyBondIncidenceAtVertex, i, hp, houtEq]
        · simp [xyBondIncidenceAtVertex, i, hp, hout, houtEq]
      · simp [xyBondIncidenceAtVertex, i, hp, hout]
  · intro j hj hji
    exact xyBondIncidenceAtVertex_zero_of_axis_ne b v j hji
  · intro hnot
    exact (hnot (Finset.mem_univ i)).elim

private theorem xyBondIncidence_sum {B : Dual3Box}
    (f : XYBonds B → ℝ) (v : (i : Fin 3) → Fin (B i + 1)) (i : Fin 3) :
    ∑ b : XYBonds B, f b * xyBondIncidenceAtVertex b v i =
      (if h : 0 < (v i).val then
        f (xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩) else 0) -
      (if h : (v i).val < B i then
        f (xyBondFromVertexEdge v i ⟨(v i).val, h⟩) else 0) := by
  classical
  by_cases hp : 0 < (v i).val
  · by_cases hout : (v i).val < B i
    · simp only [xyBondIncidenceAtVertex, dite_eq_left hp, dite_eq_left hout]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [xyBond_sum_mul_indicator f
        (xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩)]
      rw [xyBond_sum_mul_indicator f (xyBondFromVertexEdge v i ⟨(v i).val, hout⟩)]
    · simp only [xyBondIncidenceAtVertex, dite_eq_left hp, dite_eq_right hout]
      simpa only [sub_zero] using xyBond_sum_mul_indicator f
        (xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩)
  · by_cases hout : (v i).val < B i
    · simp only [xyBondIncidenceAtVertex, dite_eq_right hp, dite_eq_left hout]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      simp only [mul_zero, Finset.sum_const_zero]
      rw [xyBond_sum_mul_indicator f
        (xyBondFromVertexEdge v i ⟨(v i).val, hout⟩)]
    · simp only [xyBondIncidenceAtVertex, dite_eq_right hp, dite_eq_right hout,
        sub_self, mul_zero, Finset.sum_const_zero]

private theorem xyBondRealBoundary_vertex_formula {B : Dual3Box}
    (f : XYBonds B → ℝ) (v : (i : Fin 3) → Fin (B i + 1)) :
    realBoundary (xyBondRealChain f) (xyVertexCell v) =
      ∑ i : Fin 3,
        ((if h : 0 < (v i).val then
            f (xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩) else 0) -
          (if h : (v i).val < B i then
            f (xyBondFromVertexEdge v i ⟨(v i).val, h⟩) else 0)) := by
  classical
  rw [xyBondRealBoundary_apply]
  calc
    _ = ∑ b : XYBonds B, f b *
          ∑ i : Fin 3, xyBondIncidenceAtVertex b v i := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [xyBondRealBoundaryBasis_apply_vertex]
    _ = ∑ b : XYBonds B, ∑ i : Fin 3, f b * xyBondIncidenceAtVertex b v i := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
    _ = ∑ i : Fin 3, ∑ b : XYBonds B, f b * xyBondIncidenceAtVertex b v i :=
          Finset.sum_comm
    _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          exact xyBondIncidence_sum f v i

private def xyBondBoundaryTerm {B : Dual3Box}
    (f : XYBonds B → ℝ) (v : (i : Fin 3) → Fin (B i + 1)) (i : Fin 3) : ℝ :=
  (if h : 0 < (v i).val then
      f (xyBondFromVertexEdge v i ⟨(v i).val - 1, by omega⟩) else 0) -
    (if h : (v i).val < B i then
      f (xyBondFromVertexEdge v i ⟨(v i).val, h⟩) else 0)

private def xyTubeSiteOffset {B : Dual3Box}
    (i : Fin 3) (base u : Fin (B i + 1)) : ℤ :=
  if 2 * base.val ≤ B i then (u.val : ℤ) - base.val
  else (base.val : ℤ) - u.val

private theorem xyTubeSiteOffset_eq_zero_iff {B : Dual3Box}
    (i : Fin 3) (base u : Fin (B i + 1)) :
    xyTubeSiteOffset i base u = 0 ↔ u = base := by
  by_cases h : 2 * base.val ≤ B i
  · simp [xyTubeSiteOffset, h]
    omega
  · simp [xyTubeSiteOffset, h]
    omega

private def xyTubeEdgeLevel {B : Dual3Box}
    (i : Fin 3) (base : Fin (B i + 1)) (e : Fin (B i)) : ℤ :=
  if 2 * base.val ≤ B i then ((e.val : ℤ) - base.val) + 1
  else (base.val : ℤ) - e.val


private def xyTubeOrientationSign {B : Dual3Box}
    (i : Fin 3) (base : Fin (B i + 1)) : ℝ :=
  if 2 * base.val ≤ B i then 1 else -1

private noncomputable def xyTubeSegmentBondCoeff {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (b : XYBonds B) : ℝ := by
  classical
  let a := xyAxisTransverseA axis
  let z := xyAxisTransverseB axis
  let c := b.1
  exact match c axis, c a, c z with
  | Sum.inr t, Sum.inl u, Sum.inl v =>
      let s := (t.val : ℤ) - (base axis).val
      if hs : 0 ≤ s ∧ s < (L : ℤ) then
        uni (min s.toNat (L - 1 - s.toNat))
          (xyTubeSiteOffset a (base a) u) *
          uni (min s.toNat (L - 1 - s.toNat))
          (xyTubeSiteOffset z (base z) v)
      else 0
  | Sum.inl k, Sum.inr e, Sum.inl v =>
      let s := (k.val : ℤ) - (base axis).val
      if _hs : 0 < s ∧ s < (L : ℤ) then
        let sn := s.toNat
        let left := min (sn - 1) (L - sn)
        let right := min sn (L - 1 - sn)
        let r := min left right
        if left < right then
          xyTubeOrientationSign a (base a) * levelThree r
            (xyTubeEdgeLevel a (base a) e) (xyTubeSiteOffset z (base z) v)
        else if right < left then
          -xyTubeOrientationSign a (base a) * levelThree r
            (xyTubeEdgeLevel a (base a) e) (xyTubeSiteOffset z (base z) v)
        else 0
      else 0
  | Sum.inl k, Sum.inl u, Sum.inr e =>
      let s := (k.val : ℤ) - (base axis).val
      if _hs : 0 < s ∧ s < (L : ℤ) then
        let sn := s.toNat
        let left := min (sn - 1) (L - sn)
        let right := min sn (L - 1 - sn)
        let r := min left right
        if left < right then
          -xyTubeOrientationSign z (base z) * levelTwo r
            (xyTubeSiteOffset a (base a) u) (xyTubeEdgeLevel z (base z) e)
        else if right < left then
          xyTubeOrientationSign z (base z) * levelTwo r
            (xyTubeSiteOffset a (base a) u) (xyTubeEdgeLevel z (base z) e)
        else 0
      else 0
  | _, _, _ => 0

@[simp] private theorem xyTubeSegmentBondCoeff_axial {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (v : (i : Fin 3) → Fin (B i + 1)) (e : Fin (B axis)) :
    xyTubeSegmentBondCoeff axis base L (xyBondFromVertexEdge v axis e) =
      if _h : 0 ≤ (e.val : ℤ) - (base axis).val ∧
          (e.val : ℤ) - (base axis).val < (L : ℤ) then
        uni (min ((e.val : ℤ) - (base axis).val).toNat
          (L - 1 - ((e.val : ℤ) - (base axis).val).toNat))
          (xyTubeSiteOffset (xyAxisTransverseA axis)
            (base (xyAxisTransverseA axis)) (v (xyAxisTransverseA axis))) *
        uni (min ((e.val : ℤ) - (base axis).val).toNat
          (L - 1 - ((e.val : ℤ) - (base axis).val).toNat))
          (xyTubeSiteOffset (xyAxisTransverseB axis)
            (base (xyAxisTransverseB axis)) (v (xyAxisTransverseB axis)))
      else 0 := by
  classical
  simp [xyTubeSegmentBondCoeff, xyBondFromVertexEdge, edgeCell,
    xyVertexCell, xyAxisTransverseA_ne, xyAxisTransverseB_ne]

@[simp] private theorem xyTubeSegmentBondCoeff_transA {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (v : (i : Fin 3) → Fin (B i + 1))
    (e : Fin (B (xyAxisTransverseA axis))) :
    xyTubeSegmentBondCoeff axis base L
        (xyBondFromVertexEdge v (xyAxisTransverseA axis) e) =
      let s : ℤ := (v axis).val - (base axis).val
      if _hs : 0 < s ∧ s < (L : ℤ) then
        let sn := s.toNat
        let left := min (sn - 1) (L - sn)
        let right := min sn (L - 1 - sn)
        let r := min left right
        if left < right then
          xyTubeOrientationSign (xyAxisTransverseA axis)
            (base (xyAxisTransverseA axis)) *
            levelThree r
              (xyTubeEdgeLevel (xyAxisTransverseA axis)
                (base (xyAxisTransverseA axis)) e)
              (xyTubeSiteOffset (xyAxisTransverseB axis)
                (base (xyAxisTransverseB axis)) (v (xyAxisTransverseB axis)))
        else if right < left then
          -xyTubeOrientationSign (xyAxisTransverseA axis)
            (base (xyAxisTransverseA axis)) *
            levelThree r
              (xyTubeEdgeLevel (xyAxisTransverseA axis)
                (base (xyAxisTransverseA axis)) e)
              (xyTubeSiteOffset (xyAxisTransverseB axis)
                (base (xyAxisTransverseB axis)) (v (xyAxisTransverseB axis)))
        else 0
      else 0 := by
  classical
  simp [xyTubeSegmentBondCoeff, xyBondFromVertexEdge, edgeCell,
    xyVertexCell, xyAxis_ne_transverseA, xyAxisTransverseBA_ne]

@[simp] private theorem xyTubeSegmentBondCoeff_transB {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (v : (i : Fin 3) → Fin (B i + 1))
    (e : Fin (B (xyAxisTransverseB axis))) :
    xyTubeSegmentBondCoeff axis base L
        (xyBondFromVertexEdge v (xyAxisTransverseB axis) e) =
      let s : ℤ := (v axis).val - (base axis).val
      if _hs : 0 < s ∧ s < (L : ℤ) then
        let sn := s.toNat
        let left := min (sn - 1) (L - sn)
        let right := min sn (L - 1 - sn)
        let r := min left right
        if left < right then
          -xyTubeOrientationSign (xyAxisTransverseB axis)
            (base (xyAxisTransverseB axis)) *
            levelTwo r
              (xyTubeSiteOffset (xyAxisTransverseA axis)
                (base (xyAxisTransverseA axis)) (v (xyAxisTransverseA axis)))
              (xyTubeEdgeLevel (xyAxisTransverseB axis)
                (base (xyAxisTransverseB axis)) e)
        else if right < left then
          xyTubeOrientationSign (xyAxisTransverseB axis)
            (base (xyAxisTransverseB axis)) *
            levelTwo r
              (xyTubeSiteOffset (xyAxisTransverseA axis)
                (base (xyAxisTransverseA axis)) (v (xyAxisTransverseA axis)))
              (xyTubeEdgeLevel (xyAxisTransverseB axis)
                (base (xyAxisTransverseB axis)) e)
        else 0
      else 0 := by
  classical
  simp [xyTubeSegmentBondCoeff, xyBondFromVertexEdge, edgeCell,
    xyVertexCell, xyAxis_ne_transverseB, xyAxisTransverseAB_ne]


private theorem xyTubeLayerRadii (L s : ℕ) (hs0 : 0 < s) (hsL : s < L) :
    (2 * s < L ∧ min (s - 1) (L - s) = s - 1 ∧
      min s (L - 1 - s) = s ∧
      min (min (s - 1) (L - s)) (min s (L - 1 - s)) = s - 1) ∨
    (2 * s = L ∧ min (s - 1) (L - s) = s - 1 ∧
      min s (L - 1 - s) = s - 1 ∧
      min (min (s - 1) (L - s)) (min s (L - 1 - s)) = s - 1) ∨
    (L < 2 * s ∧ min (s - 1) (L - s) = L - s ∧
      min s (L - 1 - s) = L - 1 - s ∧
      min (min (s - 1) (L - s)) (min s (L - 1 - s)) = L - 1 - s) := by
  rcases lt_trichotomy (2 * s) L with h | h | h
  · left
    have hleft : s - 1 ≤ L - s := by omega
    have hright : s ≤ L - 1 - s := by omega
    simp [Nat.min_eq_left hleft, Nat.min_eq_left hright]
    omega
  · right
    left
    have hleft : s - 1 ≤ L - s := by omega
    have hright : L - 1 - s ≤ s := by omega
    simp [h, Nat.min_eq_left hleft, Nat.min_eq_right hright]
    omega
  · right
    right
    have hleft : L - s ≤ s - 1 := by omega
    have hright : L - 1 - s ≤ s := by omega
    simp [Nat.min_eq_right hleft, Nat.min_eq_right hright]
    omega


private theorem xyTubeSiteOffset_edgeLevel_incoming {B : Dual3Box}
    (i : Fin 3) (base u : Fin (B i + 1)) (hIn : 0 < u.val) :
    xyTubeEdgeLevel i base ⟨u.val - 1, by omega⟩ =
      if 2 * base.val ≤ B i then xyTubeSiteOffset i base u
      else xyTubeSiteOffset i base u + 1 := by
  by_cases h : 2 * base.val ≤ B i
  · simp [xyTubeEdgeLevel, xyTubeSiteOffset, h]
    omega
  · simp [xyTubeEdgeLevel, xyTubeSiteOffset, h]
    omega

private theorem xyTubeSiteOffset_edgeLevel_outgoing {B : Dual3Box}
    (i : Fin 3) (base u : Fin (B i + 1)) (hOut : u.val < B i) :
    xyTubeEdgeLevel i base ⟨u.val, hOut⟩ =
      if 2 * base.val ≤ B i then xyTubeSiteOffset i base u + 1
      else xyTubeSiteOffset i base u := by
  by_cases h : 2 * base.val ≤ B i
  · simp [xyTubeEdgeLevel, xyTubeSiteOffset, h]
  · simp [xyTubeEdgeLevel, xyTubeSiteOffset, h]

private theorem xyTubeOrientationSign_mul_edgeDifference {B : Dual3Box}
    (i : Fin 3) (base u : Fin (B i + 1))
    (hIn : 0 < u.val) (hOut : u.val < B i) (f : ℤ → ℝ) :
    xyTubeOrientationSign i base *
      (f (xyTubeEdgeLevel i base ⟨u.val - 1, by omega⟩) -
        f (xyTubeEdgeLevel i base ⟨u.val, hOut⟩)) =
      f (xyTubeSiteOffset i base u) - f (xyTubeSiteOffset i base u + 1) := by
  rw [xyTubeSiteOffset_edgeLevel_incoming i base u hIn,
    xyTubeSiteOffset_edgeLevel_outgoing i base u hOut]
  by_cases h : 2 * base.val ≤ B i
  · simp [xyTubeOrientationSign, xyTubeSiteOffset, h]
  · simp [xyTubeOrientationSign, xyTubeSiteOffset, h]


private theorem xyTubeOrientationSign_mul_profileBoundary {B : Dual3Box}
    (i : Fin 3) (base u : Fin (B i + 1)) (d : ℕ) (f : ℤ → ℝ)
    (hsupport : ∀ j, f j ≠ 0 → 1 ≤ j ∧ j ≤ (d : ℤ) + 1)
    (hd : 2 * (d + 1) ≤ B i) :
    xyTubeOrientationSign i base *
        ((if h : 0 < u.val then
            f (xyTubeEdgeLevel i base ⟨u.val - 1, by omega⟩) else 0) -
          (if h : u.val < B i then
            f (xyTubeEdgeLevel i base ⟨u.val, h⟩) else 0)) =
      f (xyTubeSiteOffset i base u) - f (xyTubeSiteOffset i base u + 1) := by
  have hbelow : ∀ j, j < 1 → f j = 0 := by
    intro j hj
    by_contra hne
    have hs := hsupport j hne
    omega
  have habove : ∀ j, (d : ℤ) + 1 < j → f j = 0 := by
    intro j hj
    by_contra hne
    have hs := hsupport j hne
    omega
  by_cases hin : 0 < u.val
  · by_cases hout : u.val < B i
    · simp only [dite_eq_left hin, dite_eq_left hout]
      exact xyTubeOrientationSign_mul_edgeDifference i base u hin hout f
    · have hu : u.val = B i := by omega
      have hBpos : 0 < B i := by omega
      have hu' : u = ⟨B i, by omega⟩ := Fin.ext hu
      rw [hu']
      dsimp
      by_cases horient : 2 * base.val ≤ B i
      · have hfar : (d : ℤ) + 1 ≤ (B i : ℤ) - base.val := by omega
        have hzero' : f ((B i : ℤ) - base.val + 1) = 0 :=
          habove _ (by omega)
        simp_all [xyTubeOrientationSign, xyTubeSiteOffset, xyTubeEdgeLevel]
        congr 1
        ring_nf
      · have hnot : ¬2 * base.val ≤ B i := by omega
        have hzero : f (base.val - (B i : ℤ)) = 0 := hbelow _ (by omega)
        simp [xyTubeOrientationSign, xyTubeSiteOffset, xyTubeEdgeLevel,
          hnot, hzero, hBpos]
        have harg : (base.val : ℤ) - ((B i : ℤ) - 1) =
            1 + base.val - (B i : ℤ) := by ring
        rw [harg]
        congr 1
        ring_nf
  · have hu : u.val = 0 := by omega
    have hBpos : 0 < B i := by omega
    have hout : u.val < B i := by omega
    have hu' : u = ⟨0, by omega⟩ := Fin.ext hu
    rw [hu']
    dsimp
    by_cases horient : 2 * base.val ≤ B i
    · by_cases hbase : base.val = 0
      · have hzero : f 0 = 0 := hbelow 0 (by norm_num)
        simp_all [xyTubeOrientationSign, xyTubeSiteOffset, xyTubeEdgeLevel]
      · have hbasePos : 1 ≤ base.val := by omega
        have hzero : f (-(base.val : ℤ)) = 0 := hbelow _ (by omega)
        have hzero' : f (1 - (base.val : ℤ)) = 0 := hbelow _ (by omega)
        simp_all [xyTubeOrientationSign, xyTubeSiteOffset, xyTubeEdgeLevel]
    · have hfar : (d : ℤ) + 1 < base.val := by omega
      have hzero : f base.val = 0 := habove _ hfar
      have hzero' : f (base.val + 1) = 0 := habove _ (by omega)
      simp [xyTubeOrientationSign, xyTubeSiteOffset, xyTubeEdgeLevel,
        horient, hzero, hzero', hBpos]


private theorem xyTubeExpandingLayer_divergence (d : ℕ) (y z : ℤ) :
    (uni d y * uni d z - uni (d + 1) y * uni (d + 1) z) +
      -(levelThree d (y + 1) z - levelThree d y z) +
      (levelTwo d y (z + 1) - levelTwo d y z) = 0 := by
  have hc := curl_level d y z
  calc
    _ = (uni d y * uni d z - uni (d + 1) y * uni (d + 1) z) -
        ((levelThree d (y + 1) z - levelThree d y z) -
          (levelTwo d y (z + 1) - levelTwo d y z)) := by ring
    _ = 0 := by rw [hc]; ring

private theorem xyTubeContractingLayer_divergence (d : ℕ) (y z : ℤ) :
    (uni (d + 1) y * uni (d + 1) z - uni d y * uni d z) -
      -(levelThree d (y + 1) z - levelThree d y z) -
      (levelTwo d y (z + 1) - levelTwo d y z) = 0 := by
  have hc := curl_level d y z
  calc
    _ = (uni (d + 1) y * uni (d + 1) z - uni d y * uni d z) +
        ((levelThree d (y + 1) z - levelThree d y z) -
          (levelTwo d y (z + 1) - levelTwo d y z)) := by ring
    _ = 0 := by rw [hc]; ring

private theorem natCast_add_toNat (a n : ℕ) :
    ((a : ℤ) + (n : ℤ)).toNat = a + n := by
  have hcast := Int.toNat_of_nonneg (show 0 ≤ (a : ℤ) + (n : ℤ) by omega)
  exact_mod_cast hcast


private theorem xyTubeSegment_boundary_at_end {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (hL : 0 < L) (hEnd : (base axis).val + L ≤ B axis) :
    realBoundary (xyBondRealChain (xyTubeSegmentBondCoeff axis base L))
      (xyVertexCell (Function.update base axis
        ⟨(base axis).val + L, by omega⟩)) = 1 := by
  let finish := Function.update base axis
    ⟨(base axis).val + L, by omega⟩
  rw [xyBondRealBoundary_vertex_formula]
  simp only [Fin.sum_univ_succ]
  fin_cases axis
  · have hA := xyTubeSegmentBondCoeff_transA (axis := (0 : Fin 3)) base L finish
    have hB := xyTubeSegmentBondCoeff_transB (axis := (0 : Fin 3)) base L finish
    simp [xyAxisTransverseA, xyAxisTransverseB, finish] at hA hB
    simp [hA, hB, Function.update_self, xyAxisTransverseA,
      xyAxisTransverseB, xyTubeSiteOffset, hL]
    have hdiff : ((base (0 : Fin 3)).val : ℤ) + (L : ℤ) - 1 -
        (base (0 : Fin 3)).val = (L : ℤ) - 1 := by ring
    have hcond : ((base (0 : Fin 3)).val : ℤ) + (L : ℤ) - 1 -
        (base (0 : Fin 3)).val < (L : ℤ) := by rw [hdiff]; omega
    have hsumToNat := natCast_add_toNat (base (0 : Fin 3)).val L
    have hindex :
        (((((base (0 : Fin 3)).val : ℤ) + (L : ℤ)).toNat) - 1 -
          (base (0 : Fin 3)).val) = L - 1 := by
      rw [hsumToNat]
      omega
    simp [hcond, hindex]
    simp [uni]
  · have hA := xyTubeSegmentBondCoeff_transA (axis := (1 : Fin 3)) base L finish
    have hB := xyTubeSegmentBondCoeff_transB (axis := (1 : Fin 3)) base L finish
    simp [xyAxisTransverseA, xyAxisTransverseB, finish] at hA hB
    simp [hA, hB, Function.update_self, xyAxisTransverseA,
      xyAxisTransverseB, xyTubeSiteOffset, hL]
    have hdiff : ((base (1 : Fin 3)).val : ℤ) + (L : ℤ) - 1 -
        (base (1 : Fin 3)).val = (L : ℤ) - 1 := by ring
    have hcond : ((base (1 : Fin 3)).val : ℤ) + (L : ℤ) - 1 -
        (base (1 : Fin 3)).val < (L : ℤ) := by rw [hdiff]; omega
    have hsumToNat := natCast_add_toNat (base (1 : Fin 3)).val L
    have hindex :
        (((((base (1 : Fin 3)).val : ℤ) + (L : ℤ)).toNat) - 1 -
          (base (1 : Fin 3)).val) = L - 1 := by
      rw [hsumToNat]
      omega
    simp [hcond, hindex]
    simp [uni]
  · have hA := xyTubeSegmentBondCoeff_transA (axis := (2 : Fin 3)) base L finish
    have hB := xyTubeSegmentBondCoeff_transB (axis := (2 : Fin 3)) base L finish
    simp [xyAxisTransverseA, xyAxisTransverseB, finish] at hA hB
    simp [hA, hB, Function.update_self, xyAxisTransverseA,
      xyAxisTransverseB, xyTubeSiteOffset, hL]
    have hdiff : ((base (2 : Fin 3)).val : ℤ) + (L : ℤ) - 1 -
        (base (2 : Fin 3)).val = (L : ℤ) - 1 := by ring
    have hcond : ((base (2 : Fin 3)).val : ℤ) + (L : ℤ) - 1 -
        (base (2 : Fin 3)).val < (L : ℤ) := by rw [hdiff]; omega
    have hsumToNat := natCast_add_toNat (base (2 : Fin 3)).val L
    have hindex :
        (((((base (2 : Fin 3)).val : ℤ) + (L : ℤ)).toNat) - 1 -
          (base (2 : Fin 3)).val) = L - 1 := by
      rw [hsumToNat]
      omega
    simp [hcond, hindex]
    simp [uni]

private theorem xyTubeSegment_boundary_at_interior_faces {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ) (_hL : 0 < L)
    (hEnd : (base axis).val + L ≤ B axis)
    (hSideA : L ≤ B (xyAxisTransverseA axis))
    (hSideB : L ≤ B (xyAxisTransverseB axis))
    (v : (i : Fin 3) → Fin (B i + 1))
    (hBefore : (base axis).val < (v axis).val)
    (hAfter : (v axis).val < (base axis).val + L) :
    realBoundary (xyBondRealChain (xyTubeSegmentBondCoeff axis base L))
      (xyVertexCell v) = 0 := by
  classical
  let a := xyAxisTransverseA axis
  let b := xyAxisTransverseB axis
  have hAxisIn : 0 < (v axis).val := by omega
  have hAxisOut : (v axis).val < B axis := by omega
  let s : ℕ := (v axis).val - (base axis).val
  have hs0 : 0 < s := by dsimp [s]; omega
  have hsL : s < L := by dsimp [s]; omega
  have hSPos : 1 ≤ s := by omega
  have hdiff : ((v axis).val : ℤ) - (base axis).val = (s : ℤ) := by
    dsimp [s]
    omega
  have hInDiff : ((v axis).val : ℤ) - 1 - (base axis).val = (s : ℤ) - 1 := by
    dsimp [s]
    omega
  have hIncomingValid :
      0 ≤ (((v axis).val - 1 : ℕ) : ℤ) - (base axis).val ∧
        (((v axis).val - 1 : ℕ) : ℤ) - (base axis).val < L := by omega
  have hOutgoingValid :
      0 ≤ ((v axis).val : ℤ) - (base axis).val ∧
        ((v axis).val : ℤ) - (base axis).val < L := by omega
  have hAxialInIndex : (v axis).val - 1 - (base axis).val = s - 1 := by omega
  have hAxialOutIndex : (v axis).val - (base axis).val = s := by omega
  have hAxialInLe : (base axis).val ≤ (v axis).val - 1 := by omega
  have hAxialOutLe : (base axis).val ≤ (v axis).val := by omega
  fin_cases axis
  all_goals
    first
    | have ha : a = (Fin.succ 0 : Fin 3) := by norm_num [a, xyAxisTransverseA]
    | have ha : a = ((Fin.succ 0).succ : Fin 3) := by norm_num [a, xyAxisTransverseA]
    | have ha : a = (0 : Fin 3) := by norm_num [a, xyAxisTransverseA]
    first
    | have hb : b = ((Fin.succ 0).succ : Fin 3) := by norm_num [b, xyAxisTransverseB]
    | have hb : b = (0 : Fin 3) := by norm_num [b, xyAxisTransverseB]
    | have hb : b = (Fin.succ 0 : Fin 3) := by norm_num [b, xyAxisTransverseB]
    first
    | have hAxisInN : 0 < (v (0 : Fin 3)).val := by simpa using hAxisIn
    | have hAxisInN : 0 < (v (1 : Fin 3)).val := by simpa using hAxisIn
    | have hAxisInN : 0 < (v (2 : Fin 3)).val := by simpa using hAxisIn
    first
    | have hAxisOutN : (v (0 : Fin 3)).val < B 0 := by simpa using hAxisOut
    | have hAxisOutN : (v (1 : Fin 3)).val < B 1 := by simpa using hAxisOut
    | have hAxisOutN : (v (2 : Fin 3)).val < B 2 := by simpa using hAxisOut
    first
    | have hBeforeN : base (0 : Fin 3) < v 0 := by simpa using hBefore
    | have hBeforeN : base (1 : Fin 3) < v 1 := by simpa using hBefore
    | have hBeforeN : base (2 : Fin 3) < v 2 := by simpa using hBefore
    first
    | have hAfterN : (v (0 : Fin 3)).val < (base 0).val + L := by simpa using hAfter
    | have hAfterN : (v (1 : Fin 3)).val < (base 1).val + L := by simpa using hAfter
    | have hAfterN : (v (2 : Fin 3)).val < (base 2).val + L := by simpa using hAfter
    first
    | have hdiffN : ((v (0 : Fin 3)).val : ℤ) - (base 0).val = (s : ℤ) := by simpa using hdiff
    | have hdiffN : ((v (1 : Fin 3)).val : ℤ) - (base 1).val = (s : ℤ) := by simpa using hdiff
    | have hdiffN : ((v (2 : Fin 3)).val : ℤ) - (base 2).val = (s : ℤ) := by simpa using hdiff
    first
    | have hInDiffN : ((v (0 : Fin 3)).val : ℤ) - 1 - (base 0).val = (s : ℤ) - 1 := by simpa using hInDiff
    | have hInDiffN : ((v (1 : Fin 3)).val : ℤ) - 1 - (base 1).val = (s : ℤ) - 1 := by simpa using hInDiff
    | have hInDiffN : ((v (2 : Fin 3)).val : ℤ) - 1 - (base 2).val = (s : ℤ) - 1 := by simpa using hInDiff
    first
    | have hIncomingValidN : 0 ≤ (((((v (0 : Fin 3)).val - 1 : ℕ) : ℤ) - (base 0).val)) ∧ (((((v 0).val - 1 : ℕ) : ℤ) - (base 0).val)) < (L : ℤ) := by simpa using hIncomingValid
    | have hIncomingValidN : 0 ≤ (((((v (1 : Fin 3)).val - 1 : ℕ) : ℤ) - (base 1).val)) ∧ (((((v 1).val - 1 : ℕ) : ℤ) - (base 1).val)) < (L : ℤ) := by simpa using hIncomingValid
    | have hIncomingValidN : 0 ≤ (((((v (2 : Fin 3)).val - 1 : ℕ) : ℤ) - (base 2).val)) ∧ (((((v 2).val - 1 : ℕ) : ℤ) - (base 2).val)) < (L : ℤ) := by simpa using hIncomingValid
    first
    | have hOutgoingValidN : 0 ≤ ((v (0 : Fin 3)).val : ℤ) - (base 0).val ∧ ((v 0).val : ℤ) - (base 0).val < (L : ℤ) := by simpa using hOutgoingValid
    | have hOutgoingValidN : 0 ≤ ((v (1 : Fin 3)).val : ℤ) - (base 1).val ∧ ((v 1).val : ℤ) - (base 1).val < (L : ℤ) := by simpa using hOutgoingValid
    | have hOutgoingValidN : 0 ≤ ((v (2 : Fin 3)).val : ℤ) - (base 2).val ∧ ((v 2).val : ℤ) - (base 2).val < (L : ℤ) := by simpa using hOutgoingValid
    first
    | have hAxialInLeN : (base 0).val ≤ (v 0).val - 1 := by simpa using hAxialInLe
    | have hAxialInLeN : (base 1).val ≤ (v 1).val - 1 := by simpa using hAxialInLe
    | have hAxialInLeN : (base 2).val ≤ (v 2).val - 1 := by simpa using hAxialInLe
    first
    | have hAxialOutLeN : (base 0).val ≤ (v 0).val := by simpa using hAxialOutLe
    | have hAxialOutLeN : (base 1).val ≤ (v 1).val := by simpa using hAxialOutLe
    | have hAxialOutLeN : (base 2).val ≤ (v 2).val := by simpa using hAxialOutLe
    rw [xyBondRealBoundary_vertex_formula]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [← ha, ← hb] at ⊢
    dsimp [a, b] at ⊢
    simp only [xyTubeSegmentBondCoeff_axial, xyTubeSegmentBondCoeff_transA,
      xyTubeSegmentBondCoeff_transB] at ⊢
    have hR := xyTubeLayerRadii L s hs0 hsL
    rcases hR with hExpand | hMiddle | hContract
    · have hrad : 2 * ((s - 1) + 1) ≤ L := by omega
      have hleft : min (s - 1) (L - s) = s - 1 := by omega
      have hright : min s (L - 1 - s) = s := by omega
      have hcmp : min (s - 1) (L - s) < min s (L - 1 - s) := by omega
      have hfirst : s - 1 < L - 1 - s ∨ L - s < L - 1 - s := by omega
      have hsecond : ¬((s < s - 1 ∨ L - 1 - s < s) ∧
          (s < L - s ∨ L - 1 - s < L - s)) := by omega
      have hwidth1 : 2 * ((s - 1) + 1) ≤ B a := hrad.trans hSideA
      have hwidth2 : 2 * ((s - 1) + 1) ≤ B b := hrad.trans hSideB
      simp [-Fin.val_pos_iff, hAxisInN, hAxisOutN, hs0, hsL, hInDiffN, hdiffN,
        hIncomingValidN, hOutgoingValidN, hAxialInLeN, hAxialOutLeN,
        hBeforeN, hAfterN, hExpand, hleft, hright, hcmp, hfirst, hsecond]
      have hwidth1' : 2 * ((s - 1) + 1) ≤ B a := by omega
      have hwidth2' : 2 * ((s - 1) + 1) ≤ B b := by omega
      have hs1 : 1 ≤ s := by omega
      have hsl : s ≤ L := Nat.le_of_lt hsL
      have hdepthIn : min (s - 1) (L - 1 - (s - 1)) = s - 1 := by omega
      try simp [-Fin.val_pos_iff, hdepthIn, hs1, hsl]
      let y := xyTubeSiteOffset a (base a) (v a)
      let z := xyTubeSiteOffset b (base b) (v b)
      have hA := xyTubeOrientationSign_mul_profileBoundary
        a (base a) (v a) (s - 1)
        (fun w => levelThree (s - 1) w z)
        (by intro w hw; exact (levelThree_ne_zero hw).1) hwidth1'
      have hA' : (if h : 0 < (v a).val then
              xyTubeOrientationSign a (base a) *
                levelThree (s - 1) (xyTubeEdgeLevel a (base a)
                  ⟨(v a).val - 1, by omega⟩) z else 0) -
            (if h : (v a).val < B a then
              xyTubeOrientationSign a (base a) *
                levelThree (s - 1) (xyTubeEdgeLevel a (base a)
                  ⟨(v a).val, h⟩) z else 0) =
          levelThree (s - 1) y z - levelThree (s - 1) (y + 1) z := by
        by_cases hin : 0 < (v a).val <;> by_cases hout : (v a).val < B a <;>
          simpa [hin, hout, y, mul_sub] using hA
      have hB := xyTubeOrientationSign_mul_profileBoundary
        b (base b) (v b) (s - 1)
        (fun w => levelTwo (s - 1) y w)
        (by intro w hw; exact (levelTwo_ne_zero hw).2) hwidth2'
      have hBnorm : (if h : 0 < (v b).val then
              xyTubeOrientationSign b (base b) *
                levelTwo (s - 1) y (xyTubeEdgeLevel b (base b)
                  ⟨(v b).val - 1, by omega⟩) else 0) -
            (if h : (v b).val < B b then
              xyTubeOrientationSign b (base b) *
                levelTwo (s - 1) y (xyTubeEdgeLevel b (base b)
                  ⟨(v b).val, h⟩) else 0) =
          levelTwo (s - 1) y z - levelTwo (s - 1) y (z + 1) := by
        by_cases hin : 0 < (v b).val <;> by_cases hout : (v b).val < B b <;>
          simpa [hin, hout, y, z, mul_sub] using hB
      have hB' : (if h : 0 < (v b).val then
              -(xyTubeOrientationSign b (base b) *
                levelTwo (s - 1) y (xyTubeEdgeLevel b (base b)
                  ⟨(v b).val - 1, by omega⟩)) else 0) -
            (if h : (v b).val < B b then
              -(xyTubeOrientationSign b (base b) *
                levelTwo (s - 1) y (xyTubeEdgeLevel b (base b)
                  ⟨(v b).val, h⟩)) else 0) =
          levelTwo (s - 1) y (z + 1) - levelTwo (s - 1) y z := by
        have hneg := congrArg (fun r : ℝ => -r) hBnorm
        by_cases hin : 0 < (v b).val <;> by_cases hout : (v b).val < B b
        · simp [hin, hout] at hneg ⊢; linear_combination hneg
        · simp [hin, hout] at hneg ⊢; linear_combination hneg
        · simp [hin, hout] at hneg ⊢; linear_combination hneg
        · simp [hin, hout] at hneg ⊢; linear_combination hneg
      have hSucc : s - 1 + 1 = s := Nat.sub_add_cancel hs1
      have hcurl := xyTubeExpandingLayer_divergence (s - 1) y z
      simp [hSucc] at hcurl
      subst a
      subst b
      dsimp [y, z] at hA' hB' hcurl
      first
      | have haFix : xyAxisTransverseA (0 : Fin 3) = (Fin.succ 0 : Fin 3) := ha
      | have haFix : xyAxisTransverseA (1 : Fin 3) = ((Fin.succ 0).succ : Fin 3) := ha
      | have haFix : xyAxisTransverseA (2 : Fin 3) = (0 : Fin 3) := ha
      first
      | have hbFix : xyAxisTransverseB (0 : Fin 3) = ((Fin.succ 0).succ : Fin 3) := hb
      | have hbFix : xyAxisTransverseB (1 : Fin 3) = (0 : Fin 3) := hb
      | have hbFix : xyAxisTransverseB (2 : Fin 3) = (Fin.succ 0 : Fin 3) := hb
      cases haFix
      cases hbFix
      rw [hA', hB']
      simp [-Fin.val_pos_iff, xyAxisTransverseA, xyAxisTransverseB, hs1] at hcurl ⊢
      linear_combination hcurl
    ·
      have hs1 : 1 ≤ s := by omega
      have hsl : s ≤ L := Nat.le_of_lt hsL
      have hinner : L - 1 - (s - 1) = L - s := by omega
      have hinDepth : min (s - 1) (L - 1 - (s - 1)) = s - 1 := by
        rw [hinner]
        exact hMiddle.2.1
      subst a
      subst b
      first
      | have haFix : xyAxisTransverseA (0 : Fin 3) = (Fin.succ 0 : Fin 3) := ha
      | have haFix : xyAxisTransverseA (1 : Fin 3) = ((Fin.succ 0).succ : Fin 3) := ha
      | have haFix : xyAxisTransverseA (2 : Fin 3) = (0 : Fin 3) := ha
      first
      | have hbFix : xyAxisTransverseB (0 : Fin 3) = ((Fin.succ 0).succ : Fin 3) := hb
      | have hbFix : xyAxisTransverseB (1 : Fin 3) = (0 : Fin 3) := hb
      | have hbFix : xyAxisTransverseB (2 : Fin 3) = (Fin.succ 0 : Fin 3) := hb
      cases haFix
      cases hbFix
      simp [-Fin.val_pos_iff, hInDiffN, hdiffN, hinDepth, hs1, hsl,
        hAxialInIndex, hAxialOutIndex, hAxialInLeN,
        hAxialOutLeN, hAxisInN, hAxisOutN, hIncomingValidN, hOutgoingValidN,
        hMiddle, hinner, xyAxisTransverseA, xyAxisTransverseB]
      have hslt : s < L := by omega
      simp [hslt]
    · let d : ℕ := L - 1 - s
      have hrad : 2 * (d + 1) ≤ L := by dsimp [d]; omega
      have hleft : min (s - 1) (L - s) = d + 1 := by dsimp [d]; omega
      have hright : min s (L - 1 - s) = d := by dsimp [d]; omega
      have hcmp : min s (L - 1 - s) < min (s - 1) (L - s) := by
        rw [hleft, hright]
        omega
      have hno : ¬ min (s - 1) (L - s) < min s (L - 1 - s) := by omega
      have hfirstC : ¬(s - 1 < L - 1 - s ∨ L - s < L - 1 - s) := by omega
      have hsecondC : (s < s - 1 ∨ L - 1 - s < s) ∧
          (s < L - s ∨ L - 1 - s < L - s) := by omega
      have hwidth1 : 2 * (d + 1) ≤ B a := hrad.trans hSideA
      have hwidth2 : 2 * (d + 1) ≤ B b := hrad.trans hSideB
      have hdSucc : L - s = d + 1 := by dsimp [d]; omega
      have hLayer : L ≤ L - 1 - s + s + 1 := by omega
      have hs1 : 1 ≤ s := by omega
      have hsl : s ≤ L := Nat.le_of_lt hsL
      simp [-Fin.val_pos_iff, hAxisInN, hAxisOutN, hs0, hsL, hInDiffN, hdiffN,
        hIncomingValidN, hOutgoingValidN, hAxialInLeN, hAxialOutLeN,
        hBeforeN, hAfterN, hContract, d, hLayer, hsl, hleft, hright, hcmp,
        hno, hfirstC, hsecondC, hAxialInIndex, hAxialOutIndex, hAxialInLe,
        hAxialOutLe]
      have hdepthIn : min (s - 1) (L - 1 - (s - 1)) = d + 1 := by omega
      try simp [-Fin.val_pos_iff, hdepthIn, hdSucc, d, hsl]
      try simp [-Fin.val_pos_iff, hleft, hright, hcmp, hno, hAxialInIndex,
        hAxialOutIndex, hAxialInLe, hAxialOutLe] at ⊢
      let y := xyTubeSiteOffset a (base a) (v a)
      let z := xyTubeSiteOffset b (base b) (v b)
      have hA := xyTubeOrientationSign_mul_profileBoundary
        a (base a) (v a) d
        (fun w => levelThree d w z)
        (by intro w hw; exact (levelThree_ne_zero hw).1) hwidth1
      have hAnorm : (if h : 0 < (v a).val then
              xyTubeOrientationSign a (base a) *
                levelThree d (xyTubeEdgeLevel a (base a)
                  ⟨(v a).val - 1, by omega⟩) z else 0) -
            (if h : (v a).val < B a then
              xyTubeOrientationSign a (base a) *
                levelThree d (xyTubeEdgeLevel a (base a)
                  ⟨(v a).val, h⟩) z else 0) =
          levelThree d y z - levelThree d (y + 1) z := by
        by_cases hin : 0 < (v a).val <;> by_cases hout : (v a).val < B a <;>
          simpa [hin, hout, y, mul_sub] using hA
      have hAnormFin := hAnorm
      simp only [Fin.val_pos_iff] at hAnormFin
      have hA' : (if h : 0 < v a then
              -(xyTubeOrientationSign a (base a) *
                levelThree d (xyTubeEdgeLevel a (base a)
                  ⟨(v a).val - 1, by omega⟩) z) else 0) -
            (if h : (v a).val < B a then
              -(xyTubeOrientationSign a (base a) *
                levelThree d (xyTubeEdgeLevel a (base a)
                  ⟨(v a).val, h⟩) z) else 0) =
          levelThree d (y + 1) z - levelThree d y z := by
        have hneg := congrArg (fun r : ℝ => -r) hAnormFin
        by_cases hin : 0 < v a <;> by_cases hout : (v a).val < B a
        · simp [hin, hout] at hneg ⊢; linear_combination hneg
        · simp [hin, hout] at hneg ⊢; linear_combination hneg
        · simp [hin, hout] at hneg ⊢; linear_combination hneg
        · simp [hin, hout] at hneg ⊢; linear_combination hneg
      have hB := xyTubeOrientationSign_mul_profileBoundary
        b (base b) (v b) d
        (fun w => levelTwo d y w)
        (by intro w hw; exact (levelTwo_ne_zero hw).2) hwidth2
      have hBnorm : (if h : 0 < (v b).val then
              xyTubeOrientationSign b (base b) *
                levelTwo d y (xyTubeEdgeLevel b (base b)
                  ⟨(v b).val - 1, by omega⟩) else 0) -
            (if h : (v b).val < B b then
              xyTubeOrientationSign b (base b) *
                levelTwo d y (xyTubeEdgeLevel b (base b)
                  ⟨(v b).val, h⟩) else 0) =
          levelTwo d y z - levelTwo d y (z + 1) := by
        by_cases hin : 0 < (v b).val <;> by_cases hout : (v b).val < B b <;>
          simpa [hin, hout, y, z, mul_sub] using hB
      have hBnormFin := hBnorm
      simp only [Fin.val_pos_iff] at hBnormFin
      have hB' : (if h : 0 < v b then
              xyTubeOrientationSign b (base b) *
                levelTwo d y (xyTubeEdgeLevel b (base b)
                  ⟨(v b).val - 1, by omega⟩) else 0) -
            (if h : (v b).val < B b then
              xyTubeOrientationSign b (base b) *
                levelTwo d y (xyTubeEdgeLevel b (base b)
                  ⟨(v b).val, h⟩) else 0) =
          levelTwo d y z - levelTwo d y (z + 1) := by
        simpa [y, z] using hBnormFin
      have hdepthAux : L - 1 - s + 1 = d + 1 := by dsimp [d]
      have hcond : 1 ≤ s ∧ s ≤ L := ⟨hs1, hsl⟩
      have hcurl := xyTubeContractingLayer_divergence d y z
      try simp only [ite_eq_left hcond, hdepthAux]
      try simp [hLayer] at ⊢
      subst a
      subst b
      dsimp [d, y, z] at hA' hB' hcurl
      rw [hdepthAux] at hcurl
      first
      | have haFix : xyAxisTransverseA (0 : Fin 3) = (Fin.succ 0 : Fin 3) := ha
      | have haFix : xyAxisTransverseA (1 : Fin 3) = ((Fin.succ 0).succ : Fin 3) := ha
      | have haFix : xyAxisTransverseA (2 : Fin 3) = (0 : Fin 3) := ha
      first
      | have hbFix : xyAxisTransverseB (0 : Fin 3) = ((Fin.succ 0).succ : Fin 3) := hb
      | have hbFix : xyAxisTransverseB (1 : Fin 3) = (0 : Fin 3) := hb
      | have hbFix : xyAxisTransverseB (2 : Fin 3) = (Fin.succ 0 : Fin 3) := hb
      cases haFix
      cases hbFix
      rw [hA', hB']
      simp [-Fin.val_pos_iff, xyAxisTransverseA, xyAxisTransverseB, hs1] at hcurl ⊢
      linear_combination hcurl


private noncomputable def xyTubeSegmentBase {B : Dual3Box}
    (x y : XYSites B) (axis : Fin 3) : (i : Fin 3) → Fin (B i + 1) :=
  fun i =>
    if i = axis then min (xySiteVertexIndex x i) (xySiteVertexIndex y i)
    else if i < axis then xySiteVertexIndex y i else xySiteVertexIndex x i

private noncomputable def xyTubeSegmentLength {B : Dual3Box}
    (x y : XYSites B) (axis : Fin 3) : ℕ :=
  if (xySiteVertexIndex x axis).val ≤ (xySiteVertexIndex y axis).val then
    (xySiteVertexIndex y axis).val - (xySiteVertexIndex x axis).val
  else (xySiteVertexIndex x axis).val - (xySiteVertexIndex y axis).val

private noncomputable def xyTubeSegmentSign {B : Dual3Box}
    (x y : XYSites B) (axis : Fin 3) : ℝ :=
  if (xySiteVertexIndex x axis).val ≤ (xySiteVertexIndex y axis).val then -1 else 1

private noncomputable def xyEndpointTubeBondField {B : Dual3Box}
    (x y : XYSites B) : XYBonds B → ℝ := fun b =>
  ∑ axis : Fin 3,
    xyTubeSegmentSign x y axis *
      xyTubeSegmentBondCoeff axis (xyTubeSegmentBase x y axis)
        (xyTubeSegmentLength x y axis) b

private noncomputable def xyEndpointTubeCurrent {B : Dual3Box}
    (x y : XYSites B) : RealChain 3 B :=
  xyBondRealChain (xyEndpointTubeBondField x y)

/-! ### Reindexing bonds by their coordinate edge and transverse vertex -/

private abbrev XYBondParameters (B : Dual3Box) :=
  Σ i : Fin 3, Fin (B i) ×
    {v : (j : Fin 3) → Fin (B j + 1) // v i = 0}

private def xyBondParameterToBond {B : Dual3Box} (p : XYBondParameters B) :
    XYBonds B :=
  xyBondFromVertexEdge p.2.2.1 p.1 p.2.1

private noncomputable def xyBondToParameter {B : Dual3Box} (b : XYBonds B) :
    XYBondParameters B := by
  classical
  let i := xyBondAxis b
  let e := xyBondAxisEdge b
  let v : (j : Fin 3) → Fin (B j + 1) := fun j =>
    if h : j = i then 0 else Sum.elim id (fun _ => 0) (b.1 j)
  exact ⟨i, e, ⟨v, by simp [v]⟩⟩

private theorem xyBondParameterToBond_toParameter {B : Dual3Box} (b : XYBonds B) :
    xyBondParameterToBond (xyBondToParameter b) = b := by
  classical
  let i := xyBondAxis b
  let e := xyBondAxisEdge b
  let v : (j : Fin 3) → Fin (B j + 1) := fun j =>
    if h : j = i then 0 else Sum.elim id (fun _ => 0) (b.1 j)
  have hparam : xyBondToParameter b = ⟨i, e, ⟨v, by simp [v]⟩⟩ := by
    rfl
  rw [hparam]
  apply Subtype.ext
  funext j
  change (edgeCell (xyVertexCell v) i e) j = b.1 j
  by_cases hj : j = i
  · subst j
    have he : b.1 i = Sum.inr e := by simpa [i, e] using xyBondAxisEdge_spec b
    rw [he]
    simp [edgeCell]
  · cases hcoord : b.1 j with
    | inl u =>
        have hv : v j = u := by
          simp [v, hj, hcoord]
        simp [edgeCell, xyVertexCell, Function.update_of_ne hj, hv]
    | inr e =>
        have hnot := xyBondAxis_other_isVertex b (by simpa [i] using hj)
        exact False.elim (hnot (by simp [coordIsEdge, hcoord]))

private noncomputable def xyBondParameterEquiv {B : Dual3Box} :
    XYBondParameters B ≃ XYBonds B :=
  Equiv.ofBijective xyBondParameterToBond (by
    constructor
    · intro p q hpq
      classical
      rcases p with ⟨i, e, v⟩
      rcases q with ⟨j, e', w⟩
      have hij : i = j := by
        have h := congrArg xyBondAxis hpq
        simpa [xyBondParameterToBond, xyBondFromVertexEdge_axis] using h
      subst j
      have hcell := congrArg (fun b : XYBonds B => b.1) hpq
      have he : e = e' := by
        have h := congrFun hcell i
        simp [xyBondParameterToBond, xyBondFromVertexEdge, edgeCell] at h
        exact h
      have hv : v.1 = w.1 := by
        funext k
        by_cases hki : k = i
        · subst k
          exact v.2.trans w.2.symm
        · have h := congrFun hcell k
          simp [xyBondParameterToBond, xyBondFromVertexEdge, edgeCell, hki] at h
          exact Sum.inl.inj h
      apply Sigma.ext
      · rfl
      · subst e'
        have hv' : v = w := Subtype.ext hv
        cases hv'
        rfl
    · intro b
      refine ⟨xyBondToParameter b, ?_⟩
      exact xyBondParameterToBond_toParameter b)

private noncomputable def xyTubeTransverseVertexEquiv {B : Dual3Box}
    (i : Fin 3) :
    {v : (j : Fin 3) → Fin (B j + 1) // v i = 0} ≃
      Fin (B (xyAxisTransverseA i) + 1) ×
        Fin (B (xyAxisTransverseB i) + 1) where
  toFun v := (v.1 (xyAxisTransverseA i), v.1 (xyAxisTransverseB i))
  invFun p := ⟨Function.update
    (Function.update (fun j : Fin 3 => (0 : Fin (B j + 1)))
      (xyAxisTransverseA i) p.1) (xyAxisTransverseB i) p.2, by
        simp [xyAxis_ne_transverseA, xyAxis_ne_transverseB]⟩
  left_inv := by
    intro v
    apply Subtype.ext
    funext j
    fin_cases i <;> fin_cases j <;>
      simp [xyAxisTransverseA, xyAxisTransverseB, Function.update_of_ne]
    all_goals simpa using v.2.symm
  right_inv := by
    intro p
    rcases p with ⟨u, v⟩
    simp [Function.update_of_ne, xyAxisTransverseA_ne, xyAxisTransverseB_ne,
      xyAxisTransverseAB_ne]

private noncomputable def xyTubeTransAVertexEquiv {B : Dual3Box}
    (axis : Fin 3) :
    {v : (j : Fin 3) → Fin (B j + 1) // v (xyAxisTransverseA axis) = 0} ≃
      Fin (B axis + 1) × Fin (B (xyAxisTransverseB axis) + 1) where
  toFun v := (v.1 axis, v.1 (xyAxisTransverseB axis))
  invFun p := ⟨Function.update
    (Function.update (fun j : Fin 3 => (0 : Fin (B j + 1)))
      axis p.1) (xyAxisTransverseB axis) p.2, by
        simp [xyAxisTransverseA_ne, xyAxisTransverseAB_ne]⟩
  left_inv := by
    intro v
    apply Subtype.ext
    funext j
    fin_cases axis <;> fin_cases j <;>
      simp [xyAxisTransverseA, xyAxisTransverseB, Function.update_of_ne]
    all_goals convert v.2.symm <;> rfl
  right_inv := by
    intro p
    rcases p with ⟨u, v⟩
    apply Prod.ext
    · change Function.update
        (Function.update (fun j : Fin 3 => (0 : Fin (B j + 1))) axis u)
        (xyAxisTransverseB axis) v axis = u
      rw [Function.update_of_ne (xyAxisTransverseB_ne axis).symm]
      simp [Function.update_self]
    · change Function.update
        (Function.update (fun j : Fin 3 => (0 : Fin (B j + 1))) axis u)
        (xyAxisTransverseB axis) v (xyAxisTransverseB axis) = v
      simp [Function.update_self]

private noncomputable def xyTubeTransBVertexEquiv {B : Dual3Box}
    (axis : Fin 3) :
    {v : (j : Fin 3) → Fin (B j + 1) // v (xyAxisTransverseB axis) = 0} ≃
      Fin (B axis + 1) × Fin (B (xyAxisTransverseA axis) + 1) where
  toFun v := (v.1 axis, v.1 (xyAxisTransverseA axis))
  invFun p := ⟨Function.update
    (Function.update (fun j : Fin 3 => (0 : Fin (B j + 1)))
      axis p.1) (xyAxisTransverseA axis) p.2, by
        rw [Function.update_of_ne (xyAxisTransverseBA_ne axis)]
        rw [Function.update_of_ne (xyAxisTransverseB_ne axis)]⟩
  left_inv := by
    intro v
    apply Subtype.ext
    funext j
    fin_cases axis <;> fin_cases j <;>
      simp [xyAxisTransverseA, xyAxisTransverseB, Function.update_of_ne]
    all_goals convert v.2.symm <;> rfl
  right_inv := by
    intro p
    rcases p with ⟨u, v⟩
    apply Prod.ext
    · change Function.update
        (Function.update (fun j : Fin 3 => (0 : Fin (B j + 1))) axis u)
        (xyAxisTransverseA axis) v axis = u
      rw [Function.update_of_ne (xyAxisTransverseA_ne axis).symm]
      simp [Function.update_self]
    · change Function.update
        (Function.update (fun j : Fin 3 => (0 : Fin (B j + 1))) axis u)
        (xyAxisTransverseA axis) v (xyAxisTransverseA axis) = v
      simp [Function.update_self]

private noncomputable def xyTubeVertexOffsets {B : Dual3Box}
    (i : Fin 3) (base : Fin (B i + 1)) : Finset ℤ :=
  Finset.univ.image (xyTubeSiteOffset i base)

private noncomputable def xyTubeEdgeLevels {B : Dual3Box}
    (i : Fin 3) (base : Fin (B i + 1)) : Finset ℤ :=
  Finset.univ.image (xyTubeEdgeLevel i base)

private theorem xyTubeSiteOffset_injective {B : Dual3Box}
    (i : Fin 3) (base : Fin (B i + 1)) :
    Function.Injective (xyTubeSiteOffset i base) := by
  intro u v huv
  apply Fin.ext
  by_cases h : 2 * base.val ≤ B i
  · have h' : (u.val : ℤ) - base.val = (v.val : ℤ) - base.val := by
      simpa [xyTubeSiteOffset, h] using huv
    omega
  · have h' : (base.val : ℤ) - u.val = (base.val : ℤ) - v.val := by
      simpa [xyTubeSiteOffset, h] using huv
    omega

private theorem xyTubeEdgeLevel_injective {B : Dual3Box}
    (i : Fin 3) (base : Fin (B i + 1)) :
    Function.Injective (xyTubeEdgeLevel i base) := by
  intro u v huv
  apply Fin.ext
  by_cases h : 2 * base.val ≤ B i
  · have h' : (u.val : ℤ) - base.val + 1 =
        (v.val : ℤ) - base.val + 1 := by
      simpa [xyTubeEdgeLevel, h] using huv
    omega
  · have h' : (base.val : ℤ) - u.val = (base.val : ℤ) - v.val := by
      simpa [xyTubeEdgeLevel, h] using huv
    omega

private theorem xyTube_sum_vertexOffset {B : Dual3Box}
    (i : Fin 3) (base : Fin (B i + 1)) (f : ℤ → ℝ) :
    ∑ u : Fin (B i + 1), f (xyTubeSiteOffset i base u) =
      ∑ z ∈ xyTubeVertexOffsets i base, f z := by
  classical
  unfold xyTubeVertexOffsets
  have hinj : Set.InjOn (xyTubeSiteOffset i base)
      (↑(Finset.univ : Finset (Fin (B i + 1))) : Set (Fin (B i + 1))) := by
    intro u hu v hv huv
    exact xyTubeSiteOffset_injective i base huv
  simpa using (Finset.sum_image (f := f) (s := Finset.univ)
    (g := xyTubeSiteOffset i base) hinj).symm

private theorem xyTube_sum_edgeLevel {B : Dual3Box}
    (i : Fin 3) (base : Fin (B i + 1)) (f : ℤ → ℝ) :
    ∑ e : Fin (B i), f (xyTubeEdgeLevel i base e) =
      ∑ z ∈ xyTubeEdgeLevels i base, f z := by
  classical
  unfold xyTubeEdgeLevels
  have hinj : Set.InjOn (xyTubeEdgeLevel i base)
      (↑(Finset.univ : Finset (Fin (B i))) : Set (Fin (B i))) := by
    intro u hu v hv huv
    exact xyTubeEdgeLevel_injective i base huv
  simpa using (Finset.sum_image (f := f) (s := Finset.univ)
    (g := xyTubeEdgeLevel i base) hinj).symm

private theorem xyTube_sum_vertexPair {B : Dual3Box}
    (i j : Fin 3) (bi : Fin (B i + 1)) (bj : Fin (B j + 1))
    (f : ℤ → ℤ → ℝ) :
    (∑ u : Fin (B i + 1), ∑ v : Fin (B j + 1),
        f (xyTubeSiteOffset i bi u) (xyTubeSiteOffset j bj v)) =
      ∑ z ∈ xyTubeVertexOffsets i bi,
        ∑ w ∈ xyTubeVertexOffsets j bj, f z w := by
  rw [xyTube_sum_vertexOffset i bi (fun z =>
    ∑ v : Fin (B j + 1), f z (xyTubeSiteOffset j bj v))]
  refine Finset.sum_congr rfl ?_
  intro z hz
  exact xyTube_sum_vertexOffset j bj (f z)

private theorem xyTube_sum_edgeVertex {B : Dual3Box}
    (i j : Fin 3) (bi : Fin (B i + 1)) (bj : Fin (B j + 1))
    (f : ℤ → ℤ → ℝ) :
    (∑ e : Fin (B i), ∑ v : Fin (B j + 1),
        f (xyTubeEdgeLevel i bi e) (xyTubeSiteOffset j bj v)) =
      ∑ z ∈ xyTubeEdgeLevels i bi,
        ∑ w ∈ xyTubeVertexOffsets j bj, f z w := by
  rw [xyTube_sum_edgeLevel i bi (fun z =>
    ∑ v : Fin (B j + 1), f z (xyTubeSiteOffset j bj v))]
  refine Finset.sum_congr rfl ?_
  intro z hz
  exact xyTube_sum_vertexOffset j bj (f z)

private theorem xyTube_sum_vertexEdge {B : Dual3Box}
    (i j : Fin 3) (bi : Fin (B i + 1)) (bj : Fin (B j + 1))
    (f : ℤ → ℤ → ℝ) :
    (∑ u : Fin (B i + 1), ∑ e : Fin (B j),
        f (xyTubeSiteOffset i bi u) (xyTubeEdgeLevel j bj e)) =
      ∑ z ∈ xyTubeVertexOffsets i bi,
        ∑ w ∈ xyTubeEdgeLevels j bj, f z w := by
  rw [xyTube_sum_vertexOffset i bi (fun z =>
    ∑ e : Fin (B j), f z (xyTubeEdgeLevel j bj e))]
  refine Finset.sum_congr rfl ?_
  intro z hz
  exact xyTube_sum_edgeLevel j bj (f z)

private theorem xyBond_squareSum_reindex {B : Dual3Box}
    (f : XYBonds B → ℝ) :
    ∑ b : XYBonds B, (f b) ^ 2 =
      ∑ i : Fin 3, ∑ e : Fin (B i),
        ∑ v : {v : (j : Fin 3) → Fin (B j + 1) // v i = 0},
          (f (xyBondFromVertexEdge v.1 i e)) ^ 2 := by
  classical
  rw [← Equiv.sum_comp xyBondParameterEquiv (fun b => (f b) ^ 2)]
  dsimp [xyBondParameterEquiv, Equiv.ofBijective]
  simp only [XYBondParameters, Fintype.sum_sigma, Fintype.sum_prod_type,
    xyBondParameterToBond]

private theorem xyTube_sum_transverseVertex {B : Dual3Box}
    (i : Fin 3)
    (f : {v : (j : Fin 3) → Fin (B j + 1) // v i = 0} → ℝ) :
    (∑ v : {v : (j : Fin 3) → Fin (B j + 1) // v i = 0}, f v) =
      ∑ p : Fin (B (xyAxisTransverseA i) + 1) ×
          Fin (B (xyAxisTransverseB i) + 1),
        f ((xyTubeTransverseVertexEquiv i).symm p) := by
  exact (Equiv.sum_comp (xyTubeTransverseVertexEquiv i).symm f).symm

private theorem xyTube_sum_transAVertex {B : Dual3Box}
    (axis : Fin 3)
    (f : {v : (j : Fin 3) → Fin (B j + 1) //
      v (xyAxisTransverseA axis) = 0} → ℝ) :
    (∑ v : {v : (j : Fin 3) → Fin (B j + 1) //
        v (xyAxisTransverseA axis) = 0}, f v) =
      ∑ p : Fin (B axis + 1) ×
          Fin (B (xyAxisTransverseB axis) + 1),
        f ((xyTubeTransAVertexEquiv axis).symm p) := by
  exact (Equiv.sum_comp (xyTubeTransAVertexEquiv axis).symm f).symm

private theorem xyTube_sum_transBVertex {B : Dual3Box}
    (axis : Fin 3)
    (f : {v : (j : Fin 3) → Fin (B j + 1) //
      v (xyAxisTransverseB axis) = 0} → ℝ) :
    (∑ v : {v : (j : Fin 3) → Fin (B j + 1) //
        v (xyAxisTransverseB axis) = 0}, f v) =
      ∑ p : Fin (B axis + 1) ×
          Fin (B (xyAxisTransverseA axis) + 1),
        f ((xyTubeTransBVertexEquiv axis).symm p) := by
  exact (Equiv.sum_comp (xyTubeTransBVertexEquiv axis).symm f).symm

private theorem xyTube_axialDepth_sum {n b L : ℕ} (hEnd : b + L ≤ n)
    (f : ℕ → ℝ) :
    (∑ e : Fin n, if b ≤ e.val ∧ e.val < b + L then
      f (min (e.val - b) (L - 1 - (e.val - b))) else 0) =
      ∑ s ∈ Finset.range L, f (min s (L - 1 - s)) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun e _ => e.val - b)
  · intro e he
    simp only [Finset.mem_univ, true_and, Finset.mem_filter] at he
    simp only [Finset.mem_range]
    omega
  · intro e he e' he' hEq
    simp only [Finset.mem_univ, true_and, Finset.mem_filter] at he he'
    omega
  · intro s hs
    simp only [Finset.mem_range] at hs
    refine ⟨⟨b + s, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_univ, true_and, Finset.mem_filter]
      omega
    · simp
  · intro e he
    simp only [Finset.mem_univ, true_and, Finset.mem_filter] at he
    rfl

private theorem xyTube_interiorDepth_sum {n b L : ℕ} (hEnd : b + L ≤ n)
    (f : ℕ → ℝ) :
    (∑ k : Fin (n + 1), if b < k.val ∧ k.val < b + L then
      f (min (k.val - b - 1) (L - 1 - (k.val - b))) else 0) =
      ∑ s ∈ Finset.range (L - 1), f (min s (L - 2 - s)) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ => k.val - b - 1)
  · intro k hk
    simp only [Finset.mem_univ, true_and, Finset.mem_filter] at hk
    simp only [Finset.mem_range]
    omega
  · intro k hk k' hk' hEq
    simp only [Finset.mem_univ, true_and, Finset.mem_filter] at hk hk'
    omega
  · intro s hs
    simp only [Finset.mem_range] at hs
    refine ⟨⟨b + s + 1, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_univ, true_and, Finset.mem_filter]
      change b < b + s + 1 ∧ b + s + 1 < b + L
      omega
    · change b + s + 1 - b - 1 = s
      omega
  · intro k hk
    simp only [Finset.mem_univ, true_and, Finset.mem_filter] at hk
    apply congrArg f
    exact congrArg₂ min rfl (by omega)

private theorem xyTube_axialLayer_energy_le {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (e : Fin (B axis)) (hLayer : (base axis).val ≤ e.val ∧
      e.val < (base axis).val + L) :
    ∑ p : Fin (B (xyAxisTransverseA axis) + 1) ×
        Fin (B (xyAxisTransverseB axis) + 1),
      (xyTubeSegmentBondCoeff axis base L
        (xyBondFromVertexEdge
          ((xyTubeTransverseVertexEquiv axis).symm p).1 axis e)) ^ 2 ≤
      1 / (((min (e.val - (base axis).val)
        (L - 1 - (e.val - (base axis).val)) : ℕ) : ℝ) + 1) ^ 2 := by
  classical
  let a := xyAxisTransverseA axis
  let b := xyAxisTransverseB axis
  let u := e.val - (base axis).val
  let d := min u (L - 1 - u)
  have hu : (e.val : ℤ) - (base axis).val = (u : ℤ) := by
    dsimp [u]
    omega
  have htoNat : ((e.val : ℤ) - (base axis).val).toNat = u := by
    rw [hu]
    simp [u]
  have hprofile : 0 ≤ (e.val : ℤ) - (base axis).val ∧
      (e.val : ℤ) - (base axis).val < (L : ℤ) := by
    constructor <;> rw [hu] <;> push_cast <;> omega
  have hsum :
      (∑ p : Fin (B a + 1) × Fin (B b + 1),
        (uni d (xyTubeSiteOffset a (base a) p.1) *
          uni d (xyTubeSiteOffset b (base b) p.2)) ^ 2) =
        ∑ z ∈ xyTubeVertexOffsets a (base a),
          ∑ w ∈ xyTubeVertexOffsets b (base b), (uni d z * uni d w) ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact xyTube_sum_vertexPair a b (base a) (base b)
      (fun z w => (uni d z * uni d w) ^ 2)
  calc
    _ = ∑ p : Fin (B a + 1) × Fin (B b + 1),
        (uni d (xyTubeSiteOffset a (base a) p.1) *
          uni d (xyTubeSiteOffset b (base b) p.2)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [xyTubeSegmentBondCoeff_axial]
          have hcoords := (xyTubeTransverseVertexEquiv axis).apply_symm_apply p
          have ha : ((xyTubeTransverseVertexEquiv axis).symm p).1 a = p.1 := by
            exact congrArg Prod.fst hcoords
          have hb : ((xyTubeTransverseVertexEquiv axis).symm p).1 b = p.2 := by
            exact congrArg Prod.snd hcoords
          split_ifs
          all_goals simp [htoNat, ha, hb, a, b, u, d]
    _ = ∑ z ∈ xyTubeVertexOffsets a (base a),
        ∑ w ∈ xyTubeVertexOffsets b (base b), (uni d z * uni d w) ^ 2 := hsum
    _ ≤ 1 / ((d : ℝ) + 1) ^ 2 := sum_spread_sq_le d
      (xyTubeVertexOffsets a (base a)) (xyTubeVertexOffsets b (base b))
    _ = 1 / (((min (e.val - (base axis).val)
        (L - 1 - (e.val - (base axis).val)) : ℕ) : ℝ) + 1) ^ 2 := by
          simp [d, u]

private theorem xyTube_axialEnergy_le {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (hEnd : (base axis).val + L ≤ B axis) :
    ∑ e : Fin (B axis),
      ∑ p : Fin (B (xyAxisTransverseA axis) + 1) ×
          Fin (B (xyAxisTransverseB axis) + 1),
        (xyTubeSegmentBondCoeff axis base L
          (xyBondFromVertexEdge
            ((xyTubeTransverseVertexEquiv axis).symm p).1 axis e)) ^ 2 ≤ 4 := by
  classical
  let b := (base axis).val
  have hLayer (e : Fin (B axis)) :
      (∑ p : Fin (B (xyAxisTransverseA axis) + 1) ×
          Fin (B (xyAxisTransverseB axis) + 1),
        (xyTubeSegmentBondCoeff axis base L
          (xyBondFromVertexEdge
            ((xyTubeTransverseVertexEquiv axis).symm p).1 axis e)) ^ 2) ≤
        if b ≤ e.val ∧ e.val < b + L then
          1 / (((min (e.val - b) (L - 1 - (e.val - b)) : ℕ) : ℝ) + 1) ^ 2
        else 0 := by
    by_cases h : b ≤ e.val ∧ e.val < b + L
    · rw [ite_eq_left h]
      exact xyTube_axialLayer_energy_le axis base L e (by simpa [b] using h)
    · rw [ite_eq_right h]
      have hprofile : ¬((base axis).val ≤ e.val ∧
          (e.val : ℤ) - (base axis).val < (L : ℤ)) := by
        intro hp
        exact h (by push_cast at hp; omega)
      simp [xyTubeSegmentBondCoeff_axial, hprofile]
  calc
    _ ≤ ∑ e : Fin (B axis), if b ≤ e.val ∧ e.val < b + L then
          1 / (((min (e.val - b) (L - 1 - (e.val - b)) : ℕ) : ℝ) + 1) ^ 2
        else 0 := Finset.sum_le_sum fun e he => hLayer e
    _ = ∑ s ∈ Finset.range L,
          1 / (((min s (L - 1 - s) : ℕ) : ℝ) + 1) ^ 2 := by
          simpa only [b] using xyTube_axialDepth_sum (n := B axis)
            (b := (base axis).val) (L := L) hEnd
            (fun d => 1 / ((d : ℝ) + 1) ^ 2)
    _ ≤ 4 := by
          by_cases hL : L = 0
          · simp [hL]
          · have hsub : L - 1 + 1 = L := Nat.sub_add_cancel (by omega)
            simpa [hsub] using tent_sum_le (L - 1)

private theorem xyTubeSegmentBondCoeff_transA_sq_le {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (v : (i : Fin 3) → Fin (B i + 1))
    (e : Fin (B (xyAxisTransverseA axis)))
    (hBefore : (base axis).val < (v axis).val)
    (hAfter : (v axis).val < (base axis).val + L) :
    (xyTubeSegmentBondCoeff axis base L
      (xyBondFromVertexEdge v (xyAxisTransverseA axis) e)) ^ 2 ≤
      (levelThree (min ((v axis).val - (base axis).val - 1)
          (L - 1 - ((v axis).val - (base axis).val)))
        (xyTubeEdgeLevel (xyAxisTransverseA axis)
          (base (xyAxisTransverseA axis)) e)
        (xyTubeSiteOffset (xyAxisTransverseB axis)
          (base (xyAxisTransverseB axis))
          (v (xyAxisTransverseB axis)))) ^ 2 := by
  classical
  let s := (v axis).val - (base axis).val
  let d := min (s - 1) (L - 1 - s)
  have hdiff : (v axis).val - (base axis).val = s := by rfl
  have htoNat : (((v axis).val : ℤ) - (base axis).val).toNat = s := by
    have hcast : ((v axis).val : ℤ) - (base axis).val = (s : ℤ) := by
      dsimp [s]
      omega
    rw [hcast]
    simp [s]
  have hvalid : 0 < (v axis).val - (base axis).val ∧
      (v axis).val - (base axis).val < L := by
    omega
  have hvalidInt : 0 < ((v axis).val : ℤ) - (base axis).val ∧
      ((v axis).val : ℤ) - (base axis).val < (L : ℤ) := by
    have hcast : ((v axis).val : ℤ) - (base axis).val = (s : ℤ) := by
      dsimp [s]
      omega
    rw [hcast]
    push_cast
    exact_mod_cast hvalid
  have hradius :
      min (min (s - 1) (L - s)) (min s (L - 1 - s)) = d := by
    dsimp [d]
    omega
  simp [xyTubeSegmentBondCoeff_transA, hvalidInt, htoNat, hradius,
    s, d, xyTubeOrientationSign]
  split_ifs <;> first | rfl | positivity

private theorem xyTubeSegmentBondCoeff_transB_sq_le {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (v : (i : Fin 3) → Fin (B i + 1))
    (e : Fin (B (xyAxisTransverseB axis)))
    (hBefore : (base axis).val < (v axis).val)
    (hAfter : (v axis).val < (base axis).val + L) :
    (xyTubeSegmentBondCoeff axis base L
      (xyBondFromVertexEdge v (xyAxisTransverseB axis) e)) ^ 2 ≤
      (levelTwo (min ((v axis).val - (base axis).val - 1)
          (L - 1 - ((v axis).val - (base axis).val)))
        (xyTubeSiteOffset (xyAxisTransverseA axis)
          (base (xyAxisTransverseA axis))
          (v (xyAxisTransverseA axis)))
        (xyTubeEdgeLevel (xyAxisTransverseB axis)
          (base (xyAxisTransverseB axis)) e)) ^ 2 := by
  classical
  let s := (v axis).val - (base axis).val
  let d := min (s - 1) (L - 1 - s)
  have htoNat : (((v axis).val : ℤ) - (base axis).val).toNat = s := by
    have hcast : ((v axis).val : ℤ) - (base axis).val = (s : ℤ) := by
      dsimp [s]
      omega
    rw [hcast]
    simp [s]
  have hvalid : 0 < (v axis).val - (base axis).val ∧
      (v axis).val - (base axis).val < L := by
    omega
  have hvalidInt : 0 < ((v axis).val : ℤ) - (base axis).val ∧
      ((v axis).val : ℤ) - (base axis).val < (L : ℤ) := by
    have hcast : ((v axis).val : ℤ) - (base axis).val = (s : ℤ) := by
      dsimp [s]
      omega
    rw [hcast]
    exact_mod_cast hvalid
  have hradius :
      min (min (s - 1) (L - s)) (min s (L - 1 - s)) = d := by
    dsimp [d]
    omega
  simp [xyTubeSegmentBondCoeff_transB, hvalidInt, htoNat, hradius,
    s, d, xyTubeOrientationSign]
  split_ifs <;> first | rfl | positivity

private theorem xyTube_transALayer_energy_le {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (k : Fin (B axis + 1))
    (hBefore : (base axis).val < k.val)
    (hAfter : k.val < (base axis).val + L) :
    ∑ e : Fin (B (xyAxisTransverseA axis)),
      ∑ w : Fin (B (xyAxisTransverseB axis) + 1),
        (xyTubeSegmentBondCoeff axis base L
          (xyBondFromVertexEdge
            ((xyTubeTransAVertexEquiv axis).symm (k, w)).1
            (xyAxisTransverseA axis) e)) ^ 2 ≤
      levelBound (min (k.val - (base axis).val - 1)
        (L - 1 - (k.val - (base axis).val))) := by
  classical
  let a := xyAxisTransverseA axis
  let b := xyAxisTransverseB axis
  let d := min (k.val - (base axis).val - 1)
    (L - 1 - (k.val - (base axis).val))
  have hpoint (e : Fin (B a)) (w : Fin (B b + 1)) :
      (xyTubeSegmentBondCoeff axis base L
        (xyBondFromVertexEdge
          ((xyTubeTransAVertexEquiv axis).symm (k, w)).1 a e)) ^ 2 ≤
        (levelThree d (xyTubeEdgeLevel a (base a) e)
          (xyTubeSiteOffset b (base b) w)) ^ 2 := by
    have hcoords := (xyTubeTransAVertexEquiv axis).apply_symm_apply (k, w)
    have haxis : ((xyTubeTransAVertexEquiv axis).symm (k, w)).1 axis = k :=
      congrArg Prod.fst hcoords
    have hb : ((xyTubeTransAVertexEquiv axis).symm (k, w)).1 b = w :=
      congrArg Prod.snd hcoords
    have hBefore' : (base axis).val <
        (((xyTubeTransAVertexEquiv axis).symm (k, w)).1 axis).val := by
      simpa [haxis] using hBefore
    have hAfter' :
        (((xyTubeTransAVertexEquiv axis).symm (k, w)).1 axis).val <
          (base axis).val + L := by
      simpa [haxis] using hAfter
    have h := xyTubeSegmentBondCoeff_transA_sq_le axis base L
      ((xyTubeTransAVertexEquiv axis).symm (k, w)).1 e
      hBefore' hAfter'
    simpa [a, b, d, haxis, hb] using h
  calc
    _ ≤ ∑ e : Fin (B a), ∑ w : Fin (B b + 1),
        (levelThree d (xyTubeEdgeLevel a (base a) e)
          (xyTubeSiteOffset b (base b) w)) ^ 2 :=
      Finset.sum_le_sum fun e he => Finset.sum_le_sum fun w hw => hpoint e w
    _ = ∑ z ∈ xyTubeEdgeLevels a (base a),
        ∑ q ∈ xyTubeVertexOffsets b (base b), (levelThree d z q) ^ 2 := by
      exact xyTube_sum_edgeVertex a b (base a) (base b)
        (fun z q => (levelThree d z q) ^ 2)
    _ ≤ levelBound d := by
      calc
        _ ≤ ∑ z ∈ xyTubeEdgeLevels a (base a),
            ∑ q ∈ xyTubeVertexOffsets b (base b),
              (levelTwo d z q ^ 2 + levelThree d z q ^ 2) := by
                apply Finset.sum_le_sum
                intro z hz
                apply Finset.sum_le_sum
                intro q hq
                nlinarith [sq_nonneg (levelTwo d z q)]
        _ ≤ levelBound d := sum_level_sq_le d
          (xyTubeEdgeLevels a (base a)) (xyTubeVertexOffsets b (base b))

private theorem xyTube_tent_levelInterior_sum_le (L : ℕ) :
    ∑ s ∈ Finset.range (L - 1), levelBound (min s (L - 2 - s)) ≤ 2 := by
  by_cases hL : L < 2
  · have hrange : L - 1 = 0 := by omega
    simp [hrange]
  · have hrange : L - 2 + 1 = L - 1 := by omega
    simpa [hrange] using tent_levelBound_sum_le (L - 2)

private theorem xyTube_transAEnergy_le {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (hEnd : (base axis).val + L ≤ B axis) :
    ∑ e : Fin (B (xyAxisTransverseA axis)),
      ∑ v : {v : (j : Fin 3) → Fin (B j + 1) //
        v (xyAxisTransverseA axis) = 0},
        (xyTubeSegmentBondCoeff axis base L
          (xyBondFromVertexEdge v.1 (xyAxisTransverseA axis) e)) ^ 2 ≤ 2 := by
  classical
  let a := xyAxisTransverseA axis
  let b := xyAxisTransverseB axis
  let baseAx := (base axis).val
  have hreindex :
      (∑ e : Fin (B a),
        ∑ v : {v : (j : Fin 3) → Fin (B j + 1) // v a = 0},
          (xyTubeSegmentBondCoeff axis base L
            (xyBondFromVertexEdge v.1 a e)) ^ 2) =
      ∑ k : Fin (B axis + 1),
        ∑ e : Fin (B a),
          ∑ w : Fin (B b + 1),
            (xyTubeSegmentBondCoeff axis base L
              (xyBondFromVertexEdge
                ((xyTubeTransAVertexEquiv axis).symm (k, w)).1 a e)) ^ 2 := by
    calc
      _ = ∑ e : Fin (B a),
          ∑ p : Fin (B axis + 1) × Fin (B b + 1),
            (xyTubeSegmentBondCoeff axis base L
              (xyBondFromVertexEdge
                ((xyTubeTransAVertexEquiv axis).symm p).1 a e)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro e he
              exact xyTube_sum_transAVertex axis (fun v =>
                (xyTubeSegmentBondCoeff axis base L
                  (xyBondFromVertexEdge v.1 a e)) ^ 2)
      _ = ∑ e : Fin (B a), ∑ k : Fin (B axis + 1),
            ∑ w : Fin (B b + 1),
              (xyTubeSegmentBondCoeff axis base L
                (xyBondFromVertexEdge
                  ((xyTubeTransAVertexEquiv axis).symm (k, w)).1 a e)) ^ 2 := by
              simp_rw [Fintype.sum_prod_type]
      _ = ∑ k : Fin (B axis + 1), ∑ e : Fin (B a),
            ∑ w : Fin (B b + 1),
              (xyTubeSegmentBondCoeff axis base L
                (xyBondFromVertexEdge
                  ((xyTubeTransAVertexEquiv axis).symm (k, w)).1 a e)) ^ 2 := by
              rw [Finset.sum_comm]
  have hLayer (k : Fin (B axis + 1)) :
      (∑ e : Fin (B a), ∑ w : Fin (B b + 1),
        (xyTubeSegmentBondCoeff axis base L
          (xyBondFromVertexEdge
            ((xyTubeTransAVertexEquiv axis).symm (k, w)).1 a e)) ^ 2) ≤
        if baseAx < k.val ∧ k.val < baseAx + L then
          levelBound (min (k.val - baseAx - 1)
            (L - 1 - (k.val - baseAx)))
        else 0 := by
    by_cases hk : baseAx < k.val ∧ k.val < baseAx + L
    · rw [ite_eq_left hk]
      exact xyTube_transALayer_energy_le axis base L k
        (by simpa [baseAx] using hk.1) (by simpa [baseAx] using hk.2)
    · rw [ite_eq_right hk]
      have hprofile : ¬(0 < (k.val : ℤ) - baseAx ∧
          (k.val : ℤ) - baseAx < (L : ℤ)) := by
        intro hp
        exact hk (by push_cast at hp; omega)
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro e he
      apply Finset.sum_eq_zero
      intro w hw
      have hcoords := (xyTubeTransAVertexEquiv axis).apply_symm_apply (k, w)
      have haxis : ((xyTubeTransAVertexEquiv axis).symm (k, w)).1 axis = k :=
        congrArg Prod.fst hcoords
      rw [xyTubeSegmentBondCoeff_transA]
      simp only [haxis]
      dsimp
      rw [ite_eq_right hprofile]
      norm_num
  rw [hreindex]
  calc
    _ ≤ ∑ k : Fin (B axis + 1), if baseAx < k.val ∧ k.val < baseAx + L then
          levelBound (min (k.val - baseAx - 1)
            (L - 1 - (k.val - baseAx))) else 0 :=
      Finset.sum_le_sum fun k hk => hLayer k
    _ = ∑ s ∈ Finset.range (L - 1), levelBound (min s (L - 2 - s)) := by
      simpa only [baseAx] using xyTube_interiorDepth_sum (n := B axis)
        (b := (base axis).val) hEnd (fun d => levelBound d)
    _ ≤ 2 := xyTube_tent_levelInterior_sum_le L

private theorem xyTube_transBLayer_energy_le {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (k : Fin (B axis + 1))
    (hBefore : (base axis).val < k.val)
    (hAfter : k.val < (base axis).val + L) :
    ∑ e : Fin (B (xyAxisTransverseB axis)),
      ∑ w : Fin (B (xyAxisTransverseA axis) + 1),
        (xyTubeSegmentBondCoeff axis base L
          (xyBondFromVertexEdge
            ((xyTubeTransBVertexEquiv axis).symm (k, w)).1
            (xyAxisTransverseB axis) e)) ^ 2 ≤
      levelBound (min (k.val - (base axis).val - 1)
        (L - 1 - (k.val - (base axis).val))) := by
  classical
  let a := xyAxisTransverseA axis
  let b := xyAxisTransverseB axis
  let d := min (k.val - (base axis).val - 1)
    (L - 1 - (k.val - (base axis).val))
  have hpoint (e : Fin (B b)) (w : Fin (B a + 1)) :
      (xyTubeSegmentBondCoeff axis base L
        (xyBondFromVertexEdge
          ((xyTubeTransBVertexEquiv axis).symm (k, w)).1 b e)) ^ 2 ≤
        (levelTwo d (xyTubeSiteOffset a (base a) w)
          (xyTubeEdgeLevel b (base b) e)) ^ 2 := by
    have hcoords := (xyTubeTransBVertexEquiv axis).apply_symm_apply (k, w)
    have haxis : ((xyTubeTransBVertexEquiv axis).symm (k, w)).1 axis = k :=
      congrArg Prod.fst hcoords
    have ha : ((xyTubeTransBVertexEquiv axis).symm (k, w)).1 a = w :=
      congrArg Prod.snd hcoords
    have hBefore' : (base axis).val <
        (((xyTubeTransBVertexEquiv axis).symm (k, w)).1 axis).val := by
      simpa [haxis] using hBefore
    have hAfter' :
        (((xyTubeTransBVertexEquiv axis).symm (k, w)).1 axis).val <
          (base axis).val + L := by
      simpa [haxis] using hAfter
    have h := xyTubeSegmentBondCoeff_transB_sq_le axis base L
      ((xyTubeTransBVertexEquiv axis).symm (k, w)).1 e
      hBefore' hAfter'
    simpa [a, b, d, haxis, ha] using h
  calc
    _ ≤ ∑ e : Fin (B b), ∑ w : Fin (B a + 1),
        (levelTwo d (xyTubeSiteOffset a (base a) w)
          (xyTubeEdgeLevel b (base b) e)) ^ 2 :=
      Finset.sum_le_sum fun e he => Finset.sum_le_sum fun w hw => hpoint e w
    _ = ∑ w : Fin (B a + 1), ∑ e : Fin (B b),
        (levelTwo d (xyTubeSiteOffset a (base a) w)
          (xyTubeEdgeLevel b (base b) e)) ^ 2 := by
          rw [Finset.sum_comm]
    _ = ∑ z ∈ xyTubeVertexOffsets a (base a),
        ∑ q ∈ xyTubeEdgeLevels b (base b), (levelTwo d z q) ^ 2 := by
      exact xyTube_sum_vertexEdge a b (base a) (base b)
        (fun z q => (levelTwo d z q) ^ 2)
    _ ≤ ∑ z ∈ xyTubeVertexOffsets a (base a),
        ∑ q ∈ xyTubeEdgeLevels b (base b),
          (levelTwo d z q ^ 2 + levelThree d z q ^ 2) := by
            apply Finset.sum_le_sum
            intro z hz
            apply Finset.sum_le_sum
            intro q hq
            nlinarith [sq_nonneg (levelThree d z q)]
    _ ≤ levelBound d := sum_level_sq_le d
      (xyTubeVertexOffsets a (base a)) (xyTubeEdgeLevels b (base b))

private theorem xyTube_transBEnergy_le {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (hEnd : (base axis).val + L ≤ B axis) :
    ∑ e : Fin (B (xyAxisTransverseB axis)),
      ∑ v : {v : (j : Fin 3) → Fin (B j + 1) //
        v (xyAxisTransverseB axis) = 0},
        (xyTubeSegmentBondCoeff axis base L
          (xyBondFromVertexEdge v.1 (xyAxisTransverseB axis) e)) ^ 2 ≤ 2 := by
  classical
  let a := xyAxisTransverseA axis
  let b := xyAxisTransverseB axis
  let baseAx := (base axis).val
  have hreindex :
      (∑ e : Fin (B b),
        ∑ v : {v : (j : Fin 3) → Fin (B j + 1) // v b = 0},
          (xyTubeSegmentBondCoeff axis base L
            (xyBondFromVertexEdge v.1 b e)) ^ 2) =
      ∑ k : Fin (B axis + 1),
        ∑ e : Fin (B b), ∑ w : Fin (B a + 1),
          (xyTubeSegmentBondCoeff axis base L
            (xyBondFromVertexEdge
              ((xyTubeTransBVertexEquiv axis).symm (k, w)).1 b e)) ^ 2 := by
    calc
      _ = ∑ e : Fin (B b),
          ∑ p : Fin (B axis + 1) × Fin (B a + 1),
            (xyTubeSegmentBondCoeff axis base L
              (xyBondFromVertexEdge
                ((xyTubeTransBVertexEquiv axis).symm p).1 b e)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro e he
              exact xyTube_sum_transBVertex axis (fun v =>
                (xyTubeSegmentBondCoeff axis base L
                  (xyBondFromVertexEdge v.1 b e)) ^ 2)
      _ = ∑ e : Fin (B b), ∑ k : Fin (B axis + 1),
            ∑ w : Fin (B a + 1),
              (xyTubeSegmentBondCoeff axis base L
                (xyBondFromVertexEdge
                  ((xyTubeTransBVertexEquiv axis).symm (k, w)).1 b e)) ^ 2 := by
              simp_rw [Fintype.sum_prod_type]
      _ = ∑ k : Fin (B axis + 1), ∑ e : Fin (B b),
            ∑ w : Fin (B a + 1),
              (xyTubeSegmentBondCoeff axis base L
                (xyBondFromVertexEdge
                  ((xyTubeTransBVertexEquiv axis).symm (k, w)).1 b e)) ^ 2 := by
              rw [Finset.sum_comm]
  have hLayer (k : Fin (B axis + 1)) :
      (∑ e : Fin (B b), ∑ w : Fin (B a + 1),
        (xyTubeSegmentBondCoeff axis base L
          (xyBondFromVertexEdge
            ((xyTubeTransBVertexEquiv axis).symm (k, w)).1 b e)) ^ 2) ≤
        if baseAx < k.val ∧ k.val < baseAx + L then
          levelBound (min (k.val - baseAx - 1)
            (L - 1 - (k.val - baseAx))) else 0 := by
    by_cases hk : baseAx < k.val ∧ k.val < baseAx + L
    · rw [ite_eq_left hk]
      exact xyTube_transBLayer_energy_le axis base L k
        (by simpa [baseAx] using hk.1) (by simpa [baseAx] using hk.2)
    · rw [ite_eq_right hk]
      have hprofile : ¬(0 < (k.val : ℤ) - baseAx ∧
          (k.val : ℤ) - baseAx < (L : ℤ)) := by
        intro hp
        exact hk (by push_cast at hp; omega)
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro e he
      apply Finset.sum_eq_zero
      intro w hw
      have hcoords := (xyTubeTransBVertexEquiv axis).apply_symm_apply (k, w)
      have haxis : ((xyTubeTransBVertexEquiv axis).symm (k, w)).1 axis = k :=
        congrArg Prod.fst hcoords
      rw [xyTubeSegmentBondCoeff_transB]
      simp only [haxis]
      dsimp
      rw [ite_eq_right hprofile]
      norm_num
  rw [hreindex]
  calc
    _ ≤ ∑ k : Fin (B axis + 1),
          if baseAx < k.val ∧ k.val < baseAx + L then
            levelBound (min (k.val - baseAx - 1)
              (L - 1 - (k.val - baseAx))) else 0 :=
      Finset.sum_le_sum fun k hk => hLayer k
    _ = ∑ s ∈ Finset.range (L - 1), levelBound (min s (L - 2 - s)) := by
      simpa only [baseAx] using xyTube_interiorDepth_sum (n := B axis)
        (b := (base axis).val) hEnd (fun d => levelBound d)
    _ ≤ 2 := xyTube_tent_levelInterior_sum_le L

private noncomputable def xyTubeAxisOrderEquiv (axis : Fin 3) : Fin 3 ≃ Fin 3 where
  toFun j := if j = 0 then axis else if j = 1 then xyAxisTransverseA axis
    else xyAxisTransverseB axis
  invFun i := if i = axis then 0 else if i = xyAxisTransverseA axis then 1 else 2
  left_inv := by
    intro j
    fin_cases axis <;> fin_cases j <;>
      simp [xyAxisTransverseA, xyAxisTransverseB]
  right_inv := by
    intro i
    fin_cases axis <;> fin_cases i <;>
      simp [xyAxisTransverseA, xyAxisTransverseB]

private theorem xyTubeAxisOrderEquiv_zero (axis : Fin 3) :
    xyTubeAxisOrderEquiv axis 0 = axis := by
  simp [xyTubeAxisOrderEquiv]

private theorem xyTubeAxisOrderEquiv_one (axis : Fin 3) :
    xyTubeAxisOrderEquiv axis (Fin.succ 0) = xyAxisTransverseA axis := by
  simp [xyTubeAxisOrderEquiv]

private theorem xyTubeAxisOrderEquiv_two (axis : Fin 3) :
    xyTubeAxisOrderEquiv axis ((Fin.succ 0).succ) = xyAxisTransverseB axis := by
  simp [xyTubeAxisOrderEquiv]

private theorem xyTube_sum_axisOrder (axis : Fin 3) (f : Fin 3 → ℝ) :
    (∑ i : Fin 3, f i) =
      f axis + (f (xyAxisTransverseA axis) + f (xyAxisTransverseB axis)) := by
  calc
    _ = ∑ j : Fin 3, f (xyTubeAxisOrderEquiv axis j) :=
      (Equiv.sum_comp (xyTubeAxisOrderEquiv axis) f).symm
    _ = _ := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
        xyTubeAxisOrderEquiv_zero, xyTubeAxisOrderEquiv_one,
        xyTubeAxisOrderEquiv_two, add_zero]

private theorem xyTubeVertex_eq_of_coordinates {B : Dual3Box} (axis : Fin 3)
    (v w : (i : Fin 3) → Fin (B i + 1))
    (hAxis : v axis = w axis)
    (hA : v (xyAxisTransverseA axis) = w (xyAxisTransverseA axis))
    (hB : v (xyAxisTransverseB axis) = w (xyAxisTransverseB axis)) : v = w := by
  funext i
  have hi : i = axis ∨ i = xyAxisTransverseA axis ∨
      i = xyAxisTransverseB axis := by
    fin_cases axis <;> fin_cases i <;>
      simp [xyAxisTransverseA, xyAxisTransverseB]
  rcases hi with hi | hi | hi
  · subst i
    exact hAxis
  · subst i
    exact hA
  · subst i
    exact hB

private theorem xyTubeSegment_boundary_at_startPlane {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (hL : 0 < L) (hEnd : (base axis).val + L ≤ B axis)
    (v : (i : Fin 3) → Fin (B i + 1)) (hAxis : v axis = base axis) :
    realBoundary (xyBondRealChain (xyTubeSegmentBondCoeff axis base L))
      (xyVertexCell v) = if v = base then -1 else 0 := by
  rw [xyBondRealBoundary_vertex_formula]
  change (∑ i : Fin 3,
      xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v i) = _
  rw [xyTube_sum_axisOrder axis]
  let a := xyAxisTransverseA axis
  let b := xyAxisTransverseB axis
  have hA : xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v a = 0 := by
    simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_transA, a, hAxis]
  have hB : xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v b = 0 := by
    simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_transB, b, hAxis]
  have hprofileA : uni 0 (xyTubeSiteOffset a (base a) (v a)) =
      if v a = base a then 1 else 0 := by
    simp only [uni_zero, xyTubeSiteOffset_eq_zero_iff]
  have hprofileB : uni 0 (xyTubeSiteOffset b (base b) (v b)) =
      if v b = base b then 1 else 0 := by
    simp only [uni_zero, xyTubeSiteOffset_eq_zero_iff]
  have hprofile :
      uni 0 (xyTubeSiteOffset a (base a) (v a)) *
        uni 0 (xyTubeSiteOffset b (base b) (v b)) =
          if v = base then 1 else 0 := by
    rw [hprofileA, hprofileB]
    by_cases ha : v a = base a <;> by_cases hb : v b = base b
    · have hv := xyTubeVertex_eq_of_coordinates axis v base hAxis ha hb
      simp [ha, hb, hv]
    · have hv : v ≠ base := by
        intro h
        exact hb (congrFun h b)
      simp [ha, hb, hv]
    · have hv : v ≠ base := by
        intro h
        exact ha (congrFun h a)
      simp [ha, hb, hv]
    · have hv : v ≠ base := by
        intro h
        exact ha (congrFun h a)
      simp [ha, hb, hv]
  have hmain :
      xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v axis =
        -(if v = base then (1 : ℝ) else 0) := by
    have hbaseLt : (base axis).val < B axis := by
      have hL' : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (by omega)
      omega
    have hBpos : 0 < B axis := by omega
    by_cases hbase : (base axis).val = 0
    · simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_axial, hAxis,
        hbase, hbaseLt, hBpos, hL, hprofile, a, b]
    · have hbasePos : 0 < (base axis).val := by omega
      simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_axial, hAxis,
        hbasePos, hbaseLt, hBpos, hL, hprofile, a, b]
  rw [hmain, hA, hB]
  by_cases hv : v = base <;> simp [hv]

private theorem xyTubeSegment_boundary_at_endPlane {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (hL : 0 < L) (hEnd : (base axis).val + L ≤ B axis)
    (v : (i : Fin 3) → Fin (B i + 1))
    (hAxis : (v axis).val = (base axis).val + L) :
    realBoundary (xyBondRealChain (xyTubeSegmentBondCoeff axis base L))
      (xyVertexCell v) =
        if v = Function.update base axis ⟨(base axis).val + L, by omega⟩
        then 1 else 0 := by
  rw [xyBondRealBoundary_vertex_formula]
  change (∑ i : Fin 3,
      xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v i) = _
  rw [xyTube_sum_axisOrder axis]
  let a := xyAxisTransverseA axis
  let b := xyAxisTransverseB axis
  let finish := Function.update base axis ⟨(base axis).val + L, by omega⟩
  have hAxisFin : v axis = finish axis := by
    apply Fin.ext
    simp [finish, hAxis]
  have hFinishA : finish a = base a := by
    dsimp [finish, a]
    exact Function.update_of_ne (xyAxisTransverseA_ne axis)
      ⟨(base axis).val + L, by omega⟩ base
  have hFinishB : finish b = base b := by
    dsimp [finish, b]
    exact Function.update_of_ne (xyAxisTransverseB_ne axis)
      ⟨(base axis).val + L, by omega⟩ base
  have hA : xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v a = 0 := by
    simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_transA, a, hAxis]
  have hB : xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v b = 0 := by
    simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_transB, b, hAxis]
  have hprofileA : uni 0 (xyTubeSiteOffset a (base a) (v a)) =
      if v a = finish a then 1 else 0 := by
    rw [hFinishA]
    simp only [uni_zero, xyTubeSiteOffset_eq_zero_iff]
  have hprofileB : uni 0 (xyTubeSiteOffset b (base b) (v b)) =
      if v b = finish b then 1 else 0 := by
    rw [hFinishB]
    simp only [uni_zero, xyTubeSiteOffset_eq_zero_iff]
  have hprofile :
      uni 0 (xyTubeSiteOffset a (base a) (v a)) *
        uni 0 (xyTubeSiteOffset b (base b) (v b)) =
          if v = finish then 1 else 0 := by
    rw [hprofileA, hprofileB]
    by_cases ha : v a = finish a <;> by_cases hb : v b = finish b
    · have hv := xyTubeVertex_eq_of_coordinates axis v finish hAxisFin ha hb
      simp [ha, hb, hv]
    · have hv : v ≠ finish := by
        intro h
        exact hb (congrFun h b)
      simp [ha, hb, hv]
    · have hv : v ≠ finish := by
        intro h
        exact ha (congrFun h a)
      simp [ha, hb, hv]
    · have hv : v ≠ finish := by
        intro h
        exact ha (congrFun h a)
      simp [ha, hb, hv]
  have hmain :
      xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v axis =
        if v = finish then (1 : ℝ) else 0 := by
    have hvpos : 0 < (v axis).val := by rw [hAxis]; omega
    have hsumToNat := natCast_add_toNat (base axis).val L
    have hindex :
        (((((base axis).val : ℤ) + (L : ℤ)).toNat) - 1 -
          (base axis).val) = L - 1 := by
      rw [hsumToNat]
      omega
    have hcond : ((base axis).val : ℤ) + (L : ℤ) - 1 -
        (base axis).val < (L : ℤ) := by
      have hL' : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (by omega)
      omega
    by_cases hvout : (v axis).val < B axis
    · simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_axial, hAxis,
        hvpos, hvout, hL, hcond, hindex, hprofile, a, b]
    · simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_axial, hAxis,
        hvpos, hvout, hL, hcond, hindex, hprofile, a, b]
  rw [hmain, hA, hB]
  simp [finish]

private theorem xyTubeSegment_boundary_outside_axialRange {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (v : (i : Fin 3) → Fin (B i + 1))
    (houtside : (v axis).val < (base axis).val ∨
      (base axis).val + L < (v axis).val) :
    realBoundary (xyBondRealChain (xyTubeSegmentBondCoeff axis base L))
      (xyVertexCell v) = 0 := by
  rw [xyBondRealBoundary_vertex_formula]
  change (∑ i : Fin 3,
      xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v i) = _
  rw [xyTube_sum_axisOrder axis]
  let a := xyAxisTransverseA axis
  let b := xyAxisTransverseB axis
  have htrans : ¬(0 < ((v axis).val : ℤ) - (base axis).val ∧
      ((v axis).val : ℤ) - (base axis).val < (L : ℤ)) := by
    rcases houtside with hbelow | habove <;> omega
  have htransLayer : ¬(base axis < v axis ∧
      ((v axis).val : ℤ) - (base axis).val < (L : ℤ)) := by
    rcases houtside with hbelow | habove <;> omega
  have hA : xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v a = 0 := by
    simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_transA, a, htransLayer]
  have hB : xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v b = 0 := by
    simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_transB, b, htransLayer]
  have hmain : xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v axis = 0 := by
    rcases houtside with hbelow | habove
    · have hInLayer : ¬(base axis < v axis ∧
          ((v axis).val : ℤ) - 1 - (base axis).val < (L : ℤ)) := by omega
      have hOutLayer : ¬(base axis ≤ v axis ∧
          ((v axis).val : ℤ) - (base axis).val < (L : ℤ)) := by omega
      by_cases hin : 0 < (v axis).val <;>
        by_cases hout : (v axis).val < B axis <;>
          simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_axial,
            hin, hout, hInLayer, hOutLayer]
    · have hInLayer : ¬(base axis < v axis ∧
          ((v axis).val : ℤ) - 1 - (base axis).val < (L : ℤ)) := by omega
      have hOutLayer : ¬(base axis ≤ v axis ∧
          ((v axis).val : ℤ) - (base axis).val < (L : ℤ)) := by omega
      by_cases hin : 0 < (v axis).val <;>
        by_cases hout : (v axis).val < B axis <;>
          simp [xyBondBoundaryTerm, xyTubeSegmentBondCoeff_axial,
            hin, hout, hInLayer, hOutLayer]
  rw [hmain, hA, hB]
  simp

private theorem xyTubeSegment_boundary_at_vertex {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (hEnd : (base axis).val + L ≤ B axis)
    (hSideA : L ≤ B (xyAxisTransverseA axis))
    (hSideB : L ≤ B (xyAxisTransverseB axis))
    (v : (i : Fin 3) → Fin (B i + 1)) :
    realBoundary (xyBondRealChain (xyTubeSegmentBondCoeff axis base L))
      (xyVertexCell v) =
        (if v = base then (-1 : ℝ) else 0) +
        (if v = Function.update base axis
          ⟨(base axis).val + L, by omega⟩ then 1 else 0) := by
  let finish := Function.update base axis
    ⟨(base axis).val + L, by omega⟩
  by_cases hL : L = 0
  · have hbd : realBoundary (xyBondRealChain
        (xyTubeSegmentBondCoeff axis base L)) (xyVertexCell v) = 0 := by
      have hcoeff : ∀ b : XYBonds B,
          xyTubeSegmentBondCoeff axis base L b = 0 := by
        let a := xyAxisTransverseA axis
        let z := xyAxisTransverseB axis
        intro b
        rcases b with ⟨c, hc⟩
        cases hAxisC : c axis <;> cases hAC : c a <;> cases hZC : c z <;>
          simp [xyTubeSegmentBondCoeff, a, z, hAxisC, hAC, hZC, hL] <;> omega
      rw [xyBondRealBoundary_vertex_formula]
      change (∑ i : Fin 3,
          xyBondBoundaryTerm (xyTubeSegmentBondCoeff axis base L) v i) = 0
      rw [xyTube_sum_axisOrder axis]
      simp [xyBondBoundaryTerm, hcoeff]
    rw [hbd]
    by_cases hv : v = base <;> simp [finish, hL, hv]
  · have hLpos : 0 < L := by omega
    by_cases hStart : (v axis).val = (base axis).val
    · have hAxis : v axis = base axis := Fin.ext hStart
      rw [xyTubeSegment_boundary_at_startPlane axis base L hLpos hEnd v hAxis]
      have hvne : v ≠ finish := by
        intro hv
        have hvAxis := congrArg (fun w => (w axis).val) hv
        simp [finish] at hvAxis
        omega
      simp [finish, hvne]
    · by_cases hFinish : (v axis).val = (base axis).val + L
      · rw [xyTubeSegment_boundary_at_endPlane axis base L hLpos hEnd v hFinish]
        have hvne : v ≠ base := by
          intro hv
          have hvAxis := congrArg (fun w => (w axis).val) hv
          omega
        simp [finish, hvne]
      · by_cases hInterior :
          (base axis).val < (v axis).val ∧
            (v axis).val < (base axis).val + L
        · have hbd := xyTubeSegment_boundary_at_interior_faces axis base L
            hLpos hEnd hSideA hSideB v hInterior.1 hInterior.2
          rw [hbd]
          have hvBase : v ≠ base := by
            intro hv
            have hvAxis := congrArg (fun w => (w axis).val) hv
            omega
          have hvFinish : v ≠ finish := by
            intro hv
            have hvAxis := congrArg (fun w => (w axis).val) hv
            simp [finish] at hvAxis
            omega
          simp [finish, hvBase, hvFinish]
        · have hOutside : (v axis).val < (base axis).val ∨
              (base axis).val + L < (v axis).val := by omega
          rw [xyTubeSegment_boundary_outside_axialRange axis base L v hOutside]
          have hvBase : v ≠ base := by
            intro hv
            have hvAxis := congrArg (fun w => (w axis).val) hv
            omega
          have hvFinish : v ≠ finish := by
            intro hv
            have hvAxis := congrArg (fun w => (w axis).val) hv
            simp [finish] at hvAxis
            omega
          simp [finish, hvBase, hvFinish]

private theorem xyTubeSegment_boundary {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (hEnd : (base axis).val + L ≤ B axis)
    (hSideA : L ≤ B (xyAxisTransverseA axis))
    (hSideB : L ≤ B (xyAxisTransverseB axis)) :
    realBoundary (xyBondRealChain (xyTubeSegmentBondCoeff axis base L)) =
      Finsupp.single (xyVertexCell (Function.update base axis
        ⟨(base axis).val + L, by omega⟩)) 1 -
      Finsupp.single (xyVertexCell base) 1 := by
  classical
  apply Finsupp.ext
  intro c
  by_cases hc0 : cellDegree c = 0
  · have haxes : cellAxes c = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [cellDegree] using hc0
    let v : (i : Fin 3) → Fin (B i + 1) := fun i =>
      match c i with
      | Sum.inl u => u
      | Sum.inr _ => 0
    have hcvertex : c = xyVertexCell v := by
      funext i
      cases hci : c i with
      | inl u => simp [xyVertexCell, v, hci]
      | inr e =>
          have hi : i ∈ cellAxes c := by
            simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hci]
            rfl
          rw [haxes] at hi
          simp at hi
    rw [hcvertex]
    rw [xyTubeSegment_boundary_at_vertex axis base L hEnd hSideA hSideB v]
    let finish := Function.update base axis
      ⟨(base axis).val + L, by omega⟩
    rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp only [xyVertexCell_eq_iff]
    exact xyEndpointDelta_eval v base finish
  · have hbd := realBoundary_homogeneousSupport
      (xyBondRealChain (xyTubeSegmentBondCoeff axis base L)) 1 (by norm_num)
      (xyBondRealChain_homogeneous _)
    have hleft : realBoundary
        (xyBondRealChain (xyTubeSegmentBondCoeff axis base L)) c = 0 := by
      by_contra hc
      have hmem : c ∈ (realBoundary
          (xyBondRealChain (xyTubeSegmentBondCoeff axis base L))).support :=
        Finsupp.mem_support_iff.mpr hc
      have := hbd c hmem
      omega
    have hbase : c ≠ xyVertexCell base := by
      intro h
      have hdeg := congrArg cellDegree h
      have hz : cellDegree (xyVertexCell base) = 0 := by
        simp [cellDegree, xyVertexCell_axes_empty]
      rw [hz] at hdeg
      exact hc0 hdeg
    let finish := Function.update base axis
      ⟨(base axis).val + L, by omega⟩
    have hfinish : c ≠ xyVertexCell finish := by
      intro h
      have hdeg := congrArg cellDegree h
      have hz : cellDegree (xyVertexCell finish) = 0 := by
        simp [cellDegree, xyVertexCell_axes_empty]
      rw [hz] at hdeg
      exact hc0 hdeg
    rw [hleft]
    change 0 = (Finsupp.single (xyVertexCell finish) (1 : ℝ)) c -
      (Finsupp.single (xyVertexCell base) (1 : ℝ)) c
    rw [Finsupp.single_apply, Finsupp.single_apply]
    rw [ite_eq_right hfinish.symm, ite_eq_right hbase.symm]
    norm_num

private def xyEndpointWaypoint {B : Dual3Box}
    (x y : XYSites B) (n : ℕ) : (i : Fin 3) → Fin (B i + 1) :=
  fun i => if i.val < n then xySiteVertexIndex y i else xySiteVertexIndex x i

private theorem xyTubeSegmentBase_endpoint {B : Dual3Box}
    (x y : XYSites B) (axis : Fin 3)
    (hle : (xySiteVertexIndex x axis).val ≤ (xySiteVertexIndex y axis).val) :
    xyTubeSegmentBase x y axis = xyEndpointWaypoint x y axis.val := by
  classical
  funext i
  by_cases hia : i = axis
  · subst i
    have hleFin : xySiteVertexIndex x axis ≤ xySiteVertexIndex y axis := by
      omega
    simp [xyTubeSegmentBase, xyEndpointWaypoint, hleFin]
  · have hval : i.val ≠ axis.val := by
      intro h
      exact hia (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hFin : i < axis := by omega
      simp [xyTubeSegmentBase, xyEndpointWaypoint, hia, hFin, hlt]
    · have hFin : axis < i := by omega
      have hNot : ¬i < axis := not_lt_of_ge hFin.le
      simp [xyTubeSegmentBase, xyEndpointWaypoint, hia, hNot, hgt]

private theorem xyTubeSegmentBase_endpoint_gt {B : Dual3Box}
    (x y : XYSites B) (axis : Fin 3)
    (hgt : (xySiteVertexIndex y axis).val < (xySiteVertexIndex x axis).val) :
    xyTubeSegmentBase x y axis = xyEndpointWaypoint x y (axis.val + 1) := by
  classical
  funext i
  by_cases hia : i = axis
  · subst i
    have hmin : xySiteVertexIndex y axis ≤ xySiteVertexIndex x axis := by
      omega
    simp [xyTubeSegmentBase, xyEndpointWaypoint, hmin]
  · have hval : i.val ≠ axis.val := by
      intro h
      exact hia (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hgt'
    · have hFin : i < axis := by omega
      have hway : i.val < axis.val + 1 := by omega
      simp [xyTubeSegmentBase, xyEndpointWaypoint, hia, hFin, hlt, hway]
    · have hFin : axis < i := by omega
      have hNot : ¬i < axis := not_lt_of_ge hFin.le
      have hway : ¬i.val < axis.val + 1 := by omega
      simp [xyTubeSegmentBase, xyEndpointWaypoint, hia, hNot, hgt', hway]

private theorem xyTubeSegmentFinish_endpoint {B : Dual3Box}
    (x y : XYSites B) (axis : Fin 3)
    (hle : (xySiteVertexIndex x axis).val ≤ (xySiteVertexIndex y axis).val) :
    Function.update (xyTubeSegmentBase x y axis) axis
        ⟨(xyTubeSegmentBase x y axis axis).val +
          xyTubeSegmentLength x y axis, by
            have hleFin : xySiteVertexIndex x axis ≤ xySiteVertexIndex y axis := by omega
            simp [xyTubeSegmentBase, xyTubeSegmentLength, hle, hleFin,
              min_eq_left hleFin]
            omega⟩ =
      xyEndpointWaypoint x y (axis.val + 1) := by
  classical
  have hleFin : xySiteVertexIndex x axis ≤ xySiteVertexIndex y axis := by omega
  have hbaseVal : (xyTubeSegmentBase x y axis axis).val =
      (xySiteVertexIndex x axis).val := by
    simp [xyTubeSegmentBase, hleFin]
  have hlen : xyTubeSegmentLength x y axis =
      (xySiteVertexIndex y axis).val - (xySiteVertexIndex x axis).val := by
    simp [xyTubeSegmentLength, hle]
  have hcoord : (xyTubeSegmentBase x y axis axis).val +
      xyTubeSegmentLength x y axis = (xySiteVertexIndex y axis).val := by
    rw [hbaseVal, hlen]
    omega
  have hfin : (⟨(xyTubeSegmentBase x y axis axis).val +
      xyTubeSegmentLength x y axis, by omega⟩ : Fin (B axis + 1)) =
      xySiteVertexIndex y axis := Fin.ext hcoord
  funext i
  by_cases hia : i = axis
  · subst i
    simp [Function.update, hfin, xyEndpointWaypoint]
  · have hval : i.val ≠ axis.val := by
      intro h
      exact hia (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hFin : i < axis := by omega
      have hway : i.val < axis.val + 1 := by omega
      simp [Function.update_of_ne hia, xyTubeSegmentBase, xyEndpointWaypoint,
        hia, hFin, hlt, hway]
    · have hFin : axis < i := by omega
      have hNot : ¬i < axis := not_lt_of_ge hFin.le
      have hway : ¬i.val < axis.val + 1 := by omega
      simp [Function.update_of_ne hia, xyTubeSegmentBase, xyEndpointWaypoint,
        hia, hNot, hgt, hway]

private theorem xyTubeSegmentFinish_endpoint_gt {B : Dual3Box}
    (x y : XYSites B) (axis : Fin 3)
    (hgt : (xySiteVertexIndex y axis).val < (xySiteVertexIndex x axis).val) :
    Function.update (xyTubeSegmentBase x y axis) axis
        ⟨(xyTubeSegmentBase x y axis axis).val +
          xyTubeSegmentLength x y axis, by
            have hmin : xySiteVertexIndex y axis ≤ xySiteVertexIndex x axis := by omega
            have hnot : ¬(xySiteVertexIndex x axis).val ≤
                (xySiteVertexIndex y axis).val := by omega
            simp [xyTubeSegmentBase, xyTubeSegmentLength, hnot, hmin]
            omega⟩ = xyEndpointWaypoint x y axis.val := by
  classical
  have hmin : xySiteVertexIndex y axis ≤ xySiteVertexIndex x axis := by omega
  have hbaseVal : (xyTubeSegmentBase x y axis axis).val =
      (xySiteVertexIndex y axis).val := by
    simp [xyTubeSegmentBase, hmin]
  have hlen : xyTubeSegmentLength x y axis =
      (xySiteVertexIndex x axis).val - (xySiteVertexIndex y axis).val := by
    simp [xyTubeSegmentLength, show ¬(xySiteVertexIndex x axis).val ≤
      (xySiteVertexIndex y axis).val by omega]
  have hcoord : (xyTubeSegmentBase x y axis axis).val +
      xyTubeSegmentLength x y axis = (xySiteVertexIndex x axis).val := by
    rw [hbaseVal, hlen]
    omega
  have hfin : (⟨(xyTubeSegmentBase x y axis axis).val +
      xyTubeSegmentLength x y axis, by omega⟩ : Fin (B axis + 1)) =
      xySiteVertexIndex x axis := Fin.ext hcoord
  funext i
  by_cases hia : i = axis
  · subst i
    simp [Function.update, hfin, xyEndpointWaypoint]
  · have hval : i.val ≠ axis.val := by
      intro h
      exact hia (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hgt'
    · have hFin : i < axis := by omega
      simp [Function.update_of_ne hia, xyTubeSegmentBase, xyEndpointWaypoint,
        hia, hFin, hlt]
    · have hFin : axis < i := by omega
      have hNot : ¬i < axis := not_lt_of_ge hFin.le
      have hway : ¬i.val < axis.val := by omega
      simp [Function.update_of_ne hia, xyTubeSegmentBase, xyEndpointWaypoint,
        hia, hNot, hgt', hway]

private theorem xyTubeSegment_geometry {B : Dual3Box}
    (x y : XYSites B) (axis : Fin 3)
    (hCube : ∀ i j : Fin 3, B i = B j) :
    (xyTubeSegmentBase x y axis axis).val +
        xyTubeSegmentLength x y axis ≤ B axis ∧
      xyTubeSegmentLength x y axis ≤ B (xyAxisTransverseA axis) ∧
      xyTubeSegmentLength x y axis ≤ B (xyAxisTransverseB axis) := by
  have hx := (xySiteVertexIndex x axis).isLt
  have hy := (xySiteVertexIndex y axis).isLt
  have hle : (xySiteVertexIndex x axis).val ≤ (xySiteVertexIndex y axis).val ∨
      (xySiteVertexIndex y axis).val < (xySiteVertexIndex x axis).val := by omega
  have hL : xyTubeSegmentLength x y axis ≤ B axis := by
    unfold xyTubeSegmentLength
    split_ifs <;> omega
  have hEnd : (xyTubeSegmentBase x y axis axis).val +
      xyTubeSegmentLength x y axis ≤ B axis := by
    rcases hle with hle | hgt
    · have hleFin : xySiteVertexIndex x axis ≤ xySiteVertexIndex y axis := by omega
      simp [xyTubeSegmentBase, xyTubeSegmentLength, hle, hleFin]
      omega
    · have hgtFin : xySiteVertexIndex y axis ≤ xySiteVertexIndex x axis := by omega
      simp [xyTubeSegmentBase, xyTubeSegmentLength,
        show ¬(xySiteVertexIndex x axis).val ≤ (xySiteVertexIndex y axis).val by omega,
        hgtFin]
      omega
  refine ⟨hEnd, ?_, ?_⟩
  · rw [← hCube axis (xyAxisTransverseA axis)]
    exact hL
  · rw [← hCube axis (xyAxisTransverseB axis)]
    exact hL

private theorem xyEndpointTubeSegment_boundary {B : Dual3Box}
    (x y : XYSites B) (axis : Fin 3)
    (hCube : ∀ i j : Fin 3, B i = B j) :
    realBoundary (xyTubeSegmentSign x y axis •
        xyBondRealChain (xyTubeSegmentBondCoeff axis
          (xyTubeSegmentBase x y axis) (xyTubeSegmentLength x y axis))) =
      Finsupp.single (xyVertexCell (xyEndpointWaypoint x y axis.val)) 1 -
      Finsupp.single (xyVertexCell (xyEndpointWaypoint x y (axis.val + 1))) 1 := by
  classical
  obtain ⟨hEnd, hSideA, hSideB⟩ := xyTubeSegment_geometry x y axis hCube
  have hraw := xyTubeSegment_boundary axis (xyTubeSegmentBase x y axis)
    (xyTubeSegmentLength x y axis) hEnd hSideA hSideB
  rw [map_smul]
  rw [hraw]
  by_cases hle : (xySiteVertexIndex x axis).val ≤
      (xySiteVertexIndex y axis).val
  · have hbase := xyTubeSegmentBase_endpoint x y axis hle
    have hfinish := xyTubeSegmentFinish_endpoint x y axis hle
    have hsign : xyTubeSegmentSign x y axis = -1 := by
      simp [xyTubeSegmentSign, hle]
    rw [hsign]
    conv_lhs => rw [hfinish, hbase]
    ext c
    simp only [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.neg_apply,
      Finsupp.single_apply]
    ring
  · have hgt : (xySiteVertexIndex y axis).val <
        (xySiteVertexIndex x axis).val := by omega
    have hbase := xyTubeSegmentBase_endpoint_gt x y axis hgt
    have hfinish := xyTubeSegmentFinish_endpoint_gt x y axis hgt
    have hsign : xyTubeSegmentSign x y axis = 1 := by
      simp [xyTubeSegmentSign, hle]
    rw [hsign]
    conv_lhs => rw [hfinish, hbase]
    simp

private theorem xyBondRealChain_sum {B : Dual3Box} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (f : ι → XYBonds B → ℝ) :
    xyBondRealChain (fun b => ∑ i, f i b) =
      ∑ i, xyBondRealChain (f i) := by
  classical
  ext c
  simp only [xyBondRealChain, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  calc
    _ = ∑ b : XYBonds B, ∑ i, f i b * (Finsupp.single b.1 (1 : ℝ)) c := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
    _ = _ := Finset.sum_comm

private theorem xyBondRealChain_smul {B : Dual3Box}
    (r : ℝ) (f : XYBonds B → ℝ) :
    xyBondRealChain (fun b => r * f b) = r • xyBondRealChain f := by
  classical
  ext c
  simp only [xyBondRealChain, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem xyEndpointTubeCurrent_eq_segmentSum {B : Dual3Box}
    (x y : XYSites B) :
    xyEndpointTubeCurrent x y =
      ∑ axis : Fin 3,
        xyTubeSegmentSign x y axis •
          xyBondRealChain (xyTubeSegmentBondCoeff axis
            (xyTubeSegmentBase x y axis) (xyTubeSegmentLength x y axis)) := by
  classical
  unfold xyEndpointTubeCurrent xyEndpointTubeBondField
  rw [xyBondRealChain_sum]
  apply Finset.sum_congr rfl
  intro axis haxis
  rw [xyBondRealChain_smul]

private theorem xyEndpointWaypoint_telescope {B : Dual3Box}
    (x y : XYSites B) :
    ∑ axis : Fin 3,
        (Finsupp.single (xyVertexCell (xyEndpointWaypoint x y axis.val)) (1 : ℝ) -
          Finsupp.single (xyVertexCell
            (xyEndpointWaypoint x y (axis.val + 1))) 1) =
      Finsupp.single (xyVertexCell (xySiteVertexIndex x)) 1 -
        Finsupp.single (xyVertexCell (xySiteVertexIndex y)) 1 := by
  classical
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  have hzero : xyEndpointWaypoint x y 0 = xySiteVertexIndex x := by
    funext i
    simp [xyEndpointWaypoint]
  have hthree : xyEndpointWaypoint x y 3 = xySiteVertexIndex y := by
    funext i
    have hi : i.val < 3 := i.isLt
    simp [xyEndpointWaypoint, hi]
  rw [hzero, hthree]
  abel_nf

private theorem xyEndpointSource_cast {B : Dual3Box}
    (x y : XYSites B) :
    castIntegerChain (xyEndpointSource x y) =
      Finsupp.single (xyVertexCell (xySiteVertexIndex x)) 1 -
        Finsupp.single (xyVertexCell (xySiteVertexIndex y)) 1 := by
  rw [xyEndpointSource, castIntegerChain_sub,
    castIntegerChain_basis, castIntegerChain_basis]
  rw [xySite_eq_xyVertexCell x, xySite_eq_xyVertexCell y]

private theorem xyEndpointTubeCurrent_boundary {B : Dual3Box}
    (x y : XYSites B) (hCube : ∀ i j : Fin 3, B i = B j) :
    realBoundary (xyEndpointTubeCurrent x y) =
      castIntegerChain (xyEndpointSource x y) := by
  rw [xyEndpointTubeCurrent_eq_segmentSum, map_sum]
  calc
    _ = ∑ axis : Fin 3,
        (Finsupp.single (xyVertexCell (xyEndpointWaypoint x y axis.val)) (1 : ℝ) -
          Finsupp.single (xyVertexCell
            (xyEndpointWaypoint x y (axis.val + 1))) 1) := by
          apply Finset.sum_congr rfl
          intro axis haxis
          exact xyEndpointTubeSegment_boundary x y axis hCube
    _ = castIntegerChain (xyEndpointSource x y) := by
          rw [xyEndpointWaypoint_telescope, xyEndpointSource_cast]

private theorem xyTubeSegment_energy_le {B : Dual3Box}
    (axis : Fin 3) (base : (i : Fin 3) → Fin (B i + 1)) (L : ℕ)
    (hEnd : (base axis).val + L ≤ B axis) :
    ∑ b : XYBonds B, (xyTubeSegmentBondCoeff axis base L b) ^ 2 ≤ 8 := by
  classical
  rw [xyBond_squareSum_reindex]
  let energy := fun i : Fin 3 =>
    ∑ e : Fin (B i), ∑ v : {v : (j : Fin 3) → Fin (B j + 1) // v i = 0},
      (xyTubeSegmentBondCoeff axis base L
        (xyBondFromVertexEdge v.1 i e)) ^ 2
  have haxial : energy axis ≤ 4 := by
    unfold energy
    calc
      _ = ∑ e : Fin (B axis),
          ∑ p : Fin (B (xyAxisTransverseA axis) + 1) ×
              Fin (B (xyAxisTransverseB axis) + 1),
            (xyTubeSegmentBondCoeff axis base L
              (xyBondFromVertexEdge
                ((xyTubeTransverseVertexEquiv axis).symm p).1 axis e)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro e he
              exact xyTube_sum_transverseVertex axis (fun v =>
                (xyTubeSegmentBondCoeff axis base L
                  (xyBondFromVertexEdge v.1 axis e)) ^ 2)
      _ ≤ 4 := xyTube_axialEnergy_le axis base L hEnd
  have hA : energy (xyAxisTransverseA axis) ≤ 2 := by
    unfold energy
    exact xyTube_transAEnergy_le axis base L hEnd
  have hB : energy (xyAxisTransverseB axis) ≤ 2 := by
    unfold energy
    exact xyTube_transBEnergy_le axis base L hEnd
  have htotal := add_le_add haxial (add_le_add hA hB)
  calc
    _ = energy axis +
        (energy (xyAxisTransverseA axis) + energy (xyAxisTransverseB axis)) := by
          rw [xyTube_sum_axisOrder]
    _ ≤ 4 + (2 + 2) := htotal
    _ = 8 := by norm_num


theorem xyDual3ResidualEnergy_eq_loopFieldResidual_inner {B : Dual3Box}
    (x y : XYSites B) :
    xyDual3ResidualEnergy x y =
      inner ℝ
        (loopFieldResidual (dual3ExactOneComplex B)
          (xyDual3EndpointPathVector x y))
        (loopFieldResidual (dual3ExactOneComplex B)
          (xyDual3EndpointPathVector x y)) := by
  let C := dual3ExactOneComplex B
  let φ := xyDual3EndpointPathVector x y
  let μ := xyDual3PathSourceCoClosed x y
  let τ := xyDual3PathTau x y
  have hodge : hodgeOnCoClosed C τ = μ := by
    exact dual3HodgeInverse_spec (xyDual3PathSourceCoClosed x y)
  have hcurl : C.d₁.adjoint (C.d₁ τ.1) = μ.1 := by
    have h := congrArg Subtype.val hodge
    simpa [hodgeOnCoClosed, formLaplacian, C, τ, μ] using h
  have hsource : C.d₁.adjoint φ = μ.1 := by
    rfl
  have horth : ∀ α : EuclideanSpace ℝ (Dual3Links B),
      inner ℝ (φ - C.d₁ τ.1) (C.d₁ α) = 0 := by
    intro α
    calc
      inner ℝ (φ - C.d₁ τ.1) (C.d₁ α) =
          inner ℝ (C.d₁.adjoint φ) α -
            inner ℝ (C.d₁.adjoint (C.d₁ τ.1)) α := by
              rw [inner_sub_left,
                ← LinearMap.adjoint_inner_left C.d₁ α φ,
                ← LinearMap.adjoint_inner_left C.d₁ α (C.d₁ τ.1)]
      _ = 0 := by rw [hsource, hcurl]; simp
  have hproj : (LinearMap.range C.d₁).starProjection φ = C.d₁ τ.1 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact LinearMap.mem_range_self C.d₁ τ.1
    · intro v hv
      rcases hv with ⟨α, rfl⟩
      exact horth α
  have hres : loopFieldResidual C φ = φ - C.d₁ τ.1 := by
    simp only [loopFieldResidual, hproj]
  have hnorm : inner ℝ (C.d₁ τ.1) (C.d₁ τ.1) = inner ℝ μ.1 τ.1 := by
    rw [← hcurl]
    exact (LinearMap.adjoint_inner_left C.d₁ τ.1 (C.d₁ τ.1)).symm
  let ε := φ - C.d₁ τ.1
  have hεorth : inner ℝ ε (C.d₁ τ.1) = 0 := by
    simpa [ε] using horth τ.1
  have hεorth' : inner ℝ (C.d₁ τ.1) ε = 0 := by
    rw [real_inner_comm]
    exact hεorth
  have hpyth : inner ℝ φ φ =
      inner ℝ ε ε +
        inner ℝ (C.d₁ τ.1) (C.d₁ τ.1) := by
    have hdecomp : ε + C.d₁ τ.1 = φ := by simp [ε]
    rw [← hdecomp]
    simp only [inner_add_left, inner_add_right]
    rw [hεorth, hεorth']
    ring
  change inner ℝ φ φ - inner ℝ μ.1 τ.1 = _
  rw [hpyth, hnorm, hres]
  simp [ε]

/-! ### A finite real bond flow is a residual competitor -/

/--
The chain fill is finite and uses the grounded dual complex's
grounded star complex.
-/
theorem xyDual3ResidualEnergy_le_of_bondFlow {B : Dual3Box}
    (x y : XYSites B) (J : RealChain 3 B)
    (hJ : realHomogeneousSupport J 1)
    (hboundary : realBoundary J = castIntegerChain (xyEndpointSource x y)) :
    xyDual3ResidualEnergy x y ≤ xyDual3BondEnergy J := by
  let path := castIntegerChain (xyEndpointPath x y)
  have hpathdeg : realHomogeneousSupport path 1 := by
    intro c hc
    exact xyEndpointPath_homogeneousSupport x y c
      (Finsupp.support_mapRange hc)
  have hpathbd : realBoundary path = castIntegerChain (xyEndpointSource x y) := by
    have hcast : castIntegerChain (boundary (xyEndpointPath x y)) =
        realBoundary path := by
      simpa [realBoundary, path] using
        (realifyLinearMap_cast boundary (xyEndpointPath x y)).symm
    rw [← hcast, xyEndpointPath_boundary]
  let q := path - J
  have hqdeg : realHomogeneousSupport q 1 := by
    intro c hc
    have hqval : q c ≠ 0 := Finsupp.mem_support_iff.mp hc
    have hs : c ∈ path.support ∨ c ∈ J.support := by
      by_contra hnot
      have hnp : c ∉ path.support := by
        intro hp
        exact hnot (Or.inl hp)
      have hnj : c ∉ J.support := by
        intro hj
        exact hnot (Or.inr hj)
      have hp0 : path c = 0 := by
        by_contra hp
        exact hnp (Finsupp.mem_support_iff.mpr hp)
      have hj0 : J c = 0 := by
        by_contra hj
        exact hnj (Finsupp.mem_support_iff.mpr hj)
      have hzero : q c = 0 := by simp [q, hp0, hj0]
      exact hqval hzero
    rcases hs with hp | hj
    · exact hpathdeg c hp
    · exact hJ c hj
  have hqcycle : realBoundary q = 0 := by
    dsimp [q]
    rw [map_sub, hpathbd, hboundary, sub_self]
  let anchor : Anchor 3 B := fun i => ⟨0, Nat.zero_lt_succ (B i)⟩
  obtain ⟨hfill, hfilldeg⟩ :=
    real_positiveDegree_filling anchor q 1 (by omega) hqdeg hqcycle
  let η := realFillingOperator anchor q
  have hηbd : realBoundary η = q := hfill
  have hηdeg : realHomogeneousSupport η 2 := by simpa [η] using hfilldeg
  have hηdualdeg : dualRealHomogeneousSupport (starMap η) 1 := by
    have h := dual3StarMap_homogeneousSupport η 2 hηdeg
    simpa using h
  have hηsupport : ((starMap η).support : Set (DualCell 3 B)) ⊆
      Set.range dual3LinksEmbedding := by
    intro c hc
    have hd := hηdualdeg c hc
    exact ⟨⟨c, hd⟩, rfl⟩
  let shift : EuclideanSpace ℝ (Dual3Links B) :=
    finsuppToEuclidean (dual3CompressSubtype dual3LinksEmbedding (starMap η))
  have hshiftEmbed : dual3LinksToChain shift = starMap η := by
    dsimp [shift, dual3LinksToChain]
    rw [euclideanToFinsupp_finsuppToEuclidean]
    exact dual3EmbedCompress_eq_self_of_support dual3LinksEmbedding
      (starMap η) hηsupport
  have hshift : (dual3ExactOneComplex B).d₁ shift =
      xyDual3EndpointPathVector x y - xyDual3StarBondVector J := by
    apply dual3PlaquettesToChain_injective
    calc
      dual3PlaquettesToChain ((dual3ExactOneComplex B).d₁ shift) =
          dualExteriorDifference (dual3LinksToChain shift) :=
        dual3D₁_embed_eq_derivative shift
      _ = starMap (realBoundary η) := by
        rw [hshiftEmbed]
        exact primalDualStar_incidence_identity η
      _ = starMap path - starMap J := by
        rw [hηbd]
        simp only [q, map_sub]
      _ = dual3PlaquettesToChain
          (xyDual3EndpointPathVector x y - xyDual3StarBondVector J) := by
        change starMap path - starMap J =
          dual3PlaquettesToChain
            (xyDual3StarBondVector path - xyDual3StarBondVector J)
        rw [map_sub,
          xyDual3StarBondVector_embed path hpathdeg,
          xyDual3StarBondVector_embed J hJ]
  have hres0 := norm_loopFieldResidual_le
    (dual3ExactOneComplex B) (xyDual3EndpointPathVector x y) shift
  have hres : ‖loopFieldResidual (dual3ExactOneComplex B)
      (xyDual3EndpointPathVector x y)‖ ≤ ‖xyDual3StarBondVector J‖ := by
    simpa [hshift] using hres0
  have hresSq : ‖loopFieldResidual (dual3ExactOneComplex B)
      (xyDual3EndpointPathVector x y)‖ ^ 2 ≤
      ‖xyDual3StarBondVector J‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hres 2
  have henergy := xyDual3StarBondVector_energy J hJ
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hresSq
  rw [xyDual3ResidualEnergy_eq_loopFieldResidual_inner, ← henergy]
  exact hresSq

private theorem xyEndpointTubeBondEnergy_le {B : Dual3Box}
    (x y : XYSites B) (hCube : ∀ i j : Fin 3, B i = B j) :
    xyDual3BondEnergy (xyEndpointTubeCurrent x y) ≤ 72 := by
  classical
  rw [xyEndpointTubeCurrent, xyBondRealChain_energy]
  have hpoint (b : XYBonds B) :
      (xyEndpointTubeBondField x y b) ^ 2 ≤
        3 * ∑ axis : Fin 3,
          (xyTubeSegmentSign x y axis *
            xyTubeSegmentBondCoeff axis (xyTubeSegmentBase x y axis)
              (xyTubeSegmentLength x y axis) b) ^ 2 := by
    simpa [xyEndpointTubeBondField] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun axis : Fin 3 =>
          xyTubeSegmentSign x y axis *
            xyTubeSegmentBondCoeff axis (xyTubeSegmentBase x y axis)
              (xyTubeSegmentLength x y axis) b))
  have hsegment : ∀ axis : Fin 3,
      ∑ b : XYBonds B,
          (xyTubeSegmentSign x y axis *
            xyTubeSegmentBondCoeff axis (xyTubeSegmentBase x y axis)
              (xyTubeSegmentLength x y axis) b) ^ 2 ≤ 8 := by
    intro axis
    obtain ⟨hEnd, _, _⟩ := xyTubeSegment_geometry x y axis hCube
    have hsign : (xyTubeSegmentSign x y axis) ^ 2 = 1 := by
      by_cases hle : (xySiteVertexIndex x axis).val ≤
          (xySiteVertexIndex y axis).val <;>
        simp [xyTubeSegmentSign, hle]
    simpa [mul_pow, hsign] using
      (xyTubeSegment_energy_le axis (xyTubeSegmentBase x y axis)
        (xyTubeSegmentLength x y axis) hEnd)
  have hsum : ∑ axis : Fin 3, ∑ b : XYBonds B,
      (xyTubeSegmentSign x y axis *
        xyTubeSegmentBondCoeff axis (xyTubeSegmentBase x y axis)
          (xyTubeSegmentLength x y axis) b) ^ 2 ≤ 24 := by
    calc
      _ ≤ ∑ axis : Fin 3, (8 : ℝ) := by
        apply Finset.sum_le_sum
        intro axis haxis
        exact hsegment axis
      _ = 24 := by norm_num
  calc
    _ ≤ ∑ b : XYBonds B, 3 * ∑ axis : Fin 3,
          (xyTubeSegmentSign x y axis *
            xyTubeSegmentBondCoeff axis (xyTubeSegmentBase x y axis)
              (xyTubeSegmentLength x y axis) b) ^ 2 := by
          apply Finset.sum_le_sum
          intro b hb
          exact hpoint b
    _ = 3 * ∑ axis : Fin 3, ∑ b : XYBonds B,
          (xyTubeSegmentSign x y axis *
            xyTubeSegmentBondCoeff axis (xyTubeSegmentBase x y axis)
              (xyTubeSegmentLength x y axis) b) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 3 * 24 := by nlinarith [hsum]
    _ = 72 := by norm_num

/--
The proof uses
three coordinate double-cones; each layer has square-summable energy and the
cube geometry supplies the transverse room toward its centre, including from
boundary corners.
-/
theorem xyDual3EndpointResidualEnergy_le_uniform {B : Dual3Box}
    (x y : XYSites B) (hCube : ∀ i j : Fin 3, B i = B j) :
    xyDual3ResidualEnergy x y ≤ 72 := by
  calc
    xyDual3ResidualEnergy x y ≤ xyDual3BondEnergy (xyEndpointTubeCurrent x y) :=
      xyDual3ResidualEnergy_le_of_bondFlow x y (xyEndpointTubeCurrent x y)
        (xyBondRealChain_homogeneous _) (xyEndpointTubeCurrent_boundary x y hCube)
    _ ≤ 72 := xyEndpointTubeBondEnergy_le x y hCube

end

end FroehlichSpencer.FS82.XY

end
