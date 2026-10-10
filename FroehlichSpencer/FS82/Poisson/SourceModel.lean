/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.SourceCarrier
public import FroehlichSpencer.FS82.Poisson.SourceTree
public import FroehlichSpencer.FS82.Poisson.GaugeCharacter
public import FroehlichSpencer.FS82.Poisson.QuadraticModel
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex

@[expose] public section

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Poisson

variable {B : Cubical.Box 4}

abbrev SourceV (B : Cubical.Box 4) := SourcePoissonVertex B
abbrev SourceE (B : Cubical.Box 4) := SourcePoissonEdge B

noncomputable def sourceTreeCoboundary (B : Cubical.Box 4)
    (p : SourceV B → ℝ) (e : SourceE B) : ℝ :=
  p (sourcePoissonEdgeUpperVertex e) - p (sourcePoissonEdgeLowerVertex e)

def sourceTreeZeroPotential (B : Cubical.Box 4)
    (u : EuclideanSpace ℝ (SourceDualZeroCells B)) : SourceV B → ℝ
  | none => 0
  | some v => u v

noncomputable def sourceTreeVertexPotential (B : Cubical.Box 4)
    (p : SourceV B → ℝ) : EuclideanSpace ℝ (SourceDualZeroCells B) :=
  finsuppToEuclidean (Finsupp.equivFunOnFinite.symm (fun v => p (some v)))

theorem sourceDualD0_single_eq_stencil
    (v : SourceDualZeroCells B) (e : SourceDualOneCells B) :
    sourceDualD₀ (finsuppToEuclidean (Finsupp.single v (1 : ℝ))) e =
      dualExteriorDifferenceStencilBasis v.1 e.1 := by
  rw [sourceDualD₀_coefficient]
  rw [dualExteriorDifference_eq_coordinateStencil]
  simp [sourceDualZeroToChain, sourceDualOneEmbedding,
    sourceDualZeroEmbedding, embedDualSubtype_eq_embDomain,
    dualExteriorDifferenceStencil, Finsupp.linearCombination_single]

theorem sourceDualD0_single_eq_faces
    (v : SourceDualZeroCells B) (e : SourceDualOneCells B) :
    sourceDualD₀ (finsuppToEuclidean (Finsupp.single v (1 : ℝ))) e =
      (-1 : ℝ) ^ (sourcePoissonEdgeAxis e).val *
        ((if e.1 = Cubical.dualUpperFace v.1 (sourcePoissonEdgeAxis e)
              (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) then 1 else 0) -
         (if e.1 = Cubical.dualLowerFace v.1 (sourcePoissonEdgeAxis e)
              (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) then 1 else 0)) := by
  rw [sourceDualD0_single_eq_stencil]
  let i := sourcePoissonEdgeAxis e
  let x := sourcePoissonVertexCoord v i
  have hrank : Cubical.dualVertexRankBefore v.1 i = i.val := by
    unfold Cubical.dualVertexRankBefore
    have hleft (j : Fin 4) : (v.1 j).isRight = false := by
      obtain ⟨n, hn⟩ := sourceDualZeroCell_axis_left v j
      rw [hn]
      rfl
    simp [hleft]
    change (Finset.univ.filter fun j : Fin 4 => j < i).card = i.val
    rw [show Finset.univ.filter (fun j : Fin 4 => j < i) = Finset.Iio i by
      ext j
      simp]
    simp
  have hsum :
      (∑ j : Fin 4, (match v.1 j with
        | Sum.inl a =>
            (-1 : ℝ) ^ Cubical.dualVertexRankBefore v.1 j •
              (Finsupp.single (Cubical.dualUpperFace v.1 j a) (1 : ℝ) -
                Finsupp.single (Cubical.dualLowerFace v.1 j a) (1 : ℝ))
        | Sum.inr _ => 0) e.1) =
      (match v.1 i with
        | Sum.inl a =>
            (-1 : ℝ) ^ Cubical.dualVertexRankBefore v.1 i •
              (Finsupp.single (Cubical.dualUpperFace v.1 i a) (1 : ℝ) -
                Finsupp.single (Cubical.dualLowerFace v.1 i a) (1 : ℝ))
        | Sum.inr _ => 0) e.1 := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      obtain ⟨n, hjleft⟩ := sourcePoissonEdge_otherCoord_left e hji
      have hUp : Cubical.dualUpperFace v.1 j
          (sourcePoissonVertexCoord v j) ≠ e.1 := by
        intro h
        have hh := congrFun h j
        rw [hjleft] at hh
        simp [Cubical.dualUpperFace] at hh
      have hLo : Cubical.dualLowerFace v.1 j
          (sourcePoissonVertexCoord v j) ≠ e.1 := by
        intro h
        have hh := congrFun h j
        rw [hjleft] at hh
        simp [Cubical.dualLowerFace] at hh
      simp [sourcePoissonVertexCoord_spec, hUp, hLo]
    · simp
  unfold Cubical.dualExteriorDifferenceStencilBasis
  rw [← Finsupp.lapply_apply (R := ℝ) (M := ℝ) e.1]
  rw [map_sum]
  simp only [Finsupp.lapply_apply]
  calc
    _ = (match v.1 i with
        | Sum.inl a =>
            (-1 : ℝ) ^ Cubical.dualVertexRankBefore v.1 i •
              (Finsupp.single (Cubical.dualUpperFace v.1 i a) (1 : ℝ) -
                Finsupp.single (Cubical.dualLowerFace v.1 i a) (1 : ℝ))
        | Sum.inr _ => 0) e.1 := by
      calc
        _ = ∑ j : Fin 4, (match v.1 j with
              | Sum.inl a =>
                  (-1 : ℝ) ^ Cubical.dualVertexRankBefore v.1 j •
                    (Finsupp.single (Cubical.dualUpperFace v.1 j a) (1 : ℝ) -
                      Finsupp.single (Cubical.dualLowerFace v.1 j a) (1 : ℝ))
              | Sum.inr _ => 0) e.1 := by
          apply Finset.sum_congr rfl
          intro j hj
          cases h : v.1 j <;> rfl
        _ = _ := hsum
    _ = _ := by
      rw [sourcePoissonVertexCoord_spec v i]
      simp [hrank, Finsupp.single_apply, eq_comm]
      simp only [i]

theorem sourcePoissonEdgeLowerVertex_face
    (e : SourceDualOneCells B) (v : SourceDualZeroCells B)
    (h : sourcePoissonEdgeLowerVertex e = some v) :
    e.1 = Cubical.dualUpperFace v.1 (sourcePoissonEdgeAxis e)
      (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) := by
  classical
  let i := sourcePoissonEdgeAxis e
  let k := sourcePoissonEdgeAxisIndex e
  have hi : i ∈ dualCellAxes e.1 := sourcePoissonEdgeAxis_mem e
  have hlt : k < B i + 1 := by
    simpa [i, k] using sourcePoissonEdgeAxisIndex_lt e
  have hk : k ≠ 0 := by
    intro hz
    have hnone : sourcePoissonEdgeLowerVertex e = none := by
      simp [sourcePoissonEdgeLowerVertex, k, hz]
    rw [hnone] at h
    cases h
  rw [sourcePoissonEdgeLowerVertex_of_index_ne_zero e hk] at h
  have hv : sourcePoissonVertexOfEdgeCoordAtAxis e i hi
      ⟨k - 1, by omega⟩ = v :=
    Option.some.inj h
  have hcoord : (sourcePoissonVertexCoord v i).val + 1 = k := by
    have hcoord' := sourcePoissonVertexCoord_ofEdgeCoordAtAxis e i hi
      ⟨k - 1, by omega⟩
    rw [hv] at hcoord'
    have hval := congrArg Fin.val hcoord'
    change (sourcePoissonVertexCoord v i).val = k - 1 at hval
    have hlt' : k < B i + 1 := hlt
    have hle : k ≤ B i := by omega
    have hx := (sourcePoissonVertexCoord v i).isLt
    omega
  funext j
  by_cases hji : j = i
  · subst j
    have hEdge := sourcePoissonEdgeAxisCoord_spec e
    have hfin :
        (⟨(sourcePoissonVertexCoord v i).val + 1,
          by have hx := (sourcePoissonVertexCoord v i).isLt; omega⟩ : Fin (B i + 1)) =
          ⟨k, sourcePoissonEdgeAxisIndex_lt e⟩ := by
      apply Fin.ext
      exact hcoord
    calc
      e.1 i = Sum.inr ⟨k, sourcePoissonEdgeAxisIndex_lt e⟩ := by
        simpa [i, k] using sourcePoissonEdgeAxisCoord_spec e
      _ = Sum.inr ⟨(sourcePoissonVertexCoord v i).val + 1,
          by have hx := (sourcePoissonVertexCoord v i).isLt; omega⟩ := by
        exact congrArg Sum.inr hfin.symm
      _ = Cubical.dualUpperFace v.1 i (sourcePoissonVertexCoord v i) i := by
        simp [Cubical.dualUpperFace]
  · have hdecoded := sourcePoissonVertexOfEdgeCoordAtAxis_apply_ne
      e i j hi ⟨k - 1, by omega⟩ hji
    rw [hv] at hdecoded
    have hface : Cubical.dualUpperFace v.1 i
        (sourcePoissonVertexCoord v i) j = v.1 j := by
      simp [Cubical.dualUpperFace, Function.update_of_ne hji]
    calc
      e.1 j = v.1 j := hdecoded.symm
      _ = Cubical.dualUpperFace v.1 i
          (sourcePoissonVertexCoord v i) j := hface.symm

theorem sourcePoissonEdgeLowerVertex_of_upperFace
    (e : SourceDualOneCells B) (v : SourceDualZeroCells B)
    (i : Fin 4)
    (h : e.1 = Cubical.dualUpperFace v.1 i (sourcePoissonVertexCoord v i)) :
    sourcePoissonEdgeLowerVertex e = some v := by
  classical
  let a := sourcePoissonEdgeAxis e
  let k := sourcePoissonEdgeAxisIndex e
  have ha : a = i := by
    have hr : (e.1 a).isRight := sourcePoissonEdgeAxis_isRight e
    have hr' : ((Cubical.dualUpperFace v.1 i (sourcePoissonVertexCoord v i)) a).isRight := by
      simpa [h] using hr
    by_contra hne
    have hleft := sourceDualZeroCell_axis_left v a
    obtain ⟨n, hn⟩ := hleft
    have hfalse : False := by
      simp [Cubical.dualUpperFace, Function.update_of_ne hne, hn] at hr'
    exact hfalse.elim
  have haxis : sourcePoissonEdgeAxis e = i := by simpa [a] using ha
  have hklt : k < B i + 1 := by
    cases haxis
    simpa [k] using sourcePoissonEdgeAxisIndex_lt e
  have hk : k = (sourcePoissonVertexCoord v i).val + 1 := by
    have hspec : e.1 i = Sum.inr ⟨k, hklt⟩ := by
      cases haxis
      simpa [k] using sourcePoissonEdgeAxisCoord_spec e
    have hcoord := congrFun h i
    rw [hspec] at hcoord
    simp only [Cubical.dualUpperFace, Function.update_self] at hcoord
    have hfin := Sum.inr.inj hcoord
    exact congrArg Fin.val hfin
  have hk0 : k ≠ 0 := by
    rw [hk]
    omega
  have hi : a ∈ dualCellAxes e.1 := sourcePoissonEdgeAxis_mem e
  have hn : k - 1 < B a := by
    have hlt : k < B a + 1 := by simpa [a, k] using sourcePoissonEdgeAxisIndex_lt e
    omega
  have hka : k = (sourcePoissonVertexCoord v a).val + 1 := by
    have htmp := hk
    rw [← haxis] at htmp
    exact htmp
  have hdecode : sourcePoissonVertexOfEdgeCoordAtAxis e a hi ⟨k - 1, hn⟩ = v := by
    apply Subtype.ext
    funext j
    by_cases hja : j = a
    · subst j
      rw [sourcePoissonVertexOfEdgeCoordAtAxis_apply_axis]
      rw [sourcePoissonVertexCoord_spec]
      congr 1
      apply Fin.ext
      change k - 1 = (sourcePoissonVertexCoord v a).val
      omega
    · rw [sourcePoissonVertexOfEdgeCoordAtAxis_apply_ne e a j hi ⟨k - 1, hn⟩ hja]
      have hji : j ≠ i := by
        intro hj
        apply hja
        change j = sourcePoissonEdgeAxis e
        rw [haxis]
        exact hj
      have hcoord := congrFun h j
      simpa [Cubical.dualUpperFace, Function.update_of_ne hji] using hcoord
  rw [sourcePoissonEdgeLowerVertex_of_index_ne_zero e (by simpa [k] using hk0)]
  apply congrArg some
  simpa [a, k] using hdecode

theorem sourcePoissonEdgeUpperVertex_of_index_ne_last
    (e : SourceDualOneCells B)
    (hk : sourcePoissonEdgeAxisIndex e ≠ B (sourcePoissonEdgeAxis e)) :
    sourcePoissonEdgeUpperVertex e = some (sourcePoissonVertexOfEdgeCoordAtAxis e
      (sourcePoissonEdgeAxis e) (sourcePoissonEdgeAxis_mem e)
      ⟨sourcePoissonEdgeAxisIndex e, by
        have hlt := sourcePoissonEdgeAxisIndex_lt e
        have hlt' : sourcePoissonEdgeAxisIndex e < B (sourcePoissonEdgeAxis e) := by omega
        exact hlt'⟩) := by
  simp [sourcePoissonEdgeUpperVertex, hk]

theorem sourcePoissonEdgeUpperVertex_face
    (e : SourceDualOneCells B) (v : SourceDualZeroCells B)
    (h : sourcePoissonEdgeUpperVertex e = some v) :
    e.1 = Cubical.dualLowerFace v.1 (sourcePoissonEdgeAxis e)
      (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) := by
  classical
  let i := sourcePoissonEdgeAxis e
  let k := sourcePoissonEdgeAxisIndex e
  have hk : k ≠ B i := by
    intro hlast
    have hnone : sourcePoissonEdgeUpperVertex e = none := by
      simp [sourcePoissonEdgeUpperVertex, i, k, hlast]
    rw [hnone] at h
    cases h
  have hkBound : k < B i := by
    have hlt : k < B i + 1 := by simpa [i, k] using sourcePoissonEdgeAxisIndex_lt e
    omega
  rw [sourcePoissonEdgeUpperVertex_of_index_ne_last e (by simpa [i, k] using hk)] at h
  have hv : sourcePoissonVertexOfEdgeCoordAtAxis e i (by simpa [i] using sourcePoissonEdgeAxis_mem e)
      ⟨k, by simpa [k] using hkBound⟩ = v :=
    Option.some.inj h
  have hcoord : (sourcePoissonVertexCoord v i).val = k := by
    have hcoord' := sourcePoissonVertexCoord_ofEdgeCoordAtAxis e i
      (by simpa [i] using sourcePoissonEdgeAxis_mem e)
      ⟨k, by simpa [k] using hkBound⟩
    rw [hv] at hcoord'
    exact congrArg Fin.val hcoord'
  funext j
  by_cases hji : j = i
  · subst j
    have hspec := sourcePoissonEdgeAxisCoord_spec e
    simpa [i, k, hcoord, Cubical.dualLowerFace] using hspec
  · have hdecoded := sourcePoissonVertexOfEdgeCoordAtAxis_apply_ne e i j
      (by simpa [i] using sourcePoissonEdgeAxis_mem e)
      ⟨k, by simpa [k] using hkBound⟩ hji
    rw [hv] at hdecoded
    have hface : Cubical.dualLowerFace v.1 i (sourcePoissonVertexCoord v i) j = v.1 j := by
      simp [Cubical.dualLowerFace, Function.update_of_ne hji]
    simpa [i] using (calc
      e.1 j = v.1 j := hdecoded.symm
      _ = Cubical.dualLowerFace v.1 i (sourcePoissonVertexCoord v i) j := hface.symm)

theorem sourcePoissonEdgeUpperVertex_of_lowerFace
    (e : SourceDualOneCells B) (v : SourceDualZeroCells B)
    (i : Fin 4)
    (h : e.1 = Cubical.dualLowerFace v.1 i (sourcePoissonVertexCoord v i)) :
    sourcePoissonEdgeUpperVertex e = some v := by
  classical
  let a := sourcePoissonEdgeAxis e
  let k := sourcePoissonEdgeAxisIndex e
  have ha : a = i := by
    have hr : (e.1 a).isRight := sourcePoissonEdgeAxis_isRight e
    have hr' : ((Cubical.dualLowerFace v.1 i (sourcePoissonVertexCoord v i)) a).isRight := by
      simpa [h] using hr
    by_contra hne
    obtain ⟨n, hn⟩ := sourceDualZeroCell_axis_left v a
    have hfalse : False := by
      simp [Cubical.dualLowerFace, Function.update, hne, hn] at hr'
    exact hfalse.elim
  have haxis : sourcePoissonEdgeAxis e = i := by simpa [a] using ha
  have hklt : k < B i + 1 := by
    cases haxis
    simpa [k] using sourcePoissonEdgeAxisIndex_lt e
  have hk : k = (sourcePoissonVertexCoord v i).val := by
    have hspec : e.1 i = Sum.inr ⟨k, hklt⟩ := by
      cases haxis
      simpa [k] using sourcePoissonEdgeAxisCoord_spec e
    have hcoord := congrFun h i
    rw [hspec] at hcoord
    simp only [Cubical.dualLowerFace, Function.update_self] at hcoord
    exact congrArg Fin.val (Sum.inr.inj hcoord)
  have hkLast : k ≠ B i := by
    rw [hk]
    exact ne_of_lt (sourcePoissonVertexCoord v i).isLt
  have hi : a ∈ dualCellAxes e.1 := sourcePoissonEdgeAxis_mem e
  have hka : k = (sourcePoissonVertexCoord v a).val := by
    have htmp := hk
    rw [← haxis] at htmp
    exact htmp
  have hbound : k < B i := by
    have hlt := hklt
    omega
  have hboundA : k < B a := by simpa [a, haxis] using hbound
  have hdecode : sourcePoissonVertexOfEdgeCoordAtAxis e a hi ⟨k, hboundA⟩ = v := by
    apply Subtype.ext
    funext j
    by_cases hja : j = a
    · subst j
      rw [sourcePoissonVertexOfEdgeCoordAtAxis_apply_axis]
      rw [sourcePoissonVertexCoord_spec]
      apply congrArg Sum.inl
      apply Fin.ext
      exact hka
    · rw [sourcePoissonVertexOfEdgeCoordAtAxis_apply_ne e a j hi ⟨k, hboundA⟩ hja]
      have hji : j ≠ i := by
        intro hj
        apply hja
        change j = sourcePoissonEdgeAxis e
        rw [haxis]
        exact hj
      have hcoord := congrFun h j
      simpa [Cubical.dualLowerFace, Function.update_of_ne hji] using hcoord
  rw [sourcePoissonEdgeUpperVertex_of_index_ne_last e (by simpa [k, haxis.symm] using hkLast)]
  apply congrArg some
  simpa [a, k] using hdecode

theorem sourcePoisson_upperFace_iff_lowerVertex
    (e : SourceDualOneCells B) (v : SourceDualZeroCells B) :
    e.1 = Cubical.dualUpperFace v.1 (sourcePoissonEdgeAxis e)
        (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) ↔
      sourcePoissonEdgeLowerVertex e = some v := by
  constructor
  · intro h
    exact sourcePoissonEdgeLowerVertex_of_upperFace e v (sourcePoissonEdgeAxis e) h
  · exact sourcePoissonEdgeLowerVertex_face e v

theorem sourcePoisson_lowerFace_iff_upperVertex
    (e : SourceDualOneCells B) (v : SourceDualZeroCells B) :
    e.1 = Cubical.dualLowerFace v.1 (sourcePoissonEdgeAxis e)
        (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) ↔
      sourcePoissonEdgeUpperVertex e = some v := by
  constructor
  · intro h
    exact sourcePoissonEdgeUpperVertex_of_lowerFace e v (sourcePoissonEdgeAxis e) h
  · exact sourcePoissonEdgeUpperVertex_face e v

private theorem sum_upperFace_values
    (u : EuclideanSpace ℝ (SourceDualZeroCells B)) (e : SourceDualOneCells B) :
    (∑ v : SourceDualZeroCells B,
      if e.1 = Cubical.dualUpperFace v.1 (sourcePoissonEdgeAxis e)
          (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) then u v else 0) =
      sourceTreeZeroPotential B u (sourcePoissonEdgeLowerVertex e) := by
  classical
  cases hL : sourcePoissonEdgeLowerVertex e with
  | none =>
      simp only [sourceTreeZeroPotential.eq_def]
      apply Finset.sum_eq_zero
      intro v hv
      split_ifs with hface
      · have hend := (sourcePoisson_upperFace_iff_lowerVertex e v).mp hface
        rw [hL] at hend
        cases hend
      · rfl
  | some v₀ =>
      simp only [sourceTreeZeroPotential.eq_def]
      rw [Finset.sum_eq_single v₀]
      · have hface := (sourcePoisson_upperFace_iff_lowerVertex e v₀).mpr hL
        simp [hface]
      · intro v hv hvne
        have hnot : e.1 ≠ Cubical.dualUpperFace v.1 (sourcePoissonEdgeAxis e)
            (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) := by
          intro hface
          have hend := (sourcePoisson_upperFace_iff_lowerVertex e v).mp hface
          rw [hL] at hend
          have hvEq : v = v₀ := (Option.some.inj hend).symm
          exact hvne hvEq
        simp [hnot]
      · intro hnot
        exact (hnot (Finset.mem_univ v₀)).elim

private theorem sum_lowerFace_values
    (u : EuclideanSpace ℝ (SourceDualZeroCells B)) (e : SourceDualOneCells B) :
    (∑ v : SourceDualZeroCells B,
      if e.1 = Cubical.dualLowerFace v.1 (sourcePoissonEdgeAxis e)
          (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) then u v else 0) =
      sourceTreeZeroPotential B u (sourcePoissonEdgeUpperVertex e) := by
  classical
  cases hU : sourcePoissonEdgeUpperVertex e with
  | none =>
      simp only [sourceTreeZeroPotential.eq_def]
      apply Finset.sum_eq_zero
      intro v hv
      split_ifs with hface
      · have hend := (sourcePoisson_lowerFace_iff_upperVertex e v).mp hface
        rw [hU] at hend
        cases hend
      · rfl
  | some v₀ =>
      simp only [sourceTreeZeroPotential.eq_def]
      rw [Finset.sum_eq_single v₀]
      · have hface := (sourcePoisson_lowerFace_iff_upperVertex e v₀).mpr hU
        simp [hface]
      · intro v hv hvne
        have hnot : e.1 ≠ Cubical.dualLowerFace v.1 (sourcePoissonEdgeAxis e)
            (sourcePoissonVertexCoord v (sourcePoissonEdgeAxis e)) := by
          intro hface
          have hend := (sourcePoisson_lowerFace_iff_upperVertex e v).mp hface
          rw [hU] at hend
          have hvEq : v = v₀ := (Option.some.inj hend).symm
          exact hvne hvEq
        simp [hnot]
      · intro hnot
        exact (hnot (Finset.mem_univ v₀)).elim

private theorem sourcePoissonEdgeAxes_singleton (e : SourceDualOneCells B) :
    dualCellAxes e.1 = {sourcePoissonEdgeAxis e} := by
  classical
  ext i
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hi
    exact sourcePoissonEdgeAxis_unique e
      (by simpa [dualCellAxes] using hi)
      (sourcePoissonEdgeAxis_isRight e)
  · intro h
    subst i
    exact sourcePoissonEdgeAxis_isRight e

private theorem sourcePoissonEdgeOrientationSign (e : SourceDualOneCells B) :
    Gaussian.dualCellOrientationSign e.1 =
      (-1 : ℝ) ^ ((sourcePoissonEdgeAxis e).val + 1) := by
  rw [Gaussian.dualCellOrientationSign, Gaussian.axisSetOrientationSign,
    sourcePoissonEdgeAxes_singleton]
  simp

private theorem sourceDualEuclidean_single (v : SourceDualZeroCells B) :
    finsuppToEuclidean (Finsupp.single v (1 : ℝ)) = EuclideanSpace.single v 1 := by
  ext w
  simp [finsuppToEuclidean, EuclideanSpace.single]

private theorem sourceDualEuclidean_sum_single
    (u : EuclideanSpace ℝ (SourceDualZeroCells B)) :
    u = ∑ v : SourceDualZeroCells B,
      u v • finsuppToEuclidean (Finsupp.single v (1 : ℝ)) := by
  have h := (EuclideanSpace.basisFun (SourceDualZeroCells B) ℝ).sum_repr u
  calc
    u = ∑ v : SourceDualZeroCells B, u v • EuclideanSpace.single v 1 := by
      simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using h.symm
    _ = ∑ v : SourceDualZeroCells B,
        u v • finsuppToEuclidean (Finsupp.single v (1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [sourceDualEuclidean_single]

theorem sourceDualT_D0_eq_treeCoboundary
    (u : EuclideanSpace ℝ (SourceDualZeroCells B)) (e : SourceDualOneCells B) :
    Gaussian.sourceDualTLinear (sourceDualD₀ u) e =
      sourceTreeCoboundary B (sourceTreeZeroPotential B u) e := by
  classical
  let i := sourcePoissonEdgeAxis e
  have hlin : sourceDualD₀ u e =
      ∑ v : SourceDualZeroCells B, u v *
        sourceDualD₀ (finsuppToEuclidean (Finsupp.single v (1 : ℝ))) e := by
    have hsum := congrArg sourceDualD₀ (sourceDualEuclidean_sum_single u)
    simp only [map_sum, map_smul] at hsum
    have hEval := congrArg (fun z : EuclideanSpace ℝ (SourceDualOneCells B) => z e) hsum
    simpa [PiLp.smul_apply, smul_eq_mul] using hEval
  have hD0 : sourceDualD₀ u e =
      (-1 : ℝ) ^ i.val *
        (sourceTreeZeroPotential B u (sourcePoissonEdgeLowerVertex e) -
          sourceTreeZeroPotential B u (sourcePoissonEdgeUpperVertex e)) := by
    rw [hlin]
    calc
      (∑ v : SourceDualZeroCells B, u v *
          sourceDualD₀ (finsuppToEuclidean (Finsupp.single v (1 : ℝ))) e) =
          ∑ v : SourceDualZeroCells B, u v *
            ((-1 : ℝ) ^ i.val *
              ((if e.1 = Cubical.dualUpperFace v.1 i (sourcePoissonVertexCoord v i)
                  then 1 else 0) -
               (if e.1 = Cubical.dualLowerFace v.1 i (sourcePoissonVertexCoord v i)
                  then 1 else 0))) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [sourceDualD0_single_eq_faces]
      _ = (-1 : ℝ) ^ i.val *
          ((∑ v : SourceDualZeroCells B,
              if e.1 = Cubical.dualUpperFace v.1 i (sourcePoissonVertexCoord v i)
                then u v else 0) -
           ∑ v : SourceDualZeroCells B,
              if e.1 = Cubical.dualLowerFace v.1 i (sourcePoissonVertexCoord v i)
                then u v else 0) := by
        calc
          _ = ∑ v : SourceDualZeroCells B, (-1 : ℝ) ^ i.val *
              ((if e.1 = Cubical.dualUpperFace v.1 i (sourcePoissonVertexCoord v i)
                  then u v else 0) -
               (if e.1 = Cubical.dualLowerFace v.1 i (sourcePoissonVertexCoord v i)
                  then u v else 0)) := by
            apply Finset.sum_congr rfl
            intro v hv
            split_ifs <;> ring
          _ = _ := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      _ = _ := by rw [sum_upperFace_values, sum_lowerFace_values]
  have hsign : (-1 : ℝ) ^ (i.val + 1) * (-1 : ℝ) ^ i.val = -1 := by
    rw [pow_add]
    have hsquare : ((-1 : ℝ) ^ i.val) ^ 2 = 1 := by
      rcases Nat.even_or_odd i.val with he | ho
      · have hpow : (-1 : ℝ) ^ i.val = 1 := he.neg_one_pow
        rw [hpow]
        norm_num
      · have hpow : (-1 : ℝ) ^ i.val = -1 := ho.neg_one_pow
        rw [hpow]
        norm_num
    calc
      ((-1 : ℝ) ^ i.val * (-1 : ℝ) ^ 1) * (-1 : ℝ) ^ i.val =
          -((( -1 : ℝ) ^ i.val) ^ 2) := by ring
      _ = -1 := by rw [hsquare]
  rw [Gaussian.sourceDualTLinear_apply, sourcePoissonEdgeOrientationSign,
    hD0]
  unfold sourceTreeCoboundary
  rw [show i = sourcePoissonEdgeAxis e by rfl]
  calc
    (-1 : ℝ) ^ (i.val + 1) *
        ((-1 : ℝ) ^ i.val *
          (sourceTreeZeroPotential B u (sourcePoissonEdgeLowerVertex e) -
            sourceTreeZeroPotential B u (sourcePoissonEdgeUpperVertex e))) =
        sourceTreeZeroPotential B u (sourcePoissonEdgeUpperVertex e) -
          sourceTreeZeroPotential B u (sourcePoissonEdgeLowerVertex e) := by
      rw [← mul_assoc, hsign]
      ring
    _ = _ := rfl

@[simp] theorem sourceTreeZeroPotential_vertexPotential
    (p : SourcePoissonVertex B → ℝ) (v : SourceDualZeroCells B) :
    sourceTreeZeroPotential B (sourceTreeVertexPotential B p) (some v) = p (some v) := by
  simp [sourceTreeZeroPotential, sourceTreeVertexPotential,
    finsuppToEuclidean_apply, Finsupp.equivFunOnFinite_symm_apply_apply]

noncomputable def sourceNormalizePotential (p : SourcePoissonVertex B → ℝ) :
    SourcePoissonVertex B → ℝ := fun x => p x - p none

theorem sourceTreeVertexPotential_normalize (p : SourcePoissonVertex B → ℝ) :
    sourceTreeZeroPotential B
      (sourceTreeVertexPotential B (sourceNormalizePotential p)) =
      sourceNormalizePotential p := by
  funext x
  cases x with
  | none => simp [sourceTreeZeroPotential, sourceNormalizePotential]
  | some v => simp [sourceTreeZeroPotential_vertexPotential, sourceNormalizePotential]

theorem sourceTreeCoboundary_normalize (p : SourcePoissonVertex B → ℝ)
    (e : SourcePoissonEdge B) :
    sourceTreeCoboundary B (sourceNormalizePotential p) e =
      sourceTreeCoboundary B p e := by
  unfold sourceTreeCoboundary sourceNormalizePotential
  ring

noncomputable def sourceGraphField (p : SourcePoissonVertex B → ℝ) :
    EuclideanSpace ℝ (SourceDualOneCells B) :=
  WithLp.toLp 2 (fun e => sourceTreeCoboundary B p e)

theorem sourceLatticeD0_eq_sourceGraphField
    (origin : Fin 4 → ℤ) (u : EuclideanSpace ℝ (SourceDualZeroCells B)) :
    (Gaussian.latticeExactOneComplex (B := B) origin).d₀ u =
      sourceGraphField (sourceTreeZeroPotential B u) := by
  ext e
  change Gaussian.sourceDualTLinear (sourceDualD₀ u) e =
    sourceTreeCoboundary B (sourceTreeZeroPotential B u) e
  exact sourceDualT_D0_eq_treeCoboundary u e

theorem sourceLatticeD0_range_eq_treeCoboundary
    (origin : Fin 4 → ℤ) (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    (∃ u, (Gaussian.latticeExactOneComplex (B := B) origin).d₀ u = x) ↔
      ∃ p : SourcePoissonVertex B → ℝ,
        ∀ e, sourceTreeCoboundary B p e = x e := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨sourceTreeZeroPotential B u, ?_⟩
    intro e
    have hfield := congrArg (fun y : EuclideanSpace ℝ (SourceDualOneCells B) => y e)
      (sourceLatticeD0_eq_sourceGraphField (B := B) origin u)
    have hx := congrArg (fun y : EuclideanSpace ℝ (SourceDualOneCells B) => y e) hu
    simpa [sourceGraphField] using hfield.symm.trans hx
  · rintro ⟨p, hp⟩
    let p₀ := sourceNormalizePotential p
    let u := sourceTreeVertexPotential B p₀
    refine ⟨u, ?_⟩
    ext e
    have hfield := congrArg (fun y : EuclideanSpace ℝ (SourceDualOneCells B) => y e)
      (sourceLatticeD0_eq_sourceGraphField (B := B) origin u)
    simp only [sourceGraphField, u, p₀, sourceTreeVertexPotential_normalize] at hfield
    rw [sourceTreeCoboundary_normalize] at hfield
    have hp' := hp e
    exact hfield.trans hp'

theorem sourceLatticeStencil_kernel_iff_D0_range
    (origin : Fin 4 → ℤ) (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    Gaussian.latticeStencilOperator origin x = 0 ↔
      ∃ u : EuclideanSpace ℝ (SourceDualZeroCells B),
        (Gaussian.latticeExactOneComplex (B := B) origin).d₀ u = x := by
  let C := Gaussian.latticeExactOneComplex (B := B) origin
  rw [← Gaussian.latticeFormLaplacian_eq_stencil origin]
  constructor
  · intro hx
    have hxker : x ∈ (Gaussian.formLaplacian C).ker := LinearMap.mem_ker.mpr hx
    rw [Gaussian.formLaplacian, LinearMap.ker_adjoint_comp_self] at hxker
    exact C.exactOne hxker
  · rintro ⟨u, hu⟩
    have hcomplex : C.d₁ (C.d₀ u) = 0 := by
      have h := congrArg (fun F : EuclideanSpace ℝ (SourceDualZeroCells B) →ₗ[ℝ]
          EuclideanSpace ℝ (Gaussian.SourceDualTwoCells B) => F u) C.complex
      simpa [LinearMap.comp_apply] using h
    have hx : C.d₁ x = 0 := by rw [← hu, hcomplex]
    rw [Gaussian.formLaplacian]
    change C.d₁.adjoint (C.d₁ x) = 0
    rw [hx]
    simp

noncomputable def sourcePoissonMatrix (origin : Fin 4 → ℤ) :
    Matrix (SourceDualOneCells B) (SourceDualOneCells B) ℝ :=
  Gaussian.matrixOfLinearMap (sourcePoissonHodge (B := B) origin)


theorem sourcePoissonMatrix_mulVec (origin : Fin 4 → ℤ)
    (x : SourceDualOneCells B → ℝ) :
    (sourcePoissonMatrix (B := B) origin).mulVec x =
      (Gaussian.latticeStencilOperator origin (WithLp.toLp 2 x)).ofLp := by
  rw [sourcePoissonMatrix, sourcePoissonHodge_eq_stencil]
  simpa using
    (Gaussian.matrixOfLinearMap_mulVec (Gaussian.latticeStencilOperator origin)
      (WithLp.toLp 2 x))

noncomputable def sourceFinitePoissonModel (origin : Fin 4 → ℤ) :
    FinitePoissonModel (sourceRootedTree B) := by
  classical
  let C := Gaussian.latticeExactOneComplex (B := B) origin
  refine ⟨sourcePoissonMatrix origin, ?_, ?_⟩
  · apply Gaussian.matrixOfLinearMap_posSemidef
    · intro x y
      rw [sourcePoissonHodge_eq_stencil,
        ← Gaussian.latticeFormLaplacian_eq_stencil origin]
      exact LinearMap.isSymmetric_adjoint_comp_self C.d₁ x y
    · intro x
      rw [sourcePoissonHodge_eq_stencil,
        ← Gaussian.latticeFormLaplacian_eq_stencil origin]
      have h := Gaussian.formLaplacian_inner_nonneg C x
      rw [real_inner_comm]
      exact h
  · intro x
    change (sourcePoissonMatrix origin).mulVec x = 0 ↔
      ∃ p : SourcePoissonVertex B → ℝ, ∀ e,
        RootedTreeGauge.coboundary (sourceRootedTree B) p e = x e
    rw [sourcePoissonMatrix_mulVec]
    rw [WithLp.ofLp_eq_zero]
    rw [sourceLatticeStencil_kernel_iff_D0_range]
    change (∃ u : EuclideanSpace ℝ (SourceDualZeroCells B),
        (Gaussian.latticeExactOneComplex (B := B) origin).d₀ u = WithLp.toLp 2 x) ↔
      ∃ p : SourcePoissonVertex B → ℝ, ∀ e,
        sourceTreeCoboundary B p e = x e
    exact sourceLatticeD0_range_eq_treeCoboundary (B := B) origin
      (WithLp.toLp 2 x)


noncomputable def sourceFiniteModelTestedExpectation
    (origin : Fin 4 → ℤ) (β : ℝ)
    (τ : (sourceRootedTree B).Chord → ℝ) (t : ℝ) : ℂ :=
  finiteModelTestedExpectation (sourceRootedTree B)
    (sourceFinitePoissonModel (B := B) origin) β τ t


theorem source_hOuterMoment
    (origin : Fin 4 → ℤ) {β : ℝ} (hβ : 0 < β)
    (τ : (sourceRootedTree B).Chord → ℝ) (t : ℝ)
    (z : ℕ → ℝ) (hnorm : HasSum (inactiveWeight z) 1)
    (hweight : ∀ q, 0 ≤ inactiveWeight z q) :
    sourceFiniteModelTestedExpectation (B := B) origin β τ t =
      (∑' b : GaugeCharacterBranch (sourceRootedTree B),
        (gaugeBranchMass (sourceRootedTree B)
          (scaledChordMatrix (sourceRootedTree B)
            (sourceFinitePoissonModel (B := B) origin) β) z b : ℂ) *
          gaugeBranchMoment (sourceRootedTree B)
            (scaledChordMatrix (sourceRootedTree B)
              (sourceFinitePoissonModel (B := B) origin) β) τ t b) /
      (xi (scaledChordMatrix (sourceRootedTree B)
        (sourceFinitePoissonModel (B := B) origin) β) : ℂ) := by
  exact gauge_hOuterMoment_of_model (sourceRootedTree B)
    (scaledChordMatrix (sourceRootedTree B)
      (sourceFinitePoissonModel (B := B) origin) β)
    (scaledChordMatrix_posDef (sourceRootedTree B)
      (sourceFinitePoissonModel (B := B) origin) hβ)
    τ t z hnorm hweight


end FroehlichSpencer.FS82.Poisson

end
