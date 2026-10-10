/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex

public section
namespace FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical

@[expose] noncomputable def dualExteriorDifferenceAxisStencilBasis {B : SourceBox}
    (i : Fin 4) (c : DualCell 4 B) : DualRealChain 4 B :=
  match c i with
  | Sum.inl v =>
      ((-1 : ℝ) ^ dualVertexRankBefore c i) •
        (Finsupp.single (dualUpperFace c i v) 1 -
          Finsupp.single (dualLowerFace c i v) 1)
  | Sum.inr _ => 0

@[expose] noncomputable def dualExteriorDifferenceAxis {B : SourceBox} (i : Fin 4) :
    DualRealChain 4 B →ₗ[ℝ] DualRealChain 4 B :=
  Finsupp.linearCombination ℝ (dualExteriorDifferenceAxisStencilBasis i)

theorem dualExteriorDifferenceStencilBasis_eq_sum_axis {B : SourceBox}
    (c : DualCell 4 B) :
    dualExteriorDifferenceStencilBasis c =
      ∑ i : Fin 4, dualExteriorDifferenceAxisStencilBasis i c := by
  unfold dualExteriorDifferenceStencilBasis
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i <;> simp [dualExteriorDifferenceAxisStencilBasis, hci]

theorem dualExteriorDifferenceStencil_eq_sum_axis (B : SourceBox) :
    dualExteriorDifferenceStencil (B := B) =
      ∑ i : Fin 4, dualExteriorDifferenceAxis (B := B) i := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp [map_add, hq, hr]
  | single c a =>
      simp [dualExteriorDifferenceStencil, dualExteriorDifferenceAxis,
        dualExteriorDifferenceStencilBasis_eq_sum_axis,
        dualExteriorDifferenceAxisStencilBasis, Finsupp.linearCombination_single,
        Finset.smul_sum]

theorem dualVertexRankBefore_update_edge_axis {B : SourceBox}
    (c : DualCell 4 B) (i j : Fin 4) (w : Fin (B j + 1))
    (hcj : ∃ v : Fin (B j), c j = Sum.inl v) :
    dualVertexRankBefore (Function.update c j (Sum.inr w)) i =
      if j < i then dualVertexRankBefore c i - 1 else dualVertexRankBefore c i := by
  unfold dualVertexRankBefore
  let S : Finset (Fin 4) :=
    Finset.univ.filter fun k => k < i ∧ ¬ (c k).isRight = true
  have hS :
      Finset.univ.filter
          (fun k : Fin 4 => k < i ∧ ¬ ((Function.update c j (Sum.inr w)) k).isRight = true) =
        if j < i then S.erase j else S := by
    ext k
    by_cases hkj : k = j
    · subst k
      obtain ⟨v, hv⟩ := hcj
      by_cases hj : j < i <;>
        simp [S, Function.update_self, hj, hv]
    · cases hck : c k <;> by_cases hj : j < i <;>
        simp [S, hkj, hck, hj]
  rw [hS]
  split_ifs with h
  · obtain ⟨v, hv⟩ := hcj
    have hjS : j ∈ S := by simp [S, h, hv]
    rw [Finset.card_erase_of_mem hjS]
  · rfl

theorem dualVertexRankBefore_update_edge_sign {B : SourceBox}
    (c : DualCell 4 B) (i j : Fin 4) (w : Fin (B j + 1))
    (hcj : ∃ v : Fin (B j), c j = Sum.inl v) :
    (-1 : ℝ) ^ dualVertexRankBefore (Function.update c j (Sum.inr w)) i =
      if j < i then -((-1 : ℝ) ^ dualVertexRankBefore c i)
      else (-1 : ℝ) ^ dualVertexRankBefore c i := by
  by_cases hj : j < i
  · obtain ⟨v, hv⟩ := hcj
    have hr : dualVertexRankBefore (Function.update c j (Sum.inr w)) i =
        dualVertexRankBefore c i - 1 := by
      simpa [hj] using dualVertexRankBefore_update_edge_axis c i j w ⟨v, hv⟩
    have hpos : 0 < dualVertexRankBefore c i := by
      unfold dualVertexRankBefore
      apply Finset.card_pos.mpr
      refine ⟨j, ?_⟩
      simp [hj, hv]
    have hn : dualVertexRankBefore c i - 1 + 1 = dualVertexRankBefore c i := by omega
    have hpow : (-1 : ℝ) ^ dualVertexRankBefore c i =
        (-1 : ℝ) ^ (dualVertexRankBefore c i - 1) * (-1 : ℝ) := by
      calc
        (-1 : ℝ) ^ dualVertexRankBefore c i =
            (-1 : ℝ) ^ (dualVertexRankBefore c i - 1 + 1) := by
          congr 1
          omega
        _ = (-1 : ℝ) ^ (dualVertexRankBefore c i - 1) * (-1 : ℝ) := by
          rw [pow_succ]
    simp [hj, hr]
    rw [hpow]
    ring
  · have hr : dualVertexRankBefore (Function.update c j (Sum.inr w)) i =
        dualVertexRankBefore c i := by
      simpa [hj] using dualVertexRankBefore_update_edge_axis c i j w hcj
    simp [hj, hr]


theorem dualVertexRankBefore_update_vertex_sign {B : SourceBox}
    (c : DualCell 4 B) (i j : Fin 4) (v : Fin (B i))
    (w : Fin (B i + 1)) (hci : c i = Sum.inr w) :
    (-1 : ℝ) ^ dualVertexRankBefore (Function.update c i (Sum.inl v)) j =
      if i < j then -((-1 : ℝ) ^ dualVertexRankBefore c j)
      else (-1 : ℝ) ^ dualVertexRankBefore c j := by
  have h := dualVertexRankBefore_update_edge_sign
    (Function.update c i (Sum.inl v)) j i w ⟨v, by simp⟩
  have hupd : Function.update (Function.update c i (Sum.inl v)) i (Sum.inr w) = c := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [hci]
    · simp [hki]
  rw [hupd] at h
  by_cases hij : i < j
  · simp [hij] at h ⊢
    linarith
  · simp [hij] at h ⊢
    linarith

@[simp] theorem dualExteriorDifferenceAxis_single {B : SourceBox}
    (i : Fin 4) (c : DualCell 4 B) :
    dualExteriorDifferenceAxis (B := B) i
        (Finsupp.single c (1 : ℝ) : DualRealChain 4 B) =
      dualExteriorDifferenceAxisStencilBasis i c := by
  simp [dualExteriorDifferenceAxis, Finsupp.linearCombination_single]

@[simp] theorem dualExteriorDifferenceAxis_single_smul {B : SourceBox}
    (i : Fin 4) (c : DualCell 4 B) (a : ℝ) :
    dualExteriorDifferenceAxis (B := B) i
        (Finsupp.single c a : DualRealChain 4 B) =
      a • dualExteriorDifferenceAxisStencilBasis i c := by
  simp [dualExteriorDifferenceAxis, Finsupp.linearCombination_single]


@[expose] noncomputable def dualExteriorDifferenceAxisAdjointStencilBasis
    {B : SourceBox} (i : Fin 4) (c : DualCell 4 B) : DualRealChain 4 B :=
  match c i with
  | Sum.inl _ => 0
  | Sum.inr e =>
      ((-1 : ℝ) ^ dualVertexRankBefore c i) •
        ((if h : 0 < e.val then
            Finsupp.single
              (Function.update c i (Sum.inl ⟨e.val - 1, by omega⟩)) (1 : ℝ)
          else 0) -
         (if h : e.val < B i then
            Finsupp.single
              (Function.update c i (Sum.inl ⟨e.val, h⟩)) (1 : ℝ)
         else 0))


theorem dualVertexRankBefore_eq_of_eq_off_axis {B : SourceBox}
    (x y : DualCell 4 B) (i : Fin 4)
    (hoff : ∀ k, k ≠ i → x k = y k) :
    dualVertexRankBefore x i = dualVertexRankBefore y i := by
  unfold dualVertexRankBefore
  congr 1
  ext k
  by_cases hki : k = i
  · simp [hki]
  · simp [hoff k hki]

@[expose] noncomputable def dualExteriorDifferenceAxisAdjoint
    {B : SourceBox} (i : Fin 4) : DualRealChain 4 B →ₗ[ℝ] DualRealChain 4 B :=
  Finsupp.linearCombination ℝ (dualExteriorDifferenceAxisAdjointStencilBasis i)

@[simp] theorem dualExteriorDifferenceAxisAdjoint_single {B : SourceBox}
    (i : Fin 4) (c : DualCell 4 B) :
    dualExteriorDifferenceAxisAdjoint (B := B) i
        (Finsupp.single c (1 : ℝ) : DualRealChain 4 B) =
      dualExteriorDifferenceAxisAdjointStencilBasis i c := by
  simp [dualExteriorDifferenceAxisAdjoint, Finsupp.linearCombination_single]

@[simp] theorem dualExteriorDifferenceAxisAdjoint_single_smul {B : SourceBox}
    (i : Fin 4) (c : DualCell 4 B) (a : ℝ) :
    dualExteriorDifferenceAxisAdjoint (B := B) i
        (Finsupp.single c a : DualRealChain 4 B) =
      a • dualExteriorDifferenceAxisAdjointStencilBasis i c := by
  simp [dualExteriorDifferenceAxisAdjoint, Finsupp.linearCombination_single]

theorem dualExteriorDifferenceAxisAdjoint_comp_anticommute_basis
    {B : SourceBox} (i j : Fin 4) (hij : i ≠ j) (c : DualCell 4 B) :
    dualExteriorDifferenceAxisAdjoint (B := B) i
        (dualExteriorDifferenceAxis (B := B) j
          (Finsupp.single c (1 : ℝ))) +
      dualExteriorDifferenceAxis (B := B) j
        (dualExteriorDifferenceAxisAdjoint (B := B) i
          (Finsupp.single c (1 : ℝ))) = 0 := by
  classical
  rw [dualExteriorDifferenceAxis_single,
    dualExteriorDifferenceAxisAdjoint_single]
  cases hci : c i with
  | inl vi =>
      cases hcj : c j with
      | inl vj =>
          simp [dualExteriorDifferenceAxisStencilBasis,
            dualExteriorDifferenceAxisAdjointStencilBasis, hci, hcj,
            dualUpperFace, dualLowerFace,
            Function.update_of_ne hij]
      | inr wj =>
          simp [dualExteriorDifferenceAxisStencilBasis,
            dualExteriorDifferenceAxisAdjointStencilBasis, hci, hcj]
  | inr wi =>
      cases hcj : c j with
      | inr wj =>
          by_cases hp : 0 < wi.val <;>
            by_cases hc : wi.val < B i <;>
            simp [dualExteriorDifferenceAxisStencilBasis,
              dualExteriorDifferenceAxisAdjointStencilBasis, hci, hcj,
              Function.update_of_ne hij.symm, hp, hc]
      | inl vj =>
          by_cases hp : 0 < wi.val <;>
            by_cases hc : wi.val < B i <;>
            all_goals
              by_cases horder : i < j
              · have hnot : ¬ j < i := by omega
                simp [dualExteriorDifferenceAxisStencilBasis,
                  dualExteriorDifferenceAxisAdjointStencilBasis, hci, hcj,
                  dualUpperFace, dualLowerFace, Function.update_comm hij,
                  Function.update_of_ne hij, Function.update_of_ne hij.symm,
                  dualVertexRankBefore_update_edge_sign,
                  dualVertexRankBefore_update_vertex_sign,
                  hp, hc, horder, hnot]
                all_goals
                  ext z
                  simp [Finsupp.single_apply]
                  split_ifs <;> ring
              · have horder' : j < i := by omega
                have hnot : ¬ i < j := by omega
                simp [dualExteriorDifferenceAxisStencilBasis,
                  dualExteriorDifferenceAxisAdjointStencilBasis, hci, hcj,
                  dualUpperFace, dualLowerFace, Function.update_comm hij,
                  Function.update_of_ne hij, Function.update_of_ne hij.symm,
                  dualVertexRankBefore_update_edge_sign,
                  dualVertexRankBefore_update_vertex_sign,
                  hp, hc, horder', hnot]
                all_goals
                  ext z
                  simp [Finsupp.single_apply]
                  split_ifs <;> ring

theorem dualExteriorDifferenceAxisAdjoint_comp_anticommute
    {B : SourceBox} (i j : Fin 4) (hij : i ≠ j) :
    (dualExteriorDifferenceAxisAdjoint (B := B) i).comp
        (dualExteriorDifferenceAxis (B := B) j) +
      (dualExteriorDifferenceAxis (B := B) j).comp
        (dualExteriorDifferenceAxisAdjoint (B := B) i) = 0 := by
  classical
  apply LinearMap.ext
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add, hq, hr]
  | single c a =>
      have hs : (Finsupp.single c a : DualRealChain 4 B) =
          a • Finsupp.single c (1 : ℝ) := by
        ext z
        simp [Finsupp.single_apply]
      rw [hs]
      simp only [map_smul]
      change a •
        (dualExteriorDifferenceAxisAdjoint (B := B) i
          (dualExteriorDifferenceAxis (B := B) j
            (Finsupp.single c (1 : ℝ))) +
         dualExteriorDifferenceAxis (B := B) j
          (dualExteriorDifferenceAxisAdjoint (B := B) i
            (Finsupp.single c (1 : ℝ)))) = a • (0 : DualRealChain 4 B)
      rw [dualExteriorDifferenceAxisAdjoint_comp_anticommute_basis
        (i := i) (j := j) hij c]


end FroehlichSpencer.FS82.Gaussian
