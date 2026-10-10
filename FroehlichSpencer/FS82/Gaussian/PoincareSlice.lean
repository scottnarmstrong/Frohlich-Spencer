/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.AxisSlices
public import FroehlichSpencer.FS82.Gaussian.PathPoincare
public import FroehlichSpencer.FS82.Gaussian.LatticeOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

open scoped BigOperators InnerProductSpace
namespace FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical

variable {B : SourceBox}

theorem axisEuclidean_apply_at_edge
    (i : Fin 4) (x : EuclideanSpace ℝ (DualCell 4 B))
    (q : DualCell 4 B) (e : Fin (B i + 1)) (hq : q i = Sum.inr e) :
    axisEuclidean i x q =
      ((-1 : ℝ) ^ dualVertexRankBefore q i) *
        ((if h : 0 < e.val then
            x (Function.update q i
              (Sum.inl ⟨e.val - 1, by omega⟩))
          else 0) -
         (if h : e.val < B i then
            x (Function.update q i
              (Sum.inl ⟨e.val, h⟩))
          else 0)) := by
  have hadj := LinearMap.adjoint_inner_left
    (axisEuclidean (B := B) i) x (EuclideanSpace.single q (1 : ℝ))
  rw [axisEuclidean_adjoint] at hadj
  have hsingle :
      inner ℝ (EuclideanSpace.single q (1 : ℝ))
          (axisEuclidean i x) = axisEuclidean i x q := by
    rw [PiLp.inner_apply]
    simp [EuclideanSpace.single]
  have htoFinsupp (c : DualCell 4 B) :
      euclideanToFinsupp (EuclideanSpace.single c (1 : ℝ)) =
        Finsupp.single c (1 : ℝ) := by
    ext z
    simp [euclideanToFinsupp_apply, Finsupp.single_apply, PiLp.single_apply, eq_comm]
  have hbasis :
      axisAdjointEuclidean i (EuclideanSpace.single q (1 : ℝ)) =
        finsuppToEuclidean (dualExteriorDifferenceAxisAdjointStencilBasis i q) := by
    simp [axisAdjointEuclidean, LinearMap.comp_apply, htoFinsupp]
  have hstencil :
      inner ℝ (axisAdjointEuclidean i (EuclideanSpace.single q (1 : ℝ))) x =
        ((-1 : ℝ) ^ dualVertexRankBefore q i) *
          ((if h : 0 < e.val then
              x (Function.update q i
                (Sum.inl ⟨e.val - 1, by omega⟩))
            else 0) -
           (if h : e.val < B i then
              x (Function.update q i
                (Sum.inl ⟨e.val, h⟩))
            else 0)) := by
    rw [hbasis]
    simp only [dualExteriorDifferenceAxisAdjointStencilBasis, hq,
      map_smul, map_sub]
    rw [inner_smul_left, inner_sub_left]
    by_cases hp : 0 < e.val <;> by_cases hlt : e.val < B i <;>
      simp [hp, hlt, inner_zero_left, ← inner_finsuppToEuclidean_single,
        real_inner_comm]
  calc
    axisEuclidean i x q =
        inner ℝ (EuclideanSpace.single q (1 : ℝ))
          (axisEuclidean i x) := hsingle.symm
    _ = inner ℝ
        (axisAdjointEuclidean i (EuclideanSpace.single q (1 : ℝ))) x :=
          hadj.symm
    _ = _ := hstencil


theorem axisEuclidean_apply (i : Fin 4)
    (x : EuclideanSpace ℝ (DualCell 4 B)) (q : DualCell 4 B) :
    axisEuclidean i x q =
      ∑ c : DualCell 4 B,
        x c * dualExteriorDifferenceAxisStencilBasis i c q := by
  rw [euclidean_coordinate_expansion (axisEuclidean i) x q]
  apply Finset.sum_congr rfl
  intro c hc
  rw [axisEuclidean_single]

theorem axisEuclidean_apply_at_vertex
    (i : Fin 4) (x : EuclideanSpace ℝ (DualCell 4 B))
    (q : DualCell 4 B) (v : Fin (B i)) (hq : q i = Sum.inl v) :
    axisEuclidean i x q = 0 := by
  rw [axisEuclidean_apply]
  apply Finset.sum_eq_zero
  intro c hc
  cases hci : c i with
  | inl w =>
      have hupper : q ≠ dualUpperFace c i w := by
        intro h
        have hi := congrArg (fun z : DualCell 4 B => z i) h
        simp [dualUpperFace, hq] at hi
      have hlower : q ≠ dualLowerFace c i w := by
        intro h
        have hi := congrArg (fun z : DualCell 4 B => z i) h
        simp [dualLowerFace, hq] at hi
      have hupper' : q ≠
          Function.update c i (Sum.inr ⟨w.val + 1,
            Nat.lt_succ_of_le (Nat.succ_le_of_lt w.isLt)⟩) := by
        simpa [dualUpperFace] using hupper
      have hlower' : q ≠
          Function.update c i (Sum.inr ⟨w.val,
            Nat.lt_succ_of_le w.isLt.le⟩) := by
        simpa [dualLowerFace] using hlower
      have hcoef : dualExteriorDifferenceAxisStencilBasis i c q = 0 := by
        simp only [dualExteriorDifferenceAxisStencilBasis, hci,
          dualUpperFace, dualLowerFace]
        simp [hupper', hlower']
      simp [hcoef]
  | inr w =>
      simp [dualExteriorDifferenceAxisStencilBasis, hci]


@[expose] noncomputable def axisSlicePath (i : Fin 4)
    (b : {c : DualCell 4 B // c i = axisEdgeZero i})
    (x : EuclideanSpace ℝ (DualCell 4 B)) (n : ℕ) : ℝ :=
  if h0 : n = 0 then 0
  else if hn : n ≤ B i then
    x (Function.update b.1 i (Sum.inl ⟨n - 1, by omega⟩))
  else 0

theorem axisSlicePath_edge_formula (i : Fin 4)
    (b : {c : DualCell 4 B // c i = axisEdgeZero i})
    (x : EuclideanSpace ℝ (DualCell 4 B)) (e : Fin (B i + 1)) :
    axisSlicePath i b x e.val - axisSlicePath i b x (e.val + 1) =
      (if h : 0 < e.val then
        x (Function.update b.1 i (Sum.inl ⟨e.val - 1, by omega⟩))
       else 0) -
      (if h : e.val < B i then
        x (Function.update b.1 i (Sum.inl ⟨e.val, h⟩))
       else 0) := by
  by_cases he0 : e.val = 0
  · have he : e = 0 := Fin.ext he0
    subst e
    by_cases hB : 0 < B i
    · have hone : (1 : ℕ) ≤ B i := by omega
      simp [axisSlicePath, hB, hone]
    · have hB0 : B i = 0 := by omega
      simp [axisSlicePath, hB0]
  · have hepos : 0 < e.val := Nat.pos_of_ne_zero he0
    have hebound : e.val ≤ B i := by omega
    by_cases hlt : e.val < B i
    · have he1pos : e.val + 1 ≠ 0 := by omega
      have he1bound : e.val + 1 ≤ B i := by omega
      simp [axisSlicePath, he0, hepos, hebound, he1bound, hlt]
    · have he1notbound : ¬ e.val + 1 ≤ B i := by omega
      simp [axisSlicePath, he0, hepos, hebound, he1notbound, hlt]

theorem axisSlicePath_edge_square_eq (i : Fin 4)
    (b : {c : DualCell 4 B // c i = axisEdgeZero i})
    (x : EuclideanSpace ℝ (DualCell 4 B)) (e : Fin (B i + 1)) :
    (axisSlicePath i b x e.val - axisSlicePath i b x (e.val + 1)) ^ 2 =
      (axisEuclidean i x (Function.update b.1 i (Sum.inr e))) ^ 2 := by
  let q := Function.update b.1 i (Sum.inr e)
  have hq : q i = Sum.inr e := by simp [q]
  have hupdate (u : DualCoord B i) :
      Function.update q i u = Function.update b.1 i u := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [q]
    · simp [q, Function.update_of_ne hk]
  have hprev (h : 0 < e.val) :
      x (Function.update q i (Sum.inl ⟨e.val - 1, by omega⟩)) =
        x (Function.update b.1 i (Sum.inl ⟨e.val - 1, by omega⟩)) := by
    exact congrArg x (hupdate (Sum.inl ⟨e.val - 1, by omega⟩))
  have hnext (h : e.val < B i) :
      x (Function.update q i (Sum.inl ⟨e.val, h⟩)) =
        x (Function.update b.1 i (Sum.inl ⟨e.val, h⟩)) := by
    exact congrArg x (hupdate (Sum.inl ⟨e.val, h⟩))
  have hD : axisEuclidean i x q =
      ((-1 : ℝ) ^ dualVertexRankBefore q i) *
        ((if h : 0 < e.val then
            x (Function.update b.1 i
              (Sum.inl ⟨e.val - 1, by omega⟩))
          else 0) -
         (if h : e.val < B i then
            x (Function.update b.1 i (Sum.inl ⟨e.val, h⟩))
          else 0)) := by
    rw [axisEuclidean_apply_at_edge i x q e hq]
    by_cases hp : 0 < e.val <;> by_cases hlt : e.val < B i
    · simp [hp, hlt, hprev hp, hnext hlt]
    · simp [hp, hlt, hprev hp]
    · simp [hp, hlt, hnext hlt]
    · simp [hp, hlt]
  have hsign : ((-1 : ℝ) ^ dualVertexRankBefore q i) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  calc
    (axisSlicePath i b x e.val - axisSlicePath i b x (e.val + 1)) ^ 2 =
        ((if h : 0 < e.val then
            x (Function.update b.1 i
              (Sum.inl ⟨e.val - 1, by omega⟩))
          else 0) -
         (if h : e.val < B i then
            x (Function.update b.1 i (Sum.inl ⟨e.val, h⟩))
          else 0)) ^ 2 := by rw [axisSlicePath_edge_formula]
    _ = (axisEuclidean i x q) ^ 2 := by
      rw [hD, mul_pow, hsign]
      ring

 theorem axisSlice_poincare (i : Fin 4)
    (b : {c : DualCell 4 B // c i = axisEdgeZero i})
    (x : EuclideanSpace ℝ (DualCell 4 B)) :
    (∑ v : Fin (B i),
      x (Function.update b.1 i (Sum.inl v)) ^ 2) ≤
      ((B i + 1 : ℕ) : ℝ) ^ 2 *
        ∑ e : Fin (B i + 1),
          (axisEuclidean i x (Function.update b.1 i (Sum.inr e))) ^ 2 := by
  let f := axisSlicePath i b x
  have hf0 : f 0 = 0 := by simp [f, axisSlicePath]
  have hp := pathPoincare (B i) f hf0
  have hleft :
      (∑ v : Fin (B i), x (Function.update b.1 i (Sum.inl v)) ^ 2) =
        ∑ j ∈ Finset.range (B i), f (j + 1) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro v hv
    have hbound : v.val + 1 ≤ B i := by omega
    simp [f, axisSlicePath, hbound]
  have hright :
      ∑ k ∈ Finset.range (B i + 1), (f (k + 1) - f k) ^ 2 =
        ∑ e : Fin (B i + 1),
          (axisEuclidean i x (Function.update b.1 i (Sum.inr e))) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro e he
    have h := axisSlicePath_edge_square_eq i b x e
    dsimp [f] at h ⊢
    nlinarith [h]
  dsimp only [f] at hp
  calc
    (∑ v : Fin (B i), x (Function.update b.1 i (Sum.inl v)) ^ 2) =
        ∑ j ∈ Finset.range (B i), axisSlicePath i b x (j + 1) ^ 2 := hleft
    _ ≤ ((B i + 1 : ℕ) : ℝ) ^ 2 *
        ∑ k ∈ Finset.range (B i + 1),
          (axisSlicePath i b x (k + 1) - axisSlicePath i b x k) ^ 2 := by
            simpa only [Nat.cast_add, Nat.cast_one] using hp
    _ = ((B i + 1 : ℕ) : ℝ) ^ 2 *
        ∑ e : Fin (B i + 1),
          (axisEuclidean i x (Function.update b.1 i (Sum.inr e))) ^ 2 := by rw [hright]


def axisVertexPart (i : Fin 4) (x : EuclideanSpace ℝ (DualCell 4 B)) : ℝ :=
  ∑ q : DualCell 4 B,
    match q i with
    | Sum.inl _ => x q ^ 2
    | Sum.inr _ => 0

theorem axisVertexPart_eq_lines (i : Fin 4)
    (x : EuclideanSpace ℝ (DualCell 4 B)) :
    axisVertexPart i x =
      ∑ b : AxisSliceBase (B := B) i,
        ∑ v : Fin (B i),
          x (Function.update b.1 i (Sum.inl v)) ^ 2 := by
  classical
  unfold axisVertexPart
  rw [sum_dualCell_eq_sum_axisSlice (B := B) (i := i)]
  simp [axisEdgeZero]

theorem axisEuclidean_norm_sq_eq_lines (i : Fin 4)
    (x : EuclideanSpace ℝ (DualCell 4 B)) :
    ‖axisEuclidean i x‖ ^ 2 =
      ∑ b : AxisSliceBase (B := B) i,
        ∑ e : Fin (B i + 1),
          (axisEuclidean i x (Function.update b.1 i (Sum.inr e))) ^ 2 := by
  classical
  have hnorm : ‖axisEuclidean i x‖ ^ 2 =
      ∑ q : DualCell 4 B, (axisEuclidean i x q) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp
  rw [hnorm, sum_dualCell_eq_sum_axisSlice (B := B) (i := i)]
  change ∑ b : AxisSliceBase (B := B) i,
      ∑ u : Sum (Fin (B i)) (Fin (B i + 1)),
        (axisEuclidean i x (Function.update b.1 i u)) ^ 2 = _
  calc
    (∑ b : AxisSliceBase (B := B) i,
      ∑ u : Sum (Fin (B i)) (Fin (B i + 1)),
        (axisEuclidean i x (Function.update b.1 i u)) ^ 2) =
      ∑ b : AxisSliceBase (B := B) i,
        ((∑ v : Fin (B i),
            (axisEuclidean i x (Function.update b.1 i (Sum.inl v))) ^ 2) +
         ∑ e : Fin (B i + 1),
            (axisEuclidean i x (Function.update b.1 i (Sum.inr e))) ^ 2) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Fintype.sum_sum_type]
    _ = ∑ b : AxisSliceBase (B := B) i,
          ∑ e : Fin (B i + 1),
            (axisEuclidean i x (Function.update b.1 i (Sum.inr e))) ^ 2 := by
          simp [axisEuclidean_apply_at_vertex]

theorem axisCoordinate_poincare (i : Fin 4)
    (x : EuclideanSpace ℝ (DualCell 4 B)) :
    axisVertexPart i x ≤
      ((B i + 1 : ℕ) : ℝ) ^ 2 * ‖axisEuclidean i x‖ ^ 2 := by
  classical
  rw [axisVertexPart_eq_lines, axisEuclidean_norm_sq_eq_lines]
  calc
    (∑ b : AxisSliceBase (B := B) i,
      ∑ v : Fin (B i),
        x (Function.update b.1 i (Sum.inl v)) ^ 2) ≤
      ∑ b : AxisSliceBase (B := B) i,
        (((B i + 1 : ℕ) : ℝ) ^ 2 *
          ∑ e : Fin (B i + 1),
            (axisEuclidean i x (Function.update b.1 i (Sum.inr e))) ^ 2) := by
              apply Finset.sum_le_sum
              intro b hb
              exact axisSlice_poincare i b x
    _ = ((B i + 1 : ℕ) : ℝ) ^ 2 *
        ∑ b : AxisSliceBase (B := B) i,
          ∑ e : Fin (B i + 1),
            (axisEuclidean i x (Function.update b.1 i (Sum.inr e))) ^ 2 := by
              rw [← Finset.mul_sum]


theorem dualCell_vertex_axis_count (q : DualCell 4 B) :
    (∑ i : Fin 4, match q i with
      | Sum.inl _ => (1 : ℝ)
      | Sum.inr _ => 0) = ((4 - dualCellDegree q : ℕ) : ℝ) := by
  classical
  let V := Finset.univ.filter fun i : Fin 4 =>
    match q i with
    | Sum.inl _ => True
    | Sum.inr _ => False
  have hV : V = Finset.univ \ Cubical.dualCellAxes q := by
    ext i
    cases h : q i <;> simp [V, Cubical.dualCellAxes, h]
  have hcard : V.card + (Cubical.dualCellAxes q).card = 4 := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (Cubical.dualCellAxes q))
    simpa [hV] using h
  have hsum :
      (∑ i : Fin 4, match q i with
        | Sum.inl _ => (1 : ℝ)
        | Sum.inr _ => 0) = (V.card : ℝ) := by
    calc
      (∑ i : Fin 4, match q i with
        | Sum.inl _ => (1 : ℝ)
        | Sum.inr _ => 0) =
          ∑ i : Fin 4, if i ∈ V then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            cases h : q i <;> simp [V, h]
      _ = (V.card : ℝ) := by simp [V]
  have hnat : V.card = 4 - dualCellDegree q := by
    have hcard' : V.card + dualCellDegree q = 4 := by
      simpa [Cubical.dualCellDegree] using hcard
    omega
  calc
    (∑ i : Fin 4, match q i with
      | Sum.inl _ => (1 : ℝ)
      | Sum.inr _ => 0) = (V.card : ℝ) := hsum
    _ = ((4 - dualCellDegree q : ℕ) : ℝ) := by exact_mod_cast hnat

theorem euclidean_norm_sq_eq_coord_sum
    (x : EuclideanSpace ℝ (DualCell 4 B)) :
    ‖x‖ ^ 2 = ∑ q : DualCell 4 B, x q ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp

theorem sum_axisVertexPart_eq_three_norm
    (x : EuclideanSpace ℝ (DualCell 4 B))
    (hx : ∀ q : DualCell 4 B, dualCellDegree q ≠ 1 → x q = 0) :
    (∑ i : Fin 4, axisVertexPart i x) = 3 * ‖x‖ ^ 2 := by
  classical
  unfold axisVertexPart
  rw [Finset.sum_comm, euclidean_norm_sq_eq_coord_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hfactor :
      (∑ i : Fin 4, (match q i with
        | Sum.inl _ => x q ^ 2
        | Sum.inr _ => 0)) =
        ((∑ i : Fin 4, match q i with
          | Sum.inl _ => (1 : ℝ)
          | Sum.inr _ => 0) * x q ^ 2) := by
    calc
      (∑ i : Fin 4, (match q i with
        | Sum.inl _ => x q ^ 2
        | Sum.inr _ => 0)) =
          ∑ i : Fin 4, (match q i with
            | Sum.inl _ => (1 : ℝ)
            | Sum.inr _ => 0) * x q ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              cases q i <;> simp
      _ = _ := by rw [← Finset.sum_mul]
  have hcount := dualCell_vertex_axis_count q
  calc
    (∑ i : Fin 4, (match q i with
      | Sum.inl _ => x q ^ 2
      | Sum.inr _ => 0)) =
        (∑ i : Fin 4, match q i with
          | Sum.inl _ => (1 : ℝ)
          | Sum.inr _ => 0) * x q ^ 2 := hfactor
    _ = ((4 - dualCellDegree q : ℕ) : ℝ) * x q ^ 2 :=
      congrArg (fun z : ℝ => z * x q ^ 2) hcount
    _ = 3 * x q ^ 2 := by
      by_cases hdeg : dualCellDegree q = 1
      · simp [hdeg]
      · have hxq := hx q hdeg
        simp [hxq]

theorem sum_axis_derivative_energy_le_curl
    (x : EuclideanSpace ℝ (DualCell 4 B))
    (hclosed : sumAxisAdjointEuclidean x = 0) :
    (∑ i : Fin 4, ‖axisEuclidean i x‖ ^ 2) ≤
      ‖sumAxisEuclidean x‖ ^ 2 := by
  have hh := sumAxis_hodge_energy x
  rw [hclosed] at hh
  simp [norm_zero] at hh
  have hnonneg : 0 ≤ ∑ i : Fin 4,
      ‖axisAdjointEuclidean i x‖ ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hterm :
      (∑ i : Fin 4, ‖axisEuclidean i x‖ ^ 2) ≤
        ∑ i : Fin 4,
          (‖axisEuclidean i x‖ ^ 2 + ‖axisAdjointEuclidean i x‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [sq_nonneg (‖axisAdjointEuclidean i x‖)]
  nlinarith

theorem fullOneForm_poincare
    (N : ℕ) (hB : ∀ i : Fin 4, B i ≤ N)
    (x : EuclideanSpace ℝ (DualCell 4 B))
    (hdegree : ∀ q : DualCell 4 B, dualCellDegree q ≠ 1 → x q = 0)
    (hclosed : sumAxisAdjointEuclidean x = 0) :
    ‖x‖ ^ 2 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 * ‖sumAxisEuclidean x‖ ^ 2 := by
  have hcoord := sum_axisVertexPart_eq_three_norm x hdegree
  have hsum := sum_axis_derivative_energy_le_curl x hclosed
  have hline :
      (∑ i : Fin 4, axisVertexPart i x) ≤
        ((N + 1 : ℕ) : ℝ) ^ 2 *
          ∑ i : Fin 4, ‖axisEuclidean i x‖ ^ 2 := by
    calc
      (∑ i : Fin 4, axisVertexPart i x) ≤
          ∑ i : Fin 4,
            ((B i + 1 : ℕ) : ℝ) ^ 2 * ‖axisEuclidean i x‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro i hi
              exact axisCoordinate_poincare i x
      _ ≤ _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hside : ((B i + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (hB i)
        have hnonneg : 0 ≤ ‖axisEuclidean i x‖ ^ 2 := sq_nonneg _
        have ha : 0 ≤ ((B i + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have hb : 0 ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have hsq : ((B i + 1 : ℕ) : ℝ) ^ 2 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
          have hprod := mul_nonneg (sub_nonneg.mpr hside) (add_nonneg hb ha)
          nlinarith
        exact mul_le_mul_of_nonneg_right hsq hnonneg
  have hNnonneg : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
  nlinarith [hcoord, hline, hsum]

end FroehlichSpencer.FS82.Gaussian
end
