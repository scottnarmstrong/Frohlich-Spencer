/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.DualComplex
public import FroehlichSpencer.FS82.Cubical.RealFilling

/-!
# Dual incidence and star transfer
-/

public section

namespace FroehlichSpencer.FS82.Cubical

noncomputable section
open Classical

@[expose] def primalThreeCellEquivLambdaStarLink {B : Box 4} :
    PrimalThreeCells B ≃ LambdaStarLinks B where
  toFun c := ⟨primalDualCellEquiv c.1, by
    have h := star_complementary_degree c.1
    rw [c.2] at h
    omega⟩
  invFun c := ⟨primalDualCellEquiv.symm c.1, by
    have h := star_complementary_degree (primalDualCellEquiv.symm c.1)
    simp only [Equiv.apply_symm_apply] at h
    rw [c.2] at h
    omega⟩
  left_inv c := by
    apply Subtype.ext
    exact primalDualCellEquiv.left_inv c.1
  right_inv c := by
    apply Subtype.ext
    exact primalDualCellEquiv.right_inv c.1

/-- The dual exterior difference is the incidence transported by the
orientation-matched star. -/
@[expose] def dualExteriorDifference {d : ℕ} {B : Box d} :
    DualRealChain d B →ₗ[ℝ] DualRealChain d B :=
  starMap.comp (realBoundary.comp starMapInverse)

private theorem realBoundary_basis_expansion {d : ℕ} {B : Box d}
    (c : Cell d B) :
    realBoundary (Finsupp.single c 1) =
      ∑ i : Fin d, match c i with
        | Sum.inl _ => 0
        | Sum.inr e =>
            ((-1 : ℝ) ^ cellRankBefore c i) •
              (Finsupp.single (upperFace c i e) 1 -
                Finsupp.single (lowerFace c i e) 1) := by
  rw [realBoundary, realifyLinearMap_single]
  simp only [one_smul]
  rw [boundary_basis]
  ext x
  let f : Fin d → Chain d B := fun i => match c i with
    | Sum.inl _ => 0
    | Sum.inr e =>
        ((-1 : ℤ) ^ cellRankBefore c i) •
          (basisChain (upperFace c i e) - basisChain (lowerFace c i e))
  let g : Fin d → RealChain d B := fun i => match c i with
    | Sum.inl _ => 0
    | Sum.inr e =>
        ((-1 : ℝ) ^ cellRankBefore c i) •
          (Finsupp.single (upperFace c i e) 1 - Finsupp.single (lowerFace c i e) 1)
  change (Int.cast ((∑ i : Fin d, f i) x) : ℝ) = (∑ i : Fin d, g i) x
  rw [Finset.sum_apply', Finset.sum_apply']
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i <;>
    simp [f, g, hci, basisChain, Int.cast_sub, Finsupp.single_apply]

/-- The dual-coordinate index of a primal edge direction before axis `i`.
Under the orientation-matched star, primal oriented directions are exactly
the dual vertices, so this is the incidence sign in `* d * = δ`. -/
@[expose] def dualVertexRankBefore {d : ℕ} {B : Box d}
    (c : DualCell d B) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun j : Fin d => j < i ∧ ¬ (c j).isRight).card

@[expose] def dualUpperFace {d : ℕ} {B : Box d} (c : DualCell d B)
    (i : Fin d) (e : Fin (B i)) : DualCell d B :=
  Function.update c i (Sum.inr ⟨e.val + 1,
    Nat.lt_succ_of_le (Nat.succ_le_of_lt e.isLt)⟩)

@[expose] def dualLowerFace {d : ℕ} {B : Box d} (c : DualCell d B)
    (i : Fin d) (e : Fin (B i)) : DualCell d B :=
  Function.update c i (Sum.inr ⟨e.val, Nat.lt_succ_of_le e.isLt.le⟩)

/-- Componentwise expansion of the transported dual incidence, now written
entirely in dual coordinates. -/
@[expose] def dualExteriorDifferenceStencilBasis {d : ℕ} {B : Box d}
    (c : DualCell d B) : DualRealChain d B :=
  ∑ i : Fin d, match c i with
    | Sum.inl e =>
        ((-1 : ℝ) ^ dualVertexRankBefore c i) •
          (Finsupp.single (dualUpperFace c i e) 1 -
            Finsupp.single (dualLowerFace c i e) 1)
    | Sum.inr _ => 0

@[expose] def dualExteriorDifferenceStencil {d : ℕ} {B : Box d} :
    DualRealChain d B →ₗ[ℝ] DualRealChain d B :=
  Finsupp.linearCombination ℝ dualExteriorDifferenceStencilBasis

theorem primalCellRankBefore_dualVertexRankBefore {d : ℕ} {B : Box d}
    (c : DualCell d B) (i : Fin d) :
    cellRankBefore (primalDualCellEquiv.symm c) i = dualVertexRankBefore c i := by
  unfold cellRankBefore dualVertexRankBefore
  apply congrArg Finset.card
  apply Finset.ext
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hji : j < i
  · cases hc : c j <;>
      simp [primalDualCellEquiv, coordIsEdge, hc, hji]
  · simp [hji]

theorem star_upperFace_dualUpperFace {d : ℕ} {B : Box d}
    (c : DualCell d B) (i : Fin d) (e : Fin (B i)) :
    primalDualCellEquiv (upperFace (primalDualCellEquiv.symm c) i e) =
      dualUpperFace c i e := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [primalDualCellEquiv, upperFace, dualUpperFace, vertexUpdate]
  · cases hc : c j <;>
      simp [primalDualCellEquiv, upperFace, dualUpperFace, vertexUpdate,
        Function.update_of_ne hji, hc]

theorem star_lowerFace_dualLowerFace {d : ℕ} {B : Box d}
    (c : DualCell d B) (i : Fin d) (e : Fin (B i)) :
    primalDualCellEquiv (lowerFace (primalDualCellEquiv.symm c) i e) =
      dualLowerFace c i e := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [primalDualCellEquiv, lowerFace, dualLowerFace, vertexUpdate]
  · cases hc : c j <;>
      simp [primalDualCellEquiv, lowerFace, dualLowerFace, vertexUpdate,
        Function.update_of_ne hji, hc]

theorem dualExteriorDifference_basis_eq_coordinateStencil {d : ℕ} {B : Box d}
    (c : DualCell d B) :
    dualExteriorDifference (Finsupp.single c 1) =
      dualExteriorDifferenceStencilBasis c := by
  have hstarInv : starMapInverse (Finsupp.single c (1 : ℝ)) =
      Finsupp.single (primalDualCellEquiv.symm c) 1 := by
    ext x
    simp [starMapInverse]
  change starMap (realBoundary (starMapInverse (Finsupp.single c 1))) = _
  rw [hstarInv, realBoundary_basis_expansion]
  rw [map_sum]
  unfold dualExteriorDifferenceStencilBasis
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i with
  | inl e =>
      have hpi : (primalDualCellEquiv.symm c) i = Sum.inr e := by
        simp [primalDualCellEquiv, hci]
      rw [hpi, primalCellRankBefore_dualVertexRankBefore]
      rw [map_smul, map_sub]
      simp [starMap, star_upperFace_dualUpperFace, star_lowerFace_dualLowerFace]
  | inr v =>
      have hpi : (primalDualCellEquiv.symm c) i = Sum.inl v := by
        simp [primalDualCellEquiv, hci]
      simp [hpi]

theorem dualExteriorDifference_eq_coordinateStencil {d : ℕ} {B : Box d} :
    dualExteriorDifference (d := d) (B := B) =
      dualExteriorDifferenceStencil (d := d) (B := B) := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp [map_add, hq, hr]
  | single c z =>
      rw [dualExteriorDifferenceStencil, Finsupp.linearCombination_single]
      have hsingle : Finsupp.single c z = z • Finsupp.single c 1 := by
        ext x
        by_cases hx : x = c <;> simp [hx]
      rw [hsingle, map_smul, dualExteriorDifference_basis_eq_coordinateStencil]

theorem primalDualStar_incidence_identity {d : ℕ} {B : Box d}
    (q : RealChain d B) :
    dualExteriorDifference (starMap q) = starMap (realBoundary q) := by
  simp [dualExteriorDifference, starMapInverse_starMap]

theorem primalDualStar_boundary_identity {d : ℕ} {B : Box d}
    (q : RealChain d B) :
    starMapInverse (dualExteriorDifference (starMap q)) = realBoundary q := by
  rw [primalDualStar_incidence_identity, starMapInverse_starMap]

theorem real_coclosed_maps_to_dual_cycle {d : ℕ} {B : Box d}
    (q : RealChain d B) (hcycle : realBoundary q = 0) :
    dualExteriorDifference (starMap q) = 0 := by
  rw [primalDualStar_incidence_identity, hcycle]
  simp

/-- The 4D co-closed 2-form transfer: star sends the primal cycle to a dual
cycle; the rectangular contraction fills it, and inverse star returns the
degree-three primal filling. -/
theorem real_coclosed_twoForm_dual_exactness {B : Box 4}
    (anchor : Anchor 4 B) (q : RealChain 4 B)
    (hq : realHomogeneousSupport q 2) (hcycle : realBoundary q = 0) :
    ∃ η : DualRealChain 4 B,
      dualExteriorDifference η = starMap q ∧
        realHomogeneousSupport (starMapInverse η) 3 ∧
        realBoundary (starMapInverse η) = q := by
  obtain ⟨hfill, hdegree⟩ := real_positiveDegree_filling anchor q 2 (by omega) hq hcycle
  refine ⟨starMap (realFillingOperator anchor q), ?_, ?_, ?_⟩
  · rw [primalDualStar_incidence_identity, hfill]
  · simpa [starMapInverse_starMap] using hdegree
  · simpa [starMapInverse_starMap] using hfill

theorem real_degree_one_exactness {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : RealChain d B)
    (hone : ∀ c ∈ q.support, cellDegree c = 1)
    (hcycle : realBoundary q = 0) :
    ∃ m : RealChain d B, realBoundary m = q ∧ realHomogeneousSupport m 2 := by
  refine ⟨realFillingOperator anchor q,
    real_degree_one_filling anchor q hone hcycle, ?_⟩
  exact real_degree_one_filling_degree_two_support anchor q hone
end
end FroehlichSpencer.FS82.Cubical

end
