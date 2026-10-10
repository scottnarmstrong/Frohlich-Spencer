/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.SourceIncidence
public import FroehlichSpencer.FS82.Infinite.Cube
public import FroehlichSpencer.FS82.Currents.ShortPhaseAggregate

/-!
# the primal cube inside the dual complex of the next cube

The expansion, selection and filling machinery of §2
lives on the dual complex `Λ*` of a box.

In the C1 embedding the closed box `cube M` is a
subcomplex of `Λ*(cube (M+1))`:

* `cubeD M`: a primal cell of `cube M` as a dual cell of `cube (M+1)` (vertex index `v ↦ v`,
  interval index `t ↦ t + 1`); `cubeJ M` is its image in the bumped box (all indices `+1`).
* `boundaryBasis_cubeJ`: `cubeJ` is a chain map for the cubical boundary.
* `boundaryBasis_cell_cast`: the lattice incidence of a dual plaquette and a dual link is the
  product of their orientation signs and the curl coefficient.
* `boundaryBasis_cube_eq`: the primal incidence of `cube M` is `σ_p σ_e curlInt (D p) (D e)`, and
  `curlInt_cubeD_eq_zero`: a dual plaquette `D p` is incident to no other dual link.
-/

open scoped BigOperators
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.ShortPhase
open FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
open FroehlichSpencer.FS82.Currents.ShortComponentPhase
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.SourceTreeChart
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Infinite

@[expose] public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

/-! ### The embedding -/

/-- A primal cell of `cube M` as a dual cell of `cube (M+1)`. -/
def cubeD (M : ℕ) (c : Cell 4 (cube M)) : DualCell 4 (cube (M + 1)) := fun i =>
  match c i with
  | Sum.inl v => Sum.inl ⟨v.val, by
      have := v.isLt
      simp only [cube] at this ⊢
      omega⟩
  | Sum.inr t => Sum.inr ⟨t.val + 1, by
      have := t.isLt
      simp only [cube] at this ⊢
      omega⟩

/-- A primal cell of `cube M` as a cell of the bumped box of `cube (M+1)`. -/
def cubeJ (M : ℕ) (c : Cell 4 (cube M)) : Cell 4 (bumpedBox (cube (M + 1))) :=
  lambdaCellToBumpedBox (cubeD M c)

theorem cubeJ_apply_inl (M : ℕ) (c : Cell 4 (cube M)) (i : Fin 4) (v : Fin (cube M i + 1))
    (h : c i = Sum.inl v) :
    cubeJ M c i = Sum.inl ⟨v.val + 1, by
      have := v.isLt
      simp only [bumpedBox, cube] at this ⊢
      omega⟩ := by
  simp [cubeJ, cubeD, lambdaCellToBumpedBox, h]

theorem cubeJ_apply_inr (M : ℕ) (c : Cell 4 (cube M)) (i : Fin 4) (t : Fin (cube M i))
    (h : c i = Sum.inr t) :
    cubeJ M c i = Sum.inr ⟨t.val + 1, by
      have := t.isLt
      simp only [bumpedBox, cube] at this ⊢
      omega⟩ := by
  simp [cubeJ, cubeD, lambdaCellToBumpedBox, h]

theorem cubeD_injective (M : ℕ) : Function.Injective (cubeD M) := by
  intro c d h
  funext i
  have hi := congrFun h i
  cases hc : c i <;> cases hd : d i <;> simp only [cubeD, hc, hd] at hi
  · exact congrArg Sum.inl (Fin.ext (by simpa using congrArg Fin.val (Sum.inl.inj hi)))
  · cases hi
  · cases hi
  · exact congrArg Sum.inr (Fin.ext (by simpa using congrArg Fin.val (Sum.inr.inj hi)))

theorem cubeJ_injective (M : ℕ) : Function.Injective (cubeJ M) := fun _ _ h =>
  cubeD_injective M (lambdaCellToBumpedBox_injective h)

theorem coordIsEdge_cubeJ (M : ℕ) (c : Cell 4 (cube M)) (i : Fin 4) :
    coordIsEdge (cubeJ M c i) ↔ coordIsEdge (c i) := by
  cases h : c i with
  | inl v => simp [cubeJ_apply_inl M c i v h, coordIsEdge]
  | inr t => simp [cubeJ_apply_inr M c i t h, coordIsEdge]

theorem cellRankBefore_cubeJ (M : ℕ) (c : Cell 4 (cube M)) (i : Fin 4) :
    cellRankBefore (cubeJ M c) i = cellRankBefore c i := by
  unfold cellRankBefore
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, coordIsEdge_cubeJ]

theorem dualCellDegree_cubeD (M : ℕ) (c : Cell 4 (cube M)) :
    dualCellDegree (cubeD M c) = cellDegree c := by
  unfold dualCellDegree cellDegree dualCellAxes cellAxes
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : c i <;> simp [cubeD, h, coordIsEdge]

theorem cubeJ_upperFace (M : ℕ) (c : Cell 4 (cube M)) (i : Fin 4) (t : Fin (cube M i)) :
    cubeJ M (upperFace c i t) = upperFace (cubeJ M c) i ⟨t.val + 1, by
      have := t.isLt
      simp only [bumpedBox, cube] at this ⊢
      omega⟩ := by
  funext j
  by_cases hj : j = i
  · subst hj
    have h1 : upperFace c j t j = Sum.inl ⟨t.val + 1, by omega⟩ := by
      simp [upperFace, vertexUpdate]
    rw [cubeJ_apply_inl M _ j _ h1]
    simp [upperFace, vertexUpdate]
  · have h1 : upperFace c i t j = c j := upperFace_apply_of_ne c i j t hj
    rw [upperFace_apply_of_ne _ i j _ hj]
    cases hc : c j with
    | inl v => rw [cubeJ_apply_inl M _ j v (h1.trans hc), cubeJ_apply_inl M c j v hc]
    | inr s => rw [cubeJ_apply_inr M _ j s (h1.trans hc), cubeJ_apply_inr M c j s hc]

theorem cubeJ_lowerFace (M : ℕ) (c : Cell 4 (cube M)) (i : Fin 4) (t : Fin (cube M i)) :
    cubeJ M (lowerFace c i t) = lowerFace (cubeJ M c) i ⟨t.val + 1, by
      have := t.isLt
      simp only [bumpedBox, cube] at this ⊢
      omega⟩ := by
  funext j
  by_cases hj : j = i
  · subst hj
    have h1 : lowerFace c j t j = Sum.inl ⟨t.val, by omega⟩ := by
      simp [lowerFace, vertexUpdate]
    rw [cubeJ_apply_inl M _ j _ h1]
    simp [lowerFace, vertexUpdate]
  · have h1 : lowerFace c i t j = c j := lowerFace_apply_of_ne c i j t hj
    rw [lowerFace_apply_of_ne _ i j _ hj]
    cases hc : c j with
    | inl v => rw [cubeJ_apply_inl M _ j v (h1.trans hc), cubeJ_apply_inl M c j v hc]
    | inr s => rw [cubeJ_apply_inr M _ j s (h1.trans hc), cubeJ_apply_inr M c j s hc]

theorem axisBoundaryBasis_cubeJ (M : ℕ) (c : Cell 4 (cube M)) (i : Fin 4) :
    axisBoundaryBasis (cubeJ M c) i = Finsupp.mapDomain (cubeJ M) (axisBoundaryBasis c i) := by
  cases hci : c i with
  | inl v =>
      have hJ := cubeJ_apply_inl M c i v hci
      simp only [axisBoundaryBasis, hci, hJ, Finsupp.mapDomain_zero]
  | inr t =>
      have hJ := cubeJ_apply_inr M c i t hci
      simp only [axisBoundaryBasis, hci, hJ]
      rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_sub]
      simp only [basisChain, Finsupp.mapDomain_single]
      rw [cellRankBefore_cubeJ, cubeJ_upperFace, cubeJ_lowerFace]

/-- The embedding is a chain map for the cubical boundary. -/
theorem boundaryBasis_cubeJ (M : ℕ) (c : Cell 4 (cube M)) :
    boundaryBasis (cubeJ M c) = Finsupp.mapDomain (cubeJ M) (boundaryBasis c) := by
  change (∑ i : Fin 4, axisBoundaryBasis (cubeJ M c) i) =
    Finsupp.mapDomain (cubeJ M) (∑ i : Fin 4, axisBoundaryBasis c i)
  rw [Finsupp.mapDomain_finsetSum]
  exact Finset.sum_congr rfl fun i _ => axisBoundaryBasis_cubeJ M c i

/-! ### Lattice incidence and the curl coefficient -/

section Incidence

variable {B : Box 4}

/-- The zero-extended one-form of a basis link field is the indicator of that link. -/
theorem sourcePrimalOneForm_single (e' : Link B) (c' : Cell 4 (bumpedBox B)) :
    sourcePrimalOneForm (EuclideanSpace.single e' (1 : ℝ)) c' =
      if c' = lambdaCellToBumpedBox e'.1 then 1 else 0 := by
  classical
  by_cases h : ∃ e'' : Link B, c' = lambdaCellToBumpedBox e''.1
  · obtain ⟨e'', rfl⟩ := h
    rw [sourcePrimalOneForm_link]
    by_cases he : e'' = e'
    · subst he
      simp
    · have hne : lambdaCellToBumpedBox e''.1 ≠ lambdaCellToBumpedBox e'.1 := fun hh =>
        he (Subtype.ext (lambdaCellToBumpedBox_injective hh))
      simp [he, hne]
  · push Not at h
    rw [sourcePrimalOneForm_eq_zero _ c' h]
    simp [h e']

/-- The lattice incidence of a dual plaquette and a dual link is the product of their
orientation signs and the curl coefficient. -/
theorem boundaryBasis_cell_cast (f : SourceDualTwoCells B) (e' : Link B) :
    ((boundaryBasis (lambdaCellToBumpedBox f.1) (lambdaCellToBumpedBox e'.1) : ℤ) : ℝ) =
      dualCellOrientationSign f.1 * dualCellOrientationSign e'.1 *
        sourceCurlCoefficient f e' := by
  classical
  have h := chainCoboundary_sourcePrimalOneForm_signed (EuclideanSpace.single e' (1 : ℝ)) f
  have hL : chainCoboundary (sourcePrimalOneForm (EuclideanSpace.single e' (1 : ℝ)))
        (lambdaCellToBumpedBox f.1) =
      ((boundaryBasis (lambdaCellToBumpedBox f.1) (lambdaCellToBumpedBox e'.1) : ℤ) : ℝ) := by
    unfold chainCoboundary chainPairing
    rw [Finset.sum_eq_single (lambdaCellToBumpedBox e'.1)]
    · rw [sourcePrimalOneForm_single]
      simp
    · intro c' _ hc'
      rw [sourcePrimalOneForm_single]
      simp [hc']
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  have hR : (latticeExactOneComplex (B := B) originZero).d₁ (EuclideanSpace.single e' (1 : ℝ)) f =
      dualCellOrientationSign e'.1 * sourceCurlCoefficient f e' := by
    change sourceDualD₁ (sourceDualTLinear (EuclideanSpace.single e' (1 : ℝ))) f = _
    rw [sourceDualD₁_eq_sourceCurl_sum, Finset.sum_eq_single e']
    · rw [sourceDualTLinear_apply]
      simp
      ring
    · intro e'' _ hne
      rw [sourceDualTLinear_apply]
      simp [hne]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  rw [← hL, h, hR]
  ring

/-- The integer form of `boundaryBasis_cell_cast`. -/
theorem boundaryBasis_cell (f : SourceDualTwoCells B) (e' : Link B) :
    boundaryBasis (lambdaCellToBumpedBox f.1) (lambdaCellToBumpedBox e'.1) =
      sourceDualSigma f * sourceDualT e' * curlInt f e' := by
  have h := boundaryBasis_cell_cast f e'
  have hT : ((sourceDualT e' : ℤ) : ℝ) = dualCellOrientationSign e'.1 :=
    sourceCurrentOrientationSign_cast e'
  rw [← sourceDualSigma_cast_eq_orientationSign, ← hT, ← curlInt_cast] at h
  exact_mod_cast h

end Incidence

/-! ### The incidence of the primal cube -/

/-- A primal link of `cube M` as a dual link of `cube (M+1)`. -/
def cubeD₁ (M : ℕ) (e : {c : Cell 4 (cube M) // cellDegree c = 1}) : Link (cube (M + 1)) :=
  ⟨cubeD M e.1, by rw [dualCellDegree_cubeD]; exact e.2⟩

/-- A primal plaquette of `cube M` as a dual plaquette of `cube (M+1)`. -/
def cubeD₂ (M : ℕ) (p : {c : Cell 4 (cube M) // cellDegree c = 2}) :
    SourceDualTwoCells (cube (M + 1)) :=
  ⟨cubeD M p.1, by rw [dualCellDegree_cubeD]; exact p.2⟩

theorem cubeD₁_injective (M : ℕ) : Function.Injective (cubeD₁ M) := fun _ _ h =>
  Subtype.ext (cubeD_injective M (congrArg Subtype.val h))

theorem cubeD₂_injective (M : ℕ) : Function.Injective (cubeD₂ M) := fun _ _ h =>
  Subtype.ext (cubeD_injective M (congrArg Subtype.val h))

/-- The primal incidence of the cube is the signed curl coefficient of the embedded cells. -/
theorem boundaryBasis_cube_eq (M : ℕ) (p : {c : Cell 4 (cube M) // cellDegree c = 2})
    (e : {c : Cell 4 (cube M) // cellDegree c = 1}) :
    boundaryBasis p.1 e.1 =
      sourceDualSigma (cubeD₂ M p) * sourceDualT (cubeD₁ M e) *
        curlInt (cubeD₂ M p) (cubeD₁ M e) := by
  rw [← boundaryBasis_cell]
  change _ = boundaryBasis (cubeJ M p.1) (cubeJ M e.1)
  rw [boundaryBasis_cubeJ]
  exact (Finsupp.mapDomain_apply_of_injective (cubeJ_injective M) (boundaryBasis p.1) e.1).symm

/-- A dual plaquette `D p` is incident to no dual link outside the image of the primal links. -/
theorem curlInt_cubeD₂_eq_zero (M : ℕ) (p : {c : Cell 4 (cube M) // cellDegree c = 2})
    (e' : Link (cube (M + 1))) (he' : ∀ e, cubeD₁ M e ≠ e') :
    curlInt (cubeD₂ M p) e' = 0 := by
  have h := boundaryBasis_cell (cubeD₂ M p) e'
  have hzero : boundaryBasis (lambdaCellToBumpedBox (cubeD₂ M p).1)
      (lambdaCellToBumpedBox e'.1) = 0 := by
    change boundaryBasis (cubeJ M p.1) (lambdaCellToBumpedBox e'.1) = 0
    rw [boundaryBasis_cubeJ]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨c, hc⟩
    have hD : cubeD M c = e'.1 := lambdaCellToBumpedBox_injective hc
    have hdeg : cellDegree c = 1 := by
      rw [← dualCellDegree_cubeD, hD]
      exact e'.2
    exact he' ⟨c, hdeg⟩ (Subtype.ext hD)
  rw [hzero] at h
  have hσ : sourceDualSigma (cubeD₂ M p) ≠ 0 := by
    rcases sourceDualSigma_is_pm_one (cubeD₂ M p) with h1 | h1 <;> rw [h1] <;> norm_num
  have hT : sourceDualT e' ≠ 0 := by
    rcases sourceDualT_is_pm_one e' with h1 | h1 <;> rw [h1] <;> norm_num
  have := mul_eq_zero.mp h.symm
  rcases this with h2 | h2
  · exact absurd h2 (mul_ne_zero hσ hT)
  · exact h2

end

end FroehlichSpencer.FS82.ZN

end
