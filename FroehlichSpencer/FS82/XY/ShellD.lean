/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.BumpD

/-!
# the shell of the bumped box and the chain of a dual current, in every dimension

The dimension-generic form of `XY/Shell3.lean`.

The cells of the bumped box are the images of the
dual cells of `B` together with the shell: the cells with a vertex coordinate at `0` or at
`B k + 1`.

The shell is closed under taking faces.

The chain of an integer current `J` on the dual
cells of degree `d − 2` is `∑ sgn(e) J(e) [bump e]`; the dual coboundaries `dualDD₀`, `dualDD₁`
and their adjoints are written in coordinates through the stencil.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

variable {d : ℕ} {B : Box d}

/-! ## The shell -/

/-- A cell of the bumped box is in the shell when one of its vertex coordinates is extreme. -/
def IsShell (x : Cell d (bumpedBoxD B)) : Prop :=
  ∃ k : Fin d, ∃ v : Fin (bumpedBoxD B k + 1), x k = Sum.inl v ∧ (v.val = 0 ∨ v.val = B k + 1)

theorem not_isShell_bumpCell (c : DualCell d B) : ¬ IsShell (bumpCell c) := by
  rintro ⟨k, v, hv, hext⟩
  cases hc : c k with
  | inl w =>
    rw [bumpCell_inl hc] at hv
    have hval : w.val + 1 = v.val := congrArg Fin.val (Sum.inl.inj hv)
    have := w.isLt
    omega
  | inr e =>
    rw [bumpCell_inr hc] at hv
    exact absurd hv (by simp)

theorem exists_bumpCell_of_not_isShell {x : Cell d (bumpedBoxD B)} (hx : ¬ IsShell x) :
    ∃ c : DualCell d B, bumpCell c = x := by
  have hk : ∀ k : Fin d, ∃ ck : DualCoord B k, ∀ c : DualCell d B, c k = ck →
      bumpCell c k = x k := by
    intro k
    cases hxk : x k with
    | inl v =>
      have h0 : v.val ≠ 0 := fun h => hx ⟨k, v, hxk, Or.inl h⟩
      have h1 : v.val ≠ B k + 1 := fun h => hx ⟨k, v, hxk, Or.inr h⟩
      have hlt : v.val < B k + 1 + 1 := v.isLt
      refine ⟨Sum.inl ⟨v.val - 1, by omega⟩, fun c hc => ?_⟩
      rw [bumpCell_inl hc]
      exact congrArg Sum.inl (Fin.ext (by simp only; omega))
    | inr e =>
      refine ⟨Sum.inr ⟨e.val, e.isLt⟩, fun c hc => ?_⟩
      rw [bumpCell_inr hc]
  choose c hc using hk
  exact ⟨c, funext fun k => hc k c rfl⟩

theorem isShell_of_boundaryBasis_ne_zero {x y : Cell d (bumpedBoxD B)} (hx : IsShell x)
    (h : boundaryBasis x y ≠ 0) : IsShell y := by
  rw [boundaryBasis_apply_eq_sum] at h
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨k, v, hkv, hext⟩ := hx
  unfold boundaryAxisTerm at hi
  cases hxi : x i with
  | inl w => simp [hxi] at hi
  | inr e =>
    have hki : k ≠ i := by
      rintro rfl
      rw [hxi] at hkv
      exact absurd hkv (by simp)
    simp only [hxi] at hi
    have hface : upperFace x i e = y ∨ lowerFace x i e = y := by
      by_contra hcon
      push Not at hcon
      simp [hcon.1, hcon.2] at hi
    refine ⟨k, v, ?_, hext⟩
    rcases hface with hf | hf
    · rw [← hf, upperFace_apply_of_ne x i k e hki, hkv]
    · rw [← hf, lowerFace_apply_of_ne x i k e hki, hkv]

/-! ## Degrees -/

theorem cellAxes_bumpCell (c : DualCell d B) : cellAxes (bumpCell c) = dualCellAxes c := by
  ext i
  simp only [cellAxes, dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact coordIsEdge_bumpCell c i

theorem cellDegree_bumpCell (c : DualCell d B) : cellDegree (bumpCell c) = dualCellDegree c := by
  simp [cellDegree, dualCellDegree, cellAxes_bumpCell]

/-! ## The chain of a current -/

/-- The chain of an integer dual-link current in the bumped box. -/
noncomputable def currentChain (J : DualDForm B (d - 2) → ℤ) : Chain d (bumpedBoxD B) :=
  ∑ e : DualDForm B (d - 2), (sgnCell e.1 * J e) • basisChain (bumpCell e.1)

theorem currentChain_apply (J : DualDForm B (d - 2) → ℤ) (x : Cell d (bumpedBoxD B)) :
    currentChain J x = ∑ e : DualDForm B (d - 2), if bumpCell e.1 = x then sgnCell e.1 * J e else 0 := by
  unfold currentChain
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [basisChain, Finsupp.single_apply]

theorem currentChain_apply_bump (J : DualDForm B (d - 2) → ℤ) (e : DualDForm B (d - 2)) :
    currentChain J (bumpCell e.1) = sgnCell e.1 * J e := by
  rw [currentChain_apply, Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    have : bumpCell f.1 ≠ bumpCell e.1 := fun h => hfe (Subtype.ext (bumpCell_injective h))
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ e) h

theorem currentChain_mem_support {J : DualDForm B (d - 2) → ℤ} {x : Cell d (bumpedBoxD B)}
    (hx : x ∈ (currentChain J).support) : ∃ e : DualDForm B (d - 2), bumpCell e.1 = x ∧ J e ≠ 0 := by
  rw [Finsupp.mem_support_iff, currentChain_apply] at hx
  obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  by_cases hbx : bumpCell e.1 = x
  · refine ⟨e, hbx, fun h0 => he ?_⟩
    simp [hbx, h0]
  · simp [hbx] at he

theorem currentChain_homogeneous (J : DualDForm B (d - 2) → ℤ) :
    homogeneousSupport (currentChain J) (d - 2) := by
  intro x hx
  obtain ⟨e, rfl, _⟩ := currentChain_mem_support hx
  rw [cellDegree_bumpCell]
  exact e.2

theorem currentChain_supportedInRect (J : DualDForm B (d - 2) → ℤ) (lo hi : Fin d → ℕ)
    (hrect : ∀ e : DualDForm B (d - 2), J e ≠ 0 → ∀ i,
      lo i ≤ cellCoordLower (bumpCell e.1) i ∧ cellCoordUpper (bumpCell e.1) i ≤ hi i) :
    supportedInRect (currentChain J) lo hi := by
  intro x hx i
  obtain ⟨e, rfl, he⟩ := currentChain_mem_support hx
  exact hrect e he i

/-- The `ℓ¹` norm of the chain of a current is at most the `ℓ¹` norm of the current. -/
theorem chainL1_currentChain_le (J : DualDForm B (d - 2) → ℤ) :
    chainL1 (currentChain J) ≤ ∑ e : DualDForm B (d - 2), (J e).natAbs := by
  classical
  unfold chainL1
  have hinj : Set.InjOn (fun e : DualDForm B (d - 2) => bumpCell e.1)
      (Finset.univ : Finset (DualDForm B (d - 2))) := fun e _ f _ h =>
    Subtype.ext (bumpCell_injective h)
  have hsub : (currentChain J).support ⊆
      (Finset.univ : Finset (DualDForm B (d - 2))).image fun e => bumpCell e.1 := by
    intro x hx
    obtain ⟨e, rfl, _⟩ := currentChain_mem_support hx
    exact Finset.mem_image_of_mem _ (Finset.mem_univ e)
  calc ∑ c ∈ (currentChain J).support, (currentChain J c).natAbs
      ≤ ∑ c ∈ (Finset.univ : Finset (DualDForm B (d - 2))).image (fun e => bumpCell e.1),
          (currentChain J c).natAbs :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ e : DualDForm B (d - 2), (currentChain J (bumpCell e.1)).natAbs :=
        Finset.sum_image hinj
    _ = ∑ e : DualDForm B (d - 2), (J e).natAbs := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [currentChain_apply_bump, Int.natAbs_mul]
        have hs : (sgnCell e.1).natAbs = 1 := by
          have h := congrArg Int.natAbs (sgnCell_mul_self e.1)
          rw [Int.natAbs_mul] at h
          have : (sgnCell e.1).natAbs * (sgnCell e.1).natAbs = 1 := by simpa using h
          exact Nat.eq_one_of_mul_eq_one_left this
        rw [hs, one_mul]

/-! ## The coboundaries and their adjoints in coordinates -/

theorem euclideanToFinsupp_single_apply {α : Type*} [Fintype α] [DecidableEq α] (a : α) (r : ℝ) :
    euclideanToFinsupp (EuclideanSpace.single a r) = Finsupp.single a r := by
  ext b
  simp [euclideanToFinsupp_apply, Finsupp.single_apply, eq_comm]

/-- The matrix of `dualDD₁` is the stencil. -/
theorem dualDD₁_single_stencil (hd : 3 ≤ d) (e : DualDForm B (d - 2)) (p : DualDForm B (d - 1)) :
    dualDD₁ (EuclideanSpace.single e (1 : ℝ)) p = dualExteriorDifferenceStencilBasis e.1 p.1 := by
  have he : dualDFormToChain (d - 2) (EuclideanSpace.single e (1 : ℝ)) =
      Finsupp.single e.1 1 := by
    change dualDEmbedSubtype (dualDFormEmbedding (d - 2))
      (euclideanToFinsupp (EuclideanSpace.single e (1 : ℝ))) = _
    rw [euclideanToFinsupp_single_apply, dualDEmbedSubtype_apply_single]
    rfl
  have heval := congrArg (fun c : DualRealChain d B => c (dualDFormEmbedding (d - 1) p))
    (dualDD₁_embed_eq_derivative hd (EuclideanSpace.single e (1 : ℝ)))
  rw [he, dualExteriorDifference_basis_eq_coordinateStencil] at heval
  have hleft : dualDFormToChain (d - 1) (dualDD₁ (EuclideanSpace.single e (1 : ℝ)))
      (dualDFormEmbedding (d - 1) p) = dualDD₁ (EuclideanSpace.single e (1 : ℝ)) p := by
    change dualDEmbedSubtype (dualDFormEmbedding (d - 1))
      (euclideanToFinsupp (dualDD₁ (EuclideanSpace.single e (1 : ℝ))))
      (dualDFormEmbedding (d - 1) p) = _
    rw [dualDEmbedSubtype_apply_at_image]
    rfl
  rw [hleft] at heval
  exact heval

/-- The matrix of `dualDD₀` is the stencil. -/
theorem dualDD₀_single_stencil (hd : 3 ≤ d) (v : DualDForm B (d - 3)) (e : DualDForm B (d - 2)) :
    dualDD₀ (EuclideanSpace.single v (1 : ℝ)) e = dualExteriorDifferenceStencilBasis v.1 e.1 := by
  have hv : dualDFormToChain (d - 3) (EuclideanSpace.single v (1 : ℝ)) =
      Finsupp.single v.1 1 := by
    change dualDEmbedSubtype (dualDFormEmbedding (d - 3))
      (euclideanToFinsupp (EuclideanSpace.single v (1 : ℝ))) = _
    rw [euclideanToFinsupp_single_apply, dualDEmbedSubtype_apply_single]
    rfl
  have heval := congrArg (fun c : DualRealChain d B => c (dualDFormEmbedding (d - 2) e))
    (dualDD₀_embed_eq_derivative hd (EuclideanSpace.single v (1 : ℝ)))
  rw [hv, dualExteriorDifference_basis_eq_coordinateStencil] at heval
  have hleft : dualDFormToChain (d - 2) (dualDD₀ (EuclideanSpace.single v (1 : ℝ)))
      (dualDFormEmbedding (d - 2) e) = dualDD₀ (EuclideanSpace.single v (1 : ℝ)) e := by
    change dualDEmbedSubtype (dualDFormEmbedding (d - 2))
      (euclideanToFinsupp (dualDD₀ (EuclideanSpace.single v (1 : ℝ))))
      (dualDFormEmbedding (d - 2) e) = _
    rw [dualDEmbedSubtype_apply_at_image]
    rfl
  rw [hleft] at heval
  exact heval

theorem dualDD₁_adjoint_apply (hd : 3 ≤ d) (G : EuclideanSpace ℝ (DualDForm B (d - 1)))
    (e : DualDForm B (d - 2)) :
    (dualDD₁.adjoint G) e = ∑ p, G p * dualExteriorDifferenceStencilBasis e.1 p.1 := by
  have h := LinearMap.adjoint_inner_right (dualDD₁ (B := B))
    (EuclideanSpace.single e (1 : ℝ)) G
  rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at h
  simp only [conj_trivial, one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rw [dualDD₁_single_stencil hd e p]

theorem dualDD₀_adjoint_apply (hd : 3 ≤ d) (a : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (v : DualDForm B (d - 3)) :
    (dualDD₀.adjoint a) v = ∑ e : DualDForm B (d - 2),
      a e * dualExteriorDifferenceStencilBasis v.1 e.1 := by
  have h := LinearMap.adjoint_inner_right (dualDD₀ (B := B))
    (EuclideanSpace.single v (1 : ℝ)) a
  rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at h
  simp only [conj_trivial, one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rw [dualDD₀_single_stencil hd v e]

end FroehlichSpencer.FS82.XY.DualD

end
