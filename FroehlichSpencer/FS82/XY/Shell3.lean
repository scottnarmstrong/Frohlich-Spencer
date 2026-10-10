/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Bump3
public import FroehlichSpencer.FS82.XY.ClosedLineage3

/-!
# the shell of the bumped box and the chain of a dual-link current

The cells of the bumped box are the images of the dual cells of `B` together with the shell: the
cells with a vertex coordinate at `0` or at `B k + 1`.

The shell is closed under taking faces.

The
chain of an integer dual-link current `J` is `∑ sgn(e) J(e) [bump e]`; the adjoints of the dual
coboundaries are written in coordinates through the stencil.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.XY.Renormalization3

variable {B : Dual3Box}

/-! ## The shell -/

/-- A cell of the bumped box is in the shell when one of its vertex coordinates is extreme. -/
def IsShell (x : Cell 3 (bumpedBox3 B)) : Prop :=
  ∃ k : Fin 3, ∃ v : Fin (bumpedBox3 B k + 1), x k = Sum.inl v ∧ (v.val = 0 ∨ v.val = B k + 1)

theorem not_isShell_bumpCell (c : DualCell 3 B) : ¬ IsShell (bumpCell c) := by
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

theorem exists_bumpCell_of_not_isShell {x : Cell 3 (bumpedBox3 B)} (hx : ¬ IsShell x) :
    ∃ c : DualCell 3 B, bumpCell c = x := by
  have hk : ∀ k : Fin 3, ∃ ck : DualCoord B k, ∀ c : DualCell 3 B, c k = ck →
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

theorem isShell_of_boundaryBasis_ne_zero {x y : Cell 3 (bumpedBox3 B)} (hx : IsShell x)
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

theorem cellAxes_bumpCell (c : DualCell 3 B) : cellAxes (bumpCell c) = dualCellAxes c := by
  ext i
  simp only [cellAxes, dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact coordIsEdge_bumpCell c i

theorem cellDegree_bumpCell (c : DualCell 3 B) : cellDegree (bumpCell c) = dualCellDegree c := by
  simp [cellDegree, dualCellDegree, cellAxes_bumpCell]

/-! ## The chain of a current -/

/-- The chain of an integer dual-link current in the bumped box. -/
noncomputable def currentChain (J : Dual3Links B → ℤ) : Chain 3 (bumpedBox3 B) :=
  ∑ e : Dual3Links B, (sgnCell e.1 * J e) • basisChain (bumpCell e.1)

theorem currentChain_apply (J : Dual3Links B → ℤ) (x : Cell 3 (bumpedBox3 B)) :
    currentChain J x = ∑ e : Dual3Links B, if bumpCell e.1 = x then sgnCell e.1 * J e else 0 := by
  unfold currentChain
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [basisChain, Finsupp.single_apply]

theorem currentChain_apply_bump (J : Dual3Links B → ℤ) (e : Dual3Links B) :
    currentChain J (bumpCell e.1) = sgnCell e.1 * J e := by
  rw [currentChain_apply, Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    have : bumpCell f.1 ≠ bumpCell e.1 := fun h => hfe (Subtype.ext (bumpCell_injective h))
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ e) h

theorem currentChain_mem_support {J : Dual3Links B → ℤ} {x : Cell 3 (bumpedBox3 B)}
    (hx : x ∈ (currentChain J).support) : ∃ e : Dual3Links B, bumpCell e.1 = x ∧ J e ≠ 0 := by
  rw [Finsupp.mem_support_iff, currentChain_apply] at hx
  obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  by_cases hbx : bumpCell e.1 = x
  · refine ⟨e, hbx, fun h0 => he ?_⟩
    simp [hbx, h0]
  · simp [hbx] at he

theorem currentChain_homogeneous (J : Dual3Links B → ℤ) :
    homogeneousSupport (currentChain J) 1 := by
  intro x hx
  obtain ⟨e, rfl, _⟩ := currentChain_mem_support hx
  rw [cellDegree_bumpCell]
  exact e.2

theorem currentChain_supportedInRect (J : Dual3Links B → ℤ) (lo hi : Fin 3 → ℕ)
    (hrect : ∀ e : Dual3Links B, J e ≠ 0 → ∀ i,
      lo i ≤ cellCoordLower (bumpCell e.1) i ∧ cellCoordUpper (bumpCell e.1) i ≤ hi i) :
    supportedInRect (currentChain J) lo hi := by
  intro x hx i
  obtain ⟨e, rfl, he⟩ := currentChain_mem_support hx
  exact hrect e he i

/-- The `ℓ¹` norm of the chain of a current is at most the `ℓ¹` norm of the current. -/
theorem chainL1_currentChain_le (J : Dual3Links B → ℤ) :
    chainL1 (currentChain J) ≤ ∑ e : Dual3Links B, (J e).natAbs := by
  classical
  unfold chainL1
  have hinj : Set.InjOn (fun e : Dual3Links B => bumpCell e.1)
      (Finset.univ : Finset (Dual3Links B)) := fun e _ f _ h =>
    Subtype.ext (bumpCell_injective h)
  have hsub : (currentChain J).support ⊆
      (Finset.univ : Finset (Dual3Links B)).image fun e => bumpCell e.1 := by
    intro x hx
    obtain ⟨e, rfl, _⟩ := currentChain_mem_support hx
    exact Finset.mem_image_of_mem _ (Finset.mem_univ e)
  calc ∑ c ∈ (currentChain J).support, (currentChain J c).natAbs
      ≤ ∑ c ∈ (Finset.univ : Finset (Dual3Links B)).image (fun e => bumpCell e.1),
          (currentChain J c).natAbs :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ e : Dual3Links B, (currentChain J (bumpCell e.1)).natAbs :=
        Finset.sum_image hinj
    _ = ∑ e : Dual3Links B, (J e).natAbs := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [currentChain_apply_bump, Int.natAbs_mul]
        have hs : (sgnCell e.1).natAbs = 1 := by
          have h := congrArg Int.natAbs (sgnCell_mul_self e.1)
          rw [Int.natAbs_mul] at h
          have : (sgnCell e.1).natAbs * (sgnCell e.1).natAbs = 1 := by simpa using h
          exact Nat.eq_one_of_mul_eq_one_left this
        rw [hs, one_mul]

/-! ## The adjoint coboundaries in coordinates -/

theorem d1_adjoint_apply (G : EuclideanSpace ℝ (Dual3Plaquettes B)) (e : Dual3Links B) :
    ((dual3ExactOneComplex B).d₁.adjoint G) e = ∑ p, G p * dual3ChartIncidence p e := by
  have h := LinearMap.adjoint_inner_right (dual3ExactOneComplex B).d₁
    (EuclideanSpace.single e (1 : ℝ)) G
  rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at h
  simp only [conj_trivial, one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rfl

theorem d0_adjoint_apply (a : EuclideanSpace ℝ (Dual3Links B)) (v : Dual3Vertices B) :
    ((dual3ExactOneComplex B).d₀.adjoint a) v =
      ∑ e : Dual3Links B, a e * dualExteriorDifferenceStencilBasis v.1 e.1 := by
  have h := LinearMap.adjoint_inner_right (dual3ExactOneComplex B).d₀
    (EuclideanSpace.single v (1 : ℝ)) a
  rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at h
  simp only [conj_trivial, one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  have hst := xy3_d0_single_stencil v e
  change (dual3D₀ (EuclideanSpace.single v 1)) e =
    dualExteriorDifferenceStencilBasis v.1 e.1 at hst
  change a e * (dual3D₀ (EuclideanSpace.single v (1 : ℝ))) e = _
  rw [hst]

end FroehlichSpencer.FS82.XY

end
