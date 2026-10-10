/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.ExtentD

/-!
# base-separated currents are co-closed one by one, in every dimension

A dual cell `v` of degree `d − 3` has cofaces of degree `d − 2`; any two of them have base points
at `ℓ^∞` distance at most one (`cellBaseNear_of_stencil_ne_zero`).

So if the supports of the
integer currents `J_i` are pairwise not base-near, then at every `v` at most one `J_i` has a
nonzero divergence, and a co-closed integer combination `∑ c_i J_i` forces every `J_i` with
`c_i ≠ 0` to be co-closed (`coClosed_of_separated_sum`).

It is the reason the collision relation of the expansion has to contain
"common face of degree `d − 3`" and not only "common coface of degree `d − 1`": two arcs of a
straight vortex line are not incident to a common cell of degree `d − 1` at the point where they
meet, and neither arc is co-closed.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

variable {d : ℕ} {B : Box d}

/-- A coface has its base point at, or one below, the base point of the cell, in every
coordinate. -/
theorem cellBase_of_stencil_ne_zero {c c' : DualCell d B}
    (h : dualExteriorDifferenceStencilBasis c c' ≠ 0) (k : Fin d) :
    cellBase c' k ≤ cellBase c k ∧ cellBase c k ≤ cellBase c' k + 1 := by
  rw [stencilBasis_apply] at h
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  unfold stencilAxisTerm at hi
  cases hc : c i with
  | inr u => simp [hc] at hi
  | inl ε =>
    simp only [hc] at hi
    have hface : dualUpperFace c i ε = c' ∨ dualLowerFace c i ε = c' := by
      by_contra hcon
      push Not at hcon
      simp [hcon.1, hcon.2] at hi
    by_cases hk : k = i
    · subst hk
      rcases hface with hf | hf
      · have hc' : c' k = Sum.inr ⟨ε.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt ε.isLt)⟩ := by
          rw [← hf]
          simp [dualUpperFace]
        simp only [cellBase, hc, hc']
        omega
      · have hc' : c' k = Sum.inr ⟨ε.val, Nat.lt_succ_of_le ε.isLt.le⟩ := by
          rw [← hf]
          simp [dualLowerFace]
        simp only [cellBase, hc, hc']
        omega
    · have hoff : c k = c' k := by
        rcases hface with hf | hf
        · rw [← hf]
          simp [dualUpperFace, Function.update_of_ne hk]
        · rw [← hf]
          simp [dualLowerFace, Function.update_of_ne hk]
      simp only [cellBase, hoff]
      omega

/-- Two cofaces of one cell are base-near. -/
theorem cellBaseNear_of_stencil_ne_zero {c e f : DualCell d B}
    (he : dualExteriorDifferenceStencilBasis c e ≠ 0)
    (hf : dualExteriorDifferenceStencilBasis c f ≠ 0) : cellBaseNear e f := by
  intro k
  have h1 := cellBase_of_stencil_ne_zero he k
  have h2 := cellBase_of_stencil_ne_zero hf k
  omega

/-- Co-closedness in coordinates. -/
theorem currentVector_mem_coClosed_iff (hd : 3 ≤ d) (J : DualDForm B (d - 2) → ℤ) :
    currentVector J ∈ coClosed (dualDExactOneComplex hd B) ↔
      ∀ v : DualDForm B (d - 3),
        ∑ e : DualDForm B (d - 2), (J e : ℝ) * dualExteriorDifferenceStencilBasis v.1 e.1 = 0 := by
  constructor
  · intro hJ v
    have hker : (dualDExactOneComplex hd B).d₀.adjoint (currentVector J) = 0 :=
      LinearMap.mem_ker.mp hJ
    have h0 := congrFun (congrArg (fun a : EuclideanSpace ℝ (DualDForm B (d - 3)) => a.ofLp) hker) v
    change (dualDD₀.adjoint (currentVector J)) v = 0 at h0
    rw [dualDD₀_adjoint_apply hd] at h0
    exact h0
  · intro h
    apply LinearMap.mem_ker.mpr
    ext v
    change (dualDD₀.adjoint (currentVector J)) v = 0
    rw [dualDD₀_adjoint_apply hd]
    exact h v

/-- **Base-separated currents are co-closed one by one.** -/
theorem coClosed_of_separated_sum (hd : 3 ≤ d) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → DualDForm B (d - 2) → ℤ) (c : ι → ℤ)
    (hsep : ∀ i j, i ≠ j → ∀ e f, J i e ≠ 0 → J j f ≠ 0 → ¬ cellBaseNear e.1 f.1)
    (hsum : currentVector (fun e => ∑ i, c i * J i e) ∈ coClosed (dualDExactOneComplex hd B))
    (i : ι) (hi : c i ≠ 0) :
    currentVector (J i) ∈ coClosed (dualDExactOneComplex hd B) := by
  classical
  rw [currentVector_mem_coClosed_iff] at hsum ⊢
  intro v
  set a : ι → ℝ := fun j =>
    ∑ e : DualDForm B (d - 2), (J j e : ℝ) * dualExteriorDifferenceStencilBasis v.1 e.1 with ha
  have htotal : ∑ j, (c j : ℝ) * a j = 0 := by
    have h := hsum v
    rw [← h]
    simp only [ha, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hone : ∀ j, j ≠ i → a i ≠ 0 → a j = 0 := by
    intro j hji hai
    by_contra haj
    obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hai
    obtain ⟨f, _, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero haj
    have hJe : J i e ≠ 0 := fun h0 => he (by simp [h0])
    have hJf : J j f ≠ 0 := fun h0 => hf (by simp [h0])
    have hse : dualExteriorDifferenceStencilBasis v.1 e.1 ≠ 0 := fun h0 => he (by simp [h0])
    have hsf : dualExteriorDifferenceStencilBasis v.1 f.1 ≠ 0 := fun h0 => hf (by simp [h0])
    exact hsep i j (Ne.symm hji) e f hJe hJf (cellBaseNear_of_stencil_ne_zero hse hsf)
  by_contra hai
  have hsingle : ∑ j, (c j : ℝ) * a j = (c i : ℝ) * a i := by
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rw [hone j hji hai, mul_zero]
  rw [hsingle] at htotal
  rcases mul_eq_zero.mp htotal with h0 | h0
  · exact hi (by exact_mod_cast h0)
  · exact hai h0

end FroehlichSpencer.FS82.XY.DualD

end
