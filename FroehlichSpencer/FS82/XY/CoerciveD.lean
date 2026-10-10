/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.ShellD

/-!
# the local gain of the dual Coulomb energy in every dimension

For an exact-one complex with `‖d₁ a‖² ≤ M ‖a‖²`, the Coulomb quadratic form of a co-closed
form is bounded below by its squared norm:

`‖μ‖² ≤ M · ⟨μ, (d₁† d₁)⁻¹ μ⟩`   (`normSq_le_mul_quotientCovarianceQuadratic`).

For the dual complex of a box of dimension `d ≥ 3` the row and column sums of the matrix of `d₁`
are at most `2d`, so `M = 4 d²` (`dualDD₁_normSq_le`, `dualD_normSq_le_quotientCovarianceQuadratic`).

This is the gain used in the renormalization of the activities, FS82 (4.30)–(4.33).

The source
obtains it by selecting cells with disjoint coboundaries; in `D = 3` that is `XY/LocalEnergy3.lean`
with the six colours of `XY/Renormalization3.lean`.

The operator bound gives the same kind of
estimate, `⟨ϱ, (δd)⁻¹ ϱ⟩ ≥ ‖ϱ‖² / (4 d²)`, with no selection and no colouring, for all `d` at once.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

/-! ## Coercivity in an exact-one complex -/

section Abstract

variable {V E P : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

theorem inner_sq_le_quotientCovarianceQuadratic_mul' (C : ExactOneComplex V E P)
    (x : coClosed C) (a : EuclideanSpace ℝ E) :
    (inner ℝ (x : EuclideanSpace ℝ E) a) ^ 2 ≤
      quotientCovarianceQuadratic C x * inner ℝ (C.d₁ a) (C.d₁ a) := by
  set g : EuclideanSpace ℝ E := (hodgeInverseOnCoClosed C x : EuclideanSpace ℝ E) with hg
  have hval : formLaplacian C g = x :=
    congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C x)
  have h1 : inner ℝ (x : EuclideanSpace ℝ E) a = inner ℝ (C.d₁ g) (C.d₁ a) := by
    rw [← hval]
    simp [formLaplacian, LinearMap.adjoint_inner_left]
  have h2 : quotientCovarianceQuadratic C x = inner ℝ (C.d₁ g) (C.d₁ g) := by
    unfold quotientCovarianceQuadratic
    rw [← hg]
    nth_rewrite 1 [← hval]
    change inner ℝ (C.d₁.adjoint (C.d₁ g)) g = _
    rw [LinearMap.adjoint_inner_left]
  rw [h1, h2, sq]
  exact real_inner_mul_inner_self_le _ _

/-- **Coercivity of the Coulomb form.** -/
theorem normSq_le_mul_quotientCovarianceQuadratic (C : ExactOneComplex V E P) (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ a : EuclideanSpace ℝ E, inner ℝ (C.d₁ a) (C.d₁ a) ≤ M * inner ℝ a a)
    (μ : coClosed C) :
    inner ℝ (μ : EuclideanSpace ℝ E) (μ : EuclideanSpace ℝ E) ≤
      M * quotientCovarianceQuadratic C μ := by
  set x := inner ℝ (μ : EuclideanSpace ℝ E) (μ : EuclideanSpace ℝ E) with hx
  have hx0 : 0 ≤ x := real_inner_self_nonneg
  have hQ0 := quotientCovarianceQuadratic_nonneg C μ
  have hcs := inner_sq_le_quotientCovarianceQuadratic_mul' C μ (μ : EuclideanSpace ℝ E)
  have hb := hM (μ : EuclideanSpace ℝ E)
  have hsq : x ^ 2 ≤ quotientCovarianceQuadratic C μ * (M * x) :=
    hcs.trans (mul_le_mul_of_nonneg_left hb hQ0)
  rcases hx0.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hM0 hQ0
  · have : x * x ≤ (M * quotientCovarianceQuadratic C μ) * x := by nlinarith
    exact le_of_mul_le_mul_right this hpos

end Abstract

/-! ## A Schur test -/

theorem sum_indicator_le_one {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (h : ∀ a b, P a → P b → a = b) : (∑ a, if P a then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have hcard : (Finset.univ.filter P).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb =>
      h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  exact_mod_cast hcard

/-- **Schur test.** A matrix with absolute row sums at most `R` and absolute column sums at most
`C` has squared operator norm at most `R C`. -/
theorem sum_sq_sum_mul_le {E P : Type*} [Fintype E] [Fintype P] (g : E → P → ℝ) (R C : ℝ)
    (hR0 : 0 ≤ R) (hR : ∀ p, ∑ e, |g e p| ≤ R) (hC : ∀ e, ∑ p, |g e p| ≤ C) (φ : E → ℝ) :
    ∑ p, (∑ e, φ e * g e p) ^ 2 ≤ R * C * ∑ e, φ e ^ 2 := by
  have hrow : ∀ p, (∑ e, φ e * g e p) ^ 2 ≤ R * ∑ e, |g e p| * φ e ^ 2 := by
    intro p
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset E)
      (r := fun e => φ e * g e p) (f := fun e => |g e p|) (g := fun e => |g e p| * φ e ^ 2)
      (fun e _ => abs_nonneg _) (fun e _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun e _ => by
        have h := abs_mul_abs_self (g e p)
        refine le_of_eq ?_
        calc (φ e * g e p) ^ 2 = (g e p * g e p) * φ e ^ 2 := by ring
          _ = |g e p| * (|g e p| * φ e ^ 2) := by rw [← h]; ring)
    refine hcs.trans (mul_le_mul_of_nonneg_right (hR p) ?_)
    exact Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  calc ∑ p, (∑ e, φ e * g e p) ^ 2 ≤ ∑ p, R * ∑ e, |g e p| * φ e ^ 2 :=
        Finset.sum_le_sum fun p _ => hrow p
    _ = R * ∑ e, (∑ p, |g e p|) * φ e ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_mul]
    _ ≤ R * ∑ e, C * φ e ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => ?_) hR0
        exact mul_le_mul_of_nonneg_right (hC e) (sq_nonneg _)
    _ = R * C * ∑ e, φ e ^ 2 := by rw [← Finset.mul_sum]; ring

/-! ## The row and column sums of the stencil -/

variable {d : ℕ} {B : Box d}

open Classical in
/-- The axis term of the stencil is bounded by the indicators of the two faces. -/
theorem abs_stencilAxisTerm_le (c c' : DualCell d B) (i : Fin d) :
    |stencilAxisTerm c c' i| ≤
      (if ∃ ε : Fin (B i), c i = Sum.inl ε ∧ dualUpperFace c i ε = c' then (1 : ℝ) else 0) +
        (if ∃ ε : Fin (B i), c i = Sum.inl ε ∧ dualLowerFace c i ε = c' then (1 : ℝ) else 0) := by
  cases hc : c i with
  | inr u =>
    have h0 : stencilAxisTerm c c' i = 0 := by simp only [stencilAxisTerm, hc]
    rw [h0, abs_zero]
    positivity
  | inl ε =>
    have hU : (∃ ε' : Fin (B i), (Sum.inl ε : DualCoord B i) = Sum.inl ε' ∧
        dualUpperFace c i ε' = c') ↔ dualUpperFace c i ε = c' := by
      constructor
      · rintro ⟨ε', h1, h2⟩
        rw [Sum.inl.inj h1]
        exact h2
      · exact fun h => ⟨ε, rfl, h⟩
    have hL : (∃ ε' : Fin (B i), (Sum.inl ε : DualCoord B i) = Sum.inl ε' ∧
        dualLowerFace c i ε' = c') ↔ dualLowerFace c i ε = c' := by
      constructor
      · rintro ⟨ε', h1, h2⟩
        rw [Sum.inl.inj h1]
        exact h2
      · exact fun h => ⟨ε, rfl, h⟩
    have hval : stencilAxisTerm c c' i = (-1 : ℝ) ^ dualVertexRankBefore c i *
        ((if dualUpperFace c i ε = c' then 1 else 0) -
          (if dualLowerFace c i ε = c' then 1 else 0)) := by
      simp only [stencilAxisTerm, hc]
    rw [hval, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    simp only [hU, hL]
    split_ifs <;> norm_num

/-- Column sums: a cell has at most `2d` cofaces, counted with the stencil. -/
theorem sum_abs_stencil_col_le (c : DualCell d B) (n : ℕ) :
    ∑ p : DualDForm B n, |dualExteriorDifferenceStencilBasis c p.1| ≤ 2 * (d : ℝ) := by
  classical
  calc ∑ p : DualDForm B n, |dualExteriorDifferenceStencilBasis c p.1|
      ≤ ∑ p : DualDForm B n, ∑ i : Fin d, |stencilAxisTerm c p.1 i| := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [stencilBasis_apply]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin d, ∑ p : DualDForm B n, |stencilAxisTerm c p.1 i| := Finset.sum_comm
    _ ≤ ∑ _i : Fin d, (2 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hU := sum_indicator_le_one
          (fun p : DualDForm B n => ∃ ε : Fin (B i), c i = Sum.inl ε ∧ dualUpperFace c i ε = p.1)
          (by
            rintro p p' ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩
            rw [h1] at h1'
            rw [← Sum.inl.inj h1'] at h2'
            exact Subtype.ext (h2.symm.trans h2'))
        have hL := sum_indicator_le_one
          (fun p : DualDForm B n => ∃ ε : Fin (B i), c i = Sum.inl ε ∧ dualLowerFace c i ε = p.1)
          (by
            rintro p p' ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩
            rw [h1] at h1'
            rw [← Sum.inl.inj h1'] at h2'
            exact Subtype.ext (h2.symm.trans h2'))
        calc ∑ p : DualDForm B n, |stencilAxisTerm c p.1 i|
            ≤ ∑ p : DualDForm B n,
                ((if ∃ ε : Fin (B i), c i = Sum.inl ε ∧ dualUpperFace c i ε = p.1
                    then (1 : ℝ) else 0) +
                  (if ∃ ε : Fin (B i), c i = Sum.inl ε ∧ dualLowerFace c i ε = p.1
                    then (1 : ℝ) else 0)) :=
              Finset.sum_le_sum fun p _ => abs_stencilAxisTerm_le c p.1 i
          _ ≤ 2 := by
              rw [Finset.sum_add_distrib]
              linarith
    _ = 2 * (d : ℝ) := by simp [mul_comm]

/-- Row sums: a cell has at most `2d` faces, counted with the stencil. -/
theorem sum_abs_stencil_row_le (c' : DualCell d B) (n : ℕ) :
    ∑ e : DualDForm B n, |dualExteriorDifferenceStencilBasis e.1 c'| ≤ 2 * (d : ℝ) := by
  classical
  have hinjU : ∀ (i : Fin d) (e e' : DualDForm B n),
      (∃ ε : Fin (B i), e.1 i = Sum.inl ε ∧ dualUpperFace e.1 i ε = c') →
      (∃ ε : Fin (B i), e'.1 i = Sum.inl ε ∧ dualUpperFace e'.1 i ε = c') → e = e' := by
    rintro i e e' ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst hj
      have ha := congrFun h2 j
      have hb := congrFun h2' j
      simp only [dualUpperFace, Function.update_self] at ha hb
      have hval := congrArg Fin.val (Sum.inr.inj (ha.trans hb.symm))
      simp only at hval
      rw [h1, h1']
      exact congrArg Sum.inl (Fin.ext (by omega))
    · have ha := congrFun h2 j
      have hb := congrFun h2' j
      simp only [dualUpperFace, Function.update_of_ne hj] at ha hb
      exact ha.trans hb.symm
  have hinjL : ∀ (i : Fin d) (e e' : DualDForm B n),
      (∃ ε : Fin (B i), e.1 i = Sum.inl ε ∧ dualLowerFace e.1 i ε = c') →
      (∃ ε : Fin (B i), e'.1 i = Sum.inl ε ∧ dualLowerFace e'.1 i ε = c') → e = e' := by
    rintro i e e' ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst hj
      have ha := congrFun h2 j
      have hb := congrFun h2' j
      simp only [dualLowerFace, Function.update_self] at ha hb
      have hval := congrArg Fin.val (Sum.inr.inj (ha.trans hb.symm))
      simp only at hval
      rw [h1, h1']
      exact congrArg Sum.inl (Fin.ext hval)
    · have ha := congrFun h2 j
      have hb := congrFun h2' j
      simp only [dualLowerFace, Function.update_of_ne hj] at ha hb
      exact ha.trans hb.symm
  calc ∑ e : DualDForm B n, |dualExteriorDifferenceStencilBasis e.1 c'|
      ≤ ∑ e : DualDForm B n, ∑ i : Fin d, |stencilAxisTerm e.1 c' i| := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [stencilBasis_apply]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin d, ∑ e : DualDForm B n, |stencilAxisTerm e.1 c' i| := Finset.sum_comm
    _ ≤ ∑ _i : Fin d, (2 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hU := sum_indicator_le_one
          (fun e : DualDForm B n =>
            ∃ ε : Fin (B i), e.1 i = Sum.inl ε ∧ dualUpperFace e.1 i ε = c') (hinjU i)
        have hL := sum_indicator_le_one
          (fun e : DualDForm B n =>
            ∃ ε : Fin (B i), e.1 i = Sum.inl ε ∧ dualLowerFace e.1 i ε = c') (hinjL i)
        calc ∑ e : DualDForm B n, |stencilAxisTerm e.1 c' i|
            ≤ ∑ e : DualDForm B n,
                ((if ∃ ε : Fin (B i), e.1 i = Sum.inl ε ∧ dualUpperFace e.1 i ε = c'
                    then (1 : ℝ) else 0) +
                  (if ∃ ε : Fin (B i), e.1 i = Sum.inl ε ∧ dualLowerFace e.1 i ε = c'
                    then (1 : ℝ) else 0)) :=
              Finset.sum_le_sum fun e _ => abs_stencilAxisTerm_le e.1 c' i
          _ ≤ 2 := by
              rw [Finset.sum_add_distrib]
              linarith
    _ = 2 * (d : ℝ) := by simp [mul_comm]

/-! ## The operator bound and the gain -/

/-- `dualDD₁` in coordinates. -/
theorem dualDD₁_apply (hd : 3 ≤ d) (a : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (p : DualDForm B (d - 1)) :
    dualDD₁ a p = ∑ e : DualDForm B (d - 2), a e * dualExteriorDifferenceStencilBasis e.1 p.1 := by
  have h := LinearMap.adjoint_inner_left (dualDD₁ (B := B)) a (EuclideanSpace.single p (1 : ℝ))
  rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at h
  simp only [conj_trivial, one_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rw [dualDD₁_adjoint_apply hd, Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [hq]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

/-- The operator bound in coordinates. -/
theorem dualDD₁_sum_sq_le (hd : 3 ≤ d) (a : EuclideanSpace ℝ (DualDForm B (d - 2))) :
    ∑ p : DualDForm B (d - 1), (dualDD₁ a p) ^ 2 ≤
      4 * (d : ℝ) ^ 2 * ∑ e : DualDForm B (d - 2), (a e) ^ 2 := by
  have h := sum_sq_sum_mul_le (E := DualDForm B (d - 2)) (P := DualDForm B (d - 1))
    (fun e p => dualExteriorDifferenceStencilBasis e.1 p.1) (2 * (d : ℝ)) (2 * (d : ℝ))
    (by positivity)
    (fun p => sum_abs_stencil_row_le p.1 (d - 2)) (fun e => sum_abs_stencil_col_le e.1 (d - 1))
    (fun e => a e)
  have hrw : ∀ p : DualDForm B (d - 1), (dualDD₁ a p) ^ 2 =
      (∑ e : DualDForm B (d - 2), a e * dualExteriorDifferenceStencilBasis e.1 p.1) ^ 2 :=
    fun p => by rw [dualDD₁_apply hd]
  rw [Finset.sum_congr rfl fun p _ => hrw p]
  refine h.trans (le_of_eq ?_)
  ring

theorem euclidean_inner_self_eq_sum_sq {α : Type*} [Fintype α] (x : EuclideanSpace ℝ α) :
    inner ℝ x x = ∑ e, (x e) ^ 2 := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun e _ => by simp [sq]

/-- **The operator bound**: `‖d₁ a‖² ≤ 4 d² ‖a‖²`. -/
theorem dualDD₁_normSq_le (hd : 3 ≤ d) (a : EuclideanSpace ℝ (DualDForm B (d - 2))) :
    inner ℝ (dualDD₁ a) (dualDD₁ a) ≤ 4 * (d : ℝ) ^ 2 * inner ℝ a a := by
  rw [euclidean_inner_self_eq_sum_sq, euclidean_inner_self_eq_sum_sq]
  exact dualDD₁_sum_sq_le hd a

/-- **The gain of the dual Coulomb energy**: `‖μ‖² ≤ 4 d² ⟨μ, (d₁† d₁)⁻¹ μ⟩` for co-closed `μ`. -/
theorem dualD_normSq_le_quotientCovarianceQuadratic (hd : 3 ≤ d)
    (μ : coClosed (dualDExactOneComplex hd B)) :
    inner ℝ (μ : EuclideanSpace ℝ (DualDForm B (d - 2)))
        (μ : EuclideanSpace ℝ (DualDForm B (d - 2))) ≤
      4 * (d : ℝ) ^ 2 * quotientCovarianceQuadratic (dualDExactOneComplex hd B) μ :=
  normSq_le_mul_quotientCovarianceQuadratic (dualDExactOneComplex hd B) (4 * (d : ℝ) ^ 2)
    (by positivity) (fun a => dualDD₁_normSq_le hd a) μ

end FroehlichSpencer.FS82.XY.DualD

end
