/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# ℓ² a-priori bound, uniqueness and finite-volume approximation

For the pointwise equation `∑' w, a x w * ψ w + (v x - z) * ψ x = f x` on an arbitrary index type
with a Hermitian kernel `a` of finite row support and bounded row sums, and an arbitrary real
potential `v`, we prove the a-priori bound `‖ψ‖² ≤ ‖f‖² / (Im z)²` for square-summable solutions,
uniqueness, and an explicit error bound between the finite-volume resolvent column and a
square-summable solution with right-hand side `δ_y`, in terms of the tail of the solution outside
the finite volume.

Method: compare with finite volumes (no infinite double sums).

Motivation:
Fröhlich–Spencer (1983), (1.4), (1.29), Fröhlich–Spencer (1983).
-/

@[expose] public section

open Matrix Filter

namespace FroehlichSpencer.Infra

section Helpers

variable {X : Type*} [DecidableEq X]

private theorem tsum_notMem_eq {E : Type*} [AddCommGroup E] [TopologicalSpace E] (h : X → E)
    (Λ : Finset X) :
    ∑' x : {x // x ∉ Λ}, h x = ∑' x, (if x ∈ Λ then 0 else h x) := by
  have := tsum_subtype ((Λ : Set X)ᶜ) h
  rw [show (∑' x : {x // x ∉ Λ}, h x) = ∑' x : ((Λ : Set X)ᶜ : Set X), h x from rfl, this]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ Λ <;> simp [Set.indicator, hx]

private theorem tsum_split {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] {h : X → E} (hs : Summable h) (Λ : Finset X) :
    ∑' x, h x = ∑ x ∈ Λ, h x + ∑' x, (if x ∈ Λ then 0 else h x) := by
  rw [← tsum_notMem_eq]
  exact (hs.sum_add_tsum_compl (s := Λ)).symm

private theorem tendsto_tail (h : X → ℝ) :
    Tendsto (fun Λ : Finset X => ∑' x, (if x ∈ Λ then 0 else h x)) atTop (nhds 0) := by
  simp_rw [← tsum_notMem_eq]
  exact tendsto_tsum_compl_atTop_zero h

omit [DecidableEq X] in
private theorem summable_norm_sq {ψ : X → ℂ} (hψ : Memℓp ψ 2) :
    Summable fun x => ‖ψ x‖ ^ 2 := by
  have := hψ.summable (by simp)
  simpa using this

end Helpers

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

/-- The part of `∑' w, a x w * ψ w` coming from outside `Λ`. -/
private noncomputable def bdry (a : X → X → ℂ) (ψ : X → ℂ) (Λ : Finset X) : Λ → ℂ :=
  fun x => ∑' w, if w ∈ Λ then 0 else a x w * ψ w

private theorem mulVec_restricted (v : X → ℝ) (Λ : Finset X) (z : ℂ) (ψ : X → ℂ) (x : Λ) :
    ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) *ᵥ (fun w : Λ => ψ w)) x =
      ∑ w ∈ Λ, a x w * ψ w + ((v x : ℂ) - z) * ψ x := by
  have e : ∀ w : Λ, (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) x w * ψ w =
      a x w * ψ w + (if x = w then ((v x : ℂ) - z) * ψ w else 0) := by
    intro w
    rw [Matrix.sub_apply, restrictedOp_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases hxw : x = w
    · simp [hxw]
      ring
    · simp [hxw]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  rw [← Finset.sum_coe_sort Λ (fun w => a x w * ψ w)]

private theorem restricted_eq (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (v : X → ℝ) (Λ : Finset X)
    (z : ℂ) {ψ f : X → ℂ}
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = f x) (x : Λ) :
    ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) *ᵥ (fun w : Λ => ψ w)) x =
      f x - bdry a ψ Λ x := by
  have hs : Summable fun w => a x w * ψ w :=
    summable_of_ne_finset_zero (s := (hfin x).toFinset) fun w hw => by
      have : a x w = 0 := by simpa using hw
      simp [this]
  have h1 := tsum_split hs Λ
  have h2 := h x
  rw [mulVec_restricted]
  simp only [bdry]
  linear_combination h2 - h1

private theorem summable_tail_sq {ψ : X → ℂ} (hψ : Memℓp ψ 2) (Λ : Finset X) :
    Summable fun x => if x ∈ Λ then (0 : ℝ) else ‖ψ x‖ ^ 2 :=
  .of_nonneg_of_le (fun x => by split_ifs <;> positivity)
    (fun x => by split_ifs <;> simp) (summable_norm_sq hψ)

private theorem sum_norm_sq_bdry_le (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    {ψ : X → ℂ} (hψ : Memℓp ψ 2) (Λ : Finset X) :
    ∑ x : Λ, ‖bdry a ψ Λ x‖ ^ 2 ≤ K ^ 2 * ∑' x, (if x ∈ Λ then 0 else ‖ψ x‖ ^ 2) := by
  set q : X → ℝ := fun w => if w ∈ Λ then 0 else ‖ψ w‖ ^ 2 with hq
  have hq0 : ∀ w, 0 ≤ q w := fun w => by simp only [hq]; split_ifs <;> positivity
  have hT0 : 0 ≤ ∑' x, q x := tsum_nonneg hq0
  rcases isEmpty_or_nonempty Λ with hΛ | ⟨⟨x0, hx0⟩⟩
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  have hK0 : 0 ≤ K := by simpa using hK x0 ∅
  set W : Finset X := Λ.biUnion fun x => (hfin x).toFinset with hW
  have hb : ∀ x : Λ, bdry a ψ Λ x = ∑ w ∈ W, if w ∈ Λ then 0 else a x w * ψ w := by
    intro x
    refine tsum_eq_sum fun w hw => ?_
    have : a x w = 0 := by
      by_contra hne
      exact hw (Finset.mem_biUnion.2 ⟨x, x.2, by simpa using hne⟩)
    simp [this]
  have hrow : ∀ x : Λ, ‖bdry a ψ Λ x‖ ^ 2 ≤ K * ∑ w ∈ W, ‖a x w‖ * q w := by
    intro x
    have h1 : ‖bdry a ψ Λ x‖ ≤ ∑ w ∈ W, (if w ∈ Λ then 0 else ‖a x w‖ * ‖ψ w‖) := by
      rw [hb x]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      split_ifs <;> simp
    have h2 : (∑ w ∈ W, (if w ∈ Λ then 0 else ‖a x w‖ * ‖ψ w‖)) ^ 2 ≤
        (∑ w ∈ W, ‖a x w‖) * ∑ w ∈ W, ‖a x w‖ * q w := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul W (fun w _ => norm_nonneg _)
        (fun w _ => mul_nonneg (norm_nonneg _) (hq0 w)) fun w _ => ?_
      simp only [hq]
      split_ifs
      · simp
      · exact le_of_eq (by ring)
    calc ‖bdry a ψ Λ x‖ ^ 2 ≤ (∑ w ∈ W, (if w ∈ Λ then 0 else ‖a x w‖ * ‖ψ w‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ w ∈ W, ‖a x w‖) * ∑ w ∈ W, ‖a x w‖ * q w := h2
      _ ≤ K * ∑ w ∈ W, ‖a x w‖ * q w :=
          mul_le_mul_of_nonneg_right (hK x W)
            (Finset.sum_nonneg fun w _ => mul_nonneg (norm_nonneg _) (hq0 w))
  have hcol : ∀ w : X, ∑ x : Λ, ‖a x w‖ ≤ K := by
    intro w
    calc ∑ x : Λ, ‖a x w‖ = ∑ x ∈ Λ, ‖a x w‖ :=
          Finset.sum_coe_sort Λ fun x => ‖a x w‖
      _ = ∑ x ∈ Λ, ‖a w x‖ := Finset.sum_congr rfl fun x _ => by rw [ha w x, norm_star]
      _ ≤ K := hK w Λ
  calc ∑ x : Λ, ‖bdry a ψ Λ x‖ ^ 2 ≤ ∑ x : Λ, K * ∑ w ∈ W, ‖a x w‖ * q w :=
        Finset.sum_le_sum fun x _ => hrow x
    _ = K * ∑ w ∈ W, (∑ x : Λ, ‖a x w‖) * q w := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ K * ∑ w ∈ W, K * q w :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_right (hcol w) (hq0 w)) hK0
    _ = K ^ 2 * ∑ w ∈ W, q w := by rw [← Finset.mul_sum]; ring
    _ ≤ K ^ 2 * ∑' x, q x :=
        mul_le_mul_of_nonneg_left
          (Summable.sum_le_tsum W (fun w _ => hq0 w) (summable_tail_sq hψ Λ)) (sq_nonneg K)

private theorem isUnit_det_restricted (ha : ∀ x y, a y x = star (a x y)) (v : X → ℝ)
    (Λ : Finset X) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (isHermitian_restrictedOp ha v Λ) z hz)

private theorem sum_norm_sq_inv_mulVec_le (ha : ∀ x y, a y x = star (a x y)) (v : X → ℝ)
    (Λ : Finset X) {z : ℂ} (hz : z.im ≠ 0) (u : Λ → ℂ) :
    ∑ x, ‖((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹ *ᵥ u) x‖ ^ 2 ≤
      (∑ x, ‖u x‖ ^ 2) / z.im ^ 2 := by
  have := re_star_dotProduct_inv_mulVec_le (isHermitian_restrictedOp ha v Λ) hz u
  rwa [re_star_dotProduct_self_eq_sum_norm_sq, re_star_dotProduct_self_eq_sum_norm_sq] at this

private theorem sum_norm_sq_sub_le {ι : Type*} [Fintype ι] (u b : ι → ℂ) :
    ∑ i, ‖(u - b) i‖ ^ 2 ≤ (√(∑ i, ‖u i‖ ^ 2) + √(∑ i, ‖b i‖ ^ 2)) ^ 2 := by
  have e : ∀ w : ι → ℂ, ∑ i, ‖w i‖ ^ 2 = ‖WithLp.toLp 2 w‖ ^ 2 := fun w => by
    rw [norm_toLp_sq, re_star_dotProduct_self_eq_sum_norm_sq]
  rw [e, e, e, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [show WithLp.toLp 2 (u - b) = WithLp.toLp 2 u - WithLp.toLp 2 b from rfl]
  exact norm_sub_le _ _

/-- The finite-volume column solves the restricted equation. -/
theorem resolventColumn_spec (ha : ∀ x y, a y x = star (a x y)) (v : X → ℝ) (Λ : Finset X)
    {z : ℂ} (hz : z.im ≠ 0) {x y : X} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∑' w, a x w * resolventColumn a v Λ z y w + ((v x : ℂ) - z) * resolventColumn a v Λ z y x =
      (Pi.single y 1 : X → ℂ) x := by
  set M := restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ) with hM
  have hdet := isUnit_det_restricted (a := a) ha v Λ hz
  have hcol : (M *ᵥ fun w : Λ => resolventColumn a v Λ z y w) = Pi.single ⟨y, hy⟩ 1 := by
    have : (fun w : Λ => resolventColumn a v Λ z y w) = M⁻¹ *ᵥ Pi.single ⟨y, hy⟩ 1 := by
      funext w
      rw [Matrix.mulVec_single_one, resolventColumn_of_mem a v z w.2 hy]
      rfl
    rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have h1 := congrFun hcol ⟨x, hx⟩
  rw [hM, mulVec_restricted] at h1
  have h2 : ∑' w, a x w * resolventColumn a v Λ z y w =
      ∑ w ∈ Λ, a x w * resolventColumn a v Λ z y w := by
    refine tsum_eq_sum fun w hw => ?_
    simp [resolventColumn_of_notMem_left a v z y hw]
  rw [h2, h1]
  simp [Pi.single_apply, Subtype.ext_iff]

theorem tsum_norm_sq_resolventColumn_le (ha : ∀ x y, a y x = star (a x y)) (v : X → ℝ)
    (Λ : Finset X) {z : ℂ} (hz : z.im ≠ 0) (y : X) :
    ∑' x, ‖resolventColumn a v Λ z y x‖ ^ 2 ≤ 1 / z.im ^ 2 := by
  have hz2 : 0 < z.im ^ 2 := by positivity
  by_cases hy : y ∈ Λ
  · rw [tsum_eq_sum (s := Λ) fun w hw => by simp [resolventColumn_of_notMem_left a v z y hw]]
    have hcol : (fun w : Λ => resolventColumn a v Λ z y w) =
        (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹ *ᵥ Pi.single ⟨y, hy⟩ 1 := by
      funext w
      rw [Matrix.mulVec_single_one, resolventColumn_of_mem a v z w.2 hy]
      rfl
    have h := sum_norm_sq_inv_mulVec_le ha v Λ hz (Pi.single ⟨y, hy⟩ 1)
    rw [← hcol] at h
    have h1 : ∑ x : Λ, ‖(Pi.single ⟨y, hy⟩ (1 : ℂ) : Λ → ℂ) x‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single ⟨y, hy⟩]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    rw [h1] at h
    rwa [← Finset.sum_coe_sort Λ fun x => ‖resolventColumn a v Λ z y x‖ ^ 2]
  · simp [resolventColumn_of_notMem_right a v z _ hy, hz2.le]

private theorem restricted_eq_inv (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (v : X → ℝ) (Λ : Finset X) {z : ℂ} (hz : z.im ≠ 0)
    {ψ f : X → ℂ} (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = f x) :
    (fun w : Λ => ψ w) = (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹ *ᵥ
      ((fun x : Λ => f x) - bdry a ψ Λ) := by
  have hdet := isUnit_det_restricted (a := a) ha v Λ hz
  have : (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) *ᵥ (fun w : Λ => ψ w) =
      (fun x : Λ => f x) - bdry a ψ Λ := funext fun x => restricted_eq hfin v Λ z h x
  rw [← this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- **A-priori bound.** -/
theorem tsum_norm_sq_le_of_eq (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {ψ f : X → ℂ} (hψ : Memℓp ψ 2) (hf : Memℓp f 2)
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = f x) :
    ∑' x, ‖ψ x‖ ^ 2 ≤ (∑' x, ‖f x‖ ^ 2) / z.im ^ 2 := by
  have hz2 : 0 < z.im ^ 2 := by positivity
  have hsψ := summable_norm_sq hψ
  have hsf := summable_norm_sq hf
  set Fs := ∑' x, ‖f x‖ ^ 2 with hFs
  have hFs0 : 0 ≤ Fs := tsum_nonneg fun x => by positivity
  set T : Finset X → ℝ := fun Λ => ∑' x, (if x ∈ Λ then 0 else ‖ψ x‖ ^ 2) with hT
  set G : ℝ → ℝ := fun t => (√Fs + √(K ^ 2 * t)) ^ 2 / z.im ^ 2 + t with hG
  have hGc : Continuous G := by
    have : Continuous fun t : ℝ => √(K ^ 2 * t) := by fun_prop
    simp only [hG]
    fun_prop
  have hlim : Tendsto (fun Λ => G (T Λ)) atTop (nhds (G 0)) :=
    (hGc.tendsto 0).comp (tendsto_tail fun x => ‖ψ x‖ ^ 2)
  have hG0 : G 0 = Fs / z.im ^ 2 := by
    simp [hG, Real.sq_sqrt hFs0]
  rw [← hG0]
  refine ge_of_tendsto' hlim fun Λ => ?_
  have hsplit := tsum_split hsψ Λ
  have h1 := sum_norm_sq_inv_mulVec_le ha v Λ hz ((fun x : Λ => f x) - bdry a ψ Λ)
  rw [← restricted_eq_inv ha hfin v Λ hz h] at h1
  have h2 := sum_norm_sq_sub_le (fun x : Λ => f x) (bdry a ψ Λ)
  have hF : ∑ x : Λ, ‖f x‖ ^ 2 ≤ Fs := by
    rw [Finset.sum_coe_sort Λ fun x => ‖f x‖ ^ 2]
    exact hsf.sum_le_tsum Λ fun x _ => by positivity
  have hB := sum_norm_sq_bdry_le ha hfin hK hψ Λ
  have h3 : (√(∑ x : Λ, ‖f x‖ ^ 2) + √(∑ x : Λ, ‖bdry a ψ Λ x‖ ^ 2)) ^ 2 ≤
      (√Fs + √(K ^ 2 * T Λ)) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    linarith only [Real.sqrt_le_sqrt hF, Real.sqrt_le_sqrt hB]
  have h4 : ∑ x ∈ Λ, ‖ψ x‖ ^ 2 ≤ (√Fs + √(K ^ 2 * T Λ)) ^ 2 / z.im ^ 2 := by
    rw [← Finset.sum_coe_sort Λ fun x => ‖ψ x‖ ^ 2]
    exact h1.trans ((div_le_div_iff_of_pos_right hz2).2 (h2.trans h3))
  rw [hsplit]
  simp only [hG]
  linarith only [h4]

/-- **Uniqueness.** -/
theorem eq_zero_of_eq_zero (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {ψ : X → ℂ} (hψ : Memℓp ψ 2)
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = 0) : ψ = 0 := by
  have h0 := tsum_norm_sq_le_of_eq ha hfin hK v hz hψ (zero_memℓp (p := 2)) (f := 0) h
  simp only [Pi.zero_apply, norm_zero] at h0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsum_zero, zero_div] at h0
  funext x
  have hx := (summable_norm_sq hψ).le_tsum x fun j _ => by positivity
  have : ‖ψ x‖ ^ 2 ≤ 0 := hx.trans h0
  simpa using this

theorem tsum_norm_sq_le_of_eq_single (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {y : X} {ψ : X → ℂ} (hψ : Memℓp ψ 2)
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x) :
    ∑' x, ‖ψ x‖ ^ 2 ≤ 1 / z.im ^ 2 := by
  have hf : Memℓp (Pi.single y (1 : ℂ) : X → ℂ) 2 := by
    have h1 := (lp.single (E := fun _ : X => ℂ) 2 y (1 : ℂ)).2
    rwa [lp.coeFn_single] at h1
  have := tsum_norm_sq_le_of_eq ha hfin hK v hz hψ hf h
  have h1 : ∑' x, ‖(Pi.single y (1 : ℂ) : X → ℂ) x‖ ^ 2 = 1 := by
    rw [tsum_eq_single y]
    · simp
    · intro b hb
      simp [Pi.single_eq_of_ne hb]
  rwa [h1] at this

/-- Pointwise bound `‖ψ x‖ ≤ 1 / |Im z|` for the `ℓ²` solution with right side `δ_y`. -/
theorem norm_le_one_div_of_eq_single (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {y : X} {ψ : X → ℂ} (hψ : Memℓp ψ 2)
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x) (x : X) :
    ‖ψ x‖ ≤ 1 / |z.im| := by
  have h1 : ‖ψ x‖ ^ 2 ≤ ∑' x, ‖ψ x‖ ^ 2 :=
    (summable_norm_sq hψ).le_tsum x fun j _ => by positivity
  have h2 := tsum_norm_sq_le_of_eq_single ha hfin hK v hz hψ h
  have h3 : (1 / |z.im|) ^ 2 = 1 / z.im ^ 2 := by rw [div_pow, sq_abs, one_pow]
  exact le_of_sq_le_sq (h1.trans (h2.trans_eq h3.symm)) (by positivity)

/-- **Finite-volume approximation**, explicit error in terms of the tail of `ψ` outside `Λ`. -/
theorem tsum_norm_sq_resolventColumn_sub_le (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z : ℂ} (hz : z.im ≠ 0) {y : X} {Λ : Finset X} (hy : y ∈ Λ) {ψ : X → ℂ}
    (hψ : Memℓp ψ 2)
    (h : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x) :
    ∑' x, ‖resolventColumn a v Λ z y x - ψ x‖ ^ 2 ≤
      (1 + K ^ 2 / z.im ^ 2) * ∑' x, (if x ∈ Λ then 0 else ‖ψ x‖ ^ 2) := by
  have hz2 : 0 < z.im ^ 2 := by positivity
  set g := resolventColumn a v Λ z y with hg
  set T := ∑' x, (if x ∈ Λ then 0 else ‖ψ x‖ ^ 2) with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun x => by split_ifs <;> positivity
  -- the finite part
  have hpsi := restricted_eq_inv ha hfin v Λ hz h
  have hδ : (fun x : Λ => (Pi.single y 1 : X → ℂ) x) = Pi.single ⟨y, hy⟩ 1 := by
    funext w
    simp [Pi.single_apply, Subtype.ext_iff]
  rw [hδ] at hpsi
  have hgΛ : (fun w : Λ => g w) = (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹ *ᵥ
      Pi.single ⟨y, hy⟩ 1 := by
    funext w
    rw [Matrix.mulVec_single_one, hg, resolventColumn_of_mem a v z w.2 hy]
    rfl
  have hdiff : (fun w : Λ => g w - ψ w) = (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹ *ᵥ
      bdry a ψ Λ := by
    have : (fun w : Λ => g w - ψ w) = (fun w : Λ => g w) - (fun w : Λ => ψ w) := rfl
    rw [this, hgΛ, hpsi, ← Matrix.mulVec_sub]
    congr 1
    abel
  have hfin1 : ∑ x ∈ Λ, ‖g x - ψ x‖ ^ 2 ≤ K ^ 2 / z.im ^ 2 * T := by
    rw [← Finset.sum_coe_sort Λ fun x => ‖g x - ψ x‖ ^ 2]
    have h1 := sum_norm_sq_inv_mulVec_le ha v Λ hz (bdry a ψ Λ)
    rw [← hdiff] at h1
    calc ∑ x : Λ, ‖g x - ψ x‖ ^ 2 ≤ (∑ x : Λ, ‖bdry a ψ Λ x‖ ^ 2) / z.im ^ 2 := h1
      _ ≤ (K ^ 2 * T) / z.im ^ 2 :=
          (div_le_div_iff_of_pos_right hz2).2 (sum_norm_sq_bdry_le ha hfin hK hψ Λ)
      _ = K ^ 2 / z.im ^ 2 * T := by ring
  -- the full sum: finite part plus tail
  have hdecomp : ∀ x, ‖g x - ψ x‖ ^ 2 =
      (if x ∈ Λ then ‖g x - ψ x‖ ^ 2 else 0) + (if x ∈ Λ then 0 else ‖ψ x‖ ^ 2) := by
    intro x
    by_cases hx : x ∈ Λ
    · simp [hx]
    · simp [hx, hg, resolventColumn_of_notMem_left a v z y hx]
  have hA : Summable fun x => if x ∈ Λ then ‖g x - ψ x‖ ^ 2 else 0 :=
    summable_of_ne_finset_zero (s := Λ) fun x hx => by simp [hx]
  have hB := summable_tail_sq hψ Λ
  have hA' : ∑' x, (if x ∈ Λ then ‖g x - ψ x‖ ^ 2 else 0) = ∑ x ∈ Λ, ‖g x - ψ x‖ ^ 2 := by
    rw [tsum_eq_sum (s := Λ) fun x hx => by simp [hx]]
    exact Finset.sum_congr rfl fun x hx => by simp [hx]
  calc ∑' x, ‖g x - ψ x‖ ^ 2 = ∑' x, ((if x ∈ Λ then ‖g x - ψ x‖ ^ 2 else 0) +
        (if x ∈ Λ then 0 else ‖ψ x‖ ^ 2)) := tsum_congr hdecomp
    _ = ∑ x ∈ Λ, ‖g x - ψ x‖ ^ 2 + T := by rw [hA.tsum_add hB, hA']
    _ ≤ K ^ 2 / z.im ^ 2 * T + T := by linarith only [hfin1]
    _ = (1 + K ^ 2 / z.im ^ 2) * T := by ring

end FroehlichSpencer.Infra
