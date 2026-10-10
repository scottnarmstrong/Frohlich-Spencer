/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.Basic

/-!
# Diagonal-dominance decay of finite-volume resolvents

If `|v x - z| ≥ N > K` on a finite volume `Λ`, where `K` bounds the row sums of the kernel `a`,
then `restrictedOp a v Λ - z • 1` is invertible and the resolvent column decays like
`(K / N) ^ ⌈d x y⌉₊ / (N - K)`, for every complex `z`.

The proof is by maximum propagation, with no
Neumann series.

Motivation: the base-scale mechanism of Fröhlich–Spencer (1983), Appendix A,
Fröhlich–Spencer (1983).
-/

@[expose] public section

open Matrix

namespace FroehlichSpencer.Infra

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

omit [DecidableEq X] in
private theorem norm_sum_mul_le (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K) (Λ : Finset X)
    (x : X) (g : X → ℂ) {B : ℝ} (hB : 0 ≤ B) (hg : ∀ w ∈ Λ, a x w ≠ 0 → ‖g w‖ ≤ B) :
    ‖∑ w ∈ Λ, a x w * g w‖ ≤ K * B := by
  calc ‖∑ w ∈ Λ, a x w * g w‖ ≤ ∑ w ∈ Λ, ‖a x w * g w‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ Λ, ‖a x w‖ * B := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [norm_mul]
        by_cases h : a x w = 0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left (hg w hw h) (norm_nonneg _)
    _ = (∑ w ∈ Λ, ‖a x w‖) * B := by rw [Finset.sum_mul]
    _ ≤ K * B := mul_le_mul_of_nonneg_right (hK x Λ) hB

omit [DecidableEq X] in
private theorem norm_mul_le_of_row (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) (Λ : Finset X) {z : ℂ} {N : ℝ} (hv : ∀ x ∈ Λ, N ≤ ‖(v x : ℂ) - z‖)
    {g r : X → ℂ} {x : X} (hx : x ∈ Λ)
    (hrow : ((v x : ℂ) - z) * g x + ∑ w ∈ Λ, a x w * g w = r x) {R B : ℝ} (hR : ‖r x‖ ≤ R)
    (hB : 0 ≤ B) (hg : ∀ w ∈ Λ, a x w ≠ 0 → ‖g w‖ ≤ B) :
    N * ‖g x‖ ≤ R + K * B := by
  have h1 : ((v x : ℂ) - z) * g x = r x - ∑ w ∈ Λ, a x w * g w := by rw [← hrow]; ring
  have h2 : ‖((v x : ℂ) - z) * g x‖ ≤ R + K * B := by
    rw [h1]
    calc ‖r x - ∑ w ∈ Λ, a x w * g w‖ ≤ ‖r x‖ + ‖∑ w ∈ Λ, a x w * g w‖ := norm_sub_le _ _
      _ ≤ R + K * B := add_le_add hR (norm_sum_mul_le hK Λ x g hB hg)
  calc N * ‖g x‖ ≤ ‖(v x : ℂ) - z‖ * ‖g x‖ :=
        mul_le_mul_of_nonneg_right (hv x hx) (norm_nonneg _)
    _ = ‖((v x : ℂ) - z) * g x‖ := (norm_mul _ _).symm
    _ ≤ R + K * B := h2

/-- Row `x` of `(H_Λ - z) u` for a function `u` on `X` restricted to `Λ`. -/
theorem restrictedOp_sub_smul_mulVec_apply (v : X → ℝ) (Λ : Finset X) (z : ℂ) (u : X → ℂ) (x : Λ) :
    ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) *ᵥ (fun w : Λ => u w)) x =
      ((v x : ℂ) - z) * u x + ∑ w ∈ Λ, a x w * u w := by
  have e : ∀ w : Λ, (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) x w * u w =
      a x w * u w + (if x = w then ((v x : ℂ) - z) * u w else 0) := by
    intro w
    rw [Matrix.sub_apply, restrictedOp_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases hxw : x = w
    · simp [hxw]
      ring
    · simp [hxw]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  rw [add_comm, Finset.sum_coe_sort Λ fun w => a x w * u w]

theorem isUnit_restrictedOp_sub_of_diag_dominant (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) (Λ : Finset X) {z : ℂ} {N : ℝ} (hKN : K < N)
    (hv : ∀ x ∈ Λ, N ≤ ‖(v x : ℂ) - z‖) :
    IsUnit (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) := by
  set M := restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ) with hM
  rw [← Matrix.mulVec_injective_iff_isUnit]
  refine (injective_iff_map_eq_zero M.mulVecLin).2 fun u hu => ?_
  have hu : M *ᵥ u = 0 := hu
  by_contra hne
  obtain ⟨x0, h0⟩ := Function.ne_iff.1 hne
  let f : X → ℂ := fun w => if h : w ∈ Λ then u ⟨w, h⟩ else 0
  have hf : ∀ w : Λ, f w = u w := fun w => by simp [f, w.2]
  obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image Λ (fun w => ‖f w‖) ⟨x0, x0.2⟩
  have hrow := restrictedOp_sub_smul_mulVec_apply (a := a) v Λ z f ⟨xs, hxs⟩
  have hfu : (fun w : Λ => f w) = u := funext hf
  rw [hfu, hu] at hrow
  have := norm_mul_le_of_row hK v Λ hv (g := f) (r := fun _ => 0) hxs
    (by simpa using hrow.symm) (R := 0) (B := ‖f xs‖) (by simp) (norm_nonneg _)
    (fun w hw _ => hmax w hw)
  have hxs0 : ‖f xs‖ = 0 := by
    have : (N - K) * ‖f xs‖ ≤ 0 := by linarith
    nlinarith [norm_nonneg (f xs)]
  have hall : ∀ w : Λ, u w = 0 := fun w => by
    have := hmax w w.2
    rw [hxs0, hf] at this
    exact norm_le_zero_iff.1 this
  exact h0 (hall x0)

/-- The column equation: if `H_Λ - z` is invertible, the resolvent column `G_Λ(z; ·, y)`
satisfies `(v x - z) G(x, y) + ∑_{w ∈ Λ} a x w G(w, y) = δ_{xy}` for `x, y ∈ Λ`. -/
theorem resolventColumn_row_of_isUnit (v : X → ℝ) (Λ : Finset X) {z : ℂ}
    (hU : IsUnit (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))) {y : X} (hy : y ∈ Λ) {x : X}
    (hx : x ∈ Λ) :
    ((v x : ℂ) - z) * resolventColumn a v Λ z y x +
      ∑ w ∈ Λ, a x w * resolventColumn a v Λ z y w = if x = y then 1 else 0 := by
  set M := restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ) with hM
  have hcol : (fun w : Λ => resolventColumn a v Λ z y w) = M⁻¹ *ᵥ Pi.single ⟨y, hy⟩ 1 := by
    funext w
    rw [Matrix.mulVec_single_one, resolventColumn_of_mem a v z w.2 hy]
    rfl
  have h2 : M *ᵥ (fun w : Λ => resolventColumn a v Λ z y w) = Pi.single ⟨y, hy⟩ 1 := by
    rw [hcol, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU), Matrix.one_mulVec]
  have h3 := congrFun h2 ⟨x, hx⟩
  rw [hM, restrictedOp_sub_smul_mulVec_apply] at h3
  rw [h3]
  by_cases hxy : x = y
  · subst hxy
    simp
  · have : (⟨x, hx⟩ : Λ) ≠ ⟨y, hy⟩ := fun h => hxy (congrArg Subtype.val h)
    simp [this, hxy]

theorem norm_resolventColumn_le_of_diag_dominant (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    {d : X → X → ℝ} (hd : ∀ x y w, d x y ≤ d x w + d w y) (hd0 : ∀ x, d x x = 0)
    (hrange : ∀ x y, a x y ≠ 0 → d x y ≤ 1) (v : X → ℝ) (Λ : Finset X) {z : ℂ} {N : ℝ}
    (hKN : K < N) (hv : ∀ x ∈ Λ, N ≤ ‖(v x : ℂ) - z‖) (x y : X) :
    ‖resolventColumn a v Λ z y x‖ ≤ (K / N) ^ ⌈d x y⌉₊ / (N - K) := by
  have hK0 : 0 ≤ K := by simpa using hK x ∅
  have hN : 0 < N := lt_of_le_of_lt hK0 hKN
  have hNK : 0 < N - K := sub_pos.2 hKN
  have hq : 0 ≤ K / N := div_nonneg hK0 hN.le
  by_cases hxy : x ∈ Λ ∧ y ∈ Λ
  swap
  · have : resolventColumn a v Λ z y x = 0 := by
      by_cases hx : x ∈ Λ
      · exact resolventColumn_of_notMem_right a v z x (fun hy => hxy ⟨hx, hy⟩)
      · exact resolventColumn_of_notMem_left a v z y hx
    rw [this, norm_zero]
    positivity
  obtain ⟨hxΛ, hyΛ⟩ := hxy
  set g := resolventColumn a v Λ z y with hg
  have hrow := fun (x : X) (hx : x ∈ Λ) => resolventColumn_row_of_isUnit v Λ
    (isUnit_restrictedOp_sub_of_diag_dominant hK v Λ hKN hv) hyΛ hx
  have key : ∀ k : ℕ, ∀ x ∈ Λ, k ≤ ⌈d x y⌉₊ → ‖g x‖ ≤ (K / N) ^ k / (N - K) := by
    intro k
    induction k with
    | zero =>
      intro x hx _
      obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image Λ (fun w => ‖g w‖) ⟨x, hx⟩
      have h := norm_mul_le_of_row hK v Λ hv (g := g) (r := fun x => if x = y then 1 else 0)
        hxs (hrow xs hxs) (R := 1) (B := ‖g xs‖) (by split_ifs <;> simp) (norm_nonneg _)
        (fun w hw _ => hmax w hw)
      rw [pow_zero, le_div_iff₀ hNK]
      calc ‖g x‖ * (N - K) ≤ ‖g xs‖ * (N - K) :=
            mul_le_mul_of_nonneg_right (hmax x hx) hNK.le
        _ ≤ 1 := by linarith
    | succ k ih =>
      intro x hx hk
      obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image (Λ.filter fun w => k + 1 ≤ ⌈d w y⌉₊)
        (fun w => ‖g w‖) ⟨x, Finset.mem_filter.2 ⟨hx, hk⟩⟩
      obtain ⟨hxsΛ, hxsk⟩ := Finset.mem_filter.1 hxs
      have hne : xs ≠ y := by
        rintro rfl
        simp [hd0] at hxsk
      have h := norm_mul_le_of_row hK v Λ hv (g := g) (r := fun x => if x = y then 1 else 0)
        hxsΛ (hrow xs hxsΛ) (R := 0) (B := (K / N) ^ k / (N - K)) (by simp [hne])
        (by positivity) (by
          intro w hw haw
          refine ih w hw ?_
          have h1 : d xs y ≤ (⌈d w y⌉₊ : ℝ) + 1 :=
            (hd xs y w).trans (add_le_add (hrange xs w haw) (Nat.le_ceil _)) |>.trans
              (le_of_eq (by ring))
          have h2 : ⌈d xs y⌉₊ ≤ ⌈d w y⌉₊ + 1 := Nat.ceil_le.2 (by exact_mod_cast h1)
          omega)
      have h' : ‖g xs‖ ≤ K * ((K / N) ^ k / (N - K)) / N := by
        rw [le_div_iff₀ hN]; linarith
      calc ‖g x‖ ≤ ‖g xs‖ := hmax x (Finset.mem_filter.2 ⟨hx, hk⟩)
        _ ≤ _ := h'
        _ = (K / N) ^ (k + 1) / (N - K) := by
          rw [pow_succ]
          field_simp
  exact key _ x hxΛ le_rfl

end FroehlichSpencer.Infra
