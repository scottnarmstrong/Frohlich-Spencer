/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.PathExpansion

/-!
# Geometric resolvent identity and the multiscale decay iteration

The geometric resolvent identity in column form: for `x ∈ B ⊆ Λ` and `y ∈ Λ \ B`,
`G_Λ(x, y) = - ∑_{k ∈ B, k' ∈ Λ \ B} G_B(x, k) a(k, k') G_Λ(k', y)`, assuming only invertibility
of the two restricted operators.

Iterating it gives the decay estimate
`‖G_Λ(x, y)‖ ≤ θ ^ ⌊d(x, y) / R⌋ * max_w ‖G_Λ(w, y)‖` used in the multiscale argument of
Fröhlich–Spencer (1983), Fröhlich–Spencer (1983).
-/

@[expose] public section

open Matrix

namespace FroehlichSpencer.Infra

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ}

/-- Geometric resolvent identity in column form: for `x ∈ B ⊆ Λ` and `y ∈ Λ \ B`,
`G_Λ(x, y) = -∑_{k ∈ B, k' ∈ Λ \ B} G_B(x, k) a(k, k') G_Λ(k', y)`, where
`G_Λ(x, y) = resolventColumn a v Λ z y x`. Only invertibility is assumed (any `z`, no Hermitian
hypothesis). -/
theorem resolventColumn_eq_neg_sum_coupling (v : X → ℝ) {Λ B : Finset X} (hBΛ : B ⊆ Λ) {z : ℂ}
    (hΛ : IsUnit (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)))
    (hB : IsUnit (restrictedOp a v B - z • (1 : Matrix B B ℂ)))
    {x y : X} (hx : x ∈ B) (hy : y ∈ Λ) (hyB : y ∉ B) :
    resolventColumn a v Λ z y x =
      -∑ k ∈ B, ∑ k' ∈ Λ \ B, resolventColumn a v B z k x * a k k' *
        resolventColumn a v Λ z y k' := by
  set g := resolventColumn a v Λ z y with hg
  set M := restrictedOp a v B - z • (1 : Matrix B B ℂ) with hM
  let r : B → ℂ := fun u => -∑ k' ∈ Λ \ B, a u k' * g k'
  have hMg : M *ᵥ (fun w : B => g w) = r := by
    funext u
    have hrow := resolventColumn_row_of_isUnit (a := a) v Λ hΛ hy (hBΛ u.2)
    have huy : (u : X) ≠ y := fun h => hyB (h ▸ u.2)
    have h0 : (if (u : X) = y then (1 : ℂ) else 0) = 0 := by simp [huy]
    rw [h0, ← Finset.sum_sdiff hBΛ (f := fun w => a u w * g w)] at hrow
    rw [hM, restrictedOp_sub_smul_mulVec_apply]
    simp only [r]
    rw [← hg] at hrow
    linear_combination hrow
  have hgB : (fun w : B => g w) = M⁻¹ *ᵥ r := by
    rw [← hMg, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hB), Matrix.one_mulVec]
  have h1 := congrFun hgB ⟨x, hx⟩
  simp only [Matrix.mulVec, dotProduct] at h1
  change g x = _ at h1
  have e : ∀ k ∈ B, ∑ k' ∈ Λ \ B, resolventColumn a v B z k x * a k k' * g k' =
      resolventColumn a v B z k x * ∑ k' ∈ Λ \ B, a k k' * g k' := fun k _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => mul_assoc _ _ _
  rw [Finset.sum_congr rfl e, h1, ← Finset.sum_coe_sort B, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [resolventColumn_of_mem a v z hx k.2]
  simp only [r]
  ring

/-- Decay iteration: if every `x ∈ Λ` with `d x y ≥ R` lies in a block `B ⊆ Λ` (not containing
`y`, with `H_B - z` invertible) whose boundary coupling `∑ ‖G_B(x, k)‖ ‖a k k'‖` is at most `θ`
and whose coupled outside points `k'` satisfy `d x k' ≤ R` (so blocks have `d`-radius below `R`),
then `‖G_Λ(x, y)‖ ≤ θ ^ ⌊d x y / R⌋₊ · max_w ‖G_Λ(w, y)‖`. No `θ < 1` is needed. -/
theorem norm_resolventColumn_le_pow_of_iteration {d : X → X → ℝ}
    (hd : ∀ x y w, d x y ≤ d x w + d w y) (v : X → ℝ) (Λ : Finset X) {z : ℂ}
    (hΛ : IsUnit (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))) {y : X} {R θ : ℝ} (hR : 0 < R)
    (hθ : 0 ≤ θ)
    (hB : ∀ x ∈ Λ, R ≤ d x y → ∃ B : Finset X, B ⊆ Λ ∧ x ∈ B ∧ y ∉ B ∧
      IsUnit (restrictedOp a v B - z • (1 : Matrix B B ℂ)) ∧
      (∀ k ∈ B, ∀ k' ∈ Λ, k' ∉ B → a k k' ≠ 0 → d x k' ≤ R) ∧
      ∑ k ∈ B, ∑ k' ∈ Λ \ B, ‖resolventColumn a v B z k x‖ * ‖a k k'‖ ≤ θ)
    {x : X} (hx : x ∈ Λ) :
    ‖resolventColumn a v Λ z y x‖ ≤
      θ ^ ⌊d x y / R⌋₊ * Λ.sup' ⟨x, hx⟩ (fun w => ‖resolventColumn a v Λ z y w‖) := by
  set S := Λ.sup' ⟨x, hx⟩ (fun w => ‖resolventColumn a v Λ z y w‖) with hS
  have hS0 : 0 ≤ S :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun w => ‖resolventColumn a v Λ z y w‖) hx)
  have key : ∀ n : ℕ, ∀ x ∈ Λ, (n : ℝ) * R ≤ d x y →
      ‖resolventColumn a v Λ z y x‖ ≤ θ ^ n * S := by
    intro n
    induction n with
    | zero =>
      intro x hx _
      simpa using Finset.le_sup' (fun w => ‖resolventColumn a v Λ z y w‖) hx
    | succ n ih =>
      intro x hx hxn
      have hRx : R ≤ d x y := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast at hxn
        nlinarith
      by_cases hy : y ∈ Λ
      swap
      · rw [resolventColumn_of_notMem_right a v z x hy, norm_zero]
        positivity
      obtain ⟨B, hBΛ, hxB, hyB, hBU, hnear, hsum⟩ := hB x hx hRx
      rw [resolventColumn_eq_neg_sum_coupling v hBΛ hΛ hBU hxB hy hyB, norm_neg]
      calc ‖∑ k ∈ B, ∑ k' ∈ Λ \ B, resolventColumn a v B z k x * a k k' *
            resolventColumn a v Λ z y k'‖
          ≤ ∑ k ∈ B, ∑ k' ∈ Λ \ B, ‖resolventColumn a v B z k x‖ * ‖a k k'‖ * (θ ^ n * S) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)
            rw [norm_mul, norm_mul]
            by_cases h0 : a k k' = 0
            · simp [h0]
            · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hk'Λ := (Finset.mem_sdiff.1 hk').1
              have hk'B := (Finset.mem_sdiff.1 hk').2
              refine ih k' hk'Λ ?_
              have h1 := hnear k hk k' hk'Λ hk'B h0
              have h2 := hd x y k'
              push_cast at hxn
              linarith
        _ = (∑ k ∈ B, ∑ k' ∈ Λ \ B, ‖resolventColumn a v B z k x‖ * ‖a k k'‖) * (θ ^ n * S) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_mul]
        _ ≤ θ * (θ ^ n * S) := mul_le_mul_of_nonneg_right hsum (by positivity)
        _ = θ ^ (n + 1) * S := by ring
  by_cases h : 0 ≤ d x y / R
  · refine key _ x hx ?_
    have := Nat.floor_le h
    rwa [le_div_iff₀ hR] at this
  · rw [Nat.floor_of_nonpos (not_le.1 h).le]
    simpa using Finset.le_sup' (fun w => ‖resolventColumn a v Λ z y w‖) hx

end FroehlichSpencer.Infra
