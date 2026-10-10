/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Renormalization.ChargeLayer

/-! # A pointwise obstruction to using `ChargeLayer.expand` unchanged

Neutralized characters on an unrestricted wired-root field are invariant under a common phase
shift. A product of site-local cosine weights on the bounded faces is not. Therefore the rooted
finite-mixture identity is an identity on root-relative fields, and cannot be supplied as the
unchanged, all-fields `ChargeLayer.expand` clause.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT.Generic

/-- A one-site cosine weight, with all other site weights equal to one. -/
noncomputable def oneSiteCosineWeight {V : Type*} [DecidableEq V]
    (j : V) (z : ℝ) (x : V) (θ : ℝ) : ℝ :=
  if x = j then 1 + z * Real.cos θ else 1

/-- A nonconstant one-site cosine product has no finite all-neutral character expansion on the
unrestricted field space. The conclusion is the exact obstruction to treating the root-relative
mixture of `BoundaryMixture` as an unchanged `ChargeLayer.expand` identity. -/
theorem no_all_neutral_character_expansion_one_site_cosine
    {V : Type*} [Fintype V] [DecidableEq V] (j : V) {z : ℝ} (hz : z ≠ 0)
    {n : ℕ} (N : Fin n → Finset (V → ℤ)) (c : Fin n → ℝ)
    (K : Fin n → (V → ℤ) → ℝ)
    (hneutral : ∀ i, ∀ q ∈ N i, ∑ x, q x = 0)
    (hexpand : ∀ ψ : V → ℝ,
      ∏ x, oneSiteCosineWeight j z x (ψ x) =
        ∑ i, c i * ∏ q ∈ N i,
          (1 + K i q * Real.cos (∑ x, ψ x * (q x : ℝ)))) : False := by
  classical
  let ψ₀ : V → ℝ := fun _ => 0
  let ψπ : V → ℝ := fun _ => Real.pi
  let rhs (ψ : V → ℝ) : ℝ :=
    ∑ i, c i * ∏ q ∈ N i,
      (1 + K i q * Real.cos (∑ x, ψ x * (q x : ℝ)))
  have hphase : ∀ i q, q ∈ N i →
      (∑ x, ψ₀ x * (q x : ℝ)) = (∑ x, ψπ x * (q x : ℝ)) := by
    intro i q hq
    have hqsum : ∑ x, (q x : ℝ) = 0 := by exact_mod_cast hneutral i q hq
    calc
      (∑ x, ψ₀ x * (q x : ℝ)) = 0 := by simp [ψ₀]
      _ = Real.pi * ∑ x, (q x : ℝ) := by rw [hqsum]; ring
      _ = ∑ x, ψπ x * (q x : ℝ) := by
        simp only [ψπ]
        rw [← Finset.mul_sum]
  have hrhs : rhs ψ₀ = rhs ψπ := by
    dsimp [rhs]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [hphase i q hq]
  have hleft₀ : ∏ x, oneSiteCosineWeight j z x (ψ₀ x) = 1 + z := by
    rw [Finset.prod_eq_single j]
    · simp [oneSiteCosineWeight, ψ₀]
    · intro x _ hx
      simp [oneSiteCosineWeight, hx]
    · simp [oneSiteCosineWeight]
  have hleftπ : ∏ x, oneSiteCosineWeight j z x (ψπ x) = 1 - z := by
    rw [Finset.prod_eq_single j]
    · simp [oneSiteCosineWeight, ψπ, Real.cos_pi]
      ring
    · intro x _ hx
      simp [oneSiteCosineWeight, hx]
    · simp [oneSiteCosineWeight]
  have hcontra : 1 + z = 1 - z := by
    calc
      1 + z = ∏ x, oneSiteCosineWeight j z x (ψ₀ x) := hleft₀.symm
      _ = rhs ψ₀ := hexpand ψ₀
      _ = rhs ψπ := hrhs
      _ = ∏ x, oneSiteCosineWeight j z x (ψπ x) := (hexpand ψπ).symm
      _ = 1 - z := hleftπ
  exact hz (by linarith)

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
