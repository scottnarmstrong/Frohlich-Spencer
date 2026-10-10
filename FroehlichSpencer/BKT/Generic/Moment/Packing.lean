/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.Aggregate
public import FroehlichSpencer.BKT.ExpMoment.Claim32Mod

/-!
# Packing the second-order errors of the real shift (generic core)

Along the real shift `t ↦ (∇φ + tθ, ⟨φ, ϱ⟩ + t[⟨σ, ϱ⟩]_{2π})` every renormalized factor loses at
most `8|z(ϱ)| (s² + (N m T)² + N² m T²)` (`FroehlichSpencer.BKT.Generic.Moment.Taylor`), where

* `s = [⟨σ, ϱ⟩]_{2π}` is the reduced phase shift;
* `N` is the number of edges carrying the wave gradient of `ϱ`;
* `T = (∑_{e touching D(ϱ)} θ_e²)^{1/2}`;
* `m ≤ 1` bounds the logarithmic-derivative defect of the weight.

This module sums these errors over one ensemble:

* `grad_ne_zero_mem_edgesTouching`: a gradient vanishes off the edges touching the support;
* `sum_shiftError_le`: `∑_ϱ 8|z(ϱ)|(s² + (N m T)² + N² m T²) ≤ ε ∑_e ([∇σ(e)]_{2π}² + θ_e²)`.

For `sum_shiftError_le`:

* The proof needs the edge-volume bound `|edges touching D(ϱ)| ≤ K_v (d+1)²` and KP's same-scale
  disjointness.
* It also needs the threshold of `sum_abs_mul_le_of_touching_center` with `K₀ = 8(K_v + 2K_v²)`,
  `p = q = 4`.
* The reduced phase is routed through the domain as in the
  (`sq_toIcoMod_pairing_le_of_center`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open Finset

variable {V : Type*} {E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- A gradient vanishes off the edges touching the support. -/
theorem grad_ne_zero_mem_edgesTouching (G : Multigraph V E) {a : V → ℝ} {S : Set V}
    (hS : Function.support a ⊆ S) {e : E} (he : G.grad a e ≠ 0) : e ∈ edgesTouching G S := by
  rw [mem_edgesTouching]
  by_contra h
  push Not at h
  have h1 : a (G.src e) = 0 := by
    by_contra h1
    exact h.1 (hS h1)
  have h2 : a (G.tgt e) = 0 := by
    by_contra h2
    exact h.2 (hS h2)
  exact he (by simp only [Multigraph.grad, h1, h2, sub_zero])

/-- The algebra of one density's error: the three error terms against the weight. -/
lemma shiftError_algebra {s2 B C Kv Y SW S2 : ℝ} (hA : s2 ≤ Kv * Y * SW)
    (hB : B ≤ Kv ^ 2 * Y * S2) (hC : C ≤ Kv ^ 2 * Y * S2) (h1 : 0 ≤ Kv * Y * S2)
    (h2 : 0 ≤ Kv ^ 2 * Y * SW) :
    8 * (s2 + B + C) ≤ 8 * (Kv + 2 * Kv ^ 2) * Y * (SW + S2) := by
  linear_combination 8 * hA + 8 * hB + 8 * hC + 8 * h1 + 16 * h2

/-- **Packing of the real-shift errors** (FS81 (6.40)–(6.44), KP  -/
theorem sum_shiftError_le (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (Kv : ℝ) (hKv : 0 ≤ Kv)
    (hvol : ∀ (ρ : V → ℤ) (j : V),
      ((edgesTouching G (G.densityDomain ρ j)).card : ℝ) ≤ Kv * ((G.densityDiameter ρ : ℝ) + 1) ^ 2)
    (N : Finset (V → ℤ)) (hne : ∀ ρ ∈ N, ρ ≠ 0) (hneutral : ∀ ρ ∈ N, ∑ j, ρ j = 0)
    (ctr : (V → ℤ) → V) (hctr : ∀ ρ ∈ N, G.IsDensityCenter ρ (ctr ρ))
    (hdisj : ∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
      G.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      G.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      ∀ j₁ j₂ : V, G.IsDensityCenter ϱ₁ j₁ → G.IsDensityCenter ϱ₂ j₂ →
        G.densityDomain ϱ₁ j₁ ∩ G.densityDomain ϱ₂ j₂ = ∅)
    (bg : (V → ℤ) → E → ℝ)
    (hbg : ∀ ρ ∈ N, ∀ e, bg ρ e ≠ 0 → e ∈ edgesTouching G (G.densityDomain ρ (ctr ρ)))
    (m : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (z : (V → ℤ) → ℝ) (b ε : ℝ)
    (hz : ∀ ρ ∈ N, |z ρ| ≤
      Real.exp (-b * (∑ x, |(ρ x : ℝ)| + Real.logb 2 (G.densityDiameter ρ + 1))))
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    (σ : V → ℝ) (θ : E → ℝ) :
    ∑ ρ ∈ N, 8 * |z ρ| *
        (toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) ^ 2 +
          (((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) * m *
            Real.sqrt (∑ e ∈ edgesTouching G (G.densityDomain ρ (ctr ρ)), θ e ^ 2)) ^ 2 +
          ((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) ^ 2 * m *
            Real.sqrt (∑ e ∈ edgesTouching G (G.densityDomain ρ (ctr ρ)), θ e ^ 2) ^ 2) ≤
      ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2) := by
  classical
  set wt : E → ℝ := fun e => toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2
    with hwt
  have hwt0 : ∀ e, 0 ≤ wt e := fun e => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hvolW : ∀ (ρ : V → ℤ) (j : V),
      ((G.edgesWithin (G.densityDomain ρ j)).card : ℝ) ≤
        Kv * ((G.densityDiameter ρ : ℝ) + 1) ^ 2 := fun ρ j =>
    (Nat.cast_le.mpr (card_le_card (edgesWithin_subset_edgesTouching G _))).trans (hvol ρ j)
  set P : (V → ℤ) → ℝ := fun ρ => 8 *
    (toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) ^ 2 +
      (((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) * m *
        Real.sqrt (∑ e ∈ edgesTouching G (G.densityDomain ρ (ctr ρ)), θ e ^ 2)) ^ 2 +
      ((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) ^ 2 * m *
        Real.sqrt (∑ e ∈ edgesTouching G (G.densityDomain ρ (ctr ρ)), θ e ^ 2) ^ 2) with hPdef
  have hK₀ : 0 ≤ 8 * (Kv + 2 * Kv ^ 2) := by positivity
  have hP : ∀ ρ ∈ N,
      P ρ ≤ 8 * (Kv + 2 * Kv ^ 2) * ((G.densityDiameter ρ : ℝ) + 1) ^ 4 *
        (∑ x, |(ρ x : ℝ)|) ^ 4 * ∑ e ∈ edgesTouching G (G.densityDomain ρ (ctr ρ)), wt e := by
    intro ρ hρ
    set d : ℝ := (G.densityDiameter ρ : ℝ) with hd
    set X : ℝ := ∑ x, |(ρ x : ℝ)| with hX
    set D := edgesTouching G (G.densityDomain ρ (ctr ρ)) with hD
    set s := toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) with hs
    set Nc : ℝ := ((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) with hNc
    set S2 : ℝ := ∑ e ∈ D, θ e ^ 2 with hS2
    set T : ℝ := Real.sqrt S2 with hT
    set SW : ℝ := ∑ e ∈ D, toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 with hSW
    set Sw : ℝ := ∑ e ∈ G.edgesWithin (G.densityDomain ρ (ctr ρ)),
      toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 with hSw
    have hd1 : (1 : ℝ) ≤ d + 1 := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
    have hd24 : (d + 1) ^ 2 ≤ (d + 1) ^ 4 := pow_le_pow_right₀ hd1 (by norm_num)
    have hX2 : 2 ≤ X := two_le_sum_abs_of_neutral ρ (hne ρ hρ) (hneutral ρ hρ)
    have hX0 : 0 ≤ X := by linarith
    have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ (by linarith)
    have hsq : ∑ x, (ρ x : ℝ) ^ 2 ≤ X ^ 2 := by
      calc ∑ x, (ρ x : ℝ) ^ 2 = ∑ x, |(ρ x : ℝ)| ^ 2 :=
            Finset.sum_congr rfl fun x _ => (sq_abs _).symm
        _ ≤ X ^ 2 := sum_sq_le_sq_sum_of_nonneg fun x _ => abs_nonneg _
    have hsq2 : (∑ x, (ρ x : ℝ) ^ 2) ^ 2 ≤ X ^ 4 := by
      calc (∑ x, (ρ x : ℝ) ^ 2) ^ 2 ≤ (X ^ 2) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg fun x _ => sq_nonneg _) hsq 2
        _ = X ^ 4 := by ring
    have hSw0 : 0 ≤ Sw := Finset.sum_nonneg fun e _ => sq_nonneg _
    have hSW0 : 0 ≤ SW := Finset.sum_nonneg fun e _ => sq_nonneg _
    have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun e _ => sq_nonneg _
    have hSwSW : Sw ≤ SW :=
      Finset.sum_le_sum_of_subset_of_nonneg (edgesWithin_subset_edgesTouching G _)
        fun _ _ _ => sq_nonneg _
    have h1 : s ^ 2 ≤ Kv * (d + 1) ^ 2 * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 * Sw :=
      sq_toIcoMod_pairing_le_of_center G hG Kv hvolW ρ (hneutral ρ hρ) (ctr ρ) (hctr ρ hρ) σ
    have hY0 : 0 ≤ (d + 1) ^ 4 * X ^ 4 := by positivity
    have hA : s ^ 2 ≤ Kv * ((d + 1) ^ 4 * X ^ 4) * SW := by
      calc s ^ 2 ≤ Kv * (d + 1) ^ 2 * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 * Sw := h1
        _ ≤ Kv * (d + 1) ^ 4 * X ^ 4 * SW :=
            mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hd24 hKv) hsq2 (sq_nonneg _)
              (mul_nonneg hKv (by positivity))) hSwSW hSw0
              (mul_nonneg (mul_nonneg hKv (by positivity)) (by positivity))
        _ = Kv * ((d + 1) ^ 4 * X ^ 4) * SW := by ring
    have hfilt : (univ.filter fun e => bg ρ e ≠ 0) ⊆ D := fun e he =>
      hbg ρ hρ e (Finset.mem_filter.mp he).2
    have hNc : Nc ≤ Kv * (d + 1) ^ 2 :=
      (Nat.cast_le.mpr (card_le_card hfilt)).trans (hvol ρ (ctr ρ))
    have hNc0 : 0 ≤ Nc := Nat.cast_nonneg _
    have hNc2 : Nc ^ 2 ≤ Kv ^ 2 * (d + 1) ^ 4 := by
      calc Nc ^ 2 ≤ (Kv * (d + 1) ^ 2) ^ 2 := pow_le_pow_left₀ hNc0 hNc 2
        _ = Kv ^ 2 * (d + 1) ^ 4 := by ring
    have hT2 : T ^ 2 = S2 := Real.sq_sqrt hS20
    have hC : Nc ^ 2 * m * T ^ 2 ≤ Kv ^ 2 * ((d + 1) ^ 4 * X ^ 4) * S2 := by
      calc Nc ^ 2 * m * T ^ 2 = m * (Nc ^ 2 * S2) := by rw [hT2]; ring
        _ ≤ 1 * (Nc ^ 2 * S2) := mul_le_mul_of_nonneg_right hm1 (mul_nonneg (sq_nonneg _) hS20)
        _ = Nc ^ 2 * S2 := one_mul _
        _ ≤ Kv ^ 2 * (d + 1) ^ 4 * S2 := mul_le_mul_of_nonneg_right hNc2 hS20
        _ ≤ Kv ^ 2 * (d + 1) ^ 4 * S2 * X ^ 4 :=
            le_mul_of_one_le_right (mul_nonneg (by positivity) hS20) hX4
        _ = Kv ^ 2 * ((d + 1) ^ 4 * X ^ 4) * S2 := by ring
    have hCnn : 0 ≤ Nc ^ 2 * m * T ^ 2 := mul_nonneg (mul_nonneg (sq_nonneg _) hm0) (sq_nonneg _)
    have hB : (Nc * m * T) ^ 2 ≤ Kv ^ 2 * ((d + 1) ^ 4 * X ^ 4) * S2 := by
      calc (Nc * m * T) ^ 2 = m * (Nc ^ 2 * m * T ^ 2) := by ring
        _ ≤ 1 * (Nc ^ 2 * m * T ^ 2) := mul_le_mul_of_nonneg_right hm1 hCnn
        _ = Nc ^ 2 * m * T ^ 2 := one_mul _
        _ ≤ _ := hC
    have hsum : ∑ e ∈ D, wt e = SW + S2 := by
      rw [hwt, Finset.sum_add_distrib]
    have halg := shiftError_algebra hA hB hC
      (mul_nonneg (mul_nonneg hKv hY0) hS20) (mul_nonneg (mul_nonneg (sq_nonneg _) hY0) hSW0)
    calc P ρ = 8 * (s ^ 2 + (Nc * m * T) ^ 2 + Nc ^ 2 * m * T ^ 2) := rfl
      _ ≤ 8 * (Kv + 2 * Kv ^ 2) * ((d + 1) ^ 4 * X ^ 4) * (SW + S2) := halg
      _ = 8 * (Kv + 2 * Kv ^ 2) * (d + 1) ^ 4 * X ^ 4 * ∑ e ∈ D, wt e := by rw [hsum]; ring
  have hmain := sum_abs_mul_le_of_touching_center G hG (8 * (Kv + 2 * Kv ^ 2)) hK₀ 4 4 wt hwt0 P
    N hne hneutral ctr hctr hP hdisj z b ε hz hthr
  calc _ = ∑ ρ ∈ N, |z ρ| * P ρ := Finset.sum_congr rfl fun ρ _ => by rw [hPdef]; ring
    _ ≤ ε * ∑ e, wt e := hmain

end FroehlichSpencer.BKT.Generic

end
