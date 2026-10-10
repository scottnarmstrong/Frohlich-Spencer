/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.ExpMoment.Claim32
public import FroehlichSpencer.BKT.ExpMoment.ReducedPhase
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import FroehlichSpencer.BKT.ExpMoment.BranchBound

/-!
# KP Claim 3.2 with reduced phases, and the modular branch bound

Write `[t]_{2π}` for
`toIcoMod Real.two_pi_pos (-π) t ∈ [-π, π)`.

* `claim32_of_pairing_le`: the scale sum of Claim 3.2, for any per-density quantity bounded by
  `K₀ (d+1)² ‖ϱ‖₂⁴` times a nonnegative edge weight summed over the domain `D_j(ϱ)`.
* `claim32_mod` (the cosine Jensen inequality): with an edge-volume bound and the T1.6 data,
  `∑_{ϱ ∈ 𝒩} |z(ϱ)| [⟨σ, ϱ⟩]_{2π}² ≤ (β / D) ∑_e [∇_e σ]_{2π}²`.

The routing coefficients are
  integers, so `[∑ c_e t_e]_{2π}` is at most `∑ |c_e| |[t_e]_{2π}|` (`abs_toIcoMod_sum_le`).
* `integral_prod_cos_shift_ge_mod` ( Step 3, KP (6.6)): the branch bound with the error
  term in the reduced phase, `D₄ = 2`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open Finset MeasureTheory

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

/-- The scale sum of KP Claim 3.2 ( (e)–(f)) for an abstract per-density quantity `P` and
nonnegative edge weight `w`: if `P ϱ ≤ K₀ (d+1)² ‖ϱ‖₂⁴ ∑_{e ∈ E(D_j(ϱ))} w e` at every admissible
center `j`, then `∑_{ϱ ∈ 𝒩} |z(ϱ)| P ϱ ≤ (β / D) ∑_e w e`. -/
theorem claim32_of_pairing_le (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (K₀ : ℝ)
    (hK₀ : 0 ≤ K₀) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) (P : (V → ℤ) → ℝ)
    (N : Finset (V → ℤ)) (hne : ∀ ρ ∈ N, ρ ≠ 0) (hneutral : ∀ ρ ∈ N, ∑ j, ρ j = 0)
    (hP : ∀ ρ ∈ N, ∀ j : V, G.IsDensityCenter ρ j →
      P ρ ≤ K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2 * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 *
        ∑ e ∈ G.edgesWithin (G.densityDomain ρ j), w e)
    (hdisj : ∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
      G.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      G.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      ∀ j₁ j₂ : V, G.IsDensityCenter ϱ₁ j₁ → G.IsDensityCenter ϱ₂ j₂ →
        G.densityDomain ϱ₁ j₁ ∩ G.densityDomain ϱ₂ j₂ = ∅)
    (z : (V → ℤ) → ℝ) (c₁ β D : ℝ) (hβ : 0 < β) (hD : 0 < D)
    (hz : ∀ ρ ∈ N, |z ρ| ≤ Real.exp (-(c₁ / β) *
      (∑ j, (ρ j : ℝ) ^ 2 + Real.logb 2 (G.densityDiameter ρ + 1))))
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      K₀ * D * (d + 1) ^ 3 * u ^ 2 * Real.exp (-(c₁ / β) * (u + Real.logb 2 (d + 1))) ≤ β) :
    ∑ ρ ∈ N, |z ρ| * P ρ ≤ β / D * ∑ e, w e := by
  classical
  have hcenter : ∀ ρ : V → ℤ, ∃ j : V, ρ ≠ 0 → G.IsDensityCenter ρ j := by
    intro ρ
    by_cases h : ρ = 0
    · obtain ⟨j⟩ := hG.nonempty
      exact ⟨j, fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := G.exists_isDensityCenter ρ h
      exact ⟨j, fun _ => hj⟩
  choose ctr hctr using hcenter
  set d : (V → ℤ) → ℕ := fun ρ => G.densityDiameter ρ with hd
  set A : (V → ℤ) → ℝ := fun ρ =>
    ∑ e ∈ G.edgesWithin (G.densityDomain ρ (ctr ρ)), w e with hA
  set T : ℝ := ∑ e, w e with hT
  set kf : (V → ℤ) → ℕ := fun ρ => Nat.log 2 (d ρ + 1) with hkf
  have hd1 : ∀ ρ ∈ N, 1 ≤ d ρ := fun ρ hρ =>
    G.one_le_densityDiameter_of_neutral hG ρ (hne ρ hρ) (hneutral ρ hρ)
  have hA0 : ∀ ρ, 0 ≤ A ρ := fun ρ => Finset.sum_nonneg fun e _ => hw e
  have hk1 : ∀ ρ ∈ N, 1 ≤ kf ρ := fun ρ hρ =>
    Nat.log_pos (by norm_num) (by have := hd1 ρ hρ; omega)
  have hklow : ∀ ρ, 2 ^ kf ρ ≤ d ρ + 1 := fun ρ => Nat.pow_log_le_self 2 (by omega)
  have hkup : ∀ ρ, d ρ + 1 < 2 ^ (kf ρ + 1) := fun ρ => Nat.lt_pow_succ_log_self (by norm_num) _
  -- Per-density bound with the damping.
  have hper : ∀ ρ ∈ N, |z ρ| * P ρ ≤ β / D * ((1 / 2 : ℝ) ^ kf ρ * A ρ) := by
    intro ρ hρ
    have hdR : (1 : ℝ) ≤ (d ρ : ℝ) := by exact_mod_cast hd1 ρ hρ
    have hu := two_le_sum_sq_of_neutral ρ (hne ρ hρ) (hneutral ρ hρ)
    have hsq := hP ρ hρ (ctr ρ) (hctr ρ (hne ρ hρ))
    have hthr' := hthr (d ρ) (∑ j, (ρ j : ℝ) ^ 2) hdR hu
    have hzρ := hz ρ hρ
    set u := ∑ j, (ρ j : ℝ) ^ 2
    set X := Real.exp (-(c₁ / β) * (u + Real.logb 2 ((d ρ : ℝ) + 1)))
    have hdpos : (0 : ℝ) < (d ρ : ℝ) + 1 := by linarith
    have hinv : 1 / ((d ρ : ℝ) + 1) ≤ (1 / 2 : ℝ) ^ kf ρ := by
      have h2 : ((2 ^ kf ρ : ℕ) : ℝ) ≤ (d ρ : ℝ) + 1 := by exact_mod_cast hklow ρ
      rw [Nat.cast_pow, Nat.cast_ofNat] at h2
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) h2
    have hzK : |z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ 2 * u ^ 2) ≤ β / D / ((d ρ : ℝ) + 1) := by
      rw [le_div_iff₀ hdpos, le_div_iff₀ hD]
      calc |z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ 2 * u ^ 2) * ((d ρ : ℝ) + 1) * D
          = |z ρ| * (K₀ * D * ((d ρ : ℝ) + 1) ^ 3 * u ^ 2) := by ring
        _ ≤ X * (K₀ * D * ((d ρ : ℝ) + 1) ^ 3 * u ^ 2) :=
            mul_le_mul_of_nonneg_right hzρ (by positivity)
        _ = K₀ * D * ((d ρ : ℝ) + 1) ^ 3 * u ^ 2 * X := by ring
        _ ≤ β := hthr'
    calc |z ρ| * P ρ
        ≤ |z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ 2 * u ^ 2 * A ρ) :=
          mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
      _ = (|z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ 2 * u ^ 2)) * A ρ := by ring
      _ ≤ (β / D / ((d ρ : ℝ) + 1)) * A ρ := mul_le_mul_of_nonneg_right hzK (hA0 ρ)
      _ = β / D * (1 / ((d ρ : ℝ) + 1) * A ρ) := by ring
      _ ≤ β / D * ((1 / 2 : ℝ) ^ kf ρ * A ρ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv (hA0 ρ))
            (div_nonneg hβ.le hD.le)
  -- Within one scale the edge sets are disjoint.
  have hclass : ∀ k ∈ N.image kf, ∑ ρ ∈ N with kf ρ = k, A ρ ≤ T := by
    intro k _
    set C := N.filter fun ρ => kf ρ = k
    have hdisjE : Set.PairwiseDisjoint (C : Set (V → ℤ))
        fun ρ => G.edgesWithin (G.densityDomain ρ (ctr ρ)) := by
      intro ρ hρ ρ' hρ' hne'
      have hρN := (Finset.mem_filter.mp hρ).1
      have hρ'N := (Finset.mem_filter.mp hρ').1
      have hkρ : kf ρ = k := (Finset.mem_filter.mp hρ).2
      have hkρ' : kf ρ' = k := (Finset.mem_filter.mp hρ').2
      have hk : 1 ≤ k := hkρ ▸ hk1 ρ hρN
      have hIcc : ∀ x ∈ N, kf x = k →
          G.densityDiameter x ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) := by
        intro x _ hkx
        have hl := hklow x
        have hu := hkup x
        rw [hkx] at hl hu
        simp only [hd] at hl hu
        generalize 2 ^ k = P at hl hu ⊢
        generalize 2 ^ (k + 1) = Q at hl hu ⊢
        exact ⟨by omega, by omega⟩
      have hempty := hdisj ρ hρN ρ' hρ'N hne' k hk (hIcc ρ hρN hkρ) (hIcc ρ' hρ'N hkρ')
        (ctr ρ) (ctr ρ') (hctr ρ (hne ρ hρN)) (hctr ρ' (hne ρ' hρ'N))
      rw [Function.onFun, Finset.disjoint_left]
      intro e he he'
      have h1 := ((G.mem_edgesWithin).1 he).1
      have h2 := ((G.mem_edgesWithin).1 he').1
      have : G.src e ∈ G.densityDomain ρ (ctr ρ) ∩ G.densityDomain ρ' (ctr ρ') := ⟨h1, h2⟩
      rw [hempty] at this
      exact this
    calc ∑ ρ ∈ C, A ρ
        = ∑ e ∈ C.biUnion (fun ρ => G.edgesWithin (G.densityDomain ρ (ctr ρ))), w e :=
          (Finset.sum_biUnion hdisjE).symm
      _ ≤ T := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun e _ _ => hw e
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun e _ => hw e
  have hgeom : ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k ≤ 1 := by
    refine sum_half_pow_le_one _ fun k hk => ?_
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hk
    exact hk1 ρ hρ
  calc ∑ ρ ∈ N, |z ρ| * P ρ
      ≤ ∑ ρ ∈ N, β / D * ((1 / 2 : ℝ) ^ kf ρ * A ρ) := Finset.sum_le_sum hper
    _ = β / D * ∑ ρ ∈ N, (1 / 2 : ℝ) ^ kf ρ * A ρ := by rw [Finset.mul_sum]
    _ ≤ β / D * T := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hβ.le hD.le)
        rw [← Finset.sum_fiberwise_of_maps_to (t := N.image kf)
          (fun ρ hρ => Finset.mem_image_of_mem kf hρ)]
        calc ∑ k ∈ N.image kf, ∑ ρ ∈ N with kf ρ = k, (1 / 2 : ℝ) ^ kf ρ * A ρ
            = ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k * ∑ ρ ∈ N with kf ρ = k, A ρ := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun ρ hρ => ?_
              rw [(Finset.mem_filter.mp hρ).2]
          _ ≤ ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k * T :=
              Finset.sum_le_sum fun k hk =>
                mul_le_mul_of_nonneg_left (hclass k hk) (by positivity)
          _ = (∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k) * T := by rw [Finset.sum_mul]
          _ ≤ 1 * T := mul_le_mul_of_nonneg_right hgeom hT0
          _ = T := one_mul T

/-- One density with reduced phases ( (b)–(d)): routing through `D_j(ϱ)`, the integer
routing coefficients, and Cauchy–Schwarz on the edges inside the domain. -/
theorem sq_toIcoMod_pairing_le_of_center (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (K₀ : ℝ) (hvol : ∀ (ρ : V → ℤ) (j : V),
      ((G.edgesWithin (G.densityDomain ρ j)).card : ℝ) ≤ K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2)
    (ρ : V → ℤ) (hsum : ∑ x, ρ x = 0) (j : V) (hj : G.IsDensityCenter ρ j) (σ : V → ℝ) :
    toIcoMod Real.two_pi_pos (-Real.pi) (∑ x, σ x * (ρ x : ℝ)) ^ 2 ≤
      K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2 * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 *
        ∑ e ∈ G.edgesWithin (G.densityDomain ρ j),
          toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 := by
  classical
  obtain ⟨c, hcsupp, hcbound, hroute⟩ := G.exists_integer_routing hG ρ hsum j hj
  set S := G.edgesWithin (G.densityDomain ρ j)
  set r : E → ℝ := fun e => |toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e)| with hr
  have hsumS : ∑ x, σ x * (ρ x : ℝ) = ∑ e ∈ S, (c e : ℝ) * G.grad σ e := by
    rw [hroute σ]
    refine (Finset.sum_subset (Finset.subset_univ S) fun e _ he => ?_).symm
    have : c e = 0 := by
      by_contra hne
      exact he ((G.mem_edgesWithin).2 (hcsupp e hne))
    simp [this]
  have hmod := abs_toIcoMod_sum_le S c (G.grad σ)
  rw [← hsumS] at hmod
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun e => |(c e : ℝ)|) r
  have hl1 : 0 ≤ ∑ x, |(ρ x : ℝ)| := Finset.sum_nonneg fun x _ => abs_nonneg _
  have hcsq : ∀ e ∈ S, |(c e : ℝ)| ^ 2 ≤ (∑ x, (ρ x : ℝ) ^ 2) ^ 2 := by
    intro e _
    have hce : |(c e : ℝ)| ≤ ∑ x, |(ρ x : ℝ)| := by
      have := hcbound e
      have h' : ((|c e| : ℤ) : ℝ) ≤ ((∑ x, |ρ x| : ℤ) : ℝ) := by exact_mod_cast this
      simpa using h'
    exact (pow_le_pow_left₀ (abs_nonneg _) hce 2).trans
      (pow_le_pow_left₀ hl1 (sum_abs_le_sum_sq ρ) 2)
  have hC : ∑ e ∈ S, |(c e : ℝ)| ^ 2 ≤
      K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2 * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 := by
    calc ∑ e ∈ S, |(c e : ℝ)| ^ 2 ≤ ∑ _e ∈ S, (∑ x, (ρ x : ℝ) ^ 2) ^ 2 :=
          Finset.sum_le_sum hcsq
      _ = (S.card : ℝ) * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2 * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right (hvol ρ j) (sq_nonneg _)
  have hr2 : ∑ e ∈ S, r e ^ 2 =
      ∑ e ∈ S, toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 :=
    Finset.sum_congr rfl fun e _ => sq_abs _
  have hR0 : 0 ≤ ∑ e ∈ S, |(c e : ℝ)| * r e :=
    Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc toIcoMod Real.two_pi_pos (-Real.pi) (∑ x, σ x * (ρ x : ℝ)) ^ 2
      = |toIcoMod Real.two_pi_pos (-Real.pi) (∑ x, σ x * (ρ x : ℝ))| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ e ∈ S, |(c e : ℝ)| * r e) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmod 2
    _ ≤ (∑ e ∈ S, |(c e : ℝ)| ^ 2) * ∑ e ∈ S, r e ^ 2 := hcs
    _ ≤ _ := by
        rw [hr2]
        exact mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun e _ => sq_nonneg _)

/-- KP Claim 3.2 with reduced phases (the cosine Jensen inequality; KP (6.16)) on a connected multigraph
whose domains satisfy the edge-volume bound `|E(D_j(ϱ))| ≤ K₀ (d(ϱ) + 1)²`. -/
theorem claim32_mod (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (K₀ : ℝ)
    (hK₀ : 0 ≤ K₀)
    (hvol : ∀ (ρ : V → ℤ) (j : V),
      ((G.edgesWithin (G.densityDomain ρ j)).card : ℝ) ≤ K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2)
    (N : Finset (V → ℤ)) (hne : ∀ ρ ∈ N, ρ ≠ 0) (hneutral : ∀ ρ ∈ N, ∑ j, ρ j = 0)
    (hdisj : ∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
      G.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      G.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      ∀ j₁ j₂ : V, G.IsDensityCenter ϱ₁ j₁ → G.IsDensityCenter ϱ₂ j₂ →
        G.densityDomain ϱ₁ j₁ ∩ G.densityDomain ϱ₂ j₂ = ∅)
    (z : (V → ℤ) → ℝ) (c₁ β D : ℝ) (hβ : 0 < β) (hD : 0 < D)
    (hz : ∀ ρ ∈ N, |z ρ| ≤ Real.exp (-(c₁ / β) *
      (∑ j, (ρ j : ℝ) ^ 2 + Real.logb 2 (G.densityDiameter ρ + 1))))
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      K₀ * D * (d + 1) ^ 3 * u ^ 2 * Real.exp (-(c₁ / β) * (u + Real.logb 2 (d + 1))) ≤ β)
    (σ : V → ℝ) :
    ∑ ρ ∈ N, |z ρ| * toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) ^ 2 ≤
      β / D * ∑ e, toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 :=
  claim32_of_pairing_le G hG K₀ hK₀
    (fun e => toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2) (fun _ => sq_nonneg _)
    (fun ρ => toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) ^ 2) N hne hneutral
    (fun ρ hρ j hj => sq_toIcoMod_pairing_le_of_center G hG K₀ hvol ρ (hneutral ρ hρ) j hj σ)
    hdisj z c₁ β D hβ hD hz hthr

/-- Shifting by the reduced phase does not change a cosine: `cos (x + [y]_{2π}) = cos (x + y)`. -/
theorem cos_add_toIcoMod (x y : ℝ) :
    Real.cos (x + toIcoMod Real.two_pi_pos (-Real.pi) y) = Real.cos (x + y) := by
  have h := self_sub_toIcoMod Real.two_pi_pos (-Real.pi) y
  rw [zsmul_eq_mul] at h
  have hy : x + y = x + toIcoMod Real.two_pi_pos (-Real.pi) y +
      (toIcoDiv Real.two_pi_pos (-Real.pi) y : ℤ) * (2 * Real.pi) := by linarith
  rw [hy, Real.cos_add_int_mul_two_pi]

/-- KP (6.6),  Step 3: the per-branch bound with the quadratic error in the reduced phase,
for an even probability measure (`D₄ = 2`). -/
theorem integral_prod_cos_shift_ge_mod {ι : Type*} (μ : Measure (V → ℝ))
    [IsProbabilityMeasure μ] (hμ : μ.map (fun φ => -φ) = μ) (s : Finset ι) (a : ι → V → ℝ)
    (y z : ι → ℝ) (hz : ∀ i ∈ s, |z i| < 1 / 8) :
    Real.exp (-∑ i ∈ s, 2 * |z i| * toIcoMod Real.two_pi_pos (-Real.pi) (y i) ^ 2) *
        ∫ φ, ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j)) ∂μ ≤
      ∫ φ, ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j + y i)) ∂μ := by
  have h := integral_prod_cos_shift_ge μ hμ s a
    (fun i => toIcoMod Real.two_pi_pos (-Real.pi) (y i)) z hz
  simp only [cos_add_toIcoMod] at h
  exact h

end FroehlichSpencer.BKT

end
