/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.DensityRouting
public import FroehlichSpencer.BKT.Charges.DensityBall
public import FroehlichSpencer.BKT.Surface.DensityCenterExists
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# KP Claim 3.2

For an ensemble satisfying
properties (1)–(3) of the Theorem 1.6 and `β` below an explicit threshold,
`∑_{ϱ ∈ 𝒩} |z(ϱ)| ⟨σ, ϱ⟩² ≤ (β / D) ∑_e (∇_e σ)²`.

The proof has three steps:
* route each density through its domain `D_j(ϱ)` (`Multigraph.exists_integer_routing`);
* apply Cauchy–Schwarz on the edges inside the domain, whose number is at most
  `K₀ (d(ϱ) + 1)²` (`K₀ = 144` on the free and periodic squares, from
  `Charges/DensityBall.lean` and a neighbour count);
* use the T1.6 damping `|z| ≤ exp(-(c₁/β)(‖ϱ‖₂² + log₂(d+1)))` through a β threshold,
  then group by the scale `2^k ≤ d + 1 < 2^{k+1}`.

Within a scale the domains are disjoint
  (T1.6 (3)), and `∑_{k ≥ 1} 2^{-k} ≤ 1`.

The threshold is a hypothesis here; `ExpMoment/Claim32Threshold.lean` provides it.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open Finset

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

namespace Multigraph

/-- The edges with both endpoints in a vertex set. -/
def edgesWithin (G : Multigraph V E) (S : Set V) : Finset E := by
  classical
  exact univ.filter fun e => G.src e ∈ S ∧ G.tgt e ∈ S

omit [Fintype V] in
theorem mem_edgesWithin (G : Multigraph V E) {S : Set V} {e : E} :
    e ∈ G.edgesWithin S ↔ G.src e ∈ S ∧ G.tgt e ∈ S := by
  classical
  simp [edgesWithin]

end Multigraph

/-- A nonzero neutral integer density has `‖ϱ‖₂² ≥ 2`. -/
theorem two_le_sum_sq_of_neutral (ρ : V → ℤ) (hρ : ρ ≠ 0) (hsum : ∑ x, ρ x = 0) :
    (2 : ℝ) ≤ ∑ j, (ρ j : ℝ) ^ 2 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, ρ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hρ (funext h)
  obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ ρ y ≠ 0 := by
    by_contra h
    push Not at h
    have : ∑ j, ρ j = ρ x := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
      rw [Finset.sum_eq_zero fun j hj => h j (Finset.ne_of_mem_erase hj), zero_add]
    exact hx (this ▸ hsum)
  have h1 : (1 : ℝ) ≤ (ρ x : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ ρ x ^ 2 := by nlinarith [Int.one_le_abs hx, sq_abs (ρ x)]
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ (ρ y : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ ρ y ^ 2 := by nlinarith [Int.one_le_abs hy, sq_abs (ρ y)]
    exact_mod_cast this
  have hpair : (ρ x : ℝ) ^ 2 + (ρ y : ℝ) ^ 2 ≤ ∑ j, (ρ j : ℝ) ^ 2 := by
    have hsub : ({x, y} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => sq_nonneg (ρ j : ℝ))
    rwa [Finset.sum_pair hyx.symm] at this
  linarith

/-- The ℓ¹ norm of an integer density is at most its squared ℓ² norm. -/
theorem sum_abs_le_sum_sq (ρ : V → ℤ) : (∑ j, |(ρ j : ℝ)|) ≤ ∑ j, (ρ j : ℝ) ^ 2 := by
  refine Finset.sum_le_sum fun j _ => ?_
  have h : |ρ j| ≤ ρ j ^ 2 := by
    rcases eq_or_ne (ρ j) 0 with h0 | h0
    · simp [h0]
    · nlinarith [Int.one_le_abs h0, sq_abs (ρ j)]
  have : ((|ρ j| : ℤ) : ℝ) ≤ ((ρ j ^ 2 : ℤ) : ℝ) := by exact_mod_cast h
  simpa using this

/-- One density: routing and Cauchy–Schwarz inside the domain ( (b)–(d)). -/
theorem sq_pairing_le_of_center (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (K₀ : ℝ) (hvol : ∀ (ρ : V → ℤ) (j : V),
      ((G.edgesWithin (G.densityDomain ρ j)).card : ℝ) ≤ K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2)
    (ρ : V → ℤ) (hsum : ∑ x, ρ x = 0) (j : V) (hj : G.IsDensityCenter ρ j) (σ : V → ℝ) :
    (∑ x, σ x * (ρ x : ℝ)) ^ 2 ≤
      K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2 * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 *
        ∑ e ∈ G.edgesWithin (G.densityDomain ρ j), G.grad σ e ^ 2 := by
  classical
  obtain ⟨c, hcsupp, hcbound, hroute⟩ := G.exists_integer_routing hG ρ hsum j hj
  set S := G.edgesWithin (G.densityDomain ρ j)
  have hsumS : ∑ x, σ x * (ρ x : ℝ) = ∑ e ∈ S, (c e : ℝ) * G.grad σ e := by
    rw [hroute σ]
    refine (Finset.sum_subset (Finset.subset_univ S) fun e _ he => ?_).symm
    have : c e = 0 := by
      by_contra hne
      exact he ((G.mem_edgesWithin).2 (hcsupp e hne))
    simp [this]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun e => (c e : ℝ)) (G.grad σ)
  have hl1 : 0 ≤ ∑ x, |(ρ x : ℝ)| := Finset.sum_nonneg fun x _ => abs_nonneg _
  have hcsq : ∀ e ∈ S, (c e : ℝ) ^ 2 ≤ (∑ x, (ρ x : ℝ) ^ 2) ^ 2 := by
    intro e _
    have hce : |(c e : ℝ)| ≤ ∑ x, |(ρ x : ℝ)| := by
      have := hcbound e
      have h' : ((|c e| : ℤ) : ℝ) ≤ ((∑ x, |ρ x| : ℤ) : ℝ) := by exact_mod_cast this
      simpa using h'
    have h2 := (sum_abs_le_sum_sq ρ)
    calc (c e : ℝ) ^ 2 = |(c e : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ x, |(ρ x : ℝ)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hce 2
      _ ≤ (∑ x, (ρ x : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hl1 h2 2
  have hC : ∑ e ∈ S, (c e : ℝ) ^ 2 ≤
      K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2 * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 := by
    calc ∑ e ∈ S, (c e : ℝ) ^ 2 ≤ ∑ _e ∈ S, (∑ x, (ρ x : ℝ) ^ 2) ^ 2 :=
          Finset.sum_le_sum hcsq
      _ = (S.card : ℝ) * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K₀ * ((G.densityDiameter ρ : ℝ) + 1) ^ 2 * (∑ x, (ρ x : ℝ) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right (hvol ρ j) (sq_nonneg _)
  rw [hsumS]
  calc (∑ e ∈ S, (c e : ℝ) * G.grad σ e) ^ 2
      ≤ (∑ e ∈ S, (c e : ℝ) ^ 2) * ∑ e ∈ S, G.grad σ e ^ 2 := hcs
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun e _ => sq_nonneg _)

/-- The partial geometric sums `∑_{k=1}^{M} 2^{-k} = 1 - 2^{-M}`. -/
theorem sum_Icc_half_pow (M : ℕ) : ∑ k ∈ Finset.Icc 1 M, (1 / 2 : ℝ) ^ k = 1 - (1 / 2) ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]
      ring

/-- `∑_{k ∈ K} 2^{-k} ≤ 1` for a finite set of positive integers. -/
theorem sum_half_pow_le_one (K : Finset ℕ) (hK : ∀ k ∈ K, 1 ≤ k) :
    ∑ k ∈ K, (1 / 2 : ℝ) ^ k ≤ 1 := by
  have hsub : K ⊆ Finset.Icc 1 (K.sup id) := fun k hk =>
    Finset.mem_Icc.mpr ⟨hK k hk, Finset.le_sup (f := id) hk⟩
  calc ∑ k ∈ K, (1 / 2 : ℝ) ^ k
      ≤ ∑ k ∈ Finset.Icc 1 (K.sup id), (1 / 2 : ℝ) ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity
    _ = 1 - (1 / 2) ^ (K.sup id) := sum_Icc_half_pow _
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ (1 / 2) ^ (K.sup id) := by positivity
        linarith

/-- KP Claim 3.2 on a connected multigraph whose domains satisfy the edge-volume bound
`|E(D_j(ϱ))| ≤ K₀ (d(ϱ) + 1)²`. -/
theorem claim32 (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (K₀ : ℝ) (hK₀ : 0 ≤ K₀)
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
    ∑ ρ ∈ N, |z ρ| * (∑ j, σ j * (ρ j : ℝ)) ^ 2 ≤ β / D * ∑ e, G.grad σ e ^ 2 := by
  classical
  -- A chosen admissible center for every nonzero density.
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
    ∑ e ∈ G.edgesWithin (G.densityDomain ρ (ctr ρ)), G.grad σ e ^ 2 with hA
  set T : ℝ := ∑ e, G.grad σ e ^ 2 with hT
  set kf : (V → ℤ) → ℕ := fun ρ => Nat.log 2 (d ρ + 1) with hkf
  have hd1 : ∀ ρ ∈ N, 1 ≤ d ρ := fun ρ hρ =>
    G.one_le_densityDiameter_of_neutral hG ρ (hne ρ hρ) (hneutral ρ hρ)
  have hA0 : ∀ ρ, 0 ≤ A ρ := fun ρ => Finset.sum_nonneg fun e _ => sq_nonneg _
  -- Scale bounds.
  have hk1 : ∀ ρ ∈ N, 1 ≤ kf ρ := fun ρ hρ =>
    Nat.log_pos (by norm_num) (by have := hd1 ρ hρ; omega)
  have hklow : ∀ ρ, 2 ^ kf ρ ≤ d ρ + 1 := fun ρ => Nat.pow_log_le_self 2 (by omega)
  have hkup : ∀ ρ, d ρ + 1 < 2 ^ (kf ρ + 1) := fun ρ => Nat.lt_pow_succ_log_self (by norm_num) _
  -- Per-density bound with the damping.
  have hper : ∀ ρ ∈ N, |z ρ| * (∑ j, σ j * (ρ j : ℝ)) ^ 2 ≤
      β / D * ((1 / 2 : ℝ) ^ kf ρ * A ρ) := by
    intro ρ hρ
    have hdR : (1 : ℝ) ≤ (d ρ : ℝ) := by exact_mod_cast hd1 ρ hρ
    have hu := two_le_sum_sq_of_neutral ρ (hne ρ hρ) (hneutral ρ hρ)
    have hsq := sq_pairing_le_of_center G hG K₀ hvol ρ (hneutral ρ hρ) (ctr ρ)
      (hctr ρ (hne ρ hρ)) σ
    have hthr' := hthr (d ρ) (∑ j, (ρ j : ℝ) ^ 2) hdR hu
    have hzρ := hz ρ hρ
    set u := ∑ j, (ρ j : ℝ) ^ 2
    set X := Real.exp (-(c₁ / β) * (u + Real.logb 2 ((d ρ : ℝ) + 1)))
    have hX0 : 0 ≤ X := (Real.exp_pos _).le
    have hdpos : (0 : ℝ) < (d ρ : ℝ) + 1 := by linarith
    have hinv : 1 / ((d ρ : ℝ) + 1) ≤ (1 / 2 : ℝ) ^ kf ρ := by
      have h2 : ((2 ^ kf ρ : ℕ) : ℝ) ≤ (d ρ : ℝ) + 1 := by exact_mod_cast hklow ρ
      rw [Nat.cast_pow, Nat.cast_ofNat] at h2
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) h2
    -- |z| K₀ (d+1)² u² ≤ β / (D (d+1)).
    have hzK : |z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ 2 * u ^ 2) ≤ β / D / ((d ρ : ℝ) + 1) := by
      have hK₀' : 0 ≤ K₀ * ((d ρ : ℝ) + 1) ^ 2 * u ^ 2 := by positivity
      rw [le_div_iff₀ hdpos, le_div_iff₀ hD]
      calc |z ρ| * (K₀ * ((d ρ : ℝ) + 1) ^ 2 * u ^ 2) * ((d ρ : ℝ) + 1) * D
          = |z ρ| * (K₀ * D * ((d ρ : ℝ) + 1) ^ 3 * u ^ 2) := by ring
        _ ≤ X * (K₀ * D * ((d ρ : ℝ) + 1) ^ 3 * u ^ 2) :=
            mul_le_mul_of_nonneg_right hzρ (by positivity)
        _ = K₀ * D * ((d ρ : ℝ) + 1) ^ 3 * u ^ 2 * X := by ring
        _ ≤ β := hthr'
    calc |z ρ| * (∑ j, σ j * (ρ j : ℝ)) ^ 2
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
        = ∑ e ∈ C.biUnion (fun ρ => G.edgesWithin (G.densityDomain ρ (ctr ρ))),
            G.grad σ e ^ 2 := (Finset.sum_biUnion hdisjE).symm
      _ ≤ T := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun e _ _ => sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun e _ => sq_nonneg _
  have hgeom : ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k ≤ 1 := by
    refine sum_half_pow_le_one _ fun k hk => ?_
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hk
    exact hk1 ρ hρ
  calc ∑ ρ ∈ N, |z ρ| * (∑ j, σ j * (ρ j : ℝ)) ^ 2
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


/-!
### The edge-volume bound on the square domains
-/

/-- On a multigraph over `Fin L × Fin L` with the lattice distance and simple edge labels, a
vertex set `S` spans at most `9 |S|` edges (each edge goes from a vertex of `S` to one of the
at most nine vertices within distance one). -/
theorem card_edgesWithin_le_of_dist {L : ℕ} {E' : Type v} [Fintype E']
    (G : Multigraph (Fin L × Fin L) E') (boundary : SquareBoundary)
    (hdist : ∀ x y, G.toSimpleGraph.dist x y = latticeDistance boundary L x y)
    (hinj : Function.Injective fun e => (G.src e, G.tgt e)) (S : Finset (Fin L × Fin L)) :
    (G.edgesWithin (S : Set (Fin L × Fin L))).card ≤ 9 * S.card := by
  classical
  set ball : Fin L × Fin L → Finset (Fin L × Fin L) := fun a =>
    Finset.univ.filter fun x => latticeDistance boundary L x a ≤ 1
  have hmaps : ∀ e ∈ G.edgesWithin (S : Set (Fin L × Fin L)),
      (G.src e, G.tgt e) ∈ S.biUnion fun a => ({a} : Finset _) ×ˢ ball a := by
    intro e he
    obtain ⟨hs, -⟩ := (G.mem_edgesWithin).1 he
    have hadj : G.toSimpleGraph.Adj (G.src e) (G.tgt e) := by
      rw [Multigraph.toSimpleGraph, SimpleGraph.fromRel_adj]
      exact ⟨G.src_ne_tgt e, Or.inl ⟨e, Or.inl ⟨rfl, rfl⟩⟩⟩
    have hd1 : latticeDistance boundary L (G.tgt e) (G.src e) ≤ 1 := by
      rw [← hdist, SimpleGraph.dist_comm, SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
    refine Finset.mem_biUnion.mpr ⟨G.src e, Finset.mem_coe.mp hs, ?_⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd1⟩⟩
  calc (G.edgesWithin (S : Set (Fin L × Fin L))).card
      ≤ (S.biUnion fun a => ({a} : Finset _) ×ˢ ball a).card :=
        Finset.card_le_card_of_injOn _ hmaps (fun e _ e' _ h => hinj h)
    _ ≤ ∑ a ∈ S, (({a} : Finset _) ×ˢ ball a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S, 9 := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Finset.card_product, Finset.card_singleton, one_mul]
        have := card_latticeDistance_le_le boundary L 1 a
        simpa using this
    _ = 9 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/--
The edge-volume bound `|E(D_j(ϱ))| ≤ 144 (d(ϱ) + 1)²` on the free square.
-/
theorem card_edgesWithin_densityDomain_squareFree_le (L : ℕ) (ρ : Fin L × Fin L → ℤ)
    (j : Fin L × Fin L) :
    (((squareFree L).edgesWithin ((squareFree L).densityDomain ρ j)).card : ℝ) ≤
      144 * (((squareFree L).densityDiameter ρ : ℝ) + 1) ^ 2 := by
  classical
  set S := Finset.univ.filter fun x => x ∈ (squareFree L).densityDomain ρ j
  have hS : (squareFree L).densityDomain ρ j = (S : Set _) := by
    ext x
    simp [S]
  have hcard : S.card ≤ 16 * ((squareFree L).densityDiameter ρ + 1) ^ 2 := by
    have := ncard_densityDomain_squareFree_le L ρ j
    rwa [hS, Set.ncard_coe_finset] at this
  have hE := card_edgesWithin_le_of_dist (squareFree L) .free (fun _ _ => rfl)
    (fun e e' h => Subtype.ext (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))) S
  rw [hS]
  have : (((squareFree L).edgesWithin (S : Set _)).card : ℝ) ≤
      ((9 * (16 * ((squareFree L).densityDiameter ρ + 1) ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast hE.trans (Nat.mul_le_mul_left 9 hcard)
  calc _ ≤ ((9 * (16 * ((squareFree L).densityDiameter ρ + 1) ^ 2) : ℕ) : ℝ) := this
    _ = 144 * (((squareFree L).densityDiameter ρ : ℝ) + 1) ^ 2 := by push_cast; ring

/--
The edge-volume bound `|E(D_j(ϱ))| ≤ 144 (d(ϱ) + 1)²` on the periodic square.
-/
theorem card_edgesWithin_densityDomain_squarePeriodic_le (L : ℕ) (ρ : Fin L × Fin L → ℤ)
    (j : Fin L × Fin L) :
    (((squarePeriodic L).edgesWithin ((squarePeriodic L).densityDomain ρ j)).card : ℝ) ≤
      144 * (((squarePeriodic L).densityDiameter ρ : ℝ) + 1) ^ 2 := by
  classical
  set S := Finset.univ.filter fun x => x ∈ (squarePeriodic L).densityDomain ρ j
  have hS : (squarePeriodic L).densityDomain ρ j = (S : Set _) := by
    ext x
    simp [S]
  have hcard : S.card ≤ 16 * ((squarePeriodic L).densityDiameter ρ + 1) ^ 2 := by
    have := ncard_densityDomain_squarePeriodic_le L ρ j
    rwa [hS, Set.ncard_coe_finset] at this
  have hE := card_edgesWithin_le_of_dist (squarePeriodic L) .periodic (fun _ _ => rfl)
    (fun e e' h => Subtype.ext (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))) S
  rw [hS]
  have : (((squarePeriodic L).edgesWithin (S : Set _)).card : ℝ) ≤
      ((9 * (16 * ((squarePeriodic L).densityDiameter ρ + 1) ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast hE.trans (Nat.mul_le_mul_left 9 hcard)
  calc _ ≤ ((9 * (16 * ((squarePeriodic L).densityDiameter ρ + 1) ^ 2) : ℕ) : ℝ) := this
    _ = 144 * (((squarePeriodic L).densityDiameter ρ : ℝ) + 1) ^ 2 := by push_cast; ring

end FroehlichSpencer.BKT

end
