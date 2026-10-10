/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.Aggregate
public import FroehlichSpencer.BKT.Generic.Moment.Packing
public import FroehlichSpencer.BKT.ExpMoment.ReducedPhase

/-!
# The packing estimate with local edge sets (generic core, rooted variant)

The KP-domain form
(`sum_abs_mul_le_of_touching_center`, `sum_shiftError_le`) uses KP's graph-ball domains
`D_j(ϱ)`.

On the augmented pinned carrier of FS81 Theorem C (`squareZero L`, the wired root a
high-degree hub) the graph balls are not local, so the rooted variant  works with
abstract per-density edge sets `S(ϱ)`:

* `sum_abs_mul_le_of_overlap`: if `P(ϱ) ≤ K₀ (d+1)^p ‖ϱ‖₁^q ∑_{e∈S(ϱ)} w(e)` with an abstract
  scale `d = dsc ϱ ≥ 1`, at most `Kov` sets `S(ϱ)` of one dyadic scale share an edge, the
  activities decay as `e^{-b(‖ϱ‖₁ + log₂(d+1))}` and the threshold holds, then
  `∑_ϱ |z(ϱ)| P(ϱ) ≤ ε ∑_e w(e)`;
* `sum_shiftError_le_local`: the second-order errors of the real shift are packed in this way,
  the phase term being bounded through an integer routing of `ϱ` supported in `S(ϱ)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open Finset

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **The packing estimate with local edge sets and bounded same-scale overlap** (KP Claim 3.2,
; FS81 (6.40)–(6.44), ). -/
theorem sum_abs_mul_le_of_overlap (dsc : (V → ℤ) → ℕ) (S : (V → ℤ) → Finset E) (Kov : ℕ)
    (K₀ : ℝ) (hK₀ : 0 ≤ K₀) (p q : ℕ) (wt : E → ℝ) (hwt : ∀ e, 0 ≤ wt e) (P : (V → ℤ) → ℝ)
    (N : Finset (V → ℤ)) (hne : ∀ ρ ∈ N, ρ ≠ 0) (hneutral : ∀ ρ ∈ N, ∑ j, ρ j = 0)
    (hdsc : ∀ ρ ∈ N, 1 ≤ dsc ρ)
    (hP : ∀ ρ ∈ N, P ρ ≤ K₀ * ((dsc ρ : ℝ) + 1) ^ p * (∑ x, |(ρ x : ℝ)|) ^ q * ∑ e ∈ S ρ, wt e)
    (hov : ∀ (k : ℕ) (e : E) (T : Finset (V → ℤ)), T ⊆ N →
      (∀ ρ ∈ T, 2 ^ k - 1 ≤ dsc ρ ∧ dsc ρ ≤ 2 ^ (k + 1) - 2 ∧ e ∈ S ρ) → T.card ≤ Kov)
    (z : (V → ℤ) → ℝ) (b ε : ℝ)
    (hz : ∀ ρ ∈ N, |z ρ| ≤ Real.exp (-b * (∑ x, |(ρ x : ℝ)| + Real.logb 2 (dsc ρ + 1))))
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      (Kov : ℝ) * K₀ * (d + 1) ^ (p + 1) * u ^ q * Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤
        ε) :
    ∑ ρ ∈ N, |z ρ| * P ρ ≤ ε * ∑ e, wt e := by
  classical
  set A : (V → ℤ) → ℝ := fun ρ => ∑ e ∈ S ρ, wt e with hA
  set T : ℝ := ∑ e, wt e with hT
  set kf : (V → ℤ) → ℕ := fun ρ => Nat.log 2 (dsc ρ + 1) with hkf
  have hε : 0 ≤ ε := by
    refine le_trans ?_ (hthr 1 2 le_rfl le_rfl)
    positivity
  have hA0 : ∀ ρ, 0 ≤ A ρ := fun ρ => Finset.sum_nonneg fun e _ => hwt e
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun e _ => hwt e
  have hk1 : ∀ ρ ∈ N, 1 ≤ kf ρ := fun ρ hρ =>
    Nat.log_pos (by norm_num) (by have := hdsc ρ hρ; omega)
  have hklow : ∀ ρ, 2 ^ kf ρ ≤ dsc ρ + 1 := fun ρ => Nat.pow_log_le_self 2 (by omega)
  have hkup : ∀ ρ, dsc ρ + 1 < 2 ^ (kf ρ + 1) := fun ρ =>
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hband : ∀ ρ, 2 ^ kf ρ - 1 ≤ dsc ρ ∧ dsc ρ ≤ 2 ^ (kf ρ + 1) - 2 := by
    intro ρ
    have hl := hklow ρ
    have hu := hkup ρ
    generalize 2 ^ kf ρ = P at hl hu ⊢
    generalize 2 ^ (kf ρ + 1) = Q at hl hu ⊢
    exact ⟨by omega, by omega⟩
  -- within one scale every edge lies in at most `Kov` of the sets
  have hclass : ∀ k, ∑ ρ ∈ N with kf ρ = k, A ρ ≤ Kov * T := by
    intro k
    set C := N.filter fun ρ => kf ρ = k with hC
    have hswap : ∑ ρ ∈ C, A ρ = ∑ e, wt e * ((C.filter fun ρ => e ∈ S ρ).card : ℝ) := by
      have h1 : ∀ ρ, A ρ = ∑ e, if e ∈ S ρ then wt e else 0 := fun ρ => by
        rw [hA, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hcount : ∀ e, ((C.filter fun ρ => e ∈ S ρ).card : ℝ) ≤ Kov := by
      intro e
      have hsub : (C.filter fun ρ => e ∈ S ρ) ⊆ N := fun ρ hρ =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).1
      have hmem : ∀ ρ ∈ (C.filter fun ρ => e ∈ S ρ),
          2 ^ k - 1 ≤ dsc ρ ∧ dsc ρ ≤ 2 ^ (k + 1) - 2 ∧ e ∈ S ρ := by
        intro ρ hρ
        obtain ⟨hρC, heS⟩ := Finset.mem_filter.mp hρ
        have hkρ : kf ρ = k := (Finset.mem_filter.mp hρC).2
        have hb := hband ρ
        rw [hkρ] at hb
        exact ⟨hb.1, hb.2, heS⟩
      exact_mod_cast hov k e _ hsub hmem
    rw [hswap, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [mul_comm (Kov : ℝ)]
    exact mul_le_mul_of_nonneg_left (hcount e) (hwt e)
  -- the per-density bound with the damping
  have hper : ∀ ρ ∈ N, (Kov : ℝ) * (|z ρ| * P ρ) ≤ ε * ((1 / 2 : ℝ) ^ kf ρ * A ρ) := by
    intro ρ hρ
    have hdR : (1 : ℝ) ≤ (dsc ρ : ℝ) := by exact_mod_cast hdsc ρ hρ
    have hu := two_le_sum_abs_of_neutral ρ (hne ρ hρ) (hneutral ρ hρ)
    have hPρ := hP ρ hρ
    have hthr' := hthr (dsc ρ) (∑ j, |(ρ j : ℝ)|) hdR hu
    have hzρ := hz ρ hρ
    set u := ∑ j, |(ρ j : ℝ)|
    set X := Real.exp (-b * (u + Real.logb 2 ((dsc ρ : ℝ) + 1)))
    have hdpos : (0 : ℝ) < (dsc ρ : ℝ) + 1 := by linarith
    have hinv : 1 / ((dsc ρ : ℝ) + 1) ≤ (1 / 2 : ℝ) ^ kf ρ := by
      have h2 : ((2 ^ kf ρ : ℕ) : ℝ) ≤ (dsc ρ : ℝ) + 1 := by exact_mod_cast hklow ρ
      rw [Nat.cast_pow, Nat.cast_ofNat] at h2
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) h2
    have hu0 : 0 ≤ u := by positivity
    have hzK : (Kov : ℝ) * (|z ρ| * (K₀ * ((dsc ρ : ℝ) + 1) ^ p * u ^ q)) ≤
        ε / ((dsc ρ : ℝ) + 1) := by
      rw [le_div_iff₀ hdpos]
      calc (Kov : ℝ) * (|z ρ| * (K₀ * ((dsc ρ : ℝ) + 1) ^ p * u ^ q)) * ((dsc ρ : ℝ) + 1)
          = |z ρ| * ((Kov : ℝ) * K₀ * ((dsc ρ : ℝ) + 1) ^ (p + 1) * u ^ q) := by ring
        _ ≤ X * ((Kov : ℝ) * K₀ * ((dsc ρ : ℝ) + 1) ^ (p + 1) * u ^ q) :=
            mul_le_mul_of_nonneg_right hzρ (by positivity)
        _ = (Kov : ℝ) * K₀ * ((dsc ρ : ℝ) + 1) ^ (p + 1) * u ^ q * X := by ring
        _ ≤ ε := hthr'
    calc (Kov : ℝ) * (|z ρ| * P ρ)
        ≤ (Kov : ℝ) * (|z ρ| * (K₀ * ((dsc ρ : ℝ) + 1) ^ p * u ^ q * A ρ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPρ (abs_nonneg _))
            (Nat.cast_nonneg _)
      _ = ((Kov : ℝ) * (|z ρ| * (K₀ * ((dsc ρ : ℝ) + 1) ^ p * u ^ q))) * A ρ := by ring
      _ ≤ (ε / ((dsc ρ : ℝ) + 1)) * A ρ := mul_le_mul_of_nonneg_right hzK (hA0 ρ)
      _ = ε * (1 / ((dsc ρ : ℝ) + 1) * A ρ) := by ring
      _ ≤ ε * ((1 / 2 : ℝ) ^ kf ρ * A ρ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv (hA0 ρ)) hε
  have hgeom : ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k ≤ 1 := by
    refine sum_half_pow_le_one _ fun k hk => ?_
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hk
    exact hk1 ρ hρ
  have hmain : (Kov : ℝ) * ∑ ρ ∈ N, |z ρ| * P ρ ≤ ε * ((Kov : ℝ) * T) := by
    rw [Finset.mul_sum]
    calc ∑ ρ ∈ N, (Kov : ℝ) * (|z ρ| * P ρ)
        ≤ ∑ ρ ∈ N, ε * ((1 / 2 : ℝ) ^ kf ρ * A ρ) := Finset.sum_le_sum hper
      _ = ε * ∑ ρ ∈ N, (1 / 2 : ℝ) ^ kf ρ * A ρ := by rw [Finset.mul_sum]
      _ ≤ ε * ((Kov : ℝ) * T) := by
          refine mul_le_mul_of_nonneg_left ?_ hε
          rw [← Finset.sum_fiberwise_of_maps_to (t := N.image kf)
            (fun ρ hρ => Finset.mem_image_of_mem kf hρ)]
          calc ∑ k ∈ N.image kf, ∑ ρ ∈ N with kf ρ = k, (1 / 2 : ℝ) ^ kf ρ * A ρ
              = ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k * ∑ ρ ∈ N with kf ρ = k, A ρ := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun ρ hρ => ?_
                rw [(Finset.mem_filter.mp hρ).2]
            _ ≤ ∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k * ((Kov : ℝ) * T) :=
                Finset.sum_le_sum fun k _ =>
                  mul_le_mul_of_nonneg_left (hclass k) (by positivity)
            _ = (∑ k ∈ N.image kf, (1 / 2 : ℝ) ^ k) * ((Kov : ℝ) * T) := by
                rw [Finset.sum_mul]
            _ ≤ 1 * ((Kov : ℝ) * T) := mul_le_mul_of_nonneg_right hgeom (by positivity)
            _ = (Kov : ℝ) * T := one_mul _
  rcases Nat.eq_zero_or_pos Kov with h0 | hpos
  · -- no set `S ϱ` contains an edge
    have hS : ∀ ρ ∈ N, S ρ = ∅ := by
      intro ρ hρ
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      have := hov (kf ρ) e {ρ} (Finset.singleton_subset_iff.mpr hρ) (fun ρ' hρ' => by
        rw [Finset.mem_singleton] at hρ'
        subst hρ'
        exact ⟨(hband ρ').1, (hband ρ').2, he⟩)
      rw [Finset.card_singleton, h0] at this
      omega
    calc ∑ ρ ∈ N, |z ρ| * P ρ ≤ ∑ _ρ ∈ N, (0 : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          have hPρ := hP ρ hρ
          rw [hS ρ hρ, Finset.sum_empty, mul_zero] at hPρ
          exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hPρ
      _ = 0 := Finset.sum_const_zero
      _ ≤ ε * ∑ e, wt e := mul_nonneg hε hT0
  · have hK : (0 : ℝ) < Kov := by exact_mod_cast hpos
    have h' : (Kov : ℝ) * ∑ ρ ∈ N, |z ρ| * P ρ ≤ (Kov : ℝ) * (ε * T) := by
      calc (Kov : ℝ) * ∑ ρ ∈ N, |z ρ| * P ρ ≤ ε * ((Kov : ℝ) * T) := hmain
        _ = (Kov : ℝ) * (ε * T) := by ring
    exact le_of_mul_le_mul_left h' hK

/-- **Packing of the real-shift errors with local edge sets** (FS81 (6.40)–(6.44), KP  The phase term is routed through an integer flow of `ϱ` supported in `S(ϱ)`. -/
theorem sum_shiftError_le_local (G : Multigraph V E) (dsc : (V → ℤ) → ℕ)
    (S : (V → ℤ) → Finset E) (Kv : ℝ) (hKv : 0 ≤ Kv) (Kov : ℕ)
    (N : Finset (V → ℤ)) (hne : ∀ ρ ∈ N, ρ ≠ 0) (hneutral : ∀ ρ ∈ N, ∑ j, ρ j = 0)
    (hdsc : ∀ ρ ∈ N, 1 ≤ dsc ρ)
    (hcard : ∀ ρ ∈ N, ((S ρ).card : ℝ) ≤ Kv * ((dsc ρ : ℝ) + 1) ^ 2)
    (hroute : ∀ ρ ∈ N, ∃ r : E → ℤ, (∀ e, r e ≠ 0 → e ∈ S ρ) ∧
      (∀ e, |(r e : ℝ)| ≤ ∑ j, |(ρ j : ℝ)|) ∧
      ∀ σ : V → ℝ, ∑ j, σ j * (ρ j : ℝ) = ∑ e, (r e : ℝ) * G.grad σ e)
    (hov : ∀ (k : ℕ) (e : E) (T : Finset (V → ℤ)), T ⊆ N →
      (∀ ρ ∈ T, 2 ^ k - 1 ≤ dsc ρ ∧ dsc ρ ≤ 2 ^ (k + 1) - 2 ∧ e ∈ S ρ) → T.card ≤ Kov)
    (bg : (V → ℤ) → E → ℝ) (hbg : ∀ ρ ∈ N, ∀ e, bg ρ e ≠ 0 → e ∈ S ρ)
    (m : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (z : (V → ℤ) → ℝ) (b ε : ℝ)
    (hz : ∀ ρ ∈ N, |z ρ| ≤ Real.exp (-b * (∑ x, |(ρ x : ℝ)| + Real.logb 2 (dsc ρ + 1))))
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    (σ : V → ℝ) (θ : E → ℝ) :
    ∑ ρ ∈ N, 8 * |z ρ| *
        (toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) ^ 2 +
          (((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) * m *
            Real.sqrt (∑ e ∈ S ρ, θ e ^ 2)) ^ 2 +
          ((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) ^ 2 * m *
            Real.sqrt (∑ e ∈ S ρ, θ e ^ 2) ^ 2) ≤
      ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2) := by
  classical
  set wt : E → ℝ := fun e => toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2
    with hwt
  have hwt0 : ∀ e, 0 ≤ wt e := fun e => add_nonneg (sq_nonneg _) (sq_nonneg _)
  set P : (V → ℤ) → ℝ := fun ρ => 8 *
    (toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) ^ 2 +
      (((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) * m *
        Real.sqrt (∑ e ∈ S ρ, θ e ^ 2)) ^ 2 +
      ((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) ^ 2 * m *
        Real.sqrt (∑ e ∈ S ρ, θ e ^ 2) ^ 2) with hPdef
  have hK₀ : 0 ≤ 8 * (Kv + 2 * Kv ^ 2) := by positivity
  have hP : ∀ ρ ∈ N,
      P ρ ≤ 8 * (Kv + 2 * Kv ^ 2) * ((dsc ρ : ℝ) + 1) ^ 4 *
        (∑ x, |(ρ x : ℝ)|) ^ 4 * ∑ e ∈ S ρ, wt e := by
    intro ρ hρ
    set d : ℝ := (dsc ρ : ℝ) with hd
    set X : ℝ := ∑ x, |(ρ x : ℝ)| with hX
    set D := S ρ with hD
    set s := toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) with hs
    set Nc : ℝ := ((univ.filter fun e => bg ρ e ≠ 0).card : ℝ) with hNc
    set S2 : ℝ := ∑ e ∈ D, θ e ^ 2 with hS2
    set T : ℝ := Real.sqrt S2 with hT
    set SW : ℝ := ∑ e ∈ D, toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 with hSW
    have hd1 : (1 : ℝ) ≤ d + 1 := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
    have hd24 : (d + 1) ^ 2 ≤ (d + 1) ^ 4 := pow_le_pow_right₀ hd1 (by norm_num)
    have hX2 : 2 ≤ X := two_le_sum_abs_of_neutral ρ (hne ρ hρ) (hneutral ρ hρ)
    have hX0 : 0 ≤ X := by linarith
    have hX24 : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ (by linarith)
    have hSW0 : 0 ≤ SW := Finset.sum_nonneg fun e _ => sq_nonneg _
    have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun e _ => sq_nonneg _
    have hcardD : (D.card : ℝ) ≤ Kv * (d + 1) ^ 2 := hcard ρ hρ
    -- the phase term through the routing
    obtain ⟨r, hrS, hrX, hroute'⟩ := hroute ρ hρ
    have hsumS : ∑ j, σ j * (ρ j : ℝ) = ∑ e ∈ D, (r e : ℝ) * G.grad σ e := by
      rw [hroute' σ]
      refine (Finset.sum_subset (Finset.subset_univ D) fun e _ he => ?_).symm
      have : r e = 0 := by
        by_contra hne'
        exact he (hrS e hne')
      simp [this]
    have hmod := abs_toIcoMod_sum_le D r (G.grad σ)
    rw [← hsumS] at hmod
    set rr : E → ℝ := fun e => |toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e)| with hrr
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq D (fun e => |(r e : ℝ)|) rr
    have hrsq : ∑ e ∈ D, |(r e : ℝ)| ^ 2 ≤ D.card * X ^ 2 := by
      calc ∑ e ∈ D, |(r e : ℝ)| ^ 2 ≤ ∑ _e ∈ D, X ^ 2 :=
            Finset.sum_le_sum fun e _ => pow_le_pow_left₀ (abs_nonneg _) (hrX e) 2
        _ = D.card * X ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    have hrr2 : ∑ e ∈ D, rr e ^ 2 = SW := Finset.sum_congr rfl fun e _ => sq_abs _
    have hR0 : 0 ≤ ∑ e ∈ D, |(r e : ℝ)| * rr e :=
      Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hY0 : 0 ≤ (d + 1) ^ 4 * X ^ 4 := by positivity
    have hA : s ^ 2 ≤ Kv * ((d + 1) ^ 4 * X ^ 4) * SW := by
      calc s ^ 2 = |s| ^ 2 := (sq_abs _).symm
        _ ≤ (∑ e ∈ D, |(r e : ℝ)| * rr e) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmod 2
        _ ≤ (∑ e ∈ D, |(r e : ℝ)| ^ 2) * ∑ e ∈ D, rr e ^ 2 := hcs
        _ ≤ (D.card * X ^ 2) * SW := by
            rw [hrr2]; exact mul_le_mul_of_nonneg_right hrsq hSW0
        _ ≤ (Kv * (d + 1) ^ 2 * X ^ 2) * SW :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcardD (sq_nonneg _)) hSW0
        _ ≤ (Kv * (d + 1) ^ 4 * X ^ 4) * SW := by
            refine mul_le_mul_of_nonneg_right ?_ hSW0
            exact mul_le_mul (mul_le_mul_of_nonneg_left hd24 hKv) hX24 (sq_nonneg _)
              (mul_nonneg hKv (by positivity))
        _ = Kv * ((d + 1) ^ 4 * X ^ 4) * SW := by ring
    have hfilt : (univ.filter fun e => bg ρ e ≠ 0) ⊆ D := fun e he =>
      hbg ρ hρ e (Finset.mem_filter.mp he).2
    have hNcle : Nc ≤ Kv * (d + 1) ^ 2 :=
      (Nat.cast_le.mpr (card_le_card hfilt)).trans hcardD
    have hNc0 : 0 ≤ Nc := Nat.cast_nonneg _
    have hNc2 : Nc ^ 2 ≤ Kv ^ 2 * (d + 1) ^ 4 := by
      calc Nc ^ 2 ≤ (Kv * (d + 1) ^ 2) ^ 2 := pow_le_pow_left₀ hNc0 hNcle 2
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
  have hmain := sum_abs_mul_le_of_overlap dsc S Kov (8 * (Kv + 2 * Kv ^ 2)) hK₀ 4 4 wt hwt0 P
    N hne hneutral hdsc hP hov z b ε hz hthr
  calc _ = ∑ ρ ∈ N, |z ρ| * P ρ := Finset.sum_congr rfl fun ρ _ => by rw [hPdef]; ring
    _ ≤ ε * ∑ e, wt e := hmain

end FroehlichSpencer.BKT.Generic

end
