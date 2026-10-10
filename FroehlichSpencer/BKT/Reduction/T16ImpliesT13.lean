/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Reduction.T16ImpliesT15
public import FroehlichSpencer.BKT.Lattice2D.C64
public import FroehlichSpencer.BKT.Lattice2D.C64Reflection
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import FroehlichSpencer.BKT.Bridge.FreeLineSource
import FroehlichSpencer.BKT.ExpMoment.BranchBound
import FroehlichSpencer.BKT.ExpMoment.Claim32Mod
import FroehlichSpencer.BKT.ExpMoment.Claim32Threshold
import FroehlichSpencer.BKT.ExpMoment.ReducedPhase
import FroehlichSpencer.BKT.Gaussian.GFFSymmetry
import FroehlichSpencer.BKT.Gaussian.WeightedGFF
import FroehlichSpencer.BKT.Gaussian.WeightedShift
import FroehlichSpencer.BKT.Surface.GFFWellDefined

/-!
# KP Claim 6.3 and Theorem 6.2 from the data of KP Theorem 1.6 (toward T1.6 ⇒ T1.3)

The KP Theorem 1.6 is not
imported; `t16Statement` (from `Reduction/T16ImpliesT15.lean`) is its verbatim statement.

With
The helper statements use the corrected endpoint `L − 1`, weights indexed by
`j ∈ Λ_L^free`, and `y₁ < L − 1`. With
`N = L − y₀`, the line source `f_y` of KP (6.3) is `Lattice2D.squareFreeLineSource L y₀ y₁`.

Two inputs to this reduction are stated here as explicit hypotheses; their exact internal-carrier
proofs are supplied by `Lattice2D/C64Transfer.lean`:
* `c63ReflectedEnergyStatement` — the reflected-energy inequality of  C6.3:
  `∑_{e ∈ E(Λ_L^free)} [2π ∇_e (−Δ)⁻¹ f_y]_{2π}² ≤ (2π)² ⟨∂₁F_y, (−Δ_{2L}^per)⁻¹ ∂₁F_y⟩`,
  proved by `Lattice2D.c63ReflectedEnergyStatement_proof` from KP (6.9), (6.11), (6.12) and
  (6.14).

Its right side is bounded by `656 log(N+1)` in the `torusC64_reflectedPotential_backward1_energy_log_upper_bound` (KP (6.15)).
* `c64Statement D₅` — KP Claim 6.4, `⟨f_y, (−Δ)⁻¹ f_y⟩ ≥ N − D₅ log(N+1)`; the exact
  `D₅ = 656` statement is proved by `Lattice2D.c64Statement_656_proof` (with the stronger
  constant `164` available in `squareFreeLineSource_energy_lower_bound`).

* `claim63`: KP Claim 6.3 on the free box; `exists_claim63` is its quantified form.
* `villainLineBound_of_t16Data`: KP Theorem 6.2 at one box, root, temperature and weight family,
  from the T1.6 data (: modular Claim 3.1, `|z| < 1/8`, C6.3 with `D = D₄ = 2`, positive
  averaging, and C6.4).
* `t62_of_t16Statement`: KP Theorem 6.2 (corrected) from `t16Statement`, with the explicit
  absolute constant `c = 1 + 2π² D₅`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Reduction

open MeasureTheory

/--
Proved by `Lattice2D.c63ReflectedEnergyStatement_proof` in `Lattice2D/C64Transfer.lean`.
-/
def c63ReflectedEnergyStatement : Prop :=
  ∀ (L y₀ y₁ : ℕ) [NeZero (2 * L)] (hside : 2 < 2 * L)
    (hT : (Lattice2D.torusGraph (2 * L) hside).Connected)
    (hF : (Lattice2D.squareFreeGraph L).Connected), 1 < L → y₀ < L → y₁ + 1 < L →
    ∑ e, toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi *
        (Lattice2D.squareFreeGraph L).grad
          ((Lattice2D.squareFreeGraph L).greenOp hF (Lattice2D.squareFreeLineSource L y₀ y₁))
          e) ^ 2 ≤
      (2 * Real.pi) ^ 2 * Lattice2D.greenBilinear (Lattice2D.torusGraph (2 * L) hside) hT
        (Lattice2D.torusC64Backward1 (Lattice2D.torusC64ReflectedPotential L y₀ y₁))
        (Lattice2D.torusC64Backward1 (Lattice2D.torusC64ReflectedPotential L y₀ y₁))

/--
The `D₅ = 656` instance is
proved in `Lattice2D.c64Statement_656_proof`.
-/
def c64Statement (D₅ : ℝ) : Prop :=
  ∀ (L y₀ y₁ : ℕ) (hF : (Lattice2D.squareFreeGraph L).Connected), 1 < L → y₀ < L →
    y₁ + 1 < L →
    ((L - y₀ : ℕ) : ℝ) - D₅ * Real.log ((L - y₀ + 1 : ℕ) : ℝ) ≤
      Lattice2D.greenBilinear (Lattice2D.squareFreeGraph L) hF
        (Lattice2D.squareFreeLineSource L y₀ y₁) (Lattice2D.squareFreeLineSource L y₀ y₁)

/-- The constant `(2π)² · 656` of the reduced-energy bound for `σ^Vil` in KP Claim 6.3. -/
def claim63Const : ℝ := (2 * Real.pi) ^ 2 * 656

theorem claim63Const_pos : 0 < claim63Const := by
  unfold claim63Const
  have := Real.pi_pos
  positivity

/--
The reduced energy of `σ^Vil = 2π (−Δ)⁻¹ f_y` on the free box is at most
`(2π)² · 656 · log(N + 1)` (KP p. 38, with the `(2π)²` of  C6.3).
-/
theorem sum_sq_toIcoMod_grad_le (hrefl : c63ReflectedEnergyStatement) (L : ℕ) (hL : 1 < L)
    (y₀ y₁ : ℕ) (hy₀ : y₀ < L) (hy₁ : y₁ + 1 < L) (σ : Fin L × Fin L → ℝ)
    (hσ : ∀ e, (squareFree L).grad σ e = 2 * Real.pi * (squareFree L).grad
      ((squareFree L).greenOp (squareFree_connected L hL)
        (Lattice2D.squareFreeLineSource L y₀ y₁)) e) :
    ∑ e, toIcoMod Real.two_pi_pos (-Real.pi) ((squareFree L).grad σ e) ^ 2 ≤
      claim63Const * Real.log ((L - y₀ + 1 : ℕ) : ℝ) := by
  have : NeZero (2 * L) := ⟨by omega⟩
  have hside : 2 < 2 * L := by omega
  have hT := Lattice2D.torusGraph_connected (2 * L) hside
  have hF := Lattice2D.squareFreeGraph_connected (L := L) (by omega)
  have heven : ∀ t : ℝ, toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * -t) ^ 2 =
      toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * t) ^ 2 := fun t => by
    rw [show 2 * Real.pi * -t = -(2 * Real.pi * t) by ring, sq_toIcoMod_neg]
  have h2 := squareFree_sum_comp_grad_greenOp_of_even hL hF
    (fun t => toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * t) ^ 2) heven
    (Lattice2D.squareFreeLineSource L y₀ y₁)
  have hpi : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  calc ∑ e, toIcoMod Real.two_pi_pos (-Real.pi) ((squareFree L).grad σ e) ^ 2
      = ∑ e, toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * (squareFree L).grad
          ((squareFree L).greenOp (squareFree_connected L hL)
            (Lattice2D.squareFreeLineSource L y₀ y₁)) e) ^ 2 :=
        Finset.sum_congr rfl fun e _ => by rw [hσ e]
    _ = ∑ e, toIcoMod Real.two_pi_pos (-Real.pi) (2 * Real.pi *
          (Lattice2D.squareFreeGraph L).grad ((Lattice2D.squareFreeGraph L).greenOp hF
            (Lattice2D.squareFreeLineSource L y₀ y₁)) e) ^ 2 := h2
    _ ≤ (2 * Real.pi) ^ 2 * Lattice2D.greenBilinear (Lattice2D.torusGraph (2 * L) hside) hT
          (Lattice2D.torusC64Backward1 (Lattice2D.torusC64ReflectedPotential L y₀ y₁))
          (Lattice2D.torusC64Backward1 (Lattice2D.torusC64ReflectedPotential L y₀ y₁)) :=
        hrefl L y₀ y₁ hside hT hF hL hy₀ hy₁
    _ ≤ (2 * Real.pi) ^ 2 * (656 * Real.log ((L - y₀ + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Lattice2D.torusC64_reflectedPotential_backward1_energy_log_upper_bound L y₀ y₁ hside hT
            hy₀) hpi
    _ = claim63Const * Real.log ((L - y₀ + 1 : ℕ) : ℝ) := by unfold claim63Const; ring

/--
**KP Claim 6.3** (KP (6.7)) on the free box, for one ensemble with the T1.6
properties (1)–(3) and `β` below the explicit threshold for `D · claim63Const`:
`∑_{ϱ ∈ 𝒩} |z(ϱ)| [⟨σ^Vil, ϱ⟩]_{2π}² ≤ (β / D) log(N + 1)`.

Here `σ^Vil` is any field whose
gradient is `2π ∇ (−Δ)⁻¹ f_y`, i.e. a solution of `Δ σ = 2π f_y` up to the sign convention of
`greenOp` (KP p. 35).
-/
theorem claim63 (hrefl : c63ReflectedEnergyStatement) (L : ℕ) (hL : 1 < L) (y₀ y₁ : ℕ)
    (hy₀ : y₀ < L) (hy₁ : y₁ + 1 < L) (N : Finset (Fin L × Fin L → ℤ))
    (hne : ∀ ρ ∈ N, ρ ≠ 0) (hneutral : ∀ ρ ∈ N, ∑ j, ρ j = 0)
    (hdisj : ∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
      (squareFree L).densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      (squareFree L).densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      ∀ j₁ j₂ : Fin L × Fin L, (squareFree L).IsDensityCenter ϱ₁ j₁ →
        (squareFree L).IsDensityCenter ϱ₂ j₂ →
        (squareFree L).densityDomain ϱ₁ j₁ ∩ (squareFree L).densityDomain ϱ₂ j₂ = ∅)
    (z : (Fin L × Fin L → ℤ) → ℝ) (c₁ β D : ℝ) (hβ : 0 < β) (hD : 0 < D)
    (hz : ∀ ρ ∈ N, |z ρ| ≤ Real.exp (-(c₁ / β) *
      (∑ j, (ρ j : ℝ) ^ 2 + Real.logb 2 ((squareFree L).densityDiameter ρ + 1))))
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      144 * (D * claim63Const) * (d + 1) ^ 3 * u ^ 2 *
        Real.exp (-(c₁ / β) * (u + Real.logb 2 (d + 1))) ≤ β)
    (σ : Fin L × Fin L → ℝ)
    (hσ : ∀ e, (squareFree L).grad σ e = 2 * Real.pi * (squareFree L).grad
      ((squareFree L).greenOp (squareFree_connected L hL)
        (Lattice2D.squareFreeLineSource L y₀ y₁)) e) :
    ∑ ρ ∈ N, |z ρ| * toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) ^ 2 ≤
      β / D * Real.log ((L - y₀ + 1 : ℕ) : ℝ) := by
  have hC := claim63Const_pos
  have hcl := claim32_mod (squareFree L) (squareFree_connected L hL) 144 (by norm_num)
    (card_edgesWithin_densityDomain_squareFree_le L) N hne hneutral hdisj z c₁ β
    (D * claim63Const) hβ (by positivity) hz hthr σ
  have hE := sum_sq_toIcoMod_grad_le hrefl L hL y₀ y₁ hy₀ hy₁ σ hσ
  calc _ ≤ β / (D * claim63Const) *
        ∑ e, toIcoMod Real.two_pi_pos (-Real.pi) ((squareFree L).grad σ e) ^ 2 := hcl
    _ ≤ β / (D * claim63Const) * (claim63Const * Real.log ((L - y₀ + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = β / D * Real.log ((L - y₀ + 1 : ℕ) : ℝ) := by
        field_simp

/-- **KP Claim 6.3** in its quantified form: for `D > 0` and the T1.6 damping constant `c₁ > 0`
there is `β₁ > 0` such that (6.7) holds for every `β < β₁`, every free box, line and ensemble
with the T1.6 properties (1)–(3). -/
theorem exists_claim63 (hrefl : c63ReflectedEnergyStatement) (c₁ D : ℝ) (hc₁ : 0 < c₁)
    (hD : 0 < D) :
    ∃ β₁ : ℝ, 0 < β₁ ∧ ∀ β : ℝ, 0 < β → β < β₁ →
      ∀ (L : ℕ) (hL : 1 < L) (y₀ y₁ : ℕ), y₀ < L → y₁ + 1 < L →
      ∀ (N : Finset (Fin L × Fin L → ℤ)), (∀ ρ ∈ N, ρ ≠ 0) → (∀ ρ ∈ N, ∑ j, ρ j = 0) →
      (∀ ϱ₁ ∈ N, ∀ ϱ₂ ∈ N, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
        (squareFree L).densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
        (squareFree L).densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
        ∀ j₁ j₂ : Fin L × Fin L, (squareFree L).IsDensityCenter ϱ₁ j₁ →
          (squareFree L).IsDensityCenter ϱ₂ j₂ →
          (squareFree L).densityDomain ϱ₁ j₁ ∩ (squareFree L).densityDomain ϱ₂ j₂ = ∅) →
      ∀ z : (Fin L × Fin L → ℤ) → ℝ, (∀ ρ ∈ N, |z ρ| ≤ Real.exp (-(c₁ / β) *
        (∑ j, (ρ j : ℝ) ^ 2 + Real.logb 2 ((squareFree L).densityDiameter ρ + 1)))) →
      ∀ σ : Fin L × Fin L → ℝ, (∀ e, (squareFree L).grad σ e = 2 * Real.pi *
        (squareFree L).grad ((squareFree L).greenOp (squareFree_connected L hL)
          (Lattice2D.squareFreeLineSource L y₀ y₁)) e) →
      ∑ ρ ∈ N, |z ρ| * toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ρ j : ℝ)) ^ 2 ≤
        β / D * Real.log ((L - y₀ + 1 : ℕ) : ℝ) := by
  have hC := claim63Const_pos
  obtain ⟨β₁, hβ₁, hthr⟩ := exists_claim32_threshold (144 * (D * claim63Const)) c₁
    (by positivity) hc₁
  exact ⟨β₁, hβ₁, fun β hβ hβ₁' L hL y₀ y₁ hy₀ hy₁ N hne hneutral hdisj z hz σ hσ =>
    claim63 hrefl L hL y₀ y₁ hy₀ hy₁ N hne hneutral hdisj z c₁ β D hβ hD hz
      (hthr β hβ hβ₁') σ hσ⟩

/-- The corrected KP (6.2) observable is `exp(⟨φ, −2πβ f_y⟩) · exp(−2π² β N)` (KP p. 35). -/
theorem lineObservable_eq (L y₀ y₁ : ℕ) (hy₁ : y₁ + 1 < L) (β : ℝ) (φ : Fin L × Fin L → ℝ) :
    Real.exp (-2 * Real.pi * β * ∑ t : Fin L with y₀ ≤ t.val,
        (φ (t, ⟨y₁, by omega⟩) - φ (t, ⟨y₁ + 1, hy₁⟩) + 2 * Real.pi / 2)) =
      Real.exp (∑ j, φ j * (-(2 * Real.pi * β) * Lattice2D.squareFreeLineSource L y₀ y₁ j)) *
        Real.exp (-(2 * Real.pi ^ 2 * β * ((L - y₀ : ℕ) : ℝ))) := by
  rw [← Real.exp_add]
  congr 1
  have h1 := sum_mul_squareFreeLineSource y₀ y₁ hy₁ φ
  have h2 : ∑ j, φ j * (-(2 * Real.pi * β) * Lattice2D.squareFreeLineSource L y₀ y₁ j) =
      -(2 * Real.pi * β) * ∑ j, φ j * Lattice2D.squareFreeLineSource L y₀ y₁ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, h1, Finset.sum_add_distrib, Finset.sum_const, card_filter_le_val, nsmul_eq_mul]
  ring

/-- **KP Theorem 6.2** (corrected) at one free box, root, temperature and weight family, from
the Theorem 1.6 data: with `N = L − y₀`,
`𝔼_{β,Λ_L^free,λ,v}[exp(−2πβ ∑_{t=y₀}^{L−1} (φ_{(t,y₁)} − φ_{(t,y₁+1)} + 2π/2))] ≥
(N + 1)^{−(1 + 2π² D₅) β}`. The thresholds are `β < c₁ / ln 8` and the Claim 6.3 threshold for
`D = D₄ = 2`. -/
theorem villainLineBound_of_t16Data (hrefl : c63ReflectedEnergyStatement) (D₅ : ℝ)
    (hc64 : c64Statement D₅) (L : ℕ) (hL : 1 < L) (y₀ y₁ : ℕ) (hy₀ : y₀ < L)
    (hy₁ : y₁ + 1 < L) (c₁ β : ℝ) (hβ : 0 < β) (hβ8 : β < c₁ / Real.log 8)
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      144 * (2 * claim63Const) * (d + 1) ^ 3 * u ^ 2 *
        Real.exp (-(c₁ / β) * (u + Real.logb 2 (d + 1))) ≤ β)
    (v : Fin L × Fin L) (lam : Fin L × Fin L → ℝ → ℝ) (Γ η θ : ℝ)
    (hlam : ∀ j, IsSubGaussian Γ η θ β (lam j))
    (hdata : ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ)) (c : Fin n → ℝ)
        (z : Fin n → (Fin L × Fin L → ℤ) → ℝ)
        (ϱbar : Fin n → (Fin L × Fin L → ℤ) → Fin L × Fin L → ℝ),
        (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
        (∀ σ : Fin L × Fin L → ℝ,
          ∫ φ, ∏ j, lam j (φ j + σ j) ∂(gffLaw (squareFree L) (squareFree_connected L hL) β hβ v) =
            ∑ i, c i * ∫ φ, ∏ ϱ ∈ N i,
              (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j + ∑ j, σ j * ϱ j))
                ∂(gffLaw (squareFree L) (squareFree_connected L hL) β hβ v)) ∧
        ∀ i,
          (∀ ϱ ∈ N i, ∑ j, ϱ j = 0) ∧
          (∀ ϱ ∈ N i, |z i ϱ| ≤ Real.exp (-(c₁ / β) *
            (∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 ((squareFree L).densityDiameter ϱ + 1)))) ∧
          ∀ ϱ₁ ∈ N i, ∀ ϱ₂ ∈ N i, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
            (squareFree L).densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
            (squareFree L).densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
            ∀ j₁ j₂ : Fin L × Fin L, (squareFree L).IsDensityCenter ϱ₁ j₁ →
              (squareFree L).IsDensityCenter ϱ₂ j₂ →
              (squareFree L).densityDomain ϱ₁ j₁ ∩ (squareFree L).densityDomain ϱ₂ j₂ = ∅) :
    ((L - y₀ + 1 : ℕ) : ℝ) ^ (-((1 + 2 * Real.pi ^ 2 * D₅) * β)) ≤
      (∫ φ, Real.exp (-2 * Real.pi * β * ∑ t : Fin L with y₀ ≤ t.val,
          (φ (t, ⟨y₁, by omega⟩) - φ (t, ⟨y₁ + 1, hy₁⟩) + 2 * Real.pi / 2)) *
          ∏ j, lam j (φ j) ∂(gffLaw (squareFree L) (squareFree_connected L hL) β hβ v)) /
        ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw (squareFree L) (squareFree_connected L hL) β hβ v) := by
  obtain ⟨n, N, c, z, ϱbar, hens, hcpos, hcsum, hid, hprops⟩ := hdata
  set Λ := squareFree L with hΛdef
  set hΛ := squareFree_connected L hL
  set μ := gffLaw Λ hΛ β hβ v with hμ
  have := isProbabilityMeasure_gffLaw Λ hΛ β hβ v
  -- Branch integrals and the normalizer (as in KP §3).
  set Zb : Fin n → (Fin L × Fin L → ℝ) → ℝ := fun i σ =>
    ∫ φ, ∏ ϱ ∈ N i, (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j + ∑ j, σ j * ϱ j)) ∂μ
    with hZb
  have hz8 : ∀ i, ∀ ϱ ∈ N i, |z i ϱ| < 1 / 8 := fun i ϱ hϱ =>
    abs_lt_eighth_of_damping Λ c₁ β hβ hβ8 ϱ ((hens i).1 ϱ hϱ) ((hprops i).1 ϱ hϱ) (z i ϱ)
      ((hprops i).2.1 ϱ hϱ)
  have hZb0 : ∀ i, Zb i 0 = ∫ φ, ∏ ϱ ∈ N i,
      (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j)) ∂μ := by
    intro i
    simp only [hZb, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  have hZb0pos : ∀ i, 0 < Zb i 0 := by
    intro i
    have h := integral_prod_one_add_cos_ge μ (N i) (ϱbar i) (fun _ => 0) (z i) (hz8 i)
    simp only [add_zero] at h
    rw [hZb0 i]
    exact lt_of_lt_of_le (pow_pos (by norm_num) _) h
  have hZ0eq : ∫ φ, ∏ j, lam j (φ j) ∂μ = ∑ i, c i * Zb i 0 := by
    have h := hid 0
    simp only [Pi.zero_apply, add_zero] at h
    exact h
  have hnpos : 0 < n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    simp at hcsum
  have hZ0pos : 0 < ∫ φ, ∏ j, lam j (φ j) ∂μ := by
    rw [hZ0eq]
    have : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hnpos⟩, Finset.mem_univ _⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hcpos i) (hZb0pos i)) this
  -- The line source and the shift `σ^Vil` (KP (6.3), (6.4)).
  set fy := Lattice2D.squareFreeLineSource L y₀ y₁ with hfy
  set f : Fin L × Fin L → ℝ := fun j => -(2 * Real.pi * β) * fy j with hf
  have hfy0 : ∑ j, fy j = 0 := sum_squareFreeLineSource y₀ y₁ hy₁
  have hf0 : ∑ j, f j = 0 := by
    simp only [hf]
    rw [← Finset.mul_sum, hfy0, mul_zero]
  have hgf : Λ.greenOp hΛ f = (-(2 * Real.pi * β)) • Λ.greenOp hΛ fy := by
    have : f = (-(2 * Real.pi * β)) • fy := by
      funext j
      simp [hf, smul_eq_mul]
    rw [this, map_smul]
  set σ := gffShift Λ hΛ β f v with hσ
  have hσgrad : ∀ e, Λ.grad σ e = 2 * Real.pi * Λ.grad (Λ.greenOp hΛ fy) e := by
    intro e
    simp only [Multigraph.grad, hσ, gffShift, hgf, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  -- Claim 6.4 transported to the box.
  set Qy := Multigraph.pairing fy (-(Λ.greenOp hΛ fy)) with hQy
  have hQyge : ((L - y₀ : ℕ) : ℝ) - D₅ * Real.log ((L - y₀ + 1 : ℕ) : ℝ) ≤ Qy := by
    have hF := Lattice2D.squareFreeGraph_connected (L := L) (by omega)
    rw [hQy, squareFree_pairing_neg_greenOp_eq_greenBilinear hL hF fy]
    exact hc64 L y₀ y₁ hF hL hy₀ hy₁
  have hQf : Multigraph.pairing f (-Λ.greenOp hΛ f) = (2 * Real.pi * β) ^ 2 * Qy := by
    rw [hgf, hQy]
    simp only [Multigraph.pairing, hf, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- Completing the square.
  obtain ⟨C, hC⟩ := exists_abs_prod_le_of_isSubGaussian hlam
  have hnum := integral_exp_pairing_mul_gffLaw Λ hΛ β hβ v f hf0 (fun φ => ∏ j, lam j (φ j))
    (continuous_prod_of_isSubGaussian hlam).measurable C hC
  have hnum' : ∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂μ =
      Real.exp (Multigraph.pairing f (-Λ.greenOp hΛ f) / (2 * β)) *
        ∫ φ, ∏ j, lam j ((φ + σ) j) ∂μ := hnum
  have hshift : ∫ φ, ∏ j, lam j ((φ + σ) j) ∂μ = ∑ i, c i * Zb i σ := by
    have h := hid σ
    simp only [Pi.add_apply]
    exact h
  -- Each branch: modular Claim 3.1 and Claim 6.3 with `D = 2`.
  set ℓ := Real.log ((L - y₀ + 1 : ℕ) : ℝ) with hℓ
  set e₀ := Real.exp (-(β * ℓ)) with he₀
  have hbranch : ∀ i, e₀ * Zb i 0 ≤ Zb i σ := by
    intro i
    have hcl := claim63 hrefl L hL y₀ y₁ hy₀ hy₁ (N i) (hens i).1 (hprops i).1 (hprops i).2.2
      (z i) c₁ β 2 hβ (by norm_num) (hprops i).2.1 hthr σ hσgrad
    have hb := integral_prod_cos_shift_ge_mod μ (gffLaw_map_neg Λ hΛ β hβ v) (N i) (ϱbar i)
      (fun ϱ => ∑ j, σ j * (ϱ j : ℝ)) (z i) (hz8 i)
    rw [← hZb0 i] at hb
    have hexp : e₀ ≤ Real.exp (-∑ ϱ ∈ N i, 2 * |z i ϱ| *
        toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ϱ j : ℝ)) ^ 2) := by
      rw [he₀]
      apply Real.exp_le_exp.mpr
      have hsum : ∑ ϱ ∈ N i, 2 * |z i ϱ| *
          toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ϱ j : ℝ)) ^ 2 =
          2 * ∑ ϱ ∈ N i, |z i ϱ| *
            toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ϱ j : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ϱ _ => by ring
      rw [hsum]
      have : 2 * (β / 2 * ℓ) = β * ℓ := by ring
      linarith only [hcl]
    calc e₀ * Zb i 0 ≤ Real.exp (-∑ ϱ ∈ N i, 2 * |z i ϱ| *
          toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ϱ j : ℝ)) ^ 2) * Zb i 0 :=
          mul_le_mul_of_nonneg_right hexp (hZb0pos i).le
      _ ≤ Zb i σ := hb
  -- Positive averaging.
  have hZσ : e₀ * ∫ φ, ∏ j, lam j (φ j) ∂μ ≤ ∫ φ, ∏ j, lam j ((φ + σ) j) ∂μ := by
    rw [hZ0eq, hshift, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have := hbranch i
      have hc := (hcpos i).le
      nlinarith only [this, hc]
  -- The observable.
  set Nr : ℝ := ((L - y₀ : ℕ) : ℝ) with hNr
  have hobs : ∫ φ, Real.exp (-2 * Real.pi * β * ∑ t : Fin L with y₀ ≤ t.val,
        (φ (t, ⟨y₁, by omega⟩) - φ (t, ⟨y₁ + 1, hy₁⟩) + 2 * Real.pi / 2)) *
        ∏ j, lam j (φ j) ∂μ =
      Real.exp (-(2 * Real.pi ^ 2 * β * Nr)) *
        ∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    simp only
    rw [lineObservable_eq L y₀ y₁ hy₁ β φ]
    ring
  rw [hobs, hnum', hQf, le_div_iff₀ hZ0pos]
  have hbase : ((L - y₀ + 1 : ℕ) : ℝ) ^ (-((1 + 2 * Real.pi ^ 2 * D₅) * β)) =
      Real.exp (-(2 * Real.pi ^ 2 * β * Nr)) *
        (Real.exp (2 * Real.pi ^ 2 * β * (Nr - D₅ * ℓ)) * e₀) := by
    rw [Real.rpow_def_of_pos (by positivity), he₀, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hQexp : 2 * Real.pi ^ 2 * β * (Nr - D₅ * ℓ) ≤ (2 * Real.pi * β) ^ 2 * Qy / (2 * β) := by
    have hk : (2 * Real.pi * β) ^ 2 * Qy / (2 * β) = 2 * Real.pi ^ 2 * β * Qy := by
      field_simp
    rw [hk]
    have : 0 ≤ 2 * Real.pi ^ 2 * β := by positivity
    exact mul_le_mul_of_nonneg_left hQyge this
  rw [hbase]
  have hA := (Real.exp_pos (-(2 * Real.pi ^ 2 * β * Nr))).le
  calc Real.exp (-(2 * Real.pi ^ 2 * β * Nr)) *
        (Real.exp (2 * Real.pi ^ 2 * β * (Nr - D₅ * ℓ)) * e₀) * ∫ φ, ∏ j, lam j (φ j) ∂μ
      = Real.exp (-(2 * Real.pi ^ 2 * β * Nr)) *
          (Real.exp (2 * Real.pi ^ 2 * β * (Nr - D₅ * ℓ)) *
            (e₀ * ∫ φ, ∏ j, lam j (φ j) ∂μ)) := by ring
    _ ≤ Real.exp (-(2 * Real.pi ^ 2 * β * Nr)) *
          (Real.exp ((2 * Real.pi * β) ^ 2 * Qy / (2 * β)) *
            ∫ φ, ∏ j, lam j ((φ + σ) j) ∂μ) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul (Real.exp_le_exp.mpr hQexp) hZσ
          (mul_pos (Real.exp_pos _) hZ0pos).le (Real.exp_pos _).le) hA

/--
The constant `c = 1 + 2π² D₅` is explicit
and absolute; `β₀ = min(β₀^{1.6}, c₁ / ln 8, β₂)` depends on `(Γ, η, θ)` only, where `β₂` is the
Claim 6.3 threshold for `D = D₄ = 2`.
-/
theorem t62_of_t16Statement (h : t16Statement) (hrefl : c63ReflectedEnergyStatement) (D₅ : ℝ)
    (hc64 : c64Statement D₅) :
    ∀ Γ : ℝ, 0 < Γ → ∀ η θ : ℝ, 0 ≤ θ → θ < 1 / 16 → ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ (L : ℕ) (hL : 1 < L) (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
        ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
        ∀ y₀ y₁ : ℕ, y₀ < L → ∀ hy₁ : y₁ + 1 < L,
          ((L - y₀ + 1 : ℕ) : ℝ) ^ (-((1 + 2 * Real.pi ^ 2 * D₅) * β)) ≤
            (∫ φ, Real.exp (-2 * Real.pi * β * ∑ t : Fin L with y₀ ≤ t.val,
                (φ (t, ⟨y₁, by omega⟩) - φ (t, ⟨y₁ + 1, hy₁⟩) + 2 * Real.pi / 2)) *
                ∏ j, lam j (φ j) ∂(gffLaw (squareFree L) (squareFree_connected L hL) β hβ v)) /
              ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw (squareFree L) (squareFree_connected L hL) β hβ v) := by
  intro Γ hΓ η θ hθ0 hθ
  obtain ⟨β₀', c₁, hβ₀', hc₁, h16⟩ := h Γ hΓ η θ hθ0 hθ
  have hC := claim63Const_pos
  obtain ⟨β₂, hβ₂, hthr⟩ := exists_claim32_threshold (144 * (2 * claim63Const)) c₁
    (by positivity) hc₁
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  refine ⟨min β₀' (min (c₁ / Real.log 8) β₂),
    lt_min hβ₀' (lt_min (div_pos hc₁ hlog8) hβ₂),
    fun L hL v β hβ hβlt lam hlam y₀ y₁ hy₀ hy₁ => ?_⟩
  have hstep := h16 L hL
  dsimp only at hstep
  have h1 : β < β₀' := lt_of_lt_of_le hβlt (min_le_left _ _)
  have h2 : β < c₁ / Real.log 8 :=
    lt_of_lt_of_le hβlt ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : β < β₂ := lt_of_lt_of_le hβlt ((min_le_right _ _).trans (min_le_right _ _))
  exact villainLineBound_of_t16Data hrefl D₅ hc64 L hL y₀ y₁ hy₀ hy₁ c₁ β hβ h2
    (hthr β hβ h3) v lam Γ η θ hlam (hstep.1 v β hβ h1 lam hlam)

/--
The expectation is the ratio of `gffLaw` integrals, as in KP (1.10).
-/
def t62Statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ Γ : ℝ, 0 < Γ → ∀ η θ : ℝ, 0 ≤ θ → θ < 1 / 16 → ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ (L : ℕ) (hL : 1 < L) (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
      ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
      ∀ y₀ y₁ : ℕ, y₀ < L → ∀ hy₁ : y₁ + 1 < L,
        ((L - y₀ + 1 : ℕ) : ℝ) ^ (-(c * β)) ≤
          (∫ φ, Real.exp (-2 * Real.pi * β * ∑ t : Fin L with y₀ ≤ t.val,
              (φ (t, ⟨y₁, by omega⟩) - φ (t, ⟨y₁ + 1, hy₁⟩) + 2 * Real.pi / 2)) *
              ∏ j, lam j (φ j) ∂(gffLaw (squareFree L) (squareFree_connected L hL) β hβ v)) /
            ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw (squareFree L) (squareFree_connected L hL) β hβ v)


theorem t62Statement_of_t16Statement (h : t16Statement) (hrefl : c63ReflectedEnergyStatement)
    (D₅ : ℝ) (hD₅ : 0 ≤ D₅) (hc64 : c64Statement D₅) : t62Statement :=
  ⟨1 + 2 * Real.pi ^ 2 * D₅, by positivity, t62_of_t16Statement h hrefl D₅ hc64⟩

end FroehlichSpencer.BKT.Reduction

end
