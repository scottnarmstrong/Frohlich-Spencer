/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.MarkedDomainSubGaussian
public import FroehlichSpencer.BKT.Coulomb.TheoremB
import Mathlib.Tactic

/-!
# FS81 Theorem B on the square domains for sub-Gaussian weights

FS81 p. 572: "the proofs of
Theorems A and B ... for the general Coulomb gases considered here are completely analogous to
the case of the hard core gas".

* `MarkedSquareBoundSubGaussianInternal`: the marked bound on one square domain.

The Villain disorder estimate (`VillainDisorder/TheoremD`) uses it with `Γ = 1` for the Fejér
weights.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory FroehlichSpencer.BKT.Generic.Marked Reduction

section SubGaussian

/-- **FS81 Theorem B on one square domain for `(Γ, 0, 0)`-sub-Gaussian weights** (CG.s21) with
constant `cB` and threshold `β₁`: for site weights `λ_j` that are `(Γ, 0, 0)`-sub-Gaussian at
inverse temperature `β` (KP Definition 1.4), the dipole mark at `o ≠ x` and
`η ≤ min(ξ, 1 − ξ)`, the normalizer is positive and
`|∫ cos(ξ(φ_o − φ_x)) ∏ λ_j(φ_j) dμ| ≤ 2 e^{-(cB η²/β) log₂(|o − x| + 1)} 𝒵`. -/
def MarkedSquareBoundSubGaussianInternal (boundary : SquareBoundary) {L : ℕ} {E : Type}
    [Fintype E] (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (cB Γ η β₁ : ℝ) : Prop :=
  ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₁ → ∀ lam : Fin L × Fin L → ℝ → ℝ,
    (∀ j, IsSubGaussian Γ 0 0 β (lam j)) → ∀ o x : Fin L × Fin L, o ≠ x → ∀ ξ : ℝ, 0 < ξ →
      ξ < 1 → η ≤ dipoleGap ξ →
      0 < ∫ φ, ∏ j, lam j (φ j) ∂gffLaw Λ hΛ β hβ v ∧
      |∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, lam j (φ j) ∂gffLaw Λ hΛ β hβ v| ≤
        2 * Real.exp (-(cB * η ^ 2 / β) * Real.logb 2 (latticeDistance boundary L o x + 1)) *
          ∫ φ, ∏ j, lam j (φ j) ∂gffLaw Λ hΛ β hβ v

/-- **FS81 Theorem B on the square domains for `(Γ, 0, 0)`-sub-Gaussian weights** (CG.s21;
FS81 p. 572: "the proofs of Theorems A and B ... for the general Coulomb gases ... are completely
analogous"). The constant is the same `cB = 1/(16384 max(D₁, 1))`; the threshold `β₁(Γ, η)` is
of order `η²`. This covers the Fejér weights of the Villain gas (`Γ = 1`). -/
theorem markedSquareBoundSubGaussian_exists :
    ∃ cB : ℝ, 0 < cB ∧ ∀ Γ : ℝ, ∀ η : ℝ, 0 < η → ∃ β₁ : ℝ, 0 < β₁ ∧
      ∀ L : ℕ, ∀ hL : 1 < L,
        MarkedSquareBoundSubGaussianInternal .free (squareFree L) (squareFree_connected L hL)
          cB Γ η β₁ ∧
        (Even L → MarkedSquareBoundSubGaussianInternal .periodic (squarePeriodic L)
          (squarePeriodic_connected L hL) cB Γ η β₁) := by
  obtain ⟨D₂, hD₂, h22⟩ := t22Statement_of_repairedBasicLemma
  obtain ⟨D₃, hD₃, h24⟩ := p24_of_l46 SpinWaves.BoundaryShellPacking.l46Statement_holds
  obtain ⟨D₁, hD₁, h21⟩ := kp_p21Statement
  obtain ⟨D₁', hD₁'⟩ : ∃ D₁' : ℝ, D₁' = max D₁ 1 := ⟨_, rfl⟩
  have hD₁'1 : 1 ≤ D₁' := hD₁' ▸ le_max_right _ _
  have hmono : ∀ {boundary : SquareBoundary} {L : ℕ}, P21Step boundary L D₁ →
      P21Step boundary L D₁' := by
    intro boundary L h cover ϱ hϱ
    obtain ⟨h1, h2⟩ := h cover ϱ hϱ
    refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (hD₁' ▸ le_max_left _ _) ?_)⟩
    positivity
  refine ⟨1 / (16384 * D₁'), by positivity, fun Γ η hη => ?_⟩
  obtain ⟨β₀, c₁, hβ₀, hc₁, hdamp⟩ := exists_damping_constants Γ 0 0 D₁' D₂ D₃
    (by norm_num) (by linarith) hD₂ hD₃
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = Real.log (max 1 Γ) + 1 + 0 := ⟨_, rfl⟩
  have hh0 : 0 ≤ h := by
    rw [hh]
    have := Real.log_nonneg (le_max_left 1 Γ)
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min c₁ (η ^ 2 / (2 * 289 * 16384 * D₁')) := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact lt_min hc₁ (by positivity)
  have hcc₁ : c ≤ c₁ := hc ▸ min_le_left _ _
  have hcη : c ≤ η ^ 2 / (2 * 289 * 16384 * D₁') := hc ▸ min_le_right _ _
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁ : ℝ, β₁ = min β₀ (min (η ^ 2 / (64 * (h + 1)))
      (min (η ^ 2 / (2 * 16384 * 289 * D₁' * max D₂ 1)) (c / 20))) := ⟨_, rfl⟩
  have hmaxD₂ : 0 < max D₂ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hβ₁pos : 0 < β₁ := by
    rw [hβ₁]
    exact lt_min hβ₀ (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hH : ∀ β : ℝ, 0 < β → β < β₁ → β < β₀ ∧
      β * (Real.log (max 1 Γ) + 1 + 0 + 1) + c ≤ η ^ 2 / 32 ∧
      4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤ η ^ 2 / (64 * β) ∧
      289 * D₂ * β + 289 * c ≤ η ^ 2 / (16384 * D₁') ∧
      Real.exp (-(c / β)) ≤ 1 / 32 := by
    intro β hβ hββ₁
    rw [hβ₁] at hββ₁
    have k0 := hββ₁.trans_le (min_le_left _ _)
    have k1 := hββ₁.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have k2 := hββ₁.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
    have k3 := hββ₁.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
    obtain ⟨H1, H2, H3, H4⟩ := markedThresholds hD₁'1 hh0 hη hcpos hcη hβ k1 k2 k3
    rw [hh] at H1
    exact ⟨k0, H1, H2, H3, H4⟩
  have hexpo : ∀ β : ℝ, η ^ 2 / (16384 * D₁' * β) = 1 / (16384 * D₁') * η ^ 2 / β := by
    intro β
    rw [div_mul_eq_mul_div, one_mul, div_div]
  refine ⟨β₁, hβ₁pos, fun L hL => ⟨?_, fun hE => ?_⟩⟩
  · intro v β hβ hββ₁ lam hlam o x hox ξ hξ0 hξ1 hηξ
    obtain ⟨hββ₀, H1, H2, H3, H4⟩ := hH β hβ hββ₁
    have hb := markedDomain_bound_subGaussian hL (squareFree L) (squareFree_connected L hL)
      (fun _ _ => rfl)
      (SpinWaves.squareFreeBipartiteDegreeFour L hL)
      (SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).1 hD₁'1 hD₂.le (h22 L hL).1
      (hmono (h21 L hL).1) (h24 L hL).1 hdamp hη hcpos hcc₁ hβ hββ₀ H1 H2 H3 H4 v lam hlam
      hox hξ0 hξ1 hηξ
    rw [hexpo] at hb
    exact hb
  · intro v β hβ hββ₁ lam hlam o x hox ξ hξ0 hξ1 hηξ
    obtain ⟨hββ₀, H1, H2, H3, H4⟩ := hH β hβ hββ₁
    have hb := markedDomain_bound_subGaussian hL (squarePeriodic L) (squarePeriodic_connected L hL)
      (fun _ _ => rfl) (SpinWaves.squarePeriodicBipartiteDegreeFour L hE hL)
      ((SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).2 hE) hD₁'1 hD₂.le
      ((h22 L hL).2 hE) (hmono ((h21 L hL).2 hE)) ((h24 L hL).2 hE) hdamp hη hcpos hcc₁
      hβ hββ₀ H1 H2 H3 H4 v lam hlam hox hξ0 hξ1 hηξ
    rw [hexpo] at hb
    exact hb

end SubGaussian

end FroehlichSpencer.BKT.Coulomb
