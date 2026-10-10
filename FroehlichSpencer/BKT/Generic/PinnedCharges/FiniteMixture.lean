/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Renormalization.Mixture

/-! # Finite cosine-product mixture for the pinned Appendix D input

The scale expansion of the finite trigonometric input is the unchanged
algebraic part of KP's general-mixture T2.2 proof. This file specializes it to
the initial product `∏ⱼ (1 + zⱼ cos ψⱼ)`. It does not claim the boundary-aware
separation, entropy, energy, or pinned-wave clauses.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT.Generic

variable {L : ℕ}

/-- The leaf factor produced by the singleton frequency mixture for
`1 + zⱼ cos θ`. -/
def cosineMixtureLeaf (z : Fin L × Fin L → ℝ) (j : Fin L × Fin L) (q : ℕ) : ℝ :=
  if q = 1 then |z j| else 0

theorem exists_finite_cosine_charge_mixture {L : ℕ} (hL : 1 < L)
    (z : Fin L × Fin L → ℝ) :
    ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ))
      (c : Fin n → ℝ) (K : Fin n → (Fin L × Fin L → ℤ) → ℝ),
      (∀ i, IsChargeEnsemble (N i)) ∧
      (∀ i, 0 < c i) ∧
      (∑ i, c i = 1) ∧
      (∀ ψ : Fin L × Fin L → ℝ,
        ∏ j, (1 + z j * Real.cos (ψ j)) =
          ∑ i, c i * ∏ ρ ∈ N i,
            (1 + K i ρ * Real.cos (∑ j, ψ j * (ρ j : ℝ)))) ∧
      (∀ i, AtMostOneNonNeutral (N i) ∧ IsScaleSeparated .free L (N i) ∧
        NeutralSplitsAreCharged .free L (N i) ∧
        ∀ ρ ∈ N i, ∑ j, ρ j = 0 →
          |K i ρ| ≤ Real.exp (200 * chargeCoverCost .free L ρ) *
            ∏ j ∈ chargeSupport ρ, cosineMixtureLeaf z j (ρ j).natAbs) := by
  classical
  let Nq : Fin L × Fin L → ℕ := fun _ => 1
  let coeff : Fin L × Fin L → ℕ → ℝ := fun j q =>
    if q = 1 then z j / 2 else 0
  let ζ : ∀ j, SiteMode (Nq j) → ℝ := fun _ _ => 1
  let lam : Fin L × Fin L → ℝ → ℝ := fun j θ => 1 + z j * Real.cos θ
  have hNq : ∀ j, 0 < Nq j := by intro j; norm_num [Nq]
  have hcut : ∀ j q, Nq j < q → coeff j q = 0 := by
    intro j q hq
    simp only [Nq] at hq
    simp [coeff, ne_of_gt (by omega : 1 < q)]
  have hlam : ∀ j θ, lam j θ =
      1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), coeff j q * Real.cos (q * θ) := by
    intro j θ
    simp [lam, coeff, Nq]
    ring
  have hζpos : ∀ j q, 0 < ζ j q := by intro j q; norm_num [ζ]
  have hζsum : ∀ j, ∑ q, ζ j q = 1 := by
    intro j
    simp [ζ, SiteMode, Nq]
  have hleaf : ∀ j q, mixtureLeaf Nq coeff ζ j q = cosineMixtureLeaf z j q := by
    intro j q
    by_cases hq : q = 1
    · subst q
      have habs : |z j / 2| = |z j| / 2 := by
        rw [abs_div]
        norm_num
      simp [mixtureLeaf, Nq, coeff, ζ, cosineMixtureLeaf, habs]
      ring
    · simp [mixtureLeaf, Nq, cosineMixtureLeaf, hq]
  obtain ⟨n, N, c, K, hens, hc, hcsum, hexp, hprops⟩ :=
    t22MixStep_holds .free hL (Or.inl rfl) lam Nq coeff ζ hNq hcut hlam hζpos hζsum
  refine ⟨n, N, c, K, hens, hc, hcsum, ?_, ?_⟩
  · intro ψ
    simpa [lam] using hexp ψ
  · intro i
    obtain ⟨hA, hB, hC, hD⟩ := hprops i
    refine ⟨hA, hB, hC, ?_⟩
    intro ρ hρ hneutral
    have hbound := hD ρ hρ hneutral
    simpa [hleaf] using hbound

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
