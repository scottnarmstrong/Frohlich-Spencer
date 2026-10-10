/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.InductionDefs
public import FroehlichSpencer.T12.Obstacles
import FroehlichSpencer.T12.FiniteVolumeT21

/-!
# the deterministic induction’s finite-volume T2.1 in the form consumed by the T1.2_Λ assembly

The joint induction exports `FroehlichSpencer.T12.exists_finiteVolumeT21_rate`
(`FiniteVolumeT21 ν P M` for `K₀ ≥ K₁(ν)` and `𝒩 ≥ 2ν e^{max 1 (2M)}`, a corollary of
`exists_finiteVolumeT21`).

The assembly theorem `probability_bound_of_T21` takes one fixed scale
constant `K₀` with the Appendix-D `ScaleConditions` and a threshold `N₀(M)` for every requested
rate `M`; this module supplies it unconditionally, with `K₀ = max K₁ K_sc`
(`exists_scaleConditions`) and `N₀(M) = 2ν e^{max 1 (2M)}`.
-/

@[expose] public section

namespace FroehlichSpencer.T12.Assembly

open Multiscale


theorem t21Hyp_of_finiteVolumeT21_rate {ν : ℕ}
    (h : ∃ K₁ : ℝ, ∀ (M : ℝ) (P : Params), K₁ ≤ P.K₀ →
      2 * ν * Real.exp (max 1 (2 * M)) ≤ P.Nthr → FiniteVolumeT21 ν P M) :
    ∃ K₀ : ℝ, ScaleConditions K₀ ∧ ∀ M : ℝ, ∃ N₀ : ℝ, ∀ P : Params, P.K₀ = K₀ →
      N₀ ≤ P.Nthr → ∀ (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ), JPred P Λ v (k + 1) M := by
  obtain ⟨K₁, hK₁⟩ := h
  obtain ⟨Ks, hKs⟩ := exists_scaleConditions
  exact ⟨max K₁ Ks, hKs _ (le_max_right _ _), fun M => ⟨2 * ν * Real.exp (max 1 (2 * M)),
    fun P hP hN => hK₁ M P (hP ▸ le_max_left _ _) hN⟩⟩


theorem t21Hyp (ν : ℕ) (hν : 0 < ν) :
    ∃ K₀ : ℝ, ScaleConditions K₀ ∧ ∀ M : ℝ, ∃ N₀ : ℝ, ∀ P : Params, P.K₀ = K₀ →
      N₀ ≤ P.Nthr → ∀ (Λ : Finset (Site ν)) (v : Site ν → ℝ) (k : ℕ), JPred P Λ v (k + 1) M :=
  t21Hyp_of_finiteVolumeT21_rate (exists_finiteVolumeT21_rate ν hν)

end FroehlichSpencer.T12.Assembly

end
