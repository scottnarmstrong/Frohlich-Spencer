/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.WiredVillainDisorder
public import FroehlichSpencer.BKT.Surface.WiredVillainDisorderLimit
public import FroehlichSpencer.BKT.Coulomb.ThermodynamicLimit
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.wiredVillain_disorderLimit_upper_bound`

From the internal `villainDisorder_bound` through `Bridge.WiredVillainDisorder.wired_bound`, with
`β'' = c η² β / ξ²`, `η = min(ξ, 1 − ξ)`, and the constant `2`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.VillainDisorder
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap dipoleGap_pos)
open FroehlichSpencer.BKT.Bridge.WiredVillainDisorder


theorem wiredVillain_disorderLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      (∃ D : ℕ → ℝ, IsWiredVillainDisorderLimit β hβ ξ D) ∧
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ D : ℕ → ℝ, IsWiredVillainDisorderLimit β hβ ξ D →
        ∀ n : ℕ, D n ≤ A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) := by
  classical
  obtain ⟨c, hc, h⟩ := wired_bound
  intro ξ hξ0 hξ1
  obtain ⟨β₀, -, hD⟩ := h ξ hξ0 hξ1
  refine ⟨β₀, fun β hβ hββ₀ => ⟨?_, c * dipoleGap ξ ^ 2 * β / ξ ^ 2, ?_, 2, ?_⟩⟩
  · -- existence: a joint subsequence of the centred boxes
    set u : ℕ → ℕ → ℝ := fun L n =>
      if hL : L / 2 + n < L ∧ L / 2 + 1 < L then
        ∫ θ, wiredVillainDisorder L β hβ ξ (⟨L / 2, by omega⟩, ⟨L / 2, by omega⟩) n ⟨hL.1, hL.2⟩ θ
          ∂villainLaw L β hβ
      else 0
    have hu : ∀ L n, |u L n| ≤ 2 := by
      intro L n
      simp only [u]
      split_ifs with hL
      · obtain ⟨h1, h2⟩ := hD β hβ hββ₀ L (⟨L / 2, by omega⟩, ⟨L / 2, by omega⟩) n ⟨hL.1, hL.2⟩
        rw [abs_of_nonneg h1]
        refine h2.trans ?_
        have hp : 0 ≤ c * dipoleGap ξ ^ 2 * β := by
          have := dipoleGap_pos hξ0 hξ1
          positivity
        have : ((n : ℝ) + 1) ^ (-(c * dipoleGap ξ ^ 2 * β)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
            (by linarith)
        linarith
      · simp
    obtain ⟨φ, hφ, D, hDlim⟩ := Coulomb.exists_subseq_tendsto_pointwise u (fun _ => 2) hu
    refine ⟨D, φ, hφ.tendsto_atTop, fun n => ?_⟩
    have hfits : ∀ᶠ k in atTop, φ k / 2 + n < φ k ∧ φ k / 2 + 1 < φ k := by
      filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop (2 * n + 4))] with k hk
      omega
    obtain ⟨K, hK⟩ := eventually_atTop.1 hfits
    have : Nonempty {k : ℕ // φ k / 2 + n < φ k ∧ φ k / 2 + 1 < φ k} := ⟨⟨K, hK K le_rfl⟩⟩
    have hval : Tendsto (Subtype.val : {k : ℕ // φ k / 2 + n < φ k ∧ φ k / 2 + 1 < φ k} → ℕ)
        atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨⟨max b K, hK _ (le_max_right _ _)⟩,
        fun k hk => (le_max_left b K).trans hk⟩
    refine ((hDlim n).comp hval).congr' (Eventually.of_forall fun k => ?_)
    simp only [Function.comp_apply, u, dite_eq_left k.2]
  · have := dipoleGap_pos hξ0 hξ1
    positivity
  · rintro D ⟨Ls, hLs, hconv⟩ n
    have hfits : ∀ᶠ k in atTop, Ls k / 2 + n < Ls k ∧ Ls k / 2 + 1 < Ls k := by
      filter_upwards [hLs.eventually (eventually_ge_atTop (2 * n + 4))] with k hk
      omega
    obtain ⟨K, hK⟩ := eventually_atTop.1 hfits
    have : Nonempty {k : ℕ // Ls k / 2 + n < Ls k ∧ Ls k / 2 + 1 < Ls k} := ⟨⟨K, hK K le_rfl⟩⟩
    refine le_of_tendsto (hconv n) (Eventually.of_forall fun k => ?_)
    rw [exponent_eq hξ0, add_comm (1 : ℝ)]
    exact (hD β hβ hββ₀ (Ls k) _ n ⟨k.2.1, k.2.2⟩).2

end FroehlichSpencer.BKT.Provider

end
