/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.SOSDirichlet
public import FroehlichSpencer.BKT.Surface.SOSDirichletLaw
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.sos_roughening_transition`

It is imported only
by that statement.

-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site siteBoundaryDepth euclideanSiteDistance)
open FroehlichSpencer.BKT.SOS.Roughening (sosHeightWeight sosHeightWeight_pos sosPartition
  sosVariance pinnedGrad pinnedField linfDist)
open FroehlichSpencer.BKT.Bridge.SOSDirichlet


theorem sos_roughening_transition :
    ∃ β₀ β₁ : ℝ, 0 < β₀ ∧ β₀ < β₁ ∧
      (∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → ∀ K : ℝ, ∃ (L : ℕ) (u v : Fin L × Fin L),
        ENNReal.ofReal K < ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ) ∧
      ∃ C : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₁ ≤ β → ∀ (L : ℕ) (u v : Fin L × Fin L),
        ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ ≤
          ENNReal.ofReal C := by
  obtain ⟨⟨β₀, β', L₀, hβ₀, -, hrough⟩, ⟨β₁, C, hβ₁, hC, hsmooth⟩⟩ :=
    SOS.Peierls.sos_roughening_transition
  refine ⟨min β₀ (β₁ / 2), β₁, lt_min hβ₀ (by linarith), (min_le_right _ _).trans_lt (by linarith),
    fun β hβ hββ₀ K => ?_, C, fun β hβ hββ₁ L u v => ?_⟩
  · obtain ⟨-, h⟩ := hrough β hβ (hββ₀.trans (min_le_left _ _))
    obtain ⟨L, u, v, -, -, hK⟩ := h (max K 0)
    have hL : 1 < L := by
      by_contra hL
      have hle : L ≤ 1 := by omega
      have huv : u = v := by
        rcases Nat.lt_or_ge L 1 with h0 | h1
        · exact absurd u.1.isLt (by omega)
        · have : L = 1 := by omega
          subst this
          exact Subsingleton.elim _ _
      rw [huv, sosVariance_self] at hK
      linarith [le_max_right K 0]
    refine ⟨L, u, v, ?_⟩
    rw [lintegral_sq_eq hL hβ]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [le_max_right K 0])).mpr
      (lt_of_le_of_lt (le_max_left _ _) hK)
  · rcases Nat.lt_or_ge 1 L with hL | hL
    · rw [lintegral_sq_eq hL hβ]
      exact ENNReal.ofReal_le_ofReal (hsmooth β hββ₁ L u v)
    · have huv : u = v := by
        rcases Nat.lt_or_ge L 1 with h0 | h1
        · exact absurd u.1.isLt (by omega)
        · have : L = 1 := by omega
          subst this
          exact Subsingleton.elim _ _
      subst huv
      simp

end FroehlichSpencer.BKT.Provider

end
