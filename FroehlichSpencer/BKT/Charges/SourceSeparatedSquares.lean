/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.SeparatedPatch

/-! # Source indexing for separated square families

KP defines the separated family at positive scales. The recurrence in Lemma
4.1 can have output scale zero (`γ(21) = γ(22) = 0`), so this module extends
the same predicate (2.4) to `k = 0`. This extension is used only by the
recurrence; Proposition 2.1 continues to sum the source-defined positive
scales.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The same separation threshold as (2.4), extended to every natural scale. -/
noncomputable def squareSeparationThresholdNat (k : ℕ) : ℝ :=
  (2 * (chargeCoverScale : ℝ)) *
    (2 : ℝ) ^ (chargeCoverExponent * (k + 1 : ℕ))

/-- The separated members of a chosen minimum cover, using the formula (2.4)
at every natural scale. At scale zero this is the recurrence extension of the
positive-scale source definition. -/
noncomputable def separatedSquaresNat (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) (k : ℕ)
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k ρ C}) : Finset (Finset (Fin L × Fin L)) := by
  classical
  exact C.val.filter fun s => 1 < C.val.card ∧
    ∀ t ∈ C.val, t ≠ s →
      squareSeparationThresholdNat k ≤
        (squareDistance boundary L s t : ℝ)

/-- On positive scales the extension is exactly KP's `separatedSquares`. -/
theorem separatedSquaresNat_eq_separatedSquares (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) (k : ℕ) (hk : 1 ≤ k)
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k ρ C}) :
    separatedSquaresNat boundary L ρ k C =
      separatedSquares boundary L ρ ⟨k, hk⟩ C := by
  classical
  simp [separatedSquaresNat, separatedSquares, squareSeparationThresholdNat]

/-- The scale-zero recurrence term is bounded by the scale-zero cover size. -/
theorem card_separatedSquaresNat_zero_le (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L)
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L 0 ρ C}) :
    (separatedSquaresNat boundary L ρ 0 C).card ≤ C.val.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

end FroehlichSpencer.BKT

end
