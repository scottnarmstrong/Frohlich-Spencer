/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyTerminalProfiles

/-! # Aggregate charge pairing over bounded scales -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- The selected-square profiles from scales `1` through `n`, added to a
separately supplied base profile. The base profile accounts for `A₀`; every
selected square contributes one unit to the pairing. -/
theorem exists_boundaryEnergy_aggregateProfile
    (Miso Msel α : ℝ) (hMiso : 1 < Miso) (hα : 1 ≤ α)
    (hMsel : 1 ≤ Msel) (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    {N : Finset (ChargeDensity L)} (hgeom : AppendixDChargeGeometry Miso α N)
    {ρ : ChargeDensity L} (hρ : ρ ∈ N)
    (n : ℕ) (C : ℕ → Finset (Finset (Site L)))
    (hC : ∀ j ∈ Finset.Icc 1 n,
      IsMinimumSquareCover .free L j ρ (C j))
    (A₀ : ℝ) (_hA₀ : 0 ≤ A₀)
    (base : RotatorDualFace L → ℝ) (hbaseRoot : base none = 0)
    (hbasePair : A₀ / 2 ≤ ∑ x, base (some x) * (ρ x : ℝ))
    (hbaseBoundary : ∀ x : Site L, siteBoundaryDepth x = 1 →
      base (some x) = 0) :
    ∃ U : RotatorDualFace L → ℝ, U none = 0 ∧
      (A₀ / 2 + ∑ j ∈ Finset.Icc 1 n,
        ((pinnedPPrime Msel α j ρ (C j)).card : ℝ)) ≤
          ∑ x, U (some x) * (ρ x : ℝ) ∧
      ∀ x : Site L, siteBoundaryDepth x = 1 → U (some x) = 0 := by
  classical
  let V : ℕ → RotatorDualFace L → ℝ := fun j =>
    boundaryEnergyScaleField ρ
      (pinnedPPrime Msel α j ρ (C j)) ((2 : ℝ) ^ j)
  have hV (j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
      V j none = 0 ∧
        ((pinnedPPrime Msel α j ρ (C j)).card : ℝ) ≤
          ∑ x, V j (some x) * (ρ x : ℝ) ∧
        (∀ x : Site L, siteBoundaryDepth x = 1 → V j (some x) = 0) := by
    simpa only [V] using boundaryEnergyTerminalScaleField_properties
      Miso Msel α hMiso hα hMsel hmargin ρ N hgeom.isolated hρ j (C j) (hC j hj)
  let U : RotatorDualFace L → ℝ := fun z =>
    base z + ∑ j ∈ Finset.Icc 1 n, V j z
  refine ⟨U, ?_, ?_, ?_⟩
  · simp only [U, hbaseRoot, zero_add]
    rw [Finset.sum_eq_zero]
    intro j hj
    exact (hV j hj).1
  · have hscalePair :
        (∑ j ∈ Finset.Icc 1 n,
          ((pinnedPPrime Msel α j ρ (C j)).card : ℝ)) ≤
          ∑ j ∈ Finset.Icc 1 n, ∑ x, V j (some x) * (ρ x : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hV j hj).2.1
    have hpairId :
        (∑ x, U (some x) * (ρ x : ℝ)) =
          (∑ x, base (some x) * (ρ x : ℝ)) +
            ∑ j ∈ Finset.Icc 1 n, ∑ x, V j (some x) * (ρ x : ℝ) := by
      calc
        (∑ x, U (some x) * (ρ x : ℝ)) =
            ∑ x, (base (some x) * (ρ x : ℝ) +
              (∑ j ∈ Finset.Icc 1 n, V j (some x)) * (ρ x : ℝ)) := by
                apply Finset.sum_congr rfl
                intro x hx
                simp only [U]
                ring
        _ = (∑ x, base (some x) * (ρ x : ℝ)) +
              ∑ x, (∑ j ∈ Finset.Icc 1 n, V j (some x)) * (ρ x : ℝ) := by
                rw [Finset.sum_add_distrib]
        _ = (∑ x, base (some x) * (ρ x : ℝ)) +
              ∑ x, ∑ j ∈ Finset.Icc 1 n, V j (some x) * (ρ x : ℝ) := by
                congr 1
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.sum_mul]
        _ = (∑ x, base (some x) * (ρ x : ℝ)) +
              ∑ j ∈ Finset.Icc 1 n, ∑ x, V j (some x) * (ρ x : ℝ) := by
                congr 1
                rw [Finset.sum_comm]
    calc
      A₀ / 2 +
          ∑ j ∈ Finset.Icc 1 n,
            ((pinnedPPrime Msel α j ρ (C j)).card : ℝ) ≤
          (∑ x, base (some x) * (ρ x : ℝ)) +
            ∑ j ∈ Finset.Icc 1 n, ∑ x, V j (some x) * (ρ x : ℝ) :=
              add_le_add hbasePair hscalePair
      _ = ∑ x, U (some x) * (ρ x : ℝ) := hpairId.symm
  · intro x hx
    simp only [U, hbaseBoundary x hx, zero_add]
    rw [Finset.sum_eq_zero]
    intro j hj
    exact (hV j hj).2.2 x hx

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
