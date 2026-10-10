/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.SourceSeparatedSquares
public import FroehlichSpencer.BKT.Charges.RecurrenceArithmetic

/-! # The numerical span budget in Lemma 4.1

For `α = 7/4` and `M = 2^16`, the separation threshold at `γ(k)` leaves
enough room for every linked pair or triple of lower-scale squares inside one
scale-`k` square. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The natural scale corresponding to the total auxiliary recurrence map. -/
noncomputable def l41LowerScale (k : ℕ) : ℕ :=
  (recurrenceGamma (k : ℤ)).toNat

/-- At every valid source scale `k≥b`, `γ(k)` is nonnegative and strictly
smaller than `k`. -/
theorem l41LowerScale_spec (k : ℕ) (hk : 21 ≤ k) :
    (l41LowerScale k : ℤ) = recurrenceGamma (k : ℤ) ∧
      l41LowerScale k + 4 ≤ k := by
  have harg : 0 ≤ (4 / 7 : ℝ) * (k : ℝ) - 83 / 7 := by
    have hkR : (21 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith only [hkR]
  have hnonneg : 0 ≤ recurrenceGamma (k : ℤ) := by
    change 0 ≤ ⌊(4 / 7 : ℝ) * (k : ℝ) - 83 / 7⌋
    exact Int.floor_nonneg.mpr harg
  have hcast : (l41LowerScale k : ℤ) = recurrenceGamma (k : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  have hcastR : (l41LowerScale k : ℝ) =
      (recurrenceGamma (k : ℤ) : ℝ) := by exact_mod_cast hcast
  have hupper := (recurrenceGamma_bounds (k : ℤ)).2
  have hkR : (21 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hupperR : (recurrenceGamma (k : ℤ) : ℝ) ≤
      (4 / 7 : ℝ) * k - 83 / 7 := by simpa using hupper
  have hgammaGap : (recurrenceGamma (k : ℤ) : ℝ) + 4 ≤ k := by
    nlinarith only [hupperR, hkR]
  have hgap : (l41LowerScale k : ℝ) + 4 ≤ k := by
    rw [hcastR]
    exact hgammaGap
  exact ⟨hcast, by exact_mod_cast hgap⟩

/-- The scale-`γ(k)` separation threshold is at most one quarter of the
target side. -/
theorem l41_separationThreshold_le_quarter_target (k : ℕ) (hk : 21 ≤ k) :
    squareSeparationThresholdNat (l41LowerScale k) ≤
      (squareSide k : ℝ) / 4 := by
  obtain ⟨hgamma, hgap⟩ := l41LowerScale_spec k hk
  have hcastR : (l41LowerScale k : ℝ) =
      (recurrenceGamma (k : ℤ) : ℝ) := by exact_mod_cast hgamma
  have hgammaR : (l41LowerScale k : ℝ) ≤
      (4 / 7 : ℝ) * k - 83 / 7 := by
    rw [hcastR]
    exact (recurrenceGamma_bounds (k : ℤ)).2
  have hexp : (17 : ℝ) + (7 / 4 : ℝ) * ((l41LowerScale k : ℝ) + 1) ≤
      (k : ℝ) - 2 := by
    nlinarith only [hgammaR]
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (x := (2 : ℝ)) (by norm_num) hexp
  have hscale : squareSeparationThresholdNat (l41LowerScale k) =
      (2 : ℝ) ^ ((17 : ℝ) + (7 / 4 : ℝ) * ((l41LowerScale k : ℝ) + 1)) := by
    change (2 * (chargeCoverScale : ℝ)) *
      (2 : ℝ) ^ (chargeCoverExponent * (l41LowerScale k + 1 : ℕ)) = _
    rw [show 2 * (chargeCoverScale : ℝ) = (2 : ℝ) ^ 17 by
      norm_num [chargeCoverScale], chargeCoverExponent]
    calc
      (2 : ℝ) ^ 17 * (2 : ℝ) ^ ((7 / 4 : ℝ) * (l41LowerScale k + 1 : ℕ)) =
          (2 : ℝ) ^ ((17 : ℝ) + (7 / 4 : ℝ) * (l41LowerScale k + 1 : ℕ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
        norm_num
      _ = (2 : ℝ) ^ ((17 : ℝ) + (7 / 4 : ℝ) * ((l41LowerScale k : ℝ) + 1)) := by
        congr 1
        rw [Nat.cast_add]
        norm_num
  have hside : (2 : ℝ) ^ ((k : ℝ) - 2) = (squareSide k : ℝ) / 4 := by
    have hk2 : 2 ≤ k := by omega
    have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      rw [Nat.cast_sub hk2]
      norm_num
    rw [← hcast, Real.rpow_natCast, squareSide]
    rw [← Nat.sub_add_cancel hk2, pow_add]
    norm_num
  rw [hscale, ← hside]
  exact hpow

/-- Any one edge of the L4.1 conflict graph gives the pair span budget. -/
theorem l41_pair_budget (k d : ℕ) (hk : 21 ≤ k)
    (hd : (d : ℝ) < squareSeparationThresholdNat (l41LowerScale k)) :
    d + 2 * (squareSide (l41LowerScale k) - 1) < squareSide k := by
  have hthreshold := l41_separationThreshold_le_quarter_target k hk
  obtain ⟨_, hgap⟩ := l41LowerScale_spec k hk
  have hgap3 : l41LowerScale k + 3 ≤ k := by omega
  have hside : (squareSide (l41LowerScale k) : ℝ) ≤
      (squareSide k : ℝ) / 8 := by
    have hpow : squareSide (l41LowerScale k) * 8 ≤ squareSide k := by
      dsimp [squareSide]
      calc
        2 ^ l41LowerScale k * 8 = 2 ^ l41LowerScale k * 2 ^ 3 := by norm_num
        _ = 2 ^ (l41LowerScale k + 3) := by rw [Nat.pow_add]
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hgap3
    have hpowR : (squareSide (l41LowerScale k) : ℝ) * 8 ≤ squareSide k := by
      exact_mod_cast hpow
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith only [hpowR]
  have hsum : (d : ℝ) +
      2 * (squareSide (l41LowerScale k) : ℝ) < squareSide k := by
    nlinarith only [hd, hthreshold, hside]
  have hcast : (d + 2 * (squareSide (l41LowerScale k) - 1) : ℕ) <
      squareSide k := by
    have hleNat : d + 2 * (squareSide (l41LowerScale k) - 1) ≤
        d + 2 * squareSide (l41LowerScale k) := by omega
    have hleReal : (d + 2 * squareSide (l41LowerScale k) : ℕ) < squareSide k := by
      exact_mod_cast hsum
    omega
  exact hcast

/-- In a connected triple, the minimizing contacts with the middle square
may differ. Moving between them costs at most the middle-square diameter, so
the universal coordinate-span budget uses `5(s-1)`. The stronger scale gap
absorbs this loss. -/
theorem l41_triple_budget_five (k d₁ d₂ : ℕ) (hk : 21 ≤ k)
    (hd₁ : (d₁ : ℝ) < squareSeparationThresholdNat (l41LowerScale k))
    (hd₂ : (d₂ : ℝ) < squareSeparationThresholdNat (l41LowerScale k)) :
    d₁ + d₂ + 5 * (squareSide (l41LowerScale k) - 1) < squareSide k := by
  have hthreshold := l41_separationThreshold_le_quarter_target k hk
  obtain ⟨_, hgap⟩ := l41LowerScale_spec k hk
  have hside : (squareSide (l41LowerScale k) : ℝ) ≤
      (squareSide k : ℝ) / 16 := by
    have hpow : squareSide (l41LowerScale k) * 16 ≤ squareSide k := by
      dsimp [squareSide]
      calc
        2 ^ l41LowerScale k * 16 = 2 ^ l41LowerScale k * 2 ^ 4 := by norm_num
        _ = 2 ^ (l41LowerScale k + 4) := by rw [Nat.pow_add]
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hgap
    have hpowR : (squareSide (l41LowerScale k) : ℝ) * 16 ≤ squareSide k := by
      exact_mod_cast hpow
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    nlinarith only [hpowR]
  have hsum : (d₁ : ℝ) + d₂ +
      5 * (squareSide (l41LowerScale k) : ℝ) < squareSide k := by
    nlinarith only [hd₁, hd₂, hthreshold, hside]
  have hleNat : d₁ + d₂ + 5 * (squareSide (l41LowerScale k) - 1) ≤
      d₁ + d₂ + 5 * squareSide (l41LowerScale k) := by omega
  have hleReal : (d₁ + d₂ + 5 * squareSide (l41LowerScale k) : ℕ) <
      squareSide k := by exact_mod_cast hsum
  omega

end FroehlichSpencer.BKT

end
