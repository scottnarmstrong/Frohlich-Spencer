/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyOverlap
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyGeometry

/-! # Selected-square separation and profile-neighborhood overlap -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

variable {L : ℕ}

private theorem boundaryEnergy_one_le_two_pow (j : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; nlinarith

/-- Distinct squares retained by pinnedPPrime inherit its same-scale separation,
including the one-square override. -/
theorem boundaryEnergy_selectedSquares_separated
    (M α : ℝ) (j : ℕ) (ρ : ChargeDensity L)
    (C : Finset (Finset (Site L))) (hC : IsMinimumSquareCover .free L j ρ C)
    {s t : Finset (Site L)}
    (hs : s ∈ pinnedPPrime M α j ρ C)
    (ht : t ∈ pinnedPPrime M α j ρ C) (hst : s ≠ t) :
    2 * M * ((2 : ℝ) ^ j) ^ α ≤ euclideanSetDistance s t := by
  have hsC : s ∈ C := pinnedPPrime_mem_of_minimumCover M α j ρ C hC hs |>.1
  have htC : t ∈ C := pinnedPPrime_mem_of_minimumCover M α j ρ C hC ht |>.1
  have hpow : ((2 : ℝ) ^ j) ^ α = (2 : ℝ) ^ (α * (j : ℝ)) := by
    calc
      ((2 : ℝ) ^ j) ^ α = (2 : ℝ) ^ ((j : ℝ) * α) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      _ = (2 : ℝ) ^ (α * (j : ℝ)) := by
        congr 1
        ring
  by_cases hsingle : C.card = 1
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsingle
    have hsu : s = u := by simpa [hu] using hsC
    have htu : t = u := by simpa [hu] using htC
    exact (hst (hsu.trans htu.symm)).elim
  · simpa only [hpow] using
      ((mem_pinnedPPrime_of_cover_card_ne_one M α j ρ C hsingle s).mp hs).2.1
        t htC hst.symm

/-- At one scale the doubled support neighborhoods of distinct selected
squares are disjoint. -/
theorem boundaryEnergy_selectedNeighborhoods_disjoint_same_scale
    (j : ℕ) (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C)
    {s t : Finset (Site L)}
    (hs : s ∈ pinnedPPrime chargeCoverScale chargeCoverExponent j ρ C)
    (ht : t ∈ pinnedPPrime chargeCoverScale chargeCoverExponent j ρ C)
    (hst : s ≠ t)
    (hnear : (boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ j) s ∩
      boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ j) t).Nonempty) : False := by
  have hsep := boundaryEnergy_selectedSquares_separated chargeCoverScale
    chargeCoverExponent j ρ C hC hs ht hst
  have hq : 1 ≤ (2 : ℝ) ^ j := boundaryEnergy_one_le_two_pow j
  have hpow : (2 : ℝ) ^ j ≤ ((2 : ℝ) ^ j) ^ chargeCoverExponent := by
    calc
      (2 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((2 : ℝ) ^ j) ^ chargeCoverExponent :=
        Real.rpow_le_rpow_of_exponent_le hq (by norm_num [chargeCoverExponent])
  have hqpos : 0 < (2 : ℝ) ^ j := by positivity
  have hcoef : 4 < 2 * (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
  have hstrong : 4 * (2 : ℝ) ^ j <
      2 * chargeCoverScale * ((2 : ℝ) ^ j) ^ chargeCoverExponent := by
    calc
      4 * (2 : ℝ) ^ j < (2 * (chargeCoverScale : ℝ)) * (2 : ℝ) ^ j :=
        mul_lt_mul_of_pos_right hcoef hqpos
      _ ≤ (2 * (chargeCoverScale : ℝ)) * ((2 : ℝ) ^ j) ^ chargeCoverExponent :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  have hclose := boundaryEnergy_two_neighborhoods_close s t
    (2 * (2 : ℝ) ^ j) hnear
  have hlt : euclideanSetDistance s t <
      2 * chargeCoverScale * ((2 : ℝ) ^ j) ^ chargeCoverExponent := by
    exact hclose.trans_lt (by nlinarith [hstrong])
  exact (not_lt_of_ge hsep) hlt

/-- The fine profile neighborhood cannot meet two larger-scale selected-square
neighborhoods. The doubled radii allow for endpoints of an edge gradient. -/
theorem boundaryEnergy_terminalNeighborhood_at_most_one_coarse
    (j k : ℕ) (hjk : j < k) (s t₁ t₂ : Finset (Site L))
    (Ck : Finset (Finset (Site L))) (ρ : ChargeDensity L)
    (hCk : IsMinimumSquareCover .free L k ρ Ck)
    (ht₁ : t₁ ∈ pinnedPPrime chargeCoverScale chargeCoverExponent k ρ Ck)
    (ht₂ : t₂ ∈ pinnedPPrime chargeCoverScale chargeCoverExponent k ρ Ck)
    (hne : t₁ ≠ t₂)
    (hs : s ∈ kpSquares .free L j)
    (hnear₁ : (boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ j) s ∩
      boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ k) t₁).Nonempty)
    (hnear₂ : (boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ j) s ∩
      boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ k) t₂).Nonempty) : False := by
  have hsep := boundaryEnergy_selectedSquares_separated chargeCoverScale
    chargeCoverExponent k ρ Ck hCk ht₁ ht₂ hne
  have hq : 0 ≤ (2 : ℝ) ^ k := by positivity
  have hqpow : 0 ≤ ((2 : ℝ) ^ k) ^ chargeCoverExponent :=
    Real.rpow_nonneg hq chargeCoverExponent
  have h2pow : (2 : ℝ) ^ chargeCoverExponent ≤ 4 := by
    calc
      (2 : ℝ) ^ chargeCoverExponent ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [chargeCoverExponent])
      _ = 4 := by norm_num
  have hsep' : 8 * ((2 : ℝ) ^ (k + 1)) ^ chargeCoverExponent ≤
      euclideanSetDistance t₁ t₂ := by
    have hpow : ((2 : ℝ) ^ (k + 1)) ^ chargeCoverExponent =
        2 ^ chargeCoverExponent * ((2 : ℝ) ^ k) ^ chargeCoverExponent := by
      rw [show (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k by
        rw [pow_succ]; ring, Real.mul_rpow (by norm_num) hq]
    rw [hpow]
    have hcoeff : 8 * (2 : ℝ) ^ chargeCoverExponent ≤
        2 * (chargeCoverScale : ℝ) := by
      change 8 * (2 : ℝ) ^ chargeCoverExponent ≤ 2 * 65536
      nlinarith [h2pow]
    calc
      8 * ((2 : ℝ) ^ chargeCoverExponent * ((2 : ℝ) ^ k) ^ chargeCoverExponent) =
          (8 * (2 : ℝ) ^ chargeCoverExponent) * ((2 : ℝ) ^ k) ^ chargeCoverExponent := by ring
      _ ≤
          (2 * (chargeCoverScale : ℝ)) * ((2 : ℝ) ^ k) ^ chargeCoverExponent :=
            mul_le_mul_of_nonneg_right hcoeff hqpow
      _ ≤ euclideanSetDistance t₁ t₂ := by
        simpa [mul_assoc] using hsep
  have hdiam₀ := freeSquare_euclideanDiameter_le hs
  have hdiam : euclideanSetDiameter s ≤ Real.sqrt 2 * (2 * (2 : ℝ) ^ j) := by
    have hpow : (2 : ℝ) ^ j ≤ 2 * (2 : ℝ) ^ j := by
      have hnonneg : 0 ≤ (2 : ℝ) ^ j := by positivity
      nlinarith
    exact hdiam₀.trans (mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg 2))
  have hR : 0 ≤ 2 * (2 : ℝ) ^ k := by positivity
  have hRone : 1 ≤ 2 * (2 : ℝ) ^ k := by
    have hpow : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih => rw [pow_succ]; nlinarith
    have := hpow k
    nlinarith
  have hr : 0 < 2 * (2 : ℝ) ^ j := by positivity
  have hscale : 2 * (2 : ℝ) ^ j ≤ (2 * (2 : ℝ) ^ k) / 2 := by
    have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k := by
      have hnat : j + 1 ≤ k := by omega
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) hnat)
    rw [pow_succ] at hpow
    have hpow' : 2 * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k := by
      nlinarith [hpow]
    nlinarith [hpow']
  have hsepRadius : 8 * (2 * (2 : ℝ) ^ k) ^ chargeCoverExponent ≤
      euclideanSetDistance t₁ t₂ := by
    have hrpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
      rw [pow_succ]
      ring
    rw [← hrpow]
    exact hsep'
  exact boundaryEnergy_neighborhood_overlap_excludes_two_coarse s t₁ t₂
    (2 * (2 : ℝ) ^ j) (2 * (2 : ℝ) ^ k) 4 chargeCoverExponent
    hdiam hr hR hRone hscale
    (by norm_num) (by norm_num [chargeCoverExponent])
    (by simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hsepRadius)
    hnear₁ hnear₂

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
