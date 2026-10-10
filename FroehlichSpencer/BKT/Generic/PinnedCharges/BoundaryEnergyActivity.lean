/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyApplication
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryProfileClosure
public import FroehlichSpencer.BKT.Charges.P21
public import FroehlichSpencer.BKT.Rotator.FreeBox

/-! # Entropy, area, and activity from terminal boundary isolation

This module combines the finite-volume entropy count with the pinned
profile-to-energy reduction.  The final activity statement is conditional on
the profile pairing and energy estimates; the profile construction supplies those hypotheses.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- Boundary isolation is monotone in its scale parameter. -/
theorem hasBoundaryIsolation_mono {M M' α : ℝ}
    (hM : M ≤ M') (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) : HasBoundaryIsolation M' α N := by
  intro ρ hρ child hchild htrigger
  have hdiam0 : 0 ≤ chargeEuclideanDiameter child :=
    SelectionG.diam_nonneg (chargeSupport child)
  have hdiamPow : 0 ≤ chargeEuclideanDiameter child ^ α :=
    Real.rpow_nonneg hdiam0 α
  have htrigger' : 2 * M * chargeEuclideanDiameter child ^ α ≤
      euclideanSetDistance (chargeSupport child)
        (chargeSupport (fun x => ρ x - child x)) := by
    nlinarith [htrigger]
  obtain ⟨hcharge, hdist⟩ := hN ρ hρ child hchild htrigger'
  refine ⟨hcharge, hdist.trans ?_⟩
  have hboundary0 : 0 ≤ chargeBoundaryDistance child :=
    le_of_lt (chargeBoundaryDistance_pos_of_ne_zero child hchild.1)
  have hboundaryPow : 0 ≤ chargeBoundaryDistance child ^ α :=
    Real.rpow_nonneg hboundary0 α
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hM (by norm_num)) hboundaryPow

def boundaryEnergyEntropyRate : ℝ :=
  (∑' k : ℕ, boundaryEntropyTerminalWeight k) + 66

/-- The entropy estimate and the logarithmic area estimate needed by
`PinnedActivityRate`, derived from the finite-volume boundary entropy count.
The entropy is the sum of minimum-cover numbers up to the charge cutoff; the
area is the scale-zero cover count plus the selected-square count. -/
theorem boundaryEnergy_entropyArea_from_isolation
    (Miso : ℝ) (hMiso : Miso ≤ chargeCoverScale)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation Miso chargeCoverExponent N)
    (hρ : ρ ∈ N) (hρne : ρ ≠ 0)
    (hn : 29 ≤ boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ) :
    (∑ j ∈ Finset.range
        (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ + 1),
        (squareCoverNumber .free L j ρ : ℝ)) ≤
          boundaryEnergyEntropyRate * ((squareCoverNumber .free L 0 ρ : ℝ) +
            ∑ j ∈ Finset.Icc 1
              (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
              boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j) ∧
      (1 / boundaryEnergyEntropyRate) * Real.log (boundaryAdjustedSize ρ) ≤
        (squareCoverNumber .free L 0 ρ : ℝ) +
          ∑ j ∈ Finset.Icc 1
            (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
            boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j := by
  classical
  let n := boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ
  let A₀ := (squareCoverNumber .free L 0 ρ : ℝ)
  let P := ∑ j ∈ Finset.Icc 1 n,
    boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j
  let H := ∑ j ∈ Finset.range (n + 1),
    (squareCoverNumber .free L j ρ : ℝ)
  let W := ∑' k : ℕ, boundaryEntropyTerminalWeight k
  let cS := boundaryEnergyEntropyRate
  have hN' : HasBoundaryIsolation chargeCoverScale chargeCoverExponent N :=
    hasBoundaryIsolation_mono hMiso N hN
  have hcount := pinned_boundary_entropy_chargeCutoff ρ N hN' hρ hρne hn
  have hW : 0 ≤ W := tsum_nonneg fun k => by
    unfold boundaryEntropyTerminalWeight
    positivity
  have hA₀ : 0 ≤ A₀ := by positivity
  have hP : 0 ≤ P := by
    apply Finset.sum_nonneg
    intro j hj
    unfold boundaryEntropySelectedCount
    positivity
  have hEntropy : H ≤ W * A₀ + (196 / 3 : ℝ) * P := by
    dsimp [H, W, A₀, P, n] at hcount ⊢
    exact hcount
  have hEntropy' : H ≤ cS * (A₀ + P) := by
    have hcoef : (196 / 3 : ℝ) ≤ 66 := by norm_num
    have hstep : W * A₀ + (196 / 3 : ℝ) * P ≤
        (W + 66) * (A₀ + P) := by
      nlinarith [mul_nonneg hW hP]
    dsimp [cS, boundaryEnergyEntropyRate]
    exact hEntropy.trans (by simpa [W] using hstep)
  have hcSpos : 0 < cS := by
    dsimp [cS, boundaryEnergyEntropyRate, W]
    have hW' : 0 ≤ ∑' k : ℕ, boundaryEntropyTerminalWeight k :=
      tsum_nonneg fun k => by
        unfold boundaryEntropyTerminalWeight
        positivity
    linarith
  have hterm : ∀ j ∈ Finset.range (n + 1),
      1 ≤ (squareCoverNumber .free L j ρ : ℝ) := by
    intro j hj
    exact_mod_cast Nat.succ_le_of_lt
      (squareCoverNumber_pos_of_ne_zero .free L j ρ hρne)
  have hlower : (n + 1 : ℝ) ≤ H := by
    dsimp [H]
    calc
      (n + 1 : ℝ) = ∑ _j ∈ Finset.range (n + 1), (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ Finset.range (n + 1), (squareCoverNumber .free L j ρ : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j hj
  have hareaLower : n + 1 ≤ cS * (A₀ + P) := by
    exact hlower.trans hEntropy'
  have hd : 1 ≤ boundaryAdjustedSize ρ := by
    by_cases hneutral : totalCharge ρ = 0
    · exact boundaryAdjustedSize_ge_one_of_neutral_ne_zero ρ hneutral hρne
    · exact one_le_boundaryAdjustedSize_of_charged_ne_zero ρ hneutral hρne
  have hdpos : 0 < boundaryAdjustedSize ρ := lt_of_lt_of_le (by norm_num) hd
  have hdlog : 0 ≤ Real.log (boundaryAdjustedSize ρ) := Real.log_nonneg hd
  have hpower : boundaryAdjustedSize ρ ≤
      boundaryAdjustedSize ρ ^ chargeCoverExponent := by
    exact Real.self_le_rpow_of_one_le hd (by norm_num [chargeCoverExponent])
  have hcutarg : boundaryAdjustedSize ρ ≤
      (chargeCoverScale : ℝ) * boundaryAdjustedSize ρ ^ chargeCoverExponent := by
    have hscale : 1 ≤ (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale)
      (Real.rpow_nonneg (le_trans (by norm_num) hd) chargeCoverExponent)]
  have hargpos : 0 < (chargeCoverScale : ℝ) *
      boundaryAdjustedSize ρ ^ chargeCoverExponent := by
    exact mul_pos (by norm_num [chargeCoverScale])
      (Real.rpow_pos_of_pos hdpos _)
  have hlogb : Real.logb 2 (boundaryAdjustedSize ρ) ≤
      Real.logb 2 ((chargeCoverScale : ℝ) *
        boundaryAdjustedSize ρ ^ chargeCoverExponent) :=
    (Real.logb_le_logb (by norm_num) hdpos hargpos).2 hcutarg
  have hceil : Real.logb 2 ((chargeCoverScale : ℝ) *
      boundaryAdjustedSize ρ ^ chargeCoverExponent) ≤ (n : ℝ) := by
    dsimp [n, boundaryChargeCutoff]
    exact Nat.le_ceil _
  have hlogln : Real.log (boundaryAdjustedSize ρ) ≤
      Real.logb 2 (boundaryAdjustedSize ρ) := by
    have h2 : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      linarith
    rw [Real.logb]
    rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  have hlogd : Real.log (boundaryAdjustedSize ρ) ≤ (n + 1 : ℝ) := by
    calc
      Real.log (boundaryAdjustedSize ρ) ≤ Real.logb 2 (boundaryAdjustedSize ρ) := hlogln
      _ ≤ Real.logb 2 ((chargeCoverScale : ℝ) *
          boundaryAdjustedSize ρ ^ chargeCoverExponent) := hlogb
      _ ≤ n := hceil
      _ ≤ n + 1 := by exact_mod_cast Nat.le_succ n
  have harea : (1 / cS) * Real.log (boundaryAdjustedSize ρ) ≤ A₀ + P := by
    calc
      (1 / cS) * Real.log (boundaryAdjustedSize ρ) =
          Real.log (boundaryAdjustedSize ρ) / cS := by ring
      _ ≤ A₀ + P := (div_le_iff₀ hcSpos).2 (by
        calc
          Real.log (boundaryAdjustedSize ρ) ≤ (n + 1 : ℝ) := hlogd
          _ ≤ (A₀ + P) * cS := by simpa [mul_comm] using hareaLower)
  refine ⟨?_, ?_⟩
  · simpa [H, A₀, P, n] using hEntropy'
  · simpa [A₀, P, n] using harea

/-- The Appendix-D activity power follows from the entropy count and a
multiscale pinned profile.  Profile construction is isolated in the two
explicit hypotheses `hpair` and `hprofileEnergy`. -/
theorem boundaryEnergy_activity_le_any_power_of_profiles
    (Miso : ℝ) (hMiso : Miso ≤ chargeCoverScale)
    (hL : 1 < L) (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation Miso chargeCoverExponent N)
    (hρ : ρ ∈ N) (hρne : ρ ≠ 0)
    (hn : 29 ≤ boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ)
    (U : RotatorDualFace L → ℝ) (hUroot : U none = 0)
    (hpair :
      ((squareCoverNumber .free L 0 ρ : ℝ) +
        ∑ j ∈ Finset.Icc 1
          (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
          boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j) / 2 ≤
        |∑ x, U (some x) * (ρ x : ℝ)|)
    (hprofileEnergy : (squareZero L).energy U ≤ 54 *
      ((squareCoverNumber .free L 0 ρ : ℝ) +
        ∑ j ∈ Finset.Icc 1
          (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
          boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j))
    (β R : ℝ) (hβ : 0 ≤ β) (hR : 0 ≤ R)
    (hThreshold :
      (R / (1 / boundaryEnergyEntropyRate) + boundaryEnergyEntropyRate) /
        (1 / 216 : ℝ) ≤ β) :
    Real.exp ((∑ j ∈ Finset.range
        (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ + 1),
        (squareCoverNumber .free L j ρ : ℝ)) - β * pinnedGreenEnergy hL ρ) ≤
      Real.exp (-R * Real.log (boundaryAdjustedSize ρ)) := by
  classical
  obtain ⟨hEntropy, hArea⟩ :=
    boundaryEnergy_entropyArea_from_isolation Miso hMiso ρ N hN hρ hρne hn
  let cS := boundaryEnergyEntropyRate
  have hcS : 0 < cS := by
    dsimp [cS, boundaryEnergyEntropyRate]
    exact add_pos_of_nonneg_of_pos (tsum_nonneg fun k => by
      unfold boundaryEntropyTerminalWeight
      positivity) (by norm_num)
  have henergy := pinnedGreenEnergy_ge_of_multiscaleProfiles hL ρ U hUroot
    ((squareCoverNumber .free L 0 ρ : ℝ))
    (∑ j ∈ Finset.Icc 1
      (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
      boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j)
    (by positivity) (by
      apply Finset.sum_nonneg
      intro j hj
      unfold boundaryEntropySelectedCount
      positivity) hpair hprofileEnergy
  have hd : 1 ≤ boundaryAdjustedSize ρ := by
    by_cases hneutral : totalCharge ρ = 0
    · exact boundaryAdjustedSize_ge_one_of_neutral_ne_zero ρ hneutral hρne
    · exact one_le_boundaryAdjustedSize_of_charged_ne_zero ρ hneutral hρne
  have henergyRate : (1 / 216 : ℝ) *
      ((squareCoverNumber .free L 0 ρ : ℝ) +
        ∑ j ∈ Finset.Icc 1
          (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
          boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j) ≤
        pinnedGreenEnergy hL ρ := by
    have := henergy
    nlinarith
  have hareaRate : 0 < 1 / cS := one_div_pos.mpr hcS
  have hArea' : (1 / cS) * Real.log (boundaryAdjustedSize ρ) ≤
      (squareCoverNumber .free L 0 ρ : ℝ) +
        ∑ j ∈ Finset.Icc 1
          (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
          boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j := by
    simpa [cS] using hArea
  exact renormalizedActivity_le_any_boundary_power β
    (∑ j ∈ Finset.range
      (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ + 1),
      (squareCoverNumber .free L j ρ : ℝ))
    (pinnedGreenEnergy hL ρ)
    ((squareCoverNumber .free L 0 ρ : ℝ) +
      ∑ j ∈ Finset.Icc 1
        (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
        boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j)
    cS (1 / 216) (1 / cS) R (boundaryAdjustedSize ρ)
    hβ hd hEntropy henergyRate hArea' hR (by norm_num) hareaRate (by
    simpa [cS] using hThreshold)

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
