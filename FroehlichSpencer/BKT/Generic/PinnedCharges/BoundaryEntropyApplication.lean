/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.SupportCover
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyFiber
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyRecurrence
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGGeometry

/-! # Finite-volume boundary entropy from isolation

This module combines the selected-family recurrence, the shifted KP fiber
count, and the summable stopping weights. The volume cutoff is stated
explicitly: every fine scale used by the recurrence must lie below the
boundary-adjusted diameter cutoff.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

/-- A fixed choice of minimum free-square cover at every scale. -/
noncomputable def boundaryEntropyMinimumCover {L : ℕ}
    (ρ : ChargeDensity L) (j : ℕ) : Finset (Finset (Site L)) :=
  Classical.choose (exists_minimumSquareCover .free L j ρ)

theorem boundaryEntropyMinimumCover_isMinimum {L : ℕ}
    (ρ : ChargeDensity L) (j : ℕ) :
    IsMinimumSquareCover .free L j ρ (boundaryEntropyMinimumCover ρ j) :=
  Classical.choose_spec (exists_minimumSquareCover .free L j ρ)

/-- Number of selected Appendix-D squares at a fine scale. -/
noncomputable def boundaryEntropySelectedCount {L : ℕ}
    (M α : ℝ) (ρ : ChargeDensity L) (j : ℕ) : ℝ :=
  ((pinnedPPrime M α j ρ (boundaryEntropyMinimumCover ρ j)).card : ℝ)

/-- Selected counts restricted to the finite charge-cutoff interval. -/
noncomputable def boundaryEntropySelectedProfile {L : ℕ}
    (M α : ℝ) (ρ : ChargeDensity L) (n j : ℕ) : ℝ :=
  if 1 ≤ j ∧ j ≤ n then boundaryEntropySelectedCount M α ρ j else 0

theorem boundaryEntropySelectedProfile_zero {L : ℕ}
    (M α : ℝ) (ρ : ChargeDensity L) (n : ℕ) :
    boundaryEntropySelectedProfile M α ρ n 0 = 0 := by
  simp [boundaryEntropySelectedProfile]

theorem boundaryEntropySelectedProfile_tail {L : ℕ}
    (M α : ℝ) (ρ : ChargeDensity L) (n j : ℕ) (hj : n < j) :
    boundaryEntropySelectedProfile M α ρ n j = 0 := by
  simp [boundaryEntropySelectedProfile, Nat.not_le_of_gt hj]

theorem boundaryEntropySelectedProfile_nonneg {L : ℕ}
    (M α : ℝ) (ρ : ChargeDensity L) (n j : ℕ) :
    0 ≤ boundaryEntropySelectedProfile M α ρ n j := by
  unfold boundaryEntropySelectedProfile
  split_ifs
  · exact Nat.cast_nonneg _
  · norm_num

theorem boundaryEntropySelectedProfile_tsum_eq {L : ℕ}
    (M α : ℝ) (ρ : ChargeDensity L) (n : ℕ) :
    (∑' j : ℕ, boundaryEntropySelectedProfile M α ρ n j) =
      ∑ j ∈ Finset.Icc 1 n, boundaryEntropySelectedCount M α ρ j := by
  have hout : ∀ j, j ∉ Finset.Icc 1 n →
      boundaryEntropySelectedProfile M α ρ n j = 0 := by
    intro j hj
    unfold boundaryEntropySelectedProfile
    split_ifs with h
    · exact False.elim (hj (Finset.mem_Icc.mpr h))
    · rfl
  rw [tsum_eq_sum hout]
  apply Finset.sum_congr rfl
  intro j hj
  simp [boundaryEntropySelectedProfile, Finset.mem_Icc.mp hj]

/-- A nonzero neutral density has at least two support sites, so its Euclidean
diameter, and hence its adjusted size, is at least one. -/
theorem boundaryAdjustedSize_ge_one_of_neutral_ne_zero {L : ℕ}
    (ρ : ChargeDensity L) (hneutral : totalCharge ρ = 0) (hρ : ρ ≠ 0) :
    1 ≤ boundaryAdjustedSize ρ := by
  rw [boundaryAdjustedSize_of_neutral ρ hneutral]
  have hsne : (chargeSupport ρ).Nonempty := chargeSupport_nonempty_of_ne_zero ρ hρ
  rcases SelectionG.diam_eq_zero_or_one_le (chargeSupport ρ) with hdiam | hdiam
  · have hcardpos : 0 < (chargeSupport ρ).card := Finset.card_pos.mpr hsne
    have hcardnotone : ¬ (chargeSupport ρ).card ≤ 1 := by
      intro hle
      have hsingle : (chargeSupport ρ).card = 1 := by omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsingle
      have htotal : totalCharge ρ = ρ x := by
        unfold totalCharge
        refine Finset.sum_eq_single x (fun y _ hy => ?_)
          (fun hx' => absurd (Finset.mem_univ x) hx')
        have hyout : y ∉ chargeSupport ρ := by
          rw [hx]
          simpa using hy
        simpa [chargeSupport] using hyout
      have hxmem : x ∈ chargeSupport ρ := by rw [hx]; simp
      have hxnonzero : ρ x ≠ 0 := by simpa [chargeSupport] using hxmem
      rw [hneutral] at htotal
      exact hxnonzero htotal.symm
    have hnotall : ¬ ∀ x ∈ chargeSupport ρ, ∀ y ∈ chargeSupport ρ, x = y := by
      intro hall
      exact hcardnotone (Finset.card_le_one.mpr hall)
    push Not at hnotall
    obtain ⟨x, hx, y, hy, hxy⟩ := hnotall
    have hdist := SelectionG.one_le_siteDist hxy
    have hdistdiam := SelectionG.siteDist_le_diam hx hy
    rw [hdiam] at hdistdiam
    linarith
  · exact hdiam

private theorem boundaryEntropyGamma_cutoff_of_chargeCutoff {L : ℕ}
    (ρ : ChargeDensity L) (hd : 1 ≤ boundaryAdjustedSize ρ)
    (k : ℕ) (hk : 29 ≤ k)
    (hkcut : k ≤ boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ) :
    16 * (2 : ℝ) ^ boundaryEntropyGamma k ≤ boundaryAdjustedSize ρ := by
  let d := boundaryAdjustedSize ρ
  let X := (chargeCoverScale : ℝ) * d ^ chargeCoverExponent
  have hd' : 1 ≤ d := hd
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd'
  have hαnonneg : 0 ≤ chargeCoverExponent := by norm_num [chargeCoverExponent]
  have hdpow : 1 ≤ d ^ chargeCoverExponent := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hd' hαnonneg
    simpa [chargeCoverExponent] using h
  have hMone : 1 ≤ (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
  have hXone : 1 ≤ X := by
    dsimp [X]
    calc
      1 = 1 * 1 := by ring
      _ ≤ (chargeCoverScale : ℝ) * d ^ chargeCoverExponent :=
        mul_le_mul hMone hdpow (by positivity) (by norm_num)
  have hlognonneg : 0 ≤ Real.logb 2 X :=
    Real.logb_nonneg (by norm_num) hXone
  have hkceil : (k : ℝ) ≤
      (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ : ℝ) := by
    exact_mod_cast hkcut
  have hceil : (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ : ℝ) <
      Real.logb 2 X + 1 := by
    exact Nat.ceil_lt_add_one hlognonneg
  have hklog : (k : ℝ) < Real.logb 2 X + 1 := hkceil.trans_lt hceil
  obtain ⟨hγcast, _⟩ := boundaryEntropyGamma_spec k hk
  have hrecUpper := (recurrenceGamma_bounds ((k : ℤ) + 8)).2
  have hrecUpperR : (recurrenceGamma ((k : ℤ) + 8) : ℝ) ≤
      (4 / 7 : ℝ) * ((k : ℝ) + 8) - 83 / 7 := by
    simpa using hrecUpper
  have hγupper : (boundaryEntropyGamma k : ℝ) ≤
      (4 / 7 : ℝ) * (k : ℝ) - 107 / 7 := by
    rw [hγcast]
    nlinarith only [hrecUpperR]
  have hγlog : (boundaryEntropyGamma k : ℝ) ≤
      (4 / 7 : ℝ) * Real.logb 2 X - 103 / 7 := by
    nlinarith only [hγupper, hklog]
  have hexp : 4 + (boundaryEntropyGamma k : ℝ) ≤
      (4 / 7 : ℝ) * Real.logb 2 X - 75 / 7 := by linarith
  have hpow : (2 : ℝ) ^ (4 + (boundaryEntropyGamma k : ℝ)) ≤
      (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X - 75 / 7) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hnatpow : (2 : ℝ) ^ boundaryEntropyGamma k =
      (2 : ℝ) ^ (boundaryEntropyGamma k : ℝ) := by
    rw [Real.rpow_natCast]
  have hleft : 16 * (2 : ℝ) ^ boundaryEntropyGamma k =
      (2 : ℝ) ^ (4 + (boundaryEntropyGamma k : ℝ)) := by
    rw [hnatpow]
    calc
      16 * (2 : ℝ) ^ (boundaryEntropyGamma k : ℝ) =
          (2 : ℝ) ^ (4 : ℕ) * (2 : ℝ) ^ (boundaryEntropyGamma k : ℝ) := by norm_num
      _ = (2 : ℝ) ^ (4 + (boundaryEntropyGamma k : ℝ)) := by
        rw [(Real.rpow_natCast (2 : ℝ) 4).symm]
        exact (Real.rpow_add (x := (2 : ℝ)) (by norm_num)
          (4 : ℝ) (boundaryEntropyGamma k : ℝ)).symm
  have hlogpow :
      (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X) = X ^ (4 / 7 : ℝ) := by
    calc
      (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X) =
          (2 : ℝ) ^ (Real.logb 2 X * (4 / 7 : ℝ)) := by
            exact congrArg (fun t : ℝ => (2 : ℝ) ^ t) (by ring)
      _ = ((2 : ℝ) ^ Real.logb 2 X) ^ (4 / 7 : ℝ) := by
        rw [Real.rpow_mul (by norm_num)]
      _ = X ^ (4 / 7 : ℝ) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (lt_of_lt_of_le
          (by norm_num) hXone)]
  have hXeq : X ^ (4 / 7 : ℝ) =
      (2 : ℝ) ^ (64 / 7 : ℝ) * d := by
    dsimp [X]
    have hM : (chargeCoverScale : ℝ) = (2 : ℝ) ^ (16 : ℕ) := by
      norm_num [chargeCoverScale]
    have hfirst : ((2 : ℝ) ^ (16 : ℕ)) ^ (4 / 7 : ℝ) =
        (2 : ℝ) ^ (64 / 7 : ℝ) := by
      calc
        ((2 : ℝ) ^ (16 : ℕ)) ^ (4 / 7 : ℝ) =
            (2 : ℝ) ^ ((16 : ℝ) * (4 / 7 : ℝ)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
              have h16 : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
              rw [h16]
        _ = (2 : ℝ) ^ (64 / 7 : ℝ) := by
          have hExp : ((16 : ℕ) : ℝ) * (4 / 7 : ℝ) = 64 / 7 := by norm_num
          exact congrArg (fun t : ℝ => (2 : ℝ) ^ t) hExp
    have hdexp : (d ^ chargeCoverExponent) ^ (4 / 7 : ℝ) = d := by
      rw [← Real.rpow_mul (by positivity)]
      norm_num [chargeCoverExponent]
    calc
      ((chargeCoverScale : ℝ) * d ^ chargeCoverExponent) ^ (4 / 7 : ℝ) =
          ((2 : ℝ) ^ (16 : ℕ)) ^ (4 / 7 : ℝ) *
            (d ^ chargeCoverExponent) ^ (4 / 7 : ℝ) := by
              rw [hM]
              exact Real.mul_rpow (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (64 / 7 : ℝ) * d := by rw [hfirst, hdexp]
  have hconst : (2 : ℝ) ^ (-75 / 7 : ℝ) *
      (2 : ℝ) ^ (64 / 7 : ℝ) = (2 : ℝ) ^ (-11 / 7 : ℝ) := by
    calc
      _ = (2 : ℝ) ^ ((-75 / 7 : ℝ) + 64 / 7) :=
        (Real.rpow_add (x := (2 : ℝ)) (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ (-11 / 7 : ℝ) := by
        rw [show (-75 / 7 : ℝ) + 64 / 7 = -11 / 7 by norm_num]
  have hcoeff' : (2 : ℝ) ^ (-11 / 7 : ℝ) ≤ (2 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
      (y := (-11 / 7 : ℝ)) (z := (0 : ℝ)) (by norm_num) (by norm_num)
  have hcoeff : (2 : ℝ) ^ (-11 / 7 : ℝ) ≤ 1 := by simpa using hcoeff'
  calc
    16 * (2 : ℝ) ^ boundaryEntropyGamma k =
        (2 : ℝ) ^ (4 + (boundaryEntropyGamma k : ℝ)) := hleft
    _ ≤ (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X - 75 / 7) := hpow
    _ = (2 : ℝ) ^ (-75 / 7 : ℝ) *
        (2 : ℝ) ^ ((4 / 7 : ℝ) * Real.logb 2 X) := by
          rw [show (4 / 7 : ℝ) * Real.logb 2 X - 75 / 7 =
            (-75 / 7 : ℝ) + (4 / 7 : ℝ) * Real.logb 2 X by ring,
            Real.rpow_add (by norm_num)]
    _ = (2 : ℝ) ^ (-75 / 7 : ℝ) *
        ((2 : ℝ) ^ (64 / 7 : ℝ) * d) := by rw [hlogpow, hXeq]
    _ = (2 : ℝ) ^ (-11 / 7 : ℝ) * d := by rw [← mul_assoc, hconst]
    _ ≤ d := by
      simpa using mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ d)

/-- The finite-volume Appendix-D entropy estimate.
Isolation supplies the local recurrence, while the explicit cutoff hypothesis
ensures each coarse scale uses a fine scale meeting the volume condition. -/
theorem pinned_boundary_entropy_scale_uniform
    {L : ℕ} (M α : ℝ) (hM : 0 < M) (hα : 0 < α)
    (hMscale : M = chargeCoverScale) (hαscale : α = chargeCoverExponent)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation M α N) (hρ : ρ ∈ N)
    (n : ℕ) (hn : 29 ≤ n)
    (hcutoff : ∀ k, 29 ≤ k → k ≤ n →
      16 * (2 : ℝ) ^ boundaryEntropyGamma k ≤ boundaryAdjustedSize ρ) :
    (∑ j ∈ Finset.range (n + 1),
      (squareCoverNumber .free L j ρ : ℝ)) ≤
      (∑' k : ℕ, boundaryEntropyTerminalWeight k) *
        (squareCoverNumber .free L 0 ρ : ℝ) +
      (196 / 3 : ℝ) *
        (∑ j ∈ Finset.Icc 1 n, boundaryEntropySelectedCount M α ρ j) := by
  classical
  let A : ℕ → ℝ := fun k =>
    if k ≤ n then (squareCoverNumber .free L k ρ : ℝ) else 0
  let P : ℕ → ℝ := boundaryEntropySelectedProfile M α ρ n
  have hstep : ∀ k, 29 ≤ k →
      A k ≤ (1 / 2 : ℝ) * A (boundaryEntropyGamma k) +
        P (boundaryEntropyGamma k) := by
    intro k hk29
    by_cases hkn : k ≤ n
    · obtain ⟨hγcast, hγgap⟩ := boundaryEntropyGamma_spec k hk29
      have hγle : boundaryEntropyGamma k ≤ n := by omega
      have hγleK : boundaryEntropyGamma k ≤ k := by omega
      have hγposR : (1 : ℝ) ≤ (boundaryEntropyGamma k : ℝ) := by
        have hlow := (recurrenceGamma_bounds ((k : ℤ) + 8)).1
        have hkR : (29 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk29
        have hlow' : (4 / 7 : ℝ) * ((k : ℝ) + 8) -
            83 / 7 - 1 ≤ (recurrenceGamma ((k : ℤ) + 8) : ℝ) := by
          simpa using hlow
        have hγint_gt : (8 : ℝ) < (recurrenceGamma ((k : ℤ) + 8) : ℝ) := by
          norm_num at hlow'
          nlinarith only [hlow', hkR]
        have hγint : 9 ≤ recurrenceGamma ((k : ℤ) + 8) := by
          exact_mod_cast hγint_gt
        rw [hγcast]
        have hγintR : (9 : ℝ) ≤ (recurrenceGamma ((k : ℤ) + 8) : ℝ) := by
          exact_mod_cast hγint
        linarith
      have hγpos : 0 < boundaryEntropyGamma k := by exact_mod_cast hγposR
      have hcutγ := hcutoff k hk29 hkn
      have hscaleFixed := boundaryEntropyGamma_matchingScale k hk29
      have hscale : 6 * (2 : ℝ) ^ boundaryEntropyGamma k +
          3 * (2 * M * ((4 + Real.sqrt 2) * (2 : ℝ) ^ boundaryEntropyGamma k) ^ α) <
            (2 : ℝ) ^ k := by
        simpa [hMscale, hαscale, chargeCoverExponent] using hscaleFixed
      let C := boundaryEntropyMinimumCover ρ (boundaryEntropyGamma k)
      have hC := boundaryEntropyMinimumCover_isMinimum ρ (boundaryEntropyGamma k)
      have hrec := boundarySquareCoverNumber_recurrence_of_isolation_allCharges
        (L := L) (j := boundaryEntropyGamma k) (k := k)
        M α hM hα ρ N hN hρ C hC hγleK hcutγ hscale
      have hrecR : (squareCoverNumber .free L k ρ : ℝ) ≤
          ((squareCoverNumber .free L (boundaryEntropyGamma k) ρ / 2 +
            (pinnedPPrime M α (boundaryEntropyGamma k) ρ C).card : ℕ) : ℝ) := by
        exact_mod_cast hrec
      have hdiv : ((squareCoverNumber .free L (boundaryEntropyGamma k) ρ / 2 : ℕ) : ℝ) ≤
          (squareCoverNumber .free L (boundaryEntropyGamma k) ρ : ℝ) / 2 :=
        Nat.cast_div_le
      have hPγ : P (boundaryEntropyGamma k) =
          ((pinnedPPrime M α (boundaryEntropyGamma k) ρ C).card : ℝ) := by
        have hγle1 : 1 ≤ boundaryEntropyGamma k := by omega
        unfold P boundaryEntropySelectedProfile
        rw [ite_eq_left ⟨hγle1, hγle⟩]
        simp [boundaryEntropySelectedCount, C, boundaryEntropyMinimumCover]
      calc
        A k = (squareCoverNumber .free L k ρ : ℝ) := by simp [A, hkn]
        _ ≤ ((squareCoverNumber .free L (boundaryEntropyGamma k) ρ / 2 : ℕ) : ℝ) +
              (pinnedPPrime M α (boundaryEntropyGamma k) ρ C).card := by
                simpa only [Nat.cast_add] using hrecR
        _ ≤ (1 / 2 : ℝ) *
              (squareCoverNumber .free L (boundaryEntropyGamma k) ρ : ℝ) +
              (pinnedPPrime M α (boundaryEntropyGamma k) ρ C).card := by
                exact add_le_add
                  (by simpa [div_eq_mul_inv, mul_comm] using hdiv) le_rfl
        _ = (1 / 2 : ℝ) * A (boundaryEntropyGamma k) +
              P (boundaryEntropyGamma k) := by
                simp [A, hγle, hPγ]
    · have hAk : A k = 0 := by simp [A, hkn]
      have hAnonneg : 0 ≤ A (boundaryEntropyGamma k) := by
        unfold A
        split_ifs <;> positivity
      have hPnonneg : 0 ≤ P (boundaryEntropyGamma k) :=
        boundaryEntropySelectedProfile_nonneg M α ρ n _
      rw [hAk]
      positivity
  have hdepth : ∀ k, 0 < boundaryEntropyDepth k →
      29 ≤ k ∧ boundaryEntropyDepth (boundaryEntropyGamma k) + 1 =
        boundaryEntropyDepth k := by
    intro k hk
    exact ⟨boundaryEntropyDepth_pos_lower hk,
      (boundaryEntropyDepth_gamma k (boundaryEntropyDepth_pos_lower hk)).symm⟩
  have hphiZero : ∀ q : ℤ, q ≤ 8 → boundaryEntropyPhi q = 0 := by
    intro q hq
    unfold boundaryEntropyPhi
    rw [Int.toNat_of_nonpos (by omega)]
  have hphiCast : ∀ q : ℤ, 8 ≤ q →
      (boundaryEntropyPhi q : ℤ) = q - 8 := by
    intro q hq
    unfold boundaryEntropyPhi
    exact Int.toNat_of_nonneg (by omega)
  have hstop : ∀ k,
      boundaryEntropyIterate boundaryEntropyGamma (boundaryEntropyDepth k) k < 29 := by
    intro k
    have hrelation := boundaryEntropyIterate_eq_phi (boundaryEntropyDepth k)
      ((k : ℤ) + 8)
    have hstart : boundaryEntropyPhi ((k : ℤ) + 8) = k := by
      unfold boundaryEntropyPhi
      have hsub : (k : ℤ) + 8 - 8 = (k : ℤ) := by omega
      rw [hsub]
      simp
    rw [hstart] at hrelation
    have hsource := boundaryEntropyDepth_stops k
    have hsmall : boundaryEntropyPhi
        (recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8)) < 29 := by
      by_cases hq : recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8) ≤ 8
      · rw [hphiZero _ hq]
        omega
      · have hq8 : 8 ≤ recurrenceIterate (boundaryEntropyDepth k)
          ((k : ℤ) + 8) := by omega
        have hcast := hphiCast _ hq8
        have hreal : (boundaryEntropyPhi
            (recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8)) : ℤ) < 29 := by
          rw [hcast]
          omega
        exact_mod_cast hreal
    rw [hrelation]
    exact hsmall
  have hterminal : ∀ k, k < 29 → A k ≤ A 0 := by
    intro k hk
    have hkn : k ≤ n := by omega
    have hmono := squareCoverNumber_le_squareCoverNumber_zero .free L k ρ
    simpa [A, hkn] using (show
      (squareCoverNumber .free L k ρ : ℝ) ≤
        (squareCoverNumber .free L 0 ρ : ℝ) by exact_mod_cast hmono)
  have hAnonneg : ∀ k, 0 ≤ A k := by
    intro k
    unfold A
    split_ifs <;> positivity
  have hPnonneg : ∀ j, 0 ≤ P j :=
    boundaryEntropySelectedProfile_nonneg M α ρ n
  have hweights :
      (∑ k ∈ Finset.range (n + 1),
        (1 / 2 : ℝ) ^ boundaryEntropyDepth k) ≤
      ∑' k : ℕ, boundaryEntropyTerminalWeight k := by
    simpa [boundaryEntropyTerminalWeight] using boundaryEntropyTerminalWeight_sum_le n
  have hfiber : ∀ m,
      (∑ k ∈ Finset.range (n + 1),
        P (boundaryEntropyIterate boundaryEntropyGamma (m + 1) k)) ≤
        (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℕ, P j := by
    intro m
    exact boundaryEntropy_nat_layer_sum_bound n m P
      (boundaryEntropySelectedProfile_zero M α ρ n)
      (boundaryEntropySelectedProfile_tail M α ρ n)
      hPnonneg
  have hbound := boundaryEntropy_sum_bound_of_iteration_fibers
    A P boundaryEntropyGamma boundaryEntropyDepth 29 n hstep hdepth hstop
    hterminal hAnonneg hPnonneg
    (∑' k : ℕ, boundaryEntropyTerminalWeight k) hweights hfiber
  have hAfinite :
      (∑ k ∈ Finset.range (n + 1),
        (squareCoverNumber .free L k ρ : ℝ)) =
      ∑ k ∈ Finset.range (n + 1), A k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by
      simp only [Finset.mem_range] at hk
      omega
    simp [A, hkn]
  rw [hAfinite]
  have hprofile := boundaryEntropySelectedProfile_tsum_eq M α ρ n
  calc
    (∑ k ∈ Finset.range (n + 1), A k) ≤
        (∑' k : ℕ, boundaryEntropyTerminalWeight k) * A 0 +
          (196 / 3 : ℝ) * ∑' j : ℕ, P j := hbound
    _ = (∑' k : ℕ, boundaryEntropyTerminalWeight k) *
          (squareCoverNumber .free L 0 ρ : ℝ) +
        (196 / 3 : ℝ) *
          (∑ j ∈ Finset.Icc 1 n, boundaryEntropySelectedCount M α ρ j) := by
      rw [hprofile]
      simp [A]

/-- The entropy estimate through the Appendix-D charge cutoff. The scale
inequality needed by every recurrence step follows from the logarithmic
definition of that cutoff and the fixed KP constants. -/
theorem pinned_boundary_entropy_chargeCutoff
    {L : ℕ} (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation chargeCoverScale chargeCoverExponent N)
    (hρ : ρ ∈ N) (hρne : ρ ≠ 0)
    (hn : 29 ≤ boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ) :
    (∑ j ∈ Finset.range
        (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ + 1),
      (squareCoverNumber .free L j ρ : ℝ)) ≤
      (∑' k : ℕ, boundaryEntropyTerminalWeight k) *
        (squareCoverNumber .free L 0 ρ : ℝ) +
      (196 / 3 : ℝ) *
        (∑ j ∈ Finset.Icc 1
          (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ),
          boundaryEntropySelectedCount chargeCoverScale chargeCoverExponent ρ j) := by
  apply pinned_boundary_entropy_scale_uniform
    (M := chargeCoverScale) (α := chargeCoverExponent)
    (by norm_num [chargeCoverScale]) (by norm_num [chargeCoverExponent]) rfl rfl
    ρ N hN hρ
    (boundaryChargeCutoff chargeCoverScale chargeCoverExponent ρ) hn
  intro k hk29 hkcut
  have hd : 1 ≤ boundaryAdjustedSize ρ := by
    by_cases hneutral : totalCharge ρ = 0
    · exact boundaryAdjustedSize_ge_one_of_neutral_ne_zero ρ hneutral hρne
    · exact one_le_boundaryAdjustedSize_of_charged_ne_zero ρ hneutral hρne
  exact boundaryEntropyGamma_cutoff_of_chargeCutoff ρ
    hd
    k hk29 hkcut

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
