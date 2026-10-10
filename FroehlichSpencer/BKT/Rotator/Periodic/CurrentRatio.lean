/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.TorusCohomology
public import FroehlichSpencer.BKT.Rotator.Periodic.SectorTools

/-!
# The periodic character as a ratio of winding-sector sums

This module closes the exact algebraic end of the periodic route: the finite-volume marked to
unmarked ratio is the ratio of the absolutely convergent winding-sector series. It also packages
the reduction of a uniform paired-sector estimate to the full ratio. The analytic paired-sector
estimate is supplied separately by the periodic Theorem C assembly.
-/

@[expose] public section

open Complex
open FroehlichSpencer.BKT.Rotator

namespace FroehlichSpencer.BKT.Rotator.Periodic

/-- The total neutral winding-sector weight is strictly positive. -/
theorem periodicNeutralSectorTsum_pos {L : ℕ} [NeZero L]
    (hL : 2 < L) {β : ℝ} (hβ : 0 < β) (hI : Summable (rotatorI β)) :
    0 < ∑' w : ℤ × ℤ, periodicNeutralSectorWeight hL β w := by
  have hsum := periodicNeutralSectorWeights_summable hL β hβ hI
  have hnonneg : ∀ w : ℤ × ℤ, 0 ≤ periodicNeutralSectorWeight hL β w :=
    fun w => (periodicNeutralSectorWeight_pos hL hβ w hI).le
  exact Summable.tsum_pos hsum hnonneg (0, 0)
    (periodicNeutralSectorWeight_pos hL hβ (0, 0) hI)

/-- The complex normalized marked integral is exactly the ratio of the total winding-sector sums.
The common raw angle-volume factor cancels. -/
theorem markedIntegral_div_partitionIntegral_eq_sectorRatio {L : ℕ} [NeZero L]
    (hL : 2 < L) {β : ℝ} (hβ : 0 < β) (a x : Site L) (ξ : ℤ)
    (hI : Summable (rotatorI β)) :
    markedIntegral L β a x ξ / (partitionIntegral L β : ℂ) =
      ((∑' w : ℤ × ℤ, periodicMarkedSectorWeight hL β a x ξ w : ℝ) /
        (∑' w : ℤ × ℤ, periodicNeutralSectorWeight hL β w : ℝ) : ℂ) := by
  have hZsum : Summable (fun w : ℤ × ℤ => periodicNeutralSectorWeight hL β w) :=
    periodicNeutralSectorWeights_summable hL β hβ hI
  have hNsum : Summable (fun w : ℤ × ℤ => periodicMarkedSectorWeight hL β a x ξ w) :=
    periodicMarkedSectorWeights_summable hL β hβ a x ξ hI
  have hZpos := periodicNeutralSectorTsum_pos hL hβ hI
  have hZne : (∑' w : ℤ × ℤ, periodicNeutralSectorWeight hL β w : ℝ) ≠ 0 :=
    ne_of_gt hZpos
  have hvol : (2 * Real.pi : ℂ) ^ Fintype.card (Site L) ≠ 0 := by
    have hp : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    exact pow_ne_zero _ hp
  rw [markedIntegral_windingSectorIdentity hL β a x ξ hI,
    partitionIntegral_windingSectorIdentity hL β hI,
    ← Complex.ofReal_tsum (fun w : ℤ × ℤ => periodicMarkedSectorWeight hL β a x ξ w),
    ← Complex.ofReal_tsum (fun w : ℤ × ℤ => periodicNeutralSectorWeight hL β w)]
  have hZneC : (∑' w : ℤ × ℤ, (periodicNeutralSectorWeight hL β w : ℂ)) ≠ 0 :=
    by
      rw [← Complex.ofReal_tsum (fun w : ℤ × ℤ => periodicNeutralSectorWeight hL β w)]
      exact Complex.ofReal_ne_zero.mpr hZne
  field_simp [hZneC, hvol]

/-- If each pair of opposite windings obeys a common ratio bound, then the full ratio obeys it.
The two sums over paired terms are twice the original sector sums. -/
theorem pairedSectorRatio_lowerBound (Z N : (ℤ × ℤ) → ℝ) {r : ℝ}
    (hZ : Summable Z) (hN : Summable N)
    (hden : 0 < ∑' w, Z w)
    (hpair : ∀ w, r * (Z w + Z (-w)) ≤ N w + N (-w)) :
    r ≤ (∑' w, N w) / (∑' w, Z w) := by
  have hZpair : Summable (fun w : ℤ × ℤ => Z w + Z (-w)) :=
    hZ.add (hZ.comp_injective (Equiv.neg (ℤ × ℤ)).injective)
  have hNpair : Summable (fun w : ℤ × ℤ => N w + N (-w)) :=
    hN.add (hN.comp_injective (Equiv.neg (ℤ × ℤ)).injective)
  have hpairSum := sectorSums_lowerBound
    (fun w : ℤ × ℤ => Z w + Z (-w))
    (fun w : ℤ × ℤ => N w + N (-w)) hZpair hNpair hpair
  have hZneg : (∑' w : ℤ × ℤ, Z (-w)) = ∑' w, Z w := by
    rw [← (Equiv.neg (ℤ × ℤ)).tsum_eq]
    simp [Equiv.neg]
  have hNneg : (∑' w : ℤ × ℤ, N (-w)) = ∑' w, N w := by
    rw [← (Equiv.neg (ℤ × ℤ)).tsum_eq]
    simp [Equiv.neg]
  have hZpairSum : (∑' w : ℤ × ℤ, (Z w + Z (-w))) =
      2 * (∑' w : ℤ × ℤ, Z w) := by
    calc
      _ = (∑' w : ℤ × ℤ, Z w) + (∑' w : ℤ × ℤ, Z (-w)) := by
        simpa [Equiv.neg] using
          (hZ.tsum_add (hZ.comp_injective (Equiv.neg (ℤ × ℤ)).injective))
      _ = _ := by rw [hZneg]; ring
  have hNpairSum : (∑' w : ℤ × ℤ, (N w + N (-w))) =
      2 * (∑' w : ℤ × ℤ, N w) := by
    calc
      _ = (∑' w : ℤ × ℤ, N w) + (∑' w : ℤ × ℤ, N (-w)) := by
        simpa [Equiv.neg] using
          (hN.tsum_add (hN.comp_injective (Equiv.neg (ℤ × ℤ)).injective))
      _ = _ := by rw [hNneg]; ring
  rw [hZpairSum, hNpairSum] at hpairSum
  have hscaled : r * (∑' w : ℤ × ℤ, Z w) ≤ (∑' w : ℤ × ℤ, N w) := by nlinarith
  exact (le_div_iff₀ hden).2 hscaled

end FroehlichSpencer.BKT.Rotator.Periodic

end
