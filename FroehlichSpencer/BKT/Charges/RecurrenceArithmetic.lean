/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Arithmetic for the KP §4.1 scale recurrence

For the reviewed choice `α = 7/4` and `M = 2^16`, the cutoff is
`b = α + 3 + log₂ M = 83/4`. Thus the total auxiliary iterate is the integer
floor `γ(q) = ⌊(4q - 83)/7⌋`. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The inverse contraction ratio `α⁻¹` for the fixed value `α = 7/4`. -/
noncomputable def recurrenceRatio : ℝ := 4 / 7

/-- The exact fixed cutoff `b = 7/4 + 3 + log₂(2^16) = 83/4`. -/
noncomputable def recurrenceCutoff : ℝ := 83 / 4


noncomputable def recurrenceThreshold : ℝ := 203 / 4

/-- The summability exponent `p = log_(7/4)(2) = 1/log₂(7/4)`. -/
noncomputable def recurrenceSeriesExponent : ℝ := Real.logb (7 / 4 : ℝ) 2

/-- The `p`-series tail term after shifting the natural index so that its
corresponding scale is at least `K*=203/4`. -/
noncomputable def recurrenceTailTerm (n : ℕ) : ℝ :=
  (recurrenceThreshold / ((n : ℝ) + 51)) ^ recurrenceSeriesExponent

/-- The explicit first-term constant from the boundary-shell estimate, with natural scales
`k≥51` represented by `k=n+51`. -/
noncomputable def recurrenceFirstTermConstant : ℝ :=
  51 + 2 * ∑' n : ℕ, recurrenceTailTerm n

/-- The exact coefficient contributed by the regrouped separated terms. -/
noncomputable def recurrenceSeparatedCoefficient : ℝ := 196 / 3

/-- The explicit P2.1 upper-bound constant obtained from the two summed
recurrence contributions. -/
noncomputable def recurrenceP21Constant : ℝ :=
  recurrenceFirstTermConstant + recurrenceSeparatedCoefficient

/-- The total integer-valued extension of the scale map, including inputs
below the recurrence cutoff. -/
noncomputable def recurrenceGamma (q : ℤ) : ℤ :=
  ⌊(4 / 7 : ℝ) * (q : ℝ) - 83 / 7⌋

/-- The `m`-fold total iterate of `recurrenceGamma`. -/
noncomputable def recurrenceIterate : ℕ → ℤ → ℤ
  | 0, q => q
  | m + 1, q => recurrenceIterate m (recurrenceGamma q)

/-- The affine upper bound for the `m`-fold iterate. -/
noncomputable def recurrencePowerSum (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, (4 / 7 : ℝ) ^ j

/-- The affine upper bound for the `m`-fold iterate. -/
noncomputable def recurrenceUpper (m : ℕ) (q : ℤ) : ℝ :=
  (4 / 7 : ℝ) ^ m * (q : ℝ) - (83 / 7 : ℝ) * recurrencePowerSum m

/-- The affine lower bound retaining every floor error in the iteration. -/
noncomputable def recurrenceLower (m : ℕ) (q : ℤ) : ℝ :=
  recurrenceUpper m q - recurrencePowerSum m

/-- The real lower endpoint for the integer inputs whose `m`-th iterate has a
specified value. -/
noncomputable def recurrencePreimageLowerReal (m : ℕ) (j : ℤ) : ℝ :=
  (7 / 4 : ℝ) ^ m * ((j : ℝ) + (83 / 7 : ℝ) * recurrencePowerSum m)

/-- The real upper endpoint for the integer inputs whose `m`-th iterate has a
specified value. -/
noncomputable def recurrencePreimageUpperReal (m : ℕ) (j : ℤ) : ℝ :=
  (7 / 4 : ℝ) ^ m * ((j : ℝ) + (90 / 7 : ℝ) * recurrencePowerSum m)

/-- The least integer allowed by the affine lower bound for an iterate
preimage. -/
noncomputable def recurrencePreimageLower (m : ℕ) (j : ℤ) : ℤ :=
  ⌈recurrencePreimageLowerReal m j⌉

/-- The greatest integer allowed by the affine upper bound for an iterate
preimage. -/
noncomputable def recurrencePreimageUpper (m : ℕ) (j : ℤ) : ℤ :=
  ⌊recurrencePreimageUpperReal m j⌋

/-- One application of the total map differs from its affine formula by at
most one unit, with exact constants. -/
theorem recurrenceGamma_bounds (q : ℤ) :
    (4 / 7 : ℝ) * (q : ℝ) - 83 / 7 - 1 ≤ (recurrenceGamma q : ℝ) ∧
      (recurrenceGamma q : ℝ) ≤ (4 / 7 : ℝ) * (q : ℝ) - 83 / 7 := by
  constructor
  · exact (Int.sub_one_lt_floor _).le
  · exact Int.floor_le _

private theorem recurrencePowerSum_add_last (m : ℕ) :
    recurrencePowerSum (m + 1) = recurrencePowerSum m + (4 / 7 : ℝ) ^ m := by
  simp [recurrencePowerSum, Finset.sum_range_succ]

private theorem recurrencePowerSum_eq (m : ℕ) :
    recurrencePowerSum m = (1 - (4 / 7 : ℝ) ^ m) / (1 - 4 / 7) := by
  induction m with
  | zero => simp [recurrencePowerSum]
  | succ m ih =>
      rw [recurrencePowerSum_add_last, ih, pow_succ]
      field_simp
      ring

/-- The total auxiliary iterate satisfies the full floor-error bounds (4.4).
The displayed sums are the expanded form of
`α⁻ᵐ k - b ∑_{j=1}^m α⁻ʲ - ∑_{j=0}^{m-1} α⁻ʲ ≤ γ^m(k) ≤
α⁻ᵐ k - b ∑_{j=1}^m α⁻ʲ`; the outer lower bound uses the exact constant
`(α+b)/(α-1)=30`. -/
theorem recurrenceIterate_bounds (m : ℕ) (q : ℤ) :
    recurrenceLower m q ≤ (recurrenceIterate m q : ℝ) ∧
      (recurrenceIterate m q : ℝ) ≤ recurrenceUpper m q := by
  induction m generalizing q with
  | zero =>
      simp [recurrenceLower, recurrenceUpper, recurrenceIterate,
        recurrencePowerSum]
  | succ m ih =>
      have hrpow : 0 ≤ (4 / 7 : ℝ) ^ m := by positivity
      have hfloor := recurrenceGamma_bounds q
      have hlow := mul_le_mul_of_nonneg_left hfloor.1 hrpow
      have hupp := mul_le_mul_of_nonneg_left hfloor.2 hrpow
      have hlowStep : recurrenceLower (m + 1) q ≤ recurrenceLower m (recurrenceGamma q) := by
        change (4 / 7 : ℝ) ^ (m + 1) * (q : ℝ) - (83 / 7 : ℝ) *
            recurrencePowerSum (m + 1) - recurrencePowerSum (m + 1) ≤
          (4 / 7 : ℝ) ^ m * (recurrenceGamma q : ℝ) -
            (83 / 7 : ℝ) * recurrencePowerSum m - recurrencePowerSum m
        rw [recurrencePowerSum_add_last, pow_succ]
        nlinarith only [hlow]
      have huppStep : recurrenceUpper m (recurrenceGamma q) ≤ recurrenceUpper (m + 1) q := by
        change (4 / 7 : ℝ) ^ m * (recurrenceGamma q : ℝ) -
            (83 / 7 : ℝ) * recurrencePowerSum m ≤
          (4 / 7 : ℝ) ^ (m + 1) * (q : ℝ) -
            (83 / 7 : ℝ) * recurrencePowerSum (m + 1)
        rw [recurrencePowerSum_add_last, pow_succ]
        nlinarith only [hupp]
      rw [recurrenceIterate]
      exact ⟨hlowStep.trans (ih (recurrenceGamma q)).1,
        ((ih (recurrenceGamma q)).2.trans huppStep)⟩

/-- The geometric sum of all propagated floor errors is bounded by `7/3`. -/
private theorem recurrencePowerSum_le (m : ℕ) : recurrencePowerSum m ≤ 7 / 3 := by
  rw [recurrencePowerSum_eq]
  have hp : 0 ≤ (4 / 7 : ℝ) ^ m := by positivity
  have hd : 0 < (1 - 4 / 7 : ℝ) := by norm_num
  rw [div_le_iff₀ hd]
  norm_num at hd ⊢

/-- Since `7/4<2`, the p-series exponent in the first recurrence term is
strictly larger than one. -/
theorem recurrenceSeriesExponent_gt_one : 1 < recurrenceSeriesExponent := by
  change 1 < Real.logb (7 / 4 : ℝ) 2
  exact (Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)).2 (by norm_num)

/-- The shifted p-series defining `recurrenceFirstTermConstant` converges. -/
theorem recurrenceTailTerm_summable : Summable recurrenceTailTerm := by
  have hp := recurrenceSeriesExponent_gt_one
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 51) ^ recurrenceSeriesExponent) := by
    have hs :=
      (Real.summable_one_div_nat_add_rpow (51 : ℝ) recurrenceSeriesExponent).2 hp
    have hpos (n : ℕ) : 0 < (n : ℝ) + 51 := by positivity
    convert hs using 1
    ext n
    rw [abs_of_pos (hpos n)]
  have hscale := Summable.mul_left (recurrenceThreshold ^ recurrenceSeriesExponent) hshift
  refine hscale.congr ?_
  intro n
  dsimp [recurrenceTailTerm]
  rw [Real.div_rpow (by norm_num [recurrenceThreshold]) (by positivity)]
  simp [div_eq_mul_inv]

/-- The lower estimate in (4.4), including its outer simplification with the
exact constant `(α+b)/(α-1)=30`. -/
theorem recurrenceIterate_outer_lower (m : ℕ) (q : ℤ) :
    (4 / 7 : ℝ) ^ m * (q : ℝ) - 30 ≤ (recurrenceIterate m q : ℝ) := by
  have hbounds := recurrenceIterate_bounds m q
  have hsum := recurrencePowerSum_le m
  have hsimple : (4 / 7 : ℝ) ^ m * (q : ℝ) - 30 ≤ recurrenceLower m q := by
    dsimp [recurrenceLower, recurrenceUpper, recurrencePowerSum] at hsum ⊢
    nlinarith only [hsum]
  exact hsimple.trans hbounds.1

/-- Above the integer cutoff `21`, one application of the total map is a
nonnegative integer strictly smaller than its input. -/
private theorem recurrenceGamma_shrinks_nat (k : ℕ) (hk : 21 ≤ k) :
    0 ≤ recurrenceGamma (k : ℤ) ∧ recurrenceGamma (k : ℤ) < (k : ℤ) := by
  have harg : 0 ≤ (4 / 7 : ℝ) * (k : ℝ) - 83 / 7 := by
    have hkReal : (21 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hmul : (4 / 7 : ℝ) * 21 ≤ (4 / 7 : ℝ) * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hkReal (by norm_num)
    norm_num at hmul ⊢
    nlinarith only [hkReal]
  have hnonneg : 0 ≤ recurrenceGamma (k : ℤ) := by
    change 0 ≤ ⌊(4 / 7 : ℝ) * (k : ℝ) - 83 / 7⌋
    exact Int.floor_nonneg.mpr harg
  have hupper := (recurrenceGamma_bounds (k : ℤ)).2
  have hlin : (4 / 7 : ℝ) * (k : ℝ) - 83 / 7 < (k : ℝ) := by
    have hkReal : (21 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkpos : 0 < (k : ℝ) := lt_of_lt_of_le (by norm_num) hkReal
    nlinarith only
  have hreal : (recurrenceGamma (k : ℤ) : ℝ) < (k : ℝ) := hupper.trans_lt hlin
  exact ⟨hnonneg, by exact_mod_cast hreal⟩

/-- The total iterate eventually exits the valid scale range. The strict
decrease on integer inputs at least `21` gives a well-founded descent. -/
private theorem exists_recurrenceIterate_below_nat (k : ℕ) :
    ∃ m, recurrenceIterate m (k : ℤ) < 21 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k < 21
      · have hkInt : (k : ℤ) < 21 := by exact_mod_cast hk
        exact ⟨0, by simpa [recurrenceIterate] using hkInt⟩
      · have hk21 : 21 ≤ k := by omega
        obtain ⟨hgamma_nonneg, hgamma_lt⟩ := recurrenceGamma_shrinks_nat k hk21
        have hgammaNat_lt : (recurrenceGamma (k : ℤ)).toNat < k := by
          have hltInt : ((recurrenceGamma (k : ℤ)).toNat : ℤ) < (k : ℤ) := by
            simpa [Int.toNat_of_nonneg hgamma_nonneg] using hgamma_lt
          exact_mod_cast hltInt
        obtain ⟨m, hm⟩ := ih (recurrenceGamma (k : ℤ)).toNat hgammaNat_lt
        refine ⟨m + 1, ?_⟩
        change recurrenceIterate m (recurrenceGamma (k : ℤ)) < 21
        have hcast : ((recurrenceGamma (k : ℤ)).toNat : ℤ) =
            recurrenceGamma (k : ℤ) := Int.toNat_of_nonneg hgamma_nonneg
        simpa [hcast] using hm

/-- Every integer input has a finite first-passage depth below the cutoff. -/
theorem exists_recurrenceIterate_below (q : ℤ) :
    ∃ m, recurrenceIterate m q < 21 := by
  by_cases hq : q < 21
  · exact ⟨0, by simpa [recurrenceIterate] using hq⟩
  · have hq_nonneg : 0 ≤ q := by omega
    obtain ⟨m, hm⟩ := exists_recurrenceIterate_below_nat q.toNat
    have hqcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq_nonneg
    exact ⟨m, by simpa [hqcast] using hm⟩

/-- The valid recurrence depth is the first iterate below the cutoff `b`.
Because the iterate is integer-valued, being below `b=83/4` is equivalent to
being below `21`. -/
noncomputable def recurrenceDepth (q : ℤ) : ℕ := by
  classical
  exact Nat.find (exists_recurrenceIterate_below q)

/-- The defining first-passage property of `recurrenceDepth`. -/
theorem recurrenceDepth_stops (q : ℤ) :
    recurrenceIterate (recurrenceDepth q) q < 21 := by
  change recurrenceIterate (Nat.find (exists_recurrenceIterate_below q)) q < 21
  exact Nat.find_spec (exists_recurrenceIterate_below q)

/-- The integer cutoff `21` is exactly the real source cutoff `b=83/4` on
integer-valued scales. -/
theorem recurrenceInteger_below_cutoff_iff (q : ℤ) :
    (q : ℝ) < recurrenceCutoff ↔ q < 21 := by
  constructor
  · intro h
    have hreal : (q : ℝ) < 21 := by
      have hcut : recurrenceCutoff < 21 := by norm_num [recurrenceCutoff]
      exact h.trans hcut
    exact_mod_cast hreal
  · intro h
    have h20 : q ≤ 20 := by omega
    have hreal : (q : ℝ) ≤ 20 := by exact_mod_cast h20
    have h20cut : (20 : ℝ) < recurrenceCutoff := by norm_num [recurrenceCutoff]
    exact hreal.trans_lt h20cut


theorem recurrenceDepth_stops_below_cutoff (q : ℤ) :
    (recurrenceIterate (recurrenceDepth q) q : ℝ) < recurrenceCutoff :=
  (recurrenceInteger_below_cutoff_iff _).2 (recurrenceDepth_stops q)

/-- No earlier iterate has crossed below the cutoff. -/
theorem recurrenceDepth_valid_before (q : ℤ) {m : ℕ} (hm : m < recurrenceDepth q) :
    21 ≤ recurrenceIterate m q := by
  by_contra h
  have hstop : recurrenceIterate m q < 21 := by omega
  have hmin := Nat.find_min' (exists_recurrenceIterate_below q) hstop
  change recurrenceDepth q ≤ m at hmin
  omega

/-- Every input used before stopping satisfies the real source-side condition
`q ≥ b`. -/
theorem recurrenceDepth_valid_before_cutoff (q : ℤ) {m : ℕ}
    (hm : m < recurrenceDepth q) :
    recurrenceCutoff ≤ (recurrenceIterate m q : ℝ) := by
  have hvalid := recurrenceDepth_valid_before q hm
  have hreal : (21 : ℝ) ≤ (recurrenceIterate m q : ℝ) := by exact_mod_cast hvalid
  have hcut : recurrenceCutoff ≤ 21 := by norm_num [recurrenceCutoff]
  exact hcut.trans hreal

/-- Below the cutoff, the valid recurrence depth is zero. -/
theorem recurrenceDepth_eq_zero_of_below (q : ℤ) (hq : q < 21) :
    recurrenceDepth q = 0 := by
  have hle : recurrenceDepth q ≤ 0 :=
    Nat.find_min' (exists_recurrenceIterate_below q)
      (by simpa [recurrenceIterate] using hq)
  omega

/-- The valid depth is zero whenever the input is below the source cutoff. -/
theorem recurrenceDepth_eq_zero_of_below_cutoff (q : ℤ)
    (hq : (q : ℝ) < recurrenceCutoff) : recurrenceDepth q = 0 :=
  recurrenceDepth_eq_zero_of_below q
    ((recurrenceInteger_below_cutoff_iff q).1 hq)

/-- If `m` is no larger than the logarithmic stopping threshold, then the
`m`-th iterate is still at or above `b`. This is the scale-by-scale form of
the valid-depth estimate in (4.4). -/
private theorem recurrenceIterate_ge_cutoff_of_le_log (q : ℤ)
    (hq : recurrenceThreshold ≤ (q : ℝ)) {m : ℕ}
    (hm : m ≤ ⌊Real.logb (7 / 4 : ℝ) ((q : ℝ) / recurrenceThreshold)⌋₊) :
    recurrenceCutoff ≤ (recurrenceIterate m q : ℝ) := by
  have hKpos : 0 < recurrenceThreshold := by norm_num [recurrenceThreshold]
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le hKpos hq
  have hratio_pos : 0 < (q : ℝ) / recurrenceThreshold := div_pos hqpos hKpos
  have hratio_ge_one : 1 ≤ (q : ℝ) / recurrenceThreshold :=
    (le_div_iff₀ hKpos).2 (by simpa using hq)
  have hlog_nonneg : 0 ≤ Real.logb (7 / 4 : ℝ)
      ((q : ℝ) / recurrenceThreshold) := by
    exact Real.logb_nonneg (by norm_num) hratio_ge_one
  have hm_log : (m : ℝ) ≤ Real.logb (7 / 4 : ℝ)
      ((q : ℝ) / recurrenceThreshold) := by
    exact (Nat.le_floor_iff hlog_nonneg).1 hm
  have hpow : (7 / 4 : ℝ) ^ m ≤ (q : ℝ) / recurrenceThreshold := by
    have hpow' :=
      (Real.le_logb_iff_rpow_le (by norm_num) hratio_pos).1 hm_log
    simpa only [Real.rpow_natCast] using hpow'
  have hprod : (7 / 4 : ℝ) ^ m * recurrenceThreshold ≤ (q : ℝ) :=
    (le_div_iff₀ hKpos).1 hpow
  have hrpow : 0 ≤ (4 / 7 : ℝ) ^ m := by positivity
  have hinv : (4 / 7 : ℝ) ^ m * (7 / 4 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have hscaled : recurrenceThreshold ≤ (4 / 7 : ℝ) ^ m * (q : ℝ) := by
    calc
      recurrenceThreshold = 1 * recurrenceThreshold := by ring
      _ = ((4 / 7 : ℝ) ^ m * (7 / 4 : ℝ) ^ m) * recurrenceThreshold := by
        rw [← hinv]
      _ = (4 / 7 : ℝ) ^ m * ((7 / 4 : ℝ) ^ m * recurrenceThreshold) := by
        rw [mul_assoc]
      _ ≤ (4 / 7 : ℝ) ^ m * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hprod hrpow
  have houter := recurrenceIterate_outer_lower m q
  have hconst : recurrenceCutoff = recurrenceThreshold - 30 := by
    norm_num [recurrenceCutoff, recurrenceThreshold]
  rw [hconst]
  linarith only [hscaled, houter]

/-- The first-passage depth is at least
`floor(log_(7/4)(k/K*))`, where the exact threshold is `K*=203/4`. -/
theorem recurrenceDepth_ge_floor_log (q : ℤ)
    (hq : recurrenceThreshold ≤ (q : ℝ)) :
    ⌊Real.logb (7 / 4 : ℝ) ((q : ℝ) / recurrenceThreshold)⌋₊ ≤
      recurrenceDepth q := by
  by_contra h
  have hdepth : recurrenceDepth q <
      ⌊Real.logb (7 / 4 : ℝ) ((q : ℝ) / recurrenceThreshold)⌋₊ := by omega
  have hstill := recurrenceIterate_ge_cutoff_of_le_log q hq (Nat.le_of_lt hdepth)
  have hstop := recurrenceDepth_stops q
  have hstopReal : (recurrenceIterate (recurrenceDepth q) q : ℝ) < 21 := by
    exact_mod_cast hstop
  have hgt20 : (20 : ℤ) < recurrenceIterate (recurrenceDepth q) q := by
    exact_mod_cast (show (20 : ℝ) < (recurrenceIterate (recurrenceDepth q) q : ℝ) by
      norm_num [recurrenceCutoff] at hstill ⊢
      linarith only [hstill])
  omega

private theorem recurrenceHalf_rpow_logb (x : ℝ) (hx : 0 < x) :
    (1 / 2 : ℝ) ^ Real.logb (7 / 4 : ℝ) x =
      x ^ (-recurrenceSeriesExponent) := by
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hx]
  apply congrArg Real.exp
  simp only [Real.logb, recurrenceSeriesExponent]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 7 / 4))]

/-- Above the threshold, the first-term weight is bounded by twice the
explicit shifted p-series term. -/
theorem recurrenceWeight_le_tail (k : ℕ) (hk : 51 ≤ k) :
    (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) ≤
      2 * recurrenceTailTerm (k - 51) := by
  have hkThreshold : recurrenceThreshold ≤ (k : ℝ) := by
    have hkReal : (51 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    norm_num [recurrenceThreshold]
    linarith only [hkReal]
  have hdepth := recurrenceDepth_ge_floor_log (k : ℤ) hkThreshold
  let x := Real.logb (7 / 4 : ℝ) ((k : ℝ) / recurrenceThreshold)
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    apply Real.logb_nonneg (by norm_num)
    exact (le_div_iff₀ (by norm_num [recurrenceThreshold])).2 (by linarith only [hkThreshold])
  have hfloor : x - 1 ≤ (Nat.floor x : ℝ) := by
    have hlt := Nat.lt_floor_add_one x
    linarith only [hlt]
  have hdepthReal : (Nat.floor x : ℝ) ≤ (recurrenceDepth (k : ℤ) : ℝ) := by
    exact_mod_cast hdepth
  have hpower : (1 / 2 : ℝ) ^ (recurrenceDepth (k : ℤ) : ℝ) ≤
      (1 / 2 : ℝ) ^ (x - 1) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (hfloor.trans hdepthReal)
  have hkpos : 0 < (k : ℝ) := by
    have hkReal : (51 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith only [hkReal]
  have hden : ((k - 51 : ℕ) : ℝ) + 51 = (k : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hk
  calc
    (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) =
        (1 / 2 : ℝ) ^ (recurrenceDepth (k : ℤ) : ℝ) := by
          rw [Real.rpow_natCast]
    _ ≤ (1 / 2 : ℝ) ^ (x - 1) := hpower
    _ = (1 / 2 : ℝ) ^ x / (1 / 2 : ℝ) ^ 1 :=
      Real.rpow_sub (by norm_num) x 1
    _ = 2 * (1 / 2 : ℝ) ^ x := by
      field_simp
      ring
    _ = 2 * ((k : ℝ) / recurrenceThreshold) ^
        (-recurrenceSeriesExponent) := by
          congr 1
          dsimp [x]
          exact recurrenceHalf_rpow_logb _ (div_pos hkpos (by norm_num [recurrenceThreshold]))
    _ = 2 * (recurrenceThreshold / (k : ℝ)) ^ recurrenceSeriesExponent := by
          congr 1
          rw [Real.rpow_neg_eq_inv_rpow]
          rw [show ((k : ℝ) / recurrenceThreshold)⁻¹ =
            recurrenceThreshold / (k : ℝ) by field_simp]
    _ = 2 * recurrenceTailTerm (k - 51) := by
          dsimp [recurrenceTailTerm]
          rw [hden]

theorem recurrenceTailTerm_nonneg (n : ℕ) :
    0 ≤ recurrenceTailTerm n := by
  dsimp [recurrenceTailTerm]
  exact Real.rpow_nonneg (div_nonneg (by norm_num [recurrenceThreshold]) (by positivity)) _

/-- Summing the terminal first-term weights over any finite range gives the
explicit initial range plus the convergent p-series tail in  -/
theorem recurrenceFirstTerm_sum_bound (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ)) ≤ recurrenceFirstTermConstant := by
  by_cases hn : 51 ≤ n + 1
  · have hsplit := Finset.sum_range_add_sum_Ico
      (fun k : ℕ => (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ)) hn
    have hinitial :
        (∑ k ∈ Finset.range 51, (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ)) ≤ 51 := by
      calc
        _ ≤ ∑ _k ∈ Finset.range 51, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact pow_le_one₀ (by norm_num) (by norm_num)
        _ = 51 := by simp
    have htailPointwise :
        (∑ k ∈ Finset.Ico 51 (n + 1),
          (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ)) ≤
        ∑ k ∈ Finset.Ico 51 (n + 1), 2 * recurrenceTailTerm (k - 51) := by
      apply Finset.sum_le_sum
      intro k hk
      exact recurrenceWeight_le_tail k (Finset.mem_Ico.mp hk).1
    have hshift :
        (∑ k ∈ Finset.Ico 51 (n + 1), 2 * recurrenceTailTerm (k - 51)) =
          ∑ i ∈ Finset.range (n + 1 - 51), 2 * recurrenceTailTerm i := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp
    have htailSeries :
        (∑ i ∈ Finset.range (n + 1 - 51), 2 * recurrenceTailTerm i) ≤
          2 * ∑' i : ℕ, recurrenceTailTerm i := by
      calc
        _ ≤ ∑' i : ℕ, 2 * recurrenceTailTerm i :=
          Summable.sum_le_tsum _ (by
            intro i hi
            exact mul_nonneg (by norm_num) (recurrenceTailTerm_nonneg i))
            (Summable.mul_left 2 recurrenceTailTerm_summable)
        _ = 2 * ∑' i : ℕ, recurrenceTailTerm i := tsum_mul_left
    rw [← hsplit]
    calc
      _ ≤ 51 + ∑ k ∈ Finset.Ico 51 (n + 1),
          2 * recurrenceTailTerm (k - 51) := add_le_add hinitial htailPointwise
      _ = 51 + ∑ i ∈ Finset.range (n + 1 - 51), 2 * recurrenceTailTerm i := by
        rw [hshift]
      _ ≤ 51 + 2 * ∑' i : ℕ, recurrenceTailTerm i := by linarith only [htailSeries]
      _ = recurrenceFirstTermConstant := by
        rfl
  · have hnlt : n + 1 < 51 := by omega
    have hfinite :
        (∑ k ∈ Finset.range (n + 1),
          (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ)) ≤ n + 1 := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (n + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact pow_le_one₀ (by norm_num) (by norm_num)
        _ = n + 1 := by simp
    have hconst : (n + 1 : ℝ) ≤ recurrenceFirstTermConstant := by
      dsimp [recurrenceFirstTermConstant]
      have hsum : 0 ≤ ∑' i : ℕ, recurrenceTailTerm i :=
        tsum_nonneg recurrenceTailTerm_nonneg
      have hnreal : (n + 1 : ℝ) ≤ 51 := by exact_mod_cast (Nat.le_of_lt hnlt)
      linarith only [hsum, hnreal]
    exact hfinite.trans hconst


theorem recurrenceIterate_preimage_count (m : ℕ) (j : ℤ) :
    Set.Finite {q : ℤ | recurrenceIterate m q = j} ∧
      ((Set.ncard {q : ℤ | recurrenceIterate m q = j} : ℝ) ≤
        (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ m) := by
  let P : Set ℤ := {q : ℤ | recurrenceIterate m q = j}
  let lo : ℤ := recurrencePreimageLower m j
  let hi : ℤ := recurrencePreimageUpper m j
  have hrpow : 0 < (4 / 7 : ℝ) ^ m := by positivity
  have halpha : 0 < (7 / 4 : ℝ) ^ m := by positivity
  have hinv : (4 / 7 : ℝ) ^ m * (7 / 4 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have hinv' : (7 / 4 : ℝ) ^ m * (4 / 7 : ℝ) ^ m = 1 := by
    rw [mul_comm, hinv]
  have hsub : P ⊆ Set.Icc lo hi := by
    intro q hq
    have hbounds := recurrenceIterate_bounds m q
    have heq : (recurrenceIterate m q : ℝ) = (j : ℝ) := congrArg Int.cast hq
    have hqLower : recurrencePreimageLowerReal m j ≤ (q : ℝ) := by
      have hraw : (j : ℝ) + (83 / 7 : ℝ) * recurrencePowerSum m ≤
          (4 / 7 : ℝ) ^ m * (q : ℝ) := by
        rw [← heq]
        dsimp [recurrenceUpper] at hbounds
        linarith only [hbounds.2]
      calc
        recurrencePreimageLowerReal m j =
            (7 / 4 : ℝ) ^ m *
              ((j : ℝ) + (83 / 7 : ℝ) * recurrencePowerSum m) := rfl
        _ ≤ (7 / 4 : ℝ) ^ m * ((4 / 7 : ℝ) ^ m * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hraw (le_of_lt halpha)
        _ = (q : ℝ) := by rw [← mul_assoc, hinv', one_mul]
    have hqUpper : (q : ℝ) ≤ recurrencePreimageUpperReal m j := by
      have hraw : (4 / 7 : ℝ) ^ m * (q : ℝ) ≤
          (j : ℝ) + (90 / 7 : ℝ) * recurrencePowerSum m := by
        rw [← heq]
        dsimp [recurrenceLower, recurrenceUpper] at hbounds
        linarith only [hbounds.1]
      calc
        (q : ℝ) = (7 / 4 : ℝ) ^ m *
            ((4 / 7 : ℝ) ^ m * (q : ℝ)) := by rw [← mul_assoc, hinv', one_mul]
        _ ≤ (7 / 4 : ℝ) ^ m *
            ((j : ℝ) + (90 / 7 : ℝ) * recurrencePowerSum m) :=
          mul_le_mul_of_nonneg_left hraw (le_of_lt halpha)
        _ = recurrencePreimageUpperReal m j := rfl
    change lo ≤ q ∧ q ≤ hi
    constructor
    · exact Int.ceil_le.mpr hqLower
    · exact Int.le_floor.mpr hqUpper
  have hfinite : P.Finite := (Set.finite_Icc lo hi).subset hsub
  have hsum_nonneg : 0 ≤ recurrencePowerSum m := by
    apply Finset.sum_nonneg
    intro i hi
    positivity
  have hwidth : recurrencePreimageUpperReal m j -
      recurrencePreimageLowerReal m j = (7 / 4 : ℝ) ^ m * recurrencePowerSum m := by
    simp [recurrencePreimageUpperReal, recurrencePreimageLowerReal]
    ring
  have hA_le_B : recurrencePreimageLowerReal m j ≤ recurrencePreimageUpperReal m j := by
    rw [← sub_nonneg, hwidth]
    positivity
  have hlohi : lo ≤ hi + 1 := by
    change ⌈recurrencePreimageLowerReal m j⌉ ≤
      ⌊recurrencePreimageUpperReal m j⌋ + 1
    have hfloor : ⌊recurrencePreimageLowerReal m j⌋ ≤
        ⌊recurrencePreimageUpperReal m j⌋ := Int.floor_mono hA_le_B
    exact (Int.ceil_le_floor_add_one _).trans (by omega)
  have hcardInt : ((Finset.Icc lo hi).card : ℤ) = hi + 1 - lo :=
    Int.card_Icc_of_le lo hi hlohi
  have hloReal : recurrencePreimageLowerReal m j ≤ (lo : ℝ) := by
    change recurrencePreimageLowerReal m j ≤ (⌈recurrencePreimageLowerReal m j⌉ : ℝ)
    exact Int.le_ceil _
  have hhiReal : (hi : ℝ) ≤ recurrencePreimageUpperReal m j := by
    change (⌊recurrencePreimageUpperReal m j⌋ : ℝ) ≤ recurrencePreimageUpperReal m j
    exact Int.floor_le _
  have hcardInterval : ((Finset.Icc lo hi).card : ℝ) ≤
      recurrencePreimageUpperReal m j - recurrencePreimageLowerReal m j + 1 := by
    have hcardReal : ((Finset.Icc lo hi).card : ℝ) = (hi : ℝ) + 1 - (lo : ℝ) := by
      exact_mod_cast hcardInt
    rw [hcardReal]
    linarith only [hloReal, hhiReal]
  have hsumBound := recurrencePowerSum_le m
  have halphaOne : 1 ≤ (7 / 4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hintervalBound : ((Finset.Icc lo hi).card : ℝ) ≤
      (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ m := by
    have hwidthBound : recurrencePreimageUpperReal m j -
      recurrencePreimageLowerReal m j ≤
          (7 / 3 : ℝ) * (7 / 4 : ℝ) ^ m := by
      rw [hwidth]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left hsumBound (le_of_lt halpha))
    have hconst : (7 / 3 : ℝ) * (7 / 4 : ℝ) ^ m + 1 ≤
        (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ m := by
      nlinarith only [halphaOne]
    linarith only [hcardInterval, halphaOne, hwidthBound]
  have hPcard : P.ncard ≤ (Finset.Icc lo hi).card := by
    rw [← Set.ncard_Icc]
    exact Set.ncard_le_ncard hsub
  have hPcardReal : (P.ncard : ℝ) ≤ (Finset.Icc lo hi).card := by
    exact_mod_cast hPcard
  refine ⟨hfinite, ?_⟩
  exact le_trans hPcardReal hintervalBound

private theorem recurrenceIterate_fiber_card_bound (m : ℕ) (j : ℤ)
    (s : Finset ℕ) :
    (((s.filter (fun k : ℕ => recurrenceIterate (m + 1) (k : ℤ) = j)).card : ℕ) : ℝ) ≤
      (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) := by
  let fiber := s.filter (fun k : ℕ => recurrenceIterate (m + 1) (k : ℤ) = j)
  let castFiber := fiber.image fun k : ℕ => (k : ℤ)
  have hinj : Set.InjOn (fun k : ℕ => (k : ℤ)) (fiber : Set ℕ) := by
    intro a ha b hb hab
    exact Int.natCast_inj.mp hab
  have hcastcard : castFiber.card = fiber.card := by
    exact Finset.card_image_of_injOn hinj
  have hsubset : (castFiber : Set ℤ) ⊆ {q | recurrenceIterate (m + 1) q = j} := by
    intro q hq
    rcases Finset.mem_coe.mp hq with hq
    rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
    exact (Finset.mem_filter.mp hk).2
  have hpre := recurrenceIterate_preimage_count (m + 1) j
  have hcard : castFiber.card ≤ Set.ncard {q | recurrenceIterate (m + 1) q = j} := by
    have h := Set.ncard_le_ncard hsubset hpre.1
    simpa [Set.ncard_coe_finset] using h
  have hcardReal : (fiber.card : ℝ) ≤
      (Set.ncard {q | recurrenceIterate (m + 1) q = j} : ℝ) := by
    rw [← hcastcard]
    exact_mod_cast hcard
  exact hcardReal.trans hpre.2

/-- For a fixed iterate layer, regrouping by its integer image and applying
the preimage-count estimate bounds the layer by `(14/3) α^(m+1)` times the
total separated weight. -/
theorem recurrenceIterate_layer_sum_bound (m n : ℕ) (f : ℤ → ℝ)
    (hf : Summable f) (hf_nonneg : ∀ j, 0 ≤ f j) :
    (∑ k ∈ Finset.range (n + 1), f (recurrenceIterate (m + 1) (k : ℤ))) ≤
      (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℤ, f j := by
  let s := Finset.range (n + 1)
  let g : ℕ → ℤ := fun k => recurrenceIterate (m + 1) (k : ℤ)
  let t := s.image g
  have hmaps : ∀ k ∈ s, g k ∈ t := fun k hk => Finset.mem_image_of_mem g hk
  have hsum :
      (∑ j ∈ t, ∑ k ∈ s with g k = j, f (g k)) ≤
        ((14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1)) * ∑ j ∈ t, f j := by
    calc
      _ ≤ ∑ j ∈ t, ((14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1)) * f j := by
        apply Finset.sum_le_sum
        intro j hj
        let fiber := s.filter fun k => g k = j
        have hfiber :
            (∑ k ∈ s with g k = j, f (g k)) = (fiber.card : ℝ) * f j := by
          calc
            _ = ∑ k ∈ fiber, f j := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [(Finset.mem_filter.mp hk).2]
            _ = (fiber.card : ℝ) * f j := by
              simp [fiber, Finset.sum_const, nsmul_eq_mul]
        rw [hfiber]
        have hcard := recurrenceIterate_fiber_card_bound m j s
        have hcard' : (fiber.card : ℝ) ≤ (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) := by
          simpa [fiber, s, g] using hcard
        exact mul_le_mul_of_nonneg_right hcard' (hf_nonneg j)
      _ = ((14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1)) * ∑ j ∈ t, f j := by
        rw [← Finset.mul_sum]
  calc
    _ = ∑ j ∈ t, ∑ k ∈ s with g k = j, f (g k) := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps (fun k => f (g k))).symm
    _ ≤ ((14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1)) * ∑ j ∈ t, f j := hsum
    _ ≤ ((14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1)) * ∑' j : ℤ, f j := by
      apply mul_le_mul_of_nonneg_left
      · exact Summable.sum_le_tsum t (fun j hj => hf_nonneg j) hf
      · positivity

/-- Exact value of the separated-term geometric coefficient at `α=7/4`. -/
theorem recurrenceSeparatedCoefficient_eq :
    (14 / 3 : ℝ) * (7 / 4 : ℝ) * ∑' m : ℕ, (7 / 8 : ℝ) ^ m =
      recurrenceSeparatedCoefficient := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num [recurrenceSeparatedCoefficient]

private theorem recurrenceHalfAlpha_power (m : ℕ) :
    (1 / 2 : ℝ) ^ m * (7 / 4 : ℝ) ^ (m + 1) =
      (7 / 4 : ℝ) * (7 / 8 : ℝ) ^ m := by
  rw [pow_succ]
  calc
    (1 / 2 : ℝ) ^ m * ((7 / 4 : ℝ) ^ m * (7 / 4 : ℝ)) =
        ((1 / 2 : ℝ) ^ m * (7 / 4 : ℝ) ^ m) * (7 / 4 : ℝ) := by ring
    _ = ((1 / 2 : ℝ) * (7 / 4 : ℝ)) ^ m * (7 / 4 : ℝ) := by rw [← mul_pow]
    _ = (7 / 4 : ℝ) * (7 / 8 : ℝ) ^ m := by norm_num; ring

/-- Every individual stopping depth in a finite range is bounded by the sum
of all depths in that range. -/
theorem recurrenceDepth_le_sum_on_range (n k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
    recurrenceDepth (k : ℤ) ≤
      ∑ i ∈ Finset.range (n + 1), recurrenceDepth (i : ℤ) := by
  exact Finset.single_le_sum
    (s := Finset.range (n + 1)) (f := fun i : ℕ => recurrenceDepth (i : ℤ))
    (fun i hi => Nat.zero_le _) hk

/-- At every valid scale, the stopping depth drops by exactly one after one
application of `γ`. -/
theorem recurrenceDepth_gamma (q : ℤ) (hq : 21 ≤ q) :
    recurrenceDepth q = recurrenceDepth (recurrenceGamma q) + 1 := by
  let d := recurrenceDepth q
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hstop := recurrenceDepth_stops q
    have hqstop : q < 21 := by simpa [d, hd0, recurrenceIterate] using hstop
    omega
  have hdeq : d - 1 + 1 = d := by omega
  have hgammaStop : recurrenceIterate (d - 1) (recurrenceGamma q) < 21 := by
    have hstop := recurrenceDepth_stops q
    change recurrenceIterate d q < 21 at hstop
    rw [← hdeq] at hstop
    simpa [recurrenceIterate] using hstop
  have hdepthLe : recurrenceDepth (recurrenceGamma q) ≤ d - 1 := by
    exact Nat.find_min' (exists_recurrenceIterate_below (recurrenceGamma q)) hgammaStop
  have hstopGamma := recurrenceDepth_stops (recurrenceGamma q)
  have hqStop :
      recurrenceIterate (recurrenceDepth (recurrenceGamma q) + 1) q < 21 := by
    simpa [recurrenceIterate] using hstopGamma
  have hdepthGe : d ≤ recurrenceDepth (recurrenceGamma q) + 1 := by
    change recurrenceDepth q ≤ recurrenceDepth (recurrenceGamma q) + 1
    exact Nat.find_min' (exists_recurrenceIterate_below q) hqStop
  omega

private theorem recurrenceSeparatedSum_succ (d : ℕ) (q : ℤ) (f : ℤ → ℝ) :
    (∑ m ∈ Finset.range (d + 1),
      (1 / 2 : ℝ) ^ m * f (recurrenceIterate (m + 1) q)) =
      f (recurrenceGamma q) + (1 / 2 : ℝ) *
        ∑ m ∈ Finset.range d,
          (1 / 2 : ℝ) ^ m * f (recurrenceIterate (m + 1) (recurrenceGamma q)) := by
  rw [Finset.sum_range_succ']
  calc
    _ = (∑ m ∈ Finset.range d,
          (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ m *
            f (recurrenceIterate (m + 1) (recurrenceGamma q)))) +
          f (recurrenceGamma q) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro m hm
        simp [recurrenceIterate, pow_succ]
        ring
      · simp [recurrenceIterate]
    _ = f (recurrenceGamma q) + (1 / 2 : ℝ) *
          ∑ m ∈ Finset.range d,
            (1 / 2 : ℝ) ^ m * f (recurrenceIterate (m + 1) (recurrenceGamma q)) := by
      rw [← Finset.mul_sum]
      ring

/-- Repeated application of a one-step cover recurrence gives its terminal
term plus the finite separated-term expansion. This helper takes the actual
per-step inequalities on valid iterates as input. -/
theorem recurrenceCover_iterate_expansion (cover sep : ℤ → ℝ)
    (hstep : ∀ q m, m < recurrenceDepth q →
      cover (recurrenceIterate m q) ≤
        (1 / 2 : ℝ) * cover (recurrenceIterate (m + 1) q) +
          sep (recurrenceIterate (m + 1) q)) (q : ℤ) :
    cover q ≤ (1 / 2 : ℝ) ^ recurrenceDepth q *
        cover (recurrenceIterate (recurrenceDepth q) q) +
      ∑ m ∈ Finset.range (recurrenceDepth q),
        (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) q) := by
  let d := recurrenceDepth q
  have aux : ∀ d q, recurrenceDepth q = d →
      cover q ≤ (1 / 2 : ℝ) ^ d * cover (recurrenceIterate d q) +
        ∑ m ∈ Finset.range d,
          (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) q) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro q hd
        by_cases hd0 : d = 0
        · subst d
          simp [hd0, recurrenceIterate]
        · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
          have hvalidIter := recurrenceDepth_valid_before q (by rw [hd]; exact hdpos)
          have hvalid : 21 ≤ q := by
            simpa [recurrenceIterate] using hvalidIter
          have hdrop := recurrenceDepth_gamma q hvalid
          have hgammaDepth : recurrenceDepth (recurrenceGamma q) + 1 = d := by
            rw [hd] at hdrop
            exact hdrop.symm
          have hgammaDepthLt : recurrenceDepth (recurrenceGamma q) < d := by omega
          have hgamma := ih (recurrenceDepth (recurrenceGamma q)) hgammaDepthLt
            (recurrenceGamma q) rfl
          have hlocal := hstep q 0 (by rw [hd]; exact hdpos)
          have hsum := recurrenceSeparatedSum_succ
            (recurrenceDepth (recurrenceGamma q)) q sep
          have hterminal :
              recurrenceIterate (recurrenceDepth (recurrenceGamma q))
                  (recurrenceGamma q) = recurrenceIterate d q := by
            calc
              _ = recurrenceIterate
                    (recurrenceDepth (recurrenceGamma q) + 1) q := by
                      simp [recurrenceIterate]
              _ = recurrenceIterate d q := by rw [hgammaDepth]
          rw [hterminal] at hgamma
          have hcoefficient :
              (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ recurrenceDepth (recurrenceGamma q) =
                (1 / 2 : ℝ) ^ d := by
            rw [← hgammaDepth, pow_succ]
            ring
          rw [hgammaDepth] at hsum
          have heq : recurrenceDepth (recurrenceGamma q) = d - 1 := by omega
          rw [heq] at hsum
          have hcoefficient' :
              (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (d - 1) = (1 / 2 : ℝ) ^ d := by
            rw [← heq]
            exact hcoefficient
          rw [heq] at hgamma
          calc
            cover q ≤
                (1 / 2 : ℝ) * cover (recurrenceGamma q) +
                  sep (recurrenceGamma q) := by
                    simpa [recurrenceIterate] using hlocal
            _ ≤ (1 / 2 : ℝ) *
                  ((1 / 2 : ℝ) ^ (d - 1) * cover (recurrenceIterate d q) +
                    ∑ m ∈ Finset.range (d - 1),
                      (1 / 2 : ℝ) ^ m * sep
                        (recurrenceIterate (m + 1) (recurrenceGamma q))) +
                  sep (recurrenceGamma q) := by
                    apply add_le_add
                    · exact mul_le_mul_of_nonneg_left hgamma
                        (by norm_num : (0 : ℝ) ≤ 1 / 2)
                    · exact le_rfl
            _ = (1 / 2 : ℝ) ^ d * cover (recurrenceIterate d q) +
                  ∑ m ∈ Finset.range d,
                    (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) q) := by
                    rw [mul_add]
                    calc
                      _ = ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (d - 1)) *
                            cover (recurrenceIterate d q) +
                            (sep (recurrenceGamma q) +
                              (1 / 2 : ℝ) *
                                ∑ m ∈ Finset.range (d - 1),
                                  (1 / 2 : ℝ) ^ m *
                                    sep (recurrenceIterate (m + 1) (recurrenceGamma q))) := by ring
                      _ = ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (d - 1)) *
                            cover (recurrenceIterate d q) +
                            ∑ m ∈ Finset.range d,
                              (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) q) := by
                                rw [← hsum]
                      _ = _ := by rw [hcoefficient']
  have hresult := aux d q rfl
  simpa [d] using hresult

/-- The full finite sum of valid separated terms, with every iterate index
`m < recurrenceDepth(k)` retained, is bounded by the exact geometric
coefficient `196/3` times the total separated weight. The finite horizon is
the sum of the stopping depths, so it contains every valid term. -/
theorem recurrenceValidSeparated_sum_bound (n : ℕ) (f : ℤ → ℝ)
    (hf : Summable f) (hf_nonneg : ∀ j, 0 ≤ f j) :
    (∑ m ∈ Finset.range (∑ k ∈ Finset.range (n + 1), recurrenceDepth (k : ℤ)),
      ∑ k ∈ Finset.range (n + 1),
        if m < recurrenceDepth (k : ℤ) then
          (1 / 2 : ℝ) ^ m * f (recurrenceIterate (m + 1) (k : ℤ)) else 0) ≤
      recurrenceSeparatedCoefficient * ∑' j : ℤ, f j := by
  let T := ∑ k ∈ Finset.range (n + 1), recurrenceDepth (k : ℤ)
  let c : ℝ := (14 / 3 : ℝ) * (7 / 4 : ℝ)
  have hfT : 0 ≤ ∑' j : ℤ, f j := tsum_nonneg hf_nonneg
  have hlayer (m : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        if m < recurrenceDepth (k : ℤ) then
          (1 / 2 : ℝ) ^ m * f (recurrenceIterate (m + 1) (k : ℤ)) else 0) ≤
        c * (7 / 8 : ℝ) ^ m * ∑' j : ℤ, f j := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n + 1),
          (1 / 2 : ℝ) ^ m * f (recurrenceIterate (m + 1) (k : ℤ)) := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hvalid : m < recurrenceDepth (k : ℤ)
        · simp [hvalid]
        · simp only [hvalid, ↓reduceIte]
          exact mul_nonneg (pow_nonneg (by norm_num) m) (hf_nonneg _)
      _ = (1 / 2 : ℝ) ^ m *
          ∑ k ∈ Finset.range (n + 1),
            f (recurrenceIterate (m + 1) (k : ℤ)) := by
        rw [Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ m *
          ((14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℤ, f j) :=
        mul_le_mul_of_nonneg_left
          (recurrenceIterate_layer_sum_bound m n f hf hf_nonneg)
          (show 0 ≤ (1 / 2 : ℝ) ^ m from
            pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m)
      _ = c * (7 / 8 : ℝ) ^ m * ∑' j : ℤ, f j := by
        calc
          _ = ((14 / 3 : ℝ) * ((1 / 2 : ℝ) ^ m * (7 / 4 : ℝ) ^ (m + 1))) *
              ∑' j : ℤ, f j := by ring
          _ = ((14 / 3 : ℝ) * (7 / 4 : ℝ) * (7 / 8 : ℝ) ^ m) *
              ∑' j : ℤ, f j := by rw [recurrenceHalfAlpha_power]; ring
          _ = c * (7 / 8 : ℝ) ^ m * ∑' j : ℤ, f j := by rfl
  have hpartial :
      (∑ m ∈ Finset.range T,
        c * (7 / 8 : ℝ) ^ m * ∑' j : ℤ, f j) ≤
        c * (∑' m : ℕ, (7 / 8 : ℝ) ^ m) * ∑' j : ℤ, f j := by
    calc
      _ = ∑ m ∈ Finset.range T,
          (c * (∑' j : ℤ, f j)) * (7 / 8 : ℝ) ^ m := by
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = c * (∑' j : ℤ, f j) * ∑ m ∈ Finset.range T, (7 / 8 : ℝ) ^ m := by
        rw [Finset.mul_sum]
      _ ≤ c * (∑' j : ℤ, f j) * ∑' m : ℕ, (7 / 8 : ℝ) ^ m := by
        apply mul_le_mul_of_nonneg_left
        · exact Summable.sum_le_tsum (Finset.range T)
            (fun m hm => pow_nonneg (by norm_num) m)
            (summable_geometric_of_lt_one (by norm_num) (by norm_num))
        · exact mul_nonneg (by norm_num [c]) hfT
      _ = c * (∑' m : ℕ, (7 / 8 : ℝ) ^ m) * ∑' j : ℤ, f j := by ring
  calc
    _ ≤ ∑ m ∈ Finset.range T,
        c * (7 / 8 : ℝ) ^ m * ∑' j : ℤ, f j := by
      apply Finset.sum_le_sum
      intro m hm
      exact hlayer m
    _ ≤ c * (∑' m : ℕ, (7 / 8 : ℝ) ^ m) * ∑' j : ℤ, f j := hpartial
    _ = recurrenceSeparatedCoefficient * ∑' j : ℤ, f j := by
      dsimp [c]
      rw [← recurrenceSeparatedCoefficient_eq]

private theorem recurrenceSum_range_extend_if (d T : ℕ) (hd : d ≤ T)
    (f : ℕ → ℝ) :
    (∑ m ∈ Finset.range d, f m) =
      ∑ m ∈ Finset.range T, if m < d then f m else 0 := by
  have hfilter : Finset.range d = (Finset.range T).filter (fun m => m < d) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  rw [hfilter, Finset.sum_filter]

/-- The summed one-step recurrence yields the two-term estimate. The
inputs are the actual local recurrence for valid iterates and the terminal
bound below the cutoff; this declaration is an internal arithmetic helper. -/
theorem recurrenceCover_total_sum_bound (n : ℕ) (cover sep : ℤ → ℝ)
    (hstep : ∀ q m, m < recurrenceDepth q →
      cover (recurrenceIterate m q) ≤
        (1 / 2 : ℝ) * cover (recurrenceIterate (m + 1) q) +
          sep (recurrenceIterate (m + 1) q))
    (hterminal : ∀ k ∈ Finset.range (n + 1),
      cover (recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)) ≤ cover 0)
    (hcover0 : 0 ≤ cover 0) (hsep : Summable sep)
    (hsep_nonneg : ∀ j, 0 ≤ sep j) :
    (∑ k ∈ Finset.range (n + 1), cover (k : ℤ)) ≤
      recurrenceFirstTermConstant * cover 0 +
        recurrenceSeparatedCoefficient * ∑' j : ℤ, sep j := by
  let T := ∑ k ∈ Finset.range (n + 1), recurrenceDepth (k : ℤ)
  have hdepth (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      recurrenceDepth (k : ℤ) ≤ T := by
    exact recurrenceDepth_le_sum_on_range n k hk
  have hsumExtend (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (∑ m ∈ Finset.range (recurrenceDepth (k : ℤ)),
        (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ))) =
      ∑ m ∈ Finset.range T,
        if m < recurrenceDepth (k : ℤ) then
          (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ)) else 0 :=
    recurrenceSum_range_extend_if _ _ (hdepth k hk) _
  have hseparatedSwap :
      (∑ k ∈ Finset.range (n + 1),
        ∑ m ∈ Finset.range (recurrenceDepth (k : ℤ)),
          (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ))) =
      (∑ m ∈ Finset.range T,
        ∑ k ∈ Finset.range (n + 1),
          if m < recurrenceDepth (k : ℤ) then
            (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ)) else 0) := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          ∑ m ∈ Finset.range T,
            if m < recurrenceDepth (k : ℤ) then
              (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ)) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hsumExtend k hk
      _ = _ := Finset.sum_comm
  have hcoverSum :
      (∑ k ∈ Finset.range (n + 1), cover (k : ℤ)) ≤
        (∑ k ∈ Finset.range (n + 1),
          (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) * cover 0) +
        (∑ k ∈ Finset.range (n + 1),
          ∑ m ∈ Finset.range (recurrenceDepth (k : ℤ)),
            (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    have hexpand := recurrenceCover_iterate_expansion cover sep hstep (k : ℤ)
    have hlast := hterminal k hk
    have hweight : 0 ≤ (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) := by positivity
    calc
      cover (k : ℤ) ≤
          (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) *
              cover (recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)) +
            ∑ m ∈ Finset.range (recurrenceDepth (k : ℤ)),
              (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ)) := hexpand
      _ ≤ (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) * cover 0 +
            ∑ m ∈ Finset.range (recurrenceDepth (k : ℤ)),
              (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hlast hweight) le_rfl
  have hfirst :
      (∑ k ∈ Finset.range (n + 1),
        (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) * cover 0) ≤
        recurrenceFirstTermConstant * cover 0 := by
    calc
      _ = cover 0 *
          ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) := by
        calc
          _ = ∑ k ∈ Finset.range (n + 1),
              cover 0 * (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
          _ = _ := by rw [Finset.mul_sum]
      _ ≤ cover 0 * recurrenceFirstTermConstant :=
        mul_le_mul_of_nonneg_left (recurrenceFirstTerm_sum_bound n) hcover0
      _ = recurrenceFirstTermConstant * cover 0 := by ring
  have hsepBound :
      (∑ k ∈ Finset.range (n + 1),
        ∑ m ∈ Finset.range (recurrenceDepth (k : ℤ)),
          (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ))) ≤
        recurrenceSeparatedCoefficient * ∑' j : ℤ, sep j := by
    rw [hseparatedSwap]
    exact recurrenceValidSeparated_sum_bound n sep hsep hsep_nonneg
  calc
    _ ≤ (∑ k ∈ Finset.range (n + 1),
          (1 / 2 : ℝ) ^ recurrenceDepth (k : ℤ) * cover 0) +
        (∑ k ∈ Finset.range (n + 1),
          ∑ m ∈ Finset.range (recurrenceDepth (k : ℤ)),
            (1 / 2 : ℝ) ^ m * sep (recurrenceIterate (m + 1) (k : ℤ))) := hcoverSum
    _ ≤ recurrenceFirstTermConstant * cover 0 +
        recurrenceSeparatedCoefficient * ∑' j : ℤ, sep j := add_le_add hfirst hsepBound

/-- Combining the two explicit coefficients gives the numerical  `D₁`.
This is the coefficient comparison used after the scale recurrence is summed. -/
theorem recurrenceD1_combination (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    recurrenceFirstTermConstant * x + recurrenceSeparatedCoefficient * y ≤
      recurrenceP21Constant * (x + y) := by
  dsimp [recurrenceP21Constant]
  have htail : 0 ≤ ∑' n : ℕ, recurrenceTailTerm n :=
    tsum_nonneg recurrenceTailTerm_nonneg
  have hfirst : 0 ≤ recurrenceFirstTermConstant := by
    dsimp [recurrenceFirstTermConstant]
    linarith only [htail]
  norm_num [recurrenceSeparatedCoefficient] at *
  nlinarith only [hx, hy, hfirst]

/-- Internal fixed-`D₁` form of the summed recurrence helper. It leaves the
one-step cover recurrence and below-cutoff terminal estimate explicit for a
later geometric-cover instantiation. -/
theorem recurrenceCover_total_sum_bound_D1_of_step (n : ℕ)
    (cover sep : ℤ → ℝ)
    (hstep : ∀ q m, m < recurrenceDepth q →
      cover (recurrenceIterate m q) ≤
        (1 / 2 : ℝ) * cover (recurrenceIterate (m + 1) q) +
          sep (recurrenceIterate (m + 1) q))
    (hterminal : ∀ k ∈ Finset.range (n + 1),
      cover (recurrenceIterate (recurrenceDepth (k : ℤ)) (k : ℤ)) ≤ cover 0)
    (hcover0 : 0 ≤ cover 0) (hsep : Summable sep)
    (hsep_nonneg : ∀ j, 0 ≤ sep j) :
    (∑ k ∈ Finset.range (n + 1), cover (k : ℤ)) ≤
      recurrenceP21Constant * (cover 0 + ∑' j : ℤ, sep j) := by
  have hsum := recurrenceCover_total_sum_bound n cover sep hstep hterminal
    hcover0 hsep hsep_nonneg
  have hsepTotal : 0 ≤ ∑' j : ℤ, sep j := tsum_nonneg hsep_nonneg
  exact hsum.trans (recurrenceD1_combination (cover 0) (∑' j : ℤ, sep j)
    hcover0 hsepTotal)

end FroehlichSpencer.BKT

end
