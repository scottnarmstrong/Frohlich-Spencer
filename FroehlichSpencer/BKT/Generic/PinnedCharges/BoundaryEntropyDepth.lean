/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyIteration
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyScale

/-! # Stopping depth for the shifted pinned scale map

The shifted scale map is conjugate to the reviewed KP floor recurrence. This
module transfers its stopping and fiber arithmetic to the pinned scale range.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

/-- Forget the eight-scale shift, clamping values below the natural scale
range to zero. -/
def boundaryEntropyPhi (q : ℤ) : ℕ := (q - 8).toNat

private theorem boundaryEntropyPhi_zero_of_le_eight {q : ℤ} (hq : q ≤ 8) :
    boundaryEntropyPhi q = 0 := by
  unfold boundaryEntropyPhi
  rw [Int.toNat_of_nonpos (by omega)]

private theorem recurrenceGamma_lt_eight_of_le_eight (q : ℤ) (hq : q ≤ 8) :
    recurrenceGamma q < 8 := by
  have hqR : (q : ℝ) ≤ 8 := by exact_mod_cast hq
  have hupper := (recurrenceGamma_bounds q).2
  have hreal : (recurrenceGamma q : ℝ) < 8 := by nlinarith only [hupper, hqR]
  exact_mod_cast hreal

/-- The clamped scale map commutes with the KP recurrence under the shift. -/
theorem boundaryEntropyPhi_recurrenceGamma (q : ℤ) :
    boundaryEntropyPhi (recurrenceGamma q) =
      boundaryEntropyGamma (boundaryEntropyPhi q) := by
  by_cases hq : 8 ≤ q
  · have hphi : (boundaryEntropyPhi q : ℤ) = q - 8 :=
      Int.toNat_of_nonneg (by omega)
    have hshift : (boundaryEntropyPhi q : ℤ) + 8 = q := by omega
    change (recurrenceGamma q - 8).toNat =
      (recurrenceGamma ((boundaryEntropyPhi q : ℤ) + 8) - 8).toNat
    rw [hshift]
  · have hq' : q ≤ 8 := by omega
    have hgamma : recurrenceGamma q < 8 := recurrenceGamma_lt_eight_of_le_eight q hq'
    have hgamma8 : recurrenceGamma 8 < 8 :=
      recurrenceGamma_lt_eight_of_le_eight 8 le_rfl
    rw [boundaryEntropyPhi_zero_of_le_eight hgamma.le]
    rw [boundaryEntropyPhi_zero_of_le_eight hq']
    change 0 = (recurrenceGamma 8 - 8).toNat
    rw [Int.toNat_of_nonpos (by omega)]

/-- Iterating the pinned scale map is exactly the shifted KP iterate after
applying the clamping map. -/
theorem boundaryEntropyIterate_eq_phi (m : ℕ) (q : ℤ) :
    boundaryEntropyIterate boundaryEntropyGamma m (boundaryEntropyPhi q) =
      boundaryEntropyPhi (recurrenceIterate m q) := by
  induction m generalizing q with
  | zero => rfl
  | succ m ih =>
      rw [boundaryEntropyIterate, recurrenceIterate]
      rw [← boundaryEntropyPhi_recurrenceGamma q]
      exact ih (recurrenceGamma q)

private theorem boundaryEntropyPhi_nat_add_eight (k : ℕ) :
    boundaryEntropyPhi ((k : ℤ) + 8) = k := by
  have hcast : ((k : ℤ) + 8 - 8) = (k : ℤ) := by omega
  simp [boundaryEntropyPhi, hcast]

private theorem boundaryEntropyPhi_lt_29_iff (q : ℤ) :
    boundaryEntropyPhi q < 29 ↔ q < 37 := by
  by_cases hq : 8 ≤ q
  · have hphi : (boundaryEntropyPhi q : ℤ) = q - 8 :=
      Int.toNat_of_nonneg (by omega)
    rw [← Int.ofNat_lt, hphi]
    omega
  · have hq' : q ≤ 8 := by omega
    rw [boundaryEntropyPhi_zero_of_le_eight hq']
    omega

private theorem exists_boundaryEntropyIterate_below_29 (k : ℕ) :
    ∃ m, boundaryEntropyIterate boundaryEntropyGamma m k < 29 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k < 29
      · exact ⟨0, by simpa [boundaryEntropyIterate] using hk⟩
      · have hk29 : 29 ≤ k := by omega
        obtain ⟨_, hgap⟩ := boundaryEntropyGamma_spec k hk29
        have hgamma : boundaryEntropyGamma k < k := by omega
        obtain ⟨m, hm⟩ := ih (boundaryEntropyGamma k) hgamma
        exact ⟨m + 1, by simpa [boundaryEntropyIterate] using hm⟩

/-- Every scale reaches the initial range after finitely many applications
of the shifted recurrence. -/
theorem exists_boundaryEntropyIterate_below (k : ℕ) :
    ∃ m, recurrenceIterate m ((k : ℤ) + 8) < 37 := by
  obtain ⟨m, hm⟩ := exists_boundaryEntropyIterate_below_29 k
  have hphi := boundaryEntropyIterate_eq_phi m ((k : ℤ) + 8)
  rw [boundaryEntropyPhi_nat_add_eight] at hphi
  exact ⟨m, (boundaryEntropyPhi_lt_29_iff _).1 (hphi ▸ hm)⟩

/-- First passage below the pinned recurrence range `k=29`. -/
noncomputable def boundaryEntropyDepth (k : ℕ) : ℕ :=
  Nat.find (exists_boundaryEntropyIterate_below k)

/-- The shifted KP iterate at the stopping depth is below `37`. -/
theorem boundaryEntropyDepth_stops (k : ℕ) :
    recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8) < 37 :=
  Nat.find_spec (exists_boundaryEntropyIterate_below k)

/-- Below scale `29`, the stopping depth is zero. -/
theorem boundaryEntropyDepth_eq_zero_of_below {k : ℕ} (hk : k < 29) :
    boundaryEntropyDepth k = 0 := by
  have hstop : recurrenceIterate 0 ((k : ℤ) + 8) < 37 := by
    simpa [recurrenceIterate] using (show (k : ℤ) + 8 < 37 by omega)
  have hle := Nat.find_min' (exists_boundaryEntropyIterate_below k) hstop
  change boundaryEntropyDepth k ≤ 0 at hle
  omega

/-- Every positive stopping depth starts in the recurrence range. -/
theorem boundaryEntropyDepth_pos_lower {k : ℕ}
    (hpos : 0 < boundaryEntropyDepth k) : 29 ≤ k := by
  by_contra hk
  have hklt : k < 29 := by omega
  have hzero := boundaryEntropyDepth_eq_zero_of_below hklt
  rw [hzero] at hpos
  omega

/-- Before the first-passage depth, every shifted iterate remains at least
`37`, so its corresponding pinned scale is at least `29`. -/
theorem boundaryEntropyDepth_valid_before (k : ℕ) {m : ℕ}
    (hm : m < boundaryEntropyDepth k) :
    37 ≤ recurrenceIterate m ((k : ℤ) + 8) := by
  by_contra h
  have hstop : recurrenceIterate m ((k : ℤ) + 8) < 37 := by omega
  have hmin := Nat.find_min' (exists_boundaryEntropyIterate_below k) hstop
  change boundaryEntropyDepth k ≤ m at hmin
  exact (Nat.not_lt_of_ge hmin) hm

/-- The stopping depth decreases by one after one scale-map step. -/
theorem boundaryEntropyDepth_gamma (k : ℕ) (hk : 29 ≤ k) :
    boundaryEntropyDepth k = boundaryEntropyDepth (boundaryEntropyGamma k) + 1 := by
  let d := boundaryEntropyDepth k
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hstop : recurrenceIterate d ((k : ℤ) + 8) < 37 := by
      simpa [d] using boundaryEntropyDepth_stops k
    have hklt : k < 29 := by
      have : (k : ℤ) + 8 < 37 := by simpa [d, hd0, recurrenceIterate] using hstop
      omega
    omega
  have hγcast : (boundaryEntropyGamma k : ℤ) + 8 =
      recurrenceGamma ((k : ℤ) + 8) := by
    obtain ⟨hcast, _⟩ := boundaryEntropyGamma_spec k hk
    have hcastInt : (boundaryEntropyGamma k : ℤ) =
        recurrenceGamma ((k : ℤ) + 8) - 8 := by exact_mod_cast hcast
    omega
  have hγstop :
      recurrenceIterate (d - 1) ((boundaryEntropyGamma k : ℤ) + 8) < 37 := by
    have hstop := boundaryEntropyDepth_stops k
    have hd' : d - 1 + 1 = d := by omega
    have hstop' : recurrenceIterate (d - 1)
        (recurrenceGamma ((k : ℤ) + 8)) < 37 := by
      have hstopd : recurrenceIterate d ((k : ℤ) + 8) < 37 := by
        simpa [d] using hstop
      rw [← hd'] at hstopd
      simpa [recurrenceIterate] using hstopd
    rw [hγcast]
    exact hstop'
  have hdepthLe : boundaryEntropyDepth (boundaryEntropyGamma k) ≤ d - 1 :=
    Nat.find_min' (exists_boundaryEntropyIterate_below (boundaryEntropyGamma k)) hγstop
  have hsmallStop := boundaryEntropyDepth_stops (boundaryEntropyGamma k)
  have hstop : recurrenceIterate
      (boundaryEntropyDepth (boundaryEntropyGamma k) + 1) ((k : ℤ) + 8) < 37 := by
    have hsmallStop' := hsmallStop
    rw [hγcast] at hsmallStop'
    simpa [recurrenceIterate] using hsmallStop'
  have hdepthGe : d ≤ boundaryEntropyDepth (boundaryEntropyGamma k) + 1 := by
    dsimp [d]
    exact Nat.find_min' (exists_boundaryEntropyIterate_below k) hstop
  omega

/-- The stopping depth dominates the logarithmic contraction count at the
threshold `68`, after accounting for the `30`-unit accumulated floor error. -/
theorem boundaryEntropyDepth_ge_floor_log (k : ℕ) (hk : 60 ≤ k) :
    ⌊Real.logb (7 / 4 : ℝ) (((k : ℝ) + 8) / 68)⌋₊ ≤
      boundaryEntropyDepth k := by
  by_contra h
  have hlt : boundaryEntropyDepth k <
      ⌊Real.logb (7 / 4 : ℝ) (((k : ℝ) + 8) / 68)⌋₊ := by omega
  have hq : 68 ≤ (k : ℝ) + 8 := by exact_mod_cast (show 60 + 8 ≤ k + 8 by omega)
  let x := Real.logb (7 / 4 : ℝ) (((k : ℝ) + 8) / 68)
  have hxpos : 0 < ((k : ℝ) + 8) / 68 := by positivity
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    exact Real.logb_nonneg (by norm_num) (by
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 68)).2 (by nlinarith [hq]))
  have hdepthFloor :
      (boundaryEntropyDepth k : ℝ) ≤ (Nat.floor x : ℝ) := by
    simpa [x] using (show
      (boundaryEntropyDepth k : ℝ) ≤
        (Nat.floor (Real.logb (7 / 4 : ℝ) (((k : ℝ) + 8) / 68)) : ℝ) by
        exact_mod_cast (Nat.le_of_lt hlt))
  have hmLog : (boundaryEntropyDepth k : ℝ) ≤ x := by
    have hfloor : (Nat.floor x : ℝ) ≤ x := Nat.floor_le (by linarith)
    exact hdepthFloor.trans hfloor
  have hpow : (7 / 4 : ℝ) ^ boundaryEntropyDepth k ≤
      ((k : ℝ) + 8) / 68 := by
    have hpow' := (Real.le_logb_iff_rpow_le (by norm_num) hxpos).1 hmLog
    simpa only [Real.rpow_natCast] using hpow'
  have hprod : (7 / 4 : ℝ) ^ boundaryEntropyDepth k * 68 ≤
      (k : ℝ) + 8 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 68)).1 hpow
  have hInv : (4 / 7 : ℝ) ^ boundaryEntropyDepth k *
      (7 / 4 : ℝ) ^ boundaryEntropyDepth k = 1 := by
    rw [← mul_pow]
    norm_num
  have hScaled : 68 ≤ (4 / 7 : ℝ) ^ boundaryEntropyDepth k *
      ((k : ℝ) + 8) := by
    have hnonneg : 0 ≤ (4 / 7 : ℝ) ^ boundaryEntropyDepth k := by positivity
    calc
      68 = 1 * 68 := by ring
      _ = ((4 / 7 : ℝ) ^ boundaryEntropyDepth k *
          (7 / 4 : ℝ) ^ boundaryEntropyDepth k) * 68 := by rw [hInv]
      _ = (4 / 7 : ℝ) ^ boundaryEntropyDepth k *
          ((7 / 4 : ℝ) ^ boundaryEntropyDepth k * 68) := by ring
      _ ≤ (4 / 7 : ℝ) ^ boundaryEntropyDepth k * ((k : ℝ) + 8) :=
        mul_le_mul_of_nonneg_left hprod hnonneg
  have houter := recurrenceIterate_outer_lower (boundaryEntropyDepth k)
    ((k : ℤ) + 8)
  have hstop := boundaryEntropyDepth_stops k
  have houter' := houter
  have houterR : (4 / 7 : ℝ) ^ boundaryEntropyDepth k *
      ((k : ℝ) + 8) - 30 ≤
        (recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8) : ℝ) := by
    simpa using houter'
  have h38 : (38 : ℝ) ≤
      (recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8) : ℝ) := by
    linarith only [hScaled, houterR]
  have hstopReal :
      (recurrenceIterate (boundaryEntropyDepth k) ((k : ℤ) + 8) : ℝ) < 37 := by
    exact_mod_cast hstop
  linarith

/-- Weight of the terminal minimum-cover term after iterating the recurrence. -/
def boundaryEntropyTerminalWeight (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ boundaryEntropyDepth k

private theorem boundaryEntropy_half_rpow_logb (x : ℝ) (hx : 0 < x) :
    (1 / 2 : ℝ) ^ Real.logb (7 / 4 : ℝ) x =
      x ^ (-recurrenceSeriesExponent) := by
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hx]
  apply congrArg Real.exp
  simp only [Real.logb, recurrenceSeriesExponent]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 7 / 4))]

/-- Pointwise p-series majorant for the terminal weights. -/
theorem boundaryEntropyTerminalWeight_le_powerTail (k : ℕ) (hk : 60 ≤ k) :
    boundaryEntropyTerminalWeight k ≤
      2 * (68 / ((k : ℝ) + 8)) ^ recurrenceSeriesExponent := by
  have hdepth := boundaryEntropyDepth_ge_floor_log k hk
  let x := Real.logb (7 / 4 : ℝ) (((k : ℝ) + 8) / 68)
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    apply Real.logb_nonneg (by norm_num)
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 68)).2 (by
      exact_mod_cast (show 68 ≤ k + 8 by omega))
  have hfloor : x - 1 ≤ (Nat.floor x : ℝ) := by
    have hlt := Nat.lt_floor_add_one x
    linarith
  have hdepthR : (Nat.floor x : ℝ) ≤ (boundaryEntropyDepth k : ℝ) := by
    simpa [x] using (show
      (Nat.floor (Real.logb (7 / 4 : ℝ) (((k : ℝ) + 8) / 68)) : ℝ) ≤
        (boundaryEntropyDepth k : ℝ) by exact_mod_cast hdepth)
  have hpow : (1 / 2 : ℝ) ^ (boundaryEntropyDepth k : ℝ) ≤
      (1 / 2 : ℝ) ^ (x - 1) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (hfloor.trans hdepthR)
  have hqpos : 0 < (k : ℝ) + 8 := by positivity
  calc
    boundaryEntropyTerminalWeight k =
        (1 / 2 : ℝ) ^ (boundaryEntropyDepth k : ℝ) := by
          simp [boundaryEntropyTerminalWeight, Real.rpow_natCast]
    _ ≤ (1 / 2 : ℝ) ^ (x - 1) := hpow
    _ = 2 * (1 / 2 : ℝ) ^ x := by
          rw [Real.rpow_sub (by norm_num), Real.rpow_one]
          field_simp
    _ = 2 * (((k : ℝ) + 8) / 68) ^ (-recurrenceSeriesExponent) := by
          congr 1
          dsimp [x]
          exact boundaryEntropy_half_rpow_logb _ (div_pos hqpos (by norm_num))
    _ = 2 * (68 / ((k : ℝ) + 8)) ^ recurrenceSeriesExponent := by
          congr 1
          rw [Real.rpow_neg_eq_inv_rpow]
          congr 1
          field_simp

/-- The terminal weights are summable uniformly in the stopping horizon. -/
theorem boundaryEntropyTerminalWeight_summable :
    Summable boundaryEntropyTerminalWeight := by
  have hp : 1 < recurrenceSeriesExponent := recurrenceSeriesExponent_gt_one
  have hpNonneg : 0 ≤ recurrenceSeriesExponent :=
    le_trans (by norm_num) hp.le
  have hbase : Summable (fun k : ℕ =>
      1 / ((k : ℝ) + 1) ^ recurrenceSeriesExponent) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 recurrenceSeriesExponent).2 hp
    have hpos (k : ℕ) : 0 < (k : ℝ) + 1 := by positivity
    convert h using 1
    ext k
    rw [abs_of_pos (hpos k)]
  let C : ℝ := (61 : ℝ) ^ recurrenceSeriesExponent +
    2 * (68 : ℝ) ^ recurrenceSeriesExponent
  have hmajorant : Summable (fun k : ℕ =>
      C * (1 / ((k : ℝ) + 1) ^ recurrenceSeriesExponent)) :=
    hbase.mul_left C
  have hpoint : ∀ k, boundaryEntropyTerminalWeight k ≤
      C * (1 / ((k : ℝ) + 1) ^ recurrenceSeriesExponent) := by
    intro k
    by_cases hk : 60 ≤ k
    · have htail := boundaryEntropyTerminalWeight_le_powerTail k hk
      have hfrac : 68 / ((k : ℝ) + 8) ≤ 68 / ((k : ℝ) + 1) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      have hpow := Real.rpow_le_rpow (by positivity) hfrac hpNonneg
      have htail' : boundaryEntropyTerminalWeight k ≤
          2 * (68 / ((k : ℝ) + 1)) ^ recurrenceSeriesExponent :=
        htail.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
      have hfactor :
          2 * (68 / ((k : ℝ) + 1)) ^ recurrenceSeriesExponent ≤
            C * (1 / ((k : ℝ) + 1) ^ recurrenceSeriesExponent) := by
        have hdenpos : 0 < (k : ℝ) + 1 := by positivity
        have hconst : 2 * (68 : ℝ) ^ recurrenceSeriesExponent ≤ C := by
          dsimp [C]
          have hpow61 : 0 ≤ (61 : ℝ) ^ recurrenceSeriesExponent :=
            Real.rpow_nonneg (by norm_num) _
          have hpow68 : 0 ≤ (68 : ℝ) ^ recurrenceSeriesExponent :=
            Real.rpow_nonneg (by norm_num) _
          linarith [hpow61, hpow68]
        have hden : 0 ≤ ((k : ℝ) + 1) ^ recurrenceSeriesExponent := by positivity
        calc
          2 * (68 / ((k : ℝ) + 1)) ^ recurrenceSeriesExponent =
              2 * ((68 : ℝ) ^ recurrenceSeriesExponent /
                ((k : ℝ) + 1) ^ recurrenceSeriesExponent) := by
                  rw [Real.div_rpow (by norm_num) (le_of_lt hdenpos)]
          _ = (2 * (68 : ℝ) ^ recurrenceSeriesExponent) *
                (1 / ((k : ℝ) + 1) ^ recurrenceSeriesExponent) := by ring
          _ ≤ C * (1 / ((k : ℝ) + 1) ^ recurrenceSeriesExponent) :=
            mul_le_mul_of_nonneg_right hconst (by positivity)
      exact htail'.trans hfactor
    · have hk' : k < 60 := by omega
      have hone : boundaryEntropyTerminalWeight k ≤ 1 := by
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have hdenle : ((k : ℝ) + 1) ^ recurrenceSeriesExponent ≤
          (61 : ℝ) ^ recurrenceSeriesExponent := by
        have hkR : (k : ℝ) + 1 ≤ 61 := by exact_mod_cast (by omega : k + 1 ≤ 61)
        exact Real.rpow_le_rpow (by positivity) hkR hpNonneg
      have hconst : 1 ≤ C / ((k : ℝ) + 1) ^ recurrenceSeriesExponent := by
        have hdenpos : 0 < ((k : ℝ) + 1) ^ recurrenceSeriesExponent := by positivity
        have hC : (61 : ℝ) ^ recurrenceSeriesExponent ≤ C := by
          dsimp [C]
          have hpow61 : 0 ≤ (61 : ℝ) ^ recurrenceSeriesExponent :=
            Real.rpow_nonneg (by norm_num) _
          have hpow68 : 0 ≤ (68 : ℝ) ^ recurrenceSeriesExponent :=
            Real.rpow_nonneg (by norm_num) _
          linarith [hpow61, hpow68]
        rw [le_div_iff₀ hdenpos]
        simpa using hdenle.trans hC
      simpa [div_eq_mul_inv] using hone.trans hconst
  refine Summable.of_nonneg_of_le (fun k => ?_) hpoint hmajorant
  unfold boundaryEntropyTerminalWeight
  positivity

/-- A horizon-independent bound on every finite sum of terminal weights. -/
theorem boundaryEntropyTerminalWeight_sum_le (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), boundaryEntropyTerminalWeight k) ≤
      ∑' k : ℕ, boundaryEntropyTerminalWeight k :=
  Summable.sum_le_tsum _ (by intro k hk; unfold boundaryEntropyTerminalWeight; positivity)
    boundaryEntropyTerminalWeight_summable

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
