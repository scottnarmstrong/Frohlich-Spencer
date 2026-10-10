/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# FS82 §3 Wilson character coefficients

The modified Bessel coefficients are defined by their standard nonnegative
power series. This module records the summability and normalization data used
to periodize the Wilson character expansion at frequencies in `Nℤ`.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.ZN

/-- The `n`th modified Bessel coefficient `I_n(h)`, given by its defining
power series. -/
@[expose] noncomputable def modifiedBesselI (n : ℕ) (h : ℝ) : ℝ :=
  ∑' k : ℕ, (h / 2) ^ (n + 2 * k) /
    ((k.factorial : ℝ) * ((n + k).factorial : ℝ))

@[expose] noncomputable def modifiedBesselITerm (n : ℕ) (h : ℝ) (k : ℕ) : ℝ :=
  (h / 2) ^ (n + 2 * k) /
    ((k.factorial : ℝ) * ((n + k).factorial : ℝ))

@[simp] theorem modifiedBesselI_eq_tsum (n : ℕ) (h : ℝ) :
    modifiedBesselI n h = ∑' k : ℕ, modifiedBesselITerm n h k := rfl

@[expose] noncomputable def modifiedBesselBaseTerm (h : ℝ) (k : ℕ) : ℝ :=
  (h / 2) ^ k / (k.factorial : ℝ)

theorem modifiedBesselITerm_eq_baseProduct (n : ℕ) (h : ℝ) (k : ℕ) :
    modifiedBesselITerm n h k =
      modifiedBesselBaseTerm h k * modifiedBesselBaseTerm h (k + n) := by
  unfold modifiedBesselITerm modifiedBesselBaseTerm
  rw [Nat.add_comm k n]
  rw [show n + 2 * k = k + (k + n) by omega, pow_add]
  field_simp
  ring

private theorem modifiedBesselITerm_summable (n : ℕ) (h : ℝ) :
    Summable (modifiedBesselITerm n h) := by
  let c : ℝ := |h / 2|
  have hbound : ∀ k : ℕ,
      ‖modifiedBesselITerm n h k‖ ≤ c ^ n * (c ^ 2) ^ k / (k.factorial : ℝ) := by
    intro k
    have hkf : 0 < (k.factorial : ℝ) := by positivity
    have hterm : ‖modifiedBesselITerm n h k‖ =
        c ^ (n + 2 * k) /
          ((k.factorial : ℝ) * ((n + k).factorial : ℝ)) := by
      simp [modifiedBesselITerm, c, Real.norm_eq_abs, abs_div]
    rw [hterm]
    have hfactNat : 1 ≤ (n + k).factorial :=
      Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hfact : 1 ≤ ((n + k).factorial : ℝ) := by exact_mod_cast hfactNat
    have hdenle : (k.factorial : ℝ) ≤
        (k.factorial : ℝ) * ((n + k).factorial : ℝ) := by
      calc
        (k.factorial : ℝ) = (k.factorial : ℝ) * 1 := by ring
        _ ≤ (k.factorial : ℝ) * ((n + k).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hfact (by positivity)
    rw [pow_add, pow_mul]
    exact (calc
      c ^ n * (c ^ 2) ^ k /
          ((k.factorial : ℝ) * ((n + k).factorial : ℝ)) ≤
        c ^ n * (c ^ 2) ^ k / (k.factorial : ℝ) := by
          apply div_le_div_of_nonneg_left (by positivity) hkf hdenle)
  exact Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (c ^ 2)).mul_left (c ^ n))
    (by
      intro k
      simpa [div_eq_mul_inv, mul_assoc] using hbound k)

/-- Absolute convergence of the defining modified Bessel series. -/
theorem summable_modifiedBesselITerm (n : ℕ) (h : ℝ) :
    Summable (modifiedBesselITerm n h) :=
  modifiedBesselITerm_summable n h

/-- A factorial envelope for the Bessel series. It implies summability in the
Fourier mode, not just convergence of each individual Bessel coefficient. -/
theorem modifiedBesselI_le_exp_envelope {n : ℕ} {h : ℝ} (hh : 0 ≤ h) :
    modifiedBesselI n h ≤
      ((h / 2) ^ n / (n.factorial : ℝ)) * Real.exp ((h / 2) ^ 2) := by
  let c : ℝ := h / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have htermBound : ∀ k : ℕ,
      modifiedBesselITerm n h k ≤
        (c ^ n / (n.factorial : ℝ)) * ((c ^ 2) ^ k / (k.factorial : ℝ)) := by
    intro k
    have hfacNat : n.factorial ≤ (n + k).factorial :=
      Nat.factorial_le (Nat.le_add_right n k)
    have hdenNat : n.factorial * k.factorial ≤ k.factorial * (n + k).factorial := by
      have := Nat.mul_le_mul_left k.factorial hfacNat
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    have hden : (n.factorial : ℝ) * (k.factorial : ℝ) ≤
        (k.factorial : ℝ) * ((n + k).factorial : ℝ) := by exact_mod_cast hdenNat
    have hdenPos : 0 < (n.factorial : ℝ) * (k.factorial : ℝ) := by positivity
    have hnum : 0 ≤ c ^ n * (c ^ 2) ^ k := by positivity
    have hpow : (h / 2) ^ (n + 2 * k) = c ^ n * (c ^ 2) ^ k := by
      dsimp [c]
      rw [pow_add, pow_mul]
    rw [modifiedBesselITerm, hpow]
    calc
      c ^ n * (c ^ 2) ^ k /
          ((k.factorial : ℝ) * ((n + k).factorial : ℝ)) ≤
        c ^ n * (c ^ 2) ^ k /
          ((n.factorial : ℝ) * (k.factorial : ℝ)) :=
        div_le_div_of_nonneg_left hnum hdenPos (by simpa [mul_comm] using hden)
      _ = (c ^ n / (n.factorial : ℝ)) *
          ((c ^ 2) ^ k / (k.factorial : ℝ)) := by
        field_simp
  have hsumLeft := summable_modifiedBesselITerm n h
  have hsumRight :=
    (Real.summable_pow_div_factorial (c ^ 2)).mul_left
      (c ^ n / (n.factorial : ℝ))
  have hsum := hsumLeft.tsum_le_tsum htermBound hsumRight
  have hexp : (∑' k : ℕ, (c ^ 2) ^ k / (k.factorial : ℝ)) = Real.exp (c ^ 2) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  calc
    modifiedBesselI n h = ∑' k : ℕ, modifiedBesselITerm n h k := rfl
    _ ≤ ∑' k : ℕ,
        (c ^ n / (n.factorial : ℝ)) * ((c ^ 2) ^ k / (k.factorial : ℝ)) := hsum
    _ = (c ^ n / (n.factorial : ℝ)) * Real.exp (c ^ 2) := by
      rw [(Real.summable_pow_div_factorial (c ^ 2)).tsum_mul_left
        (c ^ n / (n.factorial : ℝ)), hexp]
    _ = ((h / 2) ^ n / (n.factorial : ℝ)) * Real.exp ((h / 2) ^ 2) := by
      rfl

/-- For every nonzero mode, the modified Bessel coefficient is strictly below
the zero mode. The proof is the strict Cauchy–Schwarz estimate on the shifted
factorial sequence. -/
theorem modifiedBesselI_lt_zeroMode {n : ℕ} (hn : 0 < n) {h : ℝ} :
    modifiedBesselI n h < modifiedBesselI 0 h := by
  let a : ℕ → ℝ := modifiedBesselBaseTerm h
  let g : ℕ → ℝ := fun k => a k ^ 2
  let cross : ℕ → ℝ := fun k => a k * a (k + n)
  have hcrossEq : ∀ k, modifiedBesselITerm n h k = cross k := by
    intro k
    simp [cross, a, modifiedBesselITerm_eq_baseProduct]
  have hgEq : ∀ k, modifiedBesselITerm 0 h k = g k := by
    intro k
    simp [g, a, modifiedBesselITerm_eq_baseProduct, pow_two]
  have hcross : Summable cross := by
    apply (summable_modifiedBesselITerm n h).congr
    intro k
    exact hcrossEq k
  have hg : Summable g := by
    apply (summable_modifiedBesselITerm 0 h).congr
    intro k
    exact hgEq k
  have hshift : Summable (fun k => g (k + n)) :=
    hg.comp_injective (i := fun k : ℕ => k + n) (by
      intro k l hkl
      change k + n = l + n at hkl
      exact Nat.add_right_cancel hkl)
  have hIcross : ∑' k : ℕ, cross k = modifiedBesselI n h := by
    rw [modifiedBesselI_eq_tsum]
    congr 1
    funext k
    exact (hcrossEq k).symm
  have hIzero : ∑' k : ℕ, g k = modifiedBesselI 0 h := by
    rw [modifiedBesselI_eq_tsum]
    congr 1
    funext k
    exact (hgEq k).symm
  let tail : ℝ := ∑' k : ℕ, g (k + n)
  have htail : HasSum (fun k => g (k + n)) tail := by
    exact hshift.hasSum_iff.mpr rfl
  have hsplit := (hasSum_nat_add_iff n).mp htail
  have hsplitEq : tail + ∑ k ∈ Finset.range n, g k = modifiedBesselI 0 h := by
    have hwhole : HasSum g (modifiedBesselI 0 h) := hIzero ▸ hg.hasSum_iff.mpr rfl
    exact hsplit.unique hwhole
  have hprefix : 1 ≤ ∑ k ∈ Finset.range n, g k := by
    have hzero : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
    have hnonneg : ∀ k ∈ Finset.range n, 0 ≤ g k := by
      intro k hk
      positivity
    calc
      1 = g 0 := by simp [g, a, modifiedBesselBaseTerm]
      _ ≤ ∑ k ∈ Finset.range n, g k := Finset.single_le_sum hnonneg hzero
  have htailBound : tail + 1 ≤ modifiedBesselI 0 h := by linarith
  have hAMGM : ∀ k : ℕ, 2 * cross k ≤ g k + g (k + n) := by
    intro k
    dsimp [cross, g]
    nlinarith [sq_nonneg (a k - a (k + n))]
  have hright : Summable (fun k : ℕ => g k + g (k + n)) := hg.add hshift
  have hsumBound := hcross.mul_left (2 : ℝ)
  have hpointwise := hsumBound.tsum_le_tsum hAMGM hright
  have hleftEq : (∑' k : ℕ, 2 * cross k) = 2 * modifiedBesselI n h := by
    rw [hcross.tsum_mul_left 2, hIcross]
  have hrightEq : (∑' k : ℕ, (g k + g (k + n))) =
      modifiedBesselI 0 h + tail := by
    rw [hg.tsum_add hshift, hIzero]
  rw [hleftEq, hrightEq] at hpointwise
  linarith

theorem modifiedBesselI_nonneg {n : ℕ} {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ modifiedBesselI n h := by
  rw [modifiedBesselI_eq_tsum]
  apply tsum_nonneg
  intro k
  simp only [modifiedBesselITerm]
  positivity

theorem modifiedBesselI_pos {n : ℕ} {h : ℝ} (hh : 0 < h) :
    0 < modifiedBesselI n h := by
  rw [modifiedBesselI_eq_tsum]
  exact (summable_modifiedBesselITerm n h).tsum_pos
    (fun k => by
      simp only [modifiedBesselITerm]
      positivity)
    0 (by simp only [modifiedBesselITerm]; positivity)

theorem modifiedBesselI_zero_ge_one {h : ℝ} (hh : 0 ≤ h) :
    1 ≤ modifiedBesselI 0 h := by
  have hdelta : HasSum (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) 1 := by
    simpa using (hasSum_ite_eq 0 (1 : ℝ))
  have hdeltaSum :
      ∑' k : ℕ, (if k = 0 then (1 : ℝ) else 0) = 1 := hdelta.tsum_eq
  have hterm : ∀ k : ℕ,
      (if k = 0 then (1 : ℝ) else 0) ≤ modifiedBesselITerm 0 h k := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [modifiedBesselITerm]
    · simp [modifiedBesselITerm, hk]
      positivity
  have hsum := hdelta.summable.tsum_le_tsum hterm (summable_modifiedBesselITerm 0 h)
  rw [hdeltaSum] at hsum
  simpa only [modifiedBesselI_eq_tsum] using hsum


/-- The positive-frequency cosine coefficient at frequency `q*N`, in the
normalization of (3.10). Here `q` is the integer mode and `N` is the clock
order. -/
@[expose] noncomputable def wilsonCharacterCoefficient (_N q : ℕ) (h : ℝ) : ℝ :=
  2 * modifiedBesselI q h / modifiedBesselI 0 h


/-- The source's strict coefficient bounds (3.11), for positive `h` and
positive clock order. The endpoint `h=0` is handled separately below. -/
theorem wilsonCharacterCoefficient_bounds {N q : ℕ} {h : ℝ}
    (hq : 0 < q) (hh : 0 < h) :
    0 < wilsonCharacterCoefficient N q h ∧
      wilsonCharacterCoefficient N q h < 2 := by
  have hI : 0 < modifiedBesselI q h := modifiedBesselI_pos hh
  have hI0 : 0 < modifiedBesselI 0 h := modifiedBesselI_pos hh
  have hlt : modifiedBesselI q h < modifiedBesselI 0 h :=
    modifiedBesselI_lt_zeroMode hq
  constructor
  · unfold wilsonCharacterCoefficient
    exact div_pos (mul_pos (by norm_num) hI) hI0
  · unfold wilsonCharacterCoefficient
    apply (div_lt_iff₀ hI0).2
    nlinarith

/-- Absolute summability of the positive clock-frequency coefficients. -/
theorem summable_wilsonCharacterCoefficient {N : ℕ} {h : ℝ}
    (hh : 0 ≤ h) :
    Summable (fun q : ℕ => wilsonCharacterCoefficient N (q + 1) h) := by
  let c : ℝ := h / 2
  let C : ℝ := 2 * Real.exp (c ^ 2)
  have hbase : Summable (fun n : ℕ => c ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial c
  have hinj : Function.Injective (fun q : ℕ => q + 1) := by
    intro q r hqr
    exact Nat.succ.inj (by simpa using hqr)
  have hsub := hbase.comp_injective hinj
  have hboundSummable : Summable (fun q : ℕ => C *
      (c ^ (q + 1) / ((q + 1).factorial : ℝ))) :=
    hsub.mul_left C
  apply Summable.of_nonneg_of_le
  · intro q
    unfold wilsonCharacterCoefficient
    have hI : 0 ≤ modifiedBesselI (q + 1) h := modifiedBesselI_nonneg hh
    have hI0 : 0 < modifiedBesselI 0 h := lt_of_lt_of_le (by norm_num) (modifiedBesselI_zero_ge_one hh)
    positivity
  · intro q
    have hI0 : 1 ≤ modifiedBesselI 0 h := modifiedBesselI_zero_ge_one hh
    have hI : 0 ≤ modifiedBesselI (q + 1) h := modifiedBesselI_nonneg hh
    have hratio : wilsonCharacterCoefficient N (q + 1) h ≤
        2 * modifiedBesselI (q + 1) h := by
      unfold wilsonCharacterCoefficient
      calc
        2 * modifiedBesselI (q + 1) h / modifiedBesselI 0 h ≤
            2 * modifiedBesselI (q + 1) h / 1 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hI0
        _ = 2 * modifiedBesselI (q + 1) h := by simp
    have henv := modifiedBesselI_le_exp_envelope hh
      (n := q + 1)
    change wilsonCharacterCoefficient N (q + 1) h ≤
      C * (c ^ (q + 1) / ((q + 1).factorial : ℝ))
    dsimp [C, c]
    calc
      wilsonCharacterCoefficient N (q + 1) h ≤
          2 * modifiedBesselI (q + 1) h := hratio
      _ ≤ 2 * (((h / 2) ^ (q + 1) /
            ((q + 1).factorial : ℝ)) * Real.exp ((h / 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left henv (by norm_num)
      _ = 2 * Real.exp ((h / 2) ^ 2) *
            ((h / 2) ^ (q + 1) /
              ((q + 1).factorial : ℝ)) := by ring
  · exact hboundSummable


/-- Exponential splitting weights from (3.12), with the source index `q ≥ 1`
represented by `q+1` for `q : ℕ`. -/
@[expose] noncomputable def wilsonSplittingWeight (epsilon : ℝ) (q : ℕ) : ℝ :=
  Real.exp (epsilon * (q + 1 : ℕ)) / (Real.exp epsilon - 1)

theorem wilsonSplittingWeight_pos {epsilon : ℝ} {q : ℕ}
    (hepsilon : 0 < epsilon) : 0 < wilsonSplittingWeight epsilon q := by
  have hden : 0 < Real.exp epsilon - 1 := by
    have h := Real.add_one_lt_exp (ne_of_gt hepsilon)
    linarith
  simp only [wilsonSplittingWeight]
  exact div_pos (Real.exp_pos _) hden

/-- The coefficient activity `z_{qN}=ζ(q)λ(q)` from (3.13). -/
@[expose] noncomputable def wilsonCoefficientActivity
    (epsilon : ℝ) (N q : ℕ) (h : ℝ) : ℝ :=
  wilsonSplittingWeight epsilon q * wilsonCharacterCoefficient N (q + 1) h

theorem wilsonCoefficientActivity_bound {epsilon h : ℝ} {N q : ℕ}
    (hepsilon : 0 < epsilon) (hh : 0 < h) :
    0 < wilsonCoefficientActivity epsilon N q h ∧
      wilsonCoefficientActivity epsilon N q h <
        2 * epsilon⁻¹ * Real.exp (epsilon * (q + 1 : ℕ)) := by
  have hexp : epsilon < Real.exp epsilon - 1 := by
    have h := Real.add_one_lt_exp (ne_of_gt hepsilon)
    linarith
  have hden : 0 < Real.exp epsilon - 1 := by linarith
  have hw : 0 < wilsonSplittingWeight epsilon q := by
    simp only [wilsonSplittingWeight]
    exact div_pos (Real.exp_pos _) hden
  have hweight : wilsonSplittingWeight epsilon q <
      epsilon⁻¹ * Real.exp (epsilon * (q + 1 : ℕ)) := by
    rw [wilsonSplittingWeight]
    have hnum : 0 < Real.exp (epsilon * (q + 1 : ℕ)) := Real.exp_pos _
    have := div_lt_div_of_pos_left hnum hepsilon hexp
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  constructor
  · exact mul_pos hw (wilsonCharacterCoefficient_bounds (Nat.succ_pos q) hh).1
  · calc
      wilsonCoefficientActivity epsilon N q h =
          wilsonSplittingWeight epsilon q *
        wilsonCharacterCoefficient N (q + 1) h := rfl
      _ < wilsonSplittingWeight epsilon q * 2 :=
        mul_lt_mul_of_pos_left
          (wilsonCharacterCoefficient_bounds (Nat.succ_pos q) hh).2 hw
      _ < (epsilon⁻¹ * Real.exp (epsilon * (q + 1 : ℕ))) * 2 :=
        mul_lt_mul_of_pos_right hweight (by norm_num)
      _ = 2 * epsilon⁻¹ * Real.exp (epsilon * (q + 1 : ℕ)) := by ring

/-- Source-indexed version of the activity bound (3.14), with `q ≥ 1`. -/
@[expose] noncomputable def wilsonSourceCoefficientActivity
    (epsilon : ℝ) (N q : ℕ) (h : ℝ) : ℝ :=
  Real.exp (epsilon * q) / (Real.exp epsilon - 1) *
    wilsonCharacterCoefficient N q h

theorem wilsonSourceCoefficientActivity_bound {epsilon h : ℝ} {N q : ℕ}
    (hepsilon : 0 < epsilon) (hh : 0 < h) (hq : 0 < q) :
    0 < wilsonSourceCoefficientActivity epsilon N q h ∧
      wilsonSourceCoefficientActivity epsilon N q h <
        2 * epsilon⁻¹ * Real.exp (epsilon * q) := by
  have hrepr : q - 1 + 1 = q := by omega
  have hbound := wilsonCoefficientActivity_bound
    (epsilon := epsilon) (h := h) (N := N) (q := q - 1) hepsilon hh
  simpa [wilsonSourceCoefficientActivity, wilsonCoefficientActivity,
    wilsonSplittingWeight, hrepr, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hbound

theorem wilsonSplittingWeight_inv_tsum {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Summable (fun q : ℕ => (wilsonSplittingWeight epsilon q)⁻¹) ∧
      ∑' q : ℕ, (wilsonSplittingWeight epsilon q)⁻¹ = 1 := by
  let r : ℝ := Real.exp (-epsilon)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < Real.exp epsilon - 1 := by
    have h := Real.add_one_lt_exp (ne_of_gt hepsilon)
    linarith
  have hgeom := summable_geometric_of_lt_one (le_of_lt hr0) hr1
  have hgeomSum := tsum_geometric_of_lt_one (le_of_lt hr0) hr1
  have hgeomSucc : Summable (fun q : ℕ => r ^ (q + 1)) :=
    hgeom.comp_injective (i := fun q : ℕ => q + 1) (by
      intro q q' h
      exact Nat.succ.inj (by simpa using h))
  have hpower (q : ℕ) :
      Real.exp (epsilon * (q + 1 : ℕ)) * r ^ (q + 1) = 1 := by
    rw [show epsilon * (q + 1 : ℕ) = ((q + 1 : ℕ) : ℝ) * epsilon by ring,
      Real.exp_nat_mul]
    dsimp [r]
    rw [← mul_pow, Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero epsilon), one_pow]
  have hterm (q : ℕ) : (wilsonSplittingWeight epsilon q)⁻¹ =
      (Real.exp epsilon - 1) * r ^ (q + 1) := by
    rw [wilsonSplittingWeight, inv_div]
    have hinv : (Real.exp (epsilon * (q + 1 : ℕ)))⁻¹ = r ^ (q + 1) := by
      have hmul := hpower q
      calc
        (Real.exp (epsilon * (q + 1 : ℕ)))⁻¹ =
            ((r ^ (q + 1))⁻¹)⁻¹ := by
              rw [eq_inv_of_mul_eq_one_left hmul]
        _ = r ^ (q + 1) := by simp
    rw [div_eq_mul_inv, hinv]
  constructor
  · exact (hgeomSucc.mul_left (Real.exp epsilon - 1)).congr
      (fun q => (hterm q).symm)
  · calc
    (∑' q : ℕ, (wilsonSplittingWeight epsilon q)⁻¹) =
        ∑' q : ℕ, (Real.exp epsilon - 1) * r ^ (q + 1) :=
      tsum_congr hterm
    _ = (Real.exp epsilon - 1) * ∑' q : ℕ, r ^ (q + 1) :=
      hgeomSucc.tsum_mul_left _
    _ = (Real.exp epsilon - 1) *
        ((∑' q : ℕ, r ^ q) * r) := by
      congr 1
      calc
        (∑' q : ℕ, r ^ (q + 1)) = ∑' q : ℕ, r ^ q * r :=
          tsum_congr (fun q => by rw [pow_succ])
        _ = (∑' q : ℕ, r ^ q) * r := hgeom.tsum_mul_right r
    _ = 1 := by
      rw [hgeomSum]
      dsimp [r]
      rw [Real.exp_neg]
      field_simp [ne_of_gt (Real.exp_pos epsilon)]

private noncomputable def exponentialSeriesTerm (z : ℂ) (n : ℕ) : ℂ :=
  z ^ n / (n.factorial : ℂ)

private noncomputable def complexBesselTerm (n k : ℕ) (h : ℝ) : ℂ :=
  ((h : ℂ) / 2) ^ (n + 2 * k) /
    ((k.factorial : ℂ) * ((n + k).factorial : ℂ))

private noncomputable def complexBesselI (n : ℕ) (h : ℝ) : ℂ :=
  ∑' k : ℕ, complexBesselTerm n k h

private noncomputable def positiveCharacter (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I)

private noncomputable def negativeCharacter (θ : ℝ) : ℂ :=
  Complex.exp (-((θ : ℂ) * Complex.I))

/-- The absolutely summable exponential-series product, reindexed by its
integer frequency and the residual radial index. `inl n` represents
frequency `+n`, and `inr n` represents frequency `-(n+1)`. -/
private noncomputable def pairFrequencyEquiv : ℕ × ℕ ≃ (Sum ℕ ℕ) × ℕ := by
  let difference : ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) := {
    toFun := fun p =>
      if p.2 ≤ p.1 then Sum.inl (p.1 - p.2, p.2)
      else Sum.inr (p.2 - p.1 - 1, p.1)
    invFun := fun
      | Sum.inl (n, k) => (n + k, k)
      | Sum.inr (n, k) => (k, n + k + 1)
    left_inv := by
      rintro ⟨a, b⟩
      by_cases h : b ≤ a
      · simp [h]
      · simp [h]
        omega
    right_inv := by
      rintro (⟨n, k⟩ | ⟨n, k⟩)
      · simp
      · simp
        omega
  }
  exact difference.trans (Equiv.sumProdDistrib ℕ ℕ ℕ).symm

private noncomputable def pairFrequencyTerm (u v : ℂ)
    (x : (Sum ℕ ℕ) × ℕ) : ℂ :=
  exponentialSeriesTerm u (pairFrequencyEquiv.symm x).1 *
    exponentialSeriesTerm v (pairFrequencyEquiv.symm x).2

@[expose] noncomputable def wilsonBesselFrequencyTerm (h θ : ℝ) : Sum ℕ ℕ → ℂ
  | Sum.inl n => (modifiedBesselI n h : ℂ) *
      Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I))
  | Sum.inr n => (modifiedBesselI (n + 1) h : ℂ) *
      Complex.exp (-((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I))

private theorem exponentialSeriesTerm_summable (z : ℂ) :
    Summable (exponentialSeriesTerm z) := by
  change Summable (fun n : ℕ => z ^ n / (n.factorial : ℂ))
  exact (NormedSpace.expSeries_div_hasSum_exp z).summable

private theorem exponentialSeriesTerm_norm_summable (z : ℂ) :
    Summable (fun n : ℕ => ‖exponentialSeriesTerm z n‖) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖z‖) ?_
  intro n
  simp [exponentialSeriesTerm, norm_div, norm_pow]

private theorem pairFrequencyTerm_summable (u v : ℂ) :
    Summable (fun p : ℕ × ℕ => exponentialSeriesTerm u p.1 *
      exponentialSeriesTerm v p.2) := by
  have hu := exponentialSeriesTerm_norm_summable u
  have hv := exponentialSeriesTerm_norm_summable v
  have hnorm : Summable (fun p : ℕ × ℕ =>
      ‖exponentialSeriesTerm u p.1‖ * ‖exponentialSeriesTerm v p.2‖) := by
    apply (summable_prod_of_nonneg (f := fun p : ℕ × ℕ =>
      ‖exponentialSeriesTerm u p.1‖ * ‖exponentialSeriesTerm v p.2‖)
      (by intro p; positivity)).2
    constructor
    · intro n
      exact hv.mul_left ‖exponentialSeriesTerm u n‖
    · simpa only [tsum_mul_left] using
        hu.mul_right (∑' n, ‖exponentialSeriesTerm v n‖)
  exact Summable.of_norm_bounded hnorm (by intro p; simp)

private theorem pairFrequencyTerm_hasSum (u v : ℂ) :
    HasSum (pairFrequencyTerm u v) (Complex.exp u * Complex.exp v) := by
  have hp := pairFrequencyTerm_summable u v
  have hpair : HasSum
      (fun p : ℕ × ℕ => exponentialSeriesTerm u p.1 * exponentialSeriesTerm v p.2)
      (Complex.exp u * Complex.exp v) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp u).mul
      (NormedSpace.expSeries_div_hasSum_exp v) hp
    simpa only [exponentialSeriesTerm, Complex.exp_eq_exp_ℂ] using h
  have hsum : Summable (pairFrequencyTerm u v) := by
    change Summable
      ((fun p : ℕ × ℕ => exponentialSeriesTerm u p.1 *
        exponentialSeriesTerm v p.2) ∘ pairFrequencyEquiv.symm)
    exact (pairFrequencyEquiv.symm.summable_iff).2 hp
  have htsum : (∑' x, pairFrequencyTerm u v x) =
      Complex.exp u * Complex.exp v := by
    let f : ℕ × ℕ → ℂ := fun p =>
      exponentialSeriesTerm u p.1 * exponentialSeriesTerm v p.2
    calc
      (∑' x, f (pairFrequencyEquiv.symm x)) = ∑' p, f p :=
        pairFrequencyEquiv.symm.tsum_eq f
      _ = Complex.exp u * Complex.exp v := hpair.tsum_eq
  exact hsum.hasSum_iff.mpr htsum

private theorem complexBesselTerm_eq_real (n k : ℕ) (h : ℝ) :
    complexBesselTerm n k h = (modifiedBesselITerm n h k : ℂ) := by
  unfold complexBesselTerm modifiedBesselITerm
  push_cast
  ring

private theorem complexBesselI_eq_real (n : ℕ) (h : ℝ) :
    complexBesselI n h = (modifiedBesselI n h : ℂ) := by
  unfold complexBesselI modifiedBesselI
  calc
    (∑' k, complexBesselTerm n k h) =
        ∑' k, (modifiedBesselITerm n h k : ℂ) :=
      tsum_congr (fun k => complexBesselTerm_eq_real n k h)
    _ = ↑(∑' k, modifiedBesselITerm n h k) :=
      (Complex.ofReal_tsum _).symm

private theorem complexBesselTerm_summable (n : ℕ) (h : ℝ) :
    Summable (fun k => complexBesselTerm n k h) := by
  have hreal := summable_modifiedBesselITerm n h
  have hmap := Complex.ofRealCLM.summable hreal
  exact hmap.congr (fun k => (complexBesselTerm_eq_real n k h).symm)

private theorem complexBesselTerm_pair_left (h θ : ℝ) (n k : ℕ) :
    exponentialSeriesTerm ((h : ℂ) / 2 * positiveCharacter θ) (n + k) *
      exponentialSeriesTerm ((h : ℂ) / 2 * negativeCharacter θ) k =
    complexBesselTerm n k h *
      Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) := by
  unfold exponentialSeriesTerm complexBesselTerm positiveCharacter negativeCharacter
  rw [Complex.exp_neg]
  let c : ℂ := (h : ℂ) / 2
  let e : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have he : e ≠ 0 := Complex.exp_ne_zero _
  have hnum : (c * e) ^ (n + k) * (c * e⁻¹) ^ k =
      c ^ (n + 2 * k) * e ^ n := by
    rw [mul_pow, mul_pow]
    have heExp : e ^ (n + k) = e ^ n * e ^ k := pow_add e n k
    rw [heExp]
    have hePow : e ^ k * e⁻¹ ^ k = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ he, one_pow]
    have hcPow : c ^ (n + k) * c ^ k = c ^ (n + 2 * k) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      c ^ (n + k) * (e ^ n * e ^ k) * (c ^ k * e⁻¹ ^ k) =
          (c ^ (n + k) * c ^ k) * (e ^ n * (e ^ k * e⁻¹ ^ k)) := by ring
      _ = c ^ (n + 2 * k) * e ^ n := by rw [hePow, hcPow]; simp
  calc
    ((c * e) ^ (n + k) / ((n + k).factorial : ℂ)) *
        ((c * e⁻¹) ^ k / (k.factorial : ℂ)) =
        ((c * e) ^ (n + k) * (c * e⁻¹) ^ k) /
          (((n + k).factorial : ℂ) * (k.factorial : ℂ)) := by ring
    _ = (c ^ (n + 2 * k) * e ^ n) /
          (((n + k).factorial : ℂ) * (k.factorial : ℂ)) := by rw [hnum]
    _ = complexBesselTerm n k h *
          Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_nat_mul ((θ : ℂ) * Complex.I) n]
      dsimp [complexBesselTerm, c, e]
      ring

private theorem complexBesselTerm_pair_right (h θ : ℝ) (n k : ℕ) :
    exponentialSeriesTerm ((h : ℂ) / 2 * positiveCharacter θ) k *
      exponentialSeriesTerm ((h : ℂ) / 2 * negativeCharacter θ) (n + k + 1) =
    complexBesselTerm (n + 1) k h *
      Complex.exp (-((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) := by
  unfold exponentialSeriesTerm complexBesselTerm positiveCharacter negativeCharacter
  rw [Complex.exp_neg]
  let c : ℂ := (h : ℂ) / 2
  let e : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have he : e ≠ 0 := Complex.exp_ne_zero _
  have hePow : e ^ k * e⁻¹ ^ (n + k + 1) = e⁻¹ ^ (n + 1) := by
    rw [show n + k + 1 = k + (n + 1) by omega, pow_add]
    calc
      e ^ k * (e⁻¹ ^ k * e⁻¹ ^ (n + 1)) =
          (e ^ k * e⁻¹ ^ k) * e⁻¹ ^ (n + 1) := by ring
      _ = e⁻¹ ^ (n + 1) := by
        rw [← mul_pow, mul_inv_cancel₀ he]
        simp
  have hcPow : c ^ k * c ^ (n + k + 1) = c ^ (n + 1 + 2 * k) := by
    rw [← pow_add]
    congr 1
    omega
  have hnum : (c * e) ^ k * (c * e⁻¹) ^ (n + k + 1) =
      c ^ (n + 1 + 2 * k) * e⁻¹ ^ (n + 1) := by
    rw [mul_pow, mul_pow]
    calc
      c ^ k * e ^ k * (c ^ (n + k + 1) * e⁻¹ ^ (n + k + 1)) =
          (c ^ k * c ^ (n + k + 1)) * (e ^ k * e⁻¹ ^ (n + k + 1)) := by ring
      _ = c ^ (n + 1 + 2 * k) * e⁻¹ ^ (n + 1) := by rw [hcPow, hePow]
  calc
    ((c * e) ^ k / (k.factorial : ℂ)) *
        ((c * e⁻¹) ^ (n + k + 1) / ((n + k + 1).factorial : ℂ)) =
        ((c * e) ^ k * (c * e⁻¹) ^ (n + k + 1)) /
          ((k.factorial : ℂ) * ((n + k + 1).factorial : ℂ)) := by ring
    _ = (c ^ (n + 1 + 2 * k) * e⁻¹ ^ (n + 1)) /
          ((k.factorial : ℂ) * ((n + k + 1).factorial : ℂ)) := by rw [hnum]
    _ = complexBesselTerm (n + 1) k h *
          Complex.exp (-((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) := by
      have hfact : n + k + 1 = n + 1 + k := by omega
      rw [hfact]
      have heexp0 : e⁻¹ = Complex.exp (-((θ : ℂ) * Complex.I)) := by
        change (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ = _
        rw [Complex.exp_neg]
      have heexp : e⁻¹ ^ (n + 1) =
          Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I))) := by
        rw [heexp0, ← Complex.exp_nat_mul (-((θ : ℂ) * Complex.I)) (n + 1)]
        congr 1
        push_cast
        ring
      rw [heexp]
      dsimp [complexBesselTerm, c]
      ring_nf

private theorem pairFrequencyTerm_left (h θ : ℝ) (n k : ℕ) :
    pairFrequencyTerm ((h : ℂ) / 2 * positiveCharacter θ)
      ((h : ℂ) / 2 * negativeCharacter θ) (Sum.inl n, k) =
    complexBesselTerm n k h *
      Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) := by
  simpa [pairFrequencyTerm, pairFrequencyEquiv] using
    complexBesselTerm_pair_left h θ n k

private theorem pairFrequencyTerm_right (h θ : ℝ) (n k : ℕ) :
    pairFrequencyTerm ((h : ℂ) / 2 * positiveCharacter θ)
      ((h : ℂ) / 2 * negativeCharacter θ) (Sum.inr n, k) =
    complexBesselTerm (n + 1) k h *
      Complex.exp (-((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) := by
  simpa [pairFrequencyTerm, pairFrequencyEquiv] using
    complexBesselTerm_pair_right h θ n k

/-- The Wilson plaquette exponential has an absolutely summable
bilateral character expansion. The `Sum` index represents all integer
frequencies, while each coefficient is the modified Bessel series. -/
theorem wilsonBesselCharacterExpansion (h θ : ℝ) :
    HasSum (wilsonBesselFrequencyTerm h θ)
      (Complex.exp ((h : ℂ) * (Real.cos θ : ℂ))) := by
  let u : ℂ := (h : ℂ) / 2 * positiveCharacter θ
  let v : ℂ := (h : ℂ) / 2 * negativeCharacter θ
  let grouped : Sum ℕ ℕ → ℂ := fun m =>
    ∑' k : ℕ, pairFrequencyTerm u v (m, k)
  have hproduct := pairFrequencyTerm_hasSum u v
  have hgrouped : HasSum grouped (Complex.exp u * Complex.exp v) := by
    apply hproduct.prod_fiberwise
    intro m
    exact (hproduct.summable.comp_injective
      (i := fun k : ℕ => ((m, k) : (Sum ℕ ℕ) × ℕ))
      (by intro a b h; exact congrArg Prod.snd h)).hasSum
  have hgroupedEq : ∀ m, grouped m = wilsonBesselFrequencyTerm h θ m := by
    intro m
    cases m with
    | inl n =>
        calc
          grouped (Sum.inl n) =
              ∑' k : ℕ, complexBesselTerm n k h *
                Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) :=
            tsum_congr (fun k => by
              exact pairFrequencyTerm_left h θ n k)
          _ = wilsonBesselFrequencyTerm h θ (Sum.inl n) := by
            calc
              _ = (∑' k, complexBesselTerm n k h) *
                    Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) :=
                  (complexBesselTerm_summable n h).tsum_mul_right _
              _ = complexBesselI n h *
                    Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) := rfl
              _ = wilsonBesselFrequencyTerm h θ (Sum.inl n) := by
                  rw [complexBesselI_eq_real]
                  rfl
    | inr n =>
        calc
          grouped (Sum.inr n) =
              ∑' k : ℕ, complexBesselTerm (n + 1) k h *
                Complex.exp (-((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) :=
            tsum_congr (fun k => by
              exact pairFrequencyTerm_right h θ n k)
          _ = wilsonBesselFrequencyTerm h θ (Sum.inr n) := by
            calc
              _ = (∑' k, complexBesselTerm (n + 1) k h) *
                    Complex.exp (-((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) :=
                  (complexBesselTerm_summable (n + 1) h).tsum_mul_right _
              _ = complexBesselI (n + 1) h *
                    Complex.exp (-((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) := rfl
              _ = wilsonBesselFrequencyTerm h θ (Sum.inr n) := by
                  rw [complexBesselI_eq_real]
                  rfl
  have hbessel : Summable (wilsonBesselFrequencyTerm h θ) := by
    exact hgrouped.summable.congr hgroupedEq
  have hsum : (∑' m, wilsonBesselFrequencyTerm h θ m) =
      Complex.exp u * Complex.exp v := by
    calc
      (∑' m, wilsonBesselFrequencyTerm h θ m) = ∑' m, grouped m :=
        tsum_congr (fun m => (hgroupedEq m).symm)
      _ = Complex.exp u * Complex.exp v := hgrouped.tsum_eq
  have harg : u + v = (h : ℂ) * (Real.cos θ : ℂ) := by
    have hcos : Complex.exp ((θ : ℂ) * Complex.I) +
        Complex.exp (-((θ : ℂ) * Complex.I)) = 2 * (Real.cos θ : ℂ) := by
      rw [Complex.ofReal_cos]
      simp only [Complex.cos]
      ring_nf
    dsimp [u, v, positiveCharacter, negativeCharacter]
    calc
      (h : ℂ) / 2 * Complex.exp ((θ : ℂ) * Complex.I) +
          (h : ℂ) / 2 * Complex.exp (-((θ : ℂ) * Complex.I)) =
          ((h : ℂ) / 2) * (Complex.exp ((θ : ℂ) * Complex.I) +
            Complex.exp (-((θ : ℂ) * Complex.I))) := by ring
      _ = (h : ℂ) * (Real.cos θ : ℂ) := by rw [hcos]; ring
  have hsumValue : Complex.exp u * Complex.exp v =
      Complex.exp ((h : ℂ) * (Real.cos θ : ℂ)) := by
    rw [← Complex.exp_add, harg]
  exact hbessel.hasSum_iff.mpr (hsum.trans hsumValue)

/-- The normalized Fourier term for the clock factor. Its `Sum` index is a
signed mode; positive and negative modes are paired in
`wilsonNormalizedCharacterPair_eq_cos`. -/
@[expose] noncomputable def wilsonNormalizedFrequencyTerm
    (N : ℕ) (h θ : ℝ) (m : Sum ℕ ℕ) : ℂ :=
  wilsonBesselFrequencyTerm h ((N : ℝ) * θ) m /
    (modifiedBesselI 0 h : ℂ)

/-- The Bessel character expansion of the series-normalized Wilson clock
factor `exp(h cos(N θ)) / I₀(h)`. The identification of this normalization
with the source's integral definition of `ξ(h)` is a separate adapter. -/
theorem wilsonNormalizedBesselCharacterExpansion {N : ℕ} {h θ : ℝ}
    (hh : 0 ≤ h) :
    modifiedBesselI 0 h ≠ 0 ∧
      HasSum (wilsonNormalizedFrequencyTerm N h θ)
        (Complex.exp ((h : ℂ) * (Real.cos ((N : ℝ) * θ) : ℂ)) /
          (modifiedBesselI 0 h : ℂ)) := by
  have hI0 : 0 < modifiedBesselI 0 h :=
    lt_of_lt_of_le (by norm_num) (modifiedBesselI_zero_ge_one hh)
  have hsum := wilsonBesselCharacterExpansion h ((N : ℝ) * θ)
  have hscaled := hsum.mul_left ((modifiedBesselI 0 h : ℂ)⁻¹)
  refine ⟨ne_of_gt hI0, ?_⟩
  change HasSum (fun m => wilsonBesselFrequencyTerm h ((N : ℝ) * θ) m /
    (modifiedBesselI 0 h : ℂ)) _
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

private theorem complexBesselI_eq_ofReal (n : ℕ) (h : ℝ) :
    complexBesselI n h = (modifiedBesselI n h : ℂ) :=
  complexBesselI_eq_real n h

theorem positiveNegativeCharacters_eq_two_cos (n : ℕ) (θ : ℝ) :
    Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) +
        Complex.exp (-((n : ℂ) * ((θ : ℂ) * Complex.I))) =
      2 * (Real.cos ((n : ℝ) * θ) : ℂ) := by
  have he : (n : ℂ) * ((θ : ℂ) * Complex.I) =
      (((n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.ofReal_cos]
  simp only [Complex.cos]
  ring_nf

/-- Pairing the positive and negative Bessel modes gives the series cosine
coefficient `λ(q) cos(q N θ)`. Thus the `Sum`-indexed expansion above is the
bilateral form of (3.10), after the source integral normalization is identified
with `I₀(h)⁻¹`. -/
theorem wilsonNormalizedCharacterPair_eq_cos {N q : ℕ} {h θ : ℝ}
    (hq : 0 < q) :
    wilsonNormalizedFrequencyTerm N h θ (Sum.inl q) +
        wilsonNormalizedFrequencyTerm N h θ (Sum.inr (q - 1)) =
      (wilsonCharacterCoefficient N q h : ℂ) *
        (Real.cos ((q : ℝ) * ((N : ℝ) * θ)) : ℂ) := by
  have hqsub : q - 1 + 1 = q := by omega
  have hphase := positiveNegativeCharacters_eq_two_cos q ((N : ℝ) * θ)
  have hphase' :
      Complex.exp ((q : ℂ) * ((N : ℝ) * θ : ℂ) * Complex.I) +
        Complex.exp (-((q : ℂ) * ((N : ℝ) * θ : ℂ) * Complex.I)) =
      2 * (Real.cos ((q : ℝ) * ((N : ℝ) * θ)) : ℂ) := by
    simpa [mul_assoc] using hphase
  have hcoeff :
      ((modifiedBesselI q h : ℂ) / (modifiedBesselI 0 h : ℂ)) * 2 =
        (wilsonCharacterCoefficient N q h : ℂ) := by
    unfold wilsonCharacterCoefficient
    push_cast
    ring
  unfold wilsonNormalizedFrequencyTerm
  calc
    wilsonBesselFrequencyTerm h ((N : ℝ) * θ) (Sum.inl q) /
        (modifiedBesselI 0 h : ℂ) +
      wilsonBesselFrequencyTerm h ((N : ℝ) * θ) (Sum.inr (q - 1)) /
        (modifiedBesselI 0 h : ℂ) =
      ((modifiedBesselI q h : ℂ) / (modifiedBesselI 0 h : ℂ)) *
        (Complex.exp ((q : ℂ) * (((N : ℝ) * θ : ℝ) : ℂ) * Complex.I) +
          Complex.exp (-((q : ℂ) * (((N : ℝ) * θ : ℝ) : ℂ) * Complex.I))) := by
            simp [wilsonBesselFrequencyTerm, hqsub]
            ring_nf
    _ = ((modifiedBesselI q h : ℂ) / (modifiedBesselI 0 h : ℂ)) *
          (2 * (Real.cos ((q : ℝ) * ((N : ℝ) * θ)) : ℂ)) := by
            rw [Complex.ofReal_mul, hphase']
    _ = (wilsonCharacterCoefficient N q h : ℂ) *
          (Real.cos ((q : ℝ) * ((N : ℝ) * θ)) : ℂ) := by
            rw [← hcoeff]
            ring

/-- Each normalized factor in the geometric decomposition is exactly its
unweighted Fourier summand from (3.13). -/
theorem wilsonSplittingFactor_identity {epsilon x lambda : ℝ} {q : ℕ}
    (hζ : wilsonSplittingWeight epsilon q ≠ 0) :
    (wilsonSplittingWeight epsilon q)⁻¹ *
        (1 + wilsonSplittingWeight epsilon q * lambda * x) =
      (wilsonSplittingWeight epsilon q)⁻¹ + lambda * x := by
  field_simp [hζ]

theorem wilsonCharacterCoefficient_nonneg {N q : ℕ} {h : ℝ}
    (hh : 0 ≤ h) : 0 ≤ wilsonCharacterCoefficient N q h := by
  have hI : 0 ≤ modifiedBesselI q h := modifiedBesselI_nonneg hh
  have hI0 : 0 < modifiedBesselI 0 h :=
    lt_of_lt_of_le (by norm_num) (modifiedBesselI_zero_ge_one hh)
  unfold wilsonCharacterCoefficient
  exact div_nonneg (mul_nonneg (by norm_num) hI) (le_of_lt hI0)

/-- The one-sided cosine coefficient series is absolutely summable for every
nonnegative Wilson coupling. -/
theorem summable_wilsonCosineMode {N : ℕ} {h θ : ℝ} (hh : 0 ≤ h) :
    Summable (fun q : ℕ => wilsonCharacterCoefficient N (q + 1) h *
      Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ))) := by
  have hcoeff := summable_wilsonCharacterCoefficient (N := N) hh
  apply Summable.of_norm_bounded hcoeff
  intro q
  have hcoeffNonneg := wilsonCharacterCoefficient_nonneg hh (N := N) (q := q + 1)
  calc
    ‖wilsonCharacterCoefficient N (q + 1) h *
        Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ))‖ =
      |wilsonCharacterCoefficient N (q + 1) h| *
        |Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ))| := by
          simp [Real.norm_eq_abs]
    _ = wilsonCharacterCoefficient N (q + 1) h *
        |Real.cos (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ))| := by
          rw [abs_of_nonneg hcoeffNonneg]
    _ ≤ wilsonCharacterCoefficient N (q + 1) h := by
          nlinarith [Real.abs_cos_le_one
            (((q + 1 : ℕ) : ℝ) * ((N : ℝ) * θ)), hcoeffNonneg]

/-- Reweighting the absolutely summable cosine series by (3.12) gives the
countable mixture in (3.13). Each fixed frequency assignment can then be fed
to the finite separated-current API. -/
private theorem hasSum_weightedMixture {w a f : ℕ → ℝ}
    (hw : HasSum (fun q => (w q)⁻¹) 1)
    (ha : Summable (fun q => a q * f q))
    (hwne : ∀ q, w q ≠ 0) :
    HasSum (fun q => (w q)⁻¹ * (1 + w q * a q * f q))
      (1 + ∑' q, a q * f q) := by
  have hpoint : ∀ q, (w q)⁻¹ * (1 + w q * a q * f q) =
      (w q)⁻¹ + a q * f q := by
    intro q
    field_simp [hwne q]
  have hsum := hw.add ha.hasSum
  have hmix : Summable (fun q => (w q)⁻¹ * (1 + w q * a q * f q)) :=
    (hw.summable.add ha).congr (fun q => (hpoint q).symm)
  have hmixTsum : (∑' q, (w q)⁻¹ * (1 + w q * a q * f q)) =
      1 + ∑' q, a q * f q := by
    calc
      _ = ∑' q, ((w q)⁻¹ + a q * f q) := tsum_congr hpoint
      _ = 1 + ∑' q, a q * f q := hsum.tsum_eq
  exact hmix.hasSum_iff.mpr hmixTsum

/-- Reweighting the absolutely summable cosine series by (3.12) gives the
countable mixture in (3.13). Each fixed frequency assignment can then be fed
to the finite separated-current API. -/
theorem wilsonSplittingMixture_hasSum {epsilon : ℝ} {N : ℕ} {h : ℝ}
    (hepsilon : 0 < epsilon) (g : ℕ → ℝ)
    (hg : Summable (fun q : ℕ =>
      wilsonCharacterCoefficient N (q + 1) h * g q)) :
    HasSum (fun q : ℕ => (wilsonSplittingWeight epsilon q)⁻¹ *
      (1 + wilsonSplittingWeight epsilon q *
        wilsonCharacterCoefficient N (q + 1) h * g q))
      (1 + ∑' q : ℕ,
        wilsonCharacterCoefficient N (q + 1) h * g q) := by
  have hw := wilsonSplittingWeight_inv_tsum hepsilon
  have hwHas : HasSum (fun q => (wilsonSplittingWeight epsilon q)⁻¹) 1 :=
    hw.1.hasSum_iff.mpr hw.2
  simpa [mul_assoc] using
    (hasSum_weightedMixture hwHas hg (fun q =>
      (wilsonSplittingWeight_pos hepsilon).ne'))

end FroehlichSpencer.FS82.ZN

end
