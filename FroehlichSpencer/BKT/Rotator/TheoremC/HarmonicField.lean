/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.FreeBox
public import FroehlichSpencer.BKT.Rotator.CurrentIntegration
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import FroehlichSpencer.BKT.Rotator.FreeBoxBijection
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The harmonic field of a two-point mark (explicit, logarithmic energy)

Instead of the potential-kernel asymptotics this module uses
an explicit flow:

* `j` is the L-shaped lattice path `a → (x₁, a₂) → x`;
* along a straight segment of length `R` the unit flow is spread, on the `c`-th bond layer,
  uniformly over the `2 w_c + 1` bonds within distance `w_c = min(c, R − 1 − c)` of the segment
  (`flowH`), and redistributed between consecutive layers by the cumulative differences
  (`flowV`); the stream function is the cumulative distribution minus the step function of the
  segment (`strm`), so the correction `σ = 2π · strm` is explicit and vanishes away from the
  segment (in particular on the exterior face);
* the energy of one segment is at most `12 (1 + log(1 + R))` (`sum_flow_sq_le`).

The main theorem is `exists_harmonicField`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

open Finset FroehlichSpencer.BKT.Duality FroehlichSpencer.BKT.Lattice2D

/-! ## The layer profiles on `ℤ²` -/

/-- The half-width `w_c = min(c, R − 1 − c)` of the `c`-th layer. -/
def wdt (R : ℕ) (c : ℤ) : ℕ := (min c ((R : ℤ) - 1 - c)).toNat

/-- The distribution function of the uniform law on `{−w, …, w}`. -/
def cdf (w : ℕ) (y : ℤ) : ℝ :=
  if y < -(w : ℤ) then 0 else if (w : ℤ) ≤ y then 1 else ((y + w + 1 : ℤ) : ℝ) / (2 * w + 1)

/-- The stream function of the spread segment: the layer distribution function minus the step of
the segment. -/
def strm (R : ℕ) (c y : ℤ) : ℝ :=
  if 0 ≤ c ∧ c < R then cdf (wdt R c) y - (if 0 ≤ y then 1 else 0) else 0

/-- The straight segment current on the layer row `y = 0`. -/
def jlay (R : ℕ) (c y : ℤ) : ℤ :=
  if 0 ≤ c ∧ c < R ∧ y = 0 then 1 else 0

/-- The flow across the layer bonds: `j + ∂_y strm`. -/
def flowH (R : ℕ) (c y : ℤ) : ℝ :=
  (jlay R c y : ℝ) + strm R c y - strm R c (y - 1)

/-- The flow between consecutive layers: `−∂_c strm`. -/
def flowV (R : ℕ) (c y : ℤ) : ℝ :=
  strm R (c - 1) y - strm R c y

theorem cdf_eq_of_mem {w : ℕ} {y : ℤ} (h₁ : -(w : ℤ) - 1 ≤ y) (h₂ : y ≤ w) :
    cdf w y = ((y + w + 1 : ℤ) : ℝ) / (2 * w + 1) := by
  have hpos : (0 : ℝ) < 2 * w + 1 := by positivity
  unfold cdf
  split_ifs with ha hb
  · have : y + w + 1 = 0 := by omega
    rw [this, Int.cast_zero, zero_div]
  · have : y = w := by omega
    rw [this]
    push_cast
    field_simp
    ring
  · rfl

theorem cdf_zero (y : ℤ) : cdf 0 y = if 0 ≤ y then 1 else 0 := by
  unfold cdf
  split_ifs <;> first | rfl | omega

theorem cdf_sub (w : ℕ) (y : ℤ) :
    cdf w y - cdf w (y - 1) = if -(w : ℤ) ≤ y ∧ y ≤ w then 1 / (2 * (w : ℝ) + 1) else 0 := by
  have hpos : (0 : ℝ) < 2 * w + 1 := by positivity
  by_cases hlo : y < -(w : ℤ)
  · have h1 : cdf w y = 0 := by unfold cdf; rw [ite_eq_left hlo]
    have h2 : cdf w (y - 1) = 0 := by unfold cdf; rw [ite_eq_left (by omega)]
    rw [h1, h2, ite_eq_right (by omega), sub_zero]
  · by_cases hhi : (w : ℤ) < y
    · have h1 : cdf w y = 1 := by unfold cdf; rw [ite_eq_right hlo, ite_eq_left (by omega)]
      have h2 : cdf w (y - 1) = 1 := by
        unfold cdf; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      rw [h1, h2, ite_eq_right (by omega), sub_self]
    · rw [cdf_eq_of_mem (by omega) (by omega), cdf_eq_of_mem (by omega) (by omega),
        ite_eq_left (by omega)]
      push_cast
      field_simp
      ring

/-- Consecutive uniform laws: the distribution functions differ by at most `1/(2a+1)`, and only on
`{−a−1, …, a}`. -/
theorem abs_cdf_sub_succ_le (a : ℕ) (y : ℤ) :
    |cdf a y - cdf (a + 1) y| ≤ 1 / (2 * (a : ℝ) + 1) := by
  have hpos : (0 : ℝ) < 2 * a + 1 := by positivity
  by_cases hlo : y < -(a : ℤ) - 1
  · have h1 : cdf a y = 0 := by unfold cdf; rw [ite_eq_left (by omega)]
    have h2 : cdf (a + 1) y = 0 := by unfold cdf; rw [ite_eq_left (by push_cast; omega)]
    rw [h1, h2, sub_zero, abs_zero]
    positivity
  · by_cases hhi : (a : ℤ) < y
    · have h1 : cdf a y = 1 := by unfold cdf; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      have h2 : cdf (a + 1) y = 1 := by
        unfold cdf; rw [ite_eq_right (by push_cast; omega), ite_eq_left (by push_cast; omega)]
      rw [h1, h2, sub_self, abs_zero]
      positivity
    · rw [cdf_eq_of_mem (by omega) (by omega),
        cdf_eq_of_mem (w := a + 1) (by push_cast; omega) (by push_cast; omega)]
      have hy₁ : ((-(a : ℤ) - 1 : ℤ) : ℝ) ≤ (y : ℝ) := by
        exact_mod_cast (by omega : -(a : ℤ) - 1 ≤ y)
      have hy₂ : (y : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : y ≤ (a : ℤ))
      push_cast at hy₁ ⊢
      have h3 : (0 : ℝ) < 2 * (a : ℝ) + 3 := by positivity
      have hd : ((y : ℝ) + a + 1) / (2 * a + 1) - ((y : ℝ) + (a + 1) + 1) / (2 * (a + 1) + 1) =
          (2 * y + 1) / ((2 * a + 1) * (2 * a + 3)) := by
        field_simp
        ring
      rw [hd, abs_div, abs_of_pos (mul_pos hpos h3), div_le_div_iff₀ (mul_pos hpos h3) hpos,
        one_mul]
      have hab : |2 * (y : ℝ) + 1| ≤ 2 * a + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h0 : 0 ≤ |2 * (y : ℝ) + 1| := abs_nonneg _
      nlinarith

theorem cdf_sub_succ_eq_zero {a : ℕ} {y : ℤ} (h : y < -(a : ℤ) - 1 ∨ (a : ℤ) < y) :
    cdf a y - cdf (a + 1) y = 0 := by
  rcases h with h | h
  · have h1 : cdf a y = 0 := by unfold cdf; rw [ite_eq_left (by omega)]
    have h2 : cdf (a + 1) y = 0 := by unfold cdf; rw [ite_eq_left (by push_cast; omega)]
    rw [h1, h2, sub_zero]
  · have h1 : cdf a y = 1 := by unfold cdf; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    have h2 : cdf (a + 1) y = 1 := by
      unfold cdf; rw [ite_eq_right (by push_cast; omega), ite_eq_left (by push_cast; omega)]
    rw [h1, h2, sub_self]

theorem wdt_eq {R : ℕ} {c : ℤ} (h0 : 0 ≤ c) (hR : c < R) :
    (wdt R c : ℤ) = min c ((R : ℤ) - 1 - c) := by
  unfold wdt
  rw [Int.toNat_of_nonneg (le_min h0 (by omega))]

theorem strm_of_mem {R : ℕ} {c : ℤ} (h0 : 0 ≤ c) (hR : c < R) (y : ℤ) :
    strm R c y = cdf (wdt R c) y - (if 0 ≤ y then 1 else 0) := by
  unfold strm; rw [ite_eq_left ⟨h0, hR⟩]

theorem strm_of_not_mem {R : ℕ} {c : ℤ} (h : ¬ (0 ≤ c ∧ c < R)) (y : ℤ) : strm R c y = 0 := by
  unfold strm; rw [ite_eq_right h]

/-- The stream function vanishes away from the segment. -/
theorem strm_ne_zero {R : ℕ} {c y : ℤ} (h : strm R c y ≠ 0) :
    0 ≤ c ∧ c < R ∧ -(R : ℤ) < y ∧ y < R := by
  by_cases hc : 0 ≤ c ∧ c < R
  · refine ⟨hc.1, hc.2, ?_⟩
    rw [strm_of_mem hc.1 hc.2] at h
    have hw := wdt_eq hc.1 hc.2
    have hwR : (wdt R c : ℤ) < R := by rw [hw]; omega
    by_contra hy
    apply h
    by_cases hlo : y < -(wdt R c : ℤ)
    · unfold cdf; rw [ite_eq_left hlo, ite_eq_right (by omega), sub_zero]
    · have hhi : (wdt R c : ℤ) ≤ y := by omega
      unfold cdf; rw [ite_eq_right hlo, ite_eq_left hhi, ite_eq_left (by omega), sub_self]
  · exact absurd (strm_of_not_mem hc y) h

theorem flowH_eq (R : ℕ) (c y : ℤ) :
    flowH R c y = if 0 ≤ c ∧ c < R ∧ -(wdt R c : ℤ) ≤ y ∧ y ≤ wdt R c then
      1 / (2 * (wdt R c : ℝ) + 1) else 0 := by
  have key := cdf_sub (wdt R c) y
  unfold flowH jlay strm
  split_ifs at key ⊢ <;> push_cast <;> first | linarith | (exfalso; omega)

theorem flowV_of_out {R : ℕ} {c : ℤ} (h : c ≤ 0 ∨ (R : ℤ) ≤ c) (y : ℤ) : flowV R c y = 0 := by
  have hzero : ∀ c' : ℤ, (0 ≤ c' ∧ c' < (R : ℤ)) → (wdt R c' = 0) → strm R c' y = 0 := by
    intro c' hc' hw
    rw [strm_of_mem hc'.1 hc'.2, hw, cdf_zero, sub_self]
  unfold flowV
  rcases h with h | h
  · rw [strm_of_not_mem (by omega : ¬ (0 ≤ c - 1 ∧ c - 1 < R))]
    by_cases hc : 0 ≤ c ∧ c < R
    · rw [hzero c hc (by unfold wdt; omega), sub_self]
    · rw [strm_of_not_mem hc, sub_self]
  · rw [strm_of_not_mem (by omega : ¬ (0 ≤ c ∧ c < R))]
    by_cases hc : 0 ≤ c - 1 ∧ c - 1 < R
    · rw [hzero (c - 1) hc (by unfold wdt; omega), sub_self]
    · rw [strm_of_not_mem hc, sub_self]

/-- Between interior layers the flow is a difference of consecutive uniform distribution
functions. -/
theorem flowV_bound {R : ℕ} {c : ℤ} (h1 : 1 ≤ c) (h2 : c ≤ (R : ℤ) - 1) (m : ℕ)
    (hm : (m : ℤ) = min (c - 1) ((R : ℤ) - 1 - c)) (y : ℤ) :
    |flowV R c y| ≤ 1 / (2 * (m : ℝ) + 1) ∧
      (flowV R c y ≠ 0 → -(m : ℤ) - 1 ≤ y ∧ y ≤ m) := by
  have hpos : (0 : ℝ) < 2 * m + 1 := by positivity
  have e1 := wdt_eq (R := R) (c := c - 1) (by omega) (by omega)
  have e2 := wdt_eq (R := R) (c := c) (by omega) (by omega)
  have hV : flowV R c y = cdf (wdt R (c - 1)) y - cdf (wdt R c) y := by
    unfold flowV
    rw [strm_of_mem (by omega) (by omega), strm_of_mem (by omega) (by omega)]
    ring
  rw [hV]
  rcases lt_trichotomy (2 * c) R with hlt | heq | hgt
  · have ha : wdt R (c - 1) = m := by omega
    have hb : wdt R c = m + 1 := by omega
    rw [ha, hb]
    refine ⟨abs_cdf_sub_succ_le m y, fun hne => ?_⟩
    by_contra hy
    exact hne (cdf_sub_succ_eq_zero (by omega))
  · have ha : wdt R (c - 1) = wdt R c := by omega
    rw [ha, sub_self, abs_zero]
    exact ⟨by positivity, fun h => absurd rfl h⟩
  · have ha : wdt R (c - 1) = m + 1 := by omega
    have hb : wdt R c = m := by omega
    rw [ha, hb, abs_sub_comm]
    refine ⟨abs_cdf_sub_succ_le m y, fun hne => ?_⟩
    by_contra hy
    exact hne (by rw [← neg_sub, cdf_sub_succ_eq_zero (by omega), neg_zero])

theorem sum_flowH_sq {R : ℕ} {k : ℕ} (hk : k < R) :
    ∑ y ∈ Icc (-(R : ℤ)) R, flowH R k y ^ 2 = 1 / (2 * (wdt R k : ℝ) + 1) := by
  set w := wdt R k with hw
  have hwR : (w : ℤ) ≤ (R : ℤ) - 1 := by
    rw [hw, wdt_eq (by positivity) (by exact_mod_cast hk)]; omega
  have hpos : (0 : ℝ) < 2 * w + 1 := by positivity
  have hsub : Icc (-(w : ℤ)) w ⊆ Icc (-(R : ℤ)) R := Icc_subset_Icc (by omega) (by omega)
  rw [← sum_subset hsub fun y _ hy => by
    rw [flowH_eq, ite_eq_right (by rw [mem_Icc] at hy; omega)]; ring]
  rw [sum_congr rfl fun y hy => by
    rw [flowH_eq, ite_eq_left (by rw [mem_Icc] at hy; exact ⟨by omega, by exact_mod_cast hk,
      hy.1, hy.2⟩)]]
  rw [sum_const, Int.card_Icc, nsmul_eq_mul]
  have hc : ((((w : ℤ) + 1 - -(w : ℤ)).toNat : ℕ) : ℝ) = 2 * w + 1 := by
    rw [show (w : ℤ) + 1 - -(w : ℤ) = ((2 * w + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
    push_cast; ring
  rw [hc, ← hw]
  field_simp

theorem sum_flowV_sq_le {R : ℕ} {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ R) (m : ℕ)
    (hm : (m : ℤ) = min ((k : ℤ) - 1) ((R : ℤ) - 1 - k)) :
    ∑ y ∈ Icc (-(R : ℤ)) R, flowV R k y ^ 2 ≤ 2 / (2 * (m : ℝ) + 1) := by
  have hpos : (0 : ℝ) < 2 * m + 1 := by positivity
  have hb := fun y => flowV_bound (R := R) (c := k) (by exact_mod_cast hk1) (by omega) m hm y
  have hsub : Icc (-(m : ℤ) - 1) m ⊆ Icc (-(R : ℤ)) R := Icc_subset_Icc (by omega) (by omega)
  rw [← sum_subset hsub fun y _ hy => by
    have h := (hb y).2
    rw [mem_Icc] at hy
    by_contra hne
    exact hy (h (by intro h0; exact hne (by rw [h0]; ring)))]
  calc ∑ y ∈ Icc (-(m : ℤ) - 1) m, flowV R k y ^ 2
      ≤ ∑ _y ∈ Icc (-(m : ℤ) - 1) m, (1 / (2 * (m : ℝ) + 1)) ^ 2 := by
        refine sum_le_sum fun y _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb y).1 2
    _ = (2 * m + 2) * (1 / (2 * (m : ℝ) + 1)) ^ 2 := by
        rw [sum_const, Int.card_Icc, nsmul_eq_mul]
        congr 1
        rw [show (m : ℤ) + 1 - (-(m : ℤ) - 1) = ((2 * m + 2 : ℕ) : ℤ) by push_cast; ring,
          Int.toNat_natCast]
        push_cast; ring
    _ ≤ 2 / (2 * (m : ℝ) + 1) := by
        rw [div_pow, one_pow, ← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) hpos]
        nlinarith

/-- The column bound: `∑_y (flowH² + flowV²) ≤ 6/(k+1) + 6/(R−k)` on the layer `k < R`. -/
theorem column_le {R : ℕ} {k : ℕ} (hk : k < R) :
    ∑ y ∈ Icc (-(R : ℤ)) R, (flowH R k y ^ 2 + flowV R k y ^ 2) ≤
      6 / ((k : ℝ) + 1) + 6 / ((R : ℝ) - k) := by
  have hRk : (1 : ℝ) ≤ (R : ℝ) - k := by
    have : ((k + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hk
    push_cast at this; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hA : 0 < (k : ℝ) + 1 := by positivity
  have hB : 0 < (R : ℝ) - k := by linarith
  rw [sum_add_distrib, sum_flowH_sq hk]
  -- the layer term
  have hw := wdt_eq (R := R) (c := k) (by positivity) (by exact_mod_cast hk)
  have hH : 1 / (2 * (wdt R k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) + 1 / ((R : ℝ) - k) := by
    rcases min_choice (k : ℤ) ((R : ℤ) - 1 - k) with h | h
    · have hwk : (wdt R k : ℝ) = k := by exact_mod_cast (hw.trans h)
      rw [hwk]
      have : 1 / (2 * (k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le hA (by linarith)
      have : 0 ≤ 1 / ((R : ℝ) - k) := by positivity
      linarith
    · have hwk : (wdt R k : ℝ) = (R : ℝ) - 1 - k := by
        have h' := hw.trans h
        have : ((wdt R k : ℤ) : ℝ) = (((R : ℤ) - 1 - k : ℤ) : ℝ) := by rw [h']
        push_cast at this; exact this
      rw [hwk]
      have : 1 / (2 * ((R : ℝ) - 1 - k) + 1) ≤ 1 / ((R : ℝ) - k) :=
        one_div_le_one_div_of_le hB (by linarith)
      have : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
  -- the redistribution term
  have hV : ∑ y ∈ Icc (-(R : ℤ)) R, flowV R k y ^ 2 ≤ 4 / ((k : ℝ) + 1) + 4 / ((R : ℝ) - k) := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [sum_eq_zero fun y _ => by rw [flowV_of_out (Or.inl (by simp)) y]; ring]
      positivity
    · set m := (min ((k : ℤ) - 1) ((R : ℤ) - 1 - k)).toNat with hmdef
      have hm : (m : ℤ) = min ((k : ℤ) - 1) ((R : ℤ) - 1 - k) := by
        rw [hmdef, Int.toNat_of_nonneg (le_min (by omega) (by omega))]
      refine (sum_flowV_sq_le h0 hk m hm).trans ?_
      rcases min_choice ((k : ℤ) - 1) ((R : ℤ) - 1 - k) with h | h
      · have hmk : (m : ℝ) = k - 1 := by
          have : ((m : ℤ) : ℝ) = (((k : ℤ) - 1 : ℤ) : ℝ) := by rw [hm, h]
          push_cast at this; exact this
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast h0
        rw [hmk]
        have : 2 / (2 * ((k : ℝ) - 1) + 1) ≤ 4 / ((k : ℝ) + 1) := by
          rw [div_le_div_iff₀ (by linarith) hA]; nlinarith
        have : 0 ≤ 4 / ((R : ℝ) - k) := by positivity
        linarith
      · have hmk : (m : ℝ) = (R : ℝ) - 1 - k := by
          have : ((m : ℤ) : ℝ) = (((R : ℤ) - 1 - k : ℤ) : ℝ) := by rw [hm, h]
          push_cast at this; exact this
        rw [hmk]
        have : 2 / (2 * ((R : ℝ) - 1 - k) + 1) ≤ 4 / ((R : ℝ) - k) := by
          rw [div_le_div_iff₀ (by linarith) hB]; nlinarith
        have : 0 ≤ 4 / ((k : ℝ) + 1) := by positivity
        linarith
  have e1 : 6 / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) + 5 / ((k : ℝ) + 1) := by ring
  have e2 : 6 / ((R : ℝ) - k) = 1 / ((R : ℝ) - k) + 5 / ((R : ℝ) - k) := by ring
  have : 4 / ((k : ℝ) + 1) ≤ 5 / ((k : ℝ) + 1) := div_le_div_of_nonneg_right (by norm_num) hA.le
  have : 4 / ((R : ℝ) - k) ≤ 5 / ((R : ℝ) - k) := div_le_div_of_nonneg_right (by norm_num) hB.le
  linarith

/-- The block of `ℤ²` carrying one spread segment of length `R`. -/
def blk (R : ℕ) : Finset (ℤ × ℤ) :=
  ((range (R + 1)).image fun k : ℕ => (k : ℤ)) ×ˢ Icc (-(R : ℤ)) R

theorem mem_blk_of_flowH_ne_zero {R : ℕ} {c y : ℤ} (h : flowH R c y ≠ 0) : (c, y) ∈ blk R := by
  rw [flowH_eq] at h
  split_ifs at h with hc
  · have hw := wdt_eq (R := R) hc.1 hc.2.1
    have hwR : (wdt R c : ℤ) ≤ (R : ℤ) - 1 := by rw [hw]; omega
    refine mem_product.mpr ⟨mem_image.mpr ⟨c.toNat, mem_range.mpr (by omega), by omega⟩,
      mem_Icc.mpr ⟨by omega, by omega⟩⟩
  · exact absurd rfl h

theorem mem_blk_of_flowV_ne_zero {R : ℕ} {c y : ℤ} (h : flowV R c y ≠ 0) : (c, y) ∈ blk R := by
  by_cases hc : c ≤ 0 ∨ (R : ℤ) ≤ c
  · exact absurd (flowV_of_out hc y) h
  · have hm : (((min (c - 1) ((R : ℤ) - 1 - c)).toNat : ℕ) : ℤ) = min (c - 1) ((R : ℤ) - 1 - c) :=
      Int.toNat_of_nonneg (le_min (by omega) (by omega))
    have hs := (flowV_bound (R := R) (c := c) (by omega) (by omega) _ hm y).2 h
    refine mem_product.mpr ⟨mem_image.mpr ⟨c.toNat, mem_range.mpr (by omega), by omega⟩,
      mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem sum_inv_range_le_log (R : ℕ) :
    ∑ k ∈ range R, 1 / ((k : ℝ) + 1) ≤ 1 + Real.log (1 + R) := by
  have h := harmonic_le_one_add_log R
  have hcast : ((harmonic R : ℚ) : ℝ) = ∑ k ∈ range R, 1 / ((k : ℝ) + 1) := by
    unfold harmonic
    push_cast
    simp only [one_div]
  rw [hcast] at h
  refine h.trans ?_
  have : Real.log R ≤ Real.log (1 + R) := by
    rcases Nat.eq_zero_or_pos R with h0 | h0
    · subst h0; simp
    · exact Real.log_le_log (by exact_mod_cast h0) (by linarith)
  linarith

/-- **The energy of one spread segment** of length `R`. -/
theorem sum_flow_sq_le (R : ℕ) :
    ∑ z ∈ blk R, (flowH R z.1 z.2 ^ 2 + flowV R z.1 z.2 ^ 2) ≤ 12 * (1 + Real.log (1 + R)) := by
  unfold blk
  rw [sum_product, sum_image fun a _ b _ h => by exact_mod_cast h, sum_range_succ]
  have hlast : ∑ y ∈ Icc (-(R : ℤ)) R, (flowH R (R : ℕ) y ^ 2 + flowV R (R : ℕ) y ^ 2) = 0 := by
    refine sum_eq_zero fun y _ => ?_
    rw [flowV_of_out (Or.inr le_rfl), flowH_eq, ite_eq_right (by omega)]
    ring
  rw [hlast, add_zero]
  calc ∑ k ∈ range R, ∑ y ∈ Icc (-(R : ℤ)) R, (flowH R (k : ℤ) y ^ 2 + flowV R (k : ℤ) y ^ 2)
      ≤ ∑ k ∈ range R, (6 / ((k : ℝ) + 1) + 6 / ((R : ℝ) - k)) :=
        sum_le_sum fun k hk => column_le (mem_range.mp hk)
    _ = 12 * ∑ k ∈ range R, 1 / ((k : ℝ) + 1) := by
        rw [sum_add_distrib]
        have hrefl : ∑ k ∈ range R, 6 / ((R : ℝ) - k) = ∑ k ∈ range R, 6 / ((k : ℝ) + 1) := by
          rw [← sum_range_reflect (fun k : ℕ => 6 / ((k : ℝ) + 1)) R]
          refine sum_congr rfl fun k hk => ?_
          have hk := mem_range.mp hk
          congr 1
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          push_cast; ring
        rw [hrefl, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun k _ => by ring
    _ ≤ 12 * (1 + Real.log (1 + R)) :=
        mul_le_mul_of_nonneg_left (sum_inv_range_le_log R) (by norm_num)

/-! ## Currents and face fields on the free box from formulas on `ℤ²` -/

/-- A current on the box bonds: `JH x y` on the horizontal bond `(x,y) → (x+1,y)` and `JV x y` on
the vertical bond `(x,y) → (x,y+1)`. -/
def boxCurrent (L : ℕ) (JH JV : ℤ → ℤ → ℤ) : RotatorInternalBond L → ℤ
  | .inl e => JH ((e.1.1 : ℕ) : ℤ) ((e.2 : ℕ) : ℤ)
  | .inr e => JV ((e.1 : ℕ) : ℤ) ((e.2.1 : ℕ) : ℤ)

/-- A face field: `S p q` on the bounded face with lower-left corner `(p,q)`, zero on the exterior
face. -/
def boxField (L : ℕ) (S : ℤ → ℤ → ℝ) : RotatorDualFace L → ℝ
  | none => 0
  | some p => S ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ)

theorem div_boxCurrent {L : ℕ} {JH JV : ℤ → ℤ → ℤ}
    (hJH : ∀ x y, JH x y ≠ 0 → 0 ≤ x ∧ x < L) (hJV : ∀ x y, JV x y ≠ 0 → 0 ≤ y ∧ y < L)
    (v : RotatorSpinSite L) :
    rotatorCurrentDivergence (boxCurrent L JH JV) v =
      JH ((v.1 : ℕ) : ℤ) ((v.2 : ℕ) : ℤ) + JV ((v.1 : ℕ) : ℤ) ((v.2 : ℕ) : ℤ) -
        JH ((v.1 : ℕ) - 1 : ℤ) ((v.2 : ℕ) : ℤ) - JV ((v.1 : ℕ) : ℤ) ((v.2 : ℕ) - 1 : ℤ) := by
  rcases v with ⟨x, y⟩
  have hx := x.isLt
  have hy := y.isLt
  rw [rotatorCurrentDivergence_formula]
  simp only [rotatorHorizontalCurrent, rotatorVerticalCurrent, boxCurrent, horizontalDualEdgeData,
    verticalDualEdgeData, Fin.val_castLE]
  have e1 : (if hx : x.val < L then JH (x.val : ℤ) (y.val : ℤ) else 0) = JH x.val y.val := by
    split_ifs with h
    · rfl
    · by_contra hne; have := hJH _ _ (Ne.symm hne); omega
  have e2 : (if hy : y.val < L then JV (x.val : ℤ) (y.val : ℤ) else 0) = JV x.val y.val := by
    split_ifs with h
    · rfl
    · by_contra hne; have := hJV _ _ (Ne.symm hne); omega
  have e3 : (if hx : 0 < x.val then JH ((x.val - 1 : ℕ) : ℤ) (y.val : ℤ) else 0) =
      JH ((x.val : ℤ) - 1) y.val := by
    split_ifs with h
    · rw [Nat.cast_sub (by omega), Nat.cast_one]
    · by_contra hne; have := hJH _ _ (Ne.symm hne); omega
  have e4 : (if hy : 0 < y.val then JV (x.val : ℤ) ((y.val - 1 : ℕ) : ℤ) else 0) =
      JV x.val ((y.val : ℤ) - 1) := by
    split_ifs with h
    · rw [Nat.cast_sub (by omega), Nat.cast_one]
    · by_contra hne; have := hJV _ _ (Ne.symm hne); omega
  rw [e1, e2, e3, e4]

theorem grad_boxField_inl {L : ℕ} {S : ℤ → ℤ → ℝ}
    (hS : ∀ p q, S p q ≠ 0 → 0 ≤ p ∧ p < L ∧ 0 ≤ q ∧ q < L)
    (e : SquareFreeHorizontalEdge (L + 1)) :
    (rotatorDualGraph L).grad (boxField L S) (.inl e) =
      S ((e.1.1 : ℕ) : ℤ) ((e.2 : ℕ) : ℤ) - S ((e.1.1 : ℕ) : ℤ) ((e.2 : ℕ) - 1 : ℤ) := by
  have hi := e.1.2
  have hk := e.2.isLt
  simp only [Multigraph.grad, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt,
    horizontalPrimalSrc, horizontalPrimalTgt, horizontalFaceX]
  have e1 : boxField L S (if h : (e.2 : ℕ) < L then some (⟨(e.1.1 : ℕ), by omega⟩, ⟨e.2, h⟩)
      else none) = S ((e.1.1 : ℕ) : ℤ) ((e.2 : ℕ) : ℤ) := by
    split_ifs with h
    · rfl
    · by_contra hne; have := hS _ _ (Ne.symm hne); omega
  have e2 : boxField L S (if h : (e.2 : ℕ) = 0 then none else
      some (⟨(e.1.1 : ℕ), by omega⟩, ⟨(e.2 : ℕ) - 1, by omega⟩)) =
      S ((e.1.1 : ℕ) : ℤ) ((e.2 : ℕ) - 1 : ℤ) := by
    split_ifs with h
    · by_contra hne; have := hS _ _ (Ne.symm hne); omega
    · simp only [boxField]
      rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [e1, e2]

theorem grad_boxField_inr {L : ℕ} {S : ℤ → ℤ → ℝ}
    (hS : ∀ p q, S p q ≠ 0 → 0 ≤ p ∧ p < L ∧ 0 ≤ q ∧ q < L)
    (e : SquareFreeVerticalEdge (L + 1)) :
    (rotatorDualGraph L).grad (boxField L S) (.inr e) =
      S ((e.1 : ℕ) - 1 : ℤ) ((e.2.1 : ℕ) : ℤ) - S ((e.1 : ℕ) : ℤ) ((e.2.1 : ℕ) : ℤ) := by
  have hi := e.1.isLt
  have hk := e.2.2
  simp only [Multigraph.grad, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt,
    verticalPrimalSrc, verticalPrimalTgt, verticalFaceY]
  have e1 : boxField L S (if h : (e.1 : ℕ) = 0 then none else
      some (⟨(e.1 : ℕ) - 1, by omega⟩, ⟨(e.2.1 : ℕ), by omega⟩)) =
      S ((e.1 : ℕ) - 1 : ℤ) ((e.2.1 : ℕ) : ℤ) := by
    split_ifs with h
    · by_contra hne; have := hS _ _ (Ne.symm hne); omega
    · simp only [boxField]
      rw [Nat.cast_sub (by omega), Nat.cast_one]
  have e2 : boxField L S (if h : (e.1 : ℕ) < L then some (⟨(e.1 : ℕ), h⟩, ⟨(e.2.1 : ℕ), by omega⟩)
      else none) = S ((e.1 : ℕ) : ℤ) ((e.2.1 : ℕ) : ℤ) := by
    split_ifs with h
    · rfl
    · by_contra hne; have := hS _ _ (Ne.symm hne); omega
  rw [e1, e2]

/-- Summing a nonnegative function of injective lattice coordinates over a finite type. -/
theorem sum_comp_le_of_injective {α : Type*} [Fintype α] (κ : α → ℤ × ℤ)
    (hκ : Function.Injective κ) (G : ℤ × ℤ → ℝ) (hG : ∀ z, 0 ≤ G z) (B : Finset (ℤ × ℤ))
    (hB : ∀ z, G z ≠ 0 → z ∈ B) : ∑ a, G (κ a) ≤ ∑ z ∈ B, G z := by
  classical
  rw [← sum_image fun a _ b _ h => hκ h, ← sum_filter_of_ne (p := fun z => z ∈ B)
    fun z _ hz => hB z hz]
  exact sum_le_sum_of_subset_of_nonneg (fun z hz => (mem_filter.mp hz).2) fun z _ _ => hG z

/-! ## Straight segments -/

/-- The direction of a segment from `u` to `u'`. -/
def segSign (u u' : ℤ) : ℤ := if u ≤ u' then 1 else -1

/-- The length of a segment from `u` to `u'`. -/
def segLen (u u' : ℤ) : ℕ := (u' - u).natAbs

theorem segSign_sq (u u' : ℤ) : ((segSign u u' : ℤ) : ℝ) ^ 2 = 1 := by
  unfold segSign; split_ifs <;> norm_num

theorem jlay_sub (R : ℕ) (c y : ℤ) :
    jlay R c y - jlay R (c - 1) y =
      (if c = 0 ∧ y = 0 then 1 else 0) - (if c = R ∧ y = 0 then 1 else 0) := by
  unfold jlay; split_ifs <;> omega

/-- The horizontal straight current from column `u` to column `u'` on row `y₀`. -/
def hJ (u u' y₀ : ℤ) (x y : ℤ) : ℤ :=
  segSign u u' * jlay (segLen u u') (x - min u u') (y - y₀)

/-- Its spreading correction (`2π` times the stream function). -/
def hS (u u' y₀ : ℤ) (p q : ℤ) : ℝ :=
  2 * Real.pi * segSign u u' * strm (segLen u u') (p - min u u') (q - y₀)

/-- The vertical straight current from row `u` to row `u'` on column `x₀`. -/
def vJ (u u' x₀ : ℤ) (x y : ℤ) : ℤ :=
  segSign u u' * jlay (segLen u u') (y - min u u') (x - x₀)

/-- Its spreading correction. -/
def vS (u u' x₀ : ℤ) (p q : ℤ) : ℝ :=
  -(2 * Real.pi * segSign u u' * strm (segLen u u') (q - min u u') (p - x₀))

theorem hJ_div (u u' y₀ x y : ℤ) :
    hJ u u' y₀ x y - hJ u u' y₀ (x - 1) y =
      (if x = u ∧ y = y₀ then 1 else 0) - (if x = u' ∧ y = y₀ then 1 else 0) := by
  unfold hJ
  rw [← mul_sub, show x - 1 - min u u' = x - min u u' - 1 by ring, jlay_sub]
  unfold segSign segLen
  split_ifs <;> omega

theorem vJ_div (u u' x₀ x y : ℤ) :
    vJ u u' x₀ x y - vJ u u' x₀ x (y - 1) =
      (if x = x₀ ∧ y = u then 1 else 0) - (if x = x₀ ∧ y = u' then 1 else 0) := by
  unfold vJ
  rw [← mul_sub, show y - 1 - min u u' = y - min u u' - 1 by ring, jlay_sub]
  unfold segSign segLen
  split_ifs <;> omega

theorem hJ_ne_zero {u u' y₀ x y : ℤ} (h : hJ u u' y₀ x y ≠ 0) :
    min u u' ≤ x ∧ x < max u u' ∧ y = y₀ := by
  unfold hJ jlay segLen at h
  split_ifs at h with hc
  · omega
  · simp at h

theorem vJ_ne_zero {u u' x₀ x y : ℤ} (h : vJ u u' x₀ x y ≠ 0) :
    min u u' ≤ y ∧ y < max u u' ∧ x = x₀ := by
  unfold vJ jlay segLen at h
  split_ifs at h with hc
  · omega
  · simp at h

theorem hS_ne_zero {u u' y₀ p q : ℤ} (h : hS u u' y₀ p q ≠ 0) :
    min u u' ≤ p ∧ p < max u u' ∧ y₀ - |u' - u| < q ∧ q < y₀ + |u' - u| := by
  have h' : strm (segLen u u') (p - min u u') (q - y₀) ≠ 0 := by
    intro h0; apply h; unfold hS; rw [h0, mul_zero]
  have := strm_ne_zero h'
  unfold segLen at this
  rw [Int.natCast_natAbs] at this
  constructor <;> [skip; constructor <;> [skip; constructor]] <;>
    rcases abs_cases (u' - u) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

theorem vS_ne_zero {u u' x₀ p q : ℤ} (h : vS u u' x₀ p q ≠ 0) :
    min u u' ≤ q ∧ q < max u u' ∧ x₀ - |u' - u| < p ∧ p < x₀ + |u' - u| := by
  have h' : strm (segLen u u') (q - min u u') (p - x₀) ≠ 0 := by
    intro h0; apply h; unfold vS; rw [h0, mul_zero, neg_zero]
  have := strm_ne_zero h'
  unfold segLen at this
  rw [Int.natCast_natAbs] at this
  constructor <;> [skip; constructor <;> [skip; constructor]] <;>
    rcases abs_cases (u' - u) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

theorem hFlowH (u u' y₀ x y : ℤ) :
    2 * Real.pi * (hJ u u' y₀ x y : ℝ) + hS u u' y₀ x y - hS u u' y₀ x (y - 1) =
      2 * Real.pi * segSign u u' * flowH (segLen u u') (x - min u u') (y - y₀) := by
  unfold hJ hS flowH
  rw [show y - 1 - y₀ = y - y₀ - 1 by ring]
  push_cast
  ring

theorem hFlowV (u u' y₀ x y : ℤ) :
    hS u u' y₀ (x - 1) y - hS u u' y₀ x y =
      2 * Real.pi * segSign u u' * flowV (segLen u u') (x - min u u') (y - y₀) := by
  unfold hS flowV
  rw [show x - 1 - min u u' = x - min u u' - 1 by ring]
  ring

theorem vFlowH (u u' x₀ x y : ℤ) :
    2 * Real.pi * (vJ u u' x₀ x y : ℝ) + vS u u' x₀ (x - 1) y - vS u u' x₀ x y =
      2 * Real.pi * segSign u u' * flowH (segLen u u') (y - min u u') (x - x₀) := by
  unfold vJ vS flowH
  rw [show x - 1 - x₀ = x - x₀ - 1 by ring]
  push_cast
  ring

theorem vFlowV (u u' x₀ x y : ℤ) :
    vS u u' x₀ x y - vS u u' x₀ x (y - 1) =
      2 * Real.pi * segSign u u' * flowV (segLen u u') (y - min u u') (x - x₀) := by
  unfold vS flowV
  rw [show y - 1 - min u u' = y - min u u' - 1 by ring]
  ring

/-! ## The harmonic field -/

/-- The `ℓ¹` distance of two spin sites of the box. -/
def siteL1 {L : ℕ} (a x : RotatorSpinSite L) : ℕ :=
  Int.natAbs ((a.1 : ℕ) - (x.1 : ℕ) : ℤ) + Int.natAbs ((a.2 : ℕ) - (x.2 : ℕ) : ℤ)

theorem sq_add_le_of_flows {A B f g : ℝ} {s t : ℤ} (hs : ((s : ℤ) : ℝ) ^ 2 = 1)
    (ht : ((t : ℤ) : ℝ) ^ 2 = 1) (hA : A = 2 * Real.pi * s * f) (hB : B = 2 * Real.pi * t * g) :
    (A + B) ^ 2 ≤ 8 * Real.pi ^ 2 * (f ^ 2 + g ^ 2) := by
  have h2 : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (A - B)]
  have hA2 : A ^ 2 = 4 * Real.pi ^ 2 * f ^ 2 := by
    rw [hA, show (2 * Real.pi * s * f) ^ 2 = 4 * Real.pi ^ 2 * f ^ 2 * ((s : ℤ) : ℝ) ^ 2 by ring,
      hs, mul_one]
  have hB2 : B ^ 2 = 4 * Real.pi ^ 2 * g ^ 2 := by
    rw [hB, show (2 * Real.pi * t * g) ^ 2 = 4 * Real.pi ^ 2 * g ^ 2 * ((t : ℤ) : ℝ) ^ 2 by ring,
      ht, mul_one]
  rw [hA2, hB2] at h2
  linarith

theorem injective_horizontal_coords {L : ℕ} {f : ℤ × ℤ → ℤ × ℤ} (hf : Function.Injective f) :
    Function.Injective fun h : SquareFreeHorizontalEdge (L + 1) =>
      f (((h.1.1 : ℕ) : ℤ), ((h.2 : ℕ) : ℤ)) := by
  intro h h' heq
  have := Prod.ext_iff.mp (hf heq)
  simp only [Nat.cast_inj] at this
  exact Prod.ext (Subtype.ext (Fin.ext this.1)) (Fin.ext this.2)

theorem injective_vertical_coords {L : ℕ} {f : ℤ × ℤ → ℤ × ℤ} (hf : Function.Injective f) :
    Function.Injective fun h : SquareFreeVerticalEdge (L + 1) =>
      f (((h.1 : ℕ) : ℤ), ((h.2.1 : ℕ) : ℤ)) := by
  intro h h' heq
  have := Prod.ext_iff.mp (hf heq)
  simp only [Nat.cast_inj] at this
  exact Prod.ext (Fin.ext this.1) (Subtype.ext (Fin.ext this.2))

theorem injective_shift (c d : ℤ) : Function.Injective fun z : ℤ × ℤ => (z.1 - c, z.2 - d) := by
  intro z z' h
  have := Prod.ext_iff.mp h
  exact Prod.ext (by linarith [this.1]) (by linarith [this.2])

theorem injective_swap_shift (c d : ℤ) :
    Function.Injective fun z : ℤ × ℤ => (z.2 - d, z.1 - c) := by
  intro z z' h
  have := Prod.ext_iff.mp h
  exact Prod.ext (by linarith [this.2]) (by linarith [this.1])

/-- **The harmonic field of a two-point mark** (explicit, logarithmic energy). -/
theorem exists_harmonicField : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (L : ℕ) (a x : RotatorSpinSite L),
    siteL1 a x + 1 ≤ (a.1 : ℕ) → (a.1 : ℕ) + siteL1 a x + 1 ≤ L →
    siteL1 a x + 1 ≤ (a.2 : ℕ) → (a.2 : ℕ) + siteL1 a x + 1 ≤ L →
    siteL1 a x + 1 ≤ (x.1 : ℕ) → (x.1 : ℕ) + siteL1 a x + 1 ≤ L →
    siteL1 a x + 1 ≤ (x.2 : ℕ) → (x.2 : ℕ) + siteL1 a x + 1 ≤ L →
    ∃ (j : RotatorInternalBond L → ℤ) (σ : RotatorDualFace L → ℝ),
      (∀ v, rotatorCurrentDivergence j v = rotatorTwoPointFrequency a x 1 v) ∧ σ none = 0 ∧
      ∑ e, (2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e) ^ 2 ≤
        C₀ * (1 + Real.log (1 + (siteL1 a x : ℝ))) := by
  refine ⟨192 * Real.pi ^ 2, by positivity, ?_⟩
  intro L a x h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨a₁, ha₁⟩ : ∃ t : ℤ, t = ((a.1 : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ t : ℤ, t = ((a.2 : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨x₁, hx₁⟩ : ∃ t : ℤ, t = ((x.1 : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ t : ℤ, t = ((x.2 : ℕ) : ℤ) := ⟨_, rfl⟩
  have hRsum : ((segLen a₁ x₁ : ℕ) : ℤ) + ((segLen a₂ x₂ : ℕ) : ℤ) = (siteL1 a x : ℤ) := by
    unfold segLen siteL1; omega
  have habs₁ : |x₁ - a₁| = ((segLen a₁ x₁ : ℕ) : ℤ) := by
    unfold segLen; rw [Int.natCast_natAbs]
  have habs₂ : |x₂ - a₂| = ((segLen a₂ x₂ : ℕ) : ℤ) := by
    unfold segLen; rw [Int.natCast_natAbs]
  have hJHs : ∀ p q, hJ a₁ x₁ a₂ p q ≠ 0 → 0 ≤ p ∧ p < L := fun p q h => by
    have := hJ_ne_zero h; omega
  have hJVs : ∀ p q, vJ a₂ x₂ x₁ p q ≠ 0 → 0 ≤ q ∧ q < L := fun p q h => by
    have := vJ_ne_zero h; omega
  have hSs : ∀ p q, hS a₁ x₁ a₂ p q + vS a₂ x₂ x₁ p q ≠ 0 →
      0 ≤ p ∧ p < L ∧ 0 ≤ q ∧ q < L := fun p q h => by
    by_cases hh : hS a₁ x₁ a₂ p q = 0
    · have hv : vS a₂ x₂ x₁ p q ≠ 0 := by intro hv; apply h; rw [hh, hv, add_zero]
      have := vS_ne_zero hv
      rw [habs₂] at this
      omega
    · have := hS_ne_zero hh
      rw [habs₁] at this
      omega
  refine ⟨boxCurrent L (hJ a₁ x₁ a₂) (vJ a₂ x₂ x₁),
    boxField L fun p q => hS a₁ x₁ a₂ p q + vS a₂ x₂ x₁ p q, fun v => ?_, rfl, ?_⟩
  · -- the divergence
    rw [div_boxCurrent hJHs hJVs v]
    have hh := hJ_div a₁ x₁ a₂ ((v.1 : ℕ) : ℤ) ((v.2 : ℕ) : ℤ)
    have hv := vJ_div a₂ x₂ x₁ ((v.1 : ℕ) : ℤ) ((v.2 : ℕ) : ℤ)
    have hva : v = a ↔ ((v.1 : ℕ) : ℤ) = a₁ ∧ ((v.2 : ℕ) : ℤ) = a₂ := by
      rw [ha₁, ha₂, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff, Nat.cast_inj, Nat.cast_inj]
    have hvx : v = x ↔ ((v.1 : ℕ) : ℤ) = x₁ ∧ ((v.2 : ℕ) : ℤ) = x₂ := by
      rw [hx₁, hx₂, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff, Nat.cast_inj, Nat.cast_inj]
    unfold rotatorTwoPointFrequency
    simp only [hva, hvx]
    split_ifs at hh hv ⊢ <;> omega
  · -- the energy
    have hs₁ := segSign_sq a₁ x₁
    have hs₂ := segSign_sq a₂ x₂
    rw [Fintype.sum_sum_type]
    have hH : ∀ h : SquareFreeHorizontalEdge (L + 1),
        (2 * Real.pi * (boxCurrent L (hJ a₁ x₁ a₂) (vJ a₂ x₂ x₁) (.inl h) : ℝ) +
          (rotatorDualGraph L).grad
            (boxField L fun p q => hS a₁ x₁ a₂ p q + vS a₂ x₂ x₁ p q) (.inl h)) ^ 2 ≤
        8 * Real.pi ^ 2 *
          (flowH (segLen a₁ x₁) (((h.1.1 : ℕ) : ℤ) - min a₁ x₁) (((h.2 : ℕ) : ℤ) - a₂) ^ 2 +
            flowV (segLen a₂ x₂) (((h.2 : ℕ) : ℤ) - min a₂ x₂) (((h.1.1 : ℕ) : ℤ) - x₁) ^ 2) := by
      intro h
      rw [grad_boxField_inl hSs]
      simp only [boxCurrent]
      refine sq_add_le_of_flows (A := 2 * Real.pi * (hJ a₁ x₁ a₂ (h.1.1 : ℕ) (h.2 : ℕ) : ℝ) +
          hS a₁ x₁ a₂ (h.1.1 : ℕ) (h.2 : ℕ) - hS a₁ x₁ a₂ (h.1.1 : ℕ) ((h.2 : ℕ) - 1))
        (B := vS a₂ x₂ x₁ (h.1.1 : ℕ) (h.2 : ℕ) - vS a₂ x₂ x₁ (h.1.1 : ℕ) ((h.2 : ℕ) - 1))
        hs₁ hs₂ (hFlowH _ _ _ _ _) (vFlowV _ _ _ _ _) |>.trans_eq' ?_
      ring
    have hV : ∀ h : SquareFreeVerticalEdge (L + 1),
        (2 * Real.pi * (boxCurrent L (hJ a₁ x₁ a₂) (vJ a₂ x₂ x₁) (.inr h) : ℝ) +
          (rotatorDualGraph L).grad
            (boxField L fun p q => hS a₁ x₁ a₂ p q + vS a₂ x₂ x₁ p q) (.inr h)) ^ 2 ≤
        8 * Real.pi ^ 2 *
          (flowV (segLen a₁ x₁) (((h.1 : ℕ) : ℤ) - min a₁ x₁) (((h.2.1 : ℕ) : ℤ) - a₂) ^ 2 +
            flowH (segLen a₂ x₂) (((h.2.1 : ℕ) : ℤ) - min a₂ x₂) (((h.1 : ℕ) : ℤ) - x₁) ^ 2) := by
      intro h
      rw [grad_boxField_inr hSs]
      simp only [boxCurrent]
      refine sq_add_le_of_flows
        (A := hS a₁ x₁ a₂ ((h.1 : ℕ) - 1) (h.2.1 : ℕ) - hS a₁ x₁ a₂ (h.1 : ℕ) (h.2.1 : ℕ))
        (B := 2 * Real.pi * (vJ a₂ x₂ x₁ (h.1 : ℕ) (h.2.1 : ℕ) : ℝ) +
          vS a₂ x₂ x₁ ((h.1 : ℕ) - 1) (h.2.1 : ℕ) - vS a₂ x₂ x₁ (h.1 : ℕ) (h.2.1 : ℕ))
        hs₁ hs₂ (hFlowV _ _ _ _ _) (vFlowH _ _ _ _ _) |>.trans_eq' ?_
      ring
    -- reindex the four flow sums into the blocks
    have hGH : ∀ R : ℕ, ∀ z : ℤ × ℤ, flowH R z.1 z.2 ^ 2 ≠ 0 → z ∈ blk R := fun R z hz =>
      mem_blk_of_flowH_ne_zero (fun h0 => hz (by rw [h0]; ring))
    have hGV : ∀ R : ℕ, ∀ z : ℤ × ℤ, flowV R z.1 z.2 ^ 2 ≠ 0 → z ∈ blk R := fun R z hz =>
      mem_blk_of_flowV_ne_zero (fun h0 => hz (by rw [h0]; ring))
    have s1 := sum_comp_le_of_injective _
      (injective_horizontal_coords (L := L) (injective_shift (min a₁ x₁) a₂))
      (fun z => flowH (segLen a₁ x₁) z.1 z.2 ^ 2) (fun _ => sq_nonneg _) _ (hGH _)
    have s2 := sum_comp_le_of_injective _
      (injective_horizontal_coords (L := L) (injective_swap_shift x₁ (min a₂ x₂)))
      (fun z => flowV (segLen a₂ x₂) z.1 z.2 ^ 2) (fun _ => sq_nonneg _) _ (hGV _)
    have s3 := sum_comp_le_of_injective _
      (injective_vertical_coords (L := L) (injective_shift (min a₁ x₁) a₂))
      (fun z => flowV (segLen a₁ x₁) z.1 z.2 ^ 2) (fun _ => sq_nonneg _) _ (hGV _)
    have s4 := sum_comp_le_of_injective _
      (injective_vertical_coords (L := L) (injective_swap_shift x₁ (min a₂ x₂)))
      (fun z => flowH (segLen a₂ x₂) z.1 z.2 ^ 2) (fun _ => sq_nonneg _) _ (hGH _)
    simp only at s1 s2 s3 s4
    have b1 := sum_flow_sq_le (segLen a₁ x₁)
    have b2 := sum_flow_sq_le (segLen a₂ x₂)
    rw [sum_add_distrib] at b1 b2
    have hlog : ∀ n : ℕ, n ≤ siteL1 a x →
        Real.log (1 + (n : ℝ)) ≤ Real.log (1 + (siteL1 a x : ℝ)) := fun n hn =>
      Real.log_le_log (by positivity) (by have : (n : ℝ) ≤ siteL1 a x := by exact_mod_cast hn
                                          linarith)
    have l1 := hlog (segLen a₁ x₁) (by omega)
    have l2 := hlog (segLen a₂ x₂) (by omega)
    have hpi : 0 ≤ 8 * Real.pi ^ 2 := by positivity
    calc ∑ h : SquareFreeHorizontalEdge (L + 1),
          (2 * Real.pi * (boxCurrent L (hJ a₁ x₁ a₂) (vJ a₂ x₂ x₁) (.inl h) : ℝ) +
            (rotatorDualGraph L).grad
              (boxField L fun p q => hS a₁ x₁ a₂ p q + vS a₂ x₂ x₁ p q) (.inl h)) ^ 2 +
        ∑ h : SquareFreeVerticalEdge (L + 1),
          (2 * Real.pi * (boxCurrent L (hJ a₁ x₁ a₂) (vJ a₂ x₂ x₁) (.inr h) : ℝ) +
            (rotatorDualGraph L).grad
              (boxField L fun p q => hS a₁ x₁ a₂ p q + vS a₂ x₂ x₁ p q) (.inr h)) ^ 2
        ≤ ∑ h : SquareFreeHorizontalEdge (L + 1), 8 * Real.pi ^ 2 *
            (flowH (segLen a₁ x₁) (((h.1.1 : ℕ) : ℤ) - min a₁ x₁) (((h.2 : ℕ) : ℤ) - a₂) ^ 2 +
              flowV (segLen a₂ x₂) (((h.2 : ℕ) : ℤ) - min a₂ x₂) (((h.1.1 : ℕ) : ℤ) - x₁) ^ 2) +
          ∑ h : SquareFreeVerticalEdge (L + 1), 8 * Real.pi ^ 2 *
            (flowV (segLen a₁ x₁) (((h.1 : ℕ) : ℤ) - min a₁ x₁) (((h.2.1 : ℕ) : ℤ) - a₂) ^ 2 +
              flowH (segLen a₂ x₂) (((h.2.1 : ℕ) : ℤ) - min a₂ x₂) (((h.1 : ℕ) : ℤ) - x₁) ^ 2) :=
          add_le_add (sum_le_sum fun h _ => hH h) (sum_le_sum fun h _ => hV h)
      _ = 8 * Real.pi ^ 2 *
            ((∑ h : SquareFreeHorizontalEdge (L + 1), flowH (segLen a₁ x₁)
                (((h.1.1 : ℕ) : ℤ) - min a₁ x₁) (((h.2 : ℕ) : ℤ) - a₂) ^ 2 +
              ∑ h : SquareFreeVerticalEdge (L + 1), flowV (segLen a₁ x₁)
                (((h.1 : ℕ) : ℤ) - min a₁ x₁) (((h.2.1 : ℕ) : ℤ) - a₂) ^ 2) +
             (∑ h : SquareFreeVerticalEdge (L + 1), flowH (segLen a₂ x₂)
                (((h.2.1 : ℕ) : ℤ) - min a₂ x₂) (((h.1 : ℕ) : ℤ) - x₁) ^ 2 +
              ∑ h : SquareFreeHorizontalEdge (L + 1), flowV (segLen a₂ x₂)
                (((h.2 : ℕ) : ℤ) - min a₂ x₂) (((h.1.1 : ℕ) : ℤ) - x₁) ^ 2)) := by
          rw [← mul_sum, ← mul_sum, ← mul_add, sum_add_distrib, sum_add_distrib]
          ring
      _ ≤ 8 * Real.pi ^ 2 * (12 * (1 + Real.log (1 + (segLen a₁ x₁ : ℝ))) +
            12 * (1 + Real.log (1 + (segLen a₂ x₂ : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hpi
          · linarith
          · linarith
      _ ≤ 192 * Real.pi ^ 2 * (1 + Real.log (1 + (siteL1 a x : ℝ))) := by
          nlinarith

end FroehlichSpencer.BKT.Rotator.TheoremC

end
