/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Source-exact FS81 Theorem 7.1(2)

This module restores the threshold growth printed on FS81 J pp. 585–587 and makes the exponent
parameter uniform in the restricted harmonic. The threshold is enlarged by explicit terms tending
to infinity, while the clock factor representation bounds remain the source of the estimate. The exponent conversion uses
`β''(β,n,q) = n²/(2πc)` for the absolute the clock factor representation exponent `c`.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Source

private theorem decay_exponent_le {c : ℝ} (hc : 0 < c) {n ξ : ℕ} (hn : 0 < n)
    (hξn : ξ < n) :
    (ξ : ℝ) ^ 2 / (2 * Real.pi * ((n : ℝ) ^ 2 / (2 * Real.pi * c))) ≤ c := by
  have hξ : (ξ : ℝ) ≤ n := by exact_mod_cast hξn.le
  have hsq : (ξ : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hc' : c ≠ 0 := hc.ne'
  have hn' : (n : ℝ) ≠ 0 := hnR.ne'
  field_simp [Real.pi_ne_zero, hc']
  nlinarith

private theorem rpow_decay_weaken {x c a : ℝ} (hx : 1 ≤ x) (ha : a ≤ c) :
    x ^ (-c) ≤ x ^ (-a) :=
  Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg ha)

/--
**FS81 Theorem 7.1(2), source-exact form.** For every `q > 0` and `β ≥ 0` there is a size
threshold `n₀(β,q)` tending to infinity both as `β → ∞` (at fixed `q`) and as `q → 0⁺` (at fixed
`β`).

For `n ≥ n₀`, every restricted harmonic satisfies the printed power estimate on each finite
free box and in the free thermodynamic limit.

A single `β''(β,n,q)` works for all such harmonics;
we take `n²/(2πc)`, where `c` is the absolute the clock factor representation exponent.
-/
theorem clock_theorem71_2_source :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℝ → ℝ → ℕ, ∃ β'' : ℝ → ℕ → ℝ → ℝ,
      (∀ q : ℝ, 0 < q → Tendsto (fun β : ℝ => n₀ β q) atTop atTop) ∧
      (∀ β : ℝ, 0 ≤ β → Tendsto (fun q : ℝ => n₀ β q) (𝓝[>] 0) atTop) ∧
      (∀ β : ℝ, ∀ n : ℕ, ∀ q : ℝ, n₀ β q ≤ n → 0 < β'' β n q) ∧
      ∀ q : ℝ, 0 < q → ∀ (β : ℝ) (hβ : 0 ≤ β), ∀ n : ℕ, n₀ β q ≤ n →
        ∀ (hn : 0 < n) (ξ : ℕ), 0 < ξ → ξ < n →
          q ≤ dipoleGap ((ξ : ℝ) / n) →
          (∀ L : ℕ, ∀ u v : ℤ × ℤ, boxRadius u ≤ L → boxRadius v ≤ L →
            (clockModel n hn β hβ).twoPoint (ξ : ℤ) (freeBox L) u v ≤
              2 * ((l1Dist u v : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q)))) ∧
          ∀ u v : ℤ × ℤ,
            (clockModel n hn β hβ).twoPointLimit (ξ : ℤ) u v ≤
              2 * ((l1Dist u v : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q))) := by
  obtain ⟨c, hc, hfree⟩ := clock_twoPoint_freeBox_le
  let base : ℝ → ℝ → ℕ := fun β q =>
    if hβ : 0 ≤ β then
      if hq : 0 < q then Classical.choose (hfree q hq β hβ)
      else 1
    else 1
  let n₀ : ℝ → ℝ → ℕ := fun β q =>
    base β q + ⌈max β 0⌉₊ + ⌈(max q 0)⁻¹⌉₊
  let β'' : ℝ → ℕ → ℝ → ℝ := fun _ n _ => (n : ℝ) ^ 2 / (2 * Real.pi * c)
  have hβgrow (q : ℝ) : Tendsto (fun β : ℝ => n₀ β q) atTop atTop := by
    refine tendsto_atTop.2 fun K => ?_
    filter_upwards [eventually_ge_atTop (K : ℝ)] with β hK
    have hmax : (K : ℝ) ≤ max β 0 := hK.trans (le_max_left _ _)
    have hceilR : (K : ℝ) ≤ (⌈max β 0⌉₊ : ℝ) := hmax.trans (Nat.le_ceil _)
    have hceil : K ≤ ⌈max β 0⌉₊ := by exact_mod_cast hceilR
    dsimp [n₀]
    omega
  have hqgrow (β : ℝ) : Tendsto (fun q : ℝ => n₀ β q) (𝓝[>] 0) atTop := by
    have hinv : Tendsto (fun q : ℝ => q⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have hpos : ∀ᶠ q : ℝ in 𝓝[>] (0 : ℝ), 0 < q := by
      exact self_mem_nhdsWithin
    refine tendsto_atTop.2 fun K => ?_
    filter_upwards [hpos, hinv.eventually_ge_atTop (K : ℝ)] with q hq hqinv
    have hmax : max q 0 = q := max_eq_left hq.le
    have hceilR : (K : ℝ) ≤ (⌈q⁻¹⌉₊ : ℝ) := hqinv.trans (Nat.le_ceil _)
    have hceil : K ≤ ⌈q⁻¹⌉₊ := by exact_mod_cast hceilR
    have hceilMax : K ≤ ⌈(max q 0)⁻¹⌉₊ := by simpa [hmax] using hceil
    have : K ≤ n₀ β q := by
      dsimp [n₀]
      omega
    exact this
  refine ⟨c, hc, n₀, β'', (fun q _ => hβgrow q), (fun β _ => hqgrow β), ?_, ?_⟩
  · intro β n q hn
    have hbase : base β q ≤ n := by dsimp [n₀] at hn; omega
    have hbasePos : 0 < base β q := by
      by_cases hβ : 0 ≤ β
      · by_cases hq : 0 < q
        · have heq : base β q = Classical.choose (hfree q hq β hβ) := by
            simp [base, hβ, hq]
          rw [heq]
          exact (Classical.choose_spec (hfree q hq β hβ)).1
        · simp [base, hβ, hq]
      · simp [base, hβ]
    have hnpos : 0 < n := lt_of_lt_of_le hbasePos hbase
    simp only [β'']
    exact div_pos (sq_pos_of_pos (by exact_mod_cast hnpos)) (by positivity)
  · intro q hq β hβ n hn hnpos ξ hξ0 hξn hqξ
    have hbase : base β q ≤ n := by dsimp [n₀] at hn; omega
    have hbaseEq : base β q = Classical.choose (hfree q hq β hβ) := by
      simp [base, hβ, hq]
    have hbaseSpec := Classical.choose_spec (hfree q hq β hβ)
    have hbound := hbaseSpec.2 n (hbaseEq ▸ hbase) hnpos hβ ξ hξ0 hξn hqξ
    have hα : (ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q) ≤ c := by
      simpa [β''] using decay_exponent_le hc hnpos hξn
    have hfinite (u v : ℤ × ℤ) (L : ℕ) (hu : boxRadius u ≤ L) (hv : boxRadius v ≤ L) :
        (clockModel n hnpos β hβ).twoPoint (ξ : ℤ) (freeBox L) u v ≤
          2 * ((l1Dist u v : ℝ) + 1) ^
            (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q))) := by
      have hd : 0 ≤ (l1Dist u v : ℝ) := by exact_mod_cast Nat.zero_le (l1Dist u v)
      have hx : 1 ≤ (l1Dist u v : ℝ) + 1 := by linarith
      have hp := rpow_decay_weaken hx hα
      have hscale : 2 * ((l1Dist u v : ℝ) + 1) ^ (-c) ≤
          2 * ((l1Dist u v : ℝ) + 1) ^
            (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q))) :=
        mul_le_mul_of_nonneg_left hp (by norm_num)
      exact (hbound L u v hu hv).trans hscale
    constructor
    · intro L u v hu hv
      exact hfinite u v L hu hv
    · intro u v
      refine le_of_tendsto ((clockModel n hnpos β hβ).tendsto_twoPointLimit (ξ : ℤ) u v) ?_
      filter_upwards [eventually_ge_atTop (max (boxRadius u) (boxRadius v))] with L hL
      exact hfinite u v L ((le_max_left _ _).trans hL) ((le_max_right _ _).trans hL)

end FroehlichSpencer.BKT.Clock.Source

end
