/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.Theorem71
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Source-exact FS81 Theorem 7.1(2) for the Villain clock

This module exports the threshold growth and the parameter-dependent exponent printed in FS81
Theorem 7.1(2), (7.3)–(7.4), for Remark 4's Villain-constrained clock.

The threshold is enlarged
from the uniform marked bound by terms diverging as β → ∞ and q → 0⁺.

One `β''(β,n,q)` is used for
all restricted harmonics and for finite squares, centred free boxes, and the free thermodynamic
limit.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.VillainClock
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

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
**FS81 Theorem 7.1(2), source-exact Villain-clock form.** For every `q > 0` and `β > 0`,
there is a threshold `n₀(β,q)` tending to infinity both as `β → ∞` at fixed `q` and as
`q → 0⁺` at fixed `β`.

For `n ≥ n₀`, every restricted integer harmonic has the printed power
bound on finite squares, centred free boxes, and the free thermodynamic limit.

The exponent
parameter `β''(β,n,q)` is shared over all such harmonics.
-/
theorem villain_clock_theorem71_2_source :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℝ → ℝ → ℕ, ∃ β'' : ℝ → ℕ → ℝ → ℝ,
      (∀ q : ℝ, 0 < q → Tendsto (fun β : ℝ => n₀ β q) atTop atTop) ∧
      (∀ β : ℝ, Tendsto (fun q : ℝ => n₀ β q) (𝓝[>] 0) atTop) ∧
      (∀ β : ℝ, ∀ n : ℕ, ∀ q : ℝ, n₀ β q ≤ n → 0 < β'' β n q) ∧
      ∀ q : ℝ, 0 < q → ∀ (β : ℝ) (hβ : 0 < β), ∀ n : ℕ, n₀ β q ≤ n →
        ∀ (hn : 0 < n) (ξ : ℕ), 0 < ξ → ξ < n →
          q ≤ dipoleGap ((ξ : ℝ) / n) →
          ((∀ L : ℕ, ∀ a b : RotatorSpinSite L,
            (model n hn β hβ).twoPoint (ξ : ℤ) (squareBoxZ L) (siteToZ a) (siteToZ b) ≤
              2 * ((Lattice2D.freeRadius a b : ℝ) + 1) ^
                (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q)))) ∧
           (∀ L : ℕ, ∀ u v : ℤ × ℤ, boxRadius u ≤ L → boxRadius v ≤ L →
              (model n hn β hβ).twoPoint (ξ : ℤ) (freeBox L) u v ≤
                2 * ((l1Dist u v : ℝ) + 1) ^
                  (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q))))) ∧
          (∀ u v : ℤ × ℤ,
            (model n hn β hβ).twoPointLimit (ξ : ℤ) u v ≤
              2 * ((l1Dist u v : ℝ) + 1) ^
                (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q)))) := by
  obtain ⟨c, hc, hsquare⟩ := villain_twoPoint_squareBox_le
  let base : ℝ → ℝ → ℕ := fun β q =>
    if hβ : 0 < β then
      if hq : 0 < q then Classical.choose (hsquare q hq β hβ)
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
  refine ⟨c, hc, n₀, β'', (fun q _ => hβgrow q), hqgrow, ?_, ?_⟩
  · intro β n q hn
    have hbase : base β q ≤ n := by dsimp [n₀] at hn; omega
    have hbasePos : 0 < base β q := by
      by_cases hβ : 0 < β
      · by_cases hq : 0 < q
        · have heq : base β q = Classical.choose (hsquare q hq β hβ) := by
            simp [base, hβ, hq]
          rw [heq]
          exact (Classical.choose_spec (hsquare q hq β hβ)).1
        · simp [base, hβ, hq]
      · simp [base, hβ]
    have hnpos : 0 < n := lt_of_lt_of_le hbasePos hbase
    simp only [β'']
    exact div_pos (sq_pos_of_pos (by exact_mod_cast hnpos)) (by positivity)
  · intro q hq β hβ n hn hnpos ξ hξ0 hξn hqξ
    have hbase : base β q ≤ n := by dsimp [n₀] at hn; omega
    have hbaseEq : base β q = Classical.choose (hsquare q hq β hβ) := by
      simp [base, hβ, hq]
    have hbaseSpec := Classical.choose_spec (hsquare q hq β hβ)
    have hbound := hbaseSpec.2 n (hbaseEq ▸ hbase) hnpos hβ ξ hξ0 hξn hqξ
    have hα : (ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q) ≤ c := by
      simpa [β''] using decay_exponent_le hc hnpos hξn
    have hweak {x : ℝ} (hx : 1 ≤ x) :
        2 * x ^ (-c) ≤ 2 * x ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q))) := by
      exact mul_le_mul_of_nonneg_left (rpow_decay_weaken hx hα) (by norm_num)
    have hsquare' (L : ℕ) (a b : RotatorSpinSite L) :
        (model n hnpos β hβ).twoPoint (ξ : ℤ) (squareBoxZ L) (siteToZ a) (siteToZ b) ≤
          2 * ((Lattice2D.freeRadius a b : ℝ) + 1) ^
            (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q))) := by
      have hd : 0 ≤ (Lattice2D.freeRadius a b : ℝ) := by positivity
      have hx : 1 ≤ (Lattice2D.freeRadius a b : ℝ) + 1 := by linarith
      exact (hbound L a b).trans (hweak hx)
    have hfreeOld (L : ℕ) (u v : ℤ × ℤ) (hu : boxRadius u ≤ L) (hv : boxRadius v ≤ L) :
        (model n hnpos β hβ).twoPoint (ξ : ℤ) (freeBox L) u v ≤
          2 * ((l1Dist u v : ℝ) + 1) ^ (-c) := by
      have hsq := hbound (2 * L) (boxSite L u) (boxSite L v)
      rw [freeRadius_boxSite hu hv, siteToZ_boxSite hu, siteToZ_boxSite hv] at hsq
      rw [freeBox_eq_translateDomain]
      have ht := (model n hnpos β hβ).twoPoint_translate (ξ : ℤ) (squareBoxZ (2 * L))
        (u + ((L : ℤ), (L : ℤ))) (v + ((L : ℤ), (L : ℤ))) (-(L : ℤ), -(L : ℤ))
      have hu' : u + ((L : ℤ), (L : ℤ)) + (-(L : ℤ), -(L : ℤ)) = u := by ext <;> simp
      have hv' : v + ((L : ℤ), (L : ℤ)) + (-(L : ℤ), -(L : ℤ)) = v := by ext <;> simp
      rw [hu', hv'] at ht
      rw [ht]
      exact hsq
    have hfree (L : ℕ) (u v : ℤ × ℤ) (hu : boxRadius u ≤ L) (hv : boxRadius v ≤ L) :
        (model n hnpos β hβ).twoPoint (ξ : ℤ) (freeBox L) u v ≤
          2 * ((l1Dist u v : ℝ) + 1) ^
            (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q))) := by
      have hd : 0 ≤ (l1Dist u v : ℝ) := by exact_mod_cast Nat.zero_le (l1Dist u v)
      have hx : 1 ≤ (l1Dist u v : ℝ) + 1 := by linarith
      exact (hfreeOld L u v hu hv).trans (hweak hx)
    have hlimit : ∀ u v : ℤ × ℤ,
        (model n hnpos β hβ).twoPointLimit (ξ : ℤ) u v ≤
          2 * ((l1Dist u v : ℝ) + 1) ^
            (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β n q))) := by
      intro u v
      refine le_of_tendsto ((model n hnpos β hβ).tendsto_twoPointLimit (ξ : ℤ) u v) ?_
      filter_upwards [eventually_ge_atTop (max (boxRadius u) (boxRadius v))] with L hL
      exact hfree L u v ((le_max_left _ _).trans hL) ((le_max_right _ _).trans hL)
    exact ⟨⟨hsquare', hfree⟩, hlimit⟩

end FroehlichSpencer.BKT.Clock.VillainClock

end
