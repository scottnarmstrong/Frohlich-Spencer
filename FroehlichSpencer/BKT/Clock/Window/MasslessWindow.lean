/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Window.IntermediatePhase
public import FroehlichSpencer.BKT.PlaneRotator.TheoremC
public import FroehlichSpencer.BKT.Clock.CorrelationComparison
import Mathlib.Tactic

/-!
# FS81 result 4: the massless intermediate phase of the `ℤ_n` clock model

FS81 J p. 528, result 4, and §7.1, Remark 2 (J p. 585). It combines three results:
- Theorem 7.1(1): clock ≥ rotator, `correlation_dominates_rotator_limit`;
- Theorem C for the plane rotator: `PlaneRotator.rotator_theoremC`;
- Theorem 7.1(2): `Compact.clock_twoPointLimit_le`.

* `clock_theorem73`, `clock_powerLaw_lower`: (7.3) for every `n` and `β ≥ β₀`, the rotator's
  Theorem C threshold.
* `clock_powerLaw_upper_uniform`: (7.4) uniformly in `β ∈ [0, B]` for `n ≥ n₁(q, B)`. It comes from
  Theorem 7.1(2) at `β = B` and Ginibre's monotonicity of the clock correlations in `β`
  (`clockModel_twoPointLimit_mono`).
  - This is the common-threshold step that FS81 leaves implicit .
  - FS81's `n₀(β)` is not shown to be monotone. Monotonicity of the correlation itself makes
    `n₀(B)` serve every `β ≤ B`.
* `clock_intermediatePhase_of_le`: the phase on every `[β₀, B]` for `n ≥ n₁(q, B)`.
* **`clock_massless_window`**: result 4. There is `β₀ > 0` with `T₂ = 1/β₀`. For every `q > 0`
  there are `β₁(n) → ∞` and `n₁` such that for every `n ≥ n₁`:
  - `β₀ < β₁(n)`;
  - the clock model is in the massless intermediate phase at every `β ∈ [β₀, β₁(n)]`, i.e. at every
    temperature `T₁(n) = 1/β₁(n) ≤ T ≤ T₂`.
* `exists_window_of_thresholds`: from size thresholds `n₀(B)` on `[β₀, B]` to a single window
  `[β₀, β₁(n)]` with `β₁(n) → ∞`.
* `clock_massless_window_above_kt`: the window can start at the rotator's KT point
  `β_c ≥ 1/2` (`PlaneRotator.rotator_kt_transition`). For `n ≥ n₁` and `β ∈ (β_c, β₁(n)]`:
  - the fundamental harmonic has no exponential decay (`clock_not_expDecay_of_rotator`, by
    Theorem 7.1(1));
  - the restricted harmonics obey (7.4).
  This matches FS81's `β̲_c ≤ β_c`. It omits only the lower bound (7.3), which needs `β ≥ β₀`.
* `ClockPeierlsStatement`, `ClockHighTemperatureStatement`: the ordered and disordered sides
  (FS81 Remark 2 and J p. 589), **stated as propositions, not proved**. They are not needed for
  result 4.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Window

open Filter Topology
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)
open FroehlichSpencer.BKT.Clock.Compact (l1Dist)

theorem l1Norm_sub_eq_l1Dist (u v : ℤ × ℤ) :
    Rotator.Transition.l1Norm (u - v) = l1Dist u v := rfl

/-- **FS81 (7.3)**: Theorem 7.1(1) and Theorem C. There is a `β₀ > 0` (the plane rotator's
Theorem C threshold) such that for every `n` and `β ≥ β₀`, every integer harmonic of the clock
two-point function has a power-law lower bound. -/
theorem clock_powerLaw_lower :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → ∀ ξ : ℤ,
      ∃ c p : ℝ, 0 < c ∧ ∀ u v : ℤ × ℤ,
        c * ((l1Dist u v : ℝ) + 1) ^ (-p) ≤ clockCorr n hn β hβ ξ u v := by
  obtain ⟨β₀, β', -, hC⟩ := PlaneRotator.rotator_theoremC
  refine ⟨max β₀ 1, by positivity, fun n hn β hβ hβ₀ ξ => ?_⟩
  obtain ⟨-, hlow⟩ := hC β hβ ((le_max_left _ _).trans hβ₀)
  refine ⟨Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))), (ξ : ℝ) ^ 2 / (2 * Real.pi * β' β),
    Real.exp_pos _, fun u v => ?_⟩
  have h := hlow ξ u v
  rw [l1Norm_sub_eq_l1Dist] at h
  exact h.trans (correlation_dominates_rotator_limit n hn hβ ξ u v)

/-- **FS81 (7.4) uniformly on a temperature interval**: Theorem 7.1(2) at the top of the interval
and Ginibre's monotonicity in `β` below it. There is an absolute `c > 0` such that for every
`q > 0` and `B ≥ 0` there is `n₁` with: for `n ≥ n₁`, every `0 ≤ β ≤ B` and every restricted
harmonic, `⟨cos(ξ(θ_u − θ_v))⟩^{(n)}(β) ≤ 2 (|u − v|₁ + 1)^{−c}`. -/
theorem clock_powerLaw_upper_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℝ, 0 < q → ∀ B : ℝ, 0 ≤ B → ∃ n₁ : ℕ, 0 < n₁ ∧
      ∀ n : ℕ, n₁ ≤ n → ∀ (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β), β ≤ B → ∀ ξ : ℕ, 0 < ξ → ξ < n →
        q ≤ dipoleGap ((ξ : ℝ) / n) → ∀ u v : ℤ × ℤ,
          clockCorr n hn β hβ ξ u v ≤ 2 * ((l1Dist u v : ℝ) + 1) ^ (-c) := by
  obtain ⟨c, hc, h⟩ := Compact.clock_twoPointLimit_le
  refine ⟨c, hc, fun q hq B hB => ?_⟩
  obtain ⟨n₀, hn₀, hN⟩ := h q hq B hB
  refine ⟨n₀, hn₀, fun n hn₁ hn β hβ hβB ξ hξ0 hξn hqξ u v => ?_⟩
  exact (clockModel_twoPointLimit_mono n hn hβ hβB ξ u v).trans
    (hN n hn₁ hn hB ξ hξ0 hξn hqξ u v)

/-- **The intermediate phase on every bounded temperature interval above the rotator threshold**:
there is `β₀ > 0` such that for every `q > 0` and `B` there is `n₁` with: for `n ≥ n₁` and every
`β ∈ [β₀, B]`, the `ℤ_n` clock model is in the massless intermediate phase. -/
theorem clock_intermediatePhase_of_le :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ q : ℝ, 0 < q → ∀ B : ℝ, ∃ n₁ : ℕ, 0 < n₁ ∧
      ∀ n : ℕ, n₁ ≤ n → ∀ (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ B →
        IsClockIntermediatePhase n hn β hβ q := by
  obtain ⟨β₀, hβ₀, hlow⟩ := clock_powerLaw_lower
  obtain ⟨c, hc, hup⟩ := clock_powerLaw_upper_uniform
  refine ⟨β₀, hβ₀, fun q hq B => ?_⟩
  obtain ⟨n₁, hn₁, hN⟩ := hup q hq (max B 0) (le_max_right _ _)
  refine ⟨n₁, hn₁, fun n hnn hn β hβ hβ₀β hβB => ⟨fun ξ => hlow n hn β hβ hβ₀β ξ, ?_⟩⟩
  intro ξ hξ0 hξn hqξ
  exact ⟨2, c, hc, hN n hnn hn β hβ (hβB.trans (le_max_left _ _)) ξ hξ0 hξn hqξ⟩

/-- **From thresholds to a window.** Let `n₀(B)` be a size threshold for each top `B` of the
temperature interval. Then there are levels `β₁(n) → ∞` and `n₁` with `β₀ < β₁(n)` and
`n₀(β₁(n)) ≤ n` for every `n ≥ n₁`. Here `β₁(n)` is the largest integer level `k ≤ n` whose
threshold `n₀(k)` is reached. -/
theorem exists_window_of_thresholds (β₀ : ℝ) (n₀ : ℝ → ℕ) :
    ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧
      ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → β₀ < β₁ n ∧ n₀ (β₁ n) ≤ n := by
  classical
  set lev : ℕ → ℕ := fun n => Nat.findGreatest (fun k => n₀ (k : ℝ) ≤ n) n with hlev
  have hlev_ge : ∀ k n : ℕ, k ≤ n → n₀ (k : ℝ) ≤ n → k ≤ lev n := fun k n hk hkn =>
    Nat.le_findGreatest hk hkn
  have hlev_spec : ∀ n : ℕ, (∃ k ≤ n, n₀ (k : ℝ) ≤ n) → n₀ (lev n : ℝ) ≤ n := by
    rintro n ⟨k, hk, hkn⟩
    exact Nat.findGreatest_spec (P := fun k => n₀ (k : ℝ) ≤ n) hk hkn
  refine ⟨fun n => (lev n : ℝ), ?_, ?_⟩
  · refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (max ⌈b⌉₊ (n₀ (⌈b⌉₊ : ℝ)))] with n hn
    have h1 := hlev_ge ⌈b⌉₊ n ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
    exact (Nat.le_ceil b).trans (by exact_mod_cast h1)
  · set K : ℕ := ⌊β₀⌋₊ + 1 with hK
    refine ⟨max K (n₀ (K : ℝ)), fun n hn => ⟨?_, ?_⟩⟩
    · have h1 := hlev_ge K n ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
      have h2 : β₀ < (K : ℝ) := by
        rw [hK]; push_cast; exact Nat.lt_floor_add_one β₀
      exact h2.trans_le (show (K : ℝ) ≤ (lev n : ℝ) by exact_mod_cast h1)
    · exact hlev_spec n ⟨K, (le_max_left _ _).trans hn, (le_max_right _ _).trans hn⟩

/-- **FS81 result 4: the massless intermediate phase of the `ℤ_n` clock model** (J p. 528; §7.1,
Remark 2, J p. 585). There is `β₀ > 0` (the rotator's Theorem C threshold; temperature
`T₂ = 1/β₀`) such that for every harmonic margin `q > 0` there are inverse temperatures
`β₁(n) → ∞` and `n₁` with: for every `n ≥ n₁`, `β₀ < β₁(n)` and the `ℤ_n` clock model is in the
massless intermediate phase (`IsClockIntermediatePhase`) at every `β ∈ [β₀, β₁(n)]`, i.e. at every
temperature `T₁(n) = 1/β₁(n) ≤ T ≤ T₂`. -/
theorem clock_massless_window :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ q : ℝ, 0 < q → ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧
      ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ hn : 0 < n, β₀ < β₁ n ∧
        ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ β₁ n → IsClockIntermediatePhase n hn β hβ q := by
  obtain ⟨β₀, hβ₀, h⟩ := clock_intermediatePhase_of_le
  refine ⟨β₀, hβ₀, fun q hq => ?_⟩
  choose n₀ hn₀ hN using h q hq
  obtain ⟨β₁, hβ₁, n₁, hn₁⟩ := exists_window_of_thresholds β₀ n₀
  exact ⟨β₁, hβ₁, n₁, fun n hn hn0 => ⟨(hn₁ n hn).1,
    fun β hβ hβ₀β hβl => hN (β₁ n) n (hn₁ n hn).2 hn0 β hβ hβ₀β hβl⟩⟩

/-- **FS81 (7.3) in its printed form**: for `β ≥ β₀` the clock two-point function of every integer
harmonic is at least `e^{−ξ²/(2πβ')} (|u − v|₁ + 1)^{−ξ²/(2πβ')}`, with `β' = β'(β) > 1/(4π)` and
`β' → ∞` (Theorem C of the plane rotator, through Theorem 7.1(1)). -/
theorem clock_theorem73 :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → 1 / (4 * Real.pi) < β' β ∧
        ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Dist u v : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            clockCorr n hn β hβ ξ u v := by
  obtain ⟨β₀, β', hβ', hC⟩ := PlaneRotator.rotator_theoremC
  refine ⟨β₀, β', hβ', fun n hn β hβ hβ₀ => ⟨(hC β hβ hβ₀).1, fun ξ u v => ?_⟩⟩
  have h := (hC β hβ hβ₀).2 ξ u v
  rw [l1Norm_sub_eq_l1Dist] at h
  exact h.trans (correlation_dominates_rotator_limit n hn hβ ξ u v)

/-- **The fundamental clock harmonic is massless wherever the rotator is**: Theorem 7.1(1)
(rotator ≤ clock) turns exponential decay of the clock into exponential decay of the rotator. -/
theorem clock_not_expDecay_of_rotator {β : ℝ} (hβ : 0 ≤ β)
    (h : ¬ Rotator.Transition.HasExpDecay β hβ) (n : ℕ) (hn : 0 < n) :
    ¬ ClockHasExpDecay n hn β hβ 1 := by
  rintro ⟨C, m, hm, hC⟩
  refine h ⟨C, m, hm, fun u v => ?_⟩
  rw [l1Norm_sub_eq_l1Dist]
  exact (correlation_dominates_rotator_limit n hn hβ 1 u v).trans (hC u v)

/-- **FS81 §7.1, Remark 2, with the window starting at the rotator's critical point.** Let `β_c`
be the plane rotator's Kosterlitz–Thouless point (`PlaneRotator.rotator_kt_transition`). For every
`q > 0` there are `β₁(n) → ∞` and `n₁` such that for every `n ≥ n₁`, `β_c < β₁(n)`, and at every
`β ∈ (β_c, β₁(n)]`:
* the mass gap of the `ℤ_n` model vanishes: its fundamental harmonic does not decay
  exponentially;
* every restricted harmonic has a power-law upper bound (FS81 (7.4)), so the `ℤ_n` symmetry is
  unbroken in it.

This is FS81's window `[β̲_c, β̄_c)` with `β̲_c ≤ β_c`. The power-law lower bound (7.3) is only
available above the Theorem C threshold, which gives `clock_massless_window`. -/
theorem clock_massless_window_above_kt :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ ∀ q : ℝ, 0 < q → ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧
      ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ hn : 0 < n, βc < β₁ n ∧
        ∀ (β : ℝ) (hβ : 0 ≤ β), βc < β → β ≤ β₁ n → ¬ ClockHasExpDecay n hn β hβ 1 ∧
          ∀ ξ : ℕ, 0 < ξ → ξ < n → q ≤ dipoleGap ((ξ : ℝ) / n) →
            ∃ C c : ℝ, 0 < c ∧ ∀ u v : ℤ × ℤ,
              clockCorr n hn β hβ ξ u v ≤ C * ((l1Dist u v : ℝ) + 1) ^ (-c) := by
  obtain ⟨βc, hβc, -, hkt⟩ := PlaneRotator.rotator_kt_transition
  obtain ⟨c, hc, hup⟩ := clock_powerLaw_upper_uniform
  refine ⟨βc, hβc, fun q hq => ?_⟩
  choose n₀ hn₀ hN using fun B : ℝ => hup q hq (max B 0) (le_max_right _ _)
  obtain ⟨β₁, hβ₁, n₁, hn₁⟩ := exists_window_of_thresholds βc n₀
  refine ⟨β₁, hβ₁, n₁, fun n hn hn0 => ⟨(hn₁ n hn).1, fun β hβ hβcβ hβl => ⟨?_, ?_⟩⟩⟩
  · exact clock_not_expDecay_of_rotator hβ (hkt β hβ hβcβ).1 n hn0
  · intro ξ hξ0 hξn hqξ
    exact ⟨2, c, hc, hN (β₁ n) n (hn₁ n hn).2 hn0 β hβ (hβl.trans (le_max_left _ _)) ξ hξ0 hξn
      hqξ⟩

/-! ### The two other phases (stated, not proved) -/

/-- **The ordered low-temperature side** (FS81 §7.1, Remark 2: "For `β > β̄_c` the `ℤ_n`-symmetry
of the model is spontaneously broken. That `β̄_c` is finite is seen by a standard Peierls
argument."), stated as a proposition: for every `n ≥ 2` there is `βbar` such that above it every
harmonic `ξ` has long-range order. Not needed for FS81 result 4; proved in
`Clock/Peierls/ClockPeierls.lean` (`clockPeierlsStatement_holds`). -/
def ClockPeierlsStatement : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ βbar : ℝ, ∀ (β : ℝ) (hβ : 0 ≤ β), βbar < β →
    ∀ ξ : ℤ, ClockHasLongRangeOrder n (by omega) β hβ ξ

/-- **The disordered high-temperature side** (FS81 §7.1, J p. 589: for `β < β_c` the connected
correlations have exponential fall-off), stated as a proposition: there is `β_h > 0` such that
for every `n ≥ 2` and `β < β_h` the fundamental clock harmonic decays exponentially.
Not needed for FS81 result 4; proved in `Clock/HighTemp/Limit.lean`
(`clockHighTemperatureStatement_holds`). -/
def ClockHighTemperatureStatement : Prop :=
  ∃ βh : ℝ, 0 < βh ∧ ∀ (n : ℕ) (hn : 2 ≤ n) (β : ℝ) (hβ : 0 ≤ β), β < βh →
    ClockHasExpDecay n (by omega) β hβ 1

end FroehlichSpencer.BKT.Clock.Window

end
