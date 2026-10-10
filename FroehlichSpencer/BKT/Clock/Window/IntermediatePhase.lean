/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
public import FroehlichSpencer.BKT.Rotator.Transition.L1Distance
import Mathlib.Tactic

/-!
# The massless intermediate phase of the `ℤ_n` clock model: the predicate

The meaning is fixed in §7.1, Remark 2 (J p. 585; FS81).

The lower bound (7.3)
and the upper bound (7.4) "prove that … the inverse correlation length (mass gap), `m(β, n)`, of
the `ℤ_n`-model vanishes, i.e. there is a massless, intermediate phase for
`β ∈ [β_c, β̄_c)`".

The phase lies between two others (J p. 589; FS81):
- unbroken `ℤ_n` symmetry with exponential fall-off (`β < β_c`);
- broken `ℤ_n` symmetry (`β > β̄_c`).

**Decision (for the author).** FS81 defines the phase only through (7.3)–(7.4).

`IsClockIntermediatePhase n β q` records exactly these two inequalities, for the free
infinite-volume two-point function of the Ginibre `clockModel`:
* `lower`, (7.3): a power-law lower bound for every integer harmonic.

Hence no harmonic decays
  exponentially and the mass gap vanishes (`IsClockIntermediatePhase.massless`).
* `upper`, (7.4): a power-law upper bound for the restricted harmonics
  `min(ξ/n, 1 − ξ/n) ≥ q`.

Hence these harmonics have no long-range order, i.e. the `ℤ_n` symmetry
  is not broken (`IsClockIntermediatePhase.noLongRangeOrder`).

The margin `q` is a parameter, as in FS81's (7.4).

For `q ≤ 1/3` and `n ≥ 3` the half harmonic
`⌊n/2⌋` is restricted (`half_harmonic_restricted`), so the upper clause is never vacuous.

FS81
states no upper bound for the fundamental harmonic `ξ = 1` of the clock, and none is claimed here.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Window

open Filter Topology
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)
open FroehlichSpencer.BKT.Clock.Compact (l1Dist)

/-! ### The phase predicates of the `ℤ_n` clock model -/

/-- The infinite-volume free two-point function `⟨cos(ξ(θ_u − θ_v))⟩^{(n)}(β)` of the `ℤ_n` clock
model (FS81 §7.1, `twoPointLimit` of the Ginibre `clockModel`). -/
abbrev clockCorr (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ) : ℝ :=
  (clockModel n hn β hβ).twoPointLimit ξ u v

/-- The harmonic `ξ` of the clock two-point function decays exponentially (a positive mass gap,
the inverse correlation length `m(β, n) > 0` of FS81 p. 585). -/
def ClockHasExpDecay (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) : Prop :=
  ∃ C m : ℝ, 0 < m ∧ ∀ u v : ℤ × ℤ, clockCorr n hn β hβ ξ u v ≤ C * Real.exp (-m * l1Dist u v)

/-- The harmonic `ξ` of the clock two-point function has long-range order (it stays bounded below
at arbitrarily large distances; spontaneous breaking of the `ℤ_n` symmetry in this harmonic). -/
def ClockHasLongRangeOrder (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) : Prop :=
  ∃ ε > 0, ∀ R : ℕ, ∃ u v : ℤ × ℤ, R ≤ l1Dist u v ∧ ε ≤ clockCorr n hn β hβ ξ u v

/-- **The massless intermediate phase of the `ℤ_n` clock model** (FS81 result 4, J p. 528;
§7.1 Remark 2, J p. 585, (7.3)–(7.4)), at inverse temperature `β` and harmonic margin `q`:

* `lower` — FS81 (7.3): every integer harmonic `ξ` has a power-law lower bound
  `c (|u − v|₁ + 1)^{−p} ≤ ⟨cos(ξ(θ_u − θ_v))⟩^{(n)}(β)`; in particular no harmonic decays
  exponentially, i.e. the mass gap vanishes (`IsClockIntermediatePhase.massless`);
* `upper` — FS81 (7.4): every restricted harmonic `0 < ξ < n` with `min(ξ/n, 1 − ξ/n) ≥ q` has a
  power-law upper bound `⟨cos(ξ(θ_u − θ_v))⟩^{(n)}(β) ≤ C (|u − v|₁ + 1)^{−c}`; in particular
  these harmonics have no long-range order: the `ℤ_n` symmetry is not broken
  (`IsClockIntermediatePhase.noLongRangeOrder`). -/
structure IsClockIntermediatePhase (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (q : ℝ) : Prop where
  lower : ∀ ξ : ℤ, ∃ c p : ℝ, 0 < c ∧ ∀ u v : ℤ × ℤ,
    c * ((l1Dist u v : ℝ) + 1) ^ (-p) ≤ clockCorr n hn β hβ ξ u v
  upper : ∀ ξ : ℕ, 0 < ξ → ξ < n → q ≤ dipoleGap ((ξ : ℝ) / n) →
    ∃ C c : ℝ, 0 < c ∧ ∀ u v : ℤ × ℤ,
      clockCorr n hn β hβ ξ u v ≤ C * ((l1Dist u v : ℝ) + 1) ^ (-c)

/-! ### Consequences -/

theorem l1Dist_zero_right (r : ℕ) : l1Dist (0, 0) ((r : ℤ), 0) = r := by
  simp [l1Dist]

/-- A power-law lower bound excludes exponential decay. -/
theorem not_expDecay_of_powerLaw {f : ℤ × ℤ → ℤ × ℤ → ℝ} {c p : ℝ} (hc : 0 < c)
    (hlow : ∀ u v, c * ((l1Dist u v : ℝ) + 1) ^ (-p) ≤ f u v) :
    ¬ ∃ C m : ℝ, 0 < m ∧ ∀ u v, f u v ≤ C * Real.exp (-m * l1Dist u v) := by
  rintro ⟨C, m, hm, hC⟩
  -- along the points `(0,0)`, `(r,0)`: `c (r+1)^{-p} ≤ C e^{-m r}`
  have hle : ∀ r : ℕ, c * ((r : ℝ) + 1) ^ (-p) ≤ C * Real.exp (-m * r) := by
    intro r
    have h1 := hlow (0, 0) ((r : ℤ), 0)
    have h2 := hC (0, 0) ((r : ℤ), 0)
    rw [l1Dist_zero_right] at h1 h2
    exact h1.trans h2
  -- `e^{m r} (r + 1)^{-p} → ∞`
  have hT : Tendsto (fun r : ℕ => Real.exp (m * r) * ((r : ℝ) + 1) ^ (-p)) atTop atTop := by
    have hk : Tendsto (fun x : ℝ => Real.exp (m * (x + 1)) / (x + 1) ^ p) atTop atTop :=
      (tendsto_exp_mul_div_rpow_atTop p m hm).comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    have h1 : Tendsto (fun x : ℝ => Real.exp (m * x) * (x + 1) ^ (-p)) atTop atTop := by
      refine (hk.const_mul_atTop (Real.exp_pos (-m))).congr'
        (eventually_atTop.2 ⟨0, fun x hx => ?_⟩)
      have hx1 : 0 < x + 1 := by linarith
      show Real.exp (-m) * (Real.exp (m * (x + 1)) / (x + 1) ^ p) =
        Real.exp (m * x) * (x + 1) ^ (-p)
      rw [Real.rpow_neg hx1.le, div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    exact h1.comp tendsto_natCast_atTop_atTop
  obtain ⟨r, hr⟩ := (hT.eventually_gt_atTop ((max C 0) / c + 1)).exists
  have h := hle r
  have hexp : 0 < Real.exp (m * r) := Real.exp_pos _
  have hpow : 0 < ((r : ℝ) + 1) ^ (-p) := by positivity
  have h' : c * (Real.exp (m * r) * ((r : ℝ) + 1) ^ (-p)) ≤ C := by
    have := mul_le_mul_of_nonneg_left h hexp.le
    rw [show Real.exp (m * r) * (C * Real.exp (-m * r)) = C by
      rw [mul_left_comm, ← Real.exp_add]; simp] at this
    linarith
  have hC0 : C ≤ max C 0 := le_max_left _ _
  have : c * ((max C 0) / c + 1) ≤ C := by
    calc c * ((max C 0) / c + 1) ≤ c * (Real.exp (m * r) * ((r : ℝ) + 1) ^ (-p)) :=
          mul_le_mul_of_nonneg_left hr.le hc.le
      _ ≤ C := h'
  rw [mul_add, mul_div_cancel₀ _ hc.ne'] at this
  linarith [le_max_right C 0]

/-- **The mass gap vanishes in the intermediate phase**: no harmonic of the clock two-point
function decays exponentially (FS81 p. 585, `m(β, n) = 0`). -/
theorem IsClockIntermediatePhase.massless {n : ℕ} {hn : 0 < n} {β : ℝ} {hβ : 0 ≤ β} {q : ℝ}
    (h : IsClockIntermediatePhase n hn β hβ q) (ξ : ℤ) : ¬ ClockHasExpDecay n hn β hβ ξ := by
  obtain ⟨c, p, hc, hlow⟩ := h.lower ξ
  exact not_expDecay_of_powerLaw hc hlow

/-- A power-law upper bound excludes long-range order. -/
theorem not_longRangeOrder_of_powerLaw {f : ℤ × ℤ → ℤ × ℤ → ℝ} {C c : ℝ} (hc : 0 < c)
    (hup : ∀ u v, f u v ≤ C * ((l1Dist u v : ℝ) + 1) ^ (-c)) :
    ¬ ∃ ε > 0, ∀ R : ℕ, ∃ u v, R ≤ l1Dist u v ∧ ε ≤ f u v := by
  rintro ⟨ε, hε, hR⟩
  have hT : Tendsto (fun r : ℝ => C * (r + 1) ^ (-c)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hc).comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    simpa using h.const_mul C
  obtain ⟨R₀, hR₀⟩ := (eventually_atTop.1 (hT.eventually (gt_mem_nhds hε)))
  obtain ⟨u, v, huv, hfu⟩ := hR ⌈max R₀ 0⌉₊
  have hd : R₀ ≤ (l1Dist u v : ℝ) := by
    have h1 : (⌈max R₀ 0⌉₊ : ℝ) ≤ l1Dist u v := by exact_mod_cast huv
    exact (le_max_left _ _).trans ((Nat.le_ceil _).trans h1)
  have := hR₀ _ hd
  linarith [hup u v]

/-- **The `ℤ_n` symmetry is unbroken in the intermediate phase**: the restricted harmonics have no
long-range order. -/
theorem IsClockIntermediatePhase.noLongRangeOrder {n : ℕ} {hn : 0 < n} {β : ℝ} {hβ : 0 ≤ β}
    {q : ℝ} (h : IsClockIntermediatePhase n hn β hβ q) {ξ : ℕ} (hξ0 : 0 < ξ) (hξn : ξ < n)
    (hq : q ≤ dipoleGap ((ξ : ℝ) / n)) : ¬ ClockHasLongRangeOrder n hn β hβ ξ := by
  obtain ⟨C, c, hc, hup⟩ := h.upper ξ hξ0 hξn hq
  exact not_longRangeOrder_of_powerLaw hc hup

/-- The upper clause is not vacuous: for `q ≤ 1/3` and `n ≥ 3` the half harmonic `⌊n/2⌋` is
restricted. -/
theorem half_harmonic_restricted {n : ℕ} (hn : 3 ≤ n) {q : ℝ} (hq : q ≤ 1 / 3) :
    0 < n / 2 ∧ n / 2 < n ∧ q ≤ dipoleGap (((n / 2 : ℕ) : ℝ) / n) := by
  refine ⟨by omega, by omega, hq.trans ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : (n : ℝ) / 3 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 3 * (n / 2) := by omega
    rw [div_le_iff₀ (by norm_num)]
    have : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have h2 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    have : ((2 * (n / 2) : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this
    linarith
  unfold dipoleGap
  refine le_min ?_ ?_
  · rw [le_div_iff₀ hn']; linarith
  · rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hn']; linarith

end FroehlichSpencer.BKT.Clock.Window

end
