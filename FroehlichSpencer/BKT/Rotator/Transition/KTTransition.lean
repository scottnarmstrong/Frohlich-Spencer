/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Transition.HighTemperature
public import FroehlichSpencer.BKT.Rotator.Transition.PowerLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# What the Kosterlitz–Thouless transition of the plane rotator still needs

The infinite-volume free two-point function `G_β(u, v) = freeTwoPointLimit β _ 1 u v` is
nondecreasing in `β` (Ginibre). This file records three regimes:

* **exponential decay** `HasExpDecay` holds for `β < 1/2` (high-temperature current peeling, FS81
  (1.30));
* **absence of long-range order** `HasNoLongRangeOrder` holds for every `β > 0` (McBryan–Spencer,
  FS81 (1.31));
* a **power-law lower bound** `HasPowerLawLowerBound` (the form of FS81 Theorem C) excludes
  exponential decay.

The low-temperature input, FS81 Theorem C, is not proved here. `exists_transition_of_powerLaw`
states exactly what it would give: if a power-law lower bound holds for all large `β`, there is a
single `β_c ≥ 1/2` with exponential decay for `β < β_c` and, for `β > β_c`, no exponential decay and
no long-range order (the massless Kosterlitz–Thouless phase).
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.Rotator.Ginibre

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Transition

/-- Exponential decay of the infinite-volume two-point function `⟨cos(θ_u − θ_v)⟩(β)`. -/
def HasExpDecay (β : ℝ) (hβ : 0 ≤ β) : Prop :=
  ∃ C m : ℝ, 0 < m ∧ ∀ u v : ℤ × ℤ,
    freeTwoPointLimit β hβ 1 u v ≤ C * Real.exp (-m * l1Norm (u - v))

/-- A power-law lower bound for the infinite-volume two-point function (the form of FS81
Theorem C). -/
def HasPowerLawLowerBound (β : ℝ) (hβ : 0 ≤ β) : Prop :=
  ∃ c p : ℝ, 0 < c ∧ ∀ u v : ℤ × ℤ,
    c * ((l1Norm (u - v) : ℝ) + 1) ^ (-p) ≤ freeTwoPointLimit β hβ 1 u v

/-- Absence of long-range order: the two-point function tends to zero at large distance,
uniformly in the pair of sites. -/
def HasNoLongRangeOrder (β : ℝ) (hβ : 0 ≤ β) : Prop :=
  ∀ ε > 0, ∃ R : ℕ, ∀ u v : ℤ × ℤ, R ≤ l1Norm (u - v) → freeTwoPointLimit β hβ 1 u v ≤ ε

/-- **High temperature:** exponential decay for `0 ≤ β < 1/2`. -/
theorem hasExpDecay_of_lt_half {β : ℝ} (hβ : 0 ≤ β) (h : β < 1 / 2) : HasExpDecay β hβ := by
  set r := max (2 * β) (1 / 2)
  have hr0 : 0 < r := lt_max_of_lt_right (by norm_num)
  have hr1 : r < 1 := max_lt (by linarith) (by norm_num)
  refine ⟨1, -Real.log r, by linarith [Real.log_neg hr0 hr1], fun u v => ?_⟩
  refine (freeTwoPointLimit_le_pow hβ u v).trans ?_
  rw [one_mul, neg_neg, mul_comm (Real.log r), ← Real.log_pow, Real.exp_log (pow_pos hr0 _)]
  exact pow_le_pow_left₀ (by positivity) (le_max_left _ _) _

/-- Exponential decay at `β'` implies exponential decay at every smaller `β ≥ 0`. -/
theorem HasExpDecay.mono {β β' : ℝ} (hβ : 0 ≤ β) (hββ' : β ≤ β')
    (h : HasExpDecay β' (hβ.trans hββ')) : HasExpDecay β hβ := by
  obtain ⟨C, m, hm, hC⟩ := h
  exact ⟨C, m, hm, fun u v => (freeTwoPointLimit_mono_beta hβ hββ' 1 u v).trans (hC u v)⟩

/-- **McBryan–Spencer:** no long-range order at any `β > 0`. -/
theorem hasNoLongRangeOrder {β : ℝ} (hβ : 0 < β) : HasNoLongRangeOrder β hβ.le := by
  intro ε hε
  have hs := msExponent_pos hβ
  have ht : Tendsto (fun n : ℕ => Real.exp (5 / 8) * ((n : ℝ) + 1) ^ (-msExponent β)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa using ((tendsto_rpow_neg_atTop hs).comp h1).const_mul (Real.exp (5 / 8))
  obtain ⟨R, hR⟩ := (ht.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨R, fun u v huv => ?_⟩
  refine (freeTwoPointLimit_le_rpow hβ u v).trans (le_trans ?_ (hR R le_rfl).le)
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.add_le_add_right huv 1)
    (by linarith)

theorem l1Norm_horizontal (n : ℕ) : l1Norm (((n : ℤ), (0 : ℤ)) - (0, 0)) = n := by
  simp [l1Norm]

/-- A power-law lower bound excludes exponential decay. -/
theorem not_hasExpDecay_of_hasPowerLawLowerBound {β : ℝ} (hβ : 0 ≤ β)
    (h : HasPowerLawLowerBound β hβ) : ¬ HasExpDecay β hβ := by
  rintro ⟨C, m, hm, hC⟩
  obtain ⟨c, p, hc, hcp⟩ := h
  have hlim : Tendsto (fun n : ℕ => C * Real.exp m *
      (((n : ℝ) + 1) ^ p * Real.exp (-m * ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa using ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p m hm).comp h1).const_mul
      (C * Real.exp m)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
  have h1 := (hcp ((n : ℤ), 0) (0, 0)).trans (hC ((n : ℤ), 0) (0, 0))
  rw [l1Norm_horizontal] at h1
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpow : ((n : ℝ) + 1) ^ (-p) * ((n : ℝ) + 1) ^ p = 1 := by
    rw [← Real.rpow_add hpos, neg_add_cancel, Real.rpow_zero]
  have hexp : Real.exp (-m * n) = Real.exp m * Real.exp (-m * ((n : ℝ) + 1)) := by
    rw [← Real.exp_add]
    ring_nf
  have key : c ≤ C * Real.exp m * (((n : ℝ) + 1) ^ p * Real.exp (-m * ((n : ℝ) + 1))) := by
    have hq : 0 < ((n : ℝ) + 1) ^ p := Real.rpow_pos_of_pos hpos p
    calc c = c * ((n : ℝ) + 1) ^ (-p) * ((n : ℝ) + 1) ^ p := by
          rw [mul_assoc, hpow, mul_one]
      _ ≤ C * Real.exp (-m * n) * ((n : ℝ) + 1) ^ p :=
          mul_le_mul_of_nonneg_right h1 hq.le
      _ = C * Real.exp m * (((n : ℝ) + 1) ^ p * Real.exp (-m * ((n : ℝ) + 1))) := by
          rw [hexp]
          ring
  linarith

/-- **The transition, given a low-temperature input that excludes exponential decay.** If
exponential decay fails for all `β ≥ β₀`, there is a single `β_c ≥ 1/2` such that the two-point
function decays exponentially for `β < β_c`, while for `β > β_c` it does not decay exponentially and
there is no long-range order. -/
theorem exists_transition_of_not_hasExpDecay
    (h : ∃ β₀ : ℝ, ∀ β (hβ : 0 ≤ β), β₀ ≤ β → ¬ HasExpDecay β hβ) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) := by
  obtain ⟨β₀, hβ₀⟩ := h
  set S : Set ℝ := {β | ∃ hβ : 0 ≤ β, HasExpDecay β hβ}
  have hS0 : (0 : ℝ) ∈ S := ⟨le_rfl, hasExpDecay_of_lt_half le_rfl (by norm_num)⟩
  have hbdd : BddAbove S := by
    refine ⟨β₀, fun β ⟨hβ, hβd⟩ => ?_⟩
    by_contra hlt
    exact hβ₀ β hβ (le_of_lt (not_le.mp hlt)) hβd
  have hmem : ∀ β, 0 ≤ β → β < 1 / 2 → β ∈ S := fun β hβ h => ⟨hβ, hasExpDecay_of_lt_half hβ h⟩
  refine ⟨sSup S, ?_, fun β hβ hlt => ?_, fun β hβ hlt => ⟨fun hd => ?_, ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have h0 : 0 ≤ sSup S := le_csSup hbdd hS0
    have hmid : (sSup S + 1 / 2) / 2 ∈ S := hmem _ (by linarith) (by linarith)
    have := le_csSup hbdd hmid
    linarith
  · obtain ⟨β', ⟨hβ', hd⟩, hββ'⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ hlt
    exact hd.mono hβ hββ'.le
  · have := le_csSup hbdd ⟨hβ, hd⟩
    linarith
  · have h0 : 0 ≤ sSup S := le_csSup hbdd hS0
    exact hasNoLongRangeOrder (β := β) (by linarith)

/-- **What FS81 Theorem C would complete.** If the infinite-volume two-point function has a
power-law lower bound for all large `β`, the plane rotator has a Kosterlitz–Thouless transition: a
single `β_c ≥ 1/2` separating exponential decay (`β < β_c`) from a phase with neither exponential
decay nor long-range order (`β > β_c`), with power-law decay bounds there. -/
theorem exists_transition_of_powerLaw
    (hC : ∃ β₀ : ℝ, ∀ β (hβ : 0 ≤ β), β₀ ≤ β → HasPowerLawLowerBound β hβ) :
    ∃ βc : ℝ, 1 / 2 ≤ βc ∧ (∀ β (hβ : 0 ≤ β), β < βc → HasExpDecay β hβ) ∧
      (∀ β (hβ : 0 ≤ β), βc < β → ¬ HasExpDecay β hβ ∧ HasNoLongRangeOrder β hβ) := by
  obtain ⟨β₀, hβ₀⟩ := hC
  exact exists_transition_of_not_hasExpDecay
    ⟨β₀, fun β hβ h => not_hasExpDecay_of_hasPowerLawLowerBound hβ (hβ₀ β hβ h)⟩

end FroehlichSpencer.BKT.Rotator.Transition

end
