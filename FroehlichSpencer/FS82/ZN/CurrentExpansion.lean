/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.Fourier
public import FroehlichSpencer.FS82.Currents.Expansion
public import Mathlib.Analysis.Complex.Exponential

/-!
# FS82 §3 `Nℤ` current expansion

This module adapts the finite fixed-frequency expansion of FS82 §2 to
frequencies divisible by the clock order. It also isolates the gauge-character
orthogonality statement which forces local neutrality.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.ZN

open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Cubical

/-- A current takes values in `Nℤ` when every link value is an integer
multiple of the clock order `N`. -/
@[expose] def IsNMultipleCurrent {B : Cubical.Box 4} (N : ℕ)
    (Q : Link B → ℤ) : Prop :=
  ∀ e, ∃ k : ℤ, Q e = (N : ℤ) * k

/-- The current represented by any activity lineage remains `Nℤ`-valued when
the original frequency assignment is `Nℤ`-valued. -/
theorem activityLineage_value_isNMultiple {B : Cubical.Box 4} {N : ℕ}
    (q : Link B → ℤ) (hq : ∀ e, ∃ k : ℤ, q e = (N : ℤ) * k)
    (t : ActivityLineage (Link B)) :
    ∀ e, ∃ k : ℤ, ActivityLineage.value q t e = (N : ℤ) * k := by
  induction t with
  | leaf e =>
      intro x
      by_cases hx : x = e
      · obtain ⟨k, hk⟩ := hq e
        refine ⟨k, ?_⟩
        simp [ActivityLineage.value, hx, hk]
      · refine ⟨0, ?_⟩
        simp [ActivityLineage.value, hx]
  | add l r ihl ihr =>
      intro x
      obtain ⟨a, ha⟩ := ihl x
      obtain ⟨b, hb⟩ := ihr x
      refine ⟨a + b, ?_⟩
      simp [ActivityLineage.value, ha, hb]
      ring
  | sub l r ihl ihr =>
      intro x
      obtain ⟨a, ha⟩ := ihl x
      obtain ⟨b, hb⟩ := ihr x
      refine ⟨a - b, ?_⟩
      simp [ActivityLineage.value, ha, hb]
      ring
  | keepLeft l r ihl ihr =>
      intro x
      obtain ⟨a, ha⟩ := ihl x
      exact ⟨a, by simpa [ActivityLineage.value] using ha⟩
  | keepRight l r ihl ihr =>
      intro x
      obtain ⟨b, hb⟩ := ihr x
      exact ⟨b, by simpa [ActivityLineage.value] using hb⟩

/-- Every term in the §2 separated expansion of a fixed `Nℤ` frequency
assignment is itself an `Nℤ` current. Positivity, normalization, the exact
finite-frequency identity, separation, and the activity envelope are inherited
from `exists_fixedFrequencySeparatedCurrentExpansion_withLineageActivity`. -/
theorem exists_fixedNMultipleSeparatedCurrentExpansion
    {B : Cubical.Box 4} {N : ℕ} (q : Link B → ℤ) (z : ℤ → ℝ)
    (hq : ∀ e, q e ≠ 0)
    (hN : ∀ e, ∃ k : ℤ, q e = (N : ℤ) * k)
    (hz : ∀ n, 0 ≤ z n)
    (hzpos : ∀ n, 0 < n → 0 < z n) :
    ∃ T : List (CurrentExpansionTerm B),
      IsFixedFrequencyCurrentExpansion q z T ∧
      ∀ t ∈ T, ∀ a ∈ t.state,
        IsNMultipleCurrent N (lineageCurrent q a) := by
  obtain ⟨T, hT, _hsize⟩ :=
    exists_fixedFrequencySeparatedCurrentExpansion_withLineageActivity q z hq hz hzpos
  refine ⟨T, hT, ?_⟩
  intro t ht a ha e
  exact activityLineage_value_isNMultiple q hN a e

/-- The initial positive Wilson frequency assignment on each link. The source
frequency is `(m e + 1) * N`, while its Bessel coefficient has order `m e + 1`;
these indices must not be conflated. -/
@[expose] def wilsonModeFrequencyAssignment {B : Cubical.Box 4} (N : ℕ)
    (m : Link B → ℕ) : Link B → ℤ :=
  fun e => (((m e + 1) * N : ℕ) : ℤ)

/-- For one fixed assignment of positive Wilson modes, the finite §2 API gives
the separated positive ensemble expansion and every resulting current remains
`Nℤ`-valued. The outer assignment family is countable; `Fourier.lean` proves
the one-frequency reweighting identity, while the full finite-box product and
countable assignment assembly remain separate obligations. -/
theorem exists_wilsonModeFixedAssignmentSeparated
    {B : Cubical.Box 4} {N : ℕ} (m : Link B → ℕ) (z : ℤ → ℝ)
    (epsilon h : ℝ) (hN : 0 < N)
    (hz : ∀ n, 0 ≤ z n) (hzpos : ∀ n, 0 < n → 0 < z n)
    (hprofile : ∀ e,
      z (abs (wilsonModeFrequencyAssignment N m e)) =
        wilsonCoefficientActivity epsilon N (m e) h) :
    ∃ T : List (CurrentExpansionTerm B),
      IsFixedFrequencyCurrentExpansion (wilsonModeFrequencyAssignment N m) z T ∧
      (∀ e, z (abs (wilsonModeFrequencyAssignment N m e)) =
        wilsonCoefficientActivity epsilon N (m e) h) ∧
      (∀ t ∈ T, ∀ a ∈ t.state,
        IsNMultipleCurrent N (lineageCurrent (wilsonModeFrequencyAssignment N m) a)) := by
  have hq : ∀ e, wilsonModeFrequencyAssignment N m e ≠ 0 := by
    intro e
    have hp : 0 < (m e + 1) * N := Nat.mul_pos (Nat.succ_pos (m e)) hN
    have hpZ : 0 < wilsonModeFrequencyAssignment N m e := by
      dsimp [wilsonModeFrequencyAssignment]
      exact_mod_cast hp
    exact ne_of_gt hpZ
  have hNmultiple : ∀ e, ∃ k : ℤ,
      wilsonModeFrequencyAssignment N m e = (N : ℤ) * k := by
    intro e
    refine ⟨(m e + 1 : ℕ), ?_⟩
    dsimp [wilsonModeFrequencyAssignment]
    ring
  obtain ⟨T, hT, hNcurr⟩ :=
    exists_fixedNMultipleSeparatedCurrentExpansion
      (wilsonModeFrequencyAssignment N m) z hq hNmultiple hz hzpos
  exact ⟨T, hT, hprofile, hNcurr⟩


end FroehlichSpencer.FS82.ZN

end
