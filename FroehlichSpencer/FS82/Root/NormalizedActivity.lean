/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.CharacterRegroup

/-!
# FS82 MomentComparisonAssembly: an explicit normalized activity sequence

FS82 (2.38) needs a sequence `z_q` with `2 Σ_q z_q⁻¹ = 1`. The root uses the geometric sequence
`z_n = 2^(n+1)`: the inactive weights `2 / z_{q+1} = (1/2)^(q+1)` sum to one.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Root

open FroehlichSpencer.FS82.Poisson

/-- The root activity sequence `z_n = 2^(n+1)`. -/
noncomputable def rootActivity (n : ℕ) : ℝ := 2 ^ (n + 1)

theorem rootActivity_pos (n : ℕ) : 0 < rootActivity n := by
  unfold rootActivity
  positivity

theorem inactiveWeight_rootActivity (q : ℕ) :
    inactiveWeight rootActivity q = (1 / 2 : ℝ) ^ (q + 1) := by
  unfold inactiveWeight rootActivity positiveMode
  rw [div_pow, one_pow, pow_succ (2 : ℝ) (q + 1)]
  field_simp

theorem inactiveWeight_rootActivity_nonneg (q : ℕ) : 0 ≤ inactiveWeight rootActivity q := by
  rw [inactiveWeight_rootActivity]
  positivity

/-- The normalization `2 Σ_q z_q⁻¹ = 1` of FS82 (2.38). -/
theorem hasSum_inactiveWeight_rootActivity : HasSum (inactiveWeight rootActivity) 1 := by
  have h := hasSum_geometric_two
  have h2 : HasSum (fun q : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ q) ((1 / 2 : ℝ) * 2) :=
    h.mul_left (1 / 2 : ℝ)
  have e : (fun q : ℕ => inactiveWeight rootActivity q) =
      fun q : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ q := by
    funext q
    rw [inactiveWeight_rootActivity, pow_succ]
    ring
  rw [show inactiveWeight rootActivity = fun q : ℕ => inactiveWeight rootActivity q from rfl, e]
  simpa using h2

end FroehlichSpencer.FS82.Root

end
