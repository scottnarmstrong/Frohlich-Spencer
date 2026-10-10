/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Transition.CurrentPeeling

/-!
# High-temperature exponential decay of the plane-rotator two-point function

FS81 (1.30), J p. 533: for `β` small, `⟨S_j·S_ℓ⟩(β) → 0` exponentially fast. The free-box bound
`⟨cos(θ_a − θ_x)⟩ ≤ (2β)^{|a − x|₁}` of `CurrentPeeling` transfers to the centered squares, hence to
the infinite-volume two-point function `freeTwoPointLimit`, and then, by domain monotonicity, to
every finite domain of `ℤ²` with free boundary conditions. For `β < 1/2` this is exponential decay
with constant `1` and mass `log(1/(2β))`.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.Rotator.Ginibre

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Transition

theorem freeTwoPoint_freeBox_le_pow {β : ℝ} (hβ : 0 ≤ β) {L : ℕ} {u v : ℤ × ℤ}
    (hu : boxRadius u ≤ L) (hv : boxRadius v ≤ L) :
    freeTwoPoint β 1 (freeBox L) u v ≤ (2 * β) ^ l1Norm (u - v) := by
  rw [← integral_cos_rotatorMeasureInternal_boxSite L β 1 hu hv, ← boxDist_boxSite hu hv]
  exact integral_cos_rotatorMeasureInternal_le_pow hβ _ _

/-- The infinite-volume two-point function is at most `(2β)^{|u − v|₁}`. -/
theorem freeTwoPointLimit_le_pow {β : ℝ} (hβ : 0 ≤ β) (u v : ℤ × ℤ) :
    freeTwoPointLimit β hβ 1 u v ≤ (2 * β) ^ l1Norm (u - v) := by
  refine le_of_tendsto (tendsto_freeTwoPointLimit hβ 1 u v) ?_
  filter_upwards [eventually_ge_atTop (max (boxRadius u) (boxRadius v))] with L hL
  exact freeTwoPoint_freeBox_le_pow hβ ((le_max_left _ _).trans hL) ((le_max_right _ _).trans hL)

/-- **High-temperature bound, uniform in the domain.** For every finite domain `Λ ⊆ ℤ²` with free
boundary conditions and `u, v ∈ Λ`, `⟨cos(θ_u − θ_v)⟩_Λ(β) ≤ (2β)^{|u − v|₁}`. -/
theorem freeTwoPoint_le_pow {β : ℝ} (hβ : 0 ≤ β) {Λ : Finset (ℤ × ℤ)} {u v : ℤ × ℤ}
    (hu : u ∈ Λ) (hv : v ∈ Λ) :
    freeTwoPoint β 1 Λ u v ≤ (2 * β) ^ l1Norm (u - v) :=
  (freeTwoPoint_le_freeTwoPointLimit hβ 1 hu hv).trans (freeTwoPointLimit_le_pow hβ u v)

/-- The decay rate `log(1/(2β))`, positive for `0 < β < 1/2`. -/
def highTemperatureMass (β : ℝ) : ℝ :=
  -Real.log (2 * β)

theorem highTemperatureMass_pos {β : ℝ} (hβ : 0 < β) (hβ' : β < 1 / 2) :
    0 < highTemperatureMass β := by
  unfold highTemperatureMass
  have : Real.log (2 * β) < 0 := Real.log_neg (by positivity) (by linarith)
  linarith

theorem pow_eq_exp_neg_highTemperatureMass {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    (2 * β) ^ n = Real.exp (-highTemperatureMass β * n) := by
  rw [highTemperatureMass, neg_neg, mul_comm (Real.log _), ← Real.log_pow,
    Real.exp_log (by positivity)]

/-- **FS81 (1.30), exponential form.** For `0 < β < 1/2` and every finite domain with free
boundary conditions, `⟨cos(θ_u − θ_v)⟩_Λ(β) ≤ e^{−m|u − v|₁}` with `m = log(1/(2β)) > 0`. -/
theorem freeTwoPoint_le_exp {β : ℝ} (hβ : 0 < β) {Λ : Finset (ℤ × ℤ)} {u v : ℤ × ℤ}
    (hu : u ∈ Λ) (hv : v ∈ Λ) :
    freeTwoPoint β 1 Λ u v ≤ Real.exp (-highTemperatureMass β * l1Norm (u - v)) := by
  rw [← pow_eq_exp_neg_highTemperatureMass hβ]
  exact freeTwoPoint_le_pow hβ.le hu hv

theorem freeTwoPointLimit_le_exp {β : ℝ} (hβ : 0 < β) (u v : ℤ × ℤ) :
    freeTwoPointLimit β hβ.le 1 u v ≤ Real.exp (-highTemperatureMass β * l1Norm (u - v)) := by
  rw [← pow_eq_exp_neg_highTemperatureMass hβ]
  exact freeTwoPointLimit_le_pow hβ.le u v

end FroehlichSpencer.BKT.Rotator.Transition

end
