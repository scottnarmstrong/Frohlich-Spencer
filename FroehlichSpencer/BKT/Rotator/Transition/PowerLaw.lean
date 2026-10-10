/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Transition.ContourShift
public import FroehlichSpencer.BKT.Rotator.Transition.ProfileEnergy

/-!
# McBryan–Spencer power-law upper bound for the plane rotator

FS81 (1.31), J p. 533, citing McBryan–Spencer [14] (external input `X:MS`): the two-point function
of the plane rotator decays at least like a power of the distance at every temperature. Applying
the general complex-translation inequality `integral_cos_cosineGibbs_le_exp` with the logarithmic
profile `a = λ · msProfile` around `u` (whose drop from `u` to `v` is `λ H_R`, `R = |u − v|₁`, and
whose Dirichlet energy is at most `λ² (8 H_R + 10)`) and `cosh t − 1 ≤ t²` for `|t| ≤ 1` gives, for
`0 ≤ λ ≤ 1`, `⟨cos(ξ(θ_u − θ_v))⟩_Λ(β) ≤ exp(−ξ λ H_R + β λ² (8 H_R + 10))` on every finite domain.
The choice `λ = min(1, 1/(16β))` and `H_R ≥ log(R + 1)` give
`⟨cos(θ_u − θ_v)⟩_Λ(β) ≤ e^{5/8} (1 + |u − v|₁)^{−min(1/2, 1/(32β))}`, uniformly in `Λ`, and the same
bound for `freeTwoPointLimit`.
-/

@[expose] public section

open Filter Topology MeasureTheory
open FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Transition

theorem l1Norm_sub_comm (u v : ℤ × ℤ) : l1Norm (u - v) = l1Norm (v - u) := by
  simp only [l1Norm, Prod.fst_sub, Prod.snd_sub]
  omega

/-- **McBryan–Spencer bound, parametric form.** For `β ≥ 0`, `u, v ∈ Λ` and `0 ≤ λ ≤ 1`,
`⟨cos(ξ(θ_u − θ_v))⟩_Λ(β) ≤ exp(−ξ λ H + β λ² (8H + 10))` with `H = H_{|u−v|₁}`. -/
theorem freeTwoPoint_le_exp_profile {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) {Λ : Finset (ℤ × ℤ)}
    {u v : ℤ × ℤ} (hu : u ∈ Λ) (hv : v ∈ Λ) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    freeTwoPoint β ξ Λ u v ≤
      Real.exp (-(ξ : ℝ) * lam * tailHarmonic (l1Norm (u - v)) 0 +
        β * lam ^ 2 * (8 * tailHarmonic (l1Norm (u - v)) 0 + 10)) := by
  classical
  set R := l1Norm (u - v)
  set H := tailHarmonic R 0
  let a : Λ → ℝ := fun x => lam * msProfile R u x
  rw [freeTwoPoint_eq_integral_cos, freeRotatorMeasure]
  refine (integral_cos_cosineGibbs_le_exp _ (freeCoupling_nonneg hβ) _ a).trans
    (Real.exp_le_exp.mpr ?_)
  have hphase : phase (twoPointFrequency Λ ξ u v) a = ξ * (lam * H) := by
    rw [phase_twoPointFrequency]
    simp only [latticeAngle, dite_eq_left hu, dite_eq_left hv, a]
    rw [msProfile_self, msProfile_eq_zero (by rw [← l1Norm_sub_comm]), mul_zero, sub_zero]
  have hbond : ∀ b : Λ × Λ, freeCoupling β Λ b * (Real.cosh (phase (bondFrequency Λ b) a) - 1) ≤
      β * lam ^ 2 * (if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then
        (msProfile R u b.1 - msProfile R u b.2) ^ 2 else 0) := fun b => by
    rw [phase_bondFrequency, freeCoupling]
    split_ifs with hs
    · have hstep := abs_msProfile_sub_le_one R u hs
      have ht : |lam * msProfile R u b.1 - lam * msProfile R u b.2| ≤ 1 := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hlam0]
        exact (mul_le_mul hlam1 hstep (abs_nonneg _) zero_le_one).trans (by norm_num)
      have hc := cosh_sub_one_le_sq ht
      calc β * (Real.cosh (a b.1 - a b.2) - 1)
          ≤ β * (lam * msProfile R u b.1 - lam * msProfile R u b.2) ^ 2 :=
            mul_le_mul_of_nonneg_left hc hβ
        _ = β * lam ^ 2 * (msProfile R u b.1 - msProfile R u b.2) ^ 2 := by ring
    · simp
  have henergy := msProfile_energy_le R u Λ
  calc -phase (twoPointFrequency Λ ξ u v) a +
        ∑ b, freeCoupling β Λ b * (Real.cosh (phase (bondFrequency Λ b) a) - 1)
      ≤ -(ξ * (lam * H)) + ∑ b : Λ × Λ, β * lam ^ 2 * (if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ)
          then (msProfile R u b.1 - msProfile R u b.2) ^ 2 else 0) := by
        rw [hphase]
        exact add_le_add_right (Finset.sum_le_sum fun b _ => hbond b) _
    _ = -(ξ * (lam * H)) + β * lam ^ 2 * ∑ b : Λ × Λ, (if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ)
          then (msProfile R u b.1 - msProfile R u b.2) ^ 2 else 0) := by
        rw [Finset.mul_sum]
    _ ≤ -(ξ : ℝ) * lam * H + β * lam ^ 2 * (8 * H + 10) := by
        have : 0 ≤ β * lam ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left henergy this]

/-- The exponent of the McBryan–Spencer bound produced by the choice `λ = min(1, 1/(16β))`. -/
def msExponent (β : ℝ) : ℝ :=
  min (1 / 2) (1 / (32 * β))

theorem msExponent_pos {β : ℝ} (hβ : 0 < β) : 0 < msExponent β := by
  unfold msExponent
  positivity

/-- The exponent bound after optimizing `λ`: `−λ H + β λ² (8H + 10) ≤ −msExponent β · H + 5/8`. -/
theorem exists_lam_exponent_le {β : ℝ} (hβ : 0 < β) {H : ℝ} (hH : 0 ≤ H) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧
      -lam * H + β * lam ^ 2 * (8 * H + 10) ≤ -msExponent β * H + 5 / 8 := by
  by_cases hb : 1 / 16 ≤ β
  · refine ⟨1 / (16 * β), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]
      linarith
    · have hmin : msExponent β ≤ 1 / (32 * β) := min_le_right _ _
      have hβ' : β ≠ 0 := hβ.ne'
      have key : -(1 / (16 * β)) * H + β * (1 / (16 * β)) ^ 2 * (8 * H + 10) =
          -(1 / (32 * β)) * H + 5 / (128 * β) := by
        field_simp
        ring
      have h58 : 5 / (128 * β) ≤ 5 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      rw [key]
      nlinarith [mul_le_mul_of_nonneg_right hmin hH]
  · push Not at hb
    refine ⟨1, zero_le_one, le_rfl, ?_⟩
    have hmin : msExponent β ≤ 1 / 2 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hmin hH]

/-- **McBryan–Spencer power-law bound, uniform in the domain.** For `β > 0`, every finite domain
`Λ ⊆ ℤ²` with free boundary conditions and `u, v ∈ Λ`,
`⟨cos(θ_u − θ_v)⟩_Λ(β) ≤ e^{5/8} (1 + |u − v|₁)^{−min(1/2, 1/(32β))}`. -/
theorem freeTwoPoint_le_rpow {β : ℝ} (hβ : 0 < β) {Λ : Finset (ℤ × ℤ)} {u v : ℤ × ℤ}
    (hu : u ∈ Λ) (hv : v ∈ Λ) :
    freeTwoPoint β 1 Λ u v ≤
      Real.exp (5 / 8) * ((l1Norm (u - v) : ℝ) + 1) ^ (-msExponent β) := by
  set H := tailHarmonic (l1Norm (u - v)) 0
  have hH : 0 ≤ H := tailHarmonic_nonneg _ _
  obtain ⟨lam, hlam0, hlam1, hexp⟩ := exists_lam_exponent_le hβ hH
  have h := freeTwoPoint_le_exp_profile hβ.le 1 hu hv hlam0 hlam1
  push_cast at h
  have hlog : Real.log ((l1Norm (u - v) : ℝ) + 1) ≤ H :=
    log_add_one_le_tailHarmonic_zero _
  have hpos : (0 : ℝ) < (l1Norm (u - v) : ℝ) + 1 := by positivity
  refine h.trans ?_
  rw [Real.rpow_def_of_pos hpos, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hm := (msExponent_pos hβ).le
  have : -msExponent β * H ≤ Real.log ((l1Norm (u - v) : ℝ) + 1) * -msExponent β := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hm]
  linarith

/-- **McBryan–Spencer bound for the infinite-volume two-point function.** -/
theorem freeTwoPointLimit_le_rpow {β : ℝ} (hβ : 0 < β) (u v : ℤ × ℤ) :
    freeTwoPointLimit β hβ.le 1 u v ≤
      Real.exp (5 / 8) * ((l1Norm (u - v) : ℝ) + 1) ^ (-msExponent β) := by
  refine le_of_tendsto (tendsto_freeTwoPointLimit hβ.le 1 u v) ?_
  filter_upwards [eventually_ge_atTop (max (boxRadius u) (boxRadius v))] with L hL
  exact freeTwoPoint_le_rpow hβ (mem_freeBox_of_boxRadius_le ((le_max_left _ _).trans hL))
    (mem_freeBox_of_boxRadius_le ((le_max_right _ _).trans hL))

end FroehlichSpencer.BKT.Rotator.Transition

end
