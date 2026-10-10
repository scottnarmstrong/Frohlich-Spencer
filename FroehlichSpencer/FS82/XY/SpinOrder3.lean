/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.SpinLower3

/-!
# the finite-volume form of (4.38)–(4.40) on boxes and cubes, `D = 3`
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical

variable {B : Dual3Box}

/-- A box with sides at most `N` has at most `8 (N + 1)³` dual links. -/
theorem card_dual3Links_le (N : ℕ) (hB : ∀ k, B k ≤ N) :
    Fintype.card (Dual3Links B) ≤ 8 * (N + 1) ^ 3 := by
  classical
  have h := card_window_le (fun e : Dual3Links B => e.1) Subtype.val_injective
    (fun _ => 0) 0 N
  have hall : (Finset.univ.filter fun e : Dual3Links B =>
      ∀ k, (0 : ℕ) ≤ cellBase e.1 k + 0 ∧ cellBase e.1 k ≤ 0 + N) = Finset.univ := by
    refine Finset.filter_true_of_mem fun e _ k => ⟨Nat.zero_le _, ?_⟩
    have := cellBase_le e.1 k
    have := hB k
    omega
  rw [← Finset.card_univ]
  calc (Finset.univ : Finset (Dual3Links B)).card
      = (Finset.univ.filter fun e : Dual3Links B =>
          ∀ k, (0 : ℕ) ≤ cellBase e.1 k + 0 ∧ cellBase e.1 k ≤ 0 + N).card := by rw [hall]
    _ ≤ 8 * (0 + N + 1) ^ 3 := by convert h using 2
    _ = 8 * (N + 1) ^ 3 := by rw [Nat.zero_add]

/-- **(4.38) with a bound on the residual energy**: the finite-volume form of (4.40) once the
residual energy is bounded as in (4.39). -/
theorem xy3_endpointExpectation_lower_of_residual_le {β : ℝ} (hβ : 136 ≤ β) (m : ℕ)
    (hm : ∀ k, m ≤ B k) (x y : XYSites B) (C : ℝ) (hC : xyDual3ResidualEnergy x y ≤ C) :
    Real.exp (-((1 / (2 * β) + xy3JensenRate β) * C) -
        5 * Real.pi ^ 2 * (Fintype.card (Dual3Links B) : ℝ) *
          Real.exp (-(xy3ActivityRate β * (m : ℝ)))) ≤
      (xyEndpointCharacterExpectation β x y).re := by
  refine le_trans (Real.exp_le_exp.mpr ?_) (xy3_endpointExpectation_lower hβ m hm x y)
  have hcoef : 0 ≤ 1 / (2 * β) + xy3JensenRate β := by
    have := xy3JensenRate_nonneg β
    have : 0 ≤ 1 / (2 * β) := by positivity
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hC hcoef]


/-- The Jensen rate `d(β)` of (4.38) tends to zero as `β → ∞`. -/
theorem xy3JensenRate_tendsto_zero :
    Filter.Tendsto xy3JensenRate Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun β : ℝ => 3 * β / 8) Filter.atTop Filter.atTop := by
    have h := (Filter.tendsto_id (α := ℝ) (x := Filter.atTop)).const_mul_atTop
      (by norm_num : (0 : ℝ) < 3 / 8)
    refine h.congr fun β => ?_
    simp only [id]
    ring
  have h2 : Filter.Tendsto (fun β : ℝ => 51 - 3 * β / 8) Filter.atTop Filter.atBot := by
    have h := Filter.tendsto_atBot_add_const_left Filter.atTop (51 : ℝ)
      (Filter.tendsto_neg_atTop_atBot.comp h1)
    refine h.congr fun β => ?_
    simp only [Function.comp_apply]
    ring
  have h3 := ((Real.tendsto_exp_atBot.comp h2).const_mul
    (81 * (1280 * (2 * Real.pi * 64) ^ 2 * FroehlichSpencer.FS82.Moment.Packing.polyTail11)))
  rw [mul_zero] at h3
  exact squeeze_zero' (Filter.Eventually.of_forall xy3JensenRate_nonneg)
    ((Filter.eventually_ge_atTop (136 : ℝ)).mono fun β hβ => xy3JensenRate_le hβ) h3

end FroehlichSpencer.FS82.XY

end
