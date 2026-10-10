/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Reduction.GlobalKuboBound
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Vanishing Kubo limit from dyadic Green events -/

public section

open MeasureTheory Topology

namespace FroehlichSpencer.Reduction

/-- At fixed `R`, the good contribution vanishes with `ε`; the exceptional
contribution tends to zero when `R` grows. This is the two-limit step in
(1.24)--(1.27), with `N_j = R 2^j / 8`. -/
theorem kubo_tendsto_zero_of_dyadic_events
    (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ) [IsProbabilityMeasure law]
    (E m K : ℝ) (hm : 0 < m) (hK : 0 ≤ K)
    (hEvents : ∀ R : ℝ, 1 ≤ R → ∀ x : Site ν,
      MeasurableSet (greenDecayEvent ν hν E m (dyadicGreenScale ν R x) x) ∧
      ENNReal.ofReal (1 - K / Real.rpow (dyadicGreenScale ν R x)
          ((ν + 5 : ℕ) : ℝ)) ≤
        configurationMeasure ν law
          (greenDecayEvent ν hν E m (dyadicGreenScale ν R x) x)) :
    Filter.Tendsto (fun ε : {ε : ℝ // ε ≠ 0} => kuboQuantity ν hν law E ε)
      (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  apply (ENNReal.tendsto_nhds_zero).2
  intro η hη
  by_cases hηtop : η = ⊤
  · filter_upwards with ε
    simp [hηtop]
  · have hδ : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη) hηtop
    let c : ℝ := 2 / (Real.pi * (ν : ℝ))
    let B : ℝ := c * badShellConstant ν K * (8 / 7 : ℝ)
    have hB : 0 ≤ B := by
      dsimp [B, c]
      unfold badShellConstant
      positivity
    let R : ℝ := max 1 (2 * B / η.toReal + 1)
    have hR : 1 ≤ R := le_max_left _ _
    have hRbig : 2 * B / η.toReal + 1 ≤ R := le_max_right _ _
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hRlarge : 2 * B / η.toReal ≤ R := by linarith
    have hBsmall : B ≤ η.toReal / 2 * R := by
      have hmul : 2 * B ≤ R * η.toReal :=
        (div_le_iff₀ hδ).1 hRlarge
      nlinarith [hmul]
    have hRleR3 : R ≤ R ^ 3 := by
      calc
        R = R * 1 := by ring
        _ ≤ R * R ^ 2 := mul_le_mul_of_nonneg_left
          (one_le_pow₀ hR) hRpos.le
        _ = R ^ 3 := by ring
    have hBsmall3 : B ≤ η.toReal / 2 * R ^ 3 := by
      exact hBsmall.trans (mul_le_mul_of_nonneg_left hRleR3 (by positivity))
    have hbadTail : B / R ^ 3 ≤ η.toReal / 2 :=
      (div_le_iff₀ (pow_pos hRpos 3)).2 hBsmall3
    let A : ℝ := c * Real.exp (m * R / 4) * greenDecayMoment ν m
    have hc : 0 ≤ c := by
      dsimp [c]
      positivity
    have hQ : 0 ≤ greenDecayMoment ν m := by
      dsimp [greenDecayMoment]
      exact tsum_nonneg (fun x => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg (mul_nonneg hc (Real.exp_nonneg _)) hQ
    let valEps : {ε : ℝ // ε ≠ 0} → ℝ := fun ε => ε.1
    let F : Filter {ε : ℝ // ε ≠ 0} :=
      Filter.comap valEps (𝓝[>] (0 : ℝ))
    have hval : Filter.Tendsto (fun ε : {ε : ℝ // ε ≠ 0} => ε.1) F
        (𝓝 (0 : ℝ)) := by
      have ht : Filter.Tendsto valEps
          (Filter.comap valEps (𝓝[>] (0 : ℝ))) (𝓝[>] (0 : ℝ)) :=
        Filter.tendsto_comap
      have ht' := ht.mono_right nhdsWithin_le_nhds
      simpa [F] using ht'
    have hpoly : ContinuousAt (fun t : ℝ => t ^ 2 * A) 0 :=
      (continuousAt_id.pow 2).mul_const A
    have hgoodT : Filter.Tendsto (fun ε : {ε : ℝ // ε ≠ 0} => ε.1 ^ 2 * A)
        F (𝓝 (0 : ℝ)) := by
      have ht := hpoly.tendsto.comp hval
      convert ht using 1
      · funext ε
        rfl
      · simp
    have hhalf : 0 < η.toReal / 2 := by positivity
    have hgoodEventually : ∀ᶠ ε : {ε : ℝ // ε ≠ 0} in F,
        ε.1 ^ 2 * A < η.toReal / 2 :=
      hgoodT.eventually (Iio_mem_nhds hhalf)
    filter_upwards [hgoodEventually] with ε hε
    have hreal : c * (ε.1 ^ 2 * Real.exp (m * R / 4) *
        greenDecayMoment ν m +
          badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ)) ≤ η.toReal := by
      have hidentity : c * (ε.1 ^ 2 * Real.exp (m * R / 4) *
          greenDecayMoment ν m +
            badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ)) =
          ε.1 ^ 2 * A + B / R ^ 3 := by
        dsimp [A, B, c]
        ring
      rw [hidentity]
      calc
        ε.1 ^ 2 * A + B / R ^ 3 ≤ η.toReal / 2 + η.toReal / 2 :=
          add_le_add (le_of_lt hε) hbadTail
        _ = η.toReal := by ring
    have hbound := kubo_le_dyadic_bound ν hν law E m K R hm hK hR ε
      (hEvents R hR)
    have hηbound : ENNReal.ofReal
        (c * (ε.1 ^ 2 * Real.exp (m * R / 4) * greenDecayMoment ν m +
          badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ))) ≤ η :=
      (ENNReal.ofReal_le_iff_le_toReal hηtop).2 hreal
    exact hbound.trans hηbound

end FroehlichSpencer.Reduction

end
