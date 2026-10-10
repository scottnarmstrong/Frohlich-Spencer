/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyAggregate
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyQuadratic
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryProfileClosure
public import FroehlichSpencer.BKT.Gaussian.ExponentialMoment
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Global energy of the pinned multiscale profile

This module isolates the final quadratic assembly. The remaining geometric
inputs are stated as finite energy and cross-term estimates on the base and
scale profiles, so the arithmetic cannot hide a scale-dependent constant.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- Edges on which a profile has nonzero gradient. -/
def boundaryEnergyGradientSupport {V E : Type*} [Fintype E]
    (G : Multigraph V E) (f : V → ℝ) : Finset E :=
  Finset.univ.filter fun e => G.grad f e ≠ 0

/-- If at most one summand is nonzero, a uniform bound on each summand is
preserved by the finite sum. -/
theorem abs_sum_le_of_pairwise_unique_nonzero
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (g : ι → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hg : ∀ i ∈ I, |g i| ≤ c)
    (hunique : ∀ i ∈ I, ∀ j ∈ I, g i ≠ 0 → g j ≠ 0 → i = j) :
    |∑ i ∈ I, g i| ≤ c := by
  classical
  let S := I.filter fun i => g i ≠ 0
  have hsum : (∑ i ∈ I, g i) = ∑ i ∈ S, g i := by
    symm
    apply Finset.sum_subset (by
      intro i hi
      exact (Finset.mem_filter.mp hi).1)
    intro i hi hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hi, hne⟩)
  have hcard : S.card ≤ 1 := Finset.card_le_one.mpr fun i hi j hj =>
    hunique i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    have hsingle : ∑ i ∈ S, g i = g a :=
      Finset.sum_eq_single a
        (fun b hb hba => by
          have hab : a = b := Finset.card_le_one.mp hcard a ha b hb
          exact (hba hab.symm).elim)
        (by simp [ha])
    rw [hsum, hsingle]
    have haI : a ∈ I := (Finset.mem_filter.mp ha).1
    exact hg a haI
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hsum, hSempty]
    simp
    exact hc

/-- A scale field inherits the single-tent gradient bound once the geometric
separation proves that no edge has nonzero gradients from two selected tents. -/
theorem boundaryEnergyScaleField_grad_le_of_edgewiseSeparation
    {L : ℕ} (ρ : ChargeDensity L) (P : Finset (Finset (Site L))) (r : ℝ)
    (hr : 0 < r)
    (hgrad : ∀ s ∈ P, ∀ e : SquareZeroBond L,
      |(squareZero L).grad (boundaryEnergySignedChildTent ρ s r) e| ≤ 1 / r)
    (hedge : ∀ e : SquareZeroBond L, ∀ s ∈ P, ∀ t ∈ P, s ≠ t →
      (squareZero L).grad (boundaryEnergySignedChildTent ρ s r) e ≠ 0 →
      (squareZero L).grad (boundaryEnergySignedChildTent ρ t r) e = 0) :
    ∀ e : SquareZeroBond L,
      |(squareZero L).grad (boundaryEnergyScaleField ρ P r) e| ≤ 1 / r := by
  classical
  intro e
  have hsumGrad : (squareZero L).grad (boundaryEnergyScaleField ρ P r) e =
      ∑ s ∈ P,
        (squareZero L).grad (boundaryEnergySignedChildTent ρ s r) e := by
    simp only [boundaryEnergyScaleField, Multigraph.grad]
    rw [Finset.sum_sub_distrib]
  rw [hsumGrad]
  exact abs_sum_le_of_pairwise_unique_nonzero P
    (fun s => (squareZero L).grad (boundaryEnergySignedChildTent ρ s r) e)
    (1 / r) (by positivity) (fun s hs => hgrad s hs e)
    (by
      intro s hs t ht hsn htn
      by_contra hst
      have hzero := hedge e s hs t ht hst hsn
      exact False.elim (htn hzero))

/-- A pointwise gradient bound and a support-edge count give the corresponding
Dirichlet-energy bound. -/
theorem boundaryEnergy_le_of_gradientSupport
    {V E : Type*} [Fintype E] (G : Multigraph V E)
    (f : V → ℝ) (N a : ℝ)
    (ha : 0 ≤ a)
    (hgrad : ∀ e, |G.grad f e| ≤ a)
    (hsupport : ((boundaryEnergyGradientSupport G f).card : ℝ) ≤ N) :
    G.energy f ≤ N * a ^ 2 := by
  classical
  let S := boundaryEnergyGradientSupport G f
  have henergySupport : G.energy f = ∑ e ∈ S, G.grad f e ^ 2 := by
    unfold Multigraph.energy
    calc
      (∑ e, G.grad f e ^ 2) =
          ∑ e, if G.grad f e ≠ 0 then G.grad f e ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro e he
            by_cases hne : G.grad f e = 0 <;> simp [hne]
      _ = ∑ e ∈ S, G.grad f e ^ 2 := by
            symm
            simp [S, boundaryEnergyGradientSupport, Finset.sum_filter]
  rw [henergySupport]
  calc
    (∑ e ∈ S, G.grad f e ^ 2) ≤ ∑ _e ∈ S, a ^ 2 := by
      apply Finset.sum_le_sum
      intro e he
      have h := hgrad e
      have hsq := (sq_le_sq₀ (abs_nonneg _) ha).2 h
      simpa only [sq_abs] using hsq
    _ = (S.card : ℝ) * a ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * a ^ 2 := by
      exact mul_le_mul_of_nonneg_right hsupport (sq_nonneg a)

/-- The cross term is controlled by the number of edges in the first profile's
gradient support and the two uniform gradient bounds. -/
theorem boundaryEnergyCrossTerm_abs_le_of_gradientSupport
    {V E : Type*} [Fintype E] (G : Multigraph V E)
    (f g : V → ℝ) (N a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ e, |G.grad f e| ≤ a)
    (hg : ∀ e, |G.grad g e| ≤ b)
    (hsupport : ((boundaryEnergyGradientSupport G f).card : ℝ) ≤ N) :
    |boundaryEnergyCrossTerm G f g| ≤ N * a * b := by
  classical
  let S := boundaryEnergyGradientSupport G f
  have hcrossSupport : boundaryEnergyCrossTerm G f g =
      ∑ e ∈ S, G.grad f e * G.grad g e := by
    unfold boundaryEnergyCrossTerm
    calc
      (∑ e, G.grad f e * G.grad g e) =
          ∑ e, if G.grad f e ≠ 0 then
            G.grad f e * G.grad g e else 0 := by
              apply Finset.sum_congr rfl
              intro e he
              by_cases hne : G.grad f e = 0 <;> simp [hne]
      _ = ∑ e ∈ S, G.grad f e * G.grad g e := by
            symm
            simp [S, boundaryEnergyGradientSupport, Finset.sum_filter]
  rw [hcrossSupport]
  calc
    |∑ e ∈ S, G.grad f e * G.grad g e| ≤
        ∑ e ∈ S, |G.grad f e * G.grad g e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ S, a * b := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      exact mul_le_mul (hf e) (hg e) (abs_nonneg _) ha
    _ = (S.card : ℝ) * a * b := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ N * a * b := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsupport ha) hb

/-- The dyadic tail from a fixed scale through any finite coarser cutoff is at
most one. The exact sum telescopes to `1 - 2^j / 2^n`. -/
theorem boundaryEnergy_dyadicTail_eq {j n : ℕ} (hjn : j ≤ n) :
    (∑ k ∈ Finset.Icc (j + 1) n, (2 : ℝ) ^ j / (2 : ℝ) ^ k) =
      1 - (2 : ℝ) ^ j / (2 : ℝ) ^ n := by
  induction n with
  | zero =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero hjn
      subst j
      simp
  | succ n ih =>
      by_cases h : j ≤ n
      · rw [Finset.sum_Icc_succ_top (by omega)
          (fun k : ℕ => (2 : ℝ) ^ j / (2 : ℝ) ^ k), ih h]
        have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
          rw [pow_succ]
          ring
        rw [hpow]
        have hden : (2 : ℝ) ^ n ≠ 0 := by positivity
        field_simp
        ring
      · have hj : j = n + 1 := by omega
        subst j
        simp

/-- Summing only the future scales in any interval `1..n` costs at most one
fine-to-coarse ratio. -/
theorem boundaryEnergy_dyadicFutureSum_le_one (j n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n,
      if j < k then (2 : ℝ) ^ j / (2 : ℝ) ^ k else 0) ≤ 1 := by
  classical
  let S := (Finset.Icc 1 n).filter fun k => j < k
  have hsum : (∑ k ∈ Finset.Icc 1 n,
      if j < k then (2 : ℝ) ^ j / (2 : ℝ) ^ k else 0) =
      ∑ k ∈ S, (2 : ℝ) ^ j / (2 : ℝ) ^ k := by
    dsimp [S]
    rw [Finset.sum_filter]
  by_cases hjn : j ≤ n
  · have hsub : S ⊆ Finset.Icc (j + 1) n := by
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hk'.1).2⟩
    rw [hsum]
    calc
      (∑ k ∈ S, (2 : ℝ) ^ j / (2 : ℝ) ^ k) ≤
          ∑ k ∈ Finset.Icc (j + 1) n, (2 : ℝ) ^ j / (2 : ℝ) ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro k hk _
          positivity)
      _ = 1 - (2 : ℝ) ^ j / (2 : ℝ) ^ n := boundaryEnergy_dyadicTail_eq hjn
      _ ≤ 1 := by
        have hnonneg : 0 ≤ (2 : ℝ) ^ j / (2 : ℝ) ^ n := by positivity
        linarith
  · have hS : S = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro k hk hlt
      have hk' := Finset.mem_Icc.mp hk
      exact hjn (by omega)
    rw [hsum, hS]
    simp

/-- Explicit fine-to-coarse cross-term estimate from a local fine edge count
and the two tent-gradient bounds. -/
theorem boundaryEnergy_crossScale_le_of_gradientSupport
    {V E : Type*} [Fintype E] (G : Multigraph V E)
    (f g : V → ℝ) (j k : ℕ) (N : ℝ)
    (hf : ∀ e, |G.grad f e| ≤ 1 / (2 : ℝ) ^ j)
    (hg : ∀ e, |G.grad g e| ≤ 1 / (2 : ℝ) ^ k)
    (hsupport : (boundaryEnergyGradientSupport G f).card ≤ N) :
    |boundaryEnergyCrossTerm G f g| ≤
      N * (1 / (2 : ℝ) ^ j) * (1 / (2 : ℝ) ^ k) := by
  have hjpos : 0 ≤ 1 / (2 : ℝ) ^ j := by positivity
  have hkpos : 0 ≤ 1 / (2 : ℝ) ^ k := by positivity
  exact boundaryEnergyCrossTerm_abs_le_of_gradientSupport G f g N
    (1 / (2 : ℝ) ^ j) (1 / (2 : ℝ) ^ k) hjpos hkpos hf hg hsupport

/-- The geometric sum over coarser dyadic scales costs at most one for each
fine scale, so any nonnegative fine-scale count remains summable with the
same total weight. -/
theorem boundaryEnergy_weightedDyadicFutureSum_le
    (n : ℕ) (Q : ℕ → ℝ) (hQ : ∀ j ∈ Finset.Icc 1 n, 0 ≤ Q j) :
    (∑ j ∈ Finset.Icc 1 n, Q j *
      ∑ k ∈ Finset.Icc 1 n,
        if j < k then (2 : ℝ) ^ j / (2 : ℝ) ^ k else 0) ≤
      ∑ j ∈ Finset.Icc 1 n, Q j := by
  apply Finset.sum_le_sum
  intro j hj
  have htail := boundaryEnergy_dyadicFutureSum_le_one j n
  have htail0 : 0 ≤ ∑ k ∈ Finset.Icc 1 n,
      if j < k then (2 : ℝ) ^ j / (2 : ℝ) ^ k else 0 := by
    apply Finset.sum_nonneg
    intro k hk
    split_ifs with h
    · positivity
    · norm_num
  have hmul := mul_le_mul_of_nonneg_left htail (hQ j hj)
  nlinarith

/-- Summing the pairwise fine-to-coarse estimate over all scales costs at most
`50` times the total fine-scale count. -/
theorem boundaryEnergy_crossScaleSum_le
    (n : ℕ) (Q : ℕ → ℝ)
    (hQ : ∀ j ∈ Finset.Icc 1 n, 0 ≤ Q j)
    (cross : ℕ → ℕ → ℝ)
    (hcross : ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n, j < k →
      |cross j k| ≤ 50 * Q j * ((2 : ℝ) ^ j / (2 : ℝ) ^ k)) :
    (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
      if j < k then |cross j k| else 0) ≤
      50 * (∑ j ∈ Finset.Icc 1 n, Q j) := by
  have hinner (j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
      (∑ k ∈ Finset.Icc 1 n, if j < k then |cross j k| else 0) ≤
        50 * Q j * (∑ k ∈ Finset.Icc 1 n,
          if j < k then (2 : ℝ) ^ j / (2 : ℝ) ^ k else 0) := by
    calc
      (∑ k ∈ Finset.Icc 1 n, if j < k then |cross j k| else 0) ≤
          ∑ k ∈ Finset.Icc 1 n,
            (50 * Q j) * (if j < k then (2 : ℝ) ^ j / (2 : ℝ) ^ k else 0) := by
              apply Finset.sum_le_sum
              intro k hk
              split_ifs with h
              · exact hcross j hj k hk h
              · simp
      _ = 50 * Q j * (∑ k ∈ Finset.Icc 1 n,
            if j < k then (2 : ℝ) ^ j / (2 : ℝ) ^ k else 0) := by
              rw [Finset.mul_sum]
  calc
    (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
        if j < k then |cross j k| else 0) ≤
      ∑ j ∈ Finset.Icc 1 n, 50 * Q j *
        (∑ k ∈ Finset.Icc 1 n,
          if j < k then (2 : ℝ) ^ j / (2 : ℝ) ^ k else 0) := by
            apply Finset.sum_le_sum
            intro j hj
            exact hinner j hj
    _ = 50 * (∑ j ∈ Finset.Icc 1 n, Q j *
          ∑ k ∈ Finset.Icc 1 n,
            if j < k then (2 : ℝ) ^ j / (2 : ℝ) ^ k else 0) := by
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]
    _ ≤ 50 * (∑ j ∈ Finset.Icc 1 n, Q j) := by
      exact mul_le_mul_of_nonneg_left
        (boundaryEnergy_weightedDyadicFutureSum_le n Q hQ) (by norm_num)

/-- The explicit base-plus-selected-tents profile used in the global energy
estimate. -/
def boundaryEnergyAggregateField (ρ : ChargeDensity L) (Msel α : ℝ)
    (n : ℕ) (C : ℕ → Finset (Finset (Site L)))
    (base : RotatorDualFace L → ℝ) : RotatorDualFace L → ℝ := fun z =>
  base z + ∑ j ∈ Finset.Icc 1 n,
    boundaryEnergyScaleField ρ
      (pinnedPPrime Msel α j ρ (C j)) ((2 : ℝ) ^ j) z

/-- The explicit aggregate field retains the charge pairing and zero boundary
values of the separately supplied base field and every selected scale field. -/
theorem boundaryEnergyAggregateField_pairing_and_boundary
    (Miso Msel α : ℝ) (hMiso : 1 < Miso) (hα : 1 ≤ α)
    (hMsel : 1 ≤ Msel) (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    {N : Finset (ChargeDensity L)} (hgeom : AppendixDChargeGeometry Miso α N)
    {ρ : ChargeDensity L} (hρ : ρ ∈ N)
    (n : ℕ) (C : ℕ → Finset (Finset (Site L)))
    (hC : ∀ j ∈ Finset.Icc 1 n,
      IsMinimumSquareCover .free L j ρ (C j))
    (A₀ : ℝ) (base : RotatorDualFace L → ℝ)
    (hbaseRoot : base none = 0)
    (hbasePair : A₀ / 2 ≤ ∑ x, base (some x) * (ρ x : ℝ))
    (hbaseBoundary : ∀ x : Site L, siteBoundaryDepth x = 1 →
      base (some x) = 0) :
    (boundaryEnergyAggregateField ρ Msel α n C base) none = 0 ∧
      A₀ / 2 + ∑ j ∈ Finset.Icc 1 n,
        ((pinnedPPrime Msel α j ρ (C j)).card : ℝ) ≤
          ∑ x, (boundaryEnergyAggregateField ρ Msel α n C base) (some x) * (ρ x : ℝ) ∧
      ∀ x : Site L, siteBoundaryDepth x = 1 →
        (boundaryEnergyAggregateField ρ Msel α n C base) (some x) = 0 := by
  classical
  let V : ℕ → RotatorDualFace L → ℝ := fun j =>
    boundaryEnergyScaleField ρ
      (pinnedPPrime Msel α j ρ (C j)) ((2 : ℝ) ^ j)
  have hV (j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
      V j none = 0 ∧
        ((pinnedPPrime Msel α j ρ (C j)).card : ℝ) ≤
          ∑ x, V j (some x) * (ρ x : ℝ) ∧
        ∀ x : Site L, siteBoundaryDepth x = 1 → V j (some x) = 0 := by
    simpa only [V] using boundaryEnergyTerminalScaleField_properties
      Miso Msel α hMiso hα hMsel hmargin ρ N hgeom.isolated hρ j (C j) (hC j hj)
  refine ⟨?_, ?_, ?_⟩
  · simp [boundaryEnergyAggregateField, hbaseRoot, V,
      Finset.sum_eq_zero (fun j hj => (hV j hj).1)]
  · have hscalePair :
        (∑ j ∈ Finset.Icc 1 n,
          ((pinnedPPrime Msel α j ρ (C j)).card : ℝ)) ≤
          ∑ j ∈ Finset.Icc 1 n, ∑ x, V j (some x) * (ρ x : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hV j hj).2.1
    have hpairId :
        (∑ x, (boundaryEnergyAggregateField ρ Msel α n C base) (some x) * (ρ x : ℝ)) =
          (∑ x, base (some x) * (ρ x : ℝ)) +
            ∑ j ∈ Finset.Icc 1 n, ∑ x, V j (some x) * (ρ x : ℝ) := by
      calc
        _ = ∑ x, (base (some x) * (ρ x : ℝ) +
            (∑ j ∈ Finset.Icc 1 n, V j (some x)) * (ρ x : ℝ)) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp [boundaryEnergyAggregateField, V]
              ring
        _ = (∑ x, base (some x) * (ρ x : ℝ)) +
            ∑ x, (∑ j ∈ Finset.Icc 1 n, V j (some x)) * (ρ x : ℝ) := by
              rw [Finset.sum_add_distrib]
        _ = (∑ x, base (some x) * (ρ x : ℝ)) +
            ∑ x, ∑ j ∈ Finset.Icc 1 n, V j (some x) * (ρ x : ℝ) := by
              congr 1
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_mul]
        _ = (∑ x, base (some x) * (ρ x : ℝ)) +
            ∑ j ∈ Finset.Icc 1 n, ∑ x, V j (some x) * (ρ x : ℝ) := by
              congr 1
              rw [Finset.sum_comm]
    calc
      A₀ / 2 +
          ∑ j ∈ Finset.Icc 1 n,
            ((pinnedPPrime Msel α j ρ (C j)).card : ℝ) ≤
          (∑ x, base (some x) * (ρ x : ℝ)) +
            ∑ j ∈ Finset.Icc 1 n, ∑ x, V j (some x) * (ρ x : ℝ) :=
              add_le_add hbasePair hscalePair
      _ = ∑ x, (boundaryEnergyAggregateField ρ Msel α n C base) (some x) *
          (ρ x : ℝ) := hpairId.symm
  · intro x hx
    simp only [boundaryEnergyAggregateField, hbaseBoundary x hx, zero_add]
    rw [Finset.sum_eq_zero]
    intro j hj
    exact (hV j hj).2.2 x hx

private theorem boundaryEnergyCrossTerm_sum_right
    {V : Type*} {E : Type*} [Fintype E] [DecidableEq E]
    {ι : Type*} [DecidableEq ι] (G : Multigraph V E)
    (u : V → ℝ) (I : Finset ι) (v : ι → V → ℝ) :
    boundaryEnergyCrossTerm G u (fun x => ∑ i ∈ I, v i x) =
      ∑ i ∈ I, boundaryEnergyCrossTerm G u (v i) := by
  classical
  unfold boundaryEnergyCrossTerm
  have hgrad (e : E) :
      G.grad (fun x => ∑ i ∈ I, v i x) e = ∑ i ∈ I, G.grad (v i) e := by
    simp only [Multigraph.grad]
    rw [Finset.sum_sub_distrib]
  calc
    (∑ e, G.grad u e * G.grad (fun x => ∑ i ∈ I, v i x) e) =
        ∑ e, ∑ i ∈ I, G.grad u e * G.grad (v i) e := by
          apply Finset.sum_congr rfl
          intro e he
          rw [hgrad e, Finset.mul_sum]
    _ = ∑ i ∈ I, ∑ e, G.grad u e * G.grad (v i) e := by
          convert (Finset.sum_comm (s := (Finset.univ : Finset E))
            (t := I) (f := fun e i => G.grad u e * G.grad (v i) e)) using 1

private theorem boundaryEnergyCrossTerm_comm
    {V E : Type*} [Fintype E] (G : Multigraph V E)
    (f g : V → ℝ) :
    boundaryEnergyCrossTerm G f g = boundaryEnergyCrossTerm G g f := by
  unfold boundaryEnergyCrossTerm
  apply Finset.sum_congr rfl
  intro e he
  rw [mul_comm]

/-- The finite scale quadratic form is the sum of the diagonal energies and
twice the absolute fine-to-coarse cross sum. -/
theorem boundaryEnergyOrderedCrossSum_eq_diagonal_add_two_fineCoarse
    {V E : Type*} [Fintype E] (G : Multigraph V E)
    (I : Finset ℕ) (v : ℕ → V → ℝ) :
    boundaryEnergyOrderedCrossSum G I v =
      (∑ i ∈ I, G.energy (v i)) +
        2 * (∑ i ∈ I, ∑ j ∈ I,
          if i < j then |boundaryEnergyCrossTerm G (v i) (v j)| else 0) := by
  classical
  let F : ℕ → ℕ → ℝ := fun i j =>
    |boundaryEnergyCrossTerm G (v i) (v j)|
  have hinner (i : ℕ) (hi : i ∈ I) :
      (∑ j ∈ I, F i j) = F i i +
        (∑ j ∈ I, if i < j then F i j else 0) +
        ∑ j ∈ I, if j < i then F i j else 0 := by
    calc
      (∑ j ∈ I, F i j) =
          ∑ j ∈ I,
            ((if j = i then F i j else 0) +
              (if i < j then F i j else 0) +
              (if j < i then F i j else 0)) := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j = i
                · simp [hji]
                · by_cases hij : i < j
                  · have hji' : ¬ j < i := by omega
                    simp [hji, hij, hji']
                  · have hji' : j < i := by omega
                    simp [hji, hij, hji']
      _ = (∑ j ∈ I, if j = i then F i j else 0) +
            (∑ j ∈ I, if i < j then F i j else 0) +
            ∑ j ∈ I, if j < i then F i j else 0 := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = F i i + (∑ j ∈ I, if i < j then F i j else 0) +
            ∑ j ∈ I, if j < i then F i j else 0 := by
              rw [Finset.sum_ite_eq' I i (F i)]
              simp [hi]
  have hlow :
      (∑ i ∈ I, ∑ j ∈ I, if j < i then F i j else 0) =
        (∑ i ∈ I, ∑ j ∈ I, if i < j then F i j else 0) := by
    calc
      (∑ i ∈ I, ∑ j ∈ I, if j < i then F i j else 0) =
          ∑ j ∈ I, ∑ i ∈ I, if j < i then F i j else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ j ∈ I, ∑ i ∈ I, if j < i then
            |boundaryEnergyCrossTerm G (v j) (v i)| else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro i hi
              split_ifs with h
              · simp [F, boundaryEnergyCrossTerm_comm]
              · rfl
      _ = ∑ i ∈ I, ∑ j ∈ I, if i < j then F i j else 0 := by
            rfl
  have hdiag : ∀ i, F i i = G.energy (v i) := by
    intro i
    have hcross : boundaryEnergyCrossTerm G (v i) (v i) = G.energy (v i) := by
      unfold boundaryEnergyCrossTerm Multigraph.energy
      apply Finset.sum_congr rfl
      intro e he
      simp [pow_two]
    change |boundaryEnergyCrossTerm G (v i) (v i)| = G.energy (v i)
    rw [hcross]
    unfold Multigraph.energy
    apply abs_of_nonneg
    apply Finset.sum_nonneg
    intro e he
    positivity
  unfold boundaryEnergyOrderedCrossSum
  calc
    (∑ i ∈ I, ∑ j ∈ I, F i j) =
        ∑ i ∈ I, (F i i +
          (∑ j ∈ I, if i < j then F i j else 0) +
          ∑ j ∈ I, if j < i then F i j else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hinner i hi
    _ = (∑ i ∈ I, G.energy (v i)) +
        2 * (∑ i ∈ I, ∑ j ∈ I, if i < j then F i j else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hlow]
          simp_rw [hdiag]
          ring

/-- The diagonal costs one local-energy budget, while the two orientations of
each fine-to-coarse interaction cost twice the geometric cross budget. -/
theorem boundaryEnergyOrderedCrossSum_le_of_dyadicBounds
    {V E : Type*} [Fintype E] (G : Multigraph V E)
    (n : ℕ) (v : ℕ → V → ℝ) (Q : ℕ → ℝ) (P : ℝ)
    (hQ : ∀ j ∈ Finset.Icc 1 n, 0 ≤ Q j)
    (hQsum : ∑ j ∈ Finset.Icc 1 n, Q j ≤ P)
    (hdiag : ∑ j ∈ Finset.Icc 1 n, G.energy (v j) ≤ 50 * P)
    (hcross : ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n, j < k →
      |boundaryEnergyCrossTerm G (v j) (v k)| ≤
        50 * Q j * ((2 : ℝ) ^ j / (2 : ℝ) ^ k)) :
    boundaryEnergyOrderedCrossSum G (Finset.Icc 1 n) v ≤ 150 * P := by
  have hupper := boundaryEnergy_crossScaleSum_le n Q hQ
    (fun j k => boundaryEnergyCrossTerm G (v j) (v k)) hcross
  have hupper' : (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
      if j < k then |boundaryEnergyCrossTerm G (v j) (v k)| else 0) ≤ 50 * P := by
    calc
      _ ≤ 50 * (∑ j ∈ Finset.Icc 1 n, Q j) := hupper
      _ ≤ 50 * P := mul_le_mul_of_nonneg_left hQsum (by norm_num)
  rw [boundaryEnergyOrderedCrossSum_eq_diagonal_add_two_fineCoarse]
  nlinarith [hdiag, hupper']

/-- A scale-local edge count of `50 · Q_j · 4^j` together with the tent
gradient bound `2^{-j}` supplies both the diagonal and fine-to-coarse bounds
needed above. -/
theorem boundaryEnergyOrderedCrossSum_le_of_gradientLocalization
    {V E : Type*} [Fintype E] (G : Multigraph V E)
    (n : ℕ) (v : ℕ → V → ℝ) (Q : ℕ → ℝ) (P : ℝ)
    (hQ : ∀ j ∈ Finset.Icc 1 n, 0 ≤ Q j)
    (hQsum : ∑ j ∈ Finset.Icc 1 n, Q j ≤ P)
    (hgrad : ∀ j ∈ Finset.Icc 1 n, ∀ e,
      |G.grad (v j) e| ≤ 1 / (2 : ℝ) ^ j)
    (hsupport : ∀ j ∈ Finset.Icc 1 n,
      ((boundaryEnergyGradientSupport G (v j)).card : ℝ) ≤
        50 * Q j * ((2 : ℝ) ^ j) ^ 2) :
    boundaryEnergyOrderedCrossSum G (Finset.Icc 1 n) v ≤ 150 * P := by
  apply boundaryEnergyOrderedCrossSum_le_of_dyadicBounds G n v Q P hQ hQsum
  · calc
      (∑ j ∈ Finset.Icc 1 n, G.energy (v j)) ≤
          ∑ j ∈ Finset.Icc 1 n, 50 * Q j := by
            apply Finset.sum_le_sum
            intro j hj
            have hlocal := boundaryEnergy_le_of_gradientSupport G (v j)
              (50 * Q j * ((2 : ℝ) ^ j) ^ 2) (1 / (2 : ℝ) ^ j)
              (by positivity) (hgrad j hj) (hsupport j hj)
            have hpow : (2 : ℝ) ^ j ≠ 0 := by positivity
            have hrewrite :
                (50 * Q j * ((2 : ℝ) ^ j) ^ 2) *
                    (1 / (2 : ℝ) ^ j) ^ 2 = 50 * Q j := by
              field_simp
            rw [hrewrite] at hlocal
            exact hlocal
      _ = 50 * ∑ j ∈ Finset.Icc 1 n, Q j := by
            rw [Finset.mul_sum]
      _ ≤ 50 * P := mul_le_mul_of_nonneg_left hQsum (by norm_num)
  · intro j hj k hk hjk
    have hlocal := boundaryEnergyCrossTerm_abs_le_of_gradientSupport G
      (v j) (v k) (50 * Q j * ((2 : ℝ) ^ j) ^ 2)
      (1 / (2 : ℝ) ^ j) (1 / (2 : ℝ) ^ k)
      (by positivity) (by positivity) (hgrad j hj) (hgrad k hk) (hsupport j hj)
    have hpowj : (2 : ℝ) ^ j ≠ 0 := by positivity
    have hpowk : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hrewrite :
        (50 * Q j * ((2 : ℝ) ^ j) ^ 2) *
            (1 / (2 : ℝ) ^ j) * (1 / (2 : ℝ) ^ k) =
          50 * Q j * ((2 : ℝ) ^ j / (2 : ℝ) ^ k) := by
      field_simp
    rw [hrewrite] at hlocal
    exact hlocal

/-- If the base has energy `4m`, its absolute cross terms with all scales sum
to at most `4m`, and the scale aggregate has energy at most `150P`, then the
total pinned profile has energy at most `12m + 150P`. -/
theorem boundaryEnergy_aggregateField_energy_le
    (ρ : ChargeDensity L) (Msel α : ℝ)
    (n : ℕ) (C : ℕ → Finset (Finset (Site L)))
    (base : RotatorDualFace L → ℝ) (m P : ℝ)
    (hbaseEnergy : (squareZero L).energy base ≤ 4 * m)
    (hbaseCross :
      ∑ j ∈ Finset.Icc 1 n,
        |boundaryEnergyCrossTerm (squareZero L) base
          (boundaryEnergyScaleField ρ
            (pinnedPPrime Msel α j ρ (C j))
            ((2 : ℝ) ^ j))| ≤ 4 * m)
    (hscaleOrderedCross : boundaryEnergyOrderedCrossSum (squareZero L)
      (Finset.Icc 1 n) (fun j z =>
        boundaryEnergyScaleField ρ
          (pinnedPPrime Msel α j ρ (C j))
          ((2 : ℝ) ^ j) z) ≤ 150 * P) :
    (squareZero L).energy (boundaryEnergyAggregateField ρ Msel α n C base) ≤
      12 * m + 150 * P := by
  classical
  let V : ℕ → RotatorDualFace L → ℝ := fun j =>
    boundaryEnergyScaleField ρ
      (pinnedPPrime Msel α j ρ (C j)) ((2 : ℝ) ^ j)
  let S : RotatorDualFace L → ℝ := fun z => ∑ j ∈ Finset.Icc 1 n, V j z
  have hscaleEnergy : (squareZero L).energy S ≤ 150 * P := by
    have hquad := energy_finset_sum_le_orderedCrossSum (squareZero L)
      (Finset.Icc 1 n) V
    have hordered : boundaryEnergyOrderedCrossSum (squareZero L)
        (Finset.Icc 1 n) V ≤ 150 * P := by
      simpa [V] using hscaleOrderedCross
    exact hquad.trans hordered
  have hcrossAbs : |boundaryEnergyCrossTerm (squareZero L) base S| ≤ 4 * m := by
    rw [boundaryEnergyCrossTerm_sum_right]
    calc
      |∑ j ∈ Finset.Icc 1 n,
          boundaryEnergyCrossTerm (squareZero L) base (V j)| ≤
          ∑ j ∈ Finset.Icc 1 n,
            |boundaryEnergyCrossTerm (squareZero L) base (V j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ 4 * m := by
          simpa [V] using hbaseCross
  have henergy : (squareZero L).energy (base + S) ≤
      (squareZero L).energy base + 2 * (4 * m) + 150 * P := by
    rw [energy_add]
    have hc : boundaryEnergyCrossTerm (squareZero L) base S ≤ 4 * m :=
      (le_abs_self _).trans hcrossAbs
    have hc' : (∑ e, (squareZero L).grad base e *
        (squareZero L).grad S e) ≤ 4 * m := by
      simpa [boundaryEnergyCrossTerm] using hc
    have hS : (squareZero L).energy S ≤ 150 * P := by
      simpa [S, V] using hscaleEnergy
    nlinarith [hbaseEnergy, hc', hS]
  have hdef : boundaryEnergyAggregateField ρ Msel α n C base = base + S := by
    funext z
    simp [boundaryEnergyAggregateField, V, S]
  rw [hdef]
  calc
    (squareZero L).energy (base + S) ≤
        (squareZero L).energy base + 2 * (4 * m) + 150 * P := henergy
    _ ≤ 12 * m + 150 * P := by nlinarith [hbaseEnergy]

/-- Converting the profile bound to the Appendix-D variables gives a uniform
constant `150` (hence Green-energy constant `1/600`). -/
theorem boundaryEnergy_aggregateField_energy_le_area
    (ρ : ChargeDensity L) (Msel α : ℝ)
    (n : ℕ) (C : ℕ → Finset (Finset (Site L)))
    (base : RotatorDualFace L → ℝ) (A₀ P m : ℝ)
    (hA₀ : 0 ≤ A₀) (hmA₀ : m ≤ A₀)
    (hbaseEnergy : (squareZero L).energy base ≤ 4 * m)
    (hbaseCross :
      ∑ j ∈ Finset.Icc 1 n,
        |boundaryEnergyCrossTerm (squareZero L) base
          (boundaryEnergyScaleField ρ
            (pinnedPPrime Msel α j ρ (C j))
            ((2 : ℝ) ^ j))| ≤ 4 * m)
    (hscaleOrderedCross : boundaryEnergyOrderedCrossSum (squareZero L)
      (Finset.Icc 1 n) (fun j z =>
        boundaryEnergyScaleField ρ
          (pinnedPPrime Msel α j ρ (C j))
          ((2 : ℝ) ^ j) z) ≤ 150 * P) :
    (squareZero L).energy (boundaryEnergyAggregateField ρ Msel α n C base) ≤
      150 * (A₀ + P) := by
  have h := boundaryEnergy_aggregateField_energy_le ρ Msel α n C base m P
    hbaseEnergy hbaseCross hscaleOrderedCross
  calc
    (squareZero L).energy (boundaryEnergyAggregateField ρ Msel α n C base) ≤
        12 * m + 150 * P := h
    _ ≤ 150 * (A₀ + P) := by nlinarith

/-- Local support counts for the base and the scale fields imply the full
global energy estimate. The base support costs `4m`; a scale-`j` field costs
`50 · |Q_j| · 4^j`. The dyadic tail controls both kinds of cross terms. -/
theorem boundaryEnergy_aggregateField_energy_le_area_of_localization
    (ρ : ChargeDensity L) (Msel α : ℝ)
    (n : ℕ) (C : ℕ → Finset (Finset (Site L)))
    (base : RotatorDualFace L → ℝ) (A₀ P m : ℝ)
    (hA₀ : 0 ≤ A₀) (hm : 0 ≤ m) (hmA₀ : m ≤ A₀)
    (hPcount : ∑ j ∈ Finset.Icc 1 n,
      ((pinnedPPrime Msel α j ρ (C j)).card : ℝ) ≤ P)
    (hbaseGrad : ∀ e, |(squareZero L).grad base e| ≤ 1)
    (hbaseSupport :
      ((boundaryEnergyGradientSupport (squareZero L) base).card : ℝ) ≤ 4 * m)
    (hscaleGrad : ∀ j ∈ Finset.Icc 1 n, ∀ e,
      |(squareZero L).grad
        (boundaryEnergyScaleField ρ
          (pinnedPPrime Msel α j ρ (C j)) ((2 : ℝ) ^ j)) e| ≤
            1 / (2 : ℝ) ^ j)
    (hscaleSupport : ∀ j ∈ Finset.Icc 1 n,
      ((boundaryEnergyGradientSupport (squareZero L)
        (boundaryEnergyScaleField ρ
          (pinnedPPrime Msel α j ρ (C j)) ((2 : ℝ) ^ j))).card : ℝ) ≤
        50 * ((pinnedPPrime Msel α j ρ (C j)).card : ℝ) *
          ((2 : ℝ) ^ j) ^ 2) :
    (squareZero L).energy (boundaryEnergyAggregateField ρ Msel α n C base) ≤
      150 * (A₀ + P) := by
  let V : ℕ → RotatorDualFace L → ℝ := fun j =>
    boundaryEnergyScaleField ρ
      (pinnedPPrime Msel α j ρ (C j)) ((2 : ℝ) ^ j)
  let Q : ℕ → ℝ := fun j =>
    ((pinnedPPrime Msel α j ρ (C j)).card : ℝ)
  have hbaseEnergy : (squareZero L).energy base ≤ 4 * m := by
    simpa using boundaryEnergy_le_of_gradientSupport (squareZero L) base
      (4 * m) 1 (by norm_num) hbaseGrad hbaseSupport
  have hbaseCross :
      ∑ j ∈ Finset.Icc 1 n,
        |boundaryEnergyCrossTerm (squareZero L) base (V j)| ≤ 4 * m := by
    have hbaseRatio :
        (∑ j ∈ Finset.Icc 1 n, (1 / (2 : ℝ) ^ j)) ≤ 1 := by
      have htail := boundaryEnergy_dyadicTail_eq
        (j := 0) (n := n) (Nat.zero_le n)
      have hEq : (∑ j ∈ Finset.Icc 1 n, (1 / (2 : ℝ) ^ j)) =
          1 - 1 / (2 : ℝ) ^ n := by
        simpa using htail
      rw [hEq]
      have hnonneg : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ n := by positivity
      linarith
    calc
      (∑ j ∈ Finset.Icc 1 n,
          |boundaryEnergyCrossTerm (squareZero L) base (V j)|) ≤
        ∑ j ∈ Finset.Icc 1 n, (4 * m) * (1 / (2 : ℝ) ^ j) := by
          apply Finset.sum_le_sum
          intro j hj
          have hlocal := boundaryEnergyCrossTerm_abs_le_of_gradientSupport
            (squareZero L) base (V j) (4 * m) 1 (1 / (2 : ℝ) ^ j)
            (by linarith) (by positivity) hbaseGrad (hscaleGrad j hj) hbaseSupport
          simpa [mul_one] using hlocal
      _ = (4 * m) * (∑ j ∈ Finset.Icc 1 n, 1 / (2 : ℝ) ^ j) := by
          rw [Finset.mul_sum]
      _ ≤ 4 * m := by
          have hmul := mul_le_mul_of_nonneg_left hbaseRatio (by linarith : 0 ≤ 4 * m)
          nlinarith
  have hQ : ∀ j ∈ Finset.Icc 1 n, 0 ≤ Q j := by
    intro j hj
    simp [Q]
  have hdiag : ∑ j ∈ Finset.Icc 1 n, (squareZero L).energy (V j) ≤
      50 * P := by
    calc
      (∑ j ∈ Finset.Icc 1 n, (squareZero L).energy (V j)) ≤
        ∑ j ∈ Finset.Icc 1 n, 50 * Q j := by
          apply Finset.sum_le_sum
          intro j hj
          have hlocal := boundaryEnergy_le_of_gradientSupport (squareZero L)
            (V j) (50 * Q j * ((2 : ℝ) ^ j) ^ 2) (1 / (2 : ℝ) ^ j)
            (by positivity) (hscaleGrad j hj) (by simpa [Q] using hscaleSupport j hj)
          have hpow : (2 : ℝ) ^ j ≠ 0 := by positivity
          have hrewrite : (50 * Q j * ((2 : ℝ) ^ j) ^ 2) *
              (1 / (2 : ℝ) ^ j) ^ 2 = 50 * Q j := by field_simp
          rw [hrewrite] at hlocal
          exact hlocal
      _ = 50 * (∑ j ∈ Finset.Icc 1 n, Q j) := by rw [Finset.mul_sum]
      _ ≤ 50 * P := by
        exact mul_le_mul_of_nonneg_left (by simpa [Q] using hPcount) (by norm_num)
  have hcross : ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n, j < k →
      |boundaryEnergyCrossTerm (squareZero L) (V j) (V k)| ≤
        50 * Q j * ((2 : ℝ) ^ j / (2 : ℝ) ^ k) := by
    intro j hj k hk hjk
    have hlocal := boundaryEnergyCrossTerm_abs_le_of_gradientSupport
      (squareZero L) (V j) (V k) (50 * Q j * ((2 : ℝ) ^ j) ^ 2)
      (1 / (2 : ℝ) ^ j) (1 / (2 : ℝ) ^ k)
      (by positivity) (by positivity) (hscaleGrad j hj) (hscaleGrad k hk)
      (by simpa [Q] using hscaleSupport j hj)
    have hpowj : (2 : ℝ) ^ j ≠ 0 := by positivity
    have hpowk : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hrewrite : (50 * Q j * ((2 : ℝ) ^ j) ^ 2) *
        (1 / (2 : ℝ) ^ j) * (1 / (2 : ℝ) ^ k) =
          50 * Q j * ((2 : ℝ) ^ j / (2 : ℝ) ^ k) := by field_simp
    rw [hrewrite] at hlocal
    exact hlocal
  have hordered := boundaryEnergyOrderedCrossSum_le_of_dyadicBounds
    (squareZero L) n V Q P hQ (by simpa [Q] using hPcount) hdiag hcross
  exact boundaryEnergy_aggregateField_energy_le_area ρ Msel α n C base A₀ P m
    hA₀ hmA₀ hbaseEnergy (by simpa [V] using hbaseCross)
    (by simpa [V] using hordered)


theorem pinnedGreenEnergy_ge_of_boundaryEnergyAggregateField
    (hL : 1 < L) (q : Site L → ℤ)
    (U : RotatorDualFace L → ℝ) (hUroot : U none = 0)
    (A₀ P : ℝ) (hA₀ : 0 ≤ A₀) (hP : 0 ≤ P)
    (hpair : (A₀ + P) / 2 ≤ |∑ x, U (some x) * (q x : ℝ)|)
    (henergy : (squareZero L).energy U ≤ 150 * (A₀ + P)) :
    (A₀ + P) / 600 ≤ pinnedGreenEnergy hL q := by
  have harea : 0 ≤ A₀ + P := add_nonneg hA₀ hP
  have hprofile := pinned_greenEnergy_ge_of_profile hL q U hUroot
    ((A₀ + P) / 2) 300 (by positivity) (by norm_num)
    hpair (by nlinarith [henergy])
  dsimp [pinnedGreenEnergy]
  nlinarith

/-- Terminal isolation, base pairing, and the localized energy hypotheses
assemble into the finite-volume pinned Green-energy estimate. -/
theorem pinnedGreenEnergy_ge_of_terminalAggregateField
    (hL : 1 < L) (Miso Msel α : ℝ)
    (hMiso : 1 < Miso) (hα : 1 ≤ α) (hMsel : 1 ≤ Msel)
    (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    {N : Finset (ChargeDensity L)}
    (hgeom : AppendixDChargeGeometry Miso α N)
    {ρ : ChargeDensity L} (hρ : ρ ∈ N)
    (n : ℕ) (C : ℕ → Finset (Finset (Site L)))
    (hC : ∀ j ∈ Finset.Icc 1 n,
      IsMinimumSquareCover .free L j ρ (C j))
    (A₀ P m : ℝ) (hA₀ : 0 ≤ A₀) (hP : 0 ≤ P)
    (hm : 0 ≤ m) (hmA₀ : m ≤ A₀)
    (hPexact : P = ∑ j ∈ Finset.Icc 1 n,
      ((pinnedPPrime Msel α j ρ (C j)).card : ℝ))
    (base : RotatorDualFace L → ℝ)
    (hbaseRoot : base none = 0)
    (hbasePair : A₀ / 2 ≤ ∑ x, base (some x) * (ρ x : ℝ))
    (hbaseBoundary : ∀ x : Site L, siteBoundaryDepth x = 1 →
      base (some x) = 0)
    (hbaseGrad : ∀ e, |(squareZero L).grad base e| ≤ 1)
    (hbaseSupport :
      ((boundaryEnergyGradientSupport (squareZero L) base).card : ℝ) ≤ 4 * m)
    (hscaleGrad : ∀ j ∈ Finset.Icc 1 n, ∀ e,
      |(squareZero L).grad
        (boundaryEnergyScaleField ρ
          (pinnedPPrime Msel α j ρ (C j)) ((2 : ℝ) ^ j)) e| ≤
            1 / (2 : ℝ) ^ j)
    (hscaleSupport : ∀ j ∈ Finset.Icc 1 n,
      ((boundaryEnergyGradientSupport (squareZero L)
        (boundaryEnergyScaleField ρ
          (pinnedPPrime Msel α j ρ (C j)) ((2 : ℝ) ^ j))).card : ℝ) ≤
        50 * ((pinnedPPrime Msel α j ρ (C j)).card : ℝ) *
          ((2 : ℝ) ^ j) ^ 2) :
    (A₀ + P) / 600 ≤ pinnedGreenEnergy hL ρ := by
  have hprofile := boundaryEnergyAggregateField_pairing_and_boundary
    Miso Msel α hMiso hα hMsel hmargin hgeom hρ n C hC A₀ base
    hbaseRoot hbasePair hbaseBoundary
  let U := boundaryEnergyAggregateField ρ Msel α n C base
  have henergy : (squareZero L).energy U ≤ 150 * (A₀ + P) := by
    simpa [U] using boundaryEnergy_aggregateField_energy_le_area_of_localization
      ρ Msel α n C base A₀ P m hA₀ hm hmA₀ (by simp [hPexact])
      hbaseGrad hbaseSupport hscaleGrad hscaleSupport
  have hpair : (A₀ + P) / 2 ≤ |∑ x, U (some x) * (ρ x : ℝ)| := by
    have hscale :
        A₀ / 2 + ∑ j ∈ Finset.Icc 1 n,
          ((pinnedPPrime Msel α j ρ (C j)).card : ℝ) ≤
            ∑ x, U (some x) * (ρ x : ℝ) := by
      simpa [U] using hprofile.2.1
    rw [← hPexact] at hscale
    have hpositive : 0 ≤ (A₀ + P) / 2 := by positivity
    have hlower : (A₀ + P) / 2 ≤ ∑ x, U (some x) * (ρ x : ℝ) := by
      nlinarith [hscale]
    exact hlower.trans (le_abs_self _)
  exact pinnedGreenEnergy_ge_of_boundaryEnergyAggregateField hL ρ U hprofile.1
    A₀ P hA₀ hP hpair henergy

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
