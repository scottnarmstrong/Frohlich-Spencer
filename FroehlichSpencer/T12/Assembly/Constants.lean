/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Resonance
public import FroehlichSpencer.Surface.FiniteGreen
public import FroehlichSpencer.Multiscale.Basic
import FroehlichSpencer.Infra.Green.EventRegularity
import FroehlichSpencer.Infra.Lattice.Decay

/-!
# Scalar and measure-theoretic constants for the assembly
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.T12.Assembly

open Multiscale


theorem siteDist_zero_left (ν : ℕ) (x : Site ν) : siteDist ν 0 x = latticeLength ν x := by
  unfold siteDist latticeLength
  simp


theorem measurableSet_forall_norm_finiteGreen_le (ν : ℕ) (Λ : Finset (Site ν)) (E c : ℝ)
    (a b : {x // x ∈ Λ}) :
    MeasurableSet {v : Configuration ν | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
      ‖finiteGreen ν Λ v E ε hε a b‖ ≤ c} := by
  classical
  have hH := hamiltonian_isHermitian ν Λ 0
  have hA : (-dirichletLaplacian ν Λ).IsHermitian := by
    have := hH
    simpa [hamiltonian] using this
  have h := Infra.measurableSet_setOf_forall_norm_inv_le_comp hA Subtype.val E a b c
  convert h using 1
  ext v
  exact Iff.rfl


theorem exists_pow_mul_exp_le (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ^ k * Real.exp (-(r * t)) ≤ C := by
  refine ⟨((k : ℝ) / r) ^ k * Real.exp (-(k : ℝ)), by positivity, fun t ht => ?_⟩
  have := Infra.Lattice.pow_mul_exp_neg_le_const (a := k) hr ht
  rwa [neg_mul] at this


theorem exists_rpow_mul_exp_le_aux (a : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → t ^ a * Real.exp (-(r * t)) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_pow_mul_exp_le ⌈a⌉₊ hr
  refine ⟨C, hC0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith only [ht]
  calc t ^ a * Real.exp (-(r * t)) ≤ t ^ (⌈a⌉₊ : ℝ) * Real.exp (-(r * t)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le ht (Nat.le_ceil a)) (Real.exp_pos _).le
    _ = t ^ ⌈a⌉₊ * Real.exp (-(r * t)) := by rw [Real.rpow_natCast]
    _ ≤ C := hC t ht0


theorem exists_rpow_mul_exp_le (a : ℝ) {m : ℝ} (hm : 0 < m) :
    ∃ Mfin : ℝ, 0 < Mfin ∧ ∀ t : ℝ, 1 ≤ t → t ^ a * Real.exp (-(m * t / 8)) ≤ Mfin := by
  obtain ⟨C, hC0, hC⟩ := exists_rpow_mul_exp_le_aux a (r := m / 8) (by positivity)
  refine ⟨C + 1, by linarith only [hC0], fun t ht => ?_⟩
  have := hC t ht
  have e : -(m / 8 * t) = -(m * t / 8) := by ring
  rw [e] at this
  linarith only [this]


theorem resonance_absorb (ν : ℕ) {p m c Mfin : ℝ} (hc : 0 ≤ c)
    (hM : ∀ t : ℝ, 1 ≤ t → t ^ (p + ν) * Real.exp (-(m * t / 8)) ≤ Mfin)
    (hcM : Real.sqrt 2 * 10 ^ ν * c * Mfin ≤ 1) {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt (2 * Real.exp (-(m * N / 4))) * c * (10 * N) ^ ν ≤ N ^ (-p) := by
  have hN0 : 0 < N := by linarith only [hN]
  have hsq : Real.sqrt (2 * Real.exp (-(m * N / 4))) = Real.sqrt 2 * Real.exp (-(m * N / 8)) := by
    have : Real.exp (-(m * N / 4)) = Real.exp (-(m * N / 8)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (Real.exp_pos _).le]
  have hNp : 0 < N ^ p := Real.rpow_pos_of_pos hN0 p
  have hK : 0 ≤ Real.sqrt 2 * 10 ^ ν * c := by positivity
  have hMN := hM N hN
  have hmul : N ^ (p + ν) = N ^ p * N ^ ν := by
    rw [Real.rpow_add hN0, Real.rpow_natCast]
  rw [Real.rpow_neg hN0.le, ← one_div, le_div_iff₀ hNp, hsq]
  calc Real.sqrt 2 * Real.exp (-(m * N / 8)) * c * (10 * N) ^ ν * N ^ p
      = (Real.sqrt 2 * 10 ^ ν * c) * (N ^ (p + ν) * Real.exp (-(m * N / 8))) := by
        rw [hmul, mul_pow]; ring
    _ ≤ (Real.sqrt 2 * 10 ^ ν * c) * Mfin := mul_le_mul_of_nonneg_left hMN hK
    _ ≤ 1 := hcM


theorem exists_rate_path (ν : ℕ) : ∃ Mpath : ℝ, 0 ≤ Mpath ∧ ∀ M : ℝ, Mpath ≤ M →
    ∀ l : ℝ, 16 ≤ l → 4 * ν * (5 * l) ^ ν * Real.exp (-M * (l / 8 - 1)) ≤ 1 := by
  obtain ⟨C, hC0, hC⟩ := exists_pow_mul_exp_le ν (r := 1 / 8) (by norm_num)
  set D : ℝ := 4 * ν * 5 ^ ν * Real.exp 1 * C with hD
  have hD0 : 0 ≤ D := by positivity
  have hlog : 0 ≤ Real.log (D + 1) := Real.log_nonneg (by linarith only [hD0])
  refine ⟨1 + Real.log (D + 1), by linarith only [hlog], fun M hM l hl => ?_⟩
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hs : 1 ≤ l / 8 - 1 := by linarith only [hl]
  have h1 : Real.exp (-M * (l / 8 - 1)) ≤ Real.exp (-1 * (l / 8 - 1)) *
      Real.exp (-(Real.log (D + 1))) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : 0 ≤ (M - 1 - Real.log (D + 1)) * (l / 8 - 1) :=
      mul_nonneg (by linarith only [hM]) (by linarith only [hs])
    have h2 : 0 ≤ (Real.log (D + 1)) * ((l / 8 - 1) - 1) :=
      mul_nonneg hlog (by linarith only [hs])
    nlinarith only [this, h2]
  have h3 : Real.exp (-(Real.log (D + 1))) = (D + 1)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by linarith only [hD0])]
  have h4 : l ^ ν * Real.exp (-(1 / 8 * l)) ≤ C := hC l hl0
  have h5 : Real.exp (-1 * (l / 8 - 1)) = Real.exp 1 * Real.exp (-(1 / 8 * l)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < D + 1 := by linarith only [hD0]
  calc 4 * ν * (5 * l) ^ ν * Real.exp (-M * (l / 8 - 1))
      ≤ 4 * ν * (5 * l) ^ ν * (Real.exp (-1 * (l / 8 - 1)) * (D + 1)⁻¹) := by
        rw [← h3]; gcongr
    _ = (4 * ν * 5 ^ ν * Real.exp 1) * (l ^ ν * Real.exp (-(1 / 8 * l))) * (D + 1)⁻¹ := by
        rw [h5, mul_pow]; ring
    _ ≤ (4 * ν * 5 ^ ν * Real.exp 1) * C * (D + 1)⁻¹ := by gcongr
    _ = D * (D + 1)⁻¹ := by rw [hD]
    _ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hpos]; linarith only []


theorem exists_rate_local (ν : ℕ) {m : ℝ} (hm : 0 < m) : ∃ Mloc : ℝ, 0 ≤ Mloc ∧
    ∀ M : ℝ, Mloc ≤ M → ∀ N : ℝ, 1 ≤ N →
      1 + 4 * ν * (10 * N) ^ ν * Real.exp (-(3 * M * N / 4)) ≤ Real.exp (m * N / 4) := by
  obtain ⟨C, hC0, hC⟩ := exists_pow_mul_exp_le ν (r := 1 / 8) (by norm_num)
  set D : ℝ := 16 * ν * 10 ^ ν * C with hD
  have hD0 : 0 ≤ D := by positivity
  set x0 : ℝ := Real.log (D / m + 1) with hx0
  have hDm : 0 ≤ D / m := by positivity
  have hx00 : 0 ≤ x0 := Real.log_nonneg (by linarith only [hDm])
  refine ⟨1 + 2 * x0, by linarith only [hx00], fun M hM N hN => ?_⟩
  have hN0 : 0 ≤ N := by linarith only [hN]
  have h1 : Real.exp (-(3 * M * N / 4)) ≤
      Real.exp (-(1 / 8 * N)) * Real.exp (-x0) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h2 : 0 ≤ (3 * M / 4 - 1 / 8 - x0) * (N - 1) :=
      mul_nonneg (by linarith only [hx00, hM]) (by linarith only [hN])
    have h3 : 0 ≤ x0 * (N - 1) := mul_nonneg hx00 (by linarith only [hN])
    nlinarith only [hx00, hM, h2]
  have h3 : Real.exp (-x0) = (D / m + 1)⁻¹ := by
    rw [hx0, Real.exp_neg, Real.exp_log (by linarith only [hDm])]
  have h4 : N ^ ν * Real.exp (-(1 / 8 * N)) ≤ C := hC N hN0
  have hpos : 0 < D / m + 1 := by linarith only [hDm]
  have key : 4 * ν * (10 * N) ^ ν * Real.exp (-(3 * M * N / 4)) ≤ m / 4 := by
    calc 4 * ν * (10 * N) ^ ν * Real.exp (-(3 * M * N / 4))
        ≤ 4 * ν * (10 * N) ^ ν * (Real.exp (-(1 / 8 * N)) * (D / m + 1)⁻¹) := by
          rw [← h3]; gcongr
      _ = (4 * ν * 10 ^ ν) * (N ^ ν * Real.exp (-(1 / 8 * N))) * (D / m + 1)⁻¹ := by
          rw [mul_pow]; ring
      _ ≤ (4 * ν * 10 ^ ν) * C * (D / m + 1)⁻¹ := by gcongr
      _ = (D / 4) * (D / m + 1)⁻¹ := by rw [hD]; ring
      _ ≤ m / 4 := by
          rw [← div_eq_mul_inv, div_le_iff₀ hpos]
          have : D / m * m = D := by field_simp
          nlinarith only [hm, this]
  have hexp := Real.add_one_le_exp (m * N / 4)
  have hmN : m / 4 ≤ m * N / 4 := by nlinarith only [hm, hN]
  linarith only [key, hexp, hmN]


theorem two_mul_exp_le_exp_of_large {m M N r : ℝ} (hm : 0 ≤ m) (hM : 4 * m ≤ M)
    (hMN : 8 * Real.log 2 ≤ M * N) (hN : 0 ≤ N) (hr : N / 2 ≤ r) :
    2 * Real.exp (-M * r / 2) ≤ Real.exp (m * (N - r)) := by
  have h2 : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  have h2' : 2 * Real.exp (-M * r / 2) = Real.exp (Real.log 2 + -M * r / 2) := by
    rw [Real.exp_add, ← h2]
  rw [h2', Real.exp_le_exp]
  have hr0 : 0 ≤ r := by linarith only [hN, hr]
  have hM0 : 0 ≤ M := by linarith only [hm, hM]
  have a1 : 0 ≤ (M / 4 - m) * r := mul_nonneg (by linarith only [hM]) hr0
  have a2 : 0 ≤ M / 4 * (r - N / 2) := mul_nonneg (by linarith only [hM0]) (by linarith only [hr])
  have a3 : 0 ≤ m * N := mul_nonneg hm hN
  nlinarith only [hMN, a1, a2, a3]


theorem ofReal_one_sub_div_rpow_eq_zero {p N Nstar K : ℝ} (hp : 0 < p) (hN : 0 < N)
    (hNN : N ≤ Nstar) (hK : Nstar ^ p ≤ K) :
    ENNReal.ofReal (1 - K / Real.rpow N p) = 0 := by
  have h1 : N ^ p ≤ K := (Real.rpow_le_rpow hN.le hNN hp.le).trans hK
  have hpos : 0 < Real.rpow N p := Real.rpow_pos_of_pos hN p
  rw [ENNReal.ofReal_eq_zero]
  have : 1 ≤ K / Real.rpow N p := by
    rw [le_div_iff₀ hpos, one_mul]
    exact h1
  linarith only [this]


theorem ofReal_one_sub_le_of_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S) {a : ℝ} (ha : 0 ≤ a)
    (h : μ Sᶜ ≤ ENNReal.ofReal a) : ENNReal.ofReal (1 - a) ≤ μ S := by
  rw [prob_compl_eq_one_sub hS, tsub_le_iff_right] at h
  rw [ENNReal.ofReal_sub 1 ha, ENNReal.ofReal_one, tsub_le_iff_right, add_comm]
  exact h


theorem exists_gaussian_coeff_le (ν : ℕ) {γ : ℝ} (hγ : 0 < γ) {η : ℝ} (hη : 0 < η) :
    ∃ E₁ : ℝ, ∀ E : ℝ, E₁ ≤ |E - 2 * ν| →
      Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
        (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1}) ≤ η := by
  have hs : 0 < Real.sqrt (2 * Real.pi * γ) := Real.sqrt_pos.mpr (by positivity)
  have hδ : 0 < η ^ 2 * Real.sqrt (2 * Real.pi * γ) := by positivity
  have hT := T12.tendsto_gaussianLaw_window ν hγ
  have hev := hT.eventually (gt_mem_nhds hδ)
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup, Filter.eventually_atBot,
    Filter.eventually_atTop] at hev
  obtain ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ := hev
  have hν : (0 : ℝ) ≤ 2 * ν := by positivity
  refine ⟨|a| + |b| + 2 * ν, fun E hE => ?_⟩
  have hlt : (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1} <
      η ^ 2 * Real.sqrt (2 * Real.pi * γ) := by
    rcases le_abs'.mp hE with h | h
    · exact hb E (by linarith only [h, neg_abs_le b, abs_nonneg a])
    · exact ha E (by linarith only [h, le_abs_self a, abs_nonneg b])
  calc Real.sqrt (1 / Real.sqrt (2 * Real.pi * γ) *
        (gaussianLaw γ hγ).real {t | |t - (E - 2 * ν)| ≤ 2 * ν + 1})
      ≤ Real.sqrt (η ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [one_div, inv_mul_le_iff₀ hs]
        linarith only [hlt]
    _ = η := Real.sqrt_sq hη.le

end FroehlichSpencer.T12.Assembly

end
