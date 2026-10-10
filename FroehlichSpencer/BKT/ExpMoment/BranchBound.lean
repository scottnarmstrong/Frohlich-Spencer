/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.ExpMoment.Claim31
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# KP §3, per-branch bound (3.5)

Each ensemble factor is at least `7/8`, the
normalized branch measure is even, and `e^S ≥ 1 + S` with `S` odd replaces Jensen.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

open MeasureTheory

variable {V : Type*} [Fintype V] {ι : Type*}

private lemma factor_le (z t : ℝ) (hz : |z| < 1 / 8) : 1 + z * Real.cos t ≤ 9 / 8 := by
  have h1 : |z * Real.cos t| ≤ |z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one t)
  have := (abs_le.mp h1).2
  linarith

private lemma integrable_of_cont_bdd (μ : Measure (V → ℝ)) [IsProbabilityMeasure μ]
    {f : (V → ℝ) → ℝ} (hf : Continuous f) (C : ℝ) (h : ∀ φ, ‖f φ‖ ≤ C) : Integrable f μ :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable (Filter.Eventually.of_forall fun φ => by simpa using h φ)

private lemma continuous_lin (a : V → ℝ) (b : ℝ) :
    Continuous (fun φ : V → ℝ => ∑ j, φ j * a j + b) := by fun_prop

private lemma continuous_prod_cos (s : Finset ι) (a : ι → V → ℝ) (b z : ι → ℝ) :
    Continuous (fun φ : V → ℝ => ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j + b i))) :=
  continuous_finsetProd _ fun i _ => by
    have := continuous_lin (a i) (b i)
    fun_prop

private lemma prod_cos_bounds (s : Finset ι) (a : ι → V → ℝ) (b z : ι → ℝ)
    (hz : ∀ i ∈ s, |z i| < 1 / 8) (φ : V → ℝ) :
    0 ≤ ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j + b i)) ∧
    ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j + b i)) ≤ (9 / 8) ^ s.card := by
  refine ⟨Finset.prod_nonneg fun i hi => ?_, ?_⟩
  · have := claim31_denominator_ge (∑ j, φ j * a i j + b i) (z i) (hz i hi); linarith
  · calc _ ≤ ∏ _i ∈ s, (9 / 8 : ℝ) := Finset.prod_le_prod₀
          (fun i hi => by
            have := claim31_denominator_ge (∑ j, φ j * a i j + b i) (z i) (hz i hi); linarith)
          (fun i hi => factor_le _ _ (hz i hi))
      _ = _ := Finset.prod_const _

private lemma integral_neg_inv (μ : Measure (V → ℝ)) (hμ : μ.map (fun φ => -φ) = μ)
    {g : (V → ℝ) → ℝ} (hg : Continuous g) : ∫ φ, g (-φ) ∂μ = ∫ φ, g φ ∂μ := by
  have h := integral_map (μ := μ) (φ := fun φ : V → ℝ => -φ) (f := g)
    (measurable_neg.aemeasurable) (by rw [hμ]; exact hg.aestronglyMeasurable)
  rw [hμ] at h
  exact h.symm

/-- Every ensemble factor is at least `7/8`, so the product integral is at least `(7/8)^|s|`. -/
theorem integral_prod_one_add_cos_ge (μ : Measure (V → ℝ)) [IsProbabilityMeasure μ]
    (s : Finset ι) (a : ι → V → ℝ) (b z : ι → ℝ) (hz : ∀ i ∈ s, |z i| < 1 / 8) :
    (7 / 8 : ℝ) ^ s.card ≤ ∫ φ, ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j + b i)) ∂μ := by
  have hint : Integrable
      (fun φ : V → ℝ => ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j + b i))) μ :=
    integrable_of_cont_bdd μ (continuous_prod_cos s a b z) ((9 / 8) ^ s.card) fun φ => by
      have := prod_cos_bounds s a b z hz φ
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  have := integral_mono (integrable_const ((7 / 8 : ℝ) ^ s.card)) hint (f := fun _ => (7 / 8 : ℝ) ^ s.card)
    (fun φ => by
      calc (7 / 8 : ℝ) ^ s.card = ∏ _i ∈ s, (7 / 8 : ℝ) := (Finset.prod_const _).symm
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by norm_num) fun i hi =>
          (claim31_denominator_ge (∑ j, φ j * a i j + b i) (z i) (hz i hi)).le)
  simpa using this

/-- KP §3 (3.5) per branch: Claim 3.1 in product form, integrated against an even probability
measure. -/
theorem integral_prod_cos_shift_ge (μ : Measure (V → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ.map (fun φ => -φ) = μ) (s : Finset ι) (a : ι → V → ℝ) (y z : ι → ℝ)
    (hz : ∀ i ∈ s, |z i| < 1 / 8) :
    Real.exp (-∑ i ∈ s, 2 * |z i| * y i ^ 2) *
        ∫ φ, ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j)) ∂μ ≤
      ∫ φ, ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j + y i)) ∂μ := by
  classical
  set c : ℝ := -∑ i ∈ s, 2 * |z i| * y i ^ 2 with hc
  let P : (V → ℝ) → ℝ := fun φ => ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j))
  let S : (V → ℝ) → ℝ := fun φ => ∑ i ∈ s,
    -(z i * Real.sin (∑ j, φ j * a i j) * Real.sin (y i)) / (1 + z i * Real.cos (∑ j, φ j * a i j))
  let Q : (V → ℝ) → ℝ := fun φ => ∏ i ∈ s, (1 + z i * Real.cos (∑ j, φ j * a i j + y i))
  have hD : ∀ i ∈ s, ∀ φ : V → ℝ, 7 / 8 < 1 + z i * Real.cos (∑ j, φ j * a i j) :=
    fun i hi φ => claim31_denominator_ge _ _ (hz i hi)
  have hPc : Continuous P := by
    have := continuous_prod_cos s a (fun _ => 0) z
    simpa [P] using this
  have hQc : Continuous Q := continuous_prod_cos s a y z
  have hSc : Continuous S := by
    refine continuous_finsetSum _ fun i hi => ?_
    have hx : Continuous (fun φ : V → ℝ => ∑ j, φ j * a i j) := by fun_prop
    refine Continuous.div (by fun_prop) (by fun_prop) fun φ => ne_of_gt (by linarith [hD i hi φ])
  have hPb : ∀ φ, ‖P φ‖ ≤ (9 / 8) ^ s.card := fun φ => by
    have := prod_cos_bounds s a (fun _ => 0) z hz φ
    simp only [add_zero] at this
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  have hQb : ∀ φ, ‖Q φ‖ ≤ (9 / 8) ^ s.card := fun φ => by
    have := prod_cos_bounds s a y z hz φ
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  have hSb : ∀ φ, |S φ| ≤ ∑ i ∈ s, 8 / 7 * |z i| := fun φ => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hd := hD i hi φ
    rw [abs_div, abs_neg, abs_of_pos (by linarith : 0 < 1 + z i * Real.cos (∑ j, φ j * a i j)),
      div_le_iff₀ (by linarith)]
    rw [abs_mul, abs_mul]
    have h1 := Real.abs_sin_le_one (∑ j, φ j * a i j)
    have h2 := Real.abs_sin_le_one (y i)
    have h3 : |z i| * |Real.sin (∑ j, φ j * a i j)| * |Real.sin (y i)| ≤ |z i| := by
      calc _ ≤ |z i| * 1 * 1 := by gcongr
        _ = _ := by ring
    nlinarith [abs_nonneg (z i)]
  have hPi : Integrable P μ := integrable_of_cont_bdd μ hPc _ hPb
  have hQi : Integrable Q μ := integrable_of_cont_bdd μ hQc _ hQb
  have hSPc : Continuous (fun φ => S φ * P φ) := hSc.mul hPc
  have hSPi : Integrable (fun φ => S φ * P φ) μ :=
    integrable_of_cont_bdd μ hSPc ((∑ i ∈ s, 8 / 7 * |z i|) * (9 / 8) ^ s.card) fun φ => by
      rw [norm_mul]
      exact mul_le_mul (by simpa using hSb φ) (hPb φ) (norm_nonneg _)
        (le_trans (abs_nonneg _) (hSb φ))
  -- oddness
  have hodd : ∫ φ, S φ * P φ ∂μ = 0 := by
    have hneg : ∀ φ : V → ℝ, S (-φ) * P (-φ) = -(S φ * P φ) := fun φ => by
      have hx : ∀ i, ∑ j, (-φ) j * a i j = -∑ j, φ j * a i j := fun i => by
        simp [Finset.sum_neg_distrib]
      have hS : S (-φ) = -S φ := by
        simp only [S]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hx, Real.sin_neg, Real.cos_neg]
        ring
      have hP : P (-φ) = P φ :=
        Finset.prod_congr rfl fun i _ => by rw [hx i, Real.cos_neg]
      rw [hS, hP]; ring
    have h := integral_neg_inv μ hμ hSPc
    simp only [hneg, integral_neg] at h
    linarith
  -- pointwise
  have hpt : ∀ φ, Real.exp c * (P φ + S φ * P φ) ≤ Q φ := fun φ => by
    have h := claim31_prod s (fun i => ∑ j, φ j * a i j) y z hz
    have hsum : ∑ i ∈ s, (-(z i * Real.sin (∑ j, φ j * a i j) * Real.sin (y i)) /
        (1 + z i * Real.cos (∑ j, φ j * a i j)) - 2 * |z i| * y i ^ 2) = S φ + c := by
      simp only [Finset.sum_sub_distrib, S, hc]; ring
    rw [hsum, Real.exp_add] at h
    have hP0 : 0 ≤ P φ := by
      simpa using (prod_cos_bounds s a (fun _ => 0) z hz φ).1
    have he := Real.add_one_le_exp (S φ)
    have hec := (Real.exp_pos c).le
    calc Real.exp c * (P φ + S φ * P φ) = Real.exp c * ((S φ + 1) * P φ) := by ring
      _ ≤ Real.exp c * (Real.exp (S φ) * P φ) := by gcongr
      _ = Real.exp (S φ) * Real.exp c * P φ := by ring
      _ ≤ Q φ := h
  have hmono := integral_mono ((hPi.add hSPi).const_mul (Real.exp c)) hQi hpt
  rw [integral_const_mul, show (P + fun φ => S φ * P φ) = fun φ => P φ + S φ * P φ from rfl,
    integral_add hPi hSPi, hodd, add_zero] at hmono
  exact hmono

end FroehlichSpencer.BKT

end
