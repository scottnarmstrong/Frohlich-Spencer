/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.Closure
public import FroehlichSpencer.BKT.Rotator.Ginibre.System
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Ginibre's inequalities for products of bond weights

A finite family of bonds with integer frequencies `d e` and bond weights `w e : ℝ → ℝ` (continuous,
positive, bounded) defines the Gibbs measure `Z⁻¹ ∏_e w_e(d_e·θ) ∏_x ν(dθ_x)` for a single-site
reference measure `ν`. When every bond pair `(w₁ e, w₂ e)` is a Ginibre pair and the single-site
Fourier coefficients of `ν, ν'` form an equivalence kernel:

* **Ginibre I:** `⟨cos(n·θ)⟩ ≥ 0` (pairs `(w e, w e)`, `ν' = ν`);
* **Ginibre II:** `⟨cos(n·θ)⟩ ⟨cos(m·θ)⟩ ≤ ⟨cos(n·θ) cos(m·θ)⟩`;
* **comparison:** `⟨cos(n·θ)⟩_{ν', w₂} ≤ ⟨cos(n·θ)⟩_{ν, w₁}`, which gives monotonicity in the
  couplings (`ν' = ν`) and the clock/rotator comparison (`ν` clock, `ν'` circle).

Expectations of functions of restricted angles transfer along injective site maps that preserve the
weight, which with the comparison gives domain monotonicity.
-/

@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Ginibre

/-- A bond weight: continuous, positive and bounded. -/
structure IsBondWeight (w : ℝ → ℝ) : Prop where
  continuous : Continuous w
  pos : ∀ x, 0 < w x
  bdd : ∃ C, ∀ x, w x ≤ C

theorem isBondWeight_one : IsBondWeight fun _ => (1 : ℝ) :=
  ⟨continuous_const, fun _ => one_pos, ⟨1, fun _ => le_rfl⟩⟩

theorem isBondWeight_expCos (J : ℝ) : IsBondWeight (expCosWeight J) :=
  ⟨Real.continuous_exp.comp (continuous_const.mul Real.continuous_cos), fun _ => Real.exp_pos _,
    ⟨Real.exp |J|, fun x => Real.exp_le_exp.mpr <| (le_abs_self _).trans <| by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x)⟩⟩

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The product weight `∏_e w_e(d_e·θ)`. -/
def pairWeight (d : E → Frequency V) (w : E → ℝ → ℝ) (θ : V → ℝ) : ℝ :=
  ∏ e, w e (phase (d e) θ)

/-- The partition integral against the product reference measure. -/
def pairPartition (ν : Measure ℝ) (d : E → Frequency V) (w : E → ℝ → ℝ) : ℝ :=
  ∫ θ, pairWeight d w θ ∂siteProduct ν V

/-- The normalized Gibbs measure. -/
def pairGibbs (ν : Measure ℝ) (d : E → Frequency V) (w : E → ℝ → ℝ) : Measure (V → ℝ) :=
  (siteProduct ν V).withDensity fun θ => ENNReal.ofReal (pairWeight d w θ / pairPartition ν d w)

variable {d : E → Frequency V} {w : E → ℝ → ℝ}

theorem continuous_pairWeight (hw : ∀ e, IsBondWeight (w e)) : Continuous (pairWeight d w) := by
  unfold pairWeight
  exact continuous_finsetProd _ fun e _ => (hw e).continuous.comp (continuous_phase (d e))

theorem pairWeight_pos (hw : ∀ e, IsBondWeight (w e)) (θ : V → ℝ) : 0 < pairWeight d w θ :=
  Finset.prod_pos fun e _ => (hw e).pos _

theorem exists_pairWeight_le (hw : ∀ e, IsBondWeight (w e)) :
    ∃ C, ∀ θ, pairWeight d w θ ≤ C := by
  choose C hC using fun e => (hw e).bdd
  refine ⟨∏ e, C e, fun θ => Finset.prod_le_prod₀ (fun e _ => ((hw e).pos _).le)
    fun e _ => hC e _⟩

theorem integrable_mul_pairWeight {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hw : ∀ e, IsBondWeight (w e)) {f : (V → ℝ) → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ θ, |f θ| ≤ C) :
    Integrable (fun θ => f θ * pairWeight d w θ) (siteProduct ν V) := by
  obtain ⟨D, hD⟩ := exists_pairWeight_le (d := d) hw
  refine Integrable.of_bound (hf.mul (continuous_pairWeight hw)).aestronglyMeasurable (C * D)
    (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pairWeight_pos hw θ)]
  exact mul_le_mul (hC θ) (hD θ) (pairWeight_pos hw θ).le ((abs_nonneg _).trans (hC θ))

theorem integrable_pairWeight {ν : Measure ℝ} [IsFiniteMeasure ν] (hw : ∀ e, IsBondWeight (w e)) :
    Integrable (pairWeight d w) (siteProduct ν V) := by
  simpa using integrable_mul_pairWeight (ν := ν) (d := d) hw (f := fun _ => 1) continuous_const
    (C := 1) (fun _ => by simp)

theorem integrable_cos_mul_pairWeight {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hw : ∀ e, IsBondWeight (w e)) (n : Frequency V) :
    Integrable (fun θ => Real.cos (phase n θ) * pairWeight d w θ) (siteProduct ν V) :=
  integrable_mul_pairWeight hw (Real.continuous_cos.comp (continuous_phase n))
    fun _ => Real.abs_cos_le_one _

theorem pairPartition_pos {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    (hw : ∀ e, IsBondWeight (w e)) : 0 < pairPartition ν d w := by
  rw [pairPartition, integral_pos_iff_support_of_nonneg (fun θ => (pairWeight_pos hw θ).le)
    (integrable_pairWeight hw)]
  have hsupp : Function.support (pairWeight d w) = Set.univ := by
    ext θ
    simp [(pairWeight_pos hw θ).ne']
  rw [hsupp]
  exact pos_iff_ne_zero.mpr (siteProduct_univ_ne_zero hν V)

/-- Expectations are ratios of raw integrals. -/
theorem integral_pairGibbs {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    (hw : ∀ e, IsBondWeight (w e)) (f : (V → ℝ) → ℝ) :
    ∫ θ, f θ ∂pairGibbs ν d w =
      (∫ θ, f θ * pairWeight d w θ ∂siteProduct ν V) / pairPartition ν d w := by
  have hZ := pairPartition_pos (d := d) hν hw
  have hden : Measurable fun θ : V → ℝ => ENNReal.ofReal (pairWeight d w θ / pairPartition ν d w) :=
    ((continuous_pairWeight hw).measurable.div_const _).ennreal_ofReal
  rw [pairGibbs, integral_withDensity_eq_integral_toReal_smul hden
    (ae_of_all _ fun θ => ENNReal.ofReal_lt_top), ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (div_nonneg (pairWeight_pos hw θ).le hZ.le), smul_eq_mul]
  ring

theorem isProbabilityMeasure_pairGibbs {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    (hw : ∀ e, IsBondWeight (w e)) : IsProbabilityMeasure (pairGibbs ν d w) := by
  constructor
  have hZ := pairPartition_pos (d := d) hν hw
  rw [pairGibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_pairWeight hw).div_const _)
      (ae_of_all _ fun θ => div_nonneg (pairWeight_pos hw θ).le hZ.le),
    integral_div, ← pairPartition, div_self hZ.ne', ENNReal.ofReal_one]

theorem integral_cos_pairGibbs_le_one {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    (hw : ∀ e, IsBondWeight (w e)) (n : Frequency V) :
    ∫ θ, Real.cos (phase n θ) ∂pairGibbs ν d w ≤ 1 := by
  rw [integral_pairGibbs hν hw, div_le_one (pairPartition_pos hν hw), pairPartition]
  exact integral_mono (integrable_cos_mul_pairWeight hw n) (integrable_pairWeight hw)
    fun θ => mul_le_of_le_one_left (pairWeight_pos hw θ).le (Real.cos_le_one _)

/-! ### The duplicated system -/

/-- The master inequality: a cone element integrates nonnegatively against the duplicated product
weight when every bond pair is a Ginibre pair. -/
theorem integral_mul_pairWeight_nonneg {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    {lam lam' : ℤ → ℝ} (hν : HasRealFourier ν lam) (hν' : HasRealFourier ν' lam')
    (hK : HasEquivKernel lam lam') {w₁ w₂ : E → ℝ → ℝ}
    (hpair : ∀ e, IsGinibrePair V (w₁ e) (w₂ e)) {P : DupTrigAlgebra V} (hP : IsGinibre P)
    {F : (V → ℝ) × (V → ℝ) → ℝ} (hF : ∀ z, dupEval V P z = (F z : ℂ)) :
    0 ≤ ∫ z, F z * (pairWeight d w₁ z.1 * pairWeight d w₂ z.2)
      ∂(siteProduct ν V).prod (siteProduct ν' V) := by
  refine IsGinibreLimit.integral_nonneg hν hν' hK ?_
  refine ((IsGinibreLimit.of_isGinibre hP hF).mul
    (IsGinibreLimit.finsetProd Finset.univ fun e _ => hpair e (d e))).congr fun z => ?_
  simp only [pairWeight, Finset.prod_mul_distrib]

omit [Fintype V] in
theorem integral_prod_diff {μ μ' : Measure (V → ℝ)} [SFinite μ] [SFinite μ']
    {f w w' : (V → ℝ) → ℝ} (hfw' : Integrable (fun θ => f θ * w' θ) μ)
    (hfw : Integrable (fun θ => f θ * w θ) μ') (hw : Integrable w μ') (hw' : Integrable w' μ) :
    ∫ z, (f z.1 - f z.2) * (w' z.1 * w z.2) ∂μ.prod μ' =
      (∫ θ, f θ * w' θ ∂μ) * (∫ θ, w θ ∂μ') - (∫ θ, w' θ ∂μ) * ∫ θ, f θ * w θ ∂μ' := by
  have h₁ : (fun z : (V → ℝ) × (V → ℝ) => (f z.1 - f z.2) * (w' z.1 * w z.2)) =
      fun z => (f z.1 * w' z.1) * w z.2 - w' z.1 * (f z.2 * w z.2) := by
    funext z
    ring
  rw [h₁, integral_sub (hfw'.mul_prod hw) (hw'.mul_prod hfw),
    integral_prod_mul (fun θ => f θ * w' θ) w, integral_prod_mul w' (fun θ => f θ * w θ)]

omit [Fintype V] in
theorem integral_prod_diff_mul_diff {μ : Measure (V → ℝ)} [SFinite μ] {f g w : (V → ℝ) → ℝ}
    (hfgw : Integrable (fun θ => f θ * g θ * w θ) μ) (hfw : Integrable (fun θ => f θ * w θ) μ)
    (hgw : Integrable (fun θ => g θ * w θ) μ) (hw : Integrable w μ) :
    ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) * (w z.1 * w z.2) ∂μ.prod μ =
      2 * ((∫ θ, f θ * g θ * w θ ∂μ) * (∫ θ, w θ ∂μ) -
        (∫ θ, f θ * w θ ∂μ) * ∫ θ, g θ * w θ ∂μ) := by
  have h₁ : (fun z : (V → ℝ) × (V → ℝ) => (f z.1 - f z.2) * (g z.1 - g z.2) * (w z.1 * w z.2)) =
      fun z => ((f z.1 * g z.1 * w z.1) * w z.2 + w z.1 * (f z.2 * g z.2 * w z.2)) -
        ((f z.1 * w z.1) * (g z.2 * w z.2) + (g z.1 * w z.1) * (f z.2 * w z.2)) := by
    funext z
    ring
  have i₁ := hfgw.mul_prod hw
  have i₂ := hw.mul_prod hfgw
  have i₃ := hfw.mul_prod hgw
  have i₄ := hgw.mul_prod hfw
  have i₁₂ : Integrable (fun z : (V → ℝ) × (V → ℝ) =>
      (f z.1 * g z.1 * w z.1) * w z.2 + w z.1 * (f z.2 * g z.2 * w z.2)) (μ.prod μ) := i₁.add i₂
  have i₃₄ : Integrable (fun z : (V → ℝ) × (V → ℝ) =>
      (f z.1 * w z.1) * (g z.2 * w z.2) + (g z.1 * w z.1) * (f z.2 * w z.2)) (μ.prod μ) :=
    i₃.add i₄
  rw [h₁, integral_sub i₁₂ i₃₄, integral_add i₁ i₂, integral_add i₃ i₄,
    integral_prod_mul (fun θ => f θ * g θ * w θ) w,
    integral_prod_mul w (fun θ => f θ * g θ * w θ),
    integral_prod_mul (fun θ => f θ * w θ) (fun θ => g θ * w θ),
    integral_prod_mul (fun θ => g θ * w θ) (fun θ => f θ * w θ)]
  ring

/-! ### Ginibre's inequalities -/

section Inequalities

variable {ν : Measure ℝ} [IsFiniteMeasure ν] {lam : ℤ → ℝ}

/-- **Ginibre I.** -/
theorem integral_cos_pairGibbs_nonneg (hν : HasRealFourier ν lam) (hν0 : ν Set.univ ≠ 0)
    (hK : HasEquivKernel lam lam) (hw : ∀ e, IsBondWeight (w e))
    (hpair : ∀ e, IsGinibrePair V (w e) (w e)) (n : Frequency V) :
    0 ≤ ∫ θ, Real.cos (phase n θ) ∂pairGibbs ν d w := by
  rw [integral_pairGibbs hν0 hw]
  have hZ := pairPartition_pos (d := d) hν0 hw
  refine div_nonneg ?_ hZ.le
  have hP : IsGinibre ((1 / 2 : ℝ) • (cosPair n 1 + cosPair n (-1))) :=
    ((isGinibre_cosPair n (by norm_num)).add (isGinibre_cosPair n (by norm_num))).smul
      (by norm_num)
  have h := integral_mul_pairWeight_nonneg hν hν hK hpair hP (d := d)
    (F := fun z => Real.cos (phase n z.1)) (fun z => by
      simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, dupEval_cosPair,
        Complex.real_smul]
      push_cast
      ring)
  have hfac : (fun z : (V → ℝ) × (V → ℝ) =>
      Real.cos (phase n z.1) * (pairWeight d w z.1 * pairWeight d w z.2)) =
      fun z => (Real.cos (phase n z.1) * pairWeight d w z.1) * pairWeight d w z.2 := by
    funext z
    ring
  rw [hfac, integral_prod_mul (fun θ => Real.cos (phase n θ) * pairWeight d w θ)
    (pairWeight d w), ← pairPartition] at h
  exact nonneg_of_mul_nonneg_left h hZ

/-- **Ginibre II.** -/
theorem integral_cos_mul_cos_pairGibbs_ge (hν : HasRealFourier ν lam) (hν0 : ν Set.univ ≠ 0)
    (hK : HasEquivKernel lam lam) (hw : ∀ e, IsBondWeight (w e))
    (hpair : ∀ e, IsGinibrePair V (w e) (w e)) (n m : Frequency V) :
    (∫ θ, Real.cos (phase n θ) ∂pairGibbs ν d w) * (∫ θ, Real.cos (phase m θ) ∂pairGibbs ν d w) ≤
      ∫ θ, Real.cos (phase n θ) * Real.cos (phase m θ) ∂pairGibbs ν d w := by
  simp only [integral_pairGibbs hν0 hw]
  have hZ := pairPartition_pos (d := d) hν0 hw
  have hP : IsGinibre ((1 / 2 : ℝ) • (cosPair n (-1) * cosPair m (-1))) :=
    ((isGinibre_cosPair n (by norm_num)).mul (isGinibre_cosPair m (by norm_num))).smul
      (by norm_num)
  have h := integral_mul_pairWeight_nonneg hν hν hK hpair hP (d := d)
    (F := fun z => (1 / 2 : ℝ) * ((Real.cos (phase n z.1) - Real.cos (phase n z.2)) *
      (Real.cos (phase m z.1) - Real.cos (phase m z.2)))) (fun z => by
        simp only [map_smul, map_mul, Pi.smul_apply, Pi.mul_apply, dupEval_cosPair,
          Complex.real_smul]
        push_cast
        ring)
  have hnm : Integrable
      (fun θ => Real.cos (phase n θ) * Real.cos (phase m θ) * pairWeight d w θ)
      (siteProduct ν V) :=
    integrable_mul_pairWeight hw
      ((Real.continuous_cos.comp (continuous_phase n)).mul
        (Real.continuous_cos.comp (continuous_phase m))) (C := 1)
      (fun θ => by
        rw [abs_mul]
        nlinarith [Real.abs_cos_le_one (phase n θ), Real.abs_cos_le_one (phase m θ),
          abs_nonneg (Real.cos (phase n θ)), abs_nonneg (Real.cos (phase m θ))])
  have hexp : (fun z : (V → ℝ) × (V → ℝ) =>
      (1 / 2 : ℝ) * ((Real.cos (phase n z.1) - Real.cos (phase n z.2)) *
        (Real.cos (phase m z.1) - Real.cos (phase m z.2))) *
          (pairWeight d w z.1 * pairWeight d w z.2)) =
      fun z => (1 / 2 : ℝ) * ((Real.cos (phase n z.1) - Real.cos (phase n z.2)) *
        (Real.cos (phase m z.1) - Real.cos (phase m z.2)) *
          (pairWeight d w z.1 * pairWeight d w z.2)) := by
    funext z
    ring
  rw [hexp, integral_const_mul, integral_prod_diff_mul_diff hnm
    (integrable_cos_mul_pairWeight hw n) (integrable_cos_mul_pairWeight hw m)
    (integrable_pairWeight hw), ← pairPartition] at h
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hZ hZ) hZ]
  nlinarith

end Inequalities

/-- **Comparison.** If every bond pair `(w₁ e, w₂ e)` is a Ginibre pair and the coefficients of
`ν, ν'` form an equivalence kernel, then `⟨cos(n·θ)⟩_{ν', w₂} ≤ ⟨cos(n·θ)⟩_{ν, w₁}`. -/
theorem integral_cos_pairGibbs_le {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    {lam lam' : ℤ → ℝ} (hν : HasRealFourier ν lam) (hν' : HasRealFourier ν' lam')
    (hν0 : ν Set.univ ≠ 0) (hν0' : ν' Set.univ ≠ 0) (hK : HasEquivKernel lam lam')
    {w₁ w₂ : E → ℝ → ℝ} (hw₁ : ∀ e, IsBondWeight (w₁ e)) (hw₂ : ∀ e, IsBondWeight (w₂ e))
    (hpair : ∀ e, IsGinibrePair V (w₁ e) (w₂ e)) (n : Frequency V) :
    ∫ θ, Real.cos (phase n θ) ∂pairGibbs ν' d w₂ ≤ ∫ θ, Real.cos (phase n θ) ∂pairGibbs ν d w₁ := by
  rw [integral_pairGibbs hν0' hw₂, integral_pairGibbs hν0 hw₁]
  have hZ₁ := pairPartition_pos (d := d) hν0 hw₁
  have hZ₂ := pairPartition_pos (d := d) hν0' hw₂
  have h := integral_mul_pairWeight_nonneg hν hν' hK hpair (isGinibre_cosPair n (σ := -1)
    (by norm_num)) (d := d) (F := fun z => Real.cos (phase n z.1) - Real.cos (phase n z.2))
    (fun z => by
      rw [dupEval_cosPair]
      push_cast
      ring)
  rw [integral_prod_diff (integrable_cos_mul_pairWeight hw₁ n)
    (integrable_cos_mul_pairWeight hw₂ n) (integrable_pairWeight hw₂)
    (integrable_pairWeight hw₁), ← pairPartition, ← pairPartition] at h
  rw [div_le_div_iff₀ hZ₂ hZ₁]
  linarith

/-! ### Transfer along site embeddings -/

/-- If the weight of a larger system is the weight of a smaller one on the restricted angles, the
expectations of functions of the restricted angles agree. -/
theorem integral_comp_pairGibbs {V' E' : Type*} [Fintype V'] [Fintype E'] {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν0 : ν Set.univ ≠ 0) (hw : ∀ e, IsBondWeight (w e))
    {d' : E' → Frequency V'} {w' : E' → ℝ → ℝ} (hw' : ∀ e, IsBondWeight (w' e)) {ι : V → V'}
    (hι : Function.Injective ι) (hW : ∀ θ' : V' → ℝ, pairWeight d' w' θ' = pairWeight d w (θ' ∘ ι))
    {f : (V → ℝ) → ℝ} (hf : Measurable f) :
    ∫ θ', f (θ' ∘ ι) ∂pairGibbs ν d' w' = ∫ θ, f θ ∂pairGibbs ν d w := by
  have hc : (0 : ℝ) < (ν Set.univ).toReal ^ (Fintype.card V' - Fintype.card V) :=
    pow_pos (ENNReal.toReal_pos hν0 (measure_ne_top ν _)) _
  rw [integral_pairGibbs hν0 hw', integral_pairGibbs hν0 hw, pairPartition, pairPartition]
  simp_rw [hW]
  rw [integral_comp_siteProduct hι (f := fun θ => f θ * pairWeight d w θ)
      (hf.mul (continuous_pairWeight hw).measurable).aestronglyMeasurable,
    integral_comp_siteProduct hι (f := pairWeight d w)
      (continuous_pairWeight hw).aestronglyMeasurable,
    mul_div_mul_left _ _ hc.ne']

end FroehlichSpencer.BKT.Ginibre

end
