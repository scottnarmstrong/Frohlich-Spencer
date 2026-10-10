/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Renormalization.ChargeLayer
public import FroehlichSpencer.BKT.Generic.Renormalization.Activity
public import FroehlichSpencer.BKT.Generic.Renormalization.Ensemble

/-!
# The T1.6-NG assembly on the rooted edge law (generic core)

`edgeLaw_renormalization_of_chargeLayer`: for a charge layer whose translated densities are the
neutral parts of its ensembles, each with at most one non-neutral density (the rooted, KP-type
case), the spin waves `a_ϱ = envelopeWave …`  give, for every real shift `σ`,

`∫ ∏_j λ_j(φ_j + σ_j) d edgeLaw = ∑_i c_i ∫ ∏_{ϱ ∈ ℛ_i} [1 + z_i(ϱ) F_{i,ϱ}(φ, σ)] d edgeLaw`,

with `F = localFactor w c (∇a_ϱ) (∇φ) (⟨φ, ϱ⟩ + ⟨σ, ϱ⟩)` (FS81 (6.18)), and for every
`ϱ ∈ ℛ_i`:

* activity: `|z_i(ϱ)| ≤ e^{D₂ A(ϱ)} Z(ϱ) · exp(−(λ/8) ∑_j |ϱ(j)| − λ/(8 D₁) A(ϱ))`;
* strip: `|∇a_ϱ| ≤ W`;
* locality: `supp a_ϱ ⊆ D(ϱ)`, so `F` depends on the field only through the phase `⟨φ, ϱ⟩` and
  the gradients on edges meeting `D(ϱ)`;
* `|F| ≤ 1` (FS81 (6.21)).

The amplitude `λ` (exponential branch below the threshold scale `k₀`) must satisfy
`100 · 4^{k₀} B(λK₁) ≤ λ/2`, and the quadratic branch `λ ≤ min(1/(2κK₀), 2^{γk₀}/K₁)`.

The gain is linear in the charges, so the entropy `Z` of the charge layer must be at most
exponential in `∑_j |ϱ(j)|`, which is why the KP instance uses a general site mixture
(`Generic/Renormalization/Mixture.lean`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic.SpinWave

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {G : Multigraph V E}
  {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V} {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- The assembled spin wave of a translated density of the charge layer (zero otherwise). -/
def layerSpinWave (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁) (κ amp : ℝ) (k₀ : ℕ)
    (i : Fin CL.n) (ϱ : V → ℤ) : V → ℝ :=
  if h : ϱ ∈ CL.R i then envelopeWave (Classical.choose (CL.wave i ϱ h)) κ amp k₀ else 0

/-- **The gain of a translated density.** Under the amplitude conditions,
`E_c(a_ϱ, ϱ) ≥ (λ/8) ∑_j |ϱ(j)| + λ/(8 D₁) A(ϱ)`. -/
theorem layer_gain (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁) {c : ℝ → ℝ}
    {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.R i) :
    amp / 8 * ∑ j, |(ϱ j : ℝ)| + amp / (8 * D₁) * A ϱ ≤
      translationEnergy c (gradLinear G) (layerSpinWave CL κ amp k₀ i ϱ) fun j => (ϱ j : ℝ) := by
  classical
  set Wv := Classical.choose (CL.wave i ϱ hϱ) with hWv
  obtain ⟨hα, hK0, hK1, hbase, hedge, hcover, -⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
  let _ := Wv.finite
  have hwave : layerSpinWave CL κ amp k₀ i ϱ = envelopeWave Wv κ amp k₀ := by
    simp only [layerSpinWave, dite_eq_left hϱ, hWv]
  rw [hwave]
  have hα1 : 1 < α := by rw [← hα]; exact Wv.alpha_gt_one
  have hγ : 0 ≤ gradExponent α := (gradExponent_pos hα1).le
  have hcount : ∀ t, Wv.scale t < k₀ →
      ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤ 100 * 4 ^ k₀ := by
    intro t ht
    refine (hedge t).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact pow_le_pow_right₀ (by norm_num) ht.le
  have hquad : ∀ s, k₀ ≤ s →
      amp ≤ quadAmplitude κ Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) s := by
    intro s hs
    rw [hK0, hK1, hα]
    refine le_min hquad₁ (hquad₂.trans ?_)
    refine div_le_div_of_nonneg_right ?_ hK₁.le
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hγ
  have hK₀' : 0 < Wv.K₀ := by rw [hK0]; exact hK₀
  have hK₁' : 0 < Wv.K₁ := by rw [hK1]; exact hK₁
  have hampW' : amp * Wv.K₁ ≤ W := by rw [hK1]; exact hampW
  have hexp' : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * Wv.K₁) ≤ amp / 2 := by
    rw [hK1]; exact hexp
  have hgain := translationEnergy_envelopeWave_ge_gain Wv hc hκ hK₀' hK₁' hamp hampW' hk₀ hcount
    hexp' hquad
  refine le_trans ?_ hgain
  set X : ℝ := ∑ j, |(ϱ j : ℝ)|
  set S : ℝ := ((Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℝ)
  set Q : ℝ := ∑ t ∈ Finset.univ.filter (fun t => Wv.scale t = 0), |Wv.charge t|
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have hcov : A ϱ / D₁ ≤ X + S := by rw [div_le_iff₀ hD₁]; linarith [hcover]
  have h1 : amp / (8 * D₁) * A ϱ ≤ amp / 8 * (X + S) := by
    rw [show amp / (8 * D₁) * A ϱ = amp / 8 * (A ϱ / D₁) by field_simp]
    exact mul_le_mul_of_nonneg_left hcov (by positivity)
  have h2 : (1 / 2 : ℝ) * X ≤ Q := hbase
  nlinarith

/-- The assembled spin waves satisfy the support and constancy clauses of KP P2.4 relative to the
translated family. -/
theorem layerSpinWave_clauses (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) :
    (∀ ϱ ∈ CL.R i, ∀ ϱ' ∈ G.comparableDensities (CL.R i) ϱ,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ' (centerOf ϱ'), layerSpinWave CL κ amp k₀ i ϱ j = c) ∧
    (∀ ϱ ∈ CL.R i, Function.support (layerSpinWave CL κ amp k₀ i ϱ) ⊆
      G.densityDomain ϱ (centerOf ϱ)) ∧
    ∀ ϱ ∈ CL.R i, ∀ ϱ' ∈ CL.R i, ϱ ≠ ϱ' →
      ∑ j, layerSpinWave CL κ amp k₀ i ϱ j * (ϱ' j : ℝ) = 0 := by
  classical
  refine ⟨fun ϱ hϱ => ?_, fun ϱ hϱ => ?_, fun ϱ hϱ ϱ' hϱ' hne => ?_⟩
  · simp only [layerSpinWave, dite_eq_left hϱ]
    exact envelopeWave_const_plus _ κ amp k₀
  · simp only [layerSpinWave, dite_eq_left hϱ]
    exact envelopeWave_support_subset _ κ amp k₀
  · simp only [layerSpinWave, dite_eq_left hϱ]
    set Wv := Classical.choose (CL.wave i ϱ hϱ)
    obtain ⟨-, -, -, -, -, -, horth⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
    let _ := Wv.finite
    simp only [envelopeWave, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [horth t ϱ' hϱ' (Ne.symm hne), mul_zero]

/-- **The T1.6-NG assembly on the rooted edge law.** See the module docstring. -/
theorem edgeLaw_renormalization_of_chargeLayer (hG : G.toSimpleGraph.Connected) (v : V)
    (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hroot : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i))
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) {κ κ' : ℝ}
    (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hD₁ : 0 < D₁)
    {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁) :
    ∃ (z : Fin CL.n → (V → ℤ) → ℝ) (a : Fin CL.n → (V → ℤ) → V → ℝ),
      (∀ σ : V → ℝ, ∫ φ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) ∂edgeLaw G w v =
        ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.R i, ((1 : ℂ) + (z i ϱ : ℂ) *
          localFactor w c (gradLinear G (a i ϱ)) (gradLinear G φ + 0)
            (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂edgeLaw G w v) ∧
      ∀ i, ∀ ϱ ∈ CL.R i,
        |z i ϱ| ≤ Real.exp (D₂ * A ϱ) * Zent ϱ *
          Real.exp (-(amp / 8 * ∑ j, |(ϱ j : ℝ)|) - amp / (8 * D₁) * A ϱ) ∧
        (∀ e, |G.grad (a i ϱ) e| ≤ W) ∧
        Function.support (a i ϱ) ⊆ G.densityDomain ϱ (centerOf ϱ) ∧
        ∀ (φ : V → ℝ) (θ : ℝ),
          ‖localFactor w c (gradLinear G (a i ϱ)) (gradLinear G φ + 0) θ‖ ≤ 1 := by
  classical
  set a : Fin CL.n → (V → ℤ) → V → ℝ := fun i ϱ => layerSpinWave CL κ amp k₀ i ϱ with ha
  set z : Fin CL.n → (V → ℤ) → ℝ := fun i ϱ =>
    CL.K i ϱ * Real.exp (-translationEnergy c (gradLinear G) (a i ϱ) fun j => (ϱ j : ℝ)) with hz
  -- the gradient bound
  have hgrad : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, |G.grad (a i ϱ) e| ≤ W := by
    intro i ϱ hϱ e
    obtain ⟨hα, hK0, hK1, -⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
    simp only [ha, layerSpinWave, dite_eq_left hϱ]
    refine (abs_grad_envelopeWave_le _ hκ (by rw [hK0]; exact hK₀) (by rw [hK1]; exact hK₁)
      hamp k₀ e).trans ?_
    rw [hK1]
    exact max_le hampW hW1
  refine ⟨z, a, fun σ => ?_, fun i ϱ hϱ => ⟨?_, hgrad i ϱ hϱ, ?_, fun φ θ => ?_⟩⟩
  · -- the expansion, then one ensemble at a time
    have hfin : IsProbabilityMeasure (edgeLaw G w v) := isProbabilityMeasure_edgeLaw G hG hw v
    have hpt : ∀ φ : V → ℝ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) =
        ∑ i, (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
          (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ) := by
      intro φ
      rw [CL.expand fun j => φ j + σ j]
      push_cast
      rfl
    have hint : ∀ i, Integrable (fun φ : V → ℝ => (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
        (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)) (edgeLaw G w v) := by
      intro i
      refine Integrable.const_mul ?_ _
      refine Integrable.of_bound ?_ (∏ ϱ ∈ CL.N i, (1 + |CL.K i ϱ|))
        (Filter.Eventually.of_forall fun φ => norm_prod_one_add_mul_cos_le _ _ _)
      refine (Complex.continuous_ofReal.comp (continuous_finsetProd _ fun ϱ _ => ?_)).aestronglyMeasurable
      fun_prop
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    congr 1
    obtain ⟨hR, hNa⟩ := hroot i
    obtain ⟨hconst, hsupp, horth⟩ := layerSpinWave_clauses CL κ amp k₀ i
    rw [hR] at hconst hsupp horth
    have key := edgeLaw_integral_ensemble_eq G hG hw v (CL.N i) hNa (CL.K i) σ centerOf (a i)
      hconst hsupp horth (fun ϱ hϱ e => hgrad i ϱ (by rw [hR]; exact hϱ) e)
    rw [key, hR]
  · -- the activity
    have hgain := layer_gain CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂ i ϱ hϱ
    have hK := CL.entropy i ϱ hϱ
    simp only [hz, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hZ : 0 ≤ Real.exp (D₂ * A ϱ) * Zent ϱ := (abs_nonneg _).trans hK
    calc |CL.K i ϱ| * Real.exp (-translationEnergy c (gradLinear G) (a i ϱ) fun j => (ϱ j : ℝ))
        ≤ (Real.exp (D₂ * A ϱ) * Zent ϱ) *
            Real.exp (-(amp / 8 * ∑ j, |(ϱ j : ℝ)|) - amp / (8 * D₁) * A ϱ) := by
          refine mul_le_mul hK (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hZ
          simp only [ha] at hgain ⊢
          linarith
      _ = _ := rfl
  · simp only [ha]
    exact (layerSpinWave_clauses CL κ amp k₀ i).2.1 ϱ hϱ
  · exact norm_localFactor_le_one hw.ratio_le _ _ (fun e => hgrad i ϱ hϱ e) θ

end FroehlichSpencer.BKT.Generic

end
