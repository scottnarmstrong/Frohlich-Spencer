/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Tilt.Phased
public import FroehlichSpencer.BKT.Generic.Rooted.LayerD
public import FroehlichSpencer.BKT.Generic.Moment.Offset

/-!
# The phased renormalization identity for a rooted D-layer (the dipole tilt construction: FS81 (7.29), generic form)

This is interpolation's **the branch mixture** in generic form: the multi-site renormalized representation (7.29) of the tilted
SOS ensemble integrals. Under any law with phased character translations (phase `ψ`, e.g. the tilted
law `tiltLaw` with `ψ(a) = ⟨∇a, b⟩`), the comb of a `RootedChargeLayerD` expands into the
renormalized factors `1 + z_ρ F_ρ`, with the same waves and activities as without the tilt, and with
every factor's phase shifted by `ψ(a_ρ)`. That shift is FS81's endpoint phase
`α_ρ = ε(a_ρ(0) − a_ρ(x))`.

`rootedD_identity_of_law_phased`; with `ψ = 0` it is `rootedD_identity_of_law`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Tilt

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
variable {G : Multigraph V E} {root : V} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ} {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- **The phased T1.6-NG identity for a `RootedChargeLayerD`** (FS81 (7.29), generic form). -/
theorem rootedD_identity_of_law_phased (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] (r : E → ℝ)
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hw : IsStripWeight w W c) (ψ : (V → ℝ) →ₗ[ℝ] ℝ)
    (hμ : CharacterTranslationPhased μ (gradLinear G) w r W ψ) {κ : ℝ}
    (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) {amp : ℝ} (hamp : 0 ≤ amp)
    (hampW : amp * K₁ ≤ W) (hW1 : 1 ≤ W) (k₀ : ℕ) (σ : V → ℝ) :
    ∫ φ, ((∏ j, lam j (φ j + σ j - (φ root + σ root)) : ℝ) : ℂ) ∂μ =
      ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.N i, ((1 : ℂ) +
        ((rootedActivityD CL c κ amp k₀ i ϱ : ℝ) : ℂ) *
        localFactor w c (gradLinear G (rootedSpinWaveD CL κ amp k₀ i ϱ)) (gradLinear G φ + r)
          (∑ j, φ j * (ϱ j : ℝ) +
            (∑ j, σ j * (ϱ j : ℝ) + ψ (rootedSpinWaveD CL κ amp k₀ i ϱ)))) ∂μ := by
  classical
  have hpt : ∀ φ : V → ℝ, ((∏ j, lam j (φ j + σ j - (φ root + σ root)) : ℝ) : ℂ) =
      ∑ i, (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
        (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ) := by
    intro φ
    have hexp := CL.expand (fun j => φ j + σ j - (φ root + σ root)) (sub_self _)
    beta_reduce at hexp
    rw [hexp, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_mul]
    congr 2
    refine Finset.prod_congr rfl fun ϱ hϱ => ?_
    have hs := sum_sub_const_mul_eq (CL.neutral i ϱ hϱ) (fun j => φ j + σ j) (φ root + σ root)
    beta_reduce at hs
    rw [hs]
  have hint : ∀ i, Integrable (fun φ : V → ℝ => (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
      (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)) μ := by
    intro i
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound ?_ (∏ ϱ ∈ CL.N i, (1 + |CL.K i ϱ|))
      (Filter.Eventually.of_forall fun φ => norm_prod_one_add_mul_cos_le _ _ _)
    refine (Complex.continuous_ofReal.comp
      (continuous_finsetProd _ fun ϱ _ => ?_)).aestronglyMeasurable
    fun_prop
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  congr 1
  set P := CL.N i
  have key := integral_prod_add_mul_cos_eq_localFactor_phased μ (gradLinear G) w c hw.cost_even r
    hw.width_nonneg ψ hμ hw.ofReal_ne_zero
    (ι := P) (fun ϱ j => ((ϱ : V → ℤ) j : ℝ))
    (fun ϱ => by exact_mod_cast CL.neutral i ϱ ϱ.2) (fun _ => 1) (fun ϱ => CL.K i ϱ)
    (fun ϱ => ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ)) (fun ϱ => rootedSpinWaveD CL κ amp k₀ i ϱ)
    (fun ϱ ϱ' hne => rootedSpinWaveD_orth CL κ amp k₀ i ϱ.2 ϱ'.2 fun h => hne (Subtype.ext h))
    (fun ϱ ϱ' hne e => by
      simp only [gradLinear_apply]
      exact grad_rootedSpinWaveD_disjoint CL κ amp k₀ i ϱ.2 ϱ'.2
        (fun h => hne (Subtype.ext h)) e)
    (fun ϱ e => by
      simp only [gradLinear_apply]
      exact (abs_grad_rootedSpinWaveD_le CL hκ hK₀ hK₁ hamp k₀ i ϱ ϱ.2 e).trans
        (max_le hampW hW1))
  have hl : ∀ φ : V → ℝ, (((∏ ϱ ∈ P, (1 + CL.K i ϱ *
      Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ)))) : ℝ) : ℂ) =
      ((∏ ϱ : P, (1 + CL.K i ϱ * Real.cos (∑ j, φ j * ((ϱ : V → ℤ) j : ℝ) +
        ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ))) : ℝ) : ℂ) := by
    intro φ
    rw [← Finset.prod_coe_sort P]
    congr 2
    funext ϱ
    congr 3
    exact sum_add_mul_eq φ σ ϱ
  simp_rw [hl]
  rw [key]
  congr 1
  funext φ
  rw [← Finset.prod_coe_sort P]
  rfl

end FroehlichSpencer.BKT.SOS.Tilt

end
