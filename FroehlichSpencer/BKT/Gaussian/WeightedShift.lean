/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.ExponentialMoment
public import FroehlichSpencer.BKT.Bridge.GFFMeasure

/-!
# Completing the square with a weight (KP (3.1))

KP §3, p. 14 (Kharash–Peled, first version, display (3.1)):
for zero-sum `f` and the pinned translate `σ` solving `-Δ σ = f / β`, `σ_v = 0` (KP (1.5)),
`∫ e^⟨φ,f⟩ W(φ) dμ^GFF = e^{⟨f, -Δ⁻¹ f⟩ / (2β)} ∫ W(φ + σ) dμ^GFF`
for every bounded measurable weight `W`.

With `W(φ) = ∏_j λ_j(φ_j)` this gives
`𝔼_{β,Λ,λ,v}[e^⟨φ,f⟩] = Z⁻¹ e^{Q(f)/(2β)} Z(σ)`.

The proof translates Lebesgue measure by
`σ` and uses the pointwise identity `gff_shift_integrand` (KP (1.4)); `σ` is the `gffShift`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open MeasureTheory Multigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

/--
KP (3.1): completing the square under the GFF law with a bounded measurable weight
`W`.
-/
theorem integral_exp_pairing_mul_gffLaw (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (β : ℝ) (hβ : 0 < β) (v : V) [DecidableEq V] (f : V → ℝ) (hf : ∑ j, f j = 0)
    (W : (V → ℝ) → ℝ) (hWmeas : Measurable W) (C : ℝ) (hWb : ∀ φ, |W φ| ≤ C) :
    ∫ φ, Real.exp (∑ j, φ j * f j) * W φ ∂gffLaw G hG β hβ v =
      Real.exp (pairing f (-G.greenOp hG f) / (2 * β)) *
        ∫ φ, W (φ + gffShift G hG β f v) ∂gffLaw G hG β hβ v := by
  rw [gffLaw_eq_gffMeasure G hG β hβ v]
  set σ := gffShift G hG β f v with hσ
  have hdens := integrable_gffDensity G hG β hβ v
  have htilt := gff_tilted_density_integrable G hG β hβ f hf v
  have hbound : ∀ᵐ φ ∂(volume : Measure (V → ℝ)), ‖W φ‖ ≤ C :=
    ae_of_all _ fun φ => (Real.norm_eq_abs _).le.trans (hWb φ)
  have hboundσ : ∀ᵐ φ ∂(volume : Measure (V → ℝ)), ‖W (φ + σ)‖ ≤ C :=
    ae_of_all _ fun φ => (Real.norm_eq_abs _).le.trans (hWb (φ + σ))
  -- Left side through the density formula.
  have hL : Integrable (fun φ => (Real.exp (pairing φ f) * W φ) * gffDensity G β v φ)
      (volume : Measure (V → ℝ)) := by
    have h := htilt.bdd_mul hWmeas.aestronglyMeasurable hbound
    refine h.congr (ae_of_all _ fun φ => ?_)
    simp only
    ring
  -- Right side through the density formula.
  have hR : Integrable (fun φ => W (φ + σ) * gffDensity G β v φ) (volume : Measure (V → ℝ)) :=
    hdens.bdd_mul (hWmeas.comp (measurable_id.add_const σ)).aestronglyMeasurable hboundσ
  have hLform := (gffMeasure_integral_eq_div G hG β hβ v
    (fun φ => Real.exp (pairing φ f) * W φ) hL).2
  have hRform := (gffMeasure_integral_eq_div G hG β hβ v (fun φ => W (φ + σ)) hR).2
  change ∫ φ, Real.exp (pairing φ f) * W φ ∂gffMeasure G hG β hβ v = _
  rw [hLform, hRform, mul_div_assoc', ← integral_const_mul]
  congr 1
  -- Translate the numerator by `σ`.
  rw [← integral_add_right_eq_self
    (μ := (volume : Measure (V → ℝ)))
    (fun φ : V → ℝ => Real.exp (pairing φ f) * W φ * gffDensity G β v φ) σ]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  have hpt := gff_shift_integrand G hG β hβ f hf v φ
  simp only
  calc Real.exp (pairing (φ + σ) f) * W (φ + σ) * gffDensity G β v (φ + σ)
      = (Real.exp (pairing (φ + σ) f) * gffDensity G β v (φ + σ)) * W (φ + σ) := by ring
    _ = (Real.exp (pairing f (-G.greenOp hG f) / (2 * β)) * gffDensity G β v φ) *
          W (φ + σ) := by rw [hpt]
    _ = Real.exp (pairing f (-G.greenOp hG f) / (2 * β)) *
          (W (φ + σ) * gffDensity G β v φ) := by ring

end FroehlichSpencer.BKT

end
