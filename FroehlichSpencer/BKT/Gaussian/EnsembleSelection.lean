/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.ChargeSelection
public import FroehlichSpencer.BKT.Bridge.GFFMeasure
public import FroehlichSpencer.BKT.Surface.GFFWellDefined
public import FroehlichSpencer.BKT.Charges.DensityNeighbourhood

/-!
# Step 1 at the ensemble level: removing the non-neutral density

KP §2.3.1, Step 1, p. 11 (Kharash–Peled, first version):
for an ensemble `𝒩` with at most one non-neutral density (Theorem 2.2(a)),
`∫ ∏_{ϱ ∈ 𝒩} [1 + K(ϱ) cos(⟨φ, ϱ⟩ + ⟨σ, ϱ⟩)] dμ^GFF = ∫ ∏_{ϱ ∈ 𝒩₀} [⋯] dμ^GFF`,
where `𝒩₀` is the neutral part (KP (2.13)).

The per-charge root integration is
`gffMeasure_integral_charge_eq_zero` (`Gaussian/ChargeSelection.lean`).

Here it is applied to
the shift-invariant, bounded and continuous product over `𝒩₀`, and transferred to the
GFF law `gffLaw` through `Bridge/GFFMeasure.lean`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open MeasureTheory

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

/--
The cosine factor of a non-neutral charge integrates to zero against every bounded
measurable shift-invariant observable, for the GFF law (KP §2.3.1, Step 1).
-/
theorem gffLaw_integral_cos_charge_mul_eq_zero (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (ρ : V → ℤ)
    (hρ : ∑ j, ρ j ≠ 0) (s : ℝ) (F : (V → ℝ) → ℝ) (hFshift : GffShiftInvariant F)
    (hFmeas : Measurable F) (C : ℝ) (hFbounded : ∀ φ, |F φ| ≤ C) :
    ∫ φ, Real.cos (∑ j, φ j * (ρ j : ℝ) + s) * F φ ∂gffLaw G hG β hβ v = 0 := by
  classical
  rw [gffLaw_eq_gffMeasure G hG β hβ v]
  obtain ⟨hint, hzero⟩ :=
    gffMeasure_integral_charge_eq_zero G hG β hβ v ρ F hFshift hFmeas C hFbounded hρ
  have hpoint : ∀ φ : V → ℝ,
      Real.cos (∑ j, φ j * (ρ j : ℝ) + s) * F φ =
        RCLike.re (Complex.exp (Complex.I * (s : ℂ)) * gffChargeObservable ρ F φ) := by
    intro φ
    simp only [gffChargeObservable, Multigraph.pairing, RCLike.re_to_complex]
    rw [← mul_assoc, ← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, mul_comm Complex.I,
      Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, add_comm]
  simp_rw [hpoint]
  rw [integral_re (hint.const_mul _), integral_const_mul, hzero, mul_zero]
  simp

/-- The product of cosine factors over neutral densities is invariant under constant shifts. -/
theorem gffShiftInvariant_prod_neutral (N : Finset (V → ℤ)) (hN : ∀ ρ ∈ N, ∑ j, ρ j = 0)
    (K s : (V → ℤ) → ℝ) :
    GffShiftInvariant fun φ : V → ℝ =>
      ∏ ρ ∈ N, (1 + K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + s ρ)) := by
  intro φ c
  refine Finset.prod_congr rfl fun ρ hρ => ?_
  have hshift : ∑ j, (φ j + c) * (ρ j : ℝ) = ∑ j, φ j * (ρ j : ℝ) := by
    have hsum : ∑ j, (ρ j : ℝ) = 0 := by exact_mod_cast hN ρ hρ
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero]
  rw [hshift]

/-- KP §2.3.1, Step 1: for an ensemble with at most one non-neutral density, the integral of
the product of cosine factors equals the integral over the neutral part `𝒩₀` (KP (2.13)). The
phases `s ϱ` are arbitrary constants; KP's `⟨σ, ϱ⟩` is the case `s ϱ = ∑_j σ j ϱ j`. -/
theorem gffLaw_integral_prod_eq_neutralPart (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (N : Finset (V → ℤ))
    (hN : ∀ ρ₁ ∈ N, ∀ ρ₂ ∈ N, ∑ j, ρ₁ j ≠ 0 → ∑ j, ρ₂ j ≠ 0 → ρ₁ = ρ₂)
    (K s : (V → ℤ) → ℝ) :
    ∫ φ, ∏ ρ ∈ N, (1 + K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + s ρ)) ∂gffLaw G hG β hβ v =
      ∫ φ, ∏ ρ ∈ neutralPart N, (1 + K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + s ρ))
        ∂gffLaw G hG β hβ v := by
  classical
  by_cases hall : ∀ ρ ∈ N, ∑ j, ρ j = 0
  · rw [neutralPart_eq_self hall]
  simp only [not_forall, exists_prop] at hall
  obtain ⟨ρc, hρc, hQc⟩ := hall
  have hN₀ : neutralPart N = N.erase ρc :=
    neutralPart_eq_erase hQc fun ρ hρ hQ => hN ρ hρ ρc hρc hQ hQc
  set F : (V → ℝ) → ℝ := fun φ =>
    ∏ ρ ∈ N.erase ρc, (1 + K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + s ρ)) with hF
  have hsplit : ∀ φ : V → ℝ,
      ∏ ρ ∈ N, (1 + K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + s ρ)) =
        (1 + K ρc * Real.cos (∑ j, φ j * (ρc j : ℝ) + s ρc)) * F φ := fun φ =>
    (Finset.mul_prod_erase N (fun ρ => 1 + K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + s ρ))
      hρc).symm
  rw [hN₀]
  simp_rw [hsplit]
  have hneutral : ∀ ρ ∈ N.erase ρc, ∑ j, ρ j = 0 := by
    intro ρ hρ
    by_contra hQ
    exact (Finset.mem_erase.mp hρ).1 (hN ρ (Finset.mem_erase.mp hρ).2 ρc hρc hQ hQc)
  have hFcont : Continuous F := by
    simp only [hF]
    fun_prop
  have hFbound : ∀ φ, |F φ| ≤ ∏ ρ ∈ N.erase ρc, (1 + |K ρ|) := by
    intro φ
    simp only [hF]
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ρ _ => ?_
    calc |1 + K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + s ρ)|
        ≤ |(1 : ℝ)| + |K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + s ρ)| := abs_add_le _ _
      _ ≤ 1 + |K ρ| := by
        rw [abs_one, abs_mul]
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hFshift : GffShiftInvariant F := gffShiftInvariant_prod_neutral _ hneutral K s
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  have hFint : Integrable F (gffLaw G hG β hβ v) :=
    Integrable.of_bound hFcont.aestronglyMeasurable _
      (ae_of_all _ fun φ => (Real.norm_eq_abs _).le.trans (hFbound φ))
  have hcosint : Integrable
      (fun φ : V → ℝ => Real.cos (∑ j, φ j * (ρc j : ℝ) + s ρc) * F φ)
      (gffLaw G hG β hβ v) :=
    hFint.bdd_mul (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun φ => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
  have hzero := gffLaw_integral_cos_charge_mul_eq_zero G hG β hβ v ρc hQc (s ρc) F hFshift
    hFcont.measurable _ hFbound
  calc ∫ φ, (1 + K ρc * Real.cos (∑ j, φ j * (ρc j : ℝ) + s ρc)) * F φ ∂gffLaw G hG β hβ v
      = ∫ φ, (F φ + K ρc * (Real.cos (∑ j, φ j * (ρc j : ℝ) + s ρc) * F φ))
          ∂gffLaw G hG β hβ v := by
        refine integral_congr_ae (ae_of_all _ fun φ => ?_)
        ring
    _ = ∫ φ, F φ ∂gffLaw G hG β hβ v := by
        rw [integral_add hFint (hcosint.const_mul _), integral_const_mul, hzero, mul_zero,
          add_zero]

/-- KP §2.3.1, Step 1, in the form of KP (2.9): the phases are `⟨σ, ϱ⟩`. -/
theorem gffLaw_integral_prod_shift_eq_neutralPart (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (N : Finset (V → ℤ))
    (hN : ∀ ρ₁ ∈ N, ∀ ρ₂ ∈ N, ∑ j, ρ₁ j ≠ 0 → ∑ j, ρ₂ j ≠ 0 → ρ₁ = ρ₂)
    (K : (V → ℤ) → ℝ) (σ : V → ℝ) :
    ∫ φ, ∏ ρ ∈ N, (1 + K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + ∑ j, σ j * (ρ j : ℝ)))
        ∂gffLaw G hG β hβ v =
      ∫ φ, ∏ ρ ∈ neutralPart N,
          (1 + K ρ * Real.cos (∑ j, φ j * (ρ j : ℝ) + ∑ j, σ j * (ρ j : ℝ)))
        ∂gffLaw G hG β hβ v :=
  gffLaw_integral_prod_eq_neutralPart G hG β hβ v N hN K fun ρ => ∑ j, σ j * (ρ j : ℝ)

end FroehlichSpencer.BKT

end
