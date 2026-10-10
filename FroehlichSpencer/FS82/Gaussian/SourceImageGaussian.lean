/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.FiniteQuotientGaussian
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Gaussian image of the curl quotient -/

public section

namespace FroehlichSpencer.FS82.Gaussian

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {V E P : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]

noncomputable abbrev FiniteCurlImage (C : ExactOneComplex V E P) := C.d₁.range

@[expose] noncomputable def finiteCurlQuotientToImage (C : ExactOneComplex V E P) :
    FiniteGaugeQuotient C ≃ₗ[ℝ] FiniteCurlImage C := C.d₁.quotKerEquivRange

theorem finiteCurlQuotientToImage_apply (C : ExactOneComplex V E P)
    (q : FiniteGaugeQuotient C) :
    finiteCurlQuotientToImage C q = C.d₁.quotKerEquivRange q := rfl

@[expose] noncomputable def finiteCurlImageGaussian (C : ExactOneComplex V E P)
    (β : ℝ) (hβ : 0 ≤ β) : Measure (FiniteCurlImage C) :=
  Measure.map (finiteCurlQuotientToImage C) (finiteComplexQuotientGaussian C β hβ)


theorem finiteCurlQuotientToImage_measurable (C : ExactOneComplex V E P) :
    Measurable (finiteCurlQuotientToImage C) := by
  rw [measurable_from_quotient]
  have hfun : (finiteCurlQuotientToImage C ∘
      (Quotient.mk'' : EuclideanSpace ℝ E → FiniteGaugeQuotient C)) =
        C.d₁.rangeRestrict := by
    funext x
    apply Subtype.ext
    rfl
  rw [hfun]
  exact (LinearMap.continuous_of_finiteDimensional C.d₁.rangeRestrict).measurable

theorem finiteCurlImageGaussian_eq_pushAmbient (C : ExactOneComplex V E P)
    (β : ℝ) (hβ : 0 ≤ β) :
    finiteCurlImageGaussian C β hβ =
      Measure.map C.d₁.rangeRestrict
        (multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)) := by
  change Measure.map (finiteCurlQuotientToImage C)
      (Measure.map (finiteComplexQuotientMap C)
        (multivariateGaussian 0 (finiteComplexCovarianceMatrix C β))) = _
  rw [Measure.map_map (finiteCurlQuotientToImage_measurable C)
    (finiteComplexQuotientMap_measurable C)]
  congr 1

theorem finiteHodgeInverse_adjoint_on_image (C : ExactOneComplex V E P)
    (t : FiniteCurlImage C) :
    C.d₁ (hodgeInverseOnCoClosed C
      ⟨C.d₁.adjoint t.1, by
        apply LinearMap.mem_ker.mpr
        have hcomp : C.d₀.adjoint.comp C.d₁.adjoint = 0 := by
          rw [← LinearMap.adjoint_comp, C.complex]
          simp
        change (C.d₀.adjoint.comp C.d₁.adjoint) t.1 = 0
        rw [hcomp]
        simp⟩ : EuclideanSpace ℝ E) = t.1 := by
  let μ : coClosed C := ⟨C.d₁.adjoint t.1, by
    apply LinearMap.mem_ker.mpr
    have hcomp : C.d₀.adjoint.comp C.d₁.adjoint = 0 := by
      rw [← LinearMap.adjoint_comp, C.complex]
      simp
    change (C.d₀.adjoint.comp C.d₁.adjoint) t.1 = 0
    rw [hcomp]
    simp⟩
  let z : coClosed C := hodgeInverseOnCoClosed C μ
  have hz : C.d₁.adjoint (C.d₁ (z : EuclideanSpace ℝ E)) = C.d₁.adjoint t.1 := by
    have h := congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C μ)
    change formLaplacian C (z : EuclideanSpace ℝ E) = μ.1 at h
    change C.d₁.adjoint (C.d₁ (z : EuclideanSpace ℝ E)) = _
    exact h
  have hdiff : C.d₁.adjoint (C.d₁ (z : EuclideanSpace ℝ E) - t.1) = 0 := by
    rw [map_sub, hz, sub_self]
  obtain ⟨a, ha⟩ := t.2
  have hdelta : C.d₁ (z : EuclideanSpace ℝ E) - t.1 = C.d₁ ((z : EuclideanSpace ℝ E) - a) := by
    rw [map_sub, ha]
  have hnorm : inner ℝ (C.d₁ (z : EuclideanSpace ℝ E) - t.1)
      (C.d₁ (z : EuclideanSpace ℝ E) - t.1) = 0 := by
    rw [hdelta]
    calc
      inner ℝ (C.d₁ ((z : EuclideanSpace ℝ E) - a))
          (C.d₁ ((z : EuclideanSpace ℝ E) - a)) =
        inner ℝ ((z : EuclideanSpace ℝ E) - a)
          (C.d₁.adjoint (C.d₁ ((z : EuclideanSpace ℝ E) - a))) := by
            rw [← LinearMap.adjoint_inner_right]
      _ = 0 := by
        rw [← hdelta, hdiff]
        simp
  have hzero : C.d₁ (z : EuclideanSpace ℝ E) - t.1 = 0 := inner_self_eq_zero.mp hnorm
  have hresult : C.d₁ (z : EuclideanSpace ℝ E) = t.1 := sub_eq_zero.mp hzero
  change C.d₁ (hodgeInverseOnCoClosed C μ : EuclideanSpace ℝ E) = t.1
  simpa [z, μ] using hresult

theorem finiteCurlImageGaussian_eq_scaledStdGaussian (C : ExactOneComplex V E P)
    {β : ℝ} (hβ : 0 < β) :
    finiteCurlImageGaussian C β (le_of_lt hβ) =
      Measure.map (fun x : FiniteCurlImage C => Real.sqrt β • x)
        (stdGaussian (FiniteCurlImage C)) := by
  rw [finiteCurlImageGaussian_eq_pushAmbient C β (le_of_lt hβ)]
  let base := multivariateGaussian 0 (finiteComplexCovarianceMatrix C β)
  let L := C.d₁.rangeRestrict
  apply Measure.ext_of_charFun
  funext t
  let μ : coClosed C := ⟨C.d₁.adjoint t.1, by
    apply LinearMap.mem_ker.mpr
    have hcomp : C.d₀.adjoint.comp C.d₁.adjoint = 0 := by
      rw [← LinearMap.adjoint_comp, C.complex]
      simp
    change (C.d₀.adjoint.comp C.d₁.adjoint) t.1 = 0
    rw [hcomp]
    simp⟩
  have hqform : inner ℝ (μ : EuclideanSpace ℝ E)
      (hodgeInverseOnCoClosed C μ : EuclideanSpace ℝ E) = ‖t‖ ^ 2 := by
    calc
      inner ℝ (μ : EuclideanSpace ℝ E)
          (hodgeInverseOnCoClosed C μ : EuclideanSpace ℝ E) =
        inner ℝ t.1 (C.d₁ (hodgeInverseOnCoClosed C μ : EuclideanSpace ℝ E)) :=
          LinearMap.adjoint_inner_left C.d₁ _ t.1
      _ = inner ℝ t.1 t.1 := by rw [finiteHodgeInverse_adjoint_on_image C t]
      _ = ‖t‖ ^ 2 := by simp
  have hcov : inner ℝ (μ : EuclideanSpace ℝ E)
      ((β • finiteComplexAmbientCovariance C) (μ : EuclideanSpace ℝ E)) =
        β * ‖t‖ ^ 2 := by
    change inner ℝ (μ : EuclideanSpace ℝ E)
      (β • finiteComplexAmbientCovariance C (μ : EuclideanSpace ℝ E)) = _
    rw [real_inner_smul_right, finiteComplexAmbientCovariance_coClosed_apply, hqform]
  have hmapchar : charFun (Measure.map L base) t = charFun base (μ : EuclideanSpace ℝ E) := by
    rw [charFun_map_eq_charFun_map_inner_one (μ := base) (Y := L) (by fun_prop) t]
    have hf : (fun x => inner ℝ (L x) t) =
        (fun x => inner ℝ x (μ : EuclideanSpace ℝ E)) := by
      funext x
      change inner ℝ (C.d₁ x) t.1 = inner ℝ x (C.d₁.adjoint t.1)
      exact (LinearMap.adjoint_inner_right C.d₁ x t.1).symm
    rw [hf]
    simpa using (charFun_map_eq_charFun_map_inner_one (μ := base) (Y := id)
      (by fun_prop) (μ : EuclideanSpace ℝ E)).symm
  calc
    charFun (Measure.map L base) t = charFun base (μ : EuclideanSpace ℝ E) := hmapchar
    _ = Complex.exp (-↑(inner ℝ (μ : EuclideanSpace ℝ E)
        ((β • finiteComplexAmbientCovariance C) (μ : EuclideanSpace ℝ E)) / 2)) :=
          finiteComplexAmbientGaussian_characteristic C (le_of_lt hβ) (μ : _)
    _ = Complex.exp (-(β : ℂ) * (‖t‖ ^ 2 : ℂ) / 2) := by
          rw [hcov]
          push_cast
          ring_nf
    _ = charFun (Measure.map (fun x : FiniteCurlImage C => Real.sqrt β • x)
        (stdGaussian (FiniteCurlImage C))) t := by
          rw [charFun_map_smul (μ := stdGaussian (FiniteCurlImage C))
            (Real.sqrt β) t, charFun_stdGaussian]
          apply congrArg Complex.exp
          have hnorm : ‖Real.sqrt β • t‖ = Real.sqrt β * ‖t‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg β)]
          rw [hnorm]
          push_cast
          have hsqrt : (↑(Real.sqrt β) : ℂ) ^ 2 = (↑β : ℂ) := by
            exact_mod_cast Real.sq_sqrt (le_of_lt hβ)
          rw [mul_pow, hsqrt]
          ring_nf

end FroehlichSpencer.FS82.Gaussian

end
