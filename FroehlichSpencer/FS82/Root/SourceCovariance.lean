/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.LatticeComplex
public import FroehlichSpencer.FS82.Gaussian.SourceGaussian

/-!
# the lattice and source-star covariances agree under the orientation twist

The lattice complex is the conjugate of the source-star complex by the diagonal sign involution
`T` (`d₀ = T ∘ D₀`, `d₁ = D₁ ∘ T`).

Hence `T` carries lattice co-closed forms to source-star
co-closed forms, intertwines the two Hodge inverses, and preserves the covariance quadratic form.

The source quotient Gaussian therefore has the lattice character `exp(−(β/2)⟨m, V_Λ m⟩)` on the
twisted test `T m`.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

open FroehlichSpencer.FS82.Gaussian

variable {B : SourceBox}

theorem latticeD₀_adjoint_apply (origin : Fin 4 → ℤ)
    (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    (latticeExactOneComplex (B := B) origin).d₀.adjoint x =
      (sourceDualD₀ (B := B)).adjoint (sourceDualTLinear x) := by
  have hTadj : (sourceDualTLinear (B := B)).adjoint = sourceDualTLinear :=
    sourceDualTLinear_symmetric.adjoint_eq
  have hC : (latticeExactOneComplex (B := B) origin).d₀ =
      (sourceDualTLinear (B := B)).comp sourceDualD₀ := rfl
  rw [hC, LinearMap.adjoint_comp, hTadj, LinearMap.comp_apply]

theorem latticeFormLaplacian_apply (origin : Fin 4 → ℤ)
    (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    formLaplacian (latticeExactOneComplex (B := B) origin) x =
      sourceDualTLinear (formLaplacian (sourceDualComplex B) (sourceDualTLinear x)) := by
  have hTadj : (sourceDualTLinear (B := B)).adjoint = sourceDualTLinear :=
    sourceDualTLinear_symmetric.adjoint_eq
  have hC : (latticeExactOneComplex (B := B) origin).d₁ =
      (sourceDualD₁ (B := B)).comp sourceDualTLinear := rfl
  have hS : (sourceDualComplex B).d₁ = sourceDualD₁ := rfl
  unfold formLaplacian
  rw [hC, hS, LinearMap.adjoint_comp, hTadj]
  rfl

/-- The orientation twist of a lattice co-closed one-form, as a source-star co-closed form. -/
noncomputable def latticeToSourceCoClosed (origin : Fin 4 → ℤ)
    (m : coClosed (latticeExactOneComplex (B := B) origin)) :
    coClosed (sourceDualComplex B) :=
  ⟨sourceDualTLinear (m : EuclideanSpace ℝ (SourceDualOneCells B)), by
    rw [coClosed, LinearMap.mem_ker]
    have h : (latticeExactOneComplex (B := B) origin).d₀.adjoint
        (m : EuclideanSpace ℝ (SourceDualOneCells B)) = 0 := LinearMap.mem_ker.mp m.property
    rw [latticeD₀_adjoint_apply] at h
    exact h⟩

@[simp] theorem latticeToSourceCoClosed_coe (origin : Fin 4 → ℤ)
    (m : coClosed (latticeExactOneComplex (B := B) origin)) :
    (latticeToSourceCoClosed origin m : EuclideanSpace ℝ (SourceDualOneCells B)) =
      sourceDualTLinear (m : EuclideanSpace ℝ (SourceDualOneCells B)) := rfl

/-- The twist intertwines the two Hodge inverses. -/
theorem hodgeInverse_latticeToSource (origin : Fin 4 → ℤ)
    (m : coClosed (latticeExactOneComplex (B := B) origin)) :
    hodgeInverseOnCoClosed (sourceDualComplex B) (latticeToSourceCoClosed origin m) =
      latticeToSourceCoClosed origin
        (hodgeInverseOnCoClosed (latticeExactOneComplex (B := B) origin) m) := by
  apply hodgeOnCoClosed_injective (sourceDualComplex B)
  rw [hodgeOnCoClosed_hodgeInverse]
  apply Subtype.ext
  have hv : formLaplacian (latticeExactOneComplex (B := B) origin)
      (hodgeInverseOnCoClosed (latticeExactOneComplex (B := B) origin) m :
        EuclideanSpace ℝ (SourceDualOneCells B)) = m :=
    congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse _ m)
  rw [latticeFormLaplacian_apply] at hv
  change sourceDualTLinear (m : EuclideanSpace ℝ (SourceDualOneCells B)) =
    formLaplacian (sourceDualComplex B) (sourceDualTLinear
      (hodgeInverseOnCoClosed (latticeExactOneComplex (B := B) origin) m :
        EuclideanSpace ℝ (SourceDualOneCells B)))
  rw [← hv, sourceDualTLinear_apply_apply]

/-- The covariance quadratic form is invariant under the twist. -/
theorem quotientCovarianceQuadratic_latticeToSource (origin : Fin 4 → ℤ)
    (m : coClosed (latticeExactOneComplex (B := B) origin)) :
    quotientCovarianceQuadratic (sourceDualComplex B) (latticeToSourceCoClosed origin m) =
      quotientCovarianceQuadratic (latticeExactOneComplex (B := B) origin) m := by
  unfold quotientCovarianceQuadratic
  rw [hodgeInverse_latticeToSource]
  simp only [latticeToSourceCoClosed_coe]
  rw [sourceDualTLinear_symmetric, sourceDualTLinear_apply_apply]

/-- The quotient of a finite exact complex carries the Borel sets of its quotient topology. -/
theorem finiteGaugeQuotient_opensMeasurableSpace {V E P : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P]
    (C : ExactOneComplex V E P) : OpensMeasurableSpace (FiniteGaugeQuotient C) := by
  refine ⟨?_⟩
  change MeasurableSpace.generateFrom {s : Set (FiniteGaugeQuotient C) | IsOpen s} ≤ _
  rw [MeasurableSpace.generateFrom_le_iff]
  intro s hs
  have hsopen : IsOpen s := by simpa only [Set.mem_ofPred_eq] using hs
  have hms : MeasurableSet s := by
    rw [measurableSet_quotient]
    exact ((finiteComplexQuotientMap C).continuous.isOpen_preimage s hsopen).measurableSet
  simpa only [Set.mem_ofPred_eq] using hms

theorem measurable_sourceDualQuotientTestFunctional (x : coClosed (sourceDualComplex B)) :
    Measurable (sourceDualQuotientTestFunctional x) := by
  have : OpensMeasurableSpace (FiniteGaugeQuotient (sourceDualComplex B)) :=
    finiteGaugeQuotient_opensMeasurableSpace _
  exact (sourceDualQuotientTestFunctional x).continuous.measurable

/-- **Character of the source quotient Gaussian on a twisted lattice test.** -/
theorem sourceDualQuotientGaussian_integral_cexp {β : ℝ} (hβ : 0 ≤ β)
    (m : coClosed (latticeExactOneComplex (B := B) Cubical.originZero)) :
    ∫ q, Complex.exp (Complex.I *
        ((sourceDualQuotientTestFunctional (latticeToSourceCoClosed Cubical.originZero m) q : ℝ) :
          ℂ)) ∂sourceDualQuotientGaussian (B := B) β hβ =
      Complex.exp (-(((β / 2) * quotientCovarianceQuadratic
        (latticeExactOneComplex (B := B) Cubical.originZero) m : ℝ) : ℂ)) := by
  let x := latticeToSourceCoClosed Cubical.originZero m
  have hchar := sourceDualQuotientGaussian_charFunDual hβ x
  have hL : Measurable (sourceDualQuotientTestFunctional x) :=
    measurable_sourceDualQuotientTestFunctional x
  have hmap : MeasureTheory.charFun
      (Measure.map (sourceDualQuotientTestFunctional x)
        (sourceDualQuotientGaussian (B := B) β hβ)) 1 =
      ∫ q, Complex.exp (Complex.I * ((sourceDualQuotientTestFunctional x q : ℝ) : ℂ))
        ∂sourceDualQuotientGaussian (B := B) β hβ := by
    rw [MeasureTheory.charFun_apply_real]
    rw [MeasureTheory.integral_map hL.aemeasurable (by fun_prop)]
    congr 1
    funext q
    simp [mul_comm]
  rw [← hmap, hchar]
  congr 1
  have hquad : inner ℝ (x : EuclideanSpace ℝ (SourceDualOneCells B))
      ((β • sourceDualAmbientCovariance) (x : EuclideanSpace ℝ (SourceDualOneCells B))) =
      β * quotientCovarianceQuadratic
        (latticeExactOneComplex (B := B) Cubical.originZero) m := by
    rw [LinearMap.smul_apply, sourceDualAmbientCovariance_coClosed_apply, real_inner_smul_right,
      ← quotientCovarianceQuadratic_latticeToSource]
    rfl
  rw [hquad]
  push_cast
  ring

end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
