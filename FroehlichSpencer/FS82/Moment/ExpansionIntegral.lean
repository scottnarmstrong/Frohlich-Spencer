/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.Expansion
public import FroehlichSpencer.FS82.Gaussian.GaugeAveraged
public import FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent
public import FroehlichSpencer.FS82.Poisson.PerAssignment
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# finite expansion integration

Integrate the pointwise Expansion expansion against the real-tilted physical
gauge-averaged Gaussian.

The finite current Fourier representation supplies
the integrability bounds needed for the termwise integral.
-/

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Moment.ExpansionIntegral

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent
open FroehlichSpencer.FS82.Poisson

variable {B : Box 4}

/-- The positive physical frequency attached to one zero-based assignment. -/
def sourceAssignmentFrequency (q : SourcePoissonEdge B → ℕ)
    (e : SourcePoissonEdge B) : ℤ :=
  (positiveMode (q e) : ℤ)

/-- The signed mode carried by one of the three choices in a cosine factor. -/
def sourceAssignmentSignedMode (q : SourcePoissonEdge B → ℕ)
    (s : SourcePoissonEdge B → Option Bool)
    (e : SourcePoissonEdge B) : ℤ :=
  match s e with
  | none => 0
  | some true => sourceAssignmentFrequency q e
  | some false => -sourceAssignmentFrequency q e

/-- The source current whose physical Fourier mode is a signed assignment. -/
noncomputable def sourceAssignmentCurrent (q : SourcePoissonEdge B → ℕ)
    (s : SourcePoissonEdge B → Option Bool) : SourcePoissonEdge B → ℤ :=
  fun e => sourceAssignmentSignedMode q s e

/-- Coefficient of a finite signed choice in the product Fourier expansion. -/
noncomputable def sourceAssignmentFourierCoefficient
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (s : SourcePoissonEdge B → Option Bool) : ℝ :=
  (Finset.univ : Finset (SourcePoissonEdge B)).prod fun e => match s e with
    | none => 1
    | some _ => z (positiveMode (q e)) / 2

/-- The finite cosine product for a fixed positive-mode assignment, in the
physical real-link normalization. -/
noncomputable def sourceAssignmentCosineProduct
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (α : EuclideanSpace ℝ (SourceDualOneCells B)) : ℝ :=
  (Finset.univ : Finset (SourcePoissonEdge B)).prod fun e =>
    1 + z (positiveMode (q e)) *
      Real.cos (2 * Real.pi * (sourceAssignmentFrequency q e : ℝ) * α e)

/--
The finite character sum associated with a fixed source assignment.

Non-co-closed terms contribute zero by the completed-square factor.
-/
noncomputable def sourceAssignmentGaussianMoment
    (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (τ : coClosed (physicalComplex (B := B)))
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ) : ℂ :=
  ∑ s : SourcePoissonEdge B → Option Bool,
    (sourceAssignmentFourierCoefficient q z s : ℂ) *
      physicalGaussianTiltCompletedSquareFactor (B := B) β hβ t τ
        (physicalGaugeCurrent (B := B) (sourceAssignmentCurrent q s))

private noncomputable def sourceAssignmentEdgeFourierTerm
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (α : EuclideanSpace ℝ (SourceDualOneCells B))
    (e : SourcePoissonEdge B) (s : Option Bool) : ℂ :=
  match s with
  | none => 1
  | some true => (z (positiveMode (q e)) / 2 : ℝ) *
      Complex.exp ((2 * Real.pi *
        (sourceAssignmentFrequency q e : ℝ) * α e : ℝ) * Complex.I)
  | some false => (z (positiveMode (q e)) / 2 : ℝ) *
      Complex.exp (-(2 * Real.pi *
        (sourceAssignmentFrequency q e : ℝ) * α e : ℝ) * Complex.I)

private theorem sourceAssignmentEdgeFourierTerm_sum
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (α : EuclideanSpace ℝ (SourceDualOneCells B))
    (e : SourcePoissonEdge B) :
    (1 + z (positiveMode (q e)) *
        Real.cos (2 * Real.pi * (sourceAssignmentFrequency q e : ℝ) * α e) : ℂ) =
      ∑ s : Option Bool, sourceAssignmentEdgeFourierTerm q z α e s := by
  have hcos (x : ℝ) :
      (Real.cos x : ℂ) =
        (Complex.exp ((x : ℂ) * Complex.I) +
          Complex.exp (-(x : ℂ) * Complex.I)) / 2 := by
    rw [Complex.ofReal_cos]
    simp [Complex.cos, mul_comm]
  simp only [Fintype.sum_option, sourceAssignmentEdgeFourierTerm]
  rw [hcos]
  simp only [Fintype.sum_bool]
  push_cast
  ring

/-- Each signed assignment current has the expected physical Fourier mode. -/
theorem sourceAssignmentCurrent_physicalMode
    (q : SourcePoissonEdge B → ℕ)
    (s : SourcePoissonEdge B → Option Bool)
    (e : SourcePoissonEdge B) :
    latticePhysicalMode (B := B)
        (physicalGaugeCurrent (B := B) (sourceAssignmentCurrent q s)) e =
      sourceAssignmentSignedMode q s e := by
  classical
  rw [latticePhysicalMode]
  have happly (j : SourcePoissonEdge B → ℤ) :
      physicalGaugeCurrent (B := B) j e = Gaussian.sourceDualT e * j e := by
    simp [physicalGaugeCurrent]
  rw [happly, sourceAssignmentCurrent]
  rcases Gaussian.sourceDualT_is_pm_one e with he | he <;> rw [he] <;> ring

/-- Pointwise Fourier expansion of the assignment cosine product. -/
theorem sourceAssignmentCosineProduct_eq_physicalTrigPolynomial
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
    (sourceAssignmentCosineProduct q z α : ℂ) =
      physicalRealTrigPolynomial (B := B) Finset.univ
        (fun s => (sourceAssignmentFourierCoefficient q z s : ℂ))
        (fun s => physicalGaugeCurrent (B := B)
          (sourceAssignmentCurrent q s)) α := by
  classical
  let edges := (Finset.univ : Finset (SourcePoissonEdge B))
  have hprod : (∏ e ∈ edges, (1 + z (positiveMode (q e)) *
      Real.cos (2 * Real.pi * (sourceAssignmentFrequency q e : ℝ) * α e) : ℂ)) =
      ∏ e ∈ edges, ∑ d : Option Bool,
        sourceAssignmentEdgeFourierTerm q z α e d := by
    apply Finset.prod_congr rfl
    intro e he
    exact sourceAssignmentEdgeFourierTerm_sum q z α e
  calc
    (sourceAssignmentCosineProduct q z α : ℂ) =
        ∏ e ∈ edges, (1 + z (positiveMode (q e)) *
          Real.cos (2 * Real.pi * (sourceAssignmentFrequency q e : ℝ) * α e) : ℂ) := by
            simp [sourceAssignmentCosineProduct, edges,
              Complex.ofReal_prod, Complex.ofReal_add, Complex.ofReal_mul,
              Complex.ofReal_cos]
    _ = ∏ e ∈ edges, ∑ d : Option Bool,
        sourceAssignmentEdgeFourierTerm q z α e d := hprod
    _ = ∑ σ : SourcePoissonEdge B → Option Bool,
        ∏ e ∈ edges, sourceAssignmentEdgeFourierTerm q z α e (σ e) := by
          simpa [edges] using (Fintype.prod_sum
            (ι := SourcePoissonEdge B) (κ := fun _ => Option Bool)
            (f := fun e d => sourceAssignmentEdgeFourierTerm q z α e d))
    _ = _ := by
      change (∑ σ : SourcePoissonEdge B → Option Bool,
        ∏ e : SourcePoissonEdge B,
          sourceAssignmentEdgeFourierTerm q z α e (σ e)) =
        ∑ σ : SourcePoissonEdge B → Option Bool,
          sourceAssignmentFourierCoefficient q z σ *
            Complex.exp (inner ℝ ((2 * Real.pi) • latticeIntegerModeVector
              (B := B) (physicalGaugeCurrent (B := B)
                (sourceAssignmentCurrent q σ))) α * Complex.I)
      apply Finset.sum_congr rfl
      intro σ hσ
      have hmode (e : SourcePoissonEdge B) :
          latticePhysicalMode (B := B)
              (physicalGaugeCurrent (B := B) (sourceAssignmentCurrent q σ)) e =
            sourceAssignmentSignedMode q σ e :=
        sourceAssignmentCurrent_physicalMode q σ e
      have hphase :
          inner ℝ ((2 * Real.pi) • latticeIntegerModeVector (B := B)
              (physicalGaugeCurrent (B := B) (sourceAssignmentCurrent q σ))) α =
            ∑ e, 2 * Real.pi *
              (sourceAssignmentSignedMode q σ e : ℝ) * α e := by
        rw [PiLp.inner_apply]
        simp only [Real.inner_apply, latticeIntegerModeVector_apply,
          PiLp.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro e he
        rw [hmode e]
      rw [hphase]
      have hphaseExp :
          Complex.exp ((∑ e : SourcePoissonEdge B,
            2 * Real.pi * (sourceAssignmentSignedMode q σ e : ℝ) * α e) *
              Complex.I) =
            ∏ e : SourcePoissonEdge B,
              Complex.exp ((2 * Real.pi *
                (sourceAssignmentSignedMode q σ e : ℝ) * α e) * Complex.I) := by
        rw [show (∑ e : SourcePoissonEdge B,
              2 * Real.pi * (sourceAssignmentSignedMode q σ e : ℝ) * α e) *
                Complex.I =
              ∑ e : SourcePoissonEdge B,
                (2 * Real.pi * (sourceAssignmentSignedMode q σ e : ℝ) *
                  α e) * Complex.I by
                    push_cast
                    rw [Finset.sum_mul]]
        rw [Complex.exp_sum]
      have hExpLink :
          Complex.exp (inner ℝ ((2 * Real.pi) •
              latticeIntegerModeVector (B := B)
                (physicalGaugeCurrent (B := B) (sourceAssignmentCurrent q σ)))
              α * Complex.I) =
            ∏ e : SourcePoissonEdge B,
              Complex.exp ((2 * Real.pi *
                (sourceAssignmentSignedMode q σ e : ℝ) * α e) * Complex.I) := by
        calc
          _ = Complex.exp ((∑ e : SourcePoissonEdge B,
              2 * Real.pi * (sourceAssignmentSignedMode q σ e : ℝ) * α e) *
                Complex.I) := by
                  congr 1
                  exact congrArg (fun r : ℝ => (r : ℂ) * Complex.I) hphase
          _ = _ := hphaseExp
      have hcoeffProd :
          (sourceAssignmentFourierCoefficient q z σ : ℂ) =
            ∏ e : SourcePoissonEdge B,
              (match σ e with
                | none => (1 : ℂ)
                | some _ => (z (positiveMode (q e)) / 2 : ℝ)) := by
        unfold sourceAssignmentFourierCoefficient
        rw [Complex.ofReal_prod]
        apply Finset.prod_congr rfl
        intro e he
        cases σ e <;> simp
      have hterm (e : SourcePoissonEdge B) :
          sourceAssignmentEdgeFourierTerm q z α e (σ e) =
            (match σ e with
              | none => (1 : ℂ)
              | some _ => (z (positiveMode (q e)) / 2 : ℝ)) *
              Complex.exp ((2 * Real.pi *
                (sourceAssignmentSignedMode q σ e : ℝ) * α e) * Complex.I) := by
        cases hs : σ e with
        | none => simp [sourceAssignmentEdgeFourierTerm,
            sourceAssignmentSignedMode, hs]
        | some b =>
            cases b <;>
              simp [sourceAssignmentEdgeFourierTerm,
                sourceAssignmentSignedMode, hs]
      have htermProd :
          (∏ e : SourcePoissonEdge B,
            sourceAssignmentEdgeFourierTerm q z α e (σ e)) =
          sourceAssignmentFourierCoefficient q z σ *
            ∏ e : SourcePoissonEdge B,
              Complex.exp ((2 * Real.pi *
                (sourceAssignmentSignedMode q σ e : ℝ) * α e) * Complex.I) := by
        calc
          _ = ∏ e : SourcePoissonEdge B,
              (match σ e with
                | none => (1 : ℂ)
                | some _ => (z (positiveMode (q e)) / 2 : ℝ)) *
                Complex.exp ((2 * Real.pi *
                  (sourceAssignmentSignedMode q σ e : ℝ) * α e) * Complex.I) := by
                  apply Finset.prod_congr rfl
                  intro e he
                  exact hterm e
          _ = (∏ e : SourcePoissonEdge B,
                (match σ e with
                  | none => (1 : ℂ)
                  | some _ => (z (positiveMode (q e)) / 2 : ℝ))) *
                ∏ e : SourcePoissonEdge B,
                  Complex.exp ((2 * Real.pi *
                    (sourceAssignmentSignedMode q σ e : ℝ) * α e) * Complex.I) :=
                  Finset.prod_mul_distrib
          _ = _ := by rw [← hcoeffProd]
      exact htermProd.trans (congrArg (fun w : ℂ =>
        (sourceAssignmentFourierCoefficient q z σ : ℂ) * w) hphaseExp.symm)

/-- The positive natural assignment, viewed as the integer frequency used by
the Expansion expansion. -/
noncomputable def sourceAssignmentIntegerFrequency
    (q : SourcePoissonEdge B → ℕ) : Link B → ℤ :=
  fun e => (positiveMode (q e) : ℤ)

/-- The activity on integer frequencies used by Expansion. -/
noncomputable def sourceAssignmentIntegerActivity (z : ℕ → ℝ) : ℤ → ℝ :=
  fun n => z n.natAbs

/-- The assignment cosine product is exactly Expansion's initial fixed-frequency
product after inserting the source's positive mode `q + 1`. -/
theorem sourceAssignmentCosineProduct_eq_sourceCurrentProduct
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sourceAssignmentCosineProduct q z α =
      sourceCurrentProduct (sourceAssignmentIntegerFrequency q)
        (sourceAssignmentIntegerActivity z)
        (fun e => 2 * Real.pi * α e) := by
  classical
  unfold sourceAssignmentCosineProduct sourceCurrentProduct
    sourceAssignmentIntegerFrequency sourceAssignmentIntegerActivity
    sourceAssignmentFrequency
  apply Finset.prod_congr rfl
  intro e he
  have hnatAbs : (abs (positiveMode (q e) : ℤ)).natAbs =
      positiveMode (q e) := by simp
  rw [hnatAbs]
  have harg :
      2 * Real.pi * ((positiveMode (q e) : ℤ) : ℝ) * α e =
        (2 * Real.pi * α e) * ((positiveMode (q e) : ℤ) : ℝ) := by ring
  rw [harg]

/--
evaluates the physical fixed-assignment integral as a finite signed
Fourier sum.

The completed-square factor automatically removes every
non-co-closed mode.
-/
theorem sourceAssignmentGaussianMoment_eq_integral
    (β t : ℝ) (hβ : 0 ≤ β)
    (τ : coClosed (physicalComplex (B := B)))
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ) :
    sourceAssignmentGaussianMoment β hβ t τ q z =
      ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α : ℝ) : ℂ) *
          (sourceAssignmentCosineProduct q z α : ℂ)
        ∂gaugeAveragedRealGaussian (B := B) β hβ := by
  classical
  have hpoint (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        (sourceAssignmentCosineProduct q z α : ℂ) =
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        physicalRealTrigPolynomial (B := B) Finset.univ
          (fun s => (sourceAssignmentFourierCoefficient q z s : ℂ))
          (fun s => physicalGaugeCurrent (B := B)
            (sourceAssignmentCurrent q s)) α := by
    rw [sourceAssignmentCosineProduct_eq_physicalTrigPolynomial]
  have hintegral :
      (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α : ℝ) : ℂ) *
          (sourceAssignmentCosineProduct q z α : ℂ)
        ∂gaugeAveragedRealGaussian (B := B) β hβ) =
      ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α : ℝ) : ℂ) *
          physicalRealTrigPolynomial (B := B) Finset.univ
            (fun s => (sourceAssignmentFourierCoefficient q z s : ℂ))
            (fun s => physicalGaugeCurrent (B := B)
              (sourceAssignmentCurrent q s)) α
        ∂gaugeAveragedRealGaussian (B := B) β hβ := by
    apply integral_congr_ae
    filter_upwards [] with α
    exact hpoint α
  rw [sourceAssignmentGaussianMoment, hintegral]
  simpa [physicalRealTrigPolynomial] using
    (gaugeAveragedRealGaussian_tiltedTrigPolynomial_integral_completedSquare
      (B := B) β hβ t τ Finset.univ
      (fun s => (sourceAssignmentFourierCoefficient q z s : ℂ))
      (fun s => physicalGaugeCurrent (B := B)
        (sourceAssignmentCurrent q s))).symm

private theorem gaugeAveragedRealGaussian_realExp_integrable
    (β t : ℝ) (hβ : 0 ≤ β)
    (τ : coClosed (physicalComplex (B := B))) :
    Integrable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
      Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α))
      (gaugeAveragedRealGaussian (B := B) β hβ) := by
  let C := physicalComplex (B := B)
  let W := coClosed C
  let μ := coClosedGaussian (B := B) β hβ
  let ν := vertexTorusHaar (B := B)
  let u : W := t • τ
  let L : StrongDual ℝ W := InnerProductSpace.toDualMap ℝ W u
  haveI : ProbabilityTheory.IsGaussian μ := coClosedGaussian_is_gaussian β hβ
  have hL : Measurable L := L.continuous.measurable
  have hpush : Measure.map L μ = ProbabilityTheory.gaussianReal
      (∫ x, L x ∂μ) (ProbabilityTheory.variance L μ).toNNReal :=
    ProbabilityTheory.IsGaussian.map_eq_gaussianReal L
  have hexp : Integrable (fun y : ℝ => Real.exp y) (Measure.map L μ) := by
    rw [hpush]
    simpa using ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := ∫ x, L x ∂μ) (v := (ProbabilityTheory.variance L μ).toNNReal) 1
  have hbase : Integrable (fun x : W => Real.exp (inner ℝ u x)) μ := by
    have hcomp := (MeasureTheory.integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun y : ℝ => Real.exp y)
        (Measure.map L μ)) hL.aemeasurable).mp hexp
    have hLx (x : W) : L x = inner ℝ u x := by
      simp [L, InnerProductSpace.toDualMap_apply_apply (𝕜 := ℝ)]
    convert hcomp using 1
    ext x
    simp [hLx]
  let φ : W × VertexTorus (B := B) → EuclideanSpace ℝ
      (SourceDualOneCells B) := fun p => physicalRealField (B := B)
        (p.1 : EuclideanSpace ℝ (SourceDualOneCells B)) p.2
  let F : EuclideanSpace ℝ (SourceDualOneCells B) → ℝ := fun α =>
    Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
      (SourceDualOneCells B)) α)
  have hpair : Measurable (fun p : W × VertexTorus (B := B) =>
      ((p.1 : EuclideanSpace ℝ (SourceDualOneCells B)), p.2)) := by
    fun_prop
  have hφ : Measurable φ := physicalRealField_measurable.comp hpair
  have hF : Measurable F := by fun_prop
  have hν : IsProbabilityMeasure ν := vertexTorusHaar_is_probability
  have hprod : Integrable (fun p : W × VertexTorus (B := B) =>
      Real.exp (inner ℝ u p.1)) (μ.prod ν) := hbase.comp_fst ν
  have hpoint (p : W × VertexTorus (B := B)) :
      Real.exp (inner ℝ u p.1) = F (φ p) := by
    have hp := physicalRealField_pairing_coClosed (B := B)
      (p.1 : EuclideanSpace ℝ (SourceDualOneCells B)) p.2 u
    calc
      Real.exp (inner ℝ u p.1) =
          Real.exp (inner ℝ (u : EuclideanSpace ℝ
            (SourceDualOneCells B))
            (p.1 : EuclideanSpace ℝ (SourceDualOneCells B))) := by rfl
      _ = Real.exp (inner ℝ (u : EuclideanSpace ℝ
            (SourceDualOneCells B)) (φ p)) := by
              congr 1
              exact hp.symm
      _ = F (φ p) := by
              simp [F, u, real_inner_smul_left]
  have hpull : Integrable (fun p : W × VertexTorus (B := B) =>
      F (φ p)) (μ.prod ν) := hprod.congr (ae_of_all _ hpoint)
  change Integrable F (Measure.map φ (μ.prod ν))
  exact (MeasureTheory.integrable_map_measure
    hF.aestronglyMeasurable hφ.aemeasurable).mpr hpull

private theorem integrable_tilt_mul_bounded
    (β t : ℝ) (hβ : 0 ≤ β)
    (τ : coClosed (physicalComplex (B := B)))
    {f : EuclideanSpace ℝ (SourceDualOneCells B) → ℝ} (C₀ : ℝ)
    (hf : ∀ α, ‖f α‖ ≤ C₀)
    (hmf : Measurable f) :
    Integrable (fun α =>
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) * (f α : ℂ))
      (gaugeAveragedRealGaussian (B := B) β hβ) := by
  have hR := gaugeAveragedRealGaussian_realExp_integrable
    (B := B) β t hβ τ
  have hdomR : Integrable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
      C₀ * Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α))
      (gaugeAveragedRealGaussian (B := B) β hβ) := by
    simpa [mul_comm] using hR.const_mul C₀
  have hm : AEStronglyMeasurable
      (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
        Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α : ℝ) : ℂ) * (f α : ℂ))
      (gaugeAveragedRealGaussian (B := B) β hβ) := by
    fun_prop
  apply Integrable.mono' hdomR hm
  filter_upwards [] with α
  calc
    ‖Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) * (f α : ℂ)‖ =
      Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α) * ‖(f α : ℂ)‖ := by
          rw [norm_mul, Complex.norm_exp]
          simp [Complex.norm_real]
    _ ≤ Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α) * C₀ :=
      mul_le_mul_of_nonneg_left (by simpa using hf α) (Real.exp_pos _).le
    _ = C₀ * Real.exp (t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α) := by ring

private theorem abs_cosineProduct_le {I : Type*} [DecidableEq I]
    (s : Finset I) (a θ : I → ℝ) :
    |∏ i ∈ s, (1 + a i * Real.cos (θ i))| ≤
      ∏ i ∈ s, (1 + |a i|) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      have hcos : |Real.cos (θ i)| ≤ 1 := by
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have hfactor : |1 + a i * Real.cos (θ i)| ≤ 1 + |a i| := by
        calc
          |1 + a i * Real.cos (θ i)| ≤
              |1| + |a i * Real.cos (θ i)| := abs_add_le _ _
          _ = 1 + |a i| * |Real.cos (θ i)| := by rw [abs_mul]; simp
          _ ≤ 1 + |a i| := by nlinarith [abs_nonneg (a i)]
      calc
        |(1 + a i * Real.cos (θ i)) * ∏ j ∈ s,
            (1 + a j * Real.cos (θ j))| =
          |1 + a i * Real.cos (θ i)| *
            |∏ j ∈ s, (1 + a j * Real.cos (θ j))| := abs_mul _ _
        _ ≤ (1 + |a i|) * ∏ j ∈ s, (1 + |a j|) :=
          mul_le_mul hfactor ih (abs_nonneg _) (by positivity)

private theorem currentStateProduct_abs_le
    (q : Link B → ℤ) (z : ℤ → ℝ) (state : CurrentState B)
    (φ : Link B → ℝ) :
    ‖currentStateProduct q z φ state‖ ≤
      ∏ t ∈ state, (1 + |lineageCoefficient q z t|) := by
  classical
  unfold currentStateProduct currentFactor
  rw [Real.norm_eq_abs]
  exact abs_cosineProduct_le state (fun t => lineageCoefficient q z t)
    (fun t => currentPhase φ (lineageCurrent q t))

private theorem currentStateProduct_measurable
    (q : Link B → ℤ) (z : ℤ → ℝ) (state : CurrentState B) :
    Measurable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
      currentStateProduct q z
        (fun e => 2 * Real.pi * α e) state) := by
  unfold currentStateProduct currentFactor currentPhase
  fun_prop

private theorem sourceCurrentProduct_measurable
    (q : Link B → ℤ) (z : ℤ → ℝ) :
    Measurable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
      sourceCurrentProduct q z (fun e => 2 * Real.pi * α e)) := by
  unfold sourceCurrentProduct
  fun_prop

/--
Integrating the fixed-assignment Expansion identity gives the finite sum of
the corresponding terminal-branch integrals.

The angle is the physical
`2π α` normalization used by lattice characters.
-/
theorem fixedFrequencyExpansion_integral
    (β t : ℝ) (hβ : 0 ≤ β)
    (τ : coClosed (physicalComplex (B := B)))
    (q : Link B → ℤ) (z : ℤ → ℝ)
    (terms : List (CurrentExpansionTerm B))
    (hTerms : IsFixedFrequencyCurrentExpansion q z terms) :
    ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
      Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
        (SourceDualOneCells B)) α : ℝ) : ℂ) *
        (sourceCurrentProduct q z (fun e => 2 * Real.pi * α e) : ℂ)
        ∂gaugeAveragedRealGaussian (B := B) β hβ =
      (terms.map fun b => b.weight *
        (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
          Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
            (SourceDualOneCells B)) α : ℝ) : ℂ) *
            (currentStateProduct q z (fun e => 2 * Real.pi * α e)
              b.state : ℂ)
          ∂gaugeAveragedRealGaussian (B := B) β hβ)).sum := by
  classical
  let ν := gaugeAveragedRealGaussian (B := B) β hβ
  let tilt : EuclideanSpace ℝ (SourceDualOneCells B) → ℂ := fun α =>
    Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
      (SourceDualOneCells B)) α : ℝ) : ℂ)
  have hsourceBound : ∀ α : EuclideanSpace ℝ (SourceDualOneCells B),
      ‖sourceCurrentProduct q z (fun e => 2 * Real.pi * α e)‖ ≤
        ∏ e : Link B, (1 + |z (abs (q e))|) := by
    intro α
    rw [sourceCurrentProduct, Real.norm_eq_abs]
    exact abs_cosineProduct_le Finset.univ
      (fun e => z (abs (q e)))
      (fun e => (2 * Real.pi * α e) * (q e : ℝ))
  have hsourceInt := integrable_tilt_mul_bounded (B := B) β t hβ τ
    (∏ e : Link B, (1 + |z (abs (q e))|))
    hsourceBound (sourceCurrentProduct_measurable (B := B) q z)
  have hbranchInt (b : CurrentExpansionTerm B) :
      Integrable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
        tilt α *
          (currentStateProduct q z (fun e => 2 * Real.pi * α e)
            b.state : ℂ)) ν := by
    apply integrable_tilt_mul_bounded (B := B) β t hβ τ
      (∏ l ∈ b.state, (1 + |lineageCoefficient q z l|))
    · intro α
      have h := currentStateProduct_abs_le q z b.state
        (fun e => 2 * Real.pi * α e)
      simpa using h
    · exact currentStateProduct_measurable q z b.state
  have htailInt : ∀ xs : List (CurrentExpansionTerm B),
      Integrable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
        tilt α * (currentExpansionSum q z
          (fun e => 2 * Real.pi * α e) xs : ℂ)) ν := by
    intro xs
    induction xs with
    | nil => simp [currentExpansionSum, tilt]
    | cons b xs ih =>
        have hb := hbranchInt b
        have hb' : Integrable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
            tilt α * ((b.weight : ℂ) *
              (currentStateProduct q z (fun e => 2 * Real.pi * α e)
                b.state : ℂ))) ν := by
          have hmul := hb.const_mul (b.weight : ℂ)
          apply hmul.congr (ae_of_all _ fun α => ?_)
          change (b.weight : ℂ) *
              (tilt α *
                (currentStateProduct q z (fun e => 2 * Real.pi * α e)
                  b.state : ℂ)) = _
          ring
        have hadd := hb'.add ih
        have hrewrite : (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
            tilt α * (currentExpansionSum q z
              (fun e => 2 * Real.pi * α e) (b :: xs) : ℂ)) =
          (fun α => tilt α * ((b.weight : ℂ) *
              (currentStateProduct q z (fun e => 2 * Real.pi * α e)
                b.state : ℂ))) +
            (fun α => tilt α * (currentExpansionSum q z
              (fun e => 2 * Real.pi * α e) xs : ℂ)) := by
          funext α
          simp [currentExpansionSum, List.map_cons, List.sum_cons]
          ring
        exact hadd.congr (ae_of_all _ fun α => by
          have h := congrFun hrewrite α
          simpa using h.symm)
  have hbranchSum : ∀ xs : List (CurrentExpansionTerm B),
      ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        tilt α * (currentExpansionSum q z
          (fun e => 2 * Real.pi * α e) xs : ℂ) ∂ν =
        (xs.map fun b => b.weight *
          (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
            tilt α * (currentStateProduct q z
              (fun e => 2 * Real.pi * α e) b.state : ℂ) ∂ν)).sum := by
    intro xs
    induction xs with
    | nil => simp [currentExpansionSum]
    | cons b xs ih =>
        have hb := hbranchInt b
        have htail := htailInt xs
        have hb' : Integrable (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
            tilt α * ((b.weight : ℂ) *
              (currentStateProduct q z (fun e => 2 * Real.pi * α e)
                b.state : ℂ))) ν := by
          have hmul := hb.const_mul (b.weight : ℂ)
          apply hmul.congr (ae_of_all _ fun α => ?_)
          change (b.weight : ℂ) *
              (tilt α *
                (currentStateProduct q z (fun e => 2 * Real.pi * α e)
                  b.state : ℂ)) = _
          ring
        have hrewrite : (fun α : EuclideanSpace ℝ (SourceDualOneCells B) =>
            tilt α * (currentExpansionSum q z
              (fun e => 2 * Real.pi * α e) (b :: xs) : ℂ)) =
          (fun α => tilt α * ((b.weight : ℂ) *
              (currentStateProduct q z (fun e => 2 * Real.pi * α e)
                b.state : ℂ))) +
            (fun α => tilt α * (currentExpansionSum q z
              (fun e => 2 * Real.pi * α e) xs : ℂ)) := by
          funext α
          simp [currentExpansionSum, List.map_cons, List.sum_cons]
          ring
        rw [show ∫ α, tilt α *
            (currentExpansionSum q z (fun e => 2 * Real.pi * α e)
              (b :: xs) : ℂ) ∂ν =
            ∫ α, (tilt α * ((b.weight : ℂ) *
                (currentStateProduct q z (fun e => 2 * Real.pi * α e)
                  b.state : ℂ))) +
              (tilt α * (currentExpansionSum q z
                (fun e => 2 * Real.pi * α e) xs : ℂ)) ∂ν from by
                apply integral_congr_ae
                filter_upwards [] with α
                exact congrFun hrewrite α]
        rw [integral_add hb' htail]
        have hfirst :
            (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
                tilt α * ((b.weight : ℂ) *
                  (currentStateProduct q z (fun e => 2 * Real.pi * α e)
                    b.state : ℂ)) ∂ν) =
              (b.weight : ℂ) *
                ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
                  tilt α * (currentStateProduct q z
                    (fun e => 2 * Real.pi * α e) b.state : ℂ) ∂ν := by
          calc
            _ = ∫ α, (b.weight : ℂ) *
                (tilt α * (currentStateProduct q z
                  (fun e => 2 * Real.pi * α e) b.state : ℂ)) ∂ν := by
                  apply integral_congr_ae
                  filter_upwards [] with α
                  ring
            _ = _ := integral_const_mul _ _
        rw [hfirst, ih]
        simp only [List.map_cons, List.sum_cons]
  have hpoint (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
      sourceCurrentProduct q z (fun e => 2 * Real.pi * α e) =
        currentExpansionSum q z (fun e => 2 * Real.pi * α e) terms := by
    obtain ⟨_, _, _, _, _, hexp, _, _⟩ := hTerms
    exact hexp (fun e => 2 * Real.pi * α e)
  calc
    _ = ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        tilt α * (currentExpansionSum q z
          (fun e => 2 * Real.pi * α e) terms : ℂ) ∂ν := by
          apply integral_congr_ae
          filter_upwards [] with α
          simp [tilt, hpoint α]
    _ = _ := hbranchSum terms

/--
The assignment integral is the finite Expansion terminal branch sum.

The
frequency and activity maps account for the source convention `q ↦ q + 1`.
-/
theorem sourceAssignmentGaussianMoment_eq_branchSum
    (β t : ℝ) (hβ : 0 ≤ β)
    (τ : coClosed (physicalComplex (B := B)))
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (terms : List (CurrentExpansionTerm B))
    (hTerms : IsFixedFrequencyCurrentExpansion
      (sourceAssignmentIntegerFrequency q)
      (sourceAssignmentIntegerActivity z) terms) :
    sourceAssignmentGaussianMoment β hβ t τ q z =
      (terms.map fun b => b.weight *
        (∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
          Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
            (SourceDualOneCells B)) α : ℝ) : ℂ) *
            (currentStateProduct (sourceAssignmentIntegerFrequency q)
              (sourceAssignmentIntegerActivity z)
              (fun e => 2 * Real.pi * α e) b.state : ℂ)
          ∂gaugeAveragedRealGaussian (B := B) β hβ)).sum := by
  classical
  rw [sourceAssignmentGaussianMoment_eq_integral]
  calc
    _ = ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
        Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ
          (SourceDualOneCells B)) α : ℝ) : ℂ) *
          (sourceCurrentProduct (sourceAssignmentIntegerFrequency q)
            (sourceAssignmentIntegerActivity z)
            (fun e => 2 * Real.pi * α e) : ℂ)
        ∂gaugeAveragedRealGaussian (B := B) β hβ := by
          apply integral_congr_ae
          filter_upwards [] with α
          rw [← sourceAssignmentCosineProduct_eq_sourceCurrentProduct]
    _ = _ := fixedFrequencyExpansion_integral β t hβ τ
      (sourceAssignmentIntegerFrequency q)
      (sourceAssignmentIntegerActivity z) terms hTerms

end FroehlichSpencer.FS82.Moment.ExpansionIntegral

end
