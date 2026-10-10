/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent
public import FroehlichSpencer.FS82.Moment.QuotientGaussian
public import FroehlichSpencer.FS82.Poisson.SourceModel

@[expose] public section

open scoped BigOperators InnerProductSpace
open Matrix

namespace FroehlichSpencer.FS82.Moment.GaugeCharacter

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceCoercivity
open FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent
open FroehlichSpencer.FS82.Poisson

variable {B : Box 4}

noncomputable def sourceRealLinkVector (j : IntegerCurrent B) :
    EuclideanSpace ℝ (SourceDualOneCells B) :=
  finsuppToEuclidean (compressDualSubtype sourceDualOneEmbedding
    (realCurrent j))

theorem sourceRealLinkVector_apply (j : IntegerCurrent B)
    (e : SourceDualOneCells B) :
    sourceRealLinkVector (B := B) j e = (j e : ℝ) := by
  unfold sourceRealLinkVector
  rw [finsuppToEuclidean_apply, compressDualSubtype_apply,
    Currents.realCurrent]
  change Finsupp.embDomain sourceDualOneEmbedding
      (Finsupp.mapRange (fun n : ℤ => (n : ℝ)) (by simp) j)
      (sourceDualOneEmbedding e) = _
  rw [Finsupp.embDomain_apply_self]
  simp

noncomputable def sourceGaugeW (j : SourcePoissonEdge B → ℤ)
    (hj : RootedTreeGauge.CoClosed (sourceRootedTree B) j) :
    Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) :=
  sourcePhysicalCurrentCoClosed Cubical.originZero
    (physicalGaugeCurrent (B := B) j)
    (physicalGaugeCurrent_divergence_zero (B := B) j hj)

theorem sourceGaugeW_value (j : SourcePoissonEdge B → ℤ)
    (hj : RootedTreeGauge.CoClosed (sourceRootedTree B) j) :
    (sourceGaugeW (B := B) j hj : EuclideanSpace ℝ (SourceDualOneCells B)) =
      (2 * Real.pi) • gaugeRealVector (B := B) j := by
  ext e
  simp only [sourceGaugeW, sourcePhysicalCurrentCoClosed,
    sourceDualTLinear_apply]
  have hraw : sourcePhysicalCurrentVector
      (physicalGaugeCurrent (B := B) j) e =
      (2 * Real.pi) *
        ((WithLp.toLp 2 (fun e : SourceDualOneCells B =>
          ((physicalGaugeCurrent (B := B) j e : ℤ) : ℝ))) e) := by
    rw [show sourcePhysicalCurrentVector (physicalGaugeCurrent (B := B) j) =
        (2 * Real.pi) • sourceRealLinkVector (B := B)
          (physicalGaugeCurrent (B := B) j) by
          ext f
          simp [sourcePhysicalCurrentVector, sourceRealLinkVector,
            Currents.physicalCurrent_eq_scaled_realCurrent]]
    simp [sourceRealLinkVector_apply]
  have hsign :
      sourceDualTLinear (WithLp.toLp 2 (fun e : SourceDualOneCells B =>
          ((physicalGaugeCurrent (B := B) j e : ℤ) : ℝ))) =
        gaugeRealVector (B := B) j := by
    rw [physicalGaugeCurrentRealVector_eq_T (B := B) j]
    exact sourceDualTLinear_apply_apply (gaugeRealVector (B := B) j)
  have hsignE := congrArg (fun z : EuclideanSpace ℝ (SourceDualOneCells B) => z e) hsign
  have hsignVal : dualCellOrientationSign e.1 *
      ((WithLp.toLp 2 (fun e : SourceDualOneCells B =>
        ((physicalGaugeCurrent (B := B) j e : ℤ) : ℝ))) e) = (j e : ℝ) := by
    simpa [sourceDualTLinear_apply, gaugeRealVector] using hsignE
  rw [hraw]
  change dualCellOrientationSign e.1 *
      ((2 * Real.pi) *
        ((WithLp.toLp 2 (fun e : SourceDualOneCells B =>
          ((physicalGaugeCurrent (B := B) j e : ℤ) : ℝ))) e)) =
      (2 * Real.pi) * (j e : ℝ)
  calc
    _ = (2 * Real.pi) *
        (dualCellOrientationSign e.1 *
          ((WithLp.toLp 2 (fun e : SourceDualOneCells B =>
            ((physicalGaugeCurrent (B := B) j e : ℤ) : ℝ))) e)) := by ring
    _ = (2 * Real.pi) * (j e : ℝ) := by rw [hsignVal]


noncomputable def sourceGaugeUnitW (j : SourcePoissonEdge B → ℤ)
    (hj : RootedTreeGauge.CoClosed (sourceRootedTree B) j) :
    Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero) :=
  ((2 * Real.pi)⁻¹) • sourceGaugeW (B := B) j hj

theorem sourceGaugeUnitW_value (j : SourcePoissonEdge B → ℤ)
    (hj : RootedTreeGauge.CoClosed (sourceRootedTree B) j) :
    (sourceGaugeUnitW (B := B) j hj : EuclideanSpace ℝ (SourceDualOneCells B)) =
      gaugeRealVector (B := B) j := by
  change ((2 * Real.pi)⁻¹) •
      (sourceGaugeW (B := B) j hj : EuclideanSpace ℝ (SourceDualOneCells B)) = _
  rw [sourceGaugeW_value]
  ext e
  simp [gaugeRealVector, PiLp.smul_apply, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

theorem sourceGaugeW_eq_scale_unit (j : SourcePoissonEdge B → ℤ)
    (hj : RootedTreeGauge.CoClosed (sourceRootedTree B) j) :
    sourceGaugeW (B := B) j hj =
      (2 * Real.pi) • sourceGaugeUnitW (B := B) j hj := by
  apply Subtype.ext
  change (sourceGaugeW (B := B) j hj : EuclideanSpace ℝ (SourceDualOneCells B)) =
      (2 * Real.pi) •
        (sourceGaugeUnitW (B := B) j hj : EuclideanSpace ℝ (SourceDualOneCells B))
  rw [sourceGaugeW_value, sourceGaugeUnitW_value]

/-- The physical VΛ inverse pairing agrees with the gauge-fixed chord inverse
for every rooted-tree circulation. -/
theorem sourceGaugeVΛ_pairing_eq_chordInverse
    (j : SourcePoissonEdge B → ℤ)
    (hj : RootedTreeGauge.CoClosed (sourceRootedTree B) j) :
    inner ℝ (sourceGaugeUnitW (B := B) j hj : EuclideanSpace ℝ
        (SourceDualOneCells B))
      (latticeVΛ (B := B) Cubical.originZero
        (sourceGaugeUnitW (B := B) j hj) : EuclideanSpace ℝ
          (SourceDualOneCells B)) =
    dotProduct ((sourceRootedTree B).restrictChord (fun e => (j e : ℝ)))
      ((reducedChordMatrix (sourceRootedTree B)
        (sourceFinitePoissonModel (B := B) Cubical.originZero))⁻¹ *ᵥ
        (sourceRootedTree B).restrictChord (fun e => (j e : ℝ))) := by
  classical
  let T := sourceRootedTree B
  let M := sourceFinitePoissonModel (B := B) Cubical.originZero
  let J : T.Chord → ℝ := T.restrictChord (fun e => (j e : ℝ))
  let u : SourceDualOneCells B → ℝ := fun e =>
    (latticeVΛ (B := B) Cubical.originZero (sourceGaugeUnitW (B := B) j hj) :
      EuclideanSpace ℝ (SourceDualOneCells B)) e
  have hjR : RootedTreeGauge.CoClosed T (fun e => (j e : ℝ)) := by
    intro v hv
    have h := hj v hv
    have h' := congrArg (fun n : ℤ => (n : ℝ)) h
    simpa [RootedTreeGauge.CoClosed, RootedTreeGauge.divergence,
      map_sum, Int.cast_ite] using h'
  have hsolve : M.K.mulVec u = fun e => (j e : ℝ) := by
    change (sourcePoissonMatrix (B := B) Cubical.originZero).mulVec u = _
    calc
      (sourcePoissonMatrix (B := B) Cubical.originZero).mulVec u =
          (latticeStencilOperator (B := B) Cubical.originZero
            (WithLp.toLp 2 u)).ofLp :=
        sourcePoissonMatrix_mulVec (B := B) Cubical.originZero u
      _ = fun e => (j e : ℝ) := by
        have hst := latticeVΛ_inverse_stencil (B := B) Cubical.originZero
          (sourceGaugeUnitW (B := B) j hj)
        simpa [u, sourceGaugeUnitW_value, gaugeRealVector] using
          congrArg (fun x : EuclideanSpace ℝ (SourceDualOneCells B) => x.ofLp) hst
  have hvar := finiteModel_variational_identity_of_solution
    T M hjR hjR u hsolve
  have hinner : inner ℝ
      (sourceGaugeUnitW (B := B) j hj : EuclideanSpace ℝ (SourceDualOneCells B))
      (latticeVΛ (B := B) Cubical.originZero (sourceGaugeUnitW (B := B) j hj) :
        EuclideanSpace ℝ (SourceDualOneCells B)) =
      dotProduct (fun e => (j e : ℝ)) u := by
    rw [sourceGaugeUnitW_value, PiLp.inner_apply]
    simp only [gaugeRealVector, u, WithLp.ofLp_toLp]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro e he
    simp only [Real.inner_apply]
  calc
    _ = dotProduct (fun e => (j e : ℝ)) u := hinner
    _ = dotProduct ((sourceRootedTree B).restrictChord (fun e => (j e : ℝ)))
          ((reducedChordMatrix (sourceRootedTree B)
            (sourceFinitePoissonModel (B := B) Cubical.originZero))⁻¹ *ᵥ
            (sourceRootedTree B).restrictChord (fun e => (j e : ℝ))) := by
          simpa [T, M, J, u] using hvar


end FroehlichSpencer.FS82.Moment.GaugeCharacter

end
