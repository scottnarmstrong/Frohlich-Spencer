module

public import FroehlichSpencer.FS82.SurfaceInfiniteProof.FiniteLawBridge
public import FroehlichSpencer.FS82.SourceInterface.CarrierIdentities
public import FroehlichSpencer.FS82.SourceInterface.GaugeCurrentEquivalence
public import FroehlichSpencer.FS82.CovarianceTransport.QuotientChord
public import FroehlichSpencer.FS82.CovarianceTransport.ChordEnergy
public import FroehlichSpencer.FS82.Infinite.LimitStateLaw
public import Mathlib.Tactic
@[expose] public section

open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Surface.IntegerGaugeTransport
open FroehlichSpencer.FS82.Surface.GaugeCurrentEquivalence
open FroehlichSpencer.FS82.SourceCovarianceBridge
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.SourceTreeChart
open FroehlichSpencer.FS82.Gaussian.TreeGaugeQuotient
open FroehlichSpencer.FS82.Poisson

namespace FroehlichSpencer.FS82.SurfaceInfinite


theorem sourceCurrentEquiv_apply_mk (R : RectBox4) (α : IntegerDualField R) :
    (sourceCurrentEquiv R (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)).1 =
      integerLatticeCurl R α := by
  exact (Classical.choose_spec (existsUnique_sourceGaugeClass_closedCurrentEquiv R).exists) α

theorem chartCurrent_cast (R : RectBox4) (α : IntegerDualField R)
    (d : DualPlaquettes R) :
    (sourceIntegerCellSign (dualCellEmbeddingC1 R d.1) : ℝ) *
      ((sourceCurrentEquiv R
        (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)).1
        (dualCellEmbeddingC1 R d.1) : ℝ) =
      (integerChordCurvature
        (quotientClassToChord R
          ((sourceQuotientToIntegerDualModel R)
            (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)))
        ((plaquettesEquivSource R) d) : ℝ) := by
  let c := dualCellEmbeddingC1 R d.1
  let f := (plaquettesEquivSource R) d
  have hcell : c = Cubical.dualCellEmbedding (B := R.side) R.origin f.1 := by
    dsimp [c, f, plaquettesEquivSource, IntegerGaugeTransport.plaquettesEquivSource]
    rw [← c1Cell_bridge R]
    rfl
  have hcurlcast (α' : IntegerDualField R) :
      ((integerLatticeCurl R α' c : ℤ) : ℝ) =
        latticeCellOrientationSign c *
          sourceDualD₁ (sourceCurlInput R α') f := by
    have hcurl := congrArg (fun q : Cubical.RealLatticeChain 4 => q c)
      (literalCurl_cast_eq_sourceCurl R α')
    change ((integerLatticeCurl R α' c : ℤ) : ℝ) = _ at hcurl
    rw [latticeOrientationSignTwist_apply, hcell,
      sourcePhysicalDualZeroExtension_apply_embedding] at hcurl
    have hD : sourceDualTwoToChain
        (sourceDualD₁ (sourceCurlInput R α')) f.1 =
        sourceDualD₁ (sourceCurlInput R α') f := by
      change embedDualSubtype sourceDualTwoEmbedding
        (Gaussian.euclideanToFinsupp (sourceDualD₁ (sourceCurlInput R α')))
        (sourceDualTwoEmbedding f) = _
      rw [embedDualSubtype_apply_at_image]
      simp [Gaussian.euclideanToFinsupp]
    rw [hD] at hcurl
    rw [← hcell] at hcurl
    exact hcurl
  have hscale (x : IntegerDualField R) :
      (latticeCellOrientationSign c) *
        (↑(integerLatticeCurl R x c) : ℝ) =
        sourceDualD₁ (sourceCurlInput R x) f := by
    have h := hcurlcast x
    rw [h]
    have hs := latticeCellOrientationSign_sq c
    calc
      latticeCellOrientationSign c *
          (latticeCellOrientationSign c * sourceDualD₁ (sourceCurlInput R x) f) =
          (latticeCellOrientationSign c * latticeCellOrientationSign c) *
            sourceDualD₁ (sourceCurlInput R x) f := by ring
      _ = sourceDualD₁ (sourceCurlInput R x) f := by
        rw [← pow_two, hs]
        ring
  let n := quotientClassToChord R
      ((sourceQuotientToIntegerDualModel R)
        (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α))
  let T := sourceRootedTree R.side
  have hext : T.extendChord n = sourceRootNormalize R α := by
    have h := T.extend_restrictChord (rootNormalize_treeGauge R α)
    change T.extendChord (T.restrictChord (rootNormalizeSource R α)) =
      rootNormalizeSource R α
    exact h
  have hvec : sourceChordField R n = literalFieldRealVector R (rootNormalize R α) := by
    ext e
    change ((T.extendChord n e : ℤ) : ℝ) = _
    rw [hext]
    change ((rootNormalizeSource R α
      (linksEquivSource R ((linksEquivSource R).symm e)) : ℤ) : ℝ) = _
    simp [literalFieldRealVector, sourceFieldOfLiteral, castIntegerFinsupp,
      Gaussian.finsuppToEuclidean, rootNormalize, IntegerGaugeTransport.linksEquivSource]
  have hchartField :
      sourceFunctionToEuclidean (extendChordsLinear T
        (fun e => (n e : ℝ))) = sourceChordField R n := by
    ext e
    change T.extendChord (fun q => (n q : ℝ)) e =
      ((T.extendChord n e : ℤ) : ℝ)
    by_cases ht : e ∈ Set.range T.treeEdge <;> simp [RootedTreeGauge.extendChord, ht]
  have hsource : sourceDualTLinear
      (sourceFunctionToEuclidean (extendChordsLinear T
        (fun e => (n e : ℝ)))) = sourceCurlInput R (rootNormalize R α) := by
    rw [hchartField, hvec]
    rfl
  have hcurv :
      (integerChordCurvature n f : ℝ) =
        sourceDualD₁ (sourceCurlInput R (rootNormalize R α)) f := by
    rw [integerChordCurvature_cast_chartCurl]
    rw [sourceTreeChartPhysicalCurl_eq_quotientCurvature]
    rw [physicalCurlClassCurvatureAt_mk]
    change sourceDualD₁ (sourceDualTLinear
      (sourceFunctionToEuclidean (extendChordsLinear T (fun e => (n e : ℝ))))) f = _
    rw [hsource]
  have hnormcurl : integerLatticeCurl R α c =
      integerLatticeCurl R (rootNormalize R α) c := by
    have hh := congrArg (fun q => q c) (rootNormalize_integerCurl_eq R α)
    exact hh.symm
  have htarget := hscale (rootNormalize R α)
  have hsign : (sourceIntegerCellSign c : ℝ) = latticeCellOrientationSign c := by
    have haxes : globalPlaquetteAxes c = Gaussian.latticeCellAxes c := by
      ext i
      rfl
    simp [sourceIntegerCellSign, Gaussian.latticeCellOrientationSign,
      Gaussian.axisSetOrientationSign, haxes, Int.cast_pow]
  change (sourceIntegerCellSign c : ℝ) *
    ((sourceCurrentEquiv R
      (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)).1 c : ℝ) =
    (integerChordCurvature n f : ℝ)
  rw [sourceCurrentEquiv_apply_mk, hnormcurl, hsign, hscale (rootNormalize R α), ← hcurv]

end FroehlichSpencer.FS82.SurfaceInfinite
