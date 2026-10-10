/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.SourceTreeChart
public import FroehlichSpencer.FS82.Gaussian.SourceCurlIncidence
public import FroehlichSpencer.FS82.Gaussian.SourceImageGaussian
public import FroehlichSpencer.FS82.Gaussian.RadialGaussian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Source quotient Gaussian in tree-chart coordinates -/

@[expose] public section

namespace FroehlichSpencer.FS82.Gaussian.SourceTreeChart

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Gaussian.TreeGaugeQuotient
open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped InnerProductSpace

variable {B : SourceBox}

/-- The source curl quotient and the generic source-complex quotient have the
same kernel presentation. This adapter makes that quotient identification
explicit at the measure boundary. -/
theorem sourceDualComplex_d₁_kernel_eq :
    (sourceDualD₁ (B := B)).ker = (sourceDualComplex B).d₁.ker := rfl

noncomputable def sourceCurlQuotientToFiniteGauge :
    SourceCurlQuotient B ≃ₗ[ℝ]
      FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient (sourceDualComplex B) :=
  Submodule.quotEquivOfEq ((sourceDualD₁ (B := B)).ker)
    ((sourceDualComplex B).d₁.ker) sourceDualComplex_d₁_kernel_eq

theorem sourceCurlQuotientToFiniteGauge_mk
    (a : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sourceCurlQuotientToFiniteGauge (B := B) (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk a :=
  Submodule.quotEquivOfEq_mk _ _ sourceDualComplex_d₁_kernel_eq a

theorem sourceCurlQuotientToFiniteGauge_symm_mk
    (a : EuclideanSpace ℝ (SourceDualOneCells B)) :
    (sourceCurlQuotientToFiniteGauge (B := B)).symm
        (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := by
  apply (sourceCurlQuotientToFiniteGauge (B := B)).injective
  rw [(sourceCurlQuotientToFiniteGauge (B := B)).apply_symm_apply]
  exact (Submodule.quotEquivOfEq_mk _ _ sourceDualComplex_d₁_kernel_eq a).symm

noncomputable def sourceGaussianQuotientChordEquiv
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient (sourceDualComplex B) ≃ₗ[ℝ]
      (T.Chord → ℝ) :=
  (sourceCurlQuotientToFiniteGauge (B := B)).symm.trans
    (sourceCurlQuotientChordEquiv T hT)

theorem sourceGaussianQuotientChordEquiv_measurable
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    Measurable (sourceGaussianQuotientChordEquiv T hT) := by
  rw [measurable_from_quotient]
  let A : EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ] (T.Chord → ℝ) :=
    (sourceGaussianQuotientChordEquiv T hT).toLinearMap.comp
      ((sourceDualComplex B).d₁.ker.mkQ)
  have hcomp : (sourceGaussianQuotientChordEquiv T hT ∘
      (Quotient.mk'' : EuclideanSpace ℝ (SourceDualOneCells B) →
        FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient (sourceDualComplex B))) = A := by
    funext x
    rfl
  rw [hcomp]
  exact (LinearMap.continuous_of_finiteDimensional A).measurable

noncomputable def sourceTreeChartCurlEquiv
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    (T.Chord → ℝ) ≃ₗ[ℝ] (sourceDualD₁ (B := B)).range :=
  (sourceCurlQuotientChordEquiv T hT).symm.trans
    (sourceDualD₁ (B := B)).quotKerEquivRange

theorem sourceTreeChartCurlEquiv_apply_val
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget)
    (x : T.Chord → ℝ) :
    (sourceTreeChartCurlEquiv T hT x).1 = sourceTreeChartCurlLinear T x := by
  let a : EuclideanSpace ℝ (SourceDualOneCells B) :=
    sourceFunctionToEuclidean (extendChordsLinear T x)
  let f : SourceDualOneCells B → ℝ :=
    sourceEuclideanToFunction (sourceDualTLinear (sourceFunctionToEuclidean
      (extendChordsLinear T x)))
  have htree : RootedTreeGauge.InTreeGauge T f := by
    intro v
    have hext : T.extendChord x (T.treeEdge v) = 0 := by
      simp [RootedTreeGauge.extendChord]
    simp [f, sourceEuclideanToFunction, sourceFunctionToEuclidean,
      extendChordsLinear, hext]
  have hnormalize : treeNormalizeLinear T f = f := by
    funext e
    change f e - (RootedTreeGauge.treePotential T f (T.edgeTarget e) -
      RootedTreeGauge.treePotential T f (T.edgeSource e)) = f e
    rw [treePotential_eq_zero_of_treeGauge T f htree]
    rw [treePotential_eq_zero_of_treeGauge T f htree]
    simp
  have hchart : treeChordMap T f = sourceChordOrientationLinear T x := by
    change restrictChordsLinear T (treeNormalizeLinear T f) = _
    rw [hnormalize]
    funext c
    change f c.1 = sourceChordOrientationLinear T x c
    have hext : T.extendChord x c.1 = x c :=
      congrFun (RootedTreeGauge.restrict_extendChord T x) c
    simp [f, sourceChordOrientationLinear, sourceEuclideanToFunction,
      sourceFunctionToEuclidean, extendChordsLinear, hext]
  have hforward : sourceCurlQuotientChordEquiv T hT
      (Submodule.Quotient.mk a) = x := by
    change sourceChordOrientationLinear T (treeChordMap T f) = x
    rw [hchart]
    funext c
    have hs : dualCellOrientationSign c.1.1 ^ 2 = 1 :=
      dualCellOrientationSign_sq c.1
    calc
      dualCellOrientationSign c.1.1 *
          (dualCellOrientationSign c.1.1 * x c) =
        (dualCellOrientationSign c.1.1 ^ 2) * x c := by ring
      _ = x c := by rw [hs]; ring
  have hq : (sourceCurlQuotientChordEquiv T hT).symm x =
      Submodule.Quotient.mk a := by
    apply (sourceCurlQuotientChordEquiv T hT).injective
    calc
      sourceCurlQuotientChordEquiv T hT
          ((sourceCurlQuotientChordEquiv T hT).symm x) = x :=
        (sourceCurlQuotientChordEquiv T hT).apply_symm_apply x
      _ = sourceCurlQuotientChordEquiv T hT (Submodule.Quotient.mk a) := hforward.symm
  change ((sourceDualD₁ (B := B)).quotKerEquivRange
      ((sourceCurlQuotientChordEquiv T hT).symm x)).1 =
    sourceTreeChartCurlLinear T x
  rw [hq]
  rfl

theorem sourceCurlQuotientChordEquiv_symm_apply_mk
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget)
    (x : T.Chord → ℝ) :
    (sourceCurlQuotientChordEquiv T hT).symm x =
      Submodule.Quotient.mk
        (sourceFunctionToEuclidean (extendChordsLinear T x)) := by
  let a : EuclideanSpace ℝ (SourceDualOneCells B) :=
    sourceFunctionToEuclidean (extendChordsLinear T x)
  let f : SourceDualOneCells B → ℝ :=
    sourceEuclideanToFunction (sourceDualTLinear (sourceFunctionToEuclidean
      (extendChordsLinear T x)))
  have htree : RootedTreeGauge.InTreeGauge T f := by
    intro v
    have hext : T.extendChord x (T.treeEdge v) = 0 := by
      simp [RootedTreeGauge.extendChord]
    simp [f, sourceEuclideanToFunction, sourceFunctionToEuclidean,
      extendChordsLinear, hext]
  have hnormalize : treeNormalizeLinear T f = f := by
    funext e
    change f e - (RootedTreeGauge.treePotential T f (T.edgeTarget e) -
      RootedTreeGauge.treePotential T f (T.edgeSource e)) = f e
    rw [treePotential_eq_zero_of_treeGauge T f htree]
    rw [treePotential_eq_zero_of_treeGauge T f htree]
    simp
  have hchart : treeChordMap T f = sourceChordOrientationLinear T x := by
    change restrictChordsLinear T (treeNormalizeLinear T f) = _
    rw [hnormalize]
    funext c
    change f c.1 = sourceChordOrientationLinear T x c
    have hext : T.extendChord x c.1 = x c :=
      congrFun (RootedTreeGauge.restrict_extendChord T x) c
    simp [f, sourceChordOrientationLinear, sourceEuclideanToFunction,
      sourceFunctionToEuclidean, extendChordsLinear, hext]
  have hforward : sourceCurlQuotientChordEquiv T hT
      (Submodule.Quotient.mk a) = x := by
    change sourceChordOrientationLinear T (treeChordMap T f) = x
    rw [hchart]
    funext c
    have hs : dualCellOrientationSign c.1.1 ^ 2 = 1 :=
      dualCellOrientationSign_sq c.1
    calc
      dualCellOrientationSign c.1.1 *
          (dualCellOrientationSign c.1.1 * x c) =
        (dualCellOrientationSign c.1.1 ^ 2) * x c := by ring
      _ = x c := by rw [hs]; ring
  apply (sourceCurlQuotientChordEquiv T hT).injective
  calc
    sourceCurlQuotientChordEquiv T hT
        ((sourceCurlQuotientChordEquiv T hT).symm x) = x :=
      (sourceCurlQuotientChordEquiv T hT).apply_symm_apply x
    _ = sourceCurlQuotientChordEquiv T hT (Submodule.Quotient.mk a) := hforward.symm

theorem sourceGaussianQuotientChordEquiv_symm_measurable
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    Measurable (sourceGaussianQuotientChordEquiv T hT).symm := by
  let A : (T.Chord → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (SourceDualOneCells B) :=
    (sourceFunctionToEuclidean (B := B)).comp (extendChordsLinear T)
  have hfun : (sourceGaussianQuotientChordEquiv T hT).symm =
      fun x => (sourceDualComplex B).d₁.ker.mkQ (A x) := by
    funext x
    change (sourceCurlQuotientToFiniteGauge (B := B))
        ((sourceCurlQuotientChordEquiv T hT).symm x) =
      (sourceDualComplex B).d₁.ker.mkQ (A x)
    rw [sourceCurlQuotientChordEquiv_symm_apply_mk]
    rw [sourceCurlQuotientToFiniteGauge_mk]
    rfl
  rw [hfun]
  exact measurable_quotient_mk''.comp
    (LinearMap.continuous_of_finiteDimensional A).measurable


noncomputable def sourceTreeChartCurlEuclideanEquiv
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    EuclideanSpace ℝ T.Chord ≃ₗ[ℝ] (sourceDualD₁ (B := B)).range :=
  (EuclideanSpace.equiv T.Chord ℝ).toLinearEquiv.trans
    (sourceTreeChartCurlEquiv T hT)

noncomputable def sourceTreeChartCurlEuclideanCLE
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    EuclideanSpace ℝ T.Chord ≃L[ℝ] (sourceDualD₁ (B := B)).range :=
  (sourceTreeChartCurlEuclideanEquiv T hT).toContinuousLinearEquiv

noncomputable def sourceTreeChartCurlChordCLE
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    (T.Chord → ℝ) ≃L[ℝ] (sourceDualD₁ (B := B)).range :=
  (sourceTreeChartCurlEquiv T hT).toContinuousLinearEquiv

theorem sourceTreeChartCurlEuclidean_norm_sq_eq_literal
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget)
    (y : EuclideanSpace ℝ T.Chord) :
    ‖sourceTreeChartCurlEuclideanEquiv T hT y‖ ^ 2 =
      ∑ p : SourceDualTwoCells B,
        (∑ e : T.Chord,
          sourceCurlCoefficient p e.1 * (EuclideanSpace.equiv T.Chord ℝ y) e) ^ 2 := by
  change ‖(sourceTreeChartCurlEquiv T hT
    (EuclideanSpace.equiv T.Chord ℝ y)).1‖ ^ 2 = _
  rw [sourceTreeChartCurlEquiv_apply_val]
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [sourceTreeChartCurl_energy_literal]

theorem sourceChordToEuclidean_measurePreserving
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B)) :
    MeasurePreserving ((EuclideanSpace.equiv T.Chord ℝ).symm)
      (volume : Measure (T.Chord → ℝ)) (volume : Measure (EuclideanSpace ℝ T.Chord)) := by
  convert (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp T.Chord).symm using 1
  rfl

theorem sourceTreeChartLiteralDensity_mapEuclidean
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) {β : ℝ} (_hβ : 0 < β) :
    Measure.map ((EuclideanSpace.equiv T.Chord ℝ).symm)
      ((volume : Measure (T.Chord → ℝ)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
          ∑ p : SourceDualTwoCells B,
            (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2)))) =
      (volume : Measure (EuclideanSpace ℝ T.Chord)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
          ‖sourceTreeChartCurlEuclideanEquiv T hT y‖ ^ 2))) := by
  let U : (T.Chord → ℝ) ≃L[ℝ] EuclideanSpace ℝ T.Chord :=
    (EuclideanSpace.equiv T.Chord ℝ).symm.toContinuousLinearEquiv
  let f := sourceTreeChartCurlEuclideanCLE T hT
  let g : EuclideanSpace ℝ T.Chord → ENNReal :=
    fun y => radialWeight β (f y)
  have hg : Measurable g := (measurable_radialWeight β).comp f.continuous.measurable
  have hden : (fun x : T.Chord → ℝ => ENNReal.ofReal
      (Real.exp (-(1 / (2 * β)) *
        ∑ p : SourceDualTwoCells B,
          (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2))) =
      g ∘ U := by
    funext x
    have hnorm := sourceTreeChartCurlEuclidean_norm_sq_eq_literal T hT (U x)
    simpa [g, f, U, radialWeight, sourceTreeChartCurlEuclideanCLE,
      sourceTreeChartCurlEuclideanEquiv] using congrArg
      (fun r : ℝ => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) * r))) hnorm.symm
  rw [hden]
  have hmapdens := map_withDensity_linearEquiv_general U
    (volume : Measure (T.Chord → ℝ)) g hg
  have hU : Measure.map U (volume : Measure (T.Chord → ℝ)) =
      (volume : Measure (EuclideanSpace ℝ T.Chord)) := by
    simpa [U] using (sourceChordToEuclidean_measurePreserving T).map_eq
  calc
      Measure.map ((EuclideanSpace.equiv T.Chord ℝ).symm)
        ((volume : Measure (T.Chord → ℝ)).withDensity (g ∘ U)) =
        Measure.map U ((volume : Measure (T.Chord → ℝ)).withDensity (g ∘ U)) := by
          congr 1
    _ = (Measure.map U (volume : Measure (T.Chord → ℝ))).withDensity g := hmapdens
    _ = (volume : Measure (EuclideanSpace ℝ T.Chord)).withDensity g := by rw [hU]

theorem sourceTreeChartLiteralDensity_mass_finite_pos
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) {β : ℝ} (hβ : 0 < β) :
    0 < ((volume : Measure (T.Chord → ℝ)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
          ∑ p : SourceDualTwoCells B,
            (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2)))) Set.univ ∧
      ((volume : Measure (T.Chord → ℝ)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
          ∑ p : SourceDualTwoCells B,
            (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2)))) Set.univ < ⊤ := by
  let f := sourceTreeChartCurlEuclideanCLE T hT
  obtain ⟨c, hcpos, hcfinite, hcvol⟩ := map_volume_linearEquiv_smul f
  have hraw : Measure.map f
      ((volume : Measure (EuclideanSpace ℝ T.Chord)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) * ‖f y‖ ^ 2)))) =
      c • (radialDensityMeasure (V := (sourceDualD₁ (B := B)).range) β) := by
    change Measure.map f
      (volume.withDensity (radialWeight β ∘ f)) = _
    rw [map_withDensity_linearEquiv f (radialWeight β) (measurable_radialWeight β),
      hcvol, withDensity_smul_measure]
    rfl
  have hmassE : ((volume : Measure (EuclideanSpace ℝ T.Chord)).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) * ‖f y‖ ^ 2)))) Set.univ =
        c * (radialDensityMeasure (V := (sourceDualD₁ (B := B)).range) β) Set.univ := by
    have h := congrArg (fun μ : Measure (sourceDualD₁ (B := B)).range => μ Set.univ) hraw
    rw [Measure.map_apply f.continuous.measurable MeasurableSet.univ] at h
    simpa [Measure.smul_apply, ENNReal.smul_def] using h
  have hrad := radialDensityMeasure_mass_finite_pos
    (V := (sourceDualD₁ (B := B)).range) hβ
  have hmassPi := sourceTreeChartLiteralDensity_mapEuclidean T hT hβ
  have hmass : ((volume : Measure (T.Chord → ℝ)).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
        ∑ p : SourceDualTwoCells B,
          (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2)))) Set.univ =
        ((volume : Measure (EuclideanSpace ℝ T.Chord)).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) * ‖f y‖ ^ 2)))) Set.univ := by
    have h := congrArg (fun μ : Measure (EuclideanSpace ℝ T.Chord) => μ Set.univ) hmassPi
    rw [Measure.map_apply ((EuclideanSpace.equiv T.Chord ℝ).symm).continuous.measurable
      MeasurableSet.univ] at h
    have hfeq : ∀ y, f y = sourceTreeChartCurlEuclideanEquiv T hT y := by
      intro y
      apply Subtype.ext
      rfl
    simpa [hfeq] using h
  rw [hmass]
  rw [hmassE]
  constructor
  · exact ENNReal.mul_pos (ne_of_gt hcpos) (ne_of_gt hrad.1)
  · exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hcfinite) hrad.2

theorem sourceDualQuotientGaussian_treeChart_law
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) {β : ℝ} (hβ : 0 < β) :
    Measure.map (sourceGaussianQuotientChordEquiv T hT)
        (sourceDualQuotientGaussian (B := B) β (le_of_lt hβ)) =
      (fun ν => (ν Set.univ)⁻¹ • ν)
        ((volume : Measure (T.Chord → ℝ)).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
            ∑ p : SourceDualTwoCells B,
              (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2)))) := by
  let chart := sourceGaussianQuotientChordEquiv T hT
  let φ := sourceTreeChartCurlChordCLE T hT
  let μ := sourceDualQuotientGaussian (B := B) β (le_of_lt hβ)
  let ρ : Measure (T.Chord → ℝ) := (volume : Measure (T.Chord → ℝ)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
      ∑ p : SourceDualTwoCells B,
        (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2)))
  have hsource : Measure.map φ (Measure.map chart μ) =
      Measure.map (fun y : (sourceDualD₁ (B := B)).range => Real.sqrt β • y)
        (stdGaussian ((sourceDualD₁ (B := B)).range)) := by
    have hcomp : (fun q : FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient
        (sourceDualComplex B) => φ (chart q)) =
        FroehlichSpencer.FS82.Gaussian.finiteCurlQuotientToImage
          (sourceDualComplex B) := by
      funext q
      refine Submodule.Quotient.induction_on
        (p := (sourceDualComplex B).d₁.ker) q ?_
      intro a
      apply Subtype.ext
      rw [FroehlichSpencer.FS82.Gaussian.finiteCurlQuotientToImage_apply
        (sourceDualComplex B) (Submodule.Quotient.mk a)]
      have hφ (x : T.Chord → ℝ) : φ x = sourceTreeChartCurlEquiv T hT x := rfl
      have hchart (q : FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient
          (sourceDualComplex B)) :
          chart q = sourceCurlQuotientChordEquiv T hT
            ((sourceCurlQuotientToFiniteGauge (B := B)).symm q) := rfl
      rw [hφ, hchart, sourceCurlQuotientToFiniteGauge_symm_mk]
      change (((sourceCurlQuotientChordEquiv T hT).symm.trans
          (sourceDualD₁ (B := B)).quotKerEquivRange)
          (sourceCurlQuotientChordEquiv T hT (Submodule.Quotient.mk a))).1 =
        ((sourceDualComplex B).d₁.quotKerEquivRange
          (Submodule.Quotient.mk a)).1
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      rfl
    rw [Measure.map_map φ.continuous.measurable
      (sourceGaussianQuotientChordEquiv_measurable T hT)]
    change Measure.map (fun q :
      FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient (sourceDualComplex B) =>
        φ (chart q)) μ = _
    rw [hcomp]
    change FroehlichSpencer.FS82.Gaussian.finiteCurlImageGaussian
      (sourceDualComplex B) β (le_of_lt hβ) = _
    exact FroehlichSpencer.FS82.Gaussian.finiteCurlImageGaussian_eq_scaledStdGaussian
      (sourceDualComplex B) hβ
  let U : (T.Chord → ℝ) ≃L[ℝ] EuclideanSpace ℝ T.Chord :=
    (EuclideanSpace.equiv T.Chord ℝ).symm.toContinuousLinearEquiv
  let F := sourceTreeChartCurlEuclideanCLE T hT
  have hrawEucl : Measure.map U ρ =
      (volume : Measure (EuclideanSpace ℝ T.Chord)).withDensity (radialWeight β ∘ F) := by
    calc
      Measure.map U ρ = Measure.map ((EuclideanSpace.equiv T.Chord ℝ).symm) ρ := by
        congr 1
      _ = (volume : Measure (EuclideanSpace ℝ T.Chord)).withDensity
          (fun y => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
            ‖sourceTreeChartCurlEuclideanEquiv T hT y‖ ^ 2))) :=
          sourceTreeChartLiteralDensity_mapEuclidean T hT hβ
      _ = (volume : Measure (EuclideanSpace ℝ T.Chord)).withDensity
          (radialWeight β ∘ F) := by
          congr 1
  have htarget : Measure.map φ (normalizedMeasure ρ) =
      Measure.map (fun y : (sourceDualD₁ (B := B)).range => Real.sqrt β • y)
        (stdGaussian ((sourceDualD₁ (B := B)).range)) := by
    have hnormU := map_normalizedMeasure_linearEquiv U ρ
    rw [hrawEucl] at hnormU
    have hf := normalizedDensity_map_linearEquiv F (radialWeight β)
      (measurable_radialWeight β)
    calc
      Measure.map φ (normalizedMeasure ρ) =
          Measure.map F (Measure.map U (normalizedMeasure ρ)) := by
            rw [Measure.map_map F.continuous.measurable U.continuous.measurable]
            congr 1
      _ = Measure.map F (normalizedMeasure
          ((volume : Measure (EuclideanSpace ℝ T.Chord)).withDensity
            (radialWeight β ∘ F))) := by rw [hnormU]
      _ = normalizedMeasure (radialDensityMeasure
          (V := (sourceDualD₁ (B := B)).range) β) := by
            simpa [radialDensityMeasure] using hf
      _ = Measure.map (fun y : (sourceDualD₁ (B := B)).range => Real.sqrt β • y)
          (stdGaussian ((sourceDualD₁ (B := B)).range)) :=
            normalizedRadial_eq_scaledStdGaussian hβ
  have hpush : Measure.map φ (Measure.map chart μ) = Measure.map φ (normalizedMeasure ρ) :=
    hsource.trans htarget.symm
  have hcancel : Measure.map chart μ = normalizedMeasure ρ := by
    have hid : (φ.symm ∘ φ) = id := by
      funext x
      exact φ.symm_apply_apply x
    have hinv : Measure.map φ.symm (Measure.map φ (normalizedMeasure ρ)) =
        normalizedMeasure ρ := by
      rw [Measure.map_map φ.symm.continuous.measurable φ.continuous.measurable]
      rw [hid, Measure.map_id]
    have h := congrArg (Measure.map φ.symm) hpush
    rw [Measure.map_map φ.symm.continuous.measurable φ.continuous.measurable] at h
    rw [hid, Measure.map_id] at h
    rw [hinv] at h
    exact h
  change Measure.map chart μ = normalizedMeasure ρ
  exact hcancel

theorem sourceDualQuotientGaussian_treeChart_integral
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) {β : ℝ} (hβ : 0 < β)
    (F : FroehlichSpencer.FS82.Gaussian.FiniteGaugeQuotient
      (sourceDualComplex B) → ℝ)
    (hF : Integrable F
      (sourceDualQuotientGaussian (B := B) β (le_of_lt hβ))) :
    ∫ q, F q ∂(sourceDualQuotientGaussian (B := B) β (le_of_lt hβ)) =
      ∫ x, F ((sourceGaussianQuotientChordEquiv T hT).symm x) ∂
        ((fun ν => (ν Set.univ)⁻¹ • ν)
          ((volume : Measure (T.Chord → ℝ)).withDensity
            (fun x => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
              ∑ p : SourceDualTwoCells B,
                (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2))))) := by
  let μ := sourceDualQuotientGaussian (B := B) β (le_of_lt hβ)
  let chart := sourceGaussianQuotientChordEquiv T hT
  let chartLaw := (fun ν => (ν Set.univ)⁻¹ • ν)
    ((volume : Measure (T.Chord → ℝ)).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-(1 / (2 * β)) *
        ∑ p : SourceDualTwoCells B,
          (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2))))
  have hLaw : Measure.map chart μ = chartLaw := by
    simpa [μ, chartLaw] using sourceDualQuotientGaussian_treeChart_law T hT hβ
  have hpresInv : MeasurePreserving chart.symm chartLaw μ := by
    refine ⟨sourceGaussianQuotientChordEquiv_symm_measurable T hT, ?_⟩
    rw [← hLaw]
    rw [Measure.map_map (sourceGaussianQuotientChordEquiv_symm_measurable T hT)
      (sourceGaussianQuotientChordEquiv_measurable T hT)]
    have hcancel : chart.symm ∘ chart = id := by
      funext q
      exact chart.symm_apply_apply q
    rw [hcancel, Measure.map_id]
  have hFInv : Integrable (fun x => F (chart.symm x)) chartLaw :=
    (hpresInv.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hFInvMap : Integrable (fun x => F (chart.symm x)) (Measure.map chart μ) := by
    rw [hLaw]
    exact hFInv
  calc
    ∫ q, F q ∂μ = ∫ q, F (chart.symm (chart q)) ∂μ := by
      congr 1
      funext q
      rw [chart.symm_apply_apply]
    _ = ∫ x, F (chart.symm x) ∂(Measure.map chart μ) :=
      (integral_map (sourceGaussianQuotientChordEquiv_measurable T hT).aemeasurable
        hFInvMap.aestronglyMeasurable).symm
    _ = ∫ x, F (chart.symm x) ∂chartLaw := by rw [hLaw]

end FroehlichSpencer.FS82.Gaussian.SourceTreeChart

end
