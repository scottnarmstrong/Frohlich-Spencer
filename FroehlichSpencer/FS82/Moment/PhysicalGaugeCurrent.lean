/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.SourceModel
public import FroehlichSpencer.FS82.Moment.SourceCoercivity

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson

variable {B : Box 4}

noncomputable abbrev T := sourceRootedTree B

/-- Apply the C2 orientation character to a geometric tree-current before
viewing it as a physical integer current on `Λ*`. -/
noncomputable def physicalGaugeCurrent (j : SourcePoissonEdge B → ℤ) : IntegerCurrent B :=
  Finsupp.equivFunOnFinite.symm (fun e => sourceDualT e * j e)

noncomputable def gaugeRealVector (j : SourcePoissonEdge B → ℤ) :
    EuclideanSpace ℝ (SourceDualOneCells B) :=
  WithLp.toLp 2 (fun e => (j e : ℝ))

theorem physicalGaugeCurrentRealVector_eq_T (j : SourcePoissonEdge B → ℤ) :
    WithLp.toLp 2 (fun e : SourceDualOneCells B =>
      ((physicalGaugeCurrent (B := B) j e : ℤ) : ℝ)) =
      sourceDualTLinear (gaugeRealVector (B := B) j) := by
  ext e
  simp [physicalGaugeCurrent, gaugeRealVector, sourceDualTLinear_apply,
    Gaussian.sourceDualT, Gaussian.dualCellOrientationSign,
    Gaussian.axisSetOrientationSign, Gaussian.dualAxisSum]

private theorem currentDivergence_as_sum (j : IntegerCurrent B)
    (v : SourceDualZeroCells B) :
    Currents.currentDivergence j v =
      ∑ e : SourceDualOneCells B,
        (Cubical.dualExteriorDifference (Finsupp.single v.1 (1 : ℝ)) e.1) *
          (j e : ℝ) := by
  classical
  induction j using Finsupp.induction_linear with
  | zero => simp [Currents.currentDivergence, Currents.sourceDualDivergenceOperator,
      Currents.realCurrent]
  | add j k hj hk =>
      rw [Currents.currentDivergence_add, hj, hk]
      calc
        _ = ∑ e : SourceDualOneCells B,
            ((Cubical.dualExteriorDifference (Finsupp.single v.1 (1 : ℝ)) e.1) *
                (j e : ℝ) +
              (Cubical.dualExteriorDifference (Finsupp.single v.1 (1 : ℝ)) e.1) *
                (k e : ℝ)) := by rw [Finset.sum_add_distrib]
        _ = ∑ e : SourceDualOneCells B,
            (Cubical.dualExteriorDifference (Finsupp.single v.1 (1 : ℝ)) e.1) *
              ((j e : ℝ) + (k e : ℝ)) := by
                apply Finset.sum_congr rfl
                intro e he
                ring
        _ = _ := by
          apply Finset.sum_congr rfl
          intro e he
          simp [Finsupp.add_apply, Int.cast_add]
  | single e n =>
      rw [Currents.currentDivergence_single]
      simp [Finsupp.single_apply]

theorem currentDivergence_eq_D0_inner (j : IntegerCurrent B)
    (v : SourceDualZeroCells B) :
    Currents.currentDivergence j v =
      inner ℝ (sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ)))
        (WithLp.toLp 2 (fun e : SourceDualOneCells B => (j e : ℝ))) := by
  rw [currentDivergence_as_sum]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro e he
  simp [sourceDualD₀, sourceDualZeroToChain, sourceDualOneEmbedding,
    sourceDualZeroEmbedding, compressDualSubtype_apply,
    embedDualSubtype_apply_single, euclideanToFinsupp_single,
    finsuppToEuclidean_apply]
  ring

/-- A tree-gauge circulation becomes a source current closed in the physical
lattice complex after applying the C2 edge orientation character. -/
theorem physicalGaugeCurrent_divergence_zero
    (j : SourcePoissonEdge B → ℤ) (hj : RootedTreeGauge.CoClosed (T (B := B)) j) :
    Currents.currentDivergence (physicalGaugeCurrent (B := B) j) = 0 := by
  classical
  funext v
  rw [currentDivergence_eq_D0_inner]
  rw [physicalGaugeCurrentRealVector_eq_T]
  let p := sourceTreeZeroPotential B (EuclideanSpace.single v (1 : ℝ))
  have hT := sourceDualT_D0_eq_treeCoboundary
      (B := B) (EuclideanSpace.single v (1 : ℝ))
      (sourcePoissonTreeLink (B := B) v)
  -- The inner product is the tree-current pairing against the point potential.
  have hpair : inner ℝ
      (sourceDualTLinear (sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ))))
      (gaugeRealVector (B := B) j) =
      ∑ e : SourcePoissonEdge B, (j e : ℝ) *
        RootedTreeGauge.coboundary (T (B := B)) p e := by
    rw [PiLp.inner_apply]
    have hcoord (e : SourcePoissonEdge B) :
        (sourceDualTLinear (sourceDualD₀ (B := B)
          (EuclideanSpace.single v (1 : ℝ)))) e =
          RootedTreeGauge.coboundary (T (B := B)) p e := by
      simpa [T, p, RootedTreeGauge.coboundary, sourceTreeCoboundary,
        sourceRootedTree] using
        sourceDualT_D0_eq_treeCoboundary
          (B := B) (EuclideanSpace.single v (1 : ℝ)) e
    simp only [gaugeRealVector, hcoord]
    apply Finset.sum_congr rfl
    intro e he
    simp only [Real.inner_apply]
    ring
  have hdiv := RootedTreeGauge.pairing_coboundary_eq_sum_divergence
    (T := T (B := B)) (fun e => (j e : ℝ)) p
  have hp : (∑ x : SourcePoissonVertex B, p x * RootedTreeGauge.divergence (T (B := B))
      (fun e => (j e : ℝ)) x) =
      RootedTreeGauge.divergence (T (B := B)) (fun e => (j e : ℝ)) (some v) := by
    simp [p, sourceTreeZeroPotential, EuclideanSpace.single]
  have htree : RootedTreeGauge.divergence (T (B := B))
        (fun e => (j e : ℝ)) (some v) = 0 := by
    have hv := hj (some v) (by simp [T, sourceRootedTree])
    have hv' := congrArg (fun n : ℤ => (n : ℝ)) hv
    simpa [RootedTreeGauge.CoClosed, RootedTreeGauge.divergence,
      map_sum, Int.cast_ite] using hv'
  have hsym : inner ℝ (sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ)))
      (sourceDualTLinear (gaugeRealVector (B := B) j)) =
      inner ℝ (sourceDualTLinear (sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ))))
        (gaugeRealVector (B := B) j) := by
    exact (sourceDualTLinear_symmetric (B := B)
      (sourceDualD₀ (B := B) (EuclideanSpace.single v (1 : ℝ)))
      (gaugeRealVector (B := B) j)).symm
  rw [hsym, hpair, hdiv, hp, htree]
  simp


end FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent

end
