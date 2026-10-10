/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.IDS.Averaged
public import FroehlichSpencer.IDS.Green
public import FroehlichSpencer.Infra.Ergodic.Pointwise
public import FroehlichSpencer.Infra.Stieltjes.EigenvalueKernel

/-!
# Trace formula and the ergodic step for the lattice Green function

The Stieltjes transform of the averaged eigenvalue measure `idsMeasure ν Λ v` is the normalized
trace of the finite-volume resolvent; the cube averages of the diagonal Green function converge
almost surely (pointwise ergodic theorem); and `t I · E[G(tI; 0, 0)] → -1`.
-/

@[expose] public section

namespace FroehlichSpencer.IDS

open MeasureTheory ProbabilityTheory Complex Filter Topology Set Infra

theorem stieltjes_idsMeasure (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    stieltjes (idsMeasure ν Λ v) z = (Λ.card : ℂ)⁻¹ *
      ∑ x ∈ Λ, Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) Λ z x x := by
  unfold idsMeasure
  rw [stieltjes_eigenvalueMeasure _ hz, Fintype.card_coe]
  congr 1
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [hamiltonian_eq_restrictedOp]
  rw [← Finset.sum_coe_sort Λ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [resolventColumn_of_mem _ _ _ x.2 x.2]

private theorem norm_diag_le {ν : ℕ} {z : ℂ} (hz : z.im ≠ 0) (v : Site ν → ℝ) :
    ‖latticeGreen ν z v 0 0‖ ≤ 1 / |z.im| := norm_latticeGreen_le hz v 0 0

private theorem integrable_diag {ν : ℕ} (law : Measure ℝ) [IsProbabilityMeasure law] {z : ℂ}
    (hz : z.im ≠ 0) :
    Integrable (fun w => latticeGreen ν z w 0 0) (configurationMeasure ν law) := by
  have : IsProbabilityMeasure (configurationMeasure ν law) := by
    unfold configurationMeasure; infer_instance
  exact Integrable.of_bound (measurable_latticeGreen hz 0 0).aestronglyMeasurable (1 / |z.im|)
    (Eventually.of_forall fun w => norm_diag_le hz w)

theorem ae_tendsto_average_latticeGreen {ν : ℕ} (hν : 0 < ν) (law : Measure ℝ)
    [IsProbabilityMeasure law] {z : ℂ} (hz : z.im ≠ 0) :
    ∀ᵐ v ∂configurationMeasure ν law,
      Tendsto (fun L : ℕ => ((Infra.cube ν L).card : ℂ)⁻¹ * ∑ x ∈ Infra.cube ν L,
        latticeGreen ν z v x x) atTop
        (𝓝 (∫ w, latticeGreen ν z w 0 0 ∂configurationMeasure ν law)) := by
  have hi := integrable_diag (ν := ν) law hz
  have h1 := ae_tendsto_cubeAverage hν law (f := fun w => (latticeGreen ν z w 0 0).re) hi.re
  have h2 := ae_tendsto_cubeAverage hν law (f := fun w => (latticeGreen ν z w 0 0).im) hi.im
  filter_upwards [h1, h2] with v hv1 hv2
  have hT := (Complex.continuous_ofReal.tendsto _ |>.comp hv1).add
    (((Complex.continuous_ofReal.tendsto _).comp hv2).mul_const I)
  have hlim : ((∫ w, (latticeGreen ν z w 0 0).re ∂configurationMeasure ν law : ℝ) : ℂ) +
      ((∫ w, (latticeGreen ν z w 0 0).im ∂configurationMeasure ν law : ℝ) : ℂ) * I =
      ∫ w, latticeGreen ν z w 0 0 ∂configurationMeasure ν law := by
    have e1 : ∫ w, (latticeGreen ν z w 0 0).re ∂configurationMeasure ν law =
        (∫ w, latticeGreen ν z w 0 0 ∂configurationMeasure ν law).re := integral_re hi
    have e2 : ∫ w, (latticeGreen ν z w 0 0).im ∂configurationMeasure ν law =
        (∫ w, latticeGreen ν z w 0 0 ∂configurationMeasure ν law).im := integral_im hi
    rw [e1, e2]
    exact Complex.re_add_im _
  have hT' : Tendsto _ atTop (𝓝 (∫ w, latticeGreen ν z w 0 0 ∂configurationMeasure ν law)) :=
    hlim ▸ hT
  refine hT'.congr fun L => ?_
  have hsh : ∀ x : Site ν, latticeGreen ν z v x x =
      latticeGreen ν z (latticeShift x v) 0 0 := fun x => by
    simpa using latticeGreen_shift hz v x 0 0
  simp only [Function.comp_apply, cubeAverage, hsh]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum]

theorem tendsto_mul_integral_latticeGreen (ν : ℕ) (law : Measure ℝ) [IsProbabilityMeasure law] :
    Tendsto (fun t : ℝ => (t : ℂ) * I *
      ∫ w, latticeGreen ν ((t : ℂ) * I) w 0 0 ∂configurationMeasure ν law) atTop (𝓝 (-1)) := by
  have hprob : IsProbabilityMeasure (configurationMeasure ν law) := by
    unfold configurationMeasure; infer_instance
  have hint : ∀ t : ℝ, (t : ℂ) * I *
      ∫ w, latticeGreen ν ((t : ℂ) * I) w 0 0 ∂configurationMeasure ν law =
      ∫ w, (t : ℂ) * I * latticeGreen ν ((t : ℂ) * I) w 0 0 ∂configurationMeasure ν law :=
    fun t => (integral_const_mul _ _).symm
  simp_rw [hint]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := configurationMeasure ν law)
    (F := fun (t : ℝ) w => (t : ℂ) * I * latticeGreen ν ((t : ℂ) * I) w 0 0) (l := atTop)
    (f := fun _ => (-1 : ℂ)) (bound := fun _ => 1) ?_ ?_ ?_ ?_
  · simpa using h
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hz : ((t : ℂ) * I).im ≠ 0 := by simpa using ht.ne'
    exact ((measurable_latticeGreen hz 0 0).const_mul _).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    refine Eventually.of_forall fun w => ?_
    have hz : ((t : ℂ) * I).im ≠ 0 := by simpa using ht.ne'
    have h1 := norm_latticeGreen_le hz w 0 0
    have h2 : |((t : ℂ) * I).im| = t := by simp [abs_of_pos ht]
    rw [h2] at h1
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    calc t * ‖latticeGreen ν ((t : ℂ) * I) w 0 0‖ ≤ t * (1 / t) := by gcongr
      _ = 1 := by field_simp
  · exact integrable_const _
  · exact Eventually.of_forall fun w => tendsto_mul_latticeGreen ν w 0
