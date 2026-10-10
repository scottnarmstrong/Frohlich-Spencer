/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.IDS.Trace
public import FroehlichSpencer.IDS.Boundary

/-!
# Almost sure convergence of the Stieltjes transforms of the finite-volume IDS measures

For `Im z > 0`, the Stieltjes transform of `idsMeasure ν (cube ν L) v` converges, for almost every
configuration `v`, to `E[G(z; 0, 0)]`: the trace formula writes it as an average of finite-volume
diagonal resolvent entries, which differ from the infinite-volume Green function by a boundary
term, and the latter averages converge by the ergodic theorem.
-/

@[expose] public section

namespace FroehlichSpencer.IDS

open MeasureTheory ProbabilityTheory Complex Filter Topology Set Infra

theorem ae_tendsto_stieltjes_idsMeasure {ν : ℕ} (hν : 0 < ν) (law : Measure ℝ)
    [IsProbabilityMeasure law] {z : ℂ} (hz : 0 < z.im) :
    ∀ᵐ v ∂configurationMeasure ν law,
      Tendsto (fun L : ℕ => stieltjes (idsMeasure ν (Infra.cube ν L) v) z) atTop
        (𝓝 (∫ w, latticeGreen ν z w 0 0 ∂configurationMeasure ν law)) := by
  filter_upwards [ae_tendsto_average_latticeGreen hν law hz.ne'] with v hv
  have hb : Tendsto (fun L : ℕ => ((Infra.cube ν L).card : ℂ)⁻¹ * ∑ x ∈ Infra.cube ν L,
      (Infra.resolventColumn (hoppingKernel ν) (fun w => v w + 2 * (ν : ℝ)) (Infra.cube ν L) z
        x x - latticeGreen ν z v x x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun L => norm_nonneg _) (fun L => ?_)
      (tendsto_average_norm_resolventColumn_sub_latticeGreen hz.ne' v)
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  have := hv.add hb
  rw [add_zero] at this
  refine this.congr fun L => ?_
  rw [stieltjes_idsMeasure ν _ v hz, ← mul_add, ← Finset.sum_add_distrib]
  simp
