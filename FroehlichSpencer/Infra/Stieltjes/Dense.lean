/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Stieltjes.Transform

/-!
# Convergence of Stieltjes transforms on a dense set

If finite measures `μ_n` have uniformly bounded masses and `S_{μ_n}(z) → S_μ(z)` for all `z` in a
set `D` whose closure contains the upper half-plane, then the convergence holds at every `z` with
`Im z > 0` (equicontinuity of the transforms on `{Im z ≥ Im z₀ / 2}`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set

namespace FroehlichSpencer.Infra

variable {μs : ℕ → Measure ℝ} [∀ n, IsFiniteMeasure (μs n)] {μ : Measure ℝ} [IsFiniteMeasure μ]

private theorem norm_stieltjes_sub_le_of_im_ge (ν : Measure ℝ) [IsFiniteMeasure ν] {K : ℝ}
    (hK : ν.real univ ≤ K) {z w : ℂ} (hz : 0 < z.im) (hw : z.im / 2 ≤ w.im) :
    ‖stieltjes ν z - stieltjes ν w‖ ≤ K * ‖z - w‖ * (2 / z.im ^ 2) := by
  have hw0 : 0 < w.im := lt_of_lt_of_le (half_pos hz) hw
  refine (norm_stieltjes_sub_le ν hz hw0).trans ?_
  have h0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hd : z.im * (z.im / 2) ≤ z.im * w.im := by gcongr
  calc ν.real univ * ‖z - w‖ / (z.im * w.im)
      ≤ ν.real univ * ‖z - w‖ / (z.im * (z.im / 2)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ ≤ K * ‖z - w‖ / (z.im * (z.im / 2)) := by gcongr
    _ = K * ‖z - w‖ * (2 / z.im ^ 2) := by field_simp

theorem tendsto_stieltjes_of_tendsto_on_dense {M : ℝ} (hM : ∀ n, (μs n).real univ ≤ M)
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := |M| + μ.real univ with hKdef
  have hK0 : 0 ≤ K := by positivity
  set C : ℝ := K * (2 / z.im ^ 2) with hC
  have hC0 : 0 ≤ C := by positivity
  have hδ : 0 < min (z.im / 2) (ε / (3 * (C + 1))) := by
    apply lt_min (half_pos hz); positivity
  obtain ⟨w, hwD, hzw⟩ := Metric.mem_closure_iff.1 (hdense hz) _ hδ
  have hzw1 : ‖z - w‖ < z.im / 2 := by
    rw [← dist_eq_norm]; exact hzw.trans_le (min_le_left _ _)
  have hzw2 : ‖z - w‖ < ε / (3 * (C + 1)) := by
    rw [← dist_eq_norm]; exact hzw.trans_le (min_le_right _ _)
  have hwim : z.im / 2 ≤ w.im := by
    have := Complex.abs_im_le_norm (z - w)
    rw [sub_im] at this
    have := (abs_le.1 this).2
    linarith
  have hsmall : C * ‖z - w‖ < ε / 3 := by
    have hC1 : 0 < C + 1 := by linarith
    calc C * ‖z - w‖ ≤ (C + 1) * ‖z - w‖ := by gcongr; linarith
      _ < (C + 1) * (ε / (3 * (C + 1))) := by gcongr
      _ = ε / 3 := by field_simp
  have hnu : ‖stieltjes μ z - stieltjes μ w‖ < ε / 3 := by
    refine lt_of_le_of_lt (norm_stieltjes_sub_le_of_im_ge μ (K := K) ?_ hz hwim) ?_
    · simp only [hKdef]; linarith [abs_nonneg M]
    · calc _ = C * ‖z - w‖ := by rw [hC]; ring
        _ < _ := hsmall
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h w hwD) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : ‖stieltjes (μs n) z - stieltjes (μs n) w‖ < ε / 3 := by
    refine lt_of_le_of_lt (norm_stieltjes_sub_le_of_im_ge (μs n) (K := K) ?_ hz hwim) ?_
    · simp only [hKdef]
      linarith [le_abs_self M, hM n, measureReal_nonneg (μ := μ) (s := univ)]
    · calc _ = C * ‖z - w‖ := by rw [hC]; ring
        _ < _ := hsmall
  have hn2 := hN n hn
  rw [dist_eq_norm] at hn2 ⊢
  calc ‖stieltjes (μs n) z - stieltjes μ z‖
      = ‖(stieltjes (μs n) z - stieltjes (μs n) w) + (stieltjes (μs n) w - stieltjes μ w)
          + (stieltjes μ w - stieltjes μ z)‖ := by congr 1; ring
    _ ≤ ‖stieltjes (μs n) z - stieltjes (μs n) w‖ + ‖stieltjes (μs n) w - stieltjes μ w‖
          + ‖stieltjes μ w - stieltjes μ z‖ := norm_add₃_le
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [norm_sub_rev (stieltjes μ w)]
        gcongr
    _ = ε := by ring

end FroehlichSpencer.Infra
