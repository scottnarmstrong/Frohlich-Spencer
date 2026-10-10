/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Stieltjes.Average
public import FroehlichSpencer.Infra.Stieltjes.Transform
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Existence of a limit measure from Stieltjes transforms

Dominated convergence of averaged transforms to an arbitrary limit value, the tightness inequality
`μ{|x| > t} ≤ 2 (1 + Re (i t S_μ (i t)))`, existence of a probability measure with a prescribed
limiting transform (via Prokhorov's theorem), and a countable dense subset of the upper half-plane.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped BoundedContinuousFunction

namespace FroehlichSpencer.Infra

variable {Ω : Type*} [MeasurableSpace Ω]

theorem tendsto_stieltjes_bind_of_ae_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {κs : ℕ → Kernel Ω ℝ} [∀ n, IsFiniteKernel (κs n)] {M : ℝ}
    (hM : ∀ n ω, (κs n ω).real univ ≤ M) {z : ℂ} (hz : 0 < z.im) {c : ℂ}
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => stieltjes (κs n ω) z) atTop (𝓝 c)) :
    Tendsto (fun n => stieltjes (P.bind (κs n)) z) atTop (𝓝 c) := by
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => stieltjes (κs n ω) z) P := fun n =>
    (StronglyMeasurable.integral_kernel (κ := κs n)
      (f := fun t : ℝ => ((t : ℂ) - z)⁻¹)
      (Complex.measurable_ofReal.sub_const z).inv.stronglyMeasurable).aestronglyMeasurable
  simp_rw [stieltjes_bind P _ hz]
  have := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun n ω => stieltjes (κs n ω) z) (f := fun _ => c)
    (fun _ => M / z.im) hmeas (integrable_const _)
    (fun n => Eventually.of_forall fun ω => by
      have : IsFiniteMeasure (κs n ω) := inferInstance
      exact (norm_stieltjes_le (κs n ω) hz).trans
        (div_le_div_of_nonneg_right (hM n ω) hz.le)) h
  simpa using this

private theorem re_mul_inv (t x : ℝ) :
    ((t : ℂ) * I * ((x : ℂ) - (t : ℂ) * I)⁻¹).re = -t ^ 2 / (x ^ 2 + t ^ 2) := by
  rw [← div_eq_mul_inv, Complex.div_re]
  simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, mul_im,
    sub_re, sub_im, normSq_apply]
  have e : (x - 0) * (x - 0) + (0 - (t + 0)) * (0 - (t + 0)) = x ^ 2 + t ^ 2 := by ring
  rw [e]
  ring

theorem measureReal_abs_gt_le_stieltjes (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ}
    (ht : 0 < t) :
    μ.real {x | t < |x|} ≤ 2 * (1 + ((t : ℂ) * I * stieltjes μ ((t : ℂ) * I)).re) := by
  have him : 0 < ((t : ℂ) * I).im := by simpa using ht
  have hint : Integrable (fun x : ℝ => ((t : ℂ) * I * (((x : ℂ) - (t : ℂ) * I)⁻¹))) μ :=
    (integrable_inv_ofReal_sub μ him).const_mul _
  have h1 : ((t : ℂ) * I * stieltjes μ ((t : ℂ) * I)).re
      = ∫ x, -t ^ 2 / (x ^ 2 + t ^ 2) ∂μ := by
    rw [stieltjes, ← integral_const_mul]
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    simp_rw [re_mul_inv]
  have hpos : ∀ x : ℝ, 0 < x ^ 2 + t ^ 2 := fun x => by positivity
  have hcont : Integrable (fun x : ℝ => x ^ 2 / (x ^ 2 + t ^ 2)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Eventually.of_forall fun x => ?_)
    · exact (Continuous.div (by fun_prop) (by fun_prop) fun x => (hpos x).ne').aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity), div_le_one (hpos x)]
      nlinarith [sq_nonneg t]
  have h2 : 1 + ((t : ℂ) * I * stieltjes μ ((t : ℂ) * I)).re
      = ∫ x, x ^ 2 / (x ^ 2 + t ^ 2) ∂μ := by
    rw [h1]
    have hint2 : Integrable (fun x : ℝ => -t ^ 2 / (x ^ 2 + t ^ 2)) μ := by
      have := hcont.sub (integrable_const (1 : ℝ) (μ := μ))
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      field_simp [(hpos x).ne']
      ring
    have := integral_add (integrable_const (1 : ℝ)) hint2
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    field_simp [(hpos x).ne']
    ring
  rw [h2]
  have hind : ∫ x, ({x | t < |x|}.indicator (fun _ => (1 / 2 : ℝ)) x) ∂μ
      ≤ ∫ x, x ^ 2 / (x ^ 2 + t ^ 2) ∂μ := by
    refine integral_mono (integrable_const _ |>.indicator ?_) hcont fun x => ?_
    · exact measurableSet_lt measurable_const continuous_abs.measurable
    · by_cases hx : t < |x|
      · rw [indicator_of_mem (show x ∈ {x | t < |x|} from hx), le_div_iff₀ (hpos x)]
        have : t ^ 2 < x ^ 2 := by
          rw [← sq_abs x]; exact pow_lt_pow_left₀ hx ht.le (by norm_num)
        nlinarith
      · rw [indicator_of_notMem (show x ∉ {x | t < |x|} from hx)]
        positivity
  rw [integral_indicator_const _
    (measurableSet_lt measurable_const continuous_abs.measurable)] at hind
  simp only [smul_eq_mul] at hind
  linarith

theorem exists_countable_subset_upperHalfPlane_dense :
    ∃ D : Set ℂ, D.Countable ∧ D ⊆ {z | 0 < z.im} ∧ {z : ℂ | 0 < z.im} ⊆ closure D := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense {z : ℂ // 0 < z.im}
  refine ⟨Subtype.val '' D, hDc.image _, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · intro z hz
    have h := hDd ⟨z, hz⟩
    rwa [(isOpen_lt continuous_const Complex.continuous_im
      |>.isOpenEmbedding_subtypeVal).isInducing.closure_eq_preimage_closure_image D] at h

private theorem norm_inv_ofReal_sub_le' {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ‖((t : ℂ) - z)⁻¹‖ ≤ 1 / z.im := by
  rw [norm_inv, one_div]
  apply inv_anti₀ hz
  have := Complex.abs_im_le_norm ((t : ℂ) - z)
  simpa [abs_of_pos hz] using this

private theorem isTightMeasureSet_range_of_stieltjes {μs : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (μs n)] {s : ℂ → ℂ}
    (h : ∀ z : ℂ, 0 < z.im → Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (s z)))
    (hs : Tendsto (fun t : ℝ => (t : ℂ) * I * s ((t : ℂ) * I)) atTop (𝓝 (-1))) :
    IsTightMeasureSet (range μs) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  set δ : ℝ := (min ε 1).toReal with hδ
  have hδpos : 0 < δ := ENNReal.toReal_pos (lt_min hε one_pos).ne' (min_lt_of_right_lt
    ENNReal.one_lt_top).ne
  have hδε : ENNReal.ofReal δ ≤ ε := by
    rw [hδ, ENNReal.ofReal_toReal (min_lt_of_right_lt ENNReal.one_lt_top).ne]
    exact min_le_left _ _
  have hre : Tendsto (fun t : ℝ => 1 + ((t : ℂ) * I * s ((t : ℂ) * I)).re) atTop (𝓝 0) := by
    have := (continuous_re.tendsto _).comp hs
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
  obtain ⟨t, ht1, ht0⟩ := ((hre.eventually (gt_mem_nhds (half_pos hδpos))).and
    (eventually_gt_atTop 0)).exists
  have hn : Tendsto (fun n => 1 + ((t : ℂ) * I * stieltjes (μs n) ((t : ℂ) * I)).re) atTop
      (𝓝 (1 + ((t : ℂ) * I * s ((t : ℂ) * I)).re)) := by
    have := h ((t : ℂ) * I) (by simpa using ht0)
    exact (tendsto_const_nhds).add ((continuous_re.tendsto _).comp (this.const_mul _))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hn.eventually (gt_mem_nhds ht1))
  have hK : ∀ n, ∃ K : Set ℝ, IsCompact K ∧ μs n Kᶜ ≤ ε := fun n => by
    obtain ⟨K, hK, hKε⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (isTightMeasureSet_singleton (μ := μs n)) ε hε
    exact ⟨K, hK, hKε _ rfl⟩
  choose K hKc hKε using hK
  refine ⟨Metric.closedBall 0 t ∪ ⋃ n ∈ Finset.range n₀, K n,
    (isCompact_closedBall 0 t).union ((Finset.range n₀).isCompact_biUnion fun n _ => hKc n), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn' : n₀ ≤ n
  · have hb := measureReal_abs_gt_le_stieltjes (μs n) ht0
    have hlt := hn₀ n hn'
    have h3 : μs n {x | t < |x|} ≤ ENNReal.ofReal δ := by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    refine (measure_mono ?_).trans (h3.trans hδε)
    intro x hx
    simp only [mem_compl_iff, mem_union, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
      not_or] at hx
    exact not_le.1 hx.1
  · refine (measure_mono ?_).trans (hKε n)
    intro x hx hxK
    exact hx (Or.inr (mem_biUnion (Finset.mem_range.2 (not_le.1 hn')) hxK))

theorem exists_isProbabilityMeasure_stieltjes_eq {μs : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (μs n)] {s : ℂ → ℂ}
    (h : ∀ z : ℂ, 0 < z.im → Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (s z)))
    (hs : Tendsto (fun t : ℝ => (t : ℂ) * I * s ((t : ℂ) * I)) atTop (𝓝 (-1))) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ z : ℂ, 0 < z.im → stieltjes μ z = s z := by
  have htight := isTightMeasureSet_range_of_stieltjes h hs
  let ν : ℕ → ProbabilityMeasure ℝ := fun n => ⟨μs n, inferInstance⟩
  have hcompact : IsCompact (closure (range ν)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert htight using 1
    ext m
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨ν n, ⟨n, rfl⟩, rfl⟩
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨μ', -, hμ'⟩ := hcompact.ultrafilter_le_nhds (U.map ν)
    (.trans (by simp) (monotone_principal subset_closure))
  refine ⟨(μ' : Measure ℝ), inferInstance, fun z hz => ?_⟩
  let g : ℝ →ᵇ ℂ := BoundedContinuousFunction.mkOfBound
    ⟨fun x : ℝ => ((x : ℂ) - z)⁻¹, by
      refine continuous_iff_continuousAt.2 fun x => ContinuousAt.inv₀ (by fun_prop) ?_
      intro h0
      have := congrArg Complex.im h0
      simp at this
      linarith⟩ (2 / z.im) (fun x y => by
        have hx := norm_inv_ofReal_sub_le' hz x
        have hy := norm_inv_ofReal_sub_le' hz y
        simp only [ContinuousMap.coe_mk, dist_eq_norm]
        calc ‖((x : ℂ) - z)⁻¹ - ((y : ℂ) - z)⁻¹‖
            ≤ ‖((x : ℂ) - z)⁻¹‖ + ‖((y : ℂ) - z)⁻¹‖ := norm_sub_le _ _
          _ ≤ 1 / z.im + 1 / z.im := add_le_add hx hy
          _ = 2 / z.im := by ring)
  have hμ'' : Tendsto ν (U : Filter ℕ) (𝓝 μ') := hμ'
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hμ'' g
  have h2 := (h z hz).comp (Ultrafilter.of_le (atTop : Filter ℕ) : (U : Filter ℕ) ≤ atTop)
  exact tendsto_nhds_unique h1 h2

end FroehlichSpencer.Infra
