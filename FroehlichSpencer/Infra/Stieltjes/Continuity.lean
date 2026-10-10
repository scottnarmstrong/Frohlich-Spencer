/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Stieltjes.Inversion
public import FroehlichSpencer.Infra.Stieltjes.Dense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The continuity theorem for Stieltjes transforms

Finite measures `μ_n`, `μ` on `ℝ` with uniformly bounded masses whose Stieltjes transforms converge
on a dense subset of the upper half-plane converge vaguely (`∫ f dμ_n → ∫ f dμ` for continuous `f`
vanishing at infinity); if moreover the total masses converge, they converge weakly (bounded
continuous `f`), and the distribution functions converge at every `E` with `μ {E} = 0`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set

namespace FroehlichSpencer.Infra

variable {μs : ℕ → Measure ℝ} [∀ n, IsFiniteMeasure (μs n)] {μ : Measure ℝ} [IsFiniteMeasure μ]

private theorem abs_integral_sub_le_aux (ν : Measure ℝ) [IsFiniteMeasure ν] {f g : ℝ → ℝ}
    (hf : Integrable f ν) (hg : Integrable g ν) {δ : ℝ} (h : ∀ t, |g t - f t| ≤ δ) :
    |∫ t, g t ∂ν - ∫ t, f t ∂ν| ≤ δ * ν.real univ := by
  rw [← integral_sub hg hf]
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun t => g t - f t) (C := δ)
    (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using h t)
  simpa only [Real.norm_eq_abs] using this

/-- For fixed `η > 0` and `f` continuous with compact support, the Poisson smoothings integrate
against `μs n` to something converging to the integral against `μ`. -/
private theorem tendsto_integral_smooth_aux {M : ℝ} (hM : ∀ n, (μs n).real univ ≤ M)
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => ∫ t, (∫ x, f (t - x) * poissonKernel η x) ∂μs n) atTop
      (𝓝 (∫ t, (∫ x, f (t - x) * poissonKernel η x) ∂μ)) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  simp only [integral_poissonSmooth_eq _ hf hfi hη]
  have hz : ∀ E : ℝ, 0 < ((E : ℂ) + η * I).im := fun E => by simpa using hη
  refine tendsto_integral_of_dominated_convergence
    (fun E => ‖f E‖ * (M / η) / Real.pi) (fun n => ?_) ?_ ?_ ?_
  · have hc : ∀ ν : Measure ℝ, IsFiniteMeasure ν →
        Continuous fun E : ℝ => stieltjes ν ((E : ℂ) + η * I) := fun ν _ =>
      (continuousOn_stieltjes ν).comp_continuous (by fun_prop) hz
    exact ((hf.mul (Complex.continuous_im.comp (hc (μs n) inferInstance))).div_const _
      ).aestronglyMeasurable
  · exact (hfi.norm.mul_const _).div_const _
  · intro n
    refine Eventually.of_forall fun E => ?_
    have h1 := (norm_stieltjes_le (μs n) (hz E)).trans
      (div_le_div_of_nonneg_right (hM n) (hz E).le)
    have h2 : |(stieltjes (μs n) ((E : ℂ) + η * I)).im| ≤ M / η :=
      (Complex.abs_im_le_norm _).trans (by simpa using h1)
    rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    gcongr
  · refine Eventually.of_forall fun E => ?_
    have := tendsto_stieltjes_of_tendsto_on_dense hM hdense h (hz E)
    exact (((Complex.continuous_im.tendsto _).comp this).const_mul (f E)).div_const _

private theorem tendsto_integral_of_compactSupport_aux {M : ℝ} (hM : ∀ n, (μs n).real univ ≤ M)
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun n => ∫ t, f t ∂μs n) atTop (𝓝 (∫ t, f t ∂μ)) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  have hU := tendsto_poissonSmooth_uniformly (hfc.uniformContinuous_of_continuous hf)
    (C := C) (fun t => by simpa only [Real.norm_eq_abs] using hC t)
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  set K : ℝ := |M| + μ.real univ + 1 with hK
  have hK0 : 0 < K := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (3 * K) := by positivity
  obtain ⟨η, h1, hη⟩ := ((Metric.tendstoUniformly_iff.1 hU _ hδ).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have hη : 0 < η := hη
  have h1' : ∀ t, |(∫ x, f (t - x) * poissonKernel η x) - f t| ≤ ε / (3 * K) := fun t => by
    have := h1 t
    rw [dist_eq_norm, norm_sub_rev, Real.norm_eq_abs] at this
    exact this.le
  have hfν : ∀ ν : Measure ℝ, IsFiniteMeasure ν → Integrable f ν := fun ν _ =>
    hf.integrable_of_hasCompactSupport hfc
  have hgν : ∀ ν : Measure ℝ, IsFiniteMeasure ν →
      Integrable (fun t => ∫ x, f (t - x) * poissonKernel η x) ν := fun ν _ =>
    integrable_poissonSmooth ν hf hfi hη
  have hkey : ∀ ν : Measure ℝ, IsFiniteMeasure ν → ν.real univ ≤ K →
      |(∫ t, (∫ x, f (t - x) * poissonKernel η x) ∂ν) - ∫ t, f t ∂ν| ≤ ε / 3 := by
    intro ν _ hν
    refine (abs_integral_sub_le_aux ν (hfν ν inferInstance) (hgν ν inferInstance) h1').trans ?_
    calc ε / (3 * K) * ν.real univ ≤ ε / (3 * K) * K := by gcongr
      _ = ε / 3 := by field_simp
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (tendsto_integral_smooth_aux hM hdense h hf hfc hη) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 := hkey (μs n) inferInstance (by
    have := hM n
    have := le_abs_self M
    have := measureReal_nonneg (μ := μ) (s := univ)
    linarith)
  have hn2 := hkey μ inferInstance (by
    have := abs_nonneg M
    linarith)
  have hn3 := hN n hn
  rw [Real.dist_eq] at hn3 ⊢
  rw [abs_le] at hn1 hn2
  rw [abs_lt] at hn3 ⊢
  constructor <;> linarith [hn1.1, hn1.2, hn2.1, hn2.2, hn3.1, hn3.2]

private theorem integrable_of_abs_le_aux (ν : Measure ℝ) [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ t, |f t| ≤ C) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hC t)

private theorem exists_abs_lt_aux {f : ℝ → ℝ} (hf0 : Tendsto f (cocompact ℝ) (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∃ R : ℝ, ∀ t, R < |t| → |f t| < ε := by
  have h := Metric.tendsto_nhds.1 hf0 ε hε
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 h
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨R, fun t ht => ?_⟩
  have htK : t ∉ K := fun hm => by
    have := hR hm
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  have := hKs htK
  simpa only [mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs] using this

private theorem exists_abs_le_aux {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : Tendsto f (cocompact ℝ) (𝓝 0)) : ∃ C : ℝ, ∀ t, |f t| ≤ C := by
  obtain ⟨R, hR⟩ := exists_abs_lt_aux hf0 one_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 1, fun t => ?_⟩
  by_cases ht : R < |t|
  · exact (hR t ht).le.trans (le_max_right _ _)
  · rw [not_lt, abs_le] at ht
    exact (le_of_eq_of_le (Real.norm_eq_abs _).symm (hC t ht)).trans (le_max_left _ _)

theorem tendsto_integral_of_tendsto_stieltjes {M : ℝ} (hM : ∀ n, (μs n).real univ ≤ M)
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : Tendsto f (cocompact ℝ) (𝓝 0)) :
    Tendsto (fun n => ∫ t, f t ∂μs n) atTop (𝓝 (∫ t, f t ∂μ)) := by
  obtain ⟨C, hC⟩ := exists_abs_le_aux hf hf0
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  set K : ℝ := |M| + μ.real univ + 1 with hK
  have hK0 : 0 < K := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (3 * K) := by positivity
  obtain ⟨R, hR⟩ := exists_abs_lt_aux hf0 hδ
  obtain ⟨k, hk⟩ := exists_nat_ge R
  set g : ℝ → ℝ := fun t => f t * trapezoidCutoff k t with hg
  have hgc : Continuous g := hf.mul (continuous_trapezoidCutoff k)
  have hg1 : ∀ t, |f t - g t| ≤ ε / (3 * K) := fun t => by
    by_cases ht : (k : ℝ) < |t|
    · have h0 := trapezoidCutoff_nonneg k t
      have h1 := trapezoidCutoff_le_one k t
      have hft := hR t (hk.trans_lt ht)
      calc |f t - g t| = |f t| * (1 - trapezoidCutoff k t) := by
            rw [hg]; simp only
            rw [← mul_one_sub, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - trapezoidCutoff k t)]
        _ ≤ |f t| * 1 := by gcongr; linarith
        _ ≤ _ := by rw [mul_one]; exact hft.le
    · simp [hg, trapezoidCutoff_eq_one (not_lt.1 ht), hδ.le]
  have hfν : ∀ ν : Measure ℝ, IsFiniteMeasure ν → Integrable f ν := fun ν _ =>
    integrable_of_abs_le_aux ν hf hC
  have hgν : ∀ ν : Measure ℝ, IsFiniteMeasure ν → Integrable g ν := fun ν _ =>
    (hgc.integrable_of_hasCompactSupport (hasCompactSupport_mul_trapezoidCutoff k))
  have hkey : ∀ ν : Measure ℝ, IsFiniteMeasure ν → ν.real univ ≤ K →
      |(∫ t, f t ∂ν) - ∫ t, g t ∂ν| ≤ ε / 3 := by
    intro ν _ hν
    refine (abs_integral_sub_le_aux ν (hgν ν inferInstance) (hfν ν inferInstance) hg1).trans ?_
    calc ε / (3 * K) * ν.real univ ≤ ε / (3 * K) * K := by gcongr
      _ = ε / 3 := by field_simp
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (tendsto_integral_of_compactSupport_aux hM hdense h hgc
      (hasCompactSupport_mul_trapezoidCutoff k)) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 := hkey (μs n) inferInstance (by
    have := hM n
    have := le_abs_self M
    have := measureReal_nonneg (μ := μ) (s := univ)
    linarith)
  have hn2 := hkey μ inferInstance (by
    have := abs_nonneg M
    linarith)
  have hn3 := hN n hn
  rw [Real.dist_eq] at hn3 ⊢
  rw [abs_le] at hn1 hn2
  rw [abs_lt] at hn3 ⊢
  constructor <;> linarith [hn1.1, hn1.2, hn2.1, hn2.2, hn3.1, hn3.2]

private theorem integrable_cutoff_aux (ν : Measure ℝ) [IsFiniteMeasure ν] (k : ℕ) :
    Integrable (trapezoidCutoff k) ν :=
  integrable_of_abs_le_aux ν (continuous_trapezoidCutoff k) (C := 1) fun t => by
    rw [abs_of_nonneg (trapezoidCutoff_nonneg k t)]
    exact trapezoidCutoff_le_one k t

private theorem abs_integral_sub_cutoff_le_aux (ν : Measure ℝ) [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ t, |f t| ≤ C) (k : ℕ) :
    |(∫ t, f t ∂ν) - ∫ t, f t * trapezoidCutoff k t ∂ν| ≤
      C * (ν.real univ - ∫ t, trapezoidCutoff k t ∂ν) := by
  have hχ := integrable_cutoff_aux ν k
  have hfi := integrable_of_abs_le_aux ν hf hC
  have hfχ : Integrable (fun t => f t * trapezoidCutoff k t) ν :=
    integrable_of_abs_le_aux ν (hf.mul (continuous_trapezoidCutoff k)) (C := C) fun t => by
      rw [abs_mul, abs_of_nonneg (trapezoidCutoff_nonneg k t)]
      calc |f t| * trapezoidCutoff k t ≤ C * 1 :=
            mul_le_mul (hC t) (trapezoidCutoff_le_one k t) (trapezoidCutoff_nonneg k t)
              ((abs_nonneg _).trans (hC t))
        _ = C := mul_one C
  have hg : Integrable (fun t => C * (1 - trapezoidCutoff k t)) ν :=
    ((integrable_const (1 : ℝ)).sub hχ).const_mul C
  have h1 : ‖∫ t, (f t - f t * trapezoidCutoff k t) ∂ν‖ ≤
      ∫ t, C * (1 - trapezoidCutoff k t) ∂ν := by
    refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun t => ?_)
    have h0 := trapezoidCutoff_nonneg k t
    have h1 := trapezoidCutoff_le_one k t
    rw [Real.norm_eq_abs, ← mul_one_sub, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ 1 - trapezoidCutoff k t)]
    exact mul_le_mul_of_nonneg_right (hC t) (by linarith)
  have h2 : ∫ t, C * (1 - trapezoidCutoff k t) ∂ν =
      C * (ν.real univ - ∫ t, trapezoidCutoff k t ∂ν) := by
    rw [integral_const_mul, integral_sub (integrable_const _) hχ]
    simp
  rw [← integral_sub hfi hfχ]
  rw [← h2]
  simpa only [Real.norm_eq_abs] using h1

private theorem tendsto_integral_cutoff_aux (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Tendsto (fun k : ℕ => ∫ t, trapezoidCutoff k t ∂ν) atTop (𝓝 (ν.real univ)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun (k : ℕ) t => trapezoidCutoff k t) (f := fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    (fun k => (integrable_cutoff_aux ν k).aestronglyMeasurable) (integrable_const _)
    (fun k => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (trapezoidCutoff_nonneg k t)]
      exact trapezoidCutoff_le_one k t)
    (Eventually.of_forall fun t => by
      refine tendsto_atTop_of_eventually_const (i₀ := ⌈|t|⌉₊) fun k hk => ?_
      exact trapezoidCutoff_eq_one ((Nat.le_ceil _).trans (by exact_mod_cast hk)))
  simpa using h

theorem tendsto_integral_of_tendsto_stieltjes_of_bounded
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    (hmass : Tendsto (fun n => (μs n).real univ) atTop (𝓝 (μ.real univ)))
    {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ t, |f t| ≤ C) :
    Tendsto (fun n => ∫ t, f t ∂μs n) atTop (𝓝 (∫ t, f t ∂μ)) := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hmass).bddAbove
  have hM' : ∀ n, (μs n).real univ ≤ M := fun n => hM (mem_range_self n)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (4 * (C + 1)) := by positivity
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 (tendsto_integral_cutoff_aux μ)
    _ hδ).imp fun N hN => hN N le_rfl
  have hfχc : Continuous fun t => f t * trapezoidCutoff k t :=
    hf.mul (continuous_trapezoidCutoff k)
  have hCa : C * (μ.real univ - ∫ t, trapezoidCutoff k t ∂μ) ≤ ε / 4 := by
    rw [Real.dist_eq, abs_lt] at hk
    calc C * (μ.real univ - ∫ t, trapezoidCutoff k t ∂μ) ≤ C * (ε / (4 * (C + 1))) := by
          gcongr; linarith [hk.1]
      _ ≤ (C + 1) * (ε / (4 * (C + 1))) := by gcongr; linarith
      _ = ε / 4 := by field_simp
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1
    ((hmass.sub (tendsto_integral_of_compactSupport_aux hM' hdense h
      (continuous_trapezoidCutoff k) (by simpa using
        hasCompactSupport_mul_trapezoidCutoff k (g := fun _ => (1 : ℝ))))).const_mul C)
    (ε / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1
    (tendsto_integral_of_compactSupport_aux hM' hdense h hfχc
      (hasCompactSupport_mul_trapezoidCutoff k)) (ε / 4) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  have hA := abs_integral_sub_cutoff_le_aux (μs n) hf hC k
  have hB := abs_integral_sub_cutoff_le_aux μ hf hC k
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  rw [abs_le] at hA hB
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, h1.1, h1.2, h2.1, h2.2]


/-- The decreasing linear ramp: `1` on `(-∞, c - δ]`, `0` on `[c, ∞)`, linear in between. -/
noncomputable def linearRamp (c δ t : ℝ) : ℝ := max 0 (min 1 ((c - t) / δ))

theorem continuous_linearRamp (c δ : ℝ) : Continuous (linearRamp c δ) := by
  unfold linearRamp; fun_prop

theorem linearRamp_nonneg (c δ t : ℝ) : 0 ≤ linearRamp c δ t := le_max_left _ _

theorem linearRamp_le_one (c δ t : ℝ) : linearRamp c δ t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem linearRamp_eq_one {c δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ c - δ) : linearRamp c δ t = 1 := by
  unfold linearRamp
  have : 1 ≤ (c - t) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [min_eq_left this]
  exact max_eq_right zero_le_one

theorem linearRamp_eq_zero {c δ t : ℝ} (hδ : 0 < δ) (ht : c ≤ t) : linearRamp c δ t = 0 := by
  unfold linearRamp
  have : (c - t) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  exact max_eq_left (min_le_of_right_le this)

/-- The integral of the ramp is sandwiched between the masses of `Iic (c - δ)` and `Iic c`. -/
theorem integral_linearRamp_bounds (ν : Measure ℝ) [IsFiniteMeasure ν] {c δ : ℝ} (hδ : 0 < δ) :
    ν.real (Iic (c - δ)) ≤ ∫ t, linearRamp c δ t ∂ν ∧
      ∫ t, linearRamp c δ t ∂ν ≤ ν.real (Iic c) := by
  have hr : Integrable (linearRamp c δ) ν :=
    integrable_of_abs_le_aux ν (continuous_linearRamp c δ) (C := 1) fun t => by
      rw [abs_of_nonneg (linearRamp_nonneg c δ t)]; exact linearRamp_le_one c δ t
  constructor
  · rw [← integral_indicator_one measurableSet_Iic]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) hr fun t => ?_
    by_cases ht : t ≤ c - δ
    · simp [ht, linearRamp_eq_one hδ ht]
    · simp [ht, linearRamp_nonneg]
  · rw [← integral_indicator_one measurableSet_Iic]
    refine integral_mono hr ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) fun t => ?_
    by_cases ht : t ≤ c
    · simpa [ht] using linearRamp_le_one c δ t
    · simp [ht, linearRamp_eq_zero hδ (not_le.1 ht).le]

private theorem tendsto_real_Ioc_left (ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ) :
    Tendsto (fun r : ℝ => ν.real (Ioc (a - r) a)) (𝓝[>] 0) (𝓝 (ν.real {a})) := by
  have h := tendsto_measure_biInter_gt (μ := ν) (s := fun r : ℝ => Ioc (a - r) a) (a := 0)
    (fun r _ => measurableSet_Ioc.nullMeasurableSet)
    (fun i j _ hij => Ioc_subset_Ioc_left (by linarith)) ⟨1, one_pos, measure_ne_top _ _⟩
  have hI : (⋂ r > (0 : ℝ), Ioc (a - r) a) = {a} := by
    ext x
    simp only [mem_iInter, mem_Ioc, mem_singleton_iff]
    constructor
    · intro hx
      have h1 : x ≤ a := (hx 1 one_pos).2
      refine le_antisymm h1 (le_of_forall_pos_lt_add fun ε hε => ?_)
      linarith [(hx ε hε).1]
    · rintro rfl r hr
      exact ⟨by linarith, le_rfl⟩
  rw [hI] at h
  exact ((ENNReal.tendsto_toReal (measure_ne_top ν _)).comp h)

private theorem tendsto_real_Ioc_right (ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ) :
    Tendsto (fun r : ℝ => ν.real (Ioc a (a + r))) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_measure_biInter_gt (μ := ν) (s := fun r : ℝ => Ioc a (a + r)) (a := 0)
    (fun r _ => measurableSet_Ioc.nullMeasurableSet)
    (fun i j _ hij => Ioc_subset_Ioc_right (by linarith)) ⟨1, one_pos, measure_ne_top _ _⟩
  have hI : (⋂ r > (0 : ℝ), Ioc a (a + r)) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioc, mem_empty_iff_false, iff_false, not_forall]
    by_cases hx : a < x
    · exact ⟨(x - a) / 2, by linarith, fun h => by linarith [h.2]⟩
    · exact ⟨1, one_pos, fun h => hx h.1⟩
  rw [hI, measure_empty] at h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at h2
  exact h2

theorem tendsto_measure_Iic_of_tendsto_stieltjes
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    (hmass : Tendsto (fun n => (μs n).real univ) atTop (𝓝 (μ.real univ)))
    {E : ℝ} (hE : μ {E} = 0) :
    Tendsto (fun n => (μs n).real (Iic E)) atTop (𝓝 (μ.real (Iic E))) := by
  have hE0 : μ.real {E} = 0 := by simp [Measure.real, hE]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hL := (tendsto_real_Ioc_left μ E).eventually
    (Iio_mem_nhds (show μ.real {E} < ε / 2 by rw [hE0]; exact half_pos hε))
  have hR := (tendsto_real_Ioc_right μ E).eventually
    (Iio_mem_nhds (show (0 : ℝ) < ε / 2 from half_pos hε))
  obtain ⟨δ, ⟨hLδ, hRδ⟩, hδ⟩ := ((hL.and hR).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ))
    (a := 0))).exists
  have hδ : 0 < δ := hδ
  have hsplitL : μ.real (Iic E) = μ.real (Iic (E - δ)) + μ.real (Ioc (E - δ) E) := by
    rw [← measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Iic_union_Ioc_eq_Iic (by linarith)]
  have hsplitR : μ.real (Iic (E + δ)) = μ.real (Iic E) + μ.real (Ioc E (E + δ)) := by
    rw [← measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Iic_union_Ioc_eq_Iic (by linarith)]
  have hU := integral_linearRamp_bounds μ (c := E + δ) hδ
  have hL' := integral_linearRamp_bounds μ (c := E) hδ
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1
    (tendsto_integral_of_tendsto_stieltjes_of_bounded hdense h hmass
      (continuous_linearRamp (E + δ) δ) (C := 1) fun t => by
        rw [abs_of_nonneg (linearRamp_nonneg _ _ t)]; exact linearRamp_le_one _ _ t)
      (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1
    (tendsto_integral_of_tendsto_stieltjes_of_bounded hdense h hmass
      (continuous_linearRamp E δ) (C := 1) fun t => by
        rw [abs_of_nonneg (linearRamp_nonneg _ _ t)]; exact linearRamp_le_one _ _ t)
      (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  have hnU := integral_linearRamp_bounds (μs n) (c := E + δ) hδ
  have hnL := integral_linearRamp_bounds (μs n) (c := E) hδ
  rw [add_sub_cancel_right] at hnU
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hnU.1, hnL.2, hU.2, hL'.1]

end FroehlichSpencer.Infra
