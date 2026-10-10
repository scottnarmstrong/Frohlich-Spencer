/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.WaveSelection
import Mathlib.Tactic

/-!
# Real local factors and positivity on the clock law

* `clockF`: the clock local factor, which is real (`localFactor_clock_eq_ofReal`), bounded by one
  and continuous along the field.
* Positivity and comparison of renormalized products `∏ (1 + z f)` with `|z|, |f| ≤ 1`:
  `prod_one_add_mul_nonneg`, `abs_integral_mul_prod_le`, `integral_prod_mul_le_of_subset'`,
  `integral_prod_one_add_mul_pos`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Compact

open MeasureTheory Complex
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Reduction (gffCharacter)

/-! ### The real clock local factor -/

section LocalFactor

variable {E : Type*} [Fintype E]

/-- The clock local factor `F = localFactor w c b x θ` (FS81 (6.18)), which is real. -/
def clockF (β n : ℝ) (b x : E → ℝ) (θ : ℝ) : ℝ :=
  (localFactor (clockEdgeWeight β n) (clockShiftCost β n) b x θ).re

theorem localFactor_clock_eq_ofReal {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (b x : E → ℝ)
    (θ : ℝ) :
    localFactor (clockEdgeWeight β n) (clockShiftCost β n) b x θ = (clockF β n b x θ : ℂ) := by
  have hw := clockEdgeWeight_isCompactPeriodicWeight hβ hn
  have him := hw.localFactor_im_eq_zero b x (W := ∑ e, |b e|)
    (fun e => Finset.single_le_sum (fun e _ => abs_nonneg (b e)) (Finset.mem_univ e)) θ
  apply Complex.ext
  · simp [clockF]
  · simp [him]

theorem abs_clockF_le_one {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (b x : E → ℝ) (θ : ℝ) :
    |clockF β n b x θ| ≤ 1 := by
  have hw := clockEdgeWeight_isCompactPeriodicWeight hβ hn
  have h := hw.norm_localFactor_le_one b x (W := ∑ e, |b e|)
    (fun e => Finset.single_le_sum (fun e _ => abs_nonneg (b e)) (Finset.mem_univ e)) θ
  rw [localFactor_clock_eq_ofReal hβ hn, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem continuous_clockF {V : Type*} [Fintype V] (β n : ℝ) (G : Multigraph V E) (b : E → ℝ)
    (θ : (V → ℝ) → ℝ) (hθ : Continuous θ) :
    Continuous fun φ => clockF β n b (gradLinear G φ) (θ φ) := by
  unfold clockF localFactor normalizedEdgeRatio
  refine Complex.continuous_re.comp ?_
  have h1 := continuous_edgeRatio_clock β n b
  have h2 := continuous_edgeRatio_clock β n (-b)
  have hg : Continuous fun φ : V → ℝ => gradLinear G φ :=
    (gradLinear G).continuous_of_finiteDimensional
  have hθc : Continuous fun φ => ((θ φ : ℝ) : ℂ) := Complex.continuous_ofReal.comp hθ
  exact ((((continuous_const.mul hθc).cexp).mul ((h1.comp hg).mul continuous_const)).add
    (((continuous_const.mul hθc).neg.cexp).mul ((h2.comp hg).mul continuous_const))).div_const _

end LocalFactor

/-! ### Positivity of renormalized products -/

section Positivity

variable {V : Type*}

theorem prod_one_add_mul_nonneg {ι : Type*} (S : Finset ι) (z f : ι → ℝ)
    (hz : ∀ i ∈ S, |z i| ≤ 1) (hf : ∀ i ∈ S, |f i| ≤ 1) : 0 ≤ ∏ i ∈ S, (1 + z i * f i) :=
  Finset.prod_nonneg fun i hi => by
    have h3 : |z i * f i| ≤ 1 := by
      rw [abs_mul]
      calc |z i| * |f i| ≤ 1 * 1 := mul_le_mul (hz i hi) (hf i hi) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    linarith [(abs_le.1 h3).1]

theorem one_sub_abs_le_one_add_mul (z f : ℝ) (hf : |f| ≤ 1) : 1 - |z| ≤ 1 + z * f := by
  have h : |z * f| ≤ |z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hf
  linarith [(abs_le.1 h).1]

theorem integrable_prod_one_add_mul [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] (μ : Measure V) [IsFiniteMeasure μ] {ι : Type*} (S : Finset ι)
    (z : ι → ℝ) (f : ι → V → ℝ) (hf : ∀ i, Continuous (f i)) (hfb : ∀ i φ, |f i φ| ≤ 1) :
    Integrable (fun φ => ∏ i ∈ S, (1 + z i * f i φ)) μ := by
  refine Integrable.of_bound ((continuous_finsetProd _ fun i _ =>
    continuous_const.add (continuous_const.mul (hf i))).aestronglyMeasurable)
    (∏ i ∈ S, (1 + |z i|)) (ae_of_all _ fun φ => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  calc |1 + z i * f i φ| ≤ |1| + |z i * f i φ| := abs_add_le _ _
    _ ≤ 1 + |z i| := by
      rw [abs_one, abs_mul]
      have := hfb i φ
      nlinarith [abs_nonneg (z i)]

/-- `|∫ g ∏ (1 + z f) dμ| ≤ ∫ ∏ (1 + z f) dμ` for `|g| ≤ 1`, `|z| ≤ 1`, `|f| ≤ 1`. -/
theorem abs_integral_mul_prod_le [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] (μ : Measure V) [IsFiniteMeasure μ] {ι : Type*} (S : Finset ι)
    (z : ι → ℝ) (hz : ∀ i ∈ S, |z i| ≤ 1) (g : V → ℝ)
    (hgb : ∀ φ, |g φ| ≤ 1) (f : ι → V → ℝ) (hf : ∀ i, Continuous (f i))
    (hfb : ∀ i φ, |f i φ| ≤ 1) :
    |∫ φ, g φ * ∏ i ∈ S, (1 + z i * f i φ) ∂μ| ≤ ∫ φ, ∏ i ∈ S, (1 + z i * f i φ) ∂μ := by
  have hint := integrable_prod_one_add_mul μ S z f hf hfb
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (ae_of_all _ fun φ => abs_nonneg _) hint (ae_of_all _ fun φ => ?_))
  have hP := prod_one_add_mul_nonneg S z (fun i => f i φ) hz fun i _ => hfb i φ
  simp only
  rw [abs_mul, abs_of_nonneg hP]
  exact mul_le_of_le_one_left hP (hgb φ)

/-- The dropped factors of a subproduct cost at most `∏ (1 − |z|)` (FS81 (5.35)). -/
theorem integral_prod_mul_le_of_subset' [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] (μ : Measure V) [IsFiniteMeasure μ] {ι : Type*} [DecidableEq ι]
    {S S' : Finset ι} (hSS' : S ⊆ S') (z : ι → ℝ) (hz : ∀ i ∈ S', |z i| ≤ 1)
    (f : ι → V → ℝ) (hf : ∀ i, Continuous (f i)) (hfb : ∀ i φ, |f i φ| ≤ 1) :
    (∏ i ∈ S' \ S, (1 - |z i|)) * ∫ φ, ∏ i ∈ S, (1 + z i * f i φ) ∂μ ≤
      ∫ φ, ∏ i ∈ S', (1 + z i * f i φ) ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono ((integrable_prod_one_add_mul μ S z f hf hfb).const_mul _)
    (integrable_prod_one_add_mul μ S' z f hf hfb) fun φ => ?_
  simp only
  rw [← Finset.prod_sdiff hSS']
  have hP := prod_one_add_mul_nonneg S z (fun i => f i φ) (fun i hi => hz i (hSS' hi))
    fun i _ => hfb i φ
  refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun i hi => ?_) fun i _ =>
    one_sub_abs_le_one_add_mul _ _ (hfb i φ)) hP
  have := hz i (Finset.mem_sdiff.1 hi).1
  linarith

theorem integral_prod_one_add_mul_pos [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] (μ : Measure V) [IsProbabilityMeasure μ] {ι : Type*}
    (S : Finset ι) (z : ι → ℝ) (hz : ∀ i ∈ S, |z i| < 1) (f : ι → V → ℝ)
    (hf : ∀ i, Continuous (f i)) (hfb : ∀ i φ, |f i φ| ≤ 1) :
    0 < ∫ φ, ∏ i ∈ S, (1 + z i * f i φ) ∂μ := by
  have hpos : 0 < ∏ i ∈ S, (1 - |z i|) := Finset.prod_pos fun i hi => by
    have := hz i hi
    linarith
  calc (0 : ℝ) < ∫ _φ, ∏ i ∈ S, (1 - |z i|) ∂μ := by
        rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
        exact hpos
    _ ≤ _ := integral_mono (integrable_const _)
        (integrable_prod_one_add_mul μ S z f hf hfb) fun φ =>
          Finset.prod_le_prod₀ (fun i hi => by have := hz i hi; linarith) fun i _ =>
            one_sub_abs_le_one_add_mul _ _ (hfb i φ)

end Positivity

/-! ### The real translation identity -/

section RealTranslation

variable {V : Type*} [Fintype V] {E : Type*} [Fintype E]

/-- **The translation step on the clock law, in real form**: with `f_i = clockF …` the real
local factors, `∫ ∏ (A_i + B_i cos θ_i) dμ = ∫ ∏ (A_i + B_i e^{−E_c(a_i, ϱ_i)} f_i) dμ`. -/
theorem integral_prod_add_mul_cos_clockLaw_real {n β : ℝ} (hn : 0 < n) (hβ : 0 ≤ β)
    (G : Multigraph V E) {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (hcomp : ∀ i, IsClockCompatible n (ϱ i)) (A B s : ι → ℝ) (a : ι → V → ℝ)
    (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, G.grad (a i) e = 0 ∨ G.grad (a i') e = 0) :
    ∫ φ, ∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) ∂clockLaw β n G =
      ∫ φ, ∏ i, (A i +
        B i * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear G) (a i) (ϱ i)) *
          clockF β n (gradLinear G (a i)) (gradLinear G φ) (∑ j, φ j * ϱ i j + s i))
        ∂clockLaw β n G := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal,
    integral_prod_add_mul_cos_clockLaw hn hβ G ϱ hcomp A B s a horth hdisj]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  simp only
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [localFactor_clock_eq_ofReal hβ hn]
  push_cast
  ring

/-- **The neutral part with a compatible composite factor** (KP §2.3.1, Step 1, on the clock law):
for a compatible real neutral `ρ` and a family `R` with at most one non-neutral member,
`∫ cos⟨φ, ρ⟩ ∏_R (1 + K cos) dμ = ∫ cos⟨φ, ρ⟩ ∏_{R₀} (1 + K cos) dμ`. -/
theorem clockLaw_integral_cos_mul_prod_eq_neutralPart {n : ℕ} (hn : 0 < n) {β : ℝ}
    (hβ : 0 ≤ β) (G : Multigraph V E) (R : Finset (V → ℤ))
    (hRa : ∀ ϱ₁ ∈ R, ∀ ϱ₂ ∈ R, ∑ j, ϱ₁ j ≠ 0 → ∑ j, ϱ₂ j ≠ 0 → ϱ₁ = ϱ₂) (K : (V → ℤ) → ℝ)
    (ρ : V → ℝ) (hρc : IsClockCompatible (n : ℝ) ρ) (hρ : ∑ j, ρ j = 0) :
    ∫ φ, Real.cos (∑ j, φ j * ρ j) * ∏ m ∈ R, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ)))
        ∂clockLaw β n G =
      ∫ φ, Real.cos (∑ j, φ j * ρ j) *
        ∏ m ∈ neutralPart R, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂clockLaw β n G := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hμ := isProbabilityMeasure_clockLaw G hβ hn'
  set P := neutralPart R with hPdef
  have hPneutral : ∀ ϱ ∈ P, ∑ j, ϱ j = 0 := fun ϱ hϱ => (mem_neutralPart.mp hϱ).2
  by_cases hch : ∃ ϱc ∈ R, ∑ j, ϱc j ≠ 0
  · obtain ⟨ϱc, hϱc, hne⟩ := hch
    have hcP : ϱc ∉ P := fun h => hne (hPneutral ϱc h)
    have hR : R = insert ϱc P := by
      ext ϱ
      simp only [Finset.mem_insert, hPdef, mem_neutralPart]
      constructor
      · intro hϱ
        by_cases h0 : ∑ j, ϱ j = 0
        · exact Or.inr ⟨hϱ, h0⟩
        · exact Or.inl (hRa ϱ hϱ ϱc hϱc h0 hne)
      · rintro (rfl | ⟨hϱ, _⟩)
        · exact hϱc
        · exact hϱ
    -- the rest, as a product over `Option P`
    set Rest : (V → ℝ) → ℝ := fun φ => Real.cos (∑ j, φ j * ρ j) *
      ∏ m ∈ P, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) with hRest
    have hRestO : ∀ φ : V → ℝ, Rest φ = ∏ o : Option P,
        (Option.elim o 0 (fun _ => 1) + Option.elim o 1 (fun m => K m) *
          Real.cos (∑ j, φ j * Option.elim o ρ (fun m j => ((m : V → ℤ) j : ℝ)) j + 0)) := by
      intro φ
      simp only [hRest]
      rw [Fintype.prod_option]
      simp only [Option.elim, zero_add, one_mul, add_zero]
      rw [← Finset.prod_coe_sort P]
    have hcompO : ∀ o : Option P,
        IsClockCompatible (n : ℝ) (Option.elim o ρ (fun m j => ((m : V → ℤ) j : ℝ))) := by
      intro o
      rcases o with _ | m
      · exact hρc
      · exact isClockCompatible_intCast n _
    have hneuO : ∀ o : Option P, ∑ j, Option.elim o ρ (fun m j => ((m : V → ℤ) j : ℝ)) j = 0 := by
      intro o
      rcases o with _ | m
      · exact hρ
      · simp only [Option.elim]
        exact_mod_cast hPneutral m m.2
    have hzero : ∀ τ : V → ℝ, IsClockCompatible (n : ℝ) τ → ∑ j, τ j ≠ 0 →
        ∫ φ, gffCharacter τ φ * ((Rest φ : ℝ) : ℂ) ∂clockLaw β n G = 0 := by
      intro τ hτc hτ
      simp_rw [hRestO]
      exact integral_character_mul_prod_clockLaw_eq_zero hn' hβ G τ hτc hτ _ hcompO hneuO _ _ _
    have hRest_cont : Continuous Rest := by
      simp only [hRest]
      exact (by fun_prop : Continuous fun φ : V → ℝ => Real.cos (∑ j, φ j * ρ j)).mul
        (continuous_finsetProd _ fun ϱ _ => by fun_prop)
    have hRest_bdd : ∀ φ, |Rest φ| ≤ ∏ m ∈ P, (1 + |K m|) := by
      intro φ
      simp only [hRest]
      rw [abs_mul]
      have h1 := Real.abs_cos_le_one (∑ j, φ j * ρ j)
      have h2 := norm_prod_one_add_mul_cos_le P K (fun m => ∑ j, φ j * (m j : ℝ))
      rw [Complex.norm_real, Real.norm_eq_abs] at h2
      have h3 : 0 ≤ ∏ m ∈ P, (1 + |K m|) := Finset.prod_nonneg fun m _ => by positivity
      nlinarith [abs_nonneg (∏ m ∈ P, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))))]
    have hintχ : ∀ τ : V → ℝ, Integrable
        (fun φ => gffCharacter τ φ * ((Rest φ : ℝ) : ℂ)) (clockLaw β n G) :=
      fun τ => Integrable.of_bound
        (((Reduction.continuous_gffCharacter _).mul
          (Complex.continuous_ofReal.comp hRest_cont)).aestronglyMeasurable)
        (∏ m ∈ P, (1 + |K m|)) (Filter.Eventually.of_forall fun φ => by
          rw [norm_mul, Reduction.norm_gffCharacter, one_mul, Complex.norm_real,
            Real.norm_eq_abs]
          exact hRest_bdd φ)
    have hpt : ∀ φ : V → ℝ, ((Real.cos (∑ j, φ j * ρ j) *
        ∏ m ∈ R, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) : ℝ) : ℂ) =
        ((Rest φ : ℝ) : ℂ) + ((K ϱc / 2 : ℝ) : ℂ) *
          (gffCharacter (fun j => (ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ) +
            gffCharacter (fun j => -(ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ)) := by
      intro φ
      have hc1 : gffCharacter (fun j => (ϱc j : ℝ)) φ =
          Complex.exp (I * ((∑ j, φ j * (ϱc j : ℝ) : ℝ) : ℂ)) := by
        unfold gffCharacter; congr 1; push_cast; ring
      have hc2 : gffCharacter (fun j => -(ϱc j : ℝ)) φ =
          Complex.exp (-(I * ((∑ j, φ j * (ϱc j : ℝ) : ℝ) : ℂ))) := by
        unfold gffCharacter; congr 1
        push_cast
        rw [← mul_neg, ← Finset.sum_neg_distrib]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
      have hcos : ((Real.cos (∑ j, φ j * (ϱc j : ℝ)) : ℝ) : ℂ) =
          (gffCharacter (fun j => (ϱc j : ℝ)) φ + gffCharacter (fun j => -(ϱc j : ℝ)) φ) / 2 := by
        rw [hc1, hc2, Complex.ofReal_cos, Complex.cos]
        generalize ((∑ j, φ j * (ϱc j : ℝ) : ℝ) : ℂ) = θ₀
        congr 2 <;> congr 1 <;> ring
      rw [hR, Finset.prod_insert hcP]
      simp only [hRest]
      generalize Real.cos (∑ j, φ j * (ϱc j : ℝ)) = c at hcos ⊢
      generalize gffCharacter (fun j => (ϱc j : ℝ)) φ = χ₁ at hcos ⊢
      generalize gffCharacter (fun j => -(ϱc j : ℝ)) φ = χ₂ at hcos ⊢
      push_cast
      rw [hcos]
      ring
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    simp_rw [hpt]
    have hint₀ : Integrable (fun φ => ((Rest φ : ℝ) : ℂ)) (clockLaw β n G) :=
      Integrable.of_bound (Complex.continuous_ofReal.comp hRest_cont).aestronglyMeasurable
        _ (Filter.Eventually.of_forall fun φ => by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact hRest_bdd φ)
    have hA := hintχ fun j => (ϱc j : ℝ)
    have hB := hintχ fun j => -(ϱc j : ℝ)
    have hAB : Integrable (fun φ => ((K ϱc / 2 : ℝ) : ℂ) *
        (gffCharacter (fun j => (ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ) +
          gffCharacter (fun j => -(ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ))) (clockLaw β n G) :=
      (hA.add hB).const_mul _
    have hz₁ := hzero (fun j => (ϱc j : ℝ)) (isClockCompatible_intCast n ϱc)
      (by exact_mod_cast hne)
    have hz₂ := hzero (fun j => -(ϱc j : ℝ))
      (by
        intro j
        obtain ⟨k, hk⟩ := isClockCompatible_intCast n ϱc j
        exact ⟨-k, by push_cast; rw [← hk]; ring⟩)
      (by
        rw [Finset.sum_neg_distrib, neg_ne_zero]
        exact_mod_cast hne)
    rw [integral_add hint₀ hAB, integral_const_mul, integral_add hA hB, hz₁, hz₂]
    simp [hRest]
  · push Not at hch
    have hR : R = P := by
      ext ϱ
      simp only [hPdef, mem_neutralPart]
      exact ⟨fun h => ⟨h, hch ϱ h⟩, fun h => h.1⟩
    rw [hR]

end RealTranslation

end FroehlichSpencer.BKT.Clock.Compact

end
