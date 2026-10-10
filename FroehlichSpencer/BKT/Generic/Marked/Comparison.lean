/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.EnsembleSelection
public import FroehlichSpencer.BKT.Reduction.SpinWaveTranslation
import Mathlib.Tactic

/-!
# Positivity, comparison and translation of marked terms

The analytic lemmas of the marked T1.6 assembly (FS81 (5.30)–(5.35), CG.s5).

* **Positivity and comparison.** For products `∏ (1 + z cos)` with `|z| ≤ 1`:
  - `abs_integral_cos_mul_prod_le` bounds a marked term by its remainder;
  - `integral_prod_mul_le_of_subset` compares a subproduct with the full product, where the
    dropped factors cost `∏ (1 − |z|)`;
  - `integral_prod_pos` gives a positive integral.
* **Neutral part and charged composites.**
  - `gffLaw_integral_cos_mul_prod_eq_neutralPart` is KP §2.3.1, Step 1, with an extra real
    neutral factor `cos⟨φ, ρ⟩`.
  - `gffLaw_integral_cos_charged_mul_eq_zero`: a composite whose integer part is charged
    integrates to zero (the constant mode).
* **`gffLaw_integral_cos_mul_prod_translation`**: KP's complex translation for neutral real
  densities with one extra composite factor `cos⟨φ, ρ⟩`. It is derived from
  `Reduction.gffLaw_integral_prod_spinWave_translation` on `Option ι`, leaving the coefficient of
  the composite factor free.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Marked

open MeasureTheory Reduction

/-! ### Positivity and comparison of renormalized products -/

section Positivity

variable {V : Type*} [Fintype V]

/-- A product of factors `1 + z_i cos θ_i` with `|z_i| ≤ 1` is nonnegative. -/
theorem prod_one_add_mul_cos_nonneg {ι : Type*} (S : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ S, |z i| ≤ 1) (θ : ι → ℝ) : 0 ≤ ∏ i ∈ S, (1 + z i * Real.cos (θ i)) :=
  Finset.prod_nonneg fun i hi => by
    have h1 := abs_le.1 (hz i hi)
    have h2 := Real.abs_cos_le_one (θ i)
    have h3 : |z i * Real.cos (θ i)| ≤ 1 := by
      rw [abs_mul]
      calc |z i| * |Real.cos (θ i)| ≤ 1 * 1 := mul_le_mul (hz i hi) h2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    linarith [(abs_le.1 h3).1]

/-- Each factor `1 + z cos θ` is at least `1 - |z|`. -/
theorem one_sub_abs_le_one_add_mul_cos (z θ : ℝ) : 1 - |z| ≤ 1 + z * Real.cos θ := by
  have h : |z * Real.cos θ| ≤ |z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  linarith [(abs_le.1 h).1]

/-- **The marked term against the renormalized remainder** (positivity, FS81 (5.34)): with
`|z_i| ≤ 1`, `|∫ cos θ₀ ∏_i (1 + z_i cos θ_i) dμ| ≤ ∫ ∏_i (1 + z_i cos θ_i) dμ`. -/
theorem abs_integral_cos_mul_prod_le (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] {ι : Type*}
    (S : Finset ι) (z : ι → ℝ) (hz : ∀ i ∈ S, |z i| ≤ 1) (θ₀ : (V → ℝ) → ℝ)
    (θ : ι → (V → ℝ) → ℝ) (hθ : ∀ i, Continuous (θ i)) :
    |∫ φ, Real.cos (θ₀ φ) * ∏ i ∈ S, (1 + z i * Real.cos (θ i φ)) ∂μ| ≤
      ∫ φ, ∏ i ∈ S, (1 + z i * Real.cos (θ i φ)) ∂μ := by
  have hint := Reduction.integrable_prod_one_add_mul_cos μ S z θ hθ
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (ae_of_all _ fun φ => abs_nonneg _) hint (ae_of_all _ fun φ => ?_))
  have hP := prod_one_add_mul_cos_nonneg S z hz (fun i => θ i φ)
  simp only
  rw [abs_mul, abs_of_nonneg hP]
  exact mul_le_of_le_one_left hP (Real.abs_cos_le_one _)

/-- **Comparison of a subproduct with the full product** (FS81 (5.35), the dropped factors):
for `S ⊆ S'` and `|z_i| ≤ 1` on `S'`,
`∏_{S' ∖ S} (1 - |z_i|) · ∫ ∏_S (1 + z cos) dμ ≤ ∫ ∏_{S'} (1 + z cos) dμ`. -/
theorem integral_prod_mul_le_of_subset (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] {ι : Type*}
    [DecidableEq ι] {S S' : Finset ι} (hSS' : S ⊆ S') (z : ι → ℝ)
    (hz : ∀ i ∈ S', |z i| ≤ 1) (θ : ι → (V → ℝ) → ℝ) (hθ : ∀ i, Continuous (θ i)) :
    (∏ i ∈ S' \ S, (1 - |z i|)) * ∫ φ, ∏ i ∈ S, (1 + z i * Real.cos (θ i φ)) ∂μ ≤
      ∫ φ, ∏ i ∈ S', (1 + z i * Real.cos (θ i φ)) ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono (((Reduction.integrable_prod_one_add_mul_cos μ S z θ hθ).const_mul _))
    (Reduction.integrable_prod_one_add_mul_cos μ S' z θ hθ) fun φ => ?_
  simp only
  rw [← Finset.prod_sdiff hSS']
  have hP := prod_one_add_mul_cos_nonneg S z (fun i hi => hz i (hSS' hi)) (fun i => θ i φ)
  refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun i hi => ?_) fun i _ =>
    one_sub_abs_le_one_add_mul_cos _ _) hP
  have := hz i (Finset.mem_sdiff.1 hi).1
  linarith

/-- The renormalized product with `|z_i| < 1` has positive integral against a probability
measure. -/
theorem integral_prod_pos (μ : Measure (V → ℝ)) [IsProbabilityMeasure μ] {ι : Type*}
    (S : Finset ι) (z : ι → ℝ) (hz : ∀ i ∈ S, |z i| < 1) (θ : ι → (V → ℝ) → ℝ)
    (hθ : ∀ i, Continuous (θ i)) :
    0 < ∫ φ, ∏ i ∈ S, (1 + z i * Real.cos (θ i φ)) ∂μ := by
  have hpos : 0 < ∏ i ∈ S, (1 - |z i|) := Finset.prod_pos fun i hi => by
    have := hz i hi
    linarith
  calc (0 : ℝ) < ∫ _φ, ∏ i ∈ S, (1 - |z i|) ∂μ := by
        rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
        exact hpos
    _ ≤ _ := integral_mono (integrable_const _)
        (Reduction.integrable_prod_one_add_mul_cos μ S z θ hθ) fun φ =>
          Finset.prod_le_prod₀ (fun i hi => by have := hz i hi; linarith) fun i _ =>
            one_sub_abs_le_one_add_mul_cos _ _

end Positivity

/-! ### The neutral part with a real composite factor -/

section Neutral

variable {V : Type*} {E : Type*} [Fintype V] [Fintype E]

/-- The cosine of a real neutral density is shift invariant. -/
theorem gffShiftInvariant_cos_neutral (ρ : V → ℝ) (hρ : ∑ j, ρ j = 0) (s : ℝ) :
    GffShiftInvariant fun φ : V → ℝ => Real.cos (∑ j, φ j * ρ j + s) := by
  intro φ c
  have hshift : ∑ j, (φ j + c) * ρ j = ∑ j, φ j * ρ j := by
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hρ, mul_zero, add_zero]
  simp only [hshift]

/-- KP §2.3.1, Step 1, with an extra real neutral factor: for an ensemble with at most one
non-neutral density, `∫ cos⟨φ, ρ⟩ ∏_N (1 + K cos) dμ = ∫ cos⟨φ, ρ⟩ ∏_{N₀} (1 + K cos) dμ`. -/
theorem gffLaw_integral_cos_mul_prod_eq_neutralPart [DecidableEq V] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (N : Finset (V → ℤ))
    (hN : ∀ ρ₁ ∈ N, ∀ ρ₂ ∈ N, ∑ j, ρ₁ j ≠ 0 → ∑ j, ρ₂ j ≠ 0 → ρ₁ = ρ₂)
    (K : (V → ℤ) → ℝ) (ρ : V → ℝ) (hρ : ∑ j, ρ j = 0) :
    ∫ φ, Real.cos (∑ j, φ j * ρ j) *
        ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂gffLaw G hG β hβ v =
      ∫ φ, Real.cos (∑ j, φ j * ρ j) *
        ∏ m ∈ neutralPart N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ)))
          ∂gffLaw G hG β hβ v := by
  classical
  by_cases hall : ∀ m ∈ N, ∑ j, m j = 0
  · rw [neutralPart_eq_self hall]
  simp only [not_forall, exists_prop] at hall
  obtain ⟨ρc, hρc, hQc⟩ := hall
  have hN₀ : neutralPart N = N.erase ρc :=
    neutralPart_eq_erase hQc fun m hm hQ => hN m hm ρc hρc hQ hQc
  set F : (V → ℝ) → ℝ := fun φ => Real.cos (∑ j, φ j * ρ j) *
    ∏ m ∈ N.erase ρc, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) with hF
  have hsplit : ∀ φ : V → ℝ, Real.cos (∑ j, φ j * ρ j) *
      ∏ m ∈ N, (1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))) =
        (1 + K ρc * Real.cos (∑ j, φ j * (ρc j : ℝ) + 0)) * F φ := by
    intro φ
    rw [hF, add_zero, ← Finset.mul_prod_erase N _ hρc]
    ring
  rw [hN₀]
  simp_rw [hsplit]
  have hneutral : ∀ m ∈ N.erase ρc, ∑ j, m j = 0 := by
    intro m hm
    by_contra hQ
    exact (Finset.mem_erase.mp hm).1 (hN m (Finset.mem_erase.mp hm).2 ρc hρc hQ hQc)
  have hFcont : Continuous F := by
    simp only [hF]
    fun_prop
  have hFbound : ∀ φ, |F φ| ≤ ∏ m ∈ N.erase ρc, (1 + |K m|) := by
    intro φ
    simp only [hF]
    rw [abs_mul, Finset.abs_prod]
    refine (mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      (Real.abs_cos_le_one _)).trans ?_
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun m _ => ?_
    calc |1 + K m * Real.cos (∑ j, φ j * (m j : ℝ))|
        ≤ |(1 : ℝ)| + |K m * Real.cos (∑ j, φ j * (m j : ℝ))| := abs_add_le _ _
      _ ≤ 1 + |K m| := by
        rw [abs_one, abs_mul]
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hFshift : GffShiftInvariant F := by
    intro φ c
    have h1 := gffShiftInvariant_cos_neutral ρ hρ 0 φ c
    have h2 := gffShiftInvariant_prod_neutral (N.erase ρc) hneutral K (fun _ => 0) φ c
    simp only [add_zero] at h1 h2
    simp only [hF, h1, h2]
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  have hFint : Integrable F (gffLaw G hG β hβ v) :=
    Integrable.of_bound hFcont.aestronglyMeasurable _
      (ae_of_all _ fun φ => (Real.norm_eq_abs _).le.trans (hFbound φ))
  have hcosint : Integrable
      (fun φ : V → ℝ => Real.cos (∑ j, φ j * (ρc j : ℝ) + 0) * F φ)
      (gffLaw G hG β hβ v) :=
    hFint.bdd_mul (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun φ => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
  have hzero := gffLaw_integral_cos_charge_mul_eq_zero G hG β hβ v ρc hQc 0 F hFshift
    hFcont.measurable _ hFbound
  calc ∫ φ, (1 + K ρc * Real.cos (∑ j, φ j * (ρc j : ℝ) + 0)) * F φ ∂gffLaw G hG β hβ v
      = ∫ φ, (F φ + K ρc * (Real.cos (∑ j, φ j * (ρc j : ℝ) + 0) * F φ))
          ∂gffLaw G hG β hβ v := by
        refine integral_congr_ae (ae_of_all _ fun φ => ?_)
        ring
    _ = ∫ φ, F φ ∂gffLaw G hG β hβ v := by
        rw [integral_add hFint (hcosint.const_mul _), integral_const_mul, hzero, mul_zero,
          add_zero]

/-- **A charged composite integrates to zero.** If the integer part `σ` of a composite
`σ + τ` (with `τ` real and neutral) is non-neutral, then
`∫ cos(⟨φ, σ⟩ + ⟨φ, τ⟩) F dμ = 0` for every bounded continuous shift-invariant `F`. -/
theorem gffLaw_integral_cos_charged_mul_eq_zero [DecidableEq V] (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (σ : V → ℤ)
    (hσ : ∑ j, σ j ≠ 0) (τ : V → ℝ) (hτ : ∑ j, τ j = 0) (F : (V → ℝ) → ℝ)
    (hFshift : GffShiftInvariant F) (hFcont : Continuous F) (C : ℝ) (hFbound : ∀ φ, |F φ| ≤ C) :
    ∫ φ, Real.cos (∑ j, φ j * (σ j : ℝ) + ∑ j, φ j * τ j) * F φ ∂gffLaw G hG β hβ v = 0 := by
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  set F₁ : (V → ℝ) → ℝ := fun φ => Real.cos (∑ j, φ j * τ j) * F φ with hF₁
  set F₂ : (V → ℝ) → ℝ := fun φ => Real.sin (∑ j, φ j * τ j) * F φ with hF₂
  have hτshift : ∀ φ : V → ℝ, ∀ c : ℝ, ∑ j, (φ j + c) * τ j = ∑ j, φ j * τ j := by
    intro φ c
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hτ, mul_zero, add_zero]
  have hF₁shift : GffShiftInvariant F₁ := fun φ c => by
    simp only [hF₁, hτshift, hFshift φ c]
  have hF₂shift : GffShiftInvariant F₂ := fun φ c => by
    simp only [hF₂, hτshift, hFshift φ c]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hFbound 0)
  have hF₁bound : ∀ φ, |F₁ φ| ≤ C := fun φ => by
    simp only [hF₁, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans (hFbound φ)
  have hF₂bound : ∀ φ, |F₂ φ| ≤ C := fun φ => by
    simp only [hF₂, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)).trans (hFbound φ)
  have h1 := gffLaw_integral_cos_charge_mul_eq_zero G hG β hβ v σ hσ 0 F₁ hF₁shift
    (by simp only [hF₁]; fun_prop) C hF₁bound
  have h2 := gffLaw_integral_cos_charge_mul_eq_zero G hG β hβ v σ hσ (-(Real.pi / 2)) F₂
    hF₂shift (by simp only [hF₂]; fun_prop) C hF₂bound
  have hint : ∀ (s : ℝ) (F' : (V → ℝ) → ℝ), Continuous F' → (∀ φ, |F' φ| ≤ C) →
      Integrable (fun φ : V → ℝ => Real.cos (∑ j, φ j * (σ j : ℝ) + s) * F' φ)
        (gffLaw G hG β hβ v) := by
    intro s F' hF' hbd
    refine Integrable.of_bound (by fun_prop : Continuous fun φ : V → ℝ =>
      Real.cos (∑ j, φ j * (σ j : ℝ) + s) * F' φ).aestronglyMeasurable C
      (ae_of_all _ fun φ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans (hbd φ)
  have hpt : ∀ φ : V → ℝ, Real.cos (∑ j, φ j * (σ j : ℝ) + ∑ j, φ j * τ j) * F φ =
      Real.cos (∑ j, φ j * (σ j : ℝ) + 0) * F₁ φ -
        Real.cos (∑ j, φ j * (σ j : ℝ) + -(Real.pi / 2)) * F₂ φ := by
    intro φ
    simp only [hF₁, hF₂, add_zero, Real.cos_add, ← sub_eq_add_neg, Real.cos_sub_pi_div_two]
    ring
  simp_rw [hpt]
  rw [integral_sub (hint 0 F₁ (by simp only [hF₁]; fun_prop) hF₁bound)
    (hint _ F₂ (by simp only [hF₂]; fun_prop) hF₂bound), h1, h2, sub_zero]

end Neutral

/-! ### The marked translation identity -/

section Translation

variable {V : Type*} {E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Translation of a marked term** (KP §2.3.3 with one extra real neutral density): for
mutually orthogonal waves `a₀` (for the composite `ρ`) and `a_i` (for the `ϱ_i`),
1. `∫ ∏_i (1 + K_i cos⟨φ, ϱ_i⟩) dμ = ∫ ∏_i (1 + K_i e^{-E_i} cos⟨φ, ϱ_i + βΔa_i⟩) dμ`, and
2. `∫ cos⟨φ, ρ⟩ ∏_i (…) dμ = e^{-E₀} ∫ cos⟨φ, ρ + βΔa₀⟩ ∏_i (1 + K_i e^{-E_i} cos …) dμ`,
with `E = E_β(a, ·)` KP's (2.12). Both follow from `gffLaw_integral_prod_spinWave_translation`
on `Option ι`, the coefficient of the composite factor being free. -/
theorem gffLaw_integral_cos_mul_prod_translation (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ρ a₀ : V → ℝ) (hρ : ∑ j, ρ j = 0) (ϱ : ι → V → ℝ)
    (hneutral : ∀ i, ∑ j, ϱ i j = 0) (K : ι → ℝ) (a : ι → V → ℝ)
    (h0i : ∀ i, Multigraph.pairing a₀ (ϱ i) = 0) (hi0 : ∀ i, Multigraph.pairing (a i) ρ = 0)
    (horth₁ : ∀ i i', i ≠ i' → Multigraph.pairing (a i) (ϱ i') = 0)
    (h0Δ : ∀ i, Multigraph.pairing a₀ (G.laplacian (a i)) = 0)
    (horth₂ : ∀ i i', i ≠ i' → Multigraph.pairing (a i) (G.laplacian (a i')) = 0) :
    (∫ φ, ∏ i, (1 + K i * Real.cos (∑ j, φ j * ϱ i j)) ∂gffLaw G hG β hβ v =
      ∫ φ, ∏ i, (1 + K i * Real.exp (-gffTranslationEnergy G β (a i) (ϱ i)) *
          Real.cos (∑ j, φ j * (ϱ i j + β * G.laplacian (a i) j))) ∂gffLaw G hG β hβ v) ∧
    ∫ φ, Real.cos (∑ j, φ j * ρ j) * ∏ i, (1 + K i * Real.cos (∑ j, φ j * ϱ i j))
        ∂gffLaw G hG β hβ v =
      Real.exp (-gffTranslationEnergy G β a₀ ρ) *
        ∫ φ, Real.cos (∑ j, φ j * (ρ j + β * G.laplacian a₀ j)) *
          ∏ i, (1 + K i * Real.exp (-gffTranslationEnergy G β (a i) (ϱ i)) *
            Real.cos (∑ j, φ j * (ϱ i j + β * G.laplacian (a i) j))) ∂gffLaw G hG β hβ v := by
  classical
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  set μ := gffLaw G hG β hβ v with hμ
  -- the family on `Option ι`
  set ϱ' : Option ι → V → ℝ := fun o => Option.elim o ρ ϱ with hϱ'
  set a' : Option ι → V → ℝ := fun o => Option.elim o a₀ a with ha'
  have hn' : ∀ o, ∑ j, ϱ' o j = 0 := fun o => by
    rcases o with _ | i
    · exact hρ
    · exact hneutral i
  have ho₁ : ∀ o o', o ≠ o' → Multigraph.pairing (a' o) (ϱ' o') = 0 := by
    intro o o' hne
    rcases o with _ | i <;> rcases o' with _ | i'
    · exact absurd rfl hne
    · exact h0i i'
    · exact hi0 i
    · exact horth₁ i i' fun h => hne (by rw [h])
  have ho₂ : ∀ o o', o ≠ o' → Multigraph.pairing (a' o) (G.laplacian (a' o')) = 0 := by
    intro o o' hne
    rcases o with _ | i <;> rcases o' with _ | i'
    · exact absurd rfl hne
    · exact h0Δ i'
    · show Multigraph.pairing (a i) (G.laplacian a₀) = 0
      rw [Multigraph.pairing_laplacian_comm, Multigraph.pairing_comm]
      exact h0Δ i
    · exact horth₂ i i' fun h => hne (by rw [h])
  -- the translated identity with a free coefficient `κ` on the composite factor
  have hκ : ∀ κ : ℝ, ∫ φ, ∏ o, (1 + Option.elim o κ K * Real.cos (∑ j, φ j * ϱ' o j + 0)) ∂μ =
      ∫ φ, ∏ o, (1 + Option.elim o κ K * Real.exp (-gffTranslationEnergy G β (a' o) (ϱ' o)) *
        Real.cos (∑ j, φ j * (ϱ' o j + β * G.laplacian (a' o) j) + 0)) ∂μ := fun κ =>
    gffLaw_integral_prod_spinWave_translation G hG β hβ v ϱ' hn' (fun o => Option.elim o κ K)
      (fun _ => 0) a' ho₁ ho₂
  set P : (V → ℝ) → ℝ := fun φ => ∏ i, (1 + K i * Real.cos (∑ j, φ j * ϱ i j)) with hP
  set P' : (V → ℝ) → ℝ := fun φ => ∏ i, (1 + K i *
    Real.exp (-gffTranslationEnergy G β (a i) (ϱ i)) *
      Real.cos (∑ j, φ j * (ϱ i j + β * G.laplacian (a i) j))) with hP'
  set E₀ := gffTranslationEnergy G β a₀ ρ with hE₀
  have hL : ∀ κ : ℝ, ∀ φ : V → ℝ,
      ∏ o, (1 + Option.elim o κ K * Real.cos (∑ j, φ j * ϱ' o j + 0)) =
        P φ + κ * (Real.cos (∑ j, φ j * ρ j) * P φ) := by
    intro κ φ
    rw [Fintype.prod_option]
    simp only [hϱ', Option.elim, add_zero, hP]
    ring
  have hR : ∀ κ : ℝ, ∀ φ : V → ℝ,
      ∏ o, (1 + Option.elim o κ K * Real.exp (-gffTranslationEnergy G β (a' o) (ϱ' o)) *
        Real.cos (∑ j, φ j * (ϱ' o j + β * G.laplacian (a' o) j) + 0)) =
        P' φ + κ * Real.exp (-E₀) *
          (Real.cos (∑ j, φ j * (ρ j + β * G.laplacian a₀ j)) * P' φ) := by
    intro κ φ
    rw [Fintype.prod_option]
    simp only [hϱ', ha', Option.elim, add_zero, hP', hE₀]
    ring
  have hPint : Integrable P μ := by
    have := Reduction.integrable_prod_one_add_mul_cos μ Finset.univ K
      (fun i φ => ∑ j, φ j * ϱ i j) (fun i => by fun_prop)
    simpa only [hP] using this
  have hP'int : Integrable P' μ := by
    have := Reduction.integrable_prod_one_add_mul_cos μ Finset.univ
      (fun i => K i * Real.exp (-gffTranslationEnergy G β (a i) (ϱ i)))
      (fun i φ => ∑ j, φ j * (ϱ i j + β * G.laplacian (a i) j)) (fun i => by fun_prop)
    simpa only [hP'] using this
  have hcosP : Integrable (fun φ => Real.cos (∑ j, φ j * ρ j) * P φ) μ :=
    hPint.bdd_mul (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun φ => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
  have hcosP' : Integrable
      (fun φ => Real.cos (∑ j, φ j * (ρ j + β * G.laplacian a₀ j)) * P' φ) μ :=
    hP'int.bdd_mul (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun φ => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
  have hlin : ∀ κ : ℝ, ∫ φ, P φ ∂μ + κ * ∫ φ, Real.cos (∑ j, φ j * ρ j) * P φ ∂μ =
      ∫ φ, P' φ ∂μ + κ * Real.exp (-E₀) *
        ∫ φ, Real.cos (∑ j, φ j * (ρ j + β * G.laplacian a₀ j)) * P' φ ∂μ := by
    intro κ
    have h := hκ κ
    simp_rw [hL κ, hR κ] at h
    rw [integral_add hPint (hcosP.const_mul _), integral_add hP'int (hcosP'.const_mul _),
      integral_const_mul, integral_const_mul] at h
    exact h
  have h0 := hlin 0
  have h1 := hlin 1
  simp only [zero_mul, add_zero, one_mul] at h0 h1
  refine ⟨h0, ?_⟩
  linarith

end Translation

end FroehlichSpencer.BKT.Generic.Marked
