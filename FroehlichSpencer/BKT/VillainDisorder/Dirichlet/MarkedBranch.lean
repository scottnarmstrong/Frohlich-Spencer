/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedTranslation
import Mathlib.Tactic

/-!
# The rooted marked branch bound

FS81 (5.29)–(5.35) on one branch, for any connected multigraph and any rooted GFF. Nothing here
assumes at most one charged member: all densities are neutral on the rooted graph.

* `abs_markedTerm_le_of_termData`: from `RootedMarkedTermData`,
  `|∫ cos(⟨φ, σ⟩ + s₀) ∏_R (1 + K cos(⟨φ, ϱ⟩ + s ϱ))| ≤ e^{−gain} ∫ ∏_R (…)`. The translated
  remainder factors are nonnegative.
* `branch_comparison_phase`: from branch waves with renormalized activities `≤ θ < 1`,
  `Z_N > 0` and `∏_{N ∖ S}(1 − θ) Z_S ≤ Z_N`.
* **`abs_markedBranch_le_rooted`**: the observable is expanded over the clusters of a monotone
  adjacency (`cos_mul_prod_eq_sum_clusters`). This gives
  `|∫ cos(ξ⟨φ, ϱ₀⟩) ∏_N (…)| ≤ (∑_C |∏_C K| e^{−g(C)} / ∏_{N ∖ rem(C)} (1 − θ)) Z_N`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open MeasureTheory FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.Marked

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- The factor product `∏_{ϱ ∈ R} (1 + K ϱ cos(⟨φ, ϱ⟩ + s ϱ))`. -/
def phaseProduct (R : Finset (V → ℤ)) (K s : (V → ℤ) → ℝ) (φ : V → ℝ) : ℝ :=
  ∏ ϱ ∈ R, (1 + K ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ) + s ϱ))

omit [DecidableEq V] in
theorem continuous_phaseProduct (R : Finset (V → ℤ)) (K s : (V → ℤ) → ℝ) :
    Continuous (phaseProduct R K s) := by
  unfold phaseProduct
  fun_prop

omit [DecidableEq V] in
theorem integrable_phaseProduct (μ : Measure (V → ℝ)) [IsFiniteMeasure μ]
    (R : Finset (V → ℤ)) (K s : (V → ℤ) → ℝ) : Integrable (phaseProduct R K s) μ := by
  have := Reduction.integrable_prod_one_add_mul_cos μ R K
    (fun ϱ φ => ∑ j, φ j * (ϱ j : ℝ) + s ϱ) (fun ϱ => by fun_prop)
  unfold phaseProduct
  exact this

/-- The translated product with the renormalized activities `z ϱ = K ϱ e^{-E(a ϱ, ϱ)}`. -/
def translatedProduct (G : Multigraph V E) (τ : ℝ) (R : Finset (V → ℤ))
    (K s : (V → ℤ) → ℝ) (a : (V → ℤ) → V → ℝ) (φ : V → ℝ) : ℝ :=
  ∏ ϱ ∈ R, (1 + K ϱ * Real.exp (-gffTranslationEnergy G τ (a ϱ) (fun j => (ϱ j : ℝ))) *
    Real.cos (∑ j, φ j * ((ϱ j : ℝ) + τ * G.laplacian (a ϱ) j) + s ϱ))

theorem integrable_translatedProduct (μ : Measure (V → ℝ)) [IsFiniteMeasure μ]
    (G : Multigraph V E) (τ : ℝ) (R : Finset (V → ℤ)) (K s : (V → ℤ) → ℝ)
    (a : (V → ℤ) → V → ℝ) : Integrable (translatedProduct G τ R K s a) μ := by
  have := Reduction.integrable_prod_one_add_mul_cos μ R
    (fun ϱ => K ϱ * Real.exp (-gffTranslationEnergy G τ (a ϱ) (fun j => (ϱ j : ℝ))))
    (fun ϱ φ => ∑ j, φ j * ((ϱ j : ℝ) + τ * G.laplacian (a ϱ) j) + s ϱ) (fun ϱ => by fun_prop)
  unfold translatedProduct
  exact this

/-- A factor `1 + z cos` with `|z| ≤ θ` is at least `1 − θ`. -/
theorem one_sub_le_one_add_mul_cos {z θ x : ℝ} (h : |z| ≤ θ) : 1 - θ ≤ 1 + z * Real.cos x := by
  have h1 : |z * Real.cos x| ≤ θ := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg z) (Real.abs_cos_le_one x)).trans h
  linarith [neg_abs_le (z * Real.cos x)]

/-! ### The translation identities over a finset -/

section Translation

variable (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (τ : ℝ) (hτ : 0 < τ) (v : V)

/-- The product translation over a finset of neutral densities. -/
theorem integral_phaseProduct_eq_translated (R : Finset (V → ℤ))
    (hR : ∀ ϱ ∈ R, ∑ j, ϱ j = 0) (K s : (V → ℤ) → ℝ) (a : (V → ℤ) → V → ℝ)
    (horth₁ : ∀ ϱ ∈ R, ∀ ϱ' ∈ R, ϱ ≠ ϱ' →
      Multigraph.pairing (a ϱ) (fun j => (ϱ' j : ℝ)) = 0)
    (horth₂ : ∀ ϱ ∈ R, ∀ ϱ' ∈ R, ϱ ≠ ϱ' →
      Multigraph.pairing (a ϱ) (G.laplacian (a ϱ')) = 0) :
    ∫ φ, phaseProduct R K s φ ∂gffLaw G hG τ hτ v =
      ∫ φ, translatedProduct G τ R K s a φ ∂gffLaw G hG τ hτ v := by
  classical
  unfold phaseProduct translatedProduct
  simp_rw [← Finset.prod_coe_sort R]
  exact Reduction.gffLaw_integral_prod_spinWave_translation G hG τ hτ v
    (fun ϱ : R => fun j => ((ϱ : V → ℤ) j : ℝ))
    (fun ϱ => by exact_mod_cast hR ϱ ϱ.property) (fun ϱ => K ϱ) (fun ϱ => s ϱ) (fun ϱ => a ϱ)
    (fun ϱ ϱ' hne => horth₁ ϱ ϱ.2 ϱ' ϱ'.2 fun h => hne (Subtype.ext h))
    (fun ϱ ϱ' hne => horth₂ ϱ ϱ.2 ϱ' ϱ'.2 fun h => hne (Subtype.ext h))

/-- **The marked term bound** (FS81 (5.31)–(5.34)) from the renormalization data of the term:
`|∫ cos(⟨φ, σ⟩ + s₀) ∏_R (1 + K cos(⟨φ, ϱ⟩ + s ϱ)) dμ| ≤ e^{-gain} ∫ ∏_R (1 + K cos …) dμ`. -/
theorem abs_markedTerm_le_of_termData (R : Finset (V → ℤ)) (hR : ∀ ϱ ∈ R, ∑ j, ϱ j = 0)
    (K s : (V → ℤ) → ℝ) (σ : V → ℝ) (hσ : ∑ j, σ j = 0) (s₀ : ℝ) {gain : ℝ}
    (hdata : RootedMarkedTermData G τ K σ R gain) :
    |∫ φ, Real.cos (∑ j, φ j * σ j + s₀) * phaseProduct R K s φ ∂gffLaw G hG τ hτ v| ≤
      Real.exp (-gain) * ∫ φ, phaseProduct R K s φ ∂gffLaw G hG τ hτ v := by
  classical
  have := isProbabilityMeasure_gffLaw G hG τ hτ v
  set μ := gffLaw G hG τ hτ v with hμ
  obtain ⟨a₀, a, h0i, hi0, horth₁, h0Δ, horth₂, hz, hgain⟩ := hdata
  obtain ⟨hP, hM⟩ := gffLaw_integral_cos_mul_prod_translation_phase G hG τ hτ v
    σ a₀ hσ s₀ (fun ϱ : R => fun j => ((ϱ : V → ℤ) j : ℝ))
    (fun ϱ => by exact_mod_cast hR ϱ ϱ.property) (fun ϱ => K ϱ) (fun ϱ => s ϱ)
    (fun ϱ => a ϱ) (fun ϱ => h0i ϱ ϱ.2) (fun ϱ => hi0 ϱ ϱ.2)
    (fun ϱ ϱ' hne => horth₁ ϱ ϱ.2 ϱ' ϱ'.2 fun h => hne (Subtype.ext h))
    (fun ϱ => h0Δ ϱ ϱ.2)
    (fun ϱ ϱ' hne => horth₂ ϱ ϱ.2 ϱ' ϱ'.2 fun h => hne (Subtype.ext h))
  have hPeq : ∀ φ, phaseProduct R K s φ =
      ∏ ϱ : R, (1 + K ϱ * Real.cos (∑ j, φ j * ((ϱ : V → ℤ) j : ℝ) + s ϱ)) := fun φ => by
    unfold phaseProduct
    rw [← Finset.prod_coe_sort R]
  have hTeq : ∀ φ, translatedProduct G τ R K s a φ =
      ∏ ϱ : R, (1 + K ϱ * Real.exp (-gffTranslationEnergy G τ (a ϱ)
          (fun j => ((ϱ : V → ℤ) j : ℝ))) *
        Real.cos (∑ j, φ j * (((ϱ : V → ℤ) j : ℝ) + τ * G.laplacian (a ϱ) j) + s ϱ)) :=
    fun φ => by
      unfold translatedProduct
      rw [← Finset.prod_coe_sort R]
  simp_rw [← hPeq, ← hTeq] at hP hM
  rw [hM, hP]
  -- the translated factors are nonnegative
  have hT0 : ∀ φ, 0 ≤ translatedProduct G τ R K s a φ := by
    intro φ
    unfold translatedProduct
    refine Finset.prod_nonneg fun ϱ hϱ => ?_
    have h1 : |K ϱ * Real.exp (-gffTranslationEnergy G τ (a ϱ) (fun j => (ϱ j : ℝ)))| ≤ 1 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact hz ϱ hϱ
    have := one_sub_le_one_add_mul_cos (x := ∑ j, φ j * ((ϱ j : ℝ) + τ * G.laplacian (a ϱ) j) +
      s ϱ) h1
    linarith
  have hTint := integrable_translatedProduct μ G τ R K s a
  have hI0 : 0 ≤ ∫ φ, translatedProduct G τ R K s a φ ∂μ := integral_nonneg hT0
  have habs : |∫ φ, Real.cos (∑ j, φ j * (σ j + τ * G.laplacian a₀ j) + s₀) *
      translatedProduct G τ R K s a φ ∂μ| ≤ ∫ φ, translatedProduct G τ R K s a φ ∂μ := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun φ => abs_nonneg _) hTint (ae_of_all _ fun φ => ?_))
    dsimp only
    rw [abs_mul, abs_of_nonneg (hT0 φ)]
    exact mul_le_of_le_one_left (hT0 φ) (Real.abs_cos_le_one _)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-gffTranslationEnergy G τ a₀ σ) * |∫ φ, Real.cos (∑ j, φ j *
        (σ j + τ * G.laplacian a₀ j) + s₀) * translatedProduct G τ R K s a φ ∂μ|
      ≤ Real.exp (-gffTranslationEnergy G τ a₀ σ) * ∫ φ, translatedProduct G τ R K s a φ ∂μ :=
        mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le
    _ ≤ Real.exp (-gain) * ∫ φ, translatedProduct G τ R K s a φ ∂μ :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hI0

/-- **The branch comparison** (FS81 (5.35)): with branch waves whose renormalized activities are
at most `θ < 1`, the branch normalizer `Z_N` is positive and
`∏_{N ∖ S} (1 − θ) Z_S ≤ Z_N` for every `S ⊆ N`. -/
theorem branch_comparison_phase (N : Finset (V → ℤ)) (hN : ∀ ϱ ∈ N, ∑ j, ϱ j = 0)
    (K s θ : (V → ℤ) → ℝ) (b : (V → ℤ) → V → ℝ)
    (horth₁ : ∀ ϱ ∈ N, ∀ ϱ' ∈ N, ϱ ≠ ϱ' →
      Multigraph.pairing (b ϱ) (fun j => (ϱ' j : ℝ)) = 0)
    (horth₂ : ∀ ϱ ∈ N, ∀ ϱ' ∈ N, ϱ ≠ ϱ' →
      Multigraph.pairing (b ϱ) (G.laplacian (b ϱ')) = 0)
    (hz : ∀ ϱ ∈ N, |K ϱ| *
      Real.exp (-gffTranslationEnergy G τ (b ϱ) (fun j => (ϱ j : ℝ))) ≤ θ ϱ)
    (hθ : ∀ ϱ ∈ N, θ ϱ < 1) {S : Finset (V → ℤ)} (hS : S ⊆ N) :
    0 < ∫ φ, phaseProduct N K s φ ∂gffLaw G hG τ hτ v ∧
      (∏ ϱ ∈ N \ S, (1 - θ ϱ)) * ∫ φ, phaseProduct S K s φ ∂gffLaw G hG τ hτ v ≤
        ∫ φ, phaseProduct N K s φ ∂gffLaw G hG τ hτ v := by
  classical
  have := isProbabilityMeasure_gffLaw G hG τ hτ v
  set μ := gffLaw G hG τ hτ v with hμ
  have hN' := integral_phaseProduct_eq_translated G hG τ hτ v N hN K s b horth₁ horth₂
  have hS' := integral_phaseProduct_eq_translated G hG τ hτ v S (fun ϱ hϱ => hN ϱ (hS hϱ)) K s b
    (fun ϱ hϱ ϱ' hϱ' => horth₁ ϱ (hS hϱ) ϱ' (hS hϱ'))
    (fun ϱ hϱ ϱ' hϱ' => horth₂ ϱ (hS hϱ) ϱ' (hS hϱ'))
  rw [hN', hS']
  have hfac : ∀ ϱ ∈ N, ∀ φ : V → ℝ, 1 - θ ϱ ≤ 1 + K ϱ *
      Real.exp (-gffTranslationEnergy G τ (b ϱ) (fun j => (ϱ j : ℝ))) *
      Real.cos (∑ j, φ j * ((ϱ j : ℝ) + τ * G.laplacian (b ϱ) j) + s ϱ) := by
    intro ϱ hϱ φ
    apply one_sub_le_one_add_mul_cos
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact hz ϱ hϱ
  have hθ0 : ∀ ϱ ∈ N, 0 < 1 - θ ϱ := fun ϱ hϱ => by linarith [hθ ϱ hϱ]
  have hpos : ∀ X ⊆ N, ∀ φ, (∏ ϱ ∈ X, (1 - θ ϱ)) ≤ translatedProduct G τ X K s b φ := by
    intro X hX φ
    unfold translatedProduct
    exact Finset.prod_le_prod₀ (fun ϱ hϱ => (hθ0 ϱ (hX hϱ)).le) fun ϱ hϱ => hfac ϱ (hX hϱ) φ
  have hT0 : ∀ X ⊆ N, ∀ φ, 0 ≤ translatedProduct G τ X K s b φ := fun X hX φ =>
    (Finset.prod_nonneg fun ϱ hϱ => (hθ0 ϱ (hX hϱ)).le).trans (hpos X hX φ)
  refine ⟨?_, ?_⟩
  · have hc : 0 < ∏ ϱ ∈ N, (1 - θ ϱ) := Finset.prod_pos fun ϱ hϱ => hθ0 ϱ hϱ
    calc (0 : ℝ) < ∫ _φ, (∏ ϱ ∈ N, (1 - θ ϱ)) ∂μ := by simpa using hc
      _ ≤ ∫ φ, translatedProduct G τ N K s b φ ∂μ :=
        integral_mono (integrable_const _) (integrable_translatedProduct μ G τ N K s b)
          fun φ => hpos N le_rfl φ
  · rw [← integral_const_mul]
    refine integral_mono ((integrable_translatedProduct μ G τ S K s b).const_mul _)
      (integrable_translatedProduct μ G τ N K s b) fun φ => ?_
    have hsplit : translatedProduct G τ N K s b φ =
        translatedProduct G τ (N \ S) K s b φ * translatedProduct G τ S K s b φ := by
      unfold translatedProduct
      rw [Finset.prod_sdiff hS]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (hpos (N \ S) Finset.sdiff_subset φ)
      (hT0 S hS φ)

/-! ### The marked branch bound -/

/-- The phase of the composite of `(C, T)`: `∑_T s − ∑_{C ∖ T} s`. -/
def compositePhase (s : (V → ℤ) → ℝ) (C T : Finset (V → ℤ)) : ℝ :=
  ∑ m ∈ T, s m - ∑ m ∈ C \ T, s m

omit [DecidableEq V] in
theorem marked_argument_eq (ξ : ℝ) (ρ₀ : V → ℤ) (s : (V → ℤ) → ℝ) (C T : Finset (V → ℤ))
    (φ : V → ℝ) :
    ξ * ∑ j, φ j * (ρ₀ j : ℝ) + ∑ m ∈ T, (∑ j, φ j * (m j : ℝ) + s m) -
        ∑ m ∈ C \ T, (∑ j, φ j * (m j : ℝ) + s m) =
      ∑ j, φ j * rootedMarkedComposite ξ ρ₀ C T j + compositePhase s C T := by
  unfold rootedMarkedComposite compositePhase
  simp only [Finset.sum_add_distrib, mul_add, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := T), Finset.sum_comm (s := C \ T)]
  ring_nf

omit [DecidableEq V] in
theorem sum_rootedMarkedComposite (ξ : ℝ) {ρ₀ : V → ℤ} (hρ₀ : ∑ j, ρ₀ j = 0)
    {C T : Finset (V → ℤ)} (hC : ∀ m ∈ C, ∑ j, m j = 0) (hT : T ⊆ C) :
    ∑ j, rootedMarkedComposite ξ ρ₀ C T j = 0 := by
  unfold rootedMarkedComposite
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := T), Finset.sum_comm (s := Finset.univ) (t := C \ T)]
  have h0 : ∑ j, (ρ₀ j : ℝ) = 0 := by exact_mod_cast hρ₀
  have hT0 : ∑ m ∈ T, ∑ j, (m j : ℝ) = 0 :=
    Finset.sum_eq_zero fun m hm => by exact_mod_cast hC m (hT hm)
  have hC0 : ∑ m ∈ C \ T, ∑ j, (m j : ℝ) = 0 :=
    Finset.sum_eq_zero fun m hm => by exact_mod_cast hC m (Finset.mem_sdiff.1 hm).1
  rw [h0, hT0, hC0]
  ring

/-- **The rooted marked branch bound** (FS81 (5.29)–(5.35) on one branch, Appendix D form).
Expand the observable over the clusters of a monotone adjacency. Bound every term
`(C, T)` by its renormalization data (`abs_markedTerm_le_of_termData`), and every remainder
normalizer by the branch normalizer (`branch_comparison_phase`). Then
`|∫ cos(ξ⟨φ, ϱ₀⟩) ∏_N (1 + K cos(⟨φ, ϱ⟩ + s ϱ)) dμ| ≤ W_N Z_N`, with
`W_N = ∑_C |∏_C K| e^{-g(C)} / ∏_{N ∖ rem(C)} (1 − θ)`. -/
theorem abs_markedBranch_le_rooted (N : Finset (V → ℤ)) (hN : ∀ ϱ ∈ N, ∑ j, ϱ j = 0)
    (K s θ : (V → ℤ) → ℝ) (b : (V → ℤ) → V → ℝ)
    (horth₁ : ∀ ϱ ∈ N, ∀ ϱ' ∈ N, ϱ ≠ ϱ' →
      Multigraph.pairing (b ϱ) (fun j => (ϱ' j : ℝ)) = 0)
    (horth₂ : ∀ ϱ ∈ N, ∀ ϱ' ∈ N, ϱ ≠ ϱ' →
      Multigraph.pairing (b ϱ) (G.laplacian (b ϱ')) = 0)
    (hz : ∀ ϱ ∈ N, |K ϱ| *
      Real.exp (-gffTranslationEnergy G τ (b ϱ) (fun j => (ϱ j : ℝ))) ≤ θ ϱ)
    (hθ : ∀ ϱ ∈ N, θ ϱ < 1) {ρ₀ : V → ℤ} (hρ₀ : ∑ j, ρ₀ j = 0) (ξ : ℝ)
    {adj : (V → ℤ) → Finset (V → ℤ) → Prop} (hmono : AdjMonotone adj)
    (g : Finset (V → ℤ) → ℝ)
    (hterm : ∀ C ∈ clusters adj N, ∀ T ⊆ C,
      RootedMarkedTermData G τ K (rootedMarkedComposite ξ ρ₀ C T) (remainder adj N C) (g C)) :
    0 < ∫ φ, phaseProduct N K s φ ∂gffLaw G hG τ hτ v ∧
      |∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) * phaseProduct N K s φ ∂gffLaw G hG τ hτ v| ≤
        (∑ C ∈ clusters adj N, |∏ m ∈ C, K m| * Real.exp (-g C) /
          ∏ m ∈ N \ remainder adj N C, (1 - θ m)) *
          ∫ φ, phaseProduct N K s φ ∂gffLaw G hG τ hτ v := by
  classical
  have := isProbabilityMeasure_gffLaw G hG τ hτ v
  set μ := gffLaw G hG τ hτ v with hμ
  have hZpos := (branch_comparison_phase G hG τ hτ v N hN K s θ b horth₁ horth₂ hz hθ
    (Finset.empty_subset N)).1
  refine ⟨hZpos, ?_⟩
  set Z := ∫ φ, phaseProduct N K s φ ∂μ with hZ
  set J : Finset (V → ℤ) → Finset (V → ℤ) → ℝ := fun C T =>
    ∫ φ, Real.cos (∑ j, φ j * rootedMarkedComposite ξ ρ₀ C T j + compositePhase s C T) *
      phaseProduct (remainder adj N C) K s φ ∂μ with hJ
  -- the expansion
  have hpt : ∀ φ : V → ℝ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) * phaseProduct N K s φ =
      ∑ C ∈ clusters adj N, ∑ T ∈ C.powerset, ((1 / 2) ^ C.card * ∏ m ∈ C, K m) *
        (Real.cos (∑ j, φ j * rootedMarkedComposite ξ ρ₀ C T j + compositePhase s C T) *
          phaseProduct (remainder adj N C) K s φ) := by
    intro φ
    unfold phaseProduct
    rw [cos_mul_prod_eq_sum_clusters hmono N K (fun m => ∑ j, φ j * (m j : ℝ) + s m)]
    refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun T _ => ?_
    rw [marked_argument_eq]
    ring
  have hint : ∀ C T, Integrable (fun φ : V → ℝ =>
      Real.cos (∑ j, φ j * rootedMarkedComposite ξ ρ₀ C T j + compositePhase s C T) *
        phaseProduct (remainder adj N C) K s φ) μ := fun C T =>
    (integrable_phaseProduct μ _ K s).bdd_mul (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hI : ∫ φ, Real.cos (ξ * ∑ j, φ j * (ρ₀ j : ℝ)) * phaseProduct N K s φ ∂μ =
      ∑ C ∈ clusters adj N, ∑ T ∈ C.powerset, ((1 / 2) ^ C.card * ∏ m ∈ C, K m) * J C T := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun C _ =>
      integrable_finsetSum _ fun T _ => (hint C T).const_mul _]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [integral_finsetSum _ fun T _ => (hint C T).const_mul _]
    exact Finset.sum_congr rfl fun T _ => integral_const_mul _ _
  -- the term bounds
  have hJle : ∀ C ∈ clusters adj N, ∀ T ∈ C.powerset,
      |J C T| ≤ Real.exp (-g C) * ∫ φ, phaseProduct (remainder adj N C) K s φ ∂μ := by
    intro C hC T hT
    have hCN : C ⊆ N := (mem_clusters.1 hC).1
    have hT' : T ⊆ C := Finset.mem_powerset.1 hT
    exact abs_markedTerm_le_of_termData G hG τ hτ v (remainder adj N C)
      (fun ϱ hϱ => hN ϱ (remainder_subset N C hϱ)) K s _
      (sum_rootedMarkedComposite ξ hρ₀ (fun m hm => hN m (hCN hm)) hT') _ (hterm C hC T hT')
  -- the comparison
  have hcmp : ∀ C ∈ clusters adj N, (∏ m ∈ N \ remainder adj N C, (1 - θ m)) *
      ∫ φ, phaseProduct (remainder adj N C) K s φ ∂μ ≤ Z := fun C _ =>
    (branch_comparison_phase G hG τ hτ v N hN K s θ b horth₁ horth₂ hz hθ
      (remainder_subset N C)).2
  have hθ0 : ∀ C, 0 < ∏ m ∈ N \ remainder adj N C, (1 - θ m) := fun C =>
    Finset.prod_pos fun m hm => by linarith [hθ m (Finset.mem_sdiff.1 hm).1]
  rw [hI, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun C hC => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hR0 : 0 ≤ ∫ φ, phaseProduct (remainder adj N C) K s φ ∂μ := by
    have h := hcmp C hC
    have hp := hθ0 C
    by_contra hneg
    push Not at hneg
    -- the remainder normalizer is itself a branch normalizer of `rem(C)`
    have hpos := (branch_comparison_phase G hG τ hτ v (remainder adj N C)
      (fun ϱ hϱ => hN ϱ (remainder_subset N C hϱ)) K s θ b
      (fun ϱ hϱ ϱ' hϱ' => horth₁ ϱ (remainder_subset N C hϱ) ϱ' (remainder_subset N C hϱ'))
      (fun ϱ hϱ ϱ' hϱ' => horth₂ ϱ (remainder_subset N C hϱ) ϱ' (remainder_subset N C hϱ'))
      (fun ϱ hϱ => hz ϱ (remainder_subset N C hϱ))
      (fun ϱ hϱ => hθ ϱ (remainder_subset N C hϱ)) (Finset.empty_subset _)).1
    linarith
  have hZrem : ∫ φ, phaseProduct (remainder adj N C) K s φ ∂μ ≤
      Z / ∏ m ∈ N \ remainder adj N C, (1 - θ m) := by
    rw [le_div_iff₀ (hθ0 C), mul_comm]
    exact hcmp C hC
  calc ∑ T ∈ C.powerset, |((1 / 2) ^ C.card * ∏ m ∈ C, K m) * J C T|
      ≤ ∑ T ∈ C.powerset, (1 / 2) ^ C.card * |∏ m ∈ C, K m| *
          (Real.exp (-g C) * ∫ φ, phaseProduct (remainder adj N C) K s φ ∂μ) := by
        refine Finset.sum_le_sum fun T hT => ?_
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2) ^ C.card)]
        exact mul_le_mul_of_nonneg_left (hJle C hC T hT) (by positivity)
    _ = |∏ m ∈ C, K m| * Real.exp (-g C) *
          ∫ φ, phaseProduct (remainder adj N C) K s φ ∂μ := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        have h2 : (2 : ℝ) ^ C.card * (1 / 2) ^ C.card = 1 := by rw [← mul_pow]; norm_num
        push_cast
        calc (2 : ℝ) ^ C.card * ((1 / 2) ^ C.card * |∏ m ∈ C, K m| *
              (Real.exp (-g C) * ∫ φ, phaseProduct (remainder adj N C) K s φ ∂μ))
            = ((2 : ℝ) ^ C.card * (1 / 2) ^ C.card) * (|∏ m ∈ C, K m| * Real.exp (-g C) *
                ∫ φ, phaseProduct (remainder adj N C) K s φ ∂μ) := by ring
          _ = _ := by rw [h2, one_mul]
    _ ≤ |∏ m ∈ C, K m| * Real.exp (-g C) * (Z / ∏ m ∈ N \ remainder adj N C, (1 - θ m)) :=
        mul_le_mul_of_nonneg_left hZrem (by positivity)
    _ = (|∏ m ∈ C, K m| * Real.exp (-g C) / ∏ m ∈ N \ remainder adj N C, (1 - θ m)) * Z := by
        ring

end Translation

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
