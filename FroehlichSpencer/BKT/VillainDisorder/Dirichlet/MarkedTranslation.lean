/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedInterface
public import FroehlichSpencer.BKT.Generic.Marked.Comparison
import Mathlib.Tactic

/-!
# The marked translation identity with phases

`gffLaw_integral_cos_mul_prod_translation_phase` is `gffLaw_integral_cos_mul_prod_translation`
 with constant phases on the composite and on every density. On the rooted square, a root
offset `t` enters D1's branch expansion as the phases `−t ϱ(root)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open MeasureTheory FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.Marked

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-! ### The marked translation identity with phases -/

/-- **Translation of a marked term with phases** (as `gffLaw_integral_cos_mul_prod_translation`,
with a phase `s₀` on the composite and phases `s i` on the other densities). -/
theorem gffLaw_integral_cos_mul_prod_translation_phase (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ρ a₀ : V → ℝ) (hρ : ∑ j, ρ j = 0) (s₀ : ℝ) (ϱ : ι → V → ℝ)
    (hneutral : ∀ i, ∑ j, ϱ i j = 0) (K s : ι → ℝ) (a : ι → V → ℝ)
    (h0i : ∀ i, Multigraph.pairing a₀ (ϱ i) = 0) (hi0 : ∀ i, Multigraph.pairing (a i) ρ = 0)
    (horth₁ : ∀ i i', i ≠ i' → Multigraph.pairing (a i) (ϱ i') = 0)
    (h0Δ : ∀ i, Multigraph.pairing a₀ (G.laplacian (a i)) = 0)
    (horth₂ : ∀ i i', i ≠ i' → Multigraph.pairing (a i) (G.laplacian (a i')) = 0) :
    (∫ φ, ∏ i, (1 + K i * Real.cos (∑ j, φ j * ϱ i j + s i)) ∂gffLaw G hG β hβ v =
      ∫ φ, ∏ i, (1 + K i * Real.exp (-gffTranslationEnergy G β (a i) (ϱ i)) *
          Real.cos (∑ j, φ j * (ϱ i j + β * G.laplacian (a i) j) + s i))
        ∂gffLaw G hG β hβ v) ∧
    ∫ φ, Real.cos (∑ j, φ j * ρ j + s₀) *
        ∏ i, (1 + K i * Real.cos (∑ j, φ j * ϱ i j + s i)) ∂gffLaw G hG β hβ v =
      Real.exp (-gffTranslationEnergy G β a₀ ρ) *
        ∫ φ, Real.cos (∑ j, φ j * (ρ j + β * G.laplacian a₀ j) + s₀) *
          ∏ i, (1 + K i * Real.exp (-gffTranslationEnergy G β (a i) (ϱ i)) *
            Real.cos (∑ j, φ j * (ϱ i j + β * G.laplacian (a i) j) + s i))
          ∂gffLaw G hG β hβ v := by
  classical
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  set μ := gffLaw G hG β hβ v with hμ
  set ϱ' : Option ι → V → ℝ := fun o => Option.elim o ρ ϱ with hϱ'
  set a' : Option ι → V → ℝ := fun o => Option.elim o a₀ a with ha'
  set s' : Option ι → ℝ := fun o => Option.elim o s₀ s with hs'
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
  have hκ : ∀ κ : ℝ, ∫ φ, ∏ o, (1 + Option.elim o κ K * Real.cos (∑ j, φ j * ϱ' o j + s' o)) ∂μ =
      ∫ φ, ∏ o, (1 + Option.elim o κ K * Real.exp (-gffTranslationEnergy G β (a' o) (ϱ' o)) *
        Real.cos (∑ j, φ j * (ϱ' o j + β * G.laplacian (a' o) j) + s' o)) ∂μ := fun κ =>
    Reduction.gffLaw_integral_prod_spinWave_translation G hG β hβ v ϱ' hn'
      (fun o => Option.elim o κ K)
      s' a' ho₁ ho₂
  set P : (V → ℝ) → ℝ := fun φ => ∏ i, (1 + K i * Real.cos (∑ j, φ j * ϱ i j + s i)) with hP
  set P' : (V → ℝ) → ℝ := fun φ => ∏ i, (1 + K i *
    Real.exp (-gffTranslationEnergy G β (a i) (ϱ i)) *
      Real.cos (∑ j, φ j * (ϱ i j + β * G.laplacian (a i) j) + s i)) with hP'
  set E₀ := gffTranslationEnergy G β a₀ ρ with hE₀
  have hL : ∀ κ : ℝ, ∀ φ : V → ℝ,
      ∏ o, (1 + Option.elim o κ K * Real.cos (∑ j, φ j * ϱ' o j + s' o)) =
        P φ + κ * (Real.cos (∑ j, φ j * ρ j + s₀) * P φ) := by
    intro κ φ
    rw [Fintype.prod_option]
    simp only [hϱ', hs', Option.elim, hP]
    ring
  have hR : ∀ κ : ℝ, ∀ φ : V → ℝ,
      ∏ o, (1 + Option.elim o κ K * Real.exp (-gffTranslationEnergy G β (a' o) (ϱ' o)) *
        Real.cos (∑ j, φ j * (ϱ' o j + β * G.laplacian (a' o) j) + s' o)) =
        P' φ + κ * Real.exp (-E₀) *
          (Real.cos (∑ j, φ j * (ρ j + β * G.laplacian a₀ j) + s₀) * P' φ) := by
    intro κ φ
    rw [Fintype.prod_option]
    simp only [hϱ', ha', hs', Option.elim, hP', hE₀]
    ring
  have hPint : Integrable P μ := by
    have := Reduction.integrable_prod_one_add_mul_cos μ Finset.univ K
      (fun i φ => ∑ j, φ j * ϱ i j + s i) (fun i => by fun_prop)
    simpa only [hP] using this
  have hP'int : Integrable P' μ := by
    have := Reduction.integrable_prod_one_add_mul_cos μ Finset.univ
      (fun i => K i * Real.exp (-gffTranslationEnergy G β (a i) (ϱ i)))
      (fun i φ => ∑ j, φ j * (ϱ i j + β * G.laplacian (a i) j) + s i) (fun i => by fun_prop)
    simpa only [hP'] using this
  have hcosP : Integrable (fun φ => Real.cos (∑ j, φ j * ρ j + s₀) * P φ) μ :=
    hPint.bdd_mul (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun φ => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
  have hcosP' : Integrable
      (fun φ => Real.cos (∑ j, φ j * (ρ j + β * G.laplacian a₀ j) + s₀) * P' φ) μ :=
    hP'int.bdd_mul (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun φ => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
  have hlin : ∀ κ : ℝ, ∫ φ, P φ ∂μ + κ * ∫ φ, Real.cos (∑ j, φ j * ρ j + s₀) * P φ ∂μ =
      ∫ φ, P' φ ∂μ + κ * Real.exp (-E₀) *
        ∫ φ, Real.cos (∑ j, φ j * (ρ j + β * G.laplacian a₀ j) + s₀) * P' φ ∂μ := by
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

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
