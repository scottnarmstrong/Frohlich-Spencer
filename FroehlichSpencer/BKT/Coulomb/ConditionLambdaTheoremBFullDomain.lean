/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaMarkedSplit
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremB
import Mathlib.Tactic

/-!
# The split marked bound on one square domain

`markedConditionLambdaDomain_bound_split` is `markedConditionLambdaDomain_bound` (the marked-cluster estimate) with
`cluster_estimate_split` in place of `cluster_estimate`. For a finite even Fourier product with
coefficients `|λ̂_j(q)| ≤ Γ e^{(a + θ/β) q²}`, `θ ≥ 0`, `θ + δ = 1/16`:
* (H1)–(H3) are the hard-core conditions with `η²` replaced by `8δη²` and no `θ`;
* `|∫ cos(ξ(φ_o − φ_x)) ∏_j λ̂_j dμ| ≤ 2 e^{1/(64δβ)} e^{−(8δη²/(16384 D₁ β)) log₂(|o − x| + 1)} 𝒵`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory FroehlichSpencer.BKT.Generic.Marked Reduction

/-! ### The split marked bound on one square domain -/

section Domain

variable {boundary : SquareBoundary} {L : ℕ}

/-- **The split marked bound** for a finite even Fourier product whose coefficients grow like
`Γ e^{(a + θ/β) q²}` with `θ + δ = 1/16`, `θ ≥ 0`, `δ > 0`. Conditions (H1)–(H3) are those of the
hard-core bound with `η²` replaced by `8δη²` and no `θ` in (H1); the price is the factor
`e^{1/(64δβ)}` (`cluster_estimate_split`). -/
theorem markedConditionLambdaDomain_bound_split (hL : 1 < L) {E : Type} [Fintype E]
    (boundary : SquareBoundary) (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    {D₁ D₂ D₃ θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ = 1 / 16)
    (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h22 : T22Step boundary L D₂) (h21 : P21Step boundary L D₁)
    (h24 : P24Step boundary Λ D₃) {Γ a β₀ c₁ : ℝ}
    (hdamp : ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ s S A ℓ S₀ : ℝ, 0 ≤ s → 0 ≤ S → 0 ≤ ℓ → ℓ ≤ A → S₀ ≤ s →
        A ≤ D₁ * (S₀ + S) →
        D₂ * A + (Real.log (max 1 Γ) + 1 + a + θ / β) * s -
            1 / β * (1 / 16 * s + D₃ * S) ≤
          -(c₁ / β) * (s + ℓ))
    {η c β : ℝ} (hη : 0 < η) (hc : 0 < c) (hcc₁ : c ≤ c₁)
    (hβ : 0 < β) (hββ₀ : β < β₀)
    (H1 : β * (Real.log (max 1 Γ) + 1 + a + 1) + c ≤ 8 * δ * η ^ 2 / 32)
    (H2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤
      8 * δ * η ^ 2 / (64 * β))
    (H3 : 289 * D₂ * β + 289 * c ≤ 8 * δ * η ^ 2 / (16384 * D₁))
    (H4 : Real.exp (-(c / β)) ≤ 1 / 32)
    (v : Fin L × Fin L) (siteWeight : Fin L × Fin L → ℝ → ℝ)
    (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (hNq : ∀ j, 0 < Nq j) (hzero : ∀ j q, Nq j < q → lamHat j q = 0)
    (hform : ∀ j φ, siteWeight j φ =
      1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hbound : ∀ j q, 1 ≤ q →
      |lamHat j q| ≤ Γ * Real.exp ((a + θ / β) * (q : ℝ) ^ 2))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hηξ : η ≤ dipoleGap ξ) :
    0 < ∫ φ, ∏ j, siteWeight j (φ j) ∂gffLaw Λ hΛ β hβ v ∧
      |∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, siteWeight j (φ j)
        ∂gffLaw Λ hΛ β hβ v| ≤
        2 * Real.exp (1 / (64 * δ * β)) * Real.exp (-(8 * δ * η ^ 2 / (16384 * D₁ * β)) *
          Real.logb 2 (latticeDistance boundary L o x + 1)) *
          ∫ φ, ∏ j, siteWeight j (φ j) ∂gffLaw Λ hΛ β hβ v := by
  classical
  have hL0 : 0 < L := by omega
  set μ := gffLaw Λ hΛ β hβ v with hμ
  have hprob := isProbabilityMeasure_gffLaw Λ hΛ β hβ v
  obtain ⟨n, N, cc, K, hens, hcpos, hcsum, hid, hprop⟩ := h22 siteWeight Nq lamHat
    hNq hzero hform
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → Λ.IsDensityCenter ϱ j := by
    intro ϱ
    by_cases h : ϱ = 0
    · exact ⟨v, fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := Λ.exists_isDensityCenter ϱ h
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  obtain ⟨cover, hcov⟩ := h24 centerOf hcenter
  have hws : WaveSelection boundary Λ centerOf cover D₃ := hcov
  set ε := 2 * Real.exp (1 / (64 * δ * β)) * Real.exp (-(8 * δ * η ^ 2 / (16384 * D₁ * β)) *
    Real.logb 2 (latticeDistance boundary L o x + 1)) with hε
  have hθle : ∀ i, ∀ m ∈ N i, memberWeight boundary c β m ≤ 1 / 32 := by
    intro i m hm
    exact (memberWeight_le hc hβ ((hens i).1 m hm)).trans H4
  have hbranch : ∀ i, 0 < ∫ φ, ∏ m ∈ N i,
      (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ ∧
      |∫ φ, Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ| ≤
        ε * ∫ φ, ∏ m ∈ N i,
          (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    intro i
    obtain ⟨hNa, hNb, hNc, hd⟩ := hprop i
    have hz := conditionLambda_renormalizedActivity_le (boundary := boundary)
      hdamp h21 cover (hens i) (K i) hd hcc₁ hβ hββ₀ hbound Λ
    obtain ⟨hZ, hI⟩ := abs_markedBranch_le (boundary := boundary) hL Λ hΛ hdist B h46
      centerOf hcenter cover hws hβ v (hens i) hNa hNb hNc (K i)
      (memberWeight boundary c β)
      (fun m hm => (hθle i m hm).trans_lt (by norm_num)) hz hox hξ0 hξ1 hη.le hηξ
    refine ⟨hZ, hI.trans (mul_le_mul_of_nonneg_right ?_ hZ.le)⟩
    have hmono := markAdjacent_monotone (boundary := boundary)
      (dipoleMark_ne_zero hox)
    refine sum_le_of_le_explorationWeight hmono (N i)
      (explorationWeight boundary c β) (fun m hm => ?_) _ fun C hC => ?_
    · unfold explorationWeight
      split_ifs
      · exact (hθle i m hm).trans_lt (by norm_num)
      · norm_num
    · split_ifs with hCn
      · exact cluster_estimate_split (h₀ := Real.log (max 1 Γ) + 1 + a) hL hD₁ hD₂ h21 (hens i)
          hNa hNb (K i) hθ hδ hθδ hd hc hβ
          (fun ϱ _ => (prod_exp_sq_mul_abs_le ϱ lamHat Γ (a + θ / β) hbound).trans_eq
            (by rw [show Real.log (max 1 Γ) + 1 + (a + θ / β) =
              Real.log (max 1 Γ) + 1 + a + θ / β by ring]))
          hox hξ0 hξ1 hη hηξ H1 H2 H3 H4 hC hCn
      · have hπ0 : ∀ m ∈ N i, 0 ≤ explorationWeight boundary c β m := by
          intro m hm
          unfold explorationWeight
          split_ifs
          · exact (memberWeight_pos c β m).le
          · norm_num
        have hπ1 : ∀ m ∈ N i, explorationWeight boundary c β m ≤ 1 := by
          intro m hm
          unfold explorationWeight
          split_ifs
          · exact (hθle i m hm).trans (by norm_num)
          · norm_num
        have hCN : C ⊆ N i := (mem_clusters.1 hC).1
        refine mul_nonneg (by positivity) (mul_nonneg
          (Finset.prod_nonneg fun m hm => hπ0 m (hCN hm))
          (Finset.prod_nonneg fun m hm => ?_))
        have := hπ1 m (Finset.mem_sdiff.1 hm).1
        linarith
  have hweight : ∀ φ : Fin L × Fin L → ℝ, ∏ j, siteWeight j (φ j) =
      ∑ i, cc i * ∏ m ∈ N i,
        (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) := fun φ => hid φ
  have hint : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ)))) μ := by
    intro i
    exact Reduction.integrable_prod_one_add_mul_cos μ (N i) (K i)
      (fun m φ => ∑ j, φ j * (m j : ℝ)) (fun _ => by fun_prop)
  have hintc : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ)))) μ := by
    intro i
    exact (hint i).bdd_mul (c := 1)
      (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun φ => by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _)
  have hZ : ∫ φ, ∏ j, siteWeight j (φ j) ∂μ =
      ∑ i, cc i * ∫ φ, ∏ m ∈ N i,
        (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    simp_rw [hweight]
    rw [integral_finsetSum _ fun i _ => (hint i).const_mul (cc i)]
    simp_rw [integral_const_mul]
  have hI : ∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, siteWeight j (φ j) ∂μ =
      ∑ i, cc i * ∫ φ, Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    have hpt : ∀ φ : Fin L × Fin L → ℝ,
        Real.cos (ξ * (φ o - φ x)) * ∏ j, siteWeight j (φ j) =
          ∑ i, cc i * (Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
            ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ)))) := by
      intro φ
      rw [hweight, Finset.mul_sum, sum_mul_dipoleMark]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum _ fun i _ => (hintc i).const_mul (cc i)]
    simp_rw [integral_const_mul]
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hcsum
    exact zero_ne_one hcsum
  refine ⟨?_, ?_⟩
  · rw [hZ]
    exact Finset.sum_pos (fun i _ => mul_pos (hcpos i) (hbranch i).1) hn
  · rw [hI, hZ, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_of_pos (hcpos i), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hbranch i).2 (hcpos i).le

end Domain

end FroehlichSpencer.BKT.Coulomb

end
