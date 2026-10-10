/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Marked.Domain
import Mathlib.Tactic

/-!
# The marked domain bound for sub-Gaussian weights

This file extends it to site weights `λ_j` that are `(Γ, 0, 0)`-sub-Gaussian
at the GFF inverse temperature `β` (KP Definition 1.4, `IsSubGaussian Γ 0 0 β`).

The proof is the same.

KP's renormalized activities obey KP (1.14) once the Fourier coefficients
satisfy `|λ̂_j(q)| ≤ Γ` (KP §2.3.4).

These weights are the "general Coulomb gases" of FS81 p. 572.

The case used here is the Villain gas, through its Fejér cutoffs (`Γ = 1`,
`Duality.isSubGaussian_fejerPolynomial`).

* `renormalizedActivity_le_of_subGaussian`: `hardCore_renormalizedActivity_le`, for general
  Fourier coefficients bounded by `Γ`.
* **`markedDomain_bound_subGaussian`**: `markedDomain_bound` for `(Γ, 0, 0)`-sub-Gaussian
  weights.

The hard-core activity bound `z̄` becomes `Γ` in the damping hypothesis and in (H1).

The conclusion is unchanged.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Marked

open MeasureTheory Reduction

section DomainBoundSubGaussian

variable {boundary : SquareBoundary} {L : ℕ}

/-- **The renormalized activity bound** for `(Γ, 0, 0)`-sub-Gaussian site weights (KP (1.14)
with constant `c ≤ c₁`, KP §2.3.4): for every wave with KP's P2.4 energy bound,
`|K(m)| e^{-E_β(a, m)} ≤ θ_m = e^{-(c/β)(‖m‖² + log₂(d(m) + 1))}`. -/
theorem renormalizedActivity_le_of_subGaussian {D₁ D₂ D₃ Γ β₀ c₁ : ℝ}
    (hdamp : ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ s S A ℓ S₀ : ℝ, 0 ≤ s → 0 ≤ S → 0 ≤ ℓ → ℓ ≤ A → S₀ ≤ s → A ≤ D₁ * (S₀ + S) →
        D₂ * A + (Real.log (max 1 Γ) + 1 + 0 + 0 / β) * s -
            1 / β * (1 / 16 * s + D₃ * S) ≤
          -(c₁ / β) * (s + ℓ))
    (h21 : P21Step boundary L D₁) (cover : MinimumCoverSelection boundary L)
    {β : ℝ} {lamHat : Fin L × Fin L → ℕ → ℝ}
    (hbound : ∀ j q, 1 ≤ q → |lamHat j q| ≤ Γ * Real.exp ((0 + 0 / β) * (q : ℝ) ^ 2))
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N) (K : ChargeDensity L → ℝ)
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    {c : ℝ} (hcc₁ : c ≤ c₁) (hβ : 0 < β) (hββ₀ : β < β₀) {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) :
    ∀ m ∈ N, ∑ j, m j = 0 → ∀ a : Fin L × Fin L → ℝ,
      1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 + D₃ * separatedSquareTotal boundary L cover m) ≤
        SpinWaves.energyFunctional Λ β a m →
      |K m| * Real.exp (-SpinWaves.energyFunctional Λ β a m) ≤ memberWeight boundary c β m := by
  intro m hm hq a hE
  have hm0 := hens.1 m hm
  obtain ⟨hℓA, hAS⟩ := h21 cover m hm0
  have hK := hd m hm hq
  have hP := prod_exp_sq_mul_abs_le m lamHat Γ (0 + 0 / β) hbound
  have hS₀ : (squareCoverNumber boundary L 0 m : ℝ) ≤ ∑ j, (m j : ℝ) ^ 2 :=
    (Nat.cast_le.mpr (squareCoverNumber_zero_le_card boundary L m)).trans
      (card_chargeSupport_le_sum_sq m)
  have hℓ : 0 ≤ Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by
      have := (chargeDiameter boundary L m).cast_nonneg (α := ℝ)
      linarith)
  have hX := hdamp β hβ hββ₀ (∑ j, (m j : ℝ) ^ 2)
    (separatedSquareTotal boundary L cover m) (chargeCoverCost boundary L m)
    (Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1)) (squareCoverNumber boundary L 0 m)
    (Finset.sum_nonneg fun j _ => sq_nonneg _) (Nat.cast_nonneg _) hℓ hℓA hS₀ hAS
  have hs0 : 0 ≤ ∑ j, (m j : ℝ) ^ 2 + Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1) := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (m j : ℝ)
    linarith
  calc |K m| * Real.exp (-SpinWaves.energyFunctional Λ β a m)
      ≤ Real.exp (D₂ * chargeCoverCost boundary L m) *
          Real.exp ((Real.log (max 1 Γ) + 1 + (0 + 0 / β)) * ∑ j, (m j : ℝ) ^ 2) *
        Real.exp (-(1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 +
          D₃ * separatedSquareTotal boundary L cover m))) := by
        refine mul_le_mul ?_ (Real.exp_le_exp.2 (neg_le_neg hE)) (Real.exp_pos _).le
          (by positivity)
        exact hK.trans (mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le)
    _ = Real.exp (D₂ * chargeCoverCost boundary L m +
          (Real.log (max 1 Γ) + 1 + 0 + 0 / β) * ∑ j, (m j : ℝ) ^ 2 -
          1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 +
            D₃ * separatedSquareTotal boundary L cover m)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(c₁ / β) * (∑ j, (m j : ℝ) ^ 2 +
          Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1))) := Real.exp_le_exp.mpr hX
    _ ≤ memberWeight boundary c β m := by
        unfold memberWeight
        refine Real.exp_le_exp.2 ?_
        have : c / β ≤ c₁ / β := div_le_div_of_nonneg_right hcc₁ hβ.le
        nlinarith

/-- **The marked bound on one square domain for sub-Gaussian weights** (FS81 Theorem B before
the limit, CG.s21, for `(Γ, 0, 0)`-sub-Gaussian site weights in the sense of KP Definition 1.4,
e.g. the Fejér weights of the Villain gas). The hypotheses are those of `markedDomain_bound`
with the hard-core weights replaced by `λ_j`; the conclusion is
`|∫ cos(ξ(φ_o − φ_x)) ∏_j λ_j(φ_j) dμ| ≤ 2 e^{-(η²/(16384 D₁ β)) log₂(|o − x| + 1)} 𝒵`, `𝒵 > 0`. -/
theorem markedDomain_bound_subGaussian (hL : 1 < L) {E : Type} [Fintype E]
    (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    {D₁ D₂ D₃ : ℝ} (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h22 : T22Step boundary L D₂) (h21 : P21Step boundary L D₁) (h24 : P24Step boundary Λ D₃)
    {Γ β₀ c₁ : ℝ}
    (hdamp : ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ s S A ℓ S₀ : ℝ, 0 ≤ s → 0 ≤ S → 0 ≤ ℓ → ℓ ≤ A → S₀ ≤ s → A ≤ D₁ * (S₀ + S) →
        D₂ * A + (Real.log (max 1 Γ) + 1 + 0 + 0 / β) * s -
            1 / β * (1 / 16 * s + D₃ * S) ≤
          -(c₁ / β) * (s + ℓ))
    {η c β : ℝ} (hη : 0 < η) (hc : 0 < c) (hcc₁ : c ≤ c₁) (hβ : 0 < β) (hββ₀ : β < β₀)
    (H1 : β * (Real.log (max 1 Γ) + 1 + 0 + 1) + c ≤ η ^ 2 / 32)
    (H2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤ η ^ 2 / (64 * β))
    (H3 : 289 * D₂ * β + 289 * c ≤ η ^ 2 / (16384 * D₁))
    (H4 : Real.exp (-(c / β)) ≤ 1 / 32)
    (v : Fin L × Fin L) (lam : Fin L × Fin L → ℝ → ℝ)
    (hlam : ∀ j, IsSubGaussian Γ 0 0 β (lam j))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hηξ : η ≤ dipoleGap ξ) :
    0 < ∫ φ, ∏ j, lam j (φ j) ∂gffLaw Λ hΛ β hβ v ∧
      |∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, lam j (φ j)
          ∂gffLaw Λ hΛ β hβ v| ≤
        2 * Real.exp (-(η ^ 2 / (16384 * D₁ * β)) *
            Real.logb 2 (latticeDistance boundary L o x + 1)) *
          ∫ φ, ∏ j, lam j (φ j) ∂gffLaw Λ hΛ β hβ v := by
  classical
  have hL0 : 0 < L := by omega
  set μ := gffLaw Λ hΛ β hβ v with hμ
  have := isProbabilityMeasure_gffLaw Λ hΛ β hβ v
  -- the Fourier data of the sub-Gaussian weights and KP Theorem 2.2
  choose Nq hNq lamHat hzero hform hbound using hlam
  obtain ⟨n, N, cc, K, hens, hcpos, hcsum, hid, hprop⟩ := h22 lam Nq lamHat hNq hzero hform
  -- the center choice and the P2.4 cover selection
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → Λ.IsDensityCenter ϱ j := by
    intro ϱ
    by_cases h : ϱ = 0
    · exact ⟨v, fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := Λ.exists_isDensityCenter ϱ h
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  obtain ⟨cover, hcov⟩ := h24 centerOf hcenter
  have hws : WaveSelection boundary Λ centerOf cover D₃ := hcov
  -- the branch bounds
  set ε := 2 * Real.exp (-(η ^ 2 / (16384 * D₁ * β)) *
    Real.logb 2 (latticeDistance boundary L o x + 1)) with hε
  have hθle : ∀ i, ∀ m ∈ N i, memberWeight boundary c β m ≤ 1 / 32 := fun i m hm =>
    (memberWeight_le hc hβ ((hens i).1 m hm)).trans H4
  have hbranch : ∀ i, 0 < ∫ φ, ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ ∧
      |∫ φ, Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ| ≤
        ε * ∫ φ, ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    intro i
    obtain ⟨hNa, hNb, hNc, hd⟩ := hprop i
    have hz := renormalizedActivity_le_of_subGaussian (boundary := boundary) hdamp h21 cover
      hbound (hens i) (K i) hd hcc₁ hβ hββ₀ Λ
    obtain ⟨hZ, hI⟩ := abs_markedBranch_le hL Λ hΛ hdist B h46 centerOf hcenter cover hws hβ v
      (hens i) hNa hNb hNc (K i) (memberWeight boundary c β)
      (fun m hm => (hθle i m hm).trans_lt (by norm_num)) hz hox hξ0 hξ1 hη.le hηξ
    refine ⟨hZ, hI.trans (mul_le_mul_of_nonneg_right ?_ hZ.le)⟩
    -- the exploration-weight sum
    have hmono := markAdjacent_monotone (boundary := boundary) (dipoleMark_ne_zero hox)
    refine sum_le_of_le_explorationWeight hmono (N i) (explorationWeight boundary c β)
      (fun m hm => ?_) _ fun C hC => ?_
    · unfold explorationWeight
      split_ifs
      · exact (hθle i m hm).trans_lt (by norm_num)
      · norm_num
    · split_ifs with hCn
      · have hlam' : ∀ ϱ ∈ N i, ∏ j ∈ chargeSupport ϱ,
            Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs| ≤
              Real.exp ((Real.log (max 1 Γ) + 1 + 0) * ∑ j, (ϱ j : ℝ) ^ 2) := fun ϱ _ => by
          have h := prod_exp_sq_mul_abs_le ϱ lamHat Γ (0 + 0 / β) hbound
          rwa [zero_div, add_zero] at h
        exact cluster_estimate hL hD₁ hD₂ h21 (hens i) hNa hNb (K i) hd hlam' hox hξ0 hξ1 hη
          hηξ hc hβ H1 H2 H3 H4 hC hCn
      · have hπ0 : ∀ m ∈ N i, 0 ≤ explorationWeight boundary c β m := fun m _ => by
          unfold explorationWeight
          split_ifs
          · exact (memberWeight_pos c β m).le
          · norm_num
        have hπ1 : ∀ m ∈ N i, explorationWeight boundary c β m ≤ 1 := fun m hm => by
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
  -- assemble the branches
  have hlamid : ∀ φ : Fin L × Fin L → ℝ, ∏ j, lam j (φ j) =
      ∑ i, cc i * ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) := fun φ => hid φ
  have hint : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ)))) μ := fun i =>
    Reduction.integrable_prod_one_add_mul_cos μ (N i) (K i) (fun m φ => ∑ j, φ j * (m j : ℝ))
      (fun m => by fun_prop)
  have hintc : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ)))) μ := fun i =>
    (hint i).bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hZ : ∫ φ, ∏ j, lam j (φ j) ∂μ =
      ∑ i, cc i * ∫ φ, ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    simp_rw [hlamid]
    rw [integral_finsetSum _ fun i _ => (hint i).const_mul (cc i)]
    simp_rw [integral_const_mul]
  have hI : ∫ φ, Real.cos (ξ * (φ o - φ x)) * ∏ j, lam j (φ j) ∂μ =
      ∑ i, cc i * ∫ φ, Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ))) ∂μ := by
    have hpt : ∀ φ : Fin L × Fin L → ℝ,
        Real.cos (ξ * (φ o - φ x)) * ∏ j, lam j (φ j) =
        ∑ i, cc i * (Real.cos (ξ * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ m ∈ N i, (1 + K i m * Real.cos (∑ j, φ j * (m j : ℝ)))) := by
      intro φ
      rw [hlamid, Finset.mul_sum, sum_mul_dipoleMark]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
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
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hcpos i), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hbranch i).2 (hcpos i).le

end DomainBoundSubGaussian

end FroehlichSpencer.BKT.Generic.Marked
