/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.TheoremB
public import FroehlichSpencer.BKT.Coulomb.ConditionLambda
import Mathlib.Tactic

/-!
# FS81 Theorem B for a restricted Condition-λ regime, at a finite Fourier cutoff

The finite-cutoff statement uses `ConditionLambdaInternal C a θ κ λ`, with the additional
smallness condition `θ < η²/128`. Its constants are fixed before the cutoff, square, charge region,
root and dipole are selected. The proof feeds the arbitrary Fourier polynomial to KP T2.2, then
uses the marked cluster estimates and the same T2.2/P2.1/P2.4 dependencies as the hard-core
theorem. The full FS81 range `θ < 1/16` remains open here: the current marked cluster estimate
requires an additional theta dependent H1 bound when θ enters the `q²` coefficient.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory FroehlichSpencer.BKT.Generic.Marked Reduction

/-! ### General Fourier coefficients in the marked cluster bound -/

section Domain

variable {boundary : SquareBoundary} {L : ℕ}

/-- Renormalized activities for a general Fourier coefficient bound. -/
theorem conditionLambda_renormalizedActivity_le {D₁ D₂ D₃ Γ a β₀ c₁ : ℝ}
    {θ : ℝ}
    (hdamp : ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ s S A ℓ S₀ : ℝ, 0 ≤ s → 0 ≤ S → 0 ≤ ℓ → ℓ ≤ A → S₀ ≤ s →
        A ≤ D₁ * (S₀ + S) →
        D₂ * A + (Real.log (max 1 Γ) + 1 + a + θ / β) * s -
            1 / β * (1 / 16 * s + D₃ * S) ≤
          -(c₁ / β) * (s + ℓ))
    (h21 : P21Step boundary L D₁) (cover : MinimumCoverSelection boundary L)
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N) (K : ChargeDensity L → ℝ)
    {lamHat : Fin L × Fin L → ℕ → ℝ}
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    {c β : ℝ} (hcc₁ : c ≤ c₁) (hβ : 0 < β) (hββ₀ : β < β₀)
    (hlam : ∀ j q, 1 ≤ q →
      |lamHat j q| ≤ Γ * Real.exp ((a + θ / β) * (q : ℝ) ^ 2))
    {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E) :
    ∀ m ∈ N, ∑ j, m j = 0 → ∀ w : Fin L × Fin L → ℝ,
      1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 +
        D₃ * separatedSquareTotal boundary L cover m) ≤
          SpinWaves.energyFunctional Λ β w m →
      |K m| * Real.exp (-SpinWaves.energyFunctional Λ β w m) ≤
        memberWeight boundary c β m := by
  intro m hm hneutral w henergy
  have hm0 := hens.1 m hm
  obtain ⟨hℓA, hAS⟩ := h21 cover m hm0
  have hK := hd m hm hneutral
  have hprod := prod_exp_sq_mul_abs_le m lamHat Γ (a + θ / β) hlam
  have hprod' : ∏ j ∈ chargeSupport m,
      Real.exp ((m j : ℝ) ^ 2) * |lamHat j (m j).natAbs| ≤
        Real.exp ((Real.log (max 1 Γ) + 1 + (a + θ / β)) * ∑ j, (m j : ℝ) ^ 2) := by
    simpa only [chargeSupport] using hprod
  have hK' : |K m| ≤ Real.exp (D₂ * chargeCoverCost boundary L m) *
      Real.exp ((Real.log (max 1 Γ) + 1 + (a + θ / β)) * ∑ j, (m j : ℝ) ^ 2) := by
    calc |K m| ≤ Real.exp (D₂ * chargeCoverCost boundary L m) *
          ∏ j ∈ chargeSupport m,
          Real.exp ((m j : ℝ) ^ 2) * |lamHat j (m j).natAbs| := hK
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod' (Real.exp_pos _).le
  have hS₀ : (squareCoverNumber boundary L 0 m : ℝ) ≤ ∑ j, (m j : ℝ) ^ 2 :=
    (Nat.cast_le.mpr (squareCoverNumber_zero_le_card boundary L m)).trans
      (card_chargeSupport_le_sum_sq m)
  have hℓ : 0 ≤ Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by
      have := (chargeDiameter boundary L m).cast_nonneg (α := ℝ)
      linarith)
  have hX := hdamp β hβ hββ₀ (∑ j, (m j : ℝ) ^ 2)
    (separatedSquareTotal boundary L cover m) (chargeCoverCost boundary L m)
    (Real.logb 2 ((chargeDiameter boundary L m : ℝ) + 1))
    (squareCoverNumber boundary L 0 m)
    (Finset.sum_nonneg fun j _ => sq_nonneg _) (Nat.cast_nonneg _) hℓ hℓA hS₀ hAS
  calc
    |K m| * Real.exp (-SpinWaves.energyFunctional Λ β w m)
      ≤ Real.exp (D₂ * chargeCoverCost boundary L m) *
          Real.exp ((Real.log (max 1 Γ) + 1 + (a + θ / β)) * ∑ j, (m j : ℝ) ^ 2) *
          Real.exp (-(1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 +
            D₃ * separatedSquareTotal boundary L cover m))) := by
        refine mul_le_mul ?_ (Real.exp_le_exp.2 (neg_le_neg henergy))
          (Real.exp_pos _).le (by positivity)
        exact hK'
    _ = Real.exp (D₂ * chargeCoverCost boundary L m +
          (Real.log (max 1 Γ) + 1 + a + θ / β) * ∑ j, (m j : ℝ) ^ 2 -
          1 / β * (1 / 16 * ∑ j, (m j : ℝ) ^ 2 +
            D₃ * separatedSquareTotal boundary L cover m)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    _ ≤ Real.exp (-(c₁ / β) *
          (∑ j, (m j : ℝ) ^ 2 + Real.logb 2 (chargeDiameter boundary L m + 1))) :=
      Real.exp_le_exp.mpr (by convert hX using 1)
    _ ≤ memberWeight boundary c β m := by
          unfold memberWeight
          apply Real.exp_le_exp.mpr
          have hc : c / β ≤ c₁ / β := div_le_div_of_nonneg_right hcc₁ hβ.le
          have hsum : 0 ≤ ∑ j, (m j : ℝ) ^ 2 +
              Real.logb 2 (chargeDiameter boundary L m + 1) := add_nonneg
            (Finset.sum_nonneg fun j _ => sq_nonneg _) hℓ
          nlinarith [mul_nonneg (sub_nonneg.mpr hc) hsum]

/-- The marked bound for a finite even Fourier product whose coefficients have a fixed Gaussian
growth bound. The constants in `H1`–`H4` and the conclusion are independent of the polynomial
degree and of the coefficient functions. -/
theorem markedConditionLambdaDomain_bound (hL : 1 < L) {E : Type} [Fintype E]
    (boundary : SquareBoundary) (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    {D₁ D₂ D₃ θ : ℝ} (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
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
    (H1 : β * (Real.log (max 1 Γ) + 1 + (a + θ / β) + 1) + c ≤ η ^ 2 / 32)
    (H2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤
      η ^ 2 / (64 * β))
    (H3 : 289 * D₂ * β + 289 * c ≤ η ^ 2 / (16384 * D₁))
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
        2 * Real.exp (-(η ^ 2 / (16384 * D₁ * β)) *
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
  set ε := 2 * Real.exp (-(η ^ 2 / (16384 * D₁ * β)) *
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
      · exact cluster_estimate hL hD₁ hD₂ h21 (hens i) hNa hNb (K i) hd
          (fun ϱ hϱ => prod_exp_sq_mul_abs_le ϱ lamHat Γ (a + θ / β) hbound)
          hox hξ0 hξ1 hη hηξ hc hβ H1 H2 H3 H4 hC hCn
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

/-! ### Uniform square bounds for Condition-λ laws -/

section Squares

/-- A Condition-λ law-specific coefficient bound for the Fourier coefficients at cutoff `N`.
The growth data `a, θ` are independent of the cutoff. -/
def ConditionLambdaMarkedSquareBoundInternal (boundary : SquareBoundary) {L : ℕ}
    {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected) (C a θ cB η κ₀ : ℝ) : Prop :=
  ∀ (κ : ℝ), κ₀ < κ → ∀ (hκ : 0 < κ), ∀ lam : ℤ → ℝ,
    ConditionLambdaInternal C a θ κ lam → lam 0 = 1 →
    ∀ (N : ℕ) (A : Finset (Fin L × Fin L)) (v : Fin L × Fin L)
      (o x : Fin L × Fin L), o ≠ x → ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
      0 < weightedGFFNormalizer Λ hΛ κ⁻¹ (inv_pos.2 hκ) v
          (fun j => sineGordonWeightInternal N (regionWeightInternal A lam j)) ∧
        |∫ φ, Real.cos (ξ * (φ o - φ x)) *
            ∏ j, sineGordonWeightInternal N (regionWeightInternal A lam j) (φ j)
          ∂gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v| ≤
          2 * Real.exp (-(cB * η ^ 2 * κ) *
            Real.logb 2 (latticeDistance boundary L o x + 1)) *
            weightedGFFNormalizer Λ hΛ κ⁻¹ (inv_pos.2 hκ) v
              (fun j => sineGordonWeightInternal N (regionWeightInternal A lam j))

/-- The restricted Condition-λ marked square estimate. The threshold depends on the growth
constants `C,a,θ` and the dipole gap `η`, while one threshold works for every square, region, root,
fractional charge and Fourier cutoff. -/
theorem markedConditionLambdaSquareBound_exists :
    ∃ cB : ℝ, 0 < cB ∧ ∀ C a θ : ℝ, 0 ≤ C → 0 ≤ a → θ < 1 / 16 →
      ∀ η : ℝ, 0 < η → θ < η ^ 2 / 128 → ∃ κ₀ : ℝ, 0 < κ₀ ∧
        ∀ L : ℕ, ∀ hL : 1 < L,
        ConditionLambdaMarkedSquareBoundInternal .free (squareFree L)
            (squareFree_connected L hL) C a θ cB η κ₀ ∧
          (Even L → ConditionLambdaMarkedSquareBoundInternal .periodic (squarePeriodic L)
            (squarePeriodic_connected L hL) C a θ cB η κ₀) := by
  obtain ⟨D₂, hD₂, h22⟩ := t22Statement_of_repairedBasicLemma
  obtain ⟨D₃, hD₃, h24⟩ := p24_of_l46 SpinWaves.BoundaryShellPacking.l46Statement_holds
  obtain ⟨D₁, hD₁, h21⟩ := kp_p21Statement
  let D₁' := max D₁ 1
  have hD₁'1 : 1 ≤ D₁' := le_max_right _ _
  have hmono : ∀ {boundary : SquareBoundary} {L : ℕ}, P21Step boundary L D₁ →
      P21Step boundary L D₁' := by
    intro boundary L h cover ϱ hϱ
    obtain ⟨h1, h2⟩ := h cover ϱ hϱ
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  let cB := 1 / (16384 * D₁')
  refine ⟨cB, by dsimp [cB]; positivity, fun C a θ hC ha hθ η hη hθη => ?_⟩
  let Γ := max 1 C
  obtain ⟨β₀, c₁, hβ₀, hc₁, hdamp⟩ := exists_damping_constants Γ a θ D₁' D₂ D₃
    hθ (by linarith) hD₂ hD₃
  let h := Real.log Γ + 1 + a
  have hh0 : 0 ≤ h := by
    dsimp [h, Γ]
    have := Real.log_nonneg (le_max_left 1 C)
    linarith
  let c := min c₁ (η ^ 2 / (2 * 289 * 16384 * D₁'))
  have hcpos : 0 < c := lt_min hc₁ (by positivity)
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hcη : c ≤ η ^ 2 / (2 * 289 * 16384 * D₁') := min_le_right _ _
  let β₁ := min β₀ (min (η ^ 2 / (128 * (h + 1)))
      (min (η ^ 2 / (2 * 16384 * 289 * D₁' * max D₂ 1)) (c / 20)))
  have hβ₁pos : 0 < β₁ := by
    dsimp [β₁]
    exact lt_min hβ₀ (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  obtain ⟨κcut, hκcut, hcut⟩ :=
    conditionLambda_cutoff_bound 1 (by norm_num) Γ a θ hθ
  let κ₀ := max β₁⁻¹ κcut
  have hκ₀pos : 0 < κ₀ := by
    dsimp [κ₀]
    exact lt_of_lt_of_le hκcut (le_max_right _ _)
  refine ⟨κ₀, hκ₀pos, fun L hL => ?_⟩
  have hH : ∀ β : ℝ, 0 < β → β < β₁ → β < β₀ ∧
      β * (Real.log Γ + 1 + a + 1) + θ + c ≤ η ^ 2 / 32 ∧
      4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤ η ^ 2 / (64 * β) ∧
      289 * D₂ * β + 289 * c ≤ η ^ 2 / (16384 * D₁') ∧
      Real.exp (-(c / β)) ≤ 1 / 32 := by
    intro β hβ hββ₁
    have k0 : β < β₀ := lt_of_lt_of_le hββ₁ (min_le_left _ _)
    have k1 : β ≤ η ^ 2 / (128 * (h + 1)) :=
      hββ₁.le.trans (min_le_right _ _ |>.trans (min_le_left _ _))
    have k2 : β ≤ η ^ 2 / (2 * 16384 * 289 * D₁' * max D₂ 1) :=
      hββ₁.le.trans (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_left _ _)))
    have k3 : β ≤ c / 20 :=
      hββ₁.le.trans (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_right _ _)))
    have k1' : β ≤ η ^ 2 / (64 * (h + 1)) := by
      have hfrac : η ^ 2 / (128 * (h + 1)) ≤ η ^ 2 / (64 * (h + 1)) := by
        gcongr
        norm_num
      exact k1.trans hfrac
    obtain ⟨_, H2, H3, H4⟩ := markedThresholds hD₁'1 hh0 hη hcpos hcη hβ k1' k2 k3
    have hβterm : β * (h + 1) ≤ η ^ 2 / 128 := by
      rw [le_div_iff₀ (by positivity)] at k1
      nlinarith
    have hcsmall : c ≤ η ^ 2 / 64 := by
      let den : ℝ := 2 * 289 * 16384 * D₁'
      have hden : 0 < den := by positivity
      have hden64 : 64 ≤ den := by dsimp [den]; nlinarith [hD₁'1]
      have hcomp : η ^ 2 / den ≤ η ^ 2 / 64 := by
        rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 64)]
        exact mul_le_mul_of_nonneg_left hden64 (by positivity)
      exact hcη.trans (by simpa [den] using hcomp)
    have htheta : θ ≤ η ^ 2 / 128 := hθη.le
    have H1 : β * (Real.log Γ + 1 + a + 1) + θ + c ≤ η ^ 2 / 32 := by
      dsimp [h] at hβterm
      nlinarith
    exact ⟨k0, H1, H2, H3, H4⟩
  have hcutFree := hcut L hL |>.1
  have hcutPer := hcut L hL |>.2
  refine ⟨?_, ?_⟩
  · intro κ hκκ₀ hκpos lam hlam h0 N A v o x hox ξ hξ0 hξ1 hηξ
    have hβ : 0 < κ⁻¹ := inv_pos.2 hκpos
    have hββ₁ : κ⁻¹ < β₁ := by
      have hκβ : β₁⁻¹ < κ := (lt_of_le_of_lt (le_max_left _ _) hκκ₀)
      exact (inv_lt_comm₀ hκpos hβ₁pos).2 hκβ
    have ⟨hββ₀, H1, H2, H3, H4⟩ := hH κ⁻¹ hβ hββ₁
    have hCcut : ConditionLambdaInternal Γ a θ κ lam := by
      refine ⟨hlam.1, fun q => ?_⟩
      have hq := hlam.2 q
      exact hq.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.exp_pos _).le)
    have hregion : ∀ j, ConditionLambdaInternal Γ a θ κ (regionWeightInternal A lam j) :=
      fun j => by
        have hr := conditionLambda_regionWeight A hCcut j
        simpa [Γ, max_assoc] using hr
    have hregion0 : ∀ j, regionWeightInternal A lam j 0 = 1 :=
      fun j => regionWeight_zero A h0 j
    have hT : (squareFree L).IsLaplacianPseudoinverse
        ((squareFree L).greenOp (squareFree_connected L hL)) := by
      exact ⟨fun f hf => ⟨(squareFree L).laplacian_greenOp_of_sum_eq_zero
        (squareFree_connected L hL) f hf,
        (squareFree L).greenOp_laplacian_of_sum_eq_zero (squareFree_connected L hL) f hf⟩,
        (squareFree L).greenOp_const (squareFree_connected L hL)⟩
    have hcutZ := hcutFree κ (lt_of_le_of_lt (le_max_right _ _) hκκ₀)
      (fun j => regionWeightInternal A lam j) hregion hregion0 N
      ((squareFree L).greenOp (squareFree_connected L hL)) hT
    have H1' : κ⁻¹ * (Real.log (max 1 Γ) + 1 + (a + θ / κ⁻¹) + 1) + c ≤ η ^ 2 / 32 := by
      have hcoef : κ⁻¹ * (Real.log Γ + 1 + a + 1) + θ + c =
          κ⁻¹ * (Real.log Γ + 1 + (a + θ / κ⁻¹) + 1) + c := by
        field_simp
        ring
      have H1Γ : κ⁻¹ * (Real.log Γ + 1 + a + 1) + θ + c ≤ η ^ 2 / 32 := by
        simpa [Γ, max_assoc] using H1
      calc κ⁻¹ * (Real.log (max 1 Γ) + 1 + (a + θ / κ⁻¹) + 1) + c
          = κ⁻¹ * (Real.log Γ + 1 + (a + θ / κ⁻¹) + 1) + c := by simp [Γ]
        _ = κ⁻¹ * (Real.log Γ + 1 + a + 1) + θ + c := by
          rw [hcoef]
        _ ≤ η ^ 2 / 32 := H1Γ
    have hFourierBound : ∀ j q, 1 ≤ q →
        |(if q ≤ N then regionWeightInternal A lam j q else 0)| ≤
          Γ * Real.exp ((a + θ / κ⁻¹) * (q : ℝ) ^ 2) := by
      intro j q hq
      by_cases hqN : q ≤ N
      · by_cases hj : j ∈ A
        · have h := hlam.2 (q : ℤ)
          have hΓ : C ≤ Γ := le_max_right _ _
          have hcoef : a + θ / κ⁻¹ = a + θ * κ := by field_simp
          have hLam : |lam (q : ℤ)| ≤ C * Real.exp ((a + θ / κ⁻¹) * (q : ℝ) ^ 2) := by
            rw [hcoef]
            simpa using h
          have hUpper : |lam (q : ℤ)| ≤ Γ * Real.exp ((a + θ / κ⁻¹) * (q : ℝ) ^ 2) :=
            hLam.trans (mul_le_mul_of_nonneg_right hΓ (Real.exp_pos _).le)
          simpa [hqN, regionWeightInternal, hj] using hUpper
        · have hq0 : q ≠ 0 := by omega
          simp [hqN, regionWeightInternal, hj, hq0]
          positivity
      · simp [hqN]
        positivity
    have hmarked := markedConditionLambdaDomain_bound hL .free (squareFree L)
      (squareFree_connected L hL) (fun _ _ => rfl)
      (SpinWaves.squareFreeBipartiteDegreeFour L hL)
      (SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).1 hD₁'1 hD₂.le
      (h22 L hL).1 (hmono (h21 L hL).1) (h24 L hL).1 hdamp hη hcpos hcc₁ hβ hββ₀
      H1' H2 H3 H4 v
      (fun j φ => sineGordonWeightInternal N (regionWeightInternal A lam j) φ)
      (fun _ => N + 1) (fun j q => if q ≤ N then regionWeightInternal A lam j q else 0)
      (fun _ => Nat.succ_pos N)
      (by
        intro j q hq
        have hqN : ¬ q ≤ N := by omega
        simp [hqN])
      (by
        intro j φ
        unfold sineGordonWeightInternal
        rw [sum_Icc_eq_zero_add_two_mul N (fun q => regionWeightInternal A lam j q *
          Real.cos (q * φ)) (fun q => by
            rw [regionWeight_neg A hlam.1 j]
            simp only [Int.cast_neg, neg_mul, Real.cos_neg])]
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one, hregion0 j,
          Int.cast_natCast, show ¬ (N + 1 ≤ N) by omega, ite_false, zero_mul, add_zero]
        congr 2
        refine Finset.sum_congr rfl fun q hq => ?_
        have hqN := (Finset.mem_Icc.mp hq).2
        simp [hqN])
      hFourierBound
      hox hξ0 hξ1 hηξ
    have hZ : 0 < weightedGFFNormalizer (squareFree L) (squareFree_connected L hL)
        κ⁻¹ hβ v (fun j => sineGordonWeightInternal N (regionWeightInternal A lam j)) := by
      rw [weightedGFFNormalizer_sineGordon (squareFree L) (squareFree_connected L hL) κ hκpos
        v N (fun j => regionWeightInternal A lam j)
        (fun j n => regionWeight_neg A hlam.1 j n)
        ((squareFree L).greenOp (squareFree_connected L hL)) hT]
      exact hcutZ.1
    have hnorm := weightedGFFNormalizer_eq (squareFree L) (squareFree_connected L hL)
      κ⁻¹ hβ v (fun j => sineGordonWeightInternal N (regionWeightInternal A lam j))
    rw [← hnorm] at hmarked
    have hexp : η ^ 2 / (16384 * D₁' * κ⁻¹) =
        (1 / (16384 * D₁')) * η ^ 2 * κ := by
      field_simp
    refine ⟨hZ, ?_⟩
    rw [hexp] at hmarked
    simpa only [show 1 / (16384 * D₁') = 1 / (16384 * max D₁ 1) by rfl] using hmarked.2
  · intro hE κ hκκ₀ hκpos lam hlam h0 N A v o x hox ξ hξ0 hξ1 hηξ
    have hβ : 0 < κ⁻¹ := inv_pos.2 hκpos
    have hββ₁ : κ⁻¹ < β₁ := by
      have hκβ : β₁⁻¹ < κ := (lt_of_le_of_lt (le_max_left _ _) hκκ₀)
      exact (inv_lt_comm₀ hκpos hβ₁pos).2 hκβ
    have ⟨hββ₀, H1, H2, H3, H4⟩ := hH κ⁻¹ hβ hββ₁
    have hCcut : ConditionLambdaInternal Γ a θ κ lam := by
      refine ⟨hlam.1, fun q => ?_⟩
      have hq := hlam.2 q
      exact hq.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.exp_pos _).le)
    have hregion : ∀ j, ConditionLambdaInternal Γ a θ κ (regionWeightInternal A lam j) :=
      fun j => by
        have hr := conditionLambda_regionWeight A hCcut j
        simpa [Γ, max_assoc] using hr
    have hregion0 : ∀ j, regionWeightInternal A lam j 0 = 1 :=
      fun j => regionWeight_zero A h0 j
    have hT : (squarePeriodic L).IsLaplacianPseudoinverse
        ((squarePeriodic L).greenOp (squarePeriodic_connected L hL)) := by
      exact ⟨fun f hf => ⟨(squarePeriodic L).laplacian_greenOp_of_sum_eq_zero
        (squarePeriodic_connected L hL) f hf,
        (squarePeriodic L).greenOp_laplacian_of_sum_eq_zero (squarePeriodic_connected L hL) f hf⟩,
        (squarePeriodic L).greenOp_const (squarePeriodic_connected L hL)⟩
    have hcutZ := hcutPer hE κ (lt_of_le_of_lt (le_max_right _ _) hκκ₀)
      (fun j => regionWeightInternal A lam j) hregion hregion0 N
      ((squarePeriodic L).greenOp (squarePeriodic_connected L hL)) hT
    have H1' : κ⁻¹ * (Real.log (max 1 Γ) + 1 + (a + θ / κ⁻¹) + 1) + c ≤ η ^ 2 / 32 := by
      have hcoef : κ⁻¹ * (Real.log Γ + 1 + a + 1) + θ + c =
          κ⁻¹ * (Real.log Γ + 1 + (a + θ / κ⁻¹) + 1) + c := by
        field_simp
        ring
      have H1Γ : κ⁻¹ * (Real.log Γ + 1 + a + 1) + θ + c ≤ η ^ 2 / 32 := by
        simpa [Γ, max_assoc] using H1
      calc κ⁻¹ * (Real.log (max 1 Γ) + 1 + (a + θ / κ⁻¹) + 1) + c
          = κ⁻¹ * (Real.log Γ + 1 + (a + θ / κ⁻¹) + 1) + c := by simp [Γ]
        _ = κ⁻¹ * (Real.log Γ + 1 + a + 1) + θ + c := by rw [hcoef]
        _ ≤ η ^ 2 / 32 := H1Γ
    have hFourierBound : ∀ j q, 1 ≤ q →
        |(if q ≤ N then regionWeightInternal A lam j q else 0)| ≤
          Γ * Real.exp ((a + θ / κ⁻¹) * (q : ℝ) ^ 2) := by
      intro j q hq
      by_cases hqN : q ≤ N
      · by_cases hj : j ∈ A
        · have h := hlam.2 (q : ℤ)
          have hΓ : C ≤ Γ := le_max_right _ _
          have hcoef : a + θ / κ⁻¹ = a + θ * κ := by field_simp
          have hLam : |lam (q : ℤ)| ≤ C * Real.exp ((a + θ / κ⁻¹) * (q : ℝ) ^ 2) := by
            rw [hcoef]
            simpa using h
          have hUpper : |lam (q : ℤ)| ≤ Γ * Real.exp ((a + θ / κ⁻¹) * (q : ℝ) ^ 2) :=
            hLam.trans (mul_le_mul_of_nonneg_right hΓ (Real.exp_pos _).le)
          simpa [hqN, regionWeightInternal, hj] using hUpper
        · have hq0 : q ≠ 0 := by omega
          simp [hqN, regionWeightInternal, hj, hq0]
          positivity
      · simp [hqN]
        positivity
    have hmarked := markedConditionLambdaDomain_bound hL .periodic (squarePeriodic L)
      (squarePeriodic_connected L hL) (fun _ _ => rfl)
      (SpinWaves.squarePeriodicBipartiteDegreeFour L hE hL)
      ((SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).2 hE) hD₁'1 hD₂.le
      ((h22 L hL).2 hE) (hmono ((h21 L hL).2 hE)) ((h24 L hL).2 hE) hdamp hη hcpos hcc₁
      hβ hββ₀ H1' H2 H3 H4 v
      (fun j φ => sineGordonWeightInternal N (regionWeightInternal A lam j) φ)
      (fun _ => N + 1) (fun j q => if q ≤ N then regionWeightInternal A lam j q else 0)
      (fun _ => Nat.succ_pos N)
      (by
        intro j q hq
        have hqN : ¬ q ≤ N := by omega
        simp [hqN])
      (by
        intro j φ
        unfold sineGordonWeightInternal
        rw [sum_Icc_eq_zero_add_two_mul N (fun q => regionWeightInternal A lam j q *
          Real.cos (q * φ)) (fun q => by
            rw [regionWeight_neg A hlam.1 j]
            simp only [Int.cast_neg, neg_mul, Real.cos_neg])]
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one, hregion0 j,
          Int.cast_natCast, show ¬ (N + 1 ≤ N) by omega, ite_false, zero_mul, add_zero]
        congr 2
        refine Finset.sum_congr rfl fun q hq => ?_
        have hqN := (Finset.mem_Icc.mp hq).2
        simp [hqN])
      hFourierBound
      hox hξ0 hξ1 hηξ
    have hZ : 0 < weightedGFFNormalizer (squarePeriodic L) (squarePeriodic_connected L hL)
        κ⁻¹ hβ v (fun j => sineGordonWeightInternal N (regionWeightInternal A lam j)) := by
      rw [weightedGFFNormalizer_sineGordon (squarePeriodic L) (squarePeriodic_connected L hL) κ hκpos
        v N (fun j => regionWeightInternal A lam j)
        (fun j n => regionWeight_neg A hlam.1 j n)
        ((squarePeriodic L).greenOp (squarePeriodic_connected L hL)) hT]
      exact hcutZ.1
    have hnorm := weightedGFFNormalizer_eq (squarePeriodic L) (squarePeriodic_connected L hL)
      κ⁻¹ hβ v (fun j => sineGordonWeightInternal N (regionWeightInternal A lam j))
    rw [← hnorm] at hmarked
    have hexp : η ^ 2 / (16384 * D₁' * κ⁻¹) =
        (1 / (16384 * D₁')) * η ^ 2 * κ := by
      field_simp
    refine ⟨hZ, ?_⟩
    rw [hexp] at hmarked
    simpa only [show 1 / (16384 * D₁') = 1 / (16384 * max D₁ 1) by rfl] using hmarked.2

end Squares

end FroehlichSpencer.BKT.Coulomb
