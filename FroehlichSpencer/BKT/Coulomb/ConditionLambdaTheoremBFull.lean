/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBFullDomain
import Mathlib.Tactic

/-!
# Condition-λ marked square bounds in the whole range `θ < 1/16`

`markedConditionLambdaSquareBound_split_exists` is the analogue of the marked-cluster estimate's
`markedConditionLambdaSquareBound_exists` without the restriction `θ < η²/128`. Write
`δ = 1/16 − max(θ, 0)`. Then for every Condition-λ law with data `(C, a, θ)`:
* one threshold `κ₀(C, a, θ, η)` serves every free or even periodic square, charge region, root,
  dipole, fractional charge and Fourier cutoff;
* the bound is `2 e^{κ/(64δ)} e^{−cB·8δ·η²κ log₂(|o − x| + 1)}` times the normalizer
  (`ConditionLambdaMarkedSquareBoundSplitInternal`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory FroehlichSpencer.BKT.Generic.Marked Reduction

/-! ### Uniform square bounds in the whole Condition-λ range -/

section Squares

/-- The marked square estimate with a prefactor `e^{Pκ}`, uniform in the Fourier cutoff `N`, the
charge region, the root and the dipole. -/
def ConditionLambdaMarkedSquareBoundSplitInternal (boundary : SquareBoundary) {L : ℕ}
    {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected) (C a θ cB η κ₀ P : ℝ) : Prop :=
  ∀ (κ : ℝ), κ₀ < κ → ∀ (hκ : 0 < κ), ∀ lam : ℤ → ℝ,
    ConditionLambdaInternal C a θ κ lam → lam 0 = 1 →
    ∀ (N : ℕ) (A : Finset (Fin L × Fin L)) (v : Fin L × Fin L)
      (o x : Fin L × Fin L), o ≠ x → ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
      0 < weightedGFFNormalizer Λ hΛ κ⁻¹ (inv_pos.2 hκ) v
          (fun j => sineGordonWeightInternal N (regionWeightInternal A lam j)) ∧
        |∫ φ, Real.cos (ξ * (φ o - φ x)) *
            ∏ j, sineGordonWeightInternal N (regionWeightInternal A lam j) (φ j)
          ∂gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v| ≤
          2 * Real.exp (P * κ) * Real.exp (-(cB * η ^ 2 * κ) *
            Real.logb 2 (latticeDistance boundary L o x + 1)) *
            weightedGFFNormalizer Λ hΛ κ⁻¹ (inv_pos.2 hκ) v
              (fun j => sineGordonWeightInternal N (regionWeightInternal A lam j))

/-- **The marked square estimate in the whole range `θ < 1/16`.** With `δ = 1/16 − max(θ, 0)`, one
threshold `κ₀(C, a, θ, η)` works for every square, region, root, fractional charge and Fourier
cutoff; the decay rate is `cB · 8δ · η² κ` and the prefactor `2 e^{κ/(64δ)}`. -/
theorem markedConditionLambdaSquareBound_split_exists :
    ∃ cB : ℝ, 0 < cB ∧ ∀ C a θ : ℝ, 0 ≤ C → 0 ≤ a → θ < 1 / 16 →
      ∀ η : ℝ, 0 < η → ∃ κ₀ : ℝ, 0 < κ₀ ∧
        ∀ L : ℕ, ∀ hL : 1 < L,
        ConditionLambdaMarkedSquareBoundSplitInternal .free (squareFree L)
            (squareFree_connected L hL) C a θ (cB * (8 * (1 / 16 - max θ 0))) η κ₀
            (1 / (64 * (1 / 16 - max θ 0))) ∧
          (Even L → ConditionLambdaMarkedSquareBoundSplitInternal .periodic (squarePeriodic L)
            (squarePeriodic_connected L hL) C a θ (cB * (8 * (1 / 16 - max θ 0))) η κ₀
            (1 / (64 * (1 / 16 - max θ 0)))) := by
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
  refine ⟨cB, by dsimp [cB]; positivity, fun C a θ hC ha hθ η hη => ?_⟩
  let Γ := max 1 C
  have hΓ1 : max 1 Γ = Γ := max_eq_right (le_max_left _ _)
  set θ' := max θ 0 with hθ'
  set δ := 1 / 16 - θ' with hδdef
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hθθ' : θ ≤ θ' := le_max_left _ _
  have hθ'1 : θ' < 1 / 16 := max_lt hθ (by norm_num)
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hθ'δ : θ' + δ = 1 / 16 := by rw [hδdef]; ring
  set η' := Real.sqrt (8 * δ) * η with hη'def
  have hη'sq : η' ^ 2 = 8 * δ * η ^ 2 := by
    rw [hη'def, mul_pow, Real.sq_sqrt (by linarith)]
  have hη' : 0 < η' := by
    rw [hη'def]; exact mul_pos (Real.sqrt_pos.2 (by linarith)) hη
  obtain ⟨β₀, c₁, hβ₀, hc₁, hdamp⟩ := exists_damping_constants Γ a θ' D₁' D₂ D₃
    hθ'1 (by linarith) hD₂ hD₃
  let h := Real.log Γ + 1 + a
  have hh0 : 0 ≤ h := by
    dsimp [h, Γ]
    have := Real.log_nonneg (le_max_left 1 C)
    linarith
  let c := min c₁ (η' ^ 2 / (2 * 289 * 16384 * D₁'))
  have hcpos : 0 < c := lt_min hc₁ (by positivity)
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hcη : c ≤ η' ^ 2 / (2 * 289 * 16384 * D₁') := min_le_right _ _
  let β₁ := min β₀ (min (η' ^ 2 / (64 * (h + 1)))
      (min (η' ^ 2 / (2 * 16384 * 289 * D₁' * max D₂ 1)) (c / 20)))
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
      β * (Real.log Γ + 1 + a + 1) + c ≤ 8 * δ * η ^ 2 / 32 ∧
      4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β))) ≤
        8 * δ * η ^ 2 / (64 * β) ∧
      289 * D₂ * β + 289 * c ≤ 8 * δ * η ^ 2 / (16384 * D₁') ∧
      Real.exp (-(c / β)) ≤ 1 / 32 := by
    intro β hβ hββ₁
    have k0 : β < β₀ := lt_of_lt_of_le hββ₁ (min_le_left _ _)
    have k1 : β ≤ η' ^ 2 / (64 * (h + 1)) :=
      hββ₁.le.trans (min_le_right _ _ |>.trans (min_le_left _ _))
    have k2 : β ≤ η' ^ 2 / (2 * 16384 * 289 * D₁' * max D₂ 1) :=
      hββ₁.le.trans (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_left _ _)))
    have k3 : β ≤ c / 20 :=
      hββ₁.le.trans (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_right _ _)))
    obtain ⟨H1, H2, H3, H4⟩ := markedThresholds hD₁'1 hh0 hη' hcpos hcη hβ k1 k2 k3
    rw [hη'sq] at H1 H2 H3
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
    have H1' : κ⁻¹ * (Real.log (max 1 Γ) + 1 + a + 1) + c ≤ 8 * δ * η ^ 2 / 32 := by
      rw [hΓ1]; exact H1
    have hFourierBound : ∀ j q, 1 ≤ q →
        |(if q ≤ N then regionWeightInternal A lam j q else 0)| ≤
          Γ * Real.exp ((a + θ' / κ⁻¹) * (q : ℝ) ^ 2) := by
      intro j q hq
      by_cases hqN : q ≤ N
      · by_cases hj : j ∈ A
        · have h := hlam.2 (q : ℤ)
          have hΓ : C ≤ Γ := le_max_right _ _
          have hcoef : a + θ' / κ⁻¹ = a + θ' * κ := by field_simp
          have hLam : |lam (q : ℤ)| ≤ C * Real.exp ((a + θ' / κ⁻¹) * (q : ℝ) ^ 2) := by
            rw [hcoef]
            have hmon : (a + θ * κ) * ((q : ℤ) : ℝ) ^ 2 ≤ (a + θ' * κ) * (q : ℝ) ^ 2 := by
              push_cast
              exact mul_le_mul_of_nonneg_right
                (add_le_add_right (mul_le_mul_of_nonneg_right hθθ' hκpos.le) a) (sq_nonneg _)
            exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hmon) hC)
          have hUpper : |lam (q : ℤ)| ≤ Γ * Real.exp ((a + θ' / κ⁻¹) * (q : ℝ) ^ 2) :=
            hLam.trans (mul_le_mul_of_nonneg_right hΓ (Real.exp_pos _).le)
          simpa [hqN, regionWeightInternal, hj] using hUpper
        · have hq0 : q ≠ 0 := by omega
          simp [hqN, regionWeightInternal, hj, hq0]
          positivity
      · simp [hqN]
        positivity
    have hmarked := markedConditionLambdaDomain_bound_split hL .free (squareFree L)
      (squareFree_connected L hL) (fun _ _ => rfl)
      (SpinWaves.squareFreeBipartiteDegreeFour L hL)
      (SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).1 hθ'0 hδ hθ'δ hD₁'1 hD₂.le
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
    have hexp : 8 * δ * η ^ 2 / (16384 * D₁' * κ⁻¹) =
        (1 / (16384 * D₁')) * (8 * δ) * η ^ 2 * κ := by
      field_simp
    have hpre : 1 / (64 * δ * κ⁻¹) = 1 / (64 * δ) * κ := by
      field_simp
    refine ⟨hZ, ?_⟩
    rw [hexp, hpre] at hmarked
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
    have H1' : κ⁻¹ * (Real.log (max 1 Γ) + 1 + a + 1) + c ≤ 8 * δ * η ^ 2 / 32 := by
      rw [hΓ1]; exact H1
    have hFourierBound : ∀ j q, 1 ≤ q →
        |(if q ≤ N then regionWeightInternal A lam j q else 0)| ≤
          Γ * Real.exp ((a + θ' / κ⁻¹) * (q : ℝ) ^ 2) := by
      intro j q hq
      by_cases hqN : q ≤ N
      · by_cases hj : j ∈ A
        · have h := hlam.2 (q : ℤ)
          have hΓ : C ≤ Γ := le_max_right _ _
          have hcoef : a + θ' / κ⁻¹ = a + θ' * κ := by field_simp
          have hLam : |lam (q : ℤ)| ≤ C * Real.exp ((a + θ' / κ⁻¹) * (q : ℝ) ^ 2) := by
            rw [hcoef]
            have hmon : (a + θ * κ) * ((q : ℤ) : ℝ) ^ 2 ≤ (a + θ' * κ) * (q : ℝ) ^ 2 := by
              push_cast
              exact mul_le_mul_of_nonneg_right
                (add_le_add_right (mul_le_mul_of_nonneg_right hθθ' hκpos.le) a) (sq_nonneg _)
            exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hmon) hC)
          have hUpper : |lam (q : ℤ)| ≤ Γ * Real.exp ((a + θ' / κ⁻¹) * (q : ℝ) ^ 2) :=
            hLam.trans (mul_le_mul_of_nonneg_right hΓ (Real.exp_pos _).le)
          simpa [hqN, regionWeightInternal, hj] using hUpper
        · have hq0 : q ≠ 0 := by omega
          simp [hqN, regionWeightInternal, hj, hq0]
          positivity
      · simp [hqN]
        positivity
    have hmarked := markedConditionLambdaDomain_bound_split hL .periodic (squarePeriodic L)
      (squarePeriodic_connected L hL) (fun _ _ => rfl)
      (SpinWaves.squarePeriodicBipartiteDegreeFour L hE hL)
      ((SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).2 hE) hθ'0 hδ hθ'δ hD₁'1 hD₂.le
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
    have hexp : 8 * δ * η ^ 2 / (16384 * D₁' * κ⁻¹) =
        (1 / (16384 * D₁')) * (8 * δ) * η ^ 2 * κ := by
      field_simp
    have hpre : 1 / (64 * δ * κ⁻¹) = 1 / (64 * δ) * κ := by
      field_simp
    refine ⟨hZ, ?_⟩
    rw [hexp, hpre] at hmarked
    simpa only [show 1 / (16384 * D₁') = 1 / (16384 * max D₁ 1) by rfl] using hmarked.2

end Squares

end FroehlichSpencer.BKT.Coulomb

end
