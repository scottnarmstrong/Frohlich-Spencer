/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.CompactMarkedBranch
public import FroehlichSpencer.BKT.Clock.Compact.MarkedDomain
import Mathlib.Tactic

/-!
# The marked bound on one square domain under the compact Villain law

The Villain analogue of `clock_markedDomain_bound` (`Clock/Compact/MarkedDomain.lean`): FS81
Theorem 7.1(2) before the limit, for site weights given by a positive mixture such as the Fejér
weights of the clock comb, under the compact Villain law. The cluster estimates are the cosine ones.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open MeasureTheory
open FroehlichSpencer.BKT
open SpinWaves SpinWaves.P47 Reduction
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked


section DomainBound

variable {boundary : SquareBoundary} {L : ℕ}

/-- **The marked bound on one square domain under the compact Villain law** (FS81 Theorem 7.1(2) before
the limit, for site weights given by a positive mixture, e.g. the Fejér weights of the clock comb).
Let the domain carry KP's mixture T2.2, P2.1 and L4.6, the site mixture have leaves
`λ̃_j(q) ≤ e^{hq}`, the clock cost have a two-branch envelope with the unmarked amplitude `λ`
(the conditions of `clockWaveSelection_kp`) beating the leaves and the cover entropy
(`λ/8 ≥ h + s`, `λ/(8D₁) ≥ 200 + s`, `e^{-s} ≤ 1/32`), and the composite amplitude `λ_c` satisfy
`28 λ_c ≤ n`, `8192 β λ_c ≤ η n²` and (C1)–(C3). Then for the dipole at `o ≠ x` with clock mark
`ξ/n` (`0 < ξ < n`, `η ≤ min(ξ/n, 1 − ξ/n)`), `0 < 𝒵 = ∫ ∏_j λ_j(φ_j) dμ` and
`|∫ cos((ξ/n)(φ_o − φ_x)) ∏_j λ_j(φ_j) dμ| ≤ 2 e^{-(λ_c η/(32 D₁)) log₂(|o − x| + 1)} 𝒵`
under the compact Villain law `μ`. -/
theorem villain_markedDomain_bound (hL : 1 < L) (hdom : boundary = .free ∨ Even L) {E : Type}
    [Fintype E] (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    {D₁ : ℝ} (hD₁ : 1 ≤ D₁) (h21 : P21Step boundary L D₁)
    (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hNq : ∀ j, 0 < Nq j)
    (hcut : ∀ j q, Nq j < q → lamHat j q = 0)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hζpos : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) {h : ℝ}
    (hleaf : ∀ j q, mixtureLeaf Nq lamHat ζ j q ≤ Real.exp (h * q))
    {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 < β)
    {κ κ' W : ℝ} (hc : IsCostEnvelope (clockShiftCost β n) κ κ' W) (hκ : 0 < κ)
    {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * 28 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28)
    {s : ℝ} (hs : 0 < s) (H4 : Real.exp (-s) ≤ 1 / 32)
    (hamp1 : h + s ≤ amp / 8) (hamp2 : 200 + s ≤ amp / (8 * D₁))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ : ℕ} (hξ0 : 0 < ξ) (hξn : ξ < n) {η : ℝ}
    (hη : 0 < η) (hηξ : η ≤ dipoleGap ((ξ : ℝ) / n)) {lamc : ℝ} (hlamc0 : 0 ≤ lamc)
    (hlamcn : 28 * lamc ≤ n) (hcost : 8192 * β * lamc ≤ η * n ^ 2)
    (C1 : h + s + 1 ≤ lamc * η / 8)
    (C2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-s)) ≤ lamc * η / 16)
    (C3 : 289 * 200 + 289 * s ≤ lamc * η / (32 * D₁)) :
    0 < ∫ φ, ∏ j, lam j (φ j) ∂villainCompactLaw β n Λ ∧
      |∫ φ, Real.cos ((ξ : ℝ) / n * (φ o - φ x)) * ∏ j, lam j (φ j) ∂villainCompactLaw β n Λ| ≤
        2 * Real.exp (-(lamc * η / (32 * D₁)) *
            Real.logb 2 (latticeDistance boundary L o x + 1)) *
          ∫ φ, ∏ j, lam j (φ j) ∂villainCompactLaw β n Λ := by
  classical
  have hL0 : 0 < L := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hD₁pos : 0 < D₁ := by linarith
  set μ := villainCompactLaw β n Λ with hμ
  have := isProbabilityMeasure_villainCompactLaw Λ hβ hn'
  set ξ' : ℝ := (ξ : ℝ) / n with hξ'
  have hξ'0 : 0 < ξ' := div_pos (by exact_mod_cast hξ0) hn'
  have hξ'1 : ξ' < 1 := (div_lt_one hn').2 (by exact_mod_cast hξn)
  -- the mixture Theorem 2.2
  obtain ⟨m, N, cc, K, hens, hcpos, hcsum, hid, hprop⟩ :=
    t22MixStep_holds boundary hL hdom lam Nq lamHat ζ hNq hcut hlam hζpos hζsum
  -- the center choice and the wave selection
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → Λ.IsDensityCenter ϱ j := by
    intro ϱ
    by_cases hϱ : ϱ = 0
    · exact ⟨o, fun h' => absurd hϱ h'⟩
    · obtain ⟨j, hj⟩ := Λ.exists_isDensityCenter ϱ hϱ
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  have h24 := clockWaveSelection_kp boundary hL Λ hΛ hdist B h46 hD₁pos h21 centerOf hcenter
    hc hκ hamp hampW hk₀ hexp hquad₁ hquad₂
  -- the activity data in the form of the cluster estimate
  set lamHat' : Fin L × Fin L → ℕ → ℝ := fun j q =>
    mixtureLeaf Nq lamHat ζ j q * Real.exp (-((q : ℝ) ^ 2)) with hlamHat'
  have hleafform : ∀ ϱ : ChargeDensity L, ∏ j ∈ chargeSupport ϱ,
      Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat' j (ϱ j).natAbs| =
      ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs := by
    intro ϱ
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hlamHat']
    rw [abs_mul, abs_of_nonneg (mixtureLeaf_nonneg lamHat hζpos j _), Real.abs_exp,
      show (((ϱ j).natAbs : ℕ) : ℝ) ^ 2 = (ϱ j : ℝ) ^ 2 by
        rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]]
    rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  set ε := 2 * Real.exp (-(lamc * η / (32 * D₁)) *
    Real.logb 2 (latticeDistance boundary L o x + 1)) with hε
  have hθle : ∀ i, ∀ ϱ ∈ N i, linMemberWeight boundary s ϱ ≤ 1 / 32 := fun i ϱ hϱ =>
    (linMemberWeight_le hs ((hens i).1 ϱ hϱ)).trans H4
  have hbranch : ∀ i, 0 < ∫ φ, ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ ∧
      |∫ φ, Real.cos (ξ' * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ| ≤
        ε * ∫ φ, ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ := by
    intro i
    obtain ⟨hNa, hNb, hNc, hd⟩ := hprop i
    have hz : ∀ ϱ ∈ N i, ∑ j, ϱ j = 0 → ∀ a : Fin L × Fin L → ℝ,
        amp / 8 * ∑ j, |(ϱ j : ℝ)| + amp / (8 * D₁) * (chargeCoverCost boundary L ϱ : ℝ) ≤
          translationEnergy (clockShiftCost β n) (gradLinear Λ) a (fun j => (ϱ j : ℝ)) →
        |K i ϱ| * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear Λ) a
          (fun j => (ϱ j : ℝ))) ≤ linMemberWeight boundary s ϱ :=
      fun ϱ hϱ hϱn a ha => clock_renormalizedActivity_le h21 hL0 hζpos hleaf hs.le hamp1 hamp2
        ((hens i).1 ϱ hϱ) (hd ϱ hϱ hϱn) ha
    obtain ⟨hZ, hI⟩ := abs_villainMarkedBranch_le hL Λ hΛ hdist B h46 centerOf hcenter hβ hn h24
      (hens i) hNa hNb hNc (K i) (linMemberWeight boundary s)
      (fun ϱ hϱ => (hθle i ϱ hϱ).trans_lt (by norm_num)) hz hox hξ0 hξn hη hηξ hlamc0 hlamcn
      hcost
    refine ⟨hZ, hI.trans (mul_le_mul_of_nonneg_right ?_ hZ.le)⟩
    have hmono := markAdjacent_monotone (boundary := boundary) (dipoleMark_ne_zero hox)
    refine sum_le_of_le_explorationWeight hmono (N i) (linExplorationWeight boundary s)
      (fun ϱ hϱ => ?_) _ fun C hC => ?_
    · unfold linExplorationWeight
      split_ifs
      · exact (hθle i ϱ hϱ).trans_lt (by norm_num)
      · norm_num
    · split_ifs with hCn
      · exact linCluster_estimate hL hD₁ (by norm_num) h21 (hens i) hNa hNb (K i)
          (lamHat := lamHat') (h := h)
          (fun ϱ hϱ hϱn => by rw [hleafform]; exact hd ϱ hϱ hϱn)
          (fun ϱ _ => by
            rw [hleafform]
            calc ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs
                ≤ ∏ j ∈ chargeSupport ϱ, Real.exp (h * ((ϱ j).natAbs : ℝ)) :=
                  Finset.prod_le_prod₀ (fun j _ => mixtureLeaf_nonneg lamHat hζpos j _)
                    fun j _ => hleaf j _
              _ = Real.exp (h * ∑ j ∈ chargeSupport ϱ, |(ϱ j : ℝ)|) := by
                  rw [← Real.exp_sum, Finset.mul_sum]
                  congr 1
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Nat.cast_natAbs, Int.cast_abs]
              _ = Real.exp (h * ∑ j, |(ϱ j : ℝ)|) := by
                  congr 2
                  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
                  have : ϱ j = 0 := by
                    by_contra h'
                    exact hj (mem_chargeSupport'.2 h')
                  simp [this])
          hox hξ'0 hξ'1 hη hηξ hs hlamc0 C1 C2 C3 H4 hC hCn
      · have hπ0 : ∀ ϱ ∈ N i, 0 ≤ linExplorationWeight boundary s ϱ := fun ϱ _ => by
          unfold linExplorationWeight
          split_ifs
          · exact (linMemberWeight_pos s ϱ).le
          · norm_num
        have hπ1 : ∀ ϱ ∈ N i, linExplorationWeight boundary s ϱ ≤ 1 := fun ϱ hϱ => by
          unfold linExplorationWeight
          split_ifs
          · exact (hθle i ϱ hϱ).trans (by norm_num)
          · norm_num
        have hCN : C ⊆ N i := (mem_clusters.1 hC).1
        refine mul_nonneg (by positivity) (mul_nonneg
          (Finset.prod_nonneg fun ϱ hϱ => hπ0 ϱ (hCN hϱ))
          (Finset.prod_nonneg fun ϱ hϱ => ?_))
        have := hπ1 ϱ (Finset.mem_sdiff.1 hϱ).1
        linarith
  -- assemble the branches
  have hlamid : ∀ φ : Fin L × Fin L → ℝ, ∏ j, lam j (φ j) =
      ∑ i, cc i * ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) := fun φ => hid φ
  have hint : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ)))) μ := fun i =>
    Reduction.integrable_prod_one_add_mul_cos μ (N i) (K i) (fun ϱ φ => ∑ j, φ j * (ϱ j : ℝ))
      (fun ϱ => by fun_prop)
  have hintc : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      Real.cos (ξ' * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ)))) μ := fun i =>
    (hint i).bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hZ : ∫ φ, ∏ j, lam j (φ j) ∂μ =
      ∑ i, cc i * ∫ φ, ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ := by
    simp_rw [hlamid]
    rw [integral_finsetSum _ fun i _ => (hint i).const_mul (cc i)]
    simp_rw [integral_const_mul]
  have hI : ∫ φ, Real.cos (ξ' * (φ o - φ x)) * ∏ j, lam j (φ j) ∂μ =
      ∑ i, cc i * ∫ φ, Real.cos (ξ' * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ := by
    have hpt : ∀ φ : Fin L × Fin L → ℝ,
        Real.cos (ξ' * (φ o - φ x)) * ∏ j, lam j (φ j) =
        ∑ i, cc i * (Real.cos (ξ' * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ)))) := by
      intro φ
      rw [hlamid, Finset.mul_sum, sum_mul_dipoleMark]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum _ fun i _ => (hintc i).const_mul (cc i)]
    simp_rw [integral_const_mul]
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty] at h'
    rw [h', Finset.sum_empty] at hcsum
    exact zero_ne_one hcsum
  refine ⟨?_, ?_⟩
  · rw [hZ]
    exact Finset.sum_pos (fun i _ => mul_pos (hcpos i) (hbranch i).1) hne
  · rw [hI, hZ, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hcpos i), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hbranch i).2 (hcpos i).le

end DomainBound

end FroehlichSpencer.BKT.Clock.VillainClock

end
