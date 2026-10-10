/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Renormalization.Assembly
public import FroehlichSpencer.BKT.Generic.Renormalization.Mixture
public import FroehlichSpencer.BKT.Generic.Renormalization.Waves
public import FroehlichSpencer.BKT.Reduction.T16Assembly

/-!
# The KP charge layer and the T1.6-NG theorem on KP's square domains (generic core)

* `exists_kpChargeLayer`: from the general-mixture KP Theorem 2.2 (`t22MixStep_holds`, built on the
   basic lemma), KP Proposition 2.1 (`Reduction.P21Step`), KP Lemma 4.6 (`L46Step`) and the
  all-scales graded spin waves (`exists_fullGradedSpinWave`), a charge layer with
  `A(ϱ) = A_KP(ϱ)` (the cover cost), entropy `Z(ϱ) = ∏_{j ∈ supp ϱ} 2|λ̂_j(|ϱ(j)|)|/ζ_j(|ϱ(j)|)`,
  `D₂ = 200`, `α = 7/4`, `K₀ = 4096`, `K₁ = 28`, whose translated densities are the neutral parts
  of KP ensembles with at most one non-neutral density (rooted-compatible).
* `edgeLaw_renormalization_kp`: the T1.6-NG theorem for the rooted edge law on these domains, by
  `edgeLaw_renormalization_of_chargeLayer`.

The piece orthogonality `⟨ψ_t, ϱ'⟩ = 0` is the first half of KP's `spinWave_orthogonality`: a
piece is constant on `D⁺(ϱ')` for comparable `ϱ'` (which is neutral), and vanishes on the support
of a larger `ϱ'` by KP T2.2(b) (`Reduction.notMem_densityDomain_of_scaleSeparated`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic.SpinWave

/-- The number of support sites is at most the linear mass. -/
lemma card_chargeSupport_le_sum_abs {L : ℕ} (ϱ : Fin L × Fin L → ℤ) :
    ((chargeSupport ϱ).card : ℝ) ≤ ∑ j, |(ϱ j : ℝ)| := by
  classical
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  calc ∑ _j ∈ chargeSupport ϱ, (1 : ℝ) ≤ ∑ j ∈ chargeSupport ϱ, |(ϱ j : ℝ)| := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj0 : ϱ j ≠ 0 := by
          unfold chargeSupport at hj
          exact (Finset.mem_filter.mp hj).2
        have : (1 : ℝ) ≤ |(ϱ j : ℤ)| := by exact_mod_cast Int.one_le_abs hj0
        simpa using this
    _ ≤ ∑ j, |(ϱ j : ℝ)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _

/-- **The KP charge layer** on a square domain, with a general positive site mixture. -/
theorem exists_kpChargeLayer (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (hdom : boundary = .free ∨ Even L) {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ) {D₁ : ℝ}
    (hD₁ : 0 ≤ D₁) (h21 : Reduction.P21Step boundary L D₁)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hNq : ∀ j, 0 < Nq j)
    (hcut : ∀ j q, Nq j < q → lamHat j q = 0)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hζpos : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) :
    ∃ CL : ChargeLayer Λ lam centerOf (fun ϱ => (chargeCoverCost boundary L ϱ : ℝ))
        (fun ϱ => ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs)
        D₁ 200 (7 / 4) 4096 28,
      ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i) ∧
        IsChargeEnsemble (CL.N i) ∧ IsScaleSeparated boundary L (CL.N i) := by
  classical
  obtain ⟨n, N, c, K, hens, hc, hcsum, hexp, hprops⟩ :=
    t22MixStep_holds boundary hL hdom lam Nq lamHat ζ hNq hcut hlam hζpos hζsum
  -- the graded waves and the clauses the layer records
  have hwave : ∀ i, ∀ ϱ ∈ neutralPart (N i), ∃ Wv : GradedSpinWave.{0, 0, 0} Λ
      (neutralPart (N i)) centerOf ϱ,
      HasLayerWave Λ (neutralPart (N i)) centerOf (fun ϱ => (chargeCoverCost boundary L ϱ : ℝ))
        D₁ (7 / 4) 4096 28 ϱ Wv := by
    intro i ϱ hϱ
    obtain ⟨hNa, hNb, hNc, -⟩ := hprops i
    obtain ⟨Wv, hα, hK₀, hK₁, hbase, hcount, hedge⟩ := exists_fullGradedSpinWave boundary hL Λ hΛ
      hdist B h46 centerOf hcenter (N i) (hens i) hNa hNb hNc ϱ hϱ
    obtain ⟨hϱN, hneutral⟩ := mem_neutralPart.mp hϱ
    have hϱ0 : ϱ ≠ 0 := (hens i).1 ϱ hϱN
    refine ⟨Wv, hα, hK₀, hK₁, hbase, hedge, ?_, ?_⟩
    · -- the cover bound (KP P2.1)
      have hA := (h21 (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) ϱ hϱ0).2
      have hS0 : (squareCoverNumber boundary L 0 ϱ : ℝ) ≤ ∑ j, |(ϱ j : ℝ)| :=
        (Nat.cast_le.mpr (Reduction.squareCoverNumber_zero_le_card boundary L ϱ)).trans
          (card_chargeSupport_le_sum_abs ϱ)
      rw [hcount] at *
      calc (chargeCoverCost boundary L ϱ : ℝ)
          ≤ D₁ * (squareCoverNumber boundary L 0 ϱ + separatedSquareTotal boundary L
              (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) ϱ) := hA
        _ ≤ D₁ * (∑ j, |(ϱ j : ℝ)| + separatedSquareTotal boundary L
              (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) ϱ) := by
            gcongr
    · -- piece orthogonality (first half of KP's `spinWave_orthogonality`)
      intro t ϱ' hϱ' hne
      obtain ⟨hϱ'N, hneutral'⟩ := mem_neutralPart.mp hϱ'
      have hϱ'0 : ϱ' ≠ 0 := (hens i).1 ϱ' hϱ'N
      by_cases hle : Λ.densityDiameter ϱ' ≤ 2 * Λ.densityDiameter ϱ
      · obtain ⟨c₀, hc₀⟩ := Wv.const_plus t ϱ' (Λ.mem_comparableDensities.mpr ⟨hϱ', hle, Ne.symm hne⟩)
        have hterm : ∀ j, Wv.piece t j * (ϱ' j : ℝ) = c₀ * (ϱ' j : ℝ) := by
          intro j
          by_cases hj : ϱ' j = 0
          · simp [hj]
          · rw [hc₀ j (Λ.mem_densityDomainPlus_of_center hΛ hneutral' (hcenter ϱ' hϱ'0) hj)]
        rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum]
        have : ∑ j, (ϱ' j : ℝ) = 0 := by exact_mod_cast hneutral'
        rw [this, mul_zero]
      · refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : ϱ' j = 0
        · simp [hj]
        · have hsep := hNb.1 ϱ hϱN ϱ' hϱ'N (Ne.symm hne)
          have hnot := Reduction.notMem_densityDomain_of_scaleSeparated boundary Λ hΛ hdist hϱ0
            hneutral hsep (not_le.mp hle) (hcenter ϱ hϱ0) hj
          have hp : Wv.piece t j = 0 := by
            by_contra hp
            exact hnot (Wv.supp t hp)
          rw [hp, zero_mul]
  let CL : ChargeLayer Λ lam centerOf (fun ϱ => (chargeCoverCost boundary L ϱ : ℝ))
      (fun ϱ => ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs)
      D₁ 200 (7 / 4) 4096 28 :=
    { n := n
      N := N
      R := fun i => neutralPart (N i)
      c := c
      K := K
      c_pos := hc
      c_sum := hcsum
      R_sub := fun i => Finset.filter_subset _ _
      expand := hexp
      entropy := fun i ϱ hϱ => (hprops i).2.2.2 ϱ (mem_neutralPart.mp hϱ).1
        (mem_neutralPart.mp hϱ).2
      wave := hwave }
  exact ⟨CL, fun i => ⟨rfl, (hprops i).1, hens i, (hprops i).2.1⟩⟩


theorem edgeLaw_renormalization_kp (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (hdom : boundary = .free ∨ Even L) {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ) {D₁ : ℝ}
    (hD₁ : 0 < D₁) (h21 : Reduction.P21Step boundary L D₁)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hNq : ∀ j, 0 < Nq j)
    (hcut : ∀ j q, Nq j < q → lamHat j q = 0)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hζpos : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) (v : Fin L × Fin L)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) {κ κ' : ℝ}
    (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) {amp : ℝ} (hamp : 0 ≤ amp)
    (hampW : amp * 28 ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28) :
    ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ)) (cc : Fin n → ℝ)
      (z : Fin n → (Fin L × Fin L → ℤ) → ℝ)
      (a : Fin n → (Fin L × Fin L → ℤ) → Fin L × Fin L → ℝ),
      (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < cc i) ∧ ∑ i, cc i = 1 ∧
      (∀ i, ∀ ϱ ∈ N i, ∑ j, ϱ j = 0) ∧
      (∀ σ : Fin L × Fin L → ℝ, ∫ φ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) ∂edgeLaw Λ w v =
        ∑ i, (cc i : ℂ) * ∫ φ, ∏ ϱ ∈ N i, ((1 : ℂ) + (z i ϱ : ℂ) *
          localFactor w c (gradLinear Λ (a i ϱ)) (gradLinear Λ φ + 0)
            (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂edgeLaw Λ w v) ∧
      ∀ i, (∀ ϱ ∈ N i,
          |z i ϱ| ≤ Real.exp (200 * (chargeCoverCost boundary L ϱ : ℝ)) *
              (∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs) *
            Real.exp (-(amp / 8 * ∑ j, |(ϱ j : ℝ)|) -
              amp / (8 * D₁) * (chargeCoverCost boundary L ϱ : ℝ)) ∧
          (∀ e, |Λ.grad (a i ϱ) e| ≤ W) ∧
          Function.support (a i ϱ) ⊆ Λ.densityDomain ϱ (centerOf ϱ) ∧
          ∀ (φ : Fin L × Fin L → ℝ) (θ : ℝ),
            ‖localFactor w c (gradLinear Λ (a i ϱ)) (gradLinear Λ φ + 0) θ‖ ≤ 1) ∧
        ∀ ϱ₁ ∈ N i, ∀ ϱ₂ ∈ N i, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
          Λ.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
          Λ.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
          ∀ j₁ j₂ : Fin L × Fin L, Λ.IsDensityCenter ϱ₁ j₁ → Λ.IsDensityCenter ϱ₂ j₂ →
            Λ.densityDomain ϱ₁ j₁ ∩ Λ.densityDomain ϱ₂ j₂ = ∅ := by
  obtain ⟨CL, hCL⟩ := exists_kpChargeLayer boundary hL hdom Λ hΛ hdist B h46 hD₁.le h21
    centerOf hcenter lam Nq lamHat ζ hNq hcut hlam hζpos hζsum
  obtain ⟨z, a, hid, hz⟩ := edgeLaw_renormalization_of_chargeLayer hΛ v CL
    (fun i => ⟨(hCL i).1, (hCL i).2.1⟩) hw hc hκ (by norm_num) (by norm_num) hD₁ hamp hampW hW1
    hk₀ hexp hquad₁ hquad₂
  refine ⟨CL.n, CL.R, CL.c, z, a, fun i => ?_, CL.c_pos, CL.c_sum, fun i ϱ hϱ => ?_, hid,
    fun i => ⟨hz i, ?_⟩⟩
  · rw [(hCL i).1]; exact (hCL i).2.2.1.neutralPart
  · rw [(hCL i).1] at hϱ; exact (mem_neutralPart.mp hϱ).2
  · intro ϱ₁ h₁ ϱ₂ h₂ hne k hk hd₁ hd₂ j₁ j₂ hj₁ hj₂
    rw [(hCL i).1] at h₁ h₂
    exact Reduction.densityDomain_inter_eq_empty boundary Λ hΛ hdist
      ((hCL i).2.2.2.1 ϱ₁ (mem_neutralPart.mp h₁).1 ϱ₂ (mem_neutralPart.mp h₂).1 hne) hk hd₁ hd₂
      hj₁ hj₂

end FroehlichSpencer.BKT.Generic

end
