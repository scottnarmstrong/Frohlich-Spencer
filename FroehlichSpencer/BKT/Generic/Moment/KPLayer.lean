/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.Assembly
public import FroehlichSpencer.BKT.Generic.Renormalization.KPLayer
public import FroehlichSpencer.BKT.Charges.P21
public import FroehlichSpencer.BKT.SpinWaves.BoundaryShellPacking

/-!
# T1.5-NG on KP's square domains (the KP charge layer)

The charge
layer is `exists_kpChargeLayer` , and its clauses supply the generic hypotheses:

* nonzero densities and admissible centers from `IsChargeEnsemble` and the center choice;
* same-scale disjointness from `IsScaleSeparated` (`Reduction.densityDomain_inter_eq_empty`);
* `log₂(d(ϱ) + 1) ≤ A(ϱ)` from KP P2.1 (first half of `P21Step`) and
  `chargeDiameter_eq_densityDiameter`;
* the exponential entropy bound from a per-site bound on the mixture leaves
  `mixtureLeaf j q ≤ e^{a₁ q}` (`prod_mixtureLeaf_le`).

For the geometric mixture
  `ζ_j(q) ∝ e^{−a q}` of FS81 (6.8) this holds with `a₁ = a + log(2 Z_a max|λ̂|)`.

`integral_shift_ge_kp` is the statement on any square domain with KP's domain facts as hypotheses.

`integral_shift_ge_squareFree` and `integral_shift_ge_squarePeriodic` discharge them with the
theorems (`squareFreeBipartiteDegreeFour`, `l46Statement_holds`, `kp_p21Statement`) and
the edge-volume bound `|E(D)| ≤ 64 (d + 1)²` (`card_edgesTouching_densityDomain_*_le`).

There
`D₁ = kpD₁` is the constant of KP Proposition 2.1.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Finset

/-- The product of the mixture leaves over the support is at most `e^{a₁ ∑|ϱ|}` when every leaf
is at most `e^{a₁ q}`. -/
theorem prod_mixtureLeaf_le {L : ℕ} (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hζpos : ∀ j q, 0 < ζ j q) {a₁ : ℝ}
    (hleaf : ∀ j q, mixtureLeaf Nq lamHat ζ j q ≤ Real.exp (a₁ * q)) (ϱ : Fin L × Fin L → ℤ) :
    ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs ≤
      Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)|) := by
  have hnonneg : ∀ j q, 0 ≤ mixtureLeaf Nq lamHat ζ j q := fun j q => by
    unfold mixtureLeaf
    split_ifs with h
    · exact div_nonneg (by positivity) (hζpos j _).le
    · exact le_rfl
  have hsupp : ∑ j ∈ chargeSupport ϱ, |(ϱ j : ℝ)| = ∑ j, |(ϱ j : ℝ)| := by
    unfold chargeSupport
    refine Finset.sum_filter_of_ne fun j _ hj => ?_
    intro h0
    exact hj (by rw [h0, Int.cast_zero, abs_zero])
  calc ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs
      ≤ ∏ j ∈ chargeSupport ϱ, Real.exp (a₁ * |(ϱ j : ℝ)|) := by
        refine Finset.prod_le_prod₀ (fun j _ => hnonneg j _) fun j _ => ?_
        have h := hleaf j (ϱ j).natAbs
        rwa [Nat.cast_natAbs, Int.cast_abs] at h
    _ = Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)|) := by
        rw [← Real.exp_sum, ← Finset.mul_sum, hsupp]

/-- **T1.5-NG on a square domain with the KP charge layer.** -/
theorem integral_shift_ge_kp (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (hdom : boundary = .free ∨ Even L) {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ) {D₁ : ℝ}
    (hD₁ : 0 < D₁) (h21 : Reduction.P21Step boundary L D₁)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    {Kv : ℝ} (hKv : 0 ≤ Kv)
    (hvol : ∀ (ρ : Fin L × Fin L → ℤ) (j : Fin L × Fin L),
      ((edgesTouching Λ (Λ.densityDomain ρ j)).card : ℝ) ≤ Kv * ((Λ.densityDiameter ρ : ℝ) + 1) ^ 2)
    (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hNq : ∀ j, 0 < Nq j)
    (hcut : ∀ j q, Nq j < q → lamHat j q = 0)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hζpos : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) {a₁ : ℝ}
    (hleaf : ∀ j q, mixtureLeaf Nq lamHat ζ j q ≤ Real.exp (a₁ * q)) (v : Fin L × Fin L)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) {M : ℝ → ℝ} (hlog : HasLogDerivBounds w W M)
    {κc : ℝ} (hcurv : HasCurvatureBound w κc) {κ κ' : ℝ} (hc : IsCostEnvelope c κ κ' W)
    (hκ : 0 < κ) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * 28 ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hM : ∀ u : ℝ, |u| ≤ max (amp * 28) 1 → M u ≤ m)
    {b : ℝ} (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁)
    (hb₂ : b ≤ amp / (8 * D₁) - 200) {ε : ℝ}
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    (σ : Fin L × Fin L → ℝ) (θ : E → ℝ) :
    Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (Λ.grad σ e) ^ 2 + θ e ^ 2)) *
        ∫ φ, edgeDensity Λ w v φ * ∏ j, lam j (φ j) ≤
      ∫ φ, offsetEdgeDensity Λ w θ v φ * ∏ j, lam j (φ j + σ j) := by
  obtain ⟨CL, hCL⟩ := exists_kpChargeLayer boundary hL hdom Λ hΛ hdist B h46 hD₁.le h21
    centerOf hcenter lam Nq lamHat ζ hNq hcut hlam hζpos hζsum
  have hne : ∀ i, ∀ ϱ ∈ CL.R i, ϱ ≠ 0 := fun i ϱ hϱ => by
    rw [(hCL i).1] at hϱ
    exact (hCL i).2.2.1.1 ϱ (mem_neutralPart.mp hϱ).1
  refine integral_shift_ge_of_chargeLayer hΛ v CL (fun i => ⟨(hCL i).1, (hCL i).2.1⟩) hne
    (fun i ϱ hϱ => hcenter ϱ (hne i ϱ hϱ)) ?_ ?_ hKv hvol hw hnzero hlog hcurv hc hκ
    (by norm_num) (by norm_num) hD₁ hamp hampW hW1 hk₀ hexp hquad₁ hquad₂ hm0 hm1 hM (a₂ := 0)
    (fun ϱ => (prod_mixtureLeaf_le Nq lamHat ζ hζpos hleaf ϱ).trans_eq (by
      rw [zero_mul, add_zero])) hb8 hb₁ (by rw [sub_zero]; exact hb₂) hthr σ θ
  · intro i ϱ₁ h₁ ϱ₂ h₂ hne' k hk hd₁ hd₂ j₁ j₂ hj₁ hj₂
    rw [(hCL i).1] at h₁ h₂
    exact Reduction.densityDomain_inter_eq_empty boundary Λ hΛ hdist
      ((hCL i).2.2.2.1 ϱ₁ (mem_neutralPart.mp h₁).1 ϱ₂ (mem_neutralPart.mp h₂).1 hne') hk hd₁ hd₂
      hj₁ hj₂
  · intro i ϱ hϱ
    have h := (h21 (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) ϱ
      (hne i ϱ hϱ)).1
    rwa [chargeDiameter_eq_densityDiameter boundary Λ hdist] at h

/-! ## The square domains -/

/-- The constant `D₁` of KP Proposition 2.1 (`kp_p21Statement`). -/
def kpD₁ : ℝ := Classical.choose kp_p21Statement

theorem kpD₁_pos : 0 < kpD₁ := (Classical.choose_spec kp_p21Statement).1

theorem p21Step_kpD₁ {L : ℕ} (hL : 1 < L) :
    Reduction.P21Step .free L kpD₁ ∧ (Even L → Reduction.P21Step .periodic L kpD₁) :=
  (Classical.choose_spec kp_p21Statement).2 L hL

/-- **T1.5-NG on the free square** `squareFree L`, with the KP charge layer. -/
theorem integral_shift_ge_squareFree {L : ℕ} (hL : 1 < L)
    (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hNq : ∀ j, 0 < Nq j)
    (hcut : ∀ j q, Nq j < q → lamHat j q = 0)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hζpos : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) {a₁ : ℝ}
    (hleaf : ∀ j q, mixtureLeaf Nq lamHat ζ j q ≤ Real.exp (a₁ * q)) (v : Fin L × Fin L)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) {M : ℝ → ℝ} (hlog : HasLogDerivBounds w W M)
    {κc : ℝ} (hcurv : HasCurvatureBound w κc) {κ κ' : ℝ} (hc : IsCostEnvelope c κ κ' W)
    (hκ : 0 < κ) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * 28 ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hM : ∀ u : ℝ, |u| ≤ max (amp * 28) 1 → M u ≤ m)
    {b : ℝ} (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁)
    (hb₂ : b ≤ amp / (8 * kpD₁) - 200) {ε : ℝ}
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * (8 * (64 + 2 * 64 ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    (σ : Fin L × Fin L → ℝ) (θ : _ → ℝ) :
    Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) ((squareFree L).grad σ e) ^ 2 +
          θ e ^ 2)) *
        ∫ φ, edgeDensity (squareFree L) w v φ * ∏ j, lam j (φ j) ≤
      ∫ φ, offsetEdgeDensity (squareFree L) w θ v φ * ∏ j, lam j (φ j + σ j) := by
  classical
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → (squareFree L).IsDensityCenter ϱ j := by
    intro ϱ
    by_cases h : ϱ = 0
    · exact ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := (squareFree L).exists_isDensityCenter ϱ h
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  exact integral_shift_ge_kp .free hL (Or.inl rfl) (squareFree L) (squareFree_connected L hL)
    (fun _ _ => rfl) (SpinWaves.squareFreeBipartiteDegreeFour L hL)
    (SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).1 kpD₁_pos (p21Step_kpD₁ hL).1
    centerOf hcenter (by norm_num) (card_edgesTouching_densityDomain_squareFree_le hL) lam Nq
    lamHat ζ hNq hcut hlam hζpos hζsum hleaf v hw hnzero hlog hcurv hc hκ hamp hampW hW1 hk₀
    hexp hquad₁ hquad₂ hm0 hm1 hM hb8 hb₁ hb₂ hthr σ θ

/-- **T1.5-NG on the periodic square** `squarePeriodic L` (`L` even), with the KP charge layer. -/
theorem integral_shift_ge_squarePeriodic {L : ℕ} (hL : 1 < L) (hEven : Even L)
    (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hNq : ∀ j, 0 < Nq j)
    (hcut : ∀ j q, Nq j < q → lamHat j q = 0)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hζpos : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) {a₁ : ℝ}
    (hleaf : ∀ j q, mixtureLeaf Nq lamHat ζ j q ≤ Real.exp (a₁ * q)) (v : Fin L × Fin L)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) {M : ℝ → ℝ} (hlog : HasLogDerivBounds w W M)
    {κc : ℝ} (hcurv : HasCurvatureBound w κc) {κ κ' : ℝ} (hc : IsCostEnvelope c κ κ' W)
    (hκ : 0 < κ) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * 28 ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hM : ∀ u : ℝ, |u| ≤ max (amp * 28) 1 → M u ≤ m)
    {b : ℝ} (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁)
    (hb₂ : b ≤ amp / (8 * kpD₁) - 200) {ε : ℝ}
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * (8 * (64 + 2 * 64 ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    (σ : Fin L × Fin L → ℝ) (θ : _ → ℝ) :
    Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) ((squarePeriodic L).grad σ e) ^ 2 +
          θ e ^ 2)) *
        ∫ φ, edgeDensity (squarePeriodic L) w v φ * ∏ j, lam j (φ j) ≤
      ∫ φ, offsetEdgeDensity (squarePeriodic L) w θ v φ * ∏ j, lam j (φ j + σ j) := by
  classical
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → (squarePeriodic L).IsDensityCenter ϱ j := by
    intro ϱ
    by_cases h : ϱ = 0
    · exact ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := (squarePeriodic L).exists_isDensityCenter ϱ h
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  exact integral_shift_ge_kp .periodic hL (Or.inr hEven) (squarePeriodic L)
    (squarePeriodic_connected L hL) (fun _ _ => rfl)
    (SpinWaves.squarePeriodicBipartiteDegreeFour L hEven hL)
    ((SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).2 hEven) kpD₁_pos
    ((p21Step_kpD₁ hL).2 hEven) centerOf hcenter (by norm_num)
    (card_edgesTouching_densityDomain_squarePeriodic_le hL hEven) lam Nq lamHat ζ hNq hcut hlam
    hζpos hζsum hleaf v hw hnzero hlog hcurv hc hκ hamp hampW hW1 hk₀ hexp hquad₁ hquad₂ hm0 hm1
    hM hb8 hb₁ hb₂ hthr σ θ

end FroehlichSpencer.BKT.Generic

end
