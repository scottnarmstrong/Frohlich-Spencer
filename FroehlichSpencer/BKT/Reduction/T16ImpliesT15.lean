/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.ChargeEnsemble
public import FroehlichSpencer.BKT.Surface.DensityCenter
public import FroehlichSpencer.BKT.Surface.DensityDomain
public import FroehlichSpencer.BKT.Surface.GFFLaw
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverse
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
public import FroehlichSpencer.BKT.Surface.SubGaussian
public import FroehlichSpencer.BKT.ExpMoment.Claim32
public import FroehlichSpencer.BKT.Reduction.T15ImpliesT11
public import FroehlichSpencer.BKT.Surface.IntegerGFFLaw
import FroehlichSpencer.BKT.ExpMoment.BranchBound
import FroehlichSpencer.BKT.ExpMoment.Claim32Threshold
import FroehlichSpencer.BKT.Gaussian.GFFSymmetry
import FroehlichSpencer.BKT.Gaussian.WeightedGFF
import FroehlichSpencer.BKT.Gaussian.WeightedShift
import FroehlichSpencer.BKT.Surface.GFFWellDefined

/-!
# KP Theorem 1.6 implies KP Theorem 1.5 (KP §3)

`t16Statement` is the
statement of the `weightedGFF_renormalization`, copied verbatim; `t15_of_t16Statement`
proves the statement of the `weightedGFF_expMoment_lower_bound`, also verbatim.

For fixed `(Γ, η, θ)` and `ε`, take `β₀ = min(β₀^{1.6}, c₁ / ln 8, β₂)`, where
`β₂` is the Claim 3.2 threshold for `D = 4(1 + ε)/ε`.

Then:

1. **Shift.** Completing the square with the pinned translate `σ` of KP (1.5) gives
   `∫ e^⟨φ,f⟩ ∏ λ_j(φ_j) dμ^GFF = e^{Q(f)/(2β)} Z(σ)` (`integral_exp_pairing_mul_gffLaw`).

So
   `Z_i(0) ≥ (7/8)^{|𝒩_i|} > 0` and `Z(0) > 0`.
4. **Branches.** Claim 3.1 in product form, for the even law `μ^GFF`, gives
   `Z_i(σ) ≥ e^{-2 ∑ |z| ⟨σ,ϱ⟩²} Z_i(0)` (`integral_prod_cos_shift_ge`, `gffLaw_map_neg`).

Claim 3.2 gives `∑ |z| ⟨σ,ϱ⟩² ≤ (β/D) E(σ) = Q(f)/(D β)`.
5. **Averaging.** With `2/D = ε/(2(1+ε))`, positive averaging gives
   `Z(σ)/Z(0) ≥ e^{-ε Q(f) / (2(1+ε)β)}`, hence (1.10).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Reduction

open MeasureTheory

/--
The exact proposition stated as KP Theorem 1.6 (KP pp. 6–7), copied verbatim from the
renormalization statement `weightedGFF_renormalization`.
-/
def t16Statement : Prop :=
    ∀ Γ : ℝ, 0 < Γ → ∀ η θ : ℝ, 0 ≤ θ → θ < 1 / 16 →
      ∃ β₀ c₁ : ℝ, 0 < β₀ ∧ 0 < c₁ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let step : ∀ {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
          ∃ (n : ℕ) (N : Fin n → Finset (Fin L × Fin L → ℤ)) (c : Fin n → ℝ)
            (z : Fin n → (Fin L × Fin L → ℤ) → ℝ)
            (ϱbar : Fin n → (Fin L × Fin L → ℤ) → Fin L × Fin L → ℝ),
            (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
            (∀ σ : Fin L × Fin L → ℝ,
              ∫ φ, ∏ j, lam j (φ j + σ j) ∂(gffLaw Λ hΛ β hβ v) =
                ∑ i, c i * ∫ φ, ∏ ϱ ∈ N i,
                  (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j + ∑ j, σ j * ϱ j))
                    ∂(gffLaw Λ hΛ β hβ v)) ∧
            ∀ i,
              (∀ ϱ ∈ N i, ∑ j, ϱ j = 0) ∧
              (∀ ϱ ∈ N i, |z i ϱ| ≤ Real.exp (-(c₁ / β) *
                (∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 (Λ.densityDiameter ϱ + 1)))) ∧
              ∀ ϱ₁ ∈ N i, ∀ ϱ₂ ∈ N i, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
                Λ.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
                Λ.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
                ∀ j₁ j₂ : Fin L × Fin L, Λ.IsDensityCenter ϱ₁ j₁ → Λ.IsDensityCenter ϱ₂ j₂ →
                  Λ.densityDomain ϱ₁ j₁ ∩ Λ.densityDomain ϱ₂ j₂ = ∅
      step (squareFree L) (squareFree_connected L hL) ∧
        (Even L → step (squarePeriodic L) (squarePeriodic_connected L hL))

section Generic

variable {V : Type} [Fintype V] [DecidableEq V] {E : Type} [Fintype E]

omit [DecidableEq V] [Fintype E] in
/--  Step 1: below `c₁ / ln 8`, every T1.6 coefficient has `|z| < 1/8`. -/
theorem abs_lt_eighth_of_damping (Λ : Multigraph V E) (c₁ β : ℝ) (hβ : 0 < β)
    (hβ8 : β < c₁ / Real.log 8) (ϱ : V → ℤ) (hϱ : ϱ ≠ 0) (hneutral : ∑ j, ϱ j = 0) (z : ℝ)
    (hz : |z| ≤ Real.exp (-(c₁ / β) *
      (∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 (Λ.densityDiameter ϱ + 1)))) :
    |z| < 1 / 8 := by
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have ht : Real.log 8 < c₁ / β := by
    rw [lt_div_iff₀ hβ]
    rw [lt_div_iff₀ hlog8] at hβ8
    linarith only [hβ8]
  have hu := two_le_sum_sq_of_neutral ϱ hϱ hneutral
  have hlogb : 0 ≤ Real.logb 2 ((Λ.densityDiameter ϱ : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) (Λ.densityDiameter ϱ); linarith only)
  have hexp : -(c₁ / β) * (∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 (Λ.densityDiameter ϱ + 1)) <
      -Real.log 8 := by
    have h1 : Real.log 8 * 1 < (c₁ / β) * (∑ j, (ϱ j : ℝ) ^ 2 +
        Real.logb 2 (Λ.densityDiameter ϱ + 1)) := by
      have h2 : (1 : ℝ) ≤ ∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 (Λ.densityDiameter ϱ + 1) := by
        linarith only [hu, hlogb]
      calc Real.log 8 * 1 < (c₁ / β) * 1 := by linarith only [ht]
        _ ≤ (c₁ / β) * (∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 (Λ.densityDiameter ϱ + 1)) :=
            mul_le_mul_of_nonneg_left h2 (by linarith only [hlog8, ht])
    linarith only [h1]
  calc |z| ≤ _ := hz
    _ < Real.exp (-Real.log 8) := Real.exp_lt_exp.mpr hexp
    _ = 1 / 8 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-- KP §3 at one domain, root, temperature and weight family: the T1.6 data give both
conjuncts of KP Theorem 1.5. -/
theorem weightedBound_of_t16Data (Λ : Multigraph V E) (hΛ : Λ.toSimpleGraph.Connected)
    (hvol : ∀ (ρ : V → ℤ) (j : V),
      ((Λ.edgesWithin (Λ.densityDomain ρ j)).card : ℝ) ≤
        144 * ((Λ.densityDiameter ρ : ℝ) + 1) ^ 2)
    (ε : ℝ) (hε : 0 < ε) (c₁ β : ℝ) (hβ : 0 < β) (hβ8 : β < c₁ / Real.log 8)
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      144 * (4 * (1 + ε) / ε) * (d + 1) ^ 3 * u ^ 2 *
        Real.exp (-(c₁ / β) * (u + Real.logb 2 (d + 1))) ≤ β)
    (v : V) (lam : V → ℝ → ℝ) (Γ η θ : ℝ) (hlam : ∀ j, IsSubGaussian Γ η θ β (lam j))
    (hdata : ∃ (n : ℕ) (N : Fin n → Finset (V → ℤ)) (c : Fin n → ℝ)
        (z : Fin n → (V → ℤ) → ℝ) (ϱbar : Fin n → (V → ℤ) → V → ℝ),
        (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < c i) ∧ ∑ i, c i = 1 ∧
        (∀ σ : V → ℝ,
          ∫ φ, ∏ j, lam j (φ j + σ j) ∂(gffLaw Λ hΛ β hβ v) =
            ∑ i, c i * ∫ φ, ∏ ϱ ∈ N i,
              (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j + ∑ j, σ j * ϱ j))
                ∂(gffLaw Λ hΛ β hβ v)) ∧
        ∀ i,
          (∀ ϱ ∈ N i, ∑ j, ϱ j = 0) ∧
          (∀ ϱ ∈ N i, |z i ϱ| ≤ Real.exp (-(c₁ / β) *
            (∑ j, (ϱ j : ℝ) ^ 2 + Real.logb 2 (Λ.densityDiameter ϱ + 1)))) ∧
          ∀ ϱ₁ ∈ N i, ∀ ϱ₂ ∈ N i, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
            Λ.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
            Λ.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
            ∀ j₁ j₂ : V, Λ.IsDensityCenter ϱ₁ j₁ → Λ.IsDensityCenter ϱ₂ j₂ →
              Λ.densityDomain ϱ₁ j₁ ∩ Λ.densityDomain ϱ₂ j₂ = ∅) :
    0 < ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v) ∧
    ∀ T : (V → ℝ) →ₗ[ℝ] V → ℝ, Λ.IsLaplacianPseudoinverse T →
      ∀ f : V → ℝ, ∑ j, f j = 0 →
        Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β)) ≤
          (∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)) /
            ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v) := by
  obtain ⟨n, N, c, z, ϱbar, hens, hcpos, hcsum, hid, hprops⟩ := hdata
  set μ := gffLaw Λ hΛ β hβ v with hμ
  have := isProbabilityMeasure_gffLaw Λ hΛ β hβ v
  -- Branch integrals.
  set Zb : Fin n → (V → ℝ) → ℝ := fun i σ =>
    ∫ φ, ∏ ϱ ∈ N i, (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j + ∑ j, σ j * ϱ j)) ∂μ
    with hZb
  have hz8 : ∀ i, ∀ ϱ ∈ N i, |z i ϱ| < 1 / 8 := fun i ϱ hϱ =>
    abs_lt_eighth_of_damping Λ c₁ β hβ hβ8 ϱ ((hens i).1 ϱ hϱ) ((hprops i).1 ϱ hϱ) (z i ϱ)
      ((hprops i).2.1 ϱ hϱ)
  have hZb0 : ∀ i, Zb i 0 = ∫ φ, ∏ ϱ ∈ N i,
      (1 + z i ϱ * Real.cos (∑ j, φ j * ϱbar i ϱ j)) ∂μ := by
    intro i
    simp only [hZb, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  have hZb0pos : ∀ i, 0 < Zb i 0 := by
    intro i
    have h := integral_prod_one_add_cos_ge μ (N i) (ϱbar i) (fun _ => 0) (z i) (hz8 i)
    simp only [add_zero] at h
    rw [hZb0 i]
    exact lt_of_lt_of_le (pow_pos (by norm_num) _) h
  -- The normalizer `Z(0)`.
  have hZ0eq : ∫ φ, ∏ j, lam j (φ j) ∂μ = ∑ i, c i * Zb i 0 := by
    have h := hid 0
    simp only [Pi.zero_apply, add_zero] at h
    exact h
  have hnpos : 0 < n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    simp at hcsum
  have hZ0pos : 0 < ∫ φ, ∏ j, lam j (φ j) ∂μ := by
    rw [hZ0eq]
    have : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hnpos⟩, Finset.mem_univ _⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hcpos i) (hZb0pos i)) this
  refine ⟨hZ0pos, ?_⟩
  intro T hT f hf
  -- `T` is the mean-zero inverse.
  have hTg : T = Λ.greenOp hΛ := Multigraph.greenOp_unique Λ hΛ T hT.1 hT.2
  subst hTg
  set Q := Multigraph.pairing f (-Λ.greenOp hΛ f) with hQ
  have hQdef : ∑ j, f j * -(Λ.greenOp hΛ f j) = Q := rfl
  rw [hQdef]
  set σ := gffShift Λ hΛ β f v with hσ
  -- Completing the square.
  obtain ⟨C, hC⟩ := exists_abs_prod_le_of_isSubGaussian hlam
  have hnum := integral_exp_pairing_mul_gffLaw Λ hΛ β hβ v f hf (fun φ => ∏ j, lam j (φ j))
    (continuous_prod_of_isSubGaussian hlam).measurable C hC
  have hshift : ∫ φ, ∏ j, lam j ((φ + σ) j) ∂μ = ∑ i, c i * Zb i σ := by
    have h := hid σ
    simp only [Pi.add_apply]
    exact h
  -- Each branch.
  have hE : ∑ e, Λ.grad σ e ^ 2 = Q / β ^ 2 := energy_gffShift Λ hΛ β f hf v
  set D := 4 * (1 + ε) / ε with hD
  have hDpos : 0 < D := by positivity
  set e₀ := Real.exp (-(ε * Q / (2 * (1 + ε) * β))) with he₀
  have hbranch : ∀ i, e₀ * Zb i 0 ≤ Zb i σ := by
    intro i
    have hcl := claim32 Λ hΛ 144 (by norm_num) hvol (N i) (hens i).1 (hprops i).1
      (hprops i).2.2 (z i) c₁ β D hβ hDpos (hprops i).2.1 hthr σ
    rw [hE] at hcl
    have hb := integral_prod_cos_shift_ge μ (gffLaw_map_neg Λ hΛ β hβ v) (N i) (ϱbar i)
      (fun ϱ => ∑ j, σ j * (ϱ j : ℝ)) (z i) (hz8 i)
    rw [← hZb0 i] at hb
    have hexp : e₀ ≤ Real.exp (-∑ ϱ ∈ N i, 2 * |z i ϱ| * (∑ j, σ j * (ϱ j : ℝ)) ^ 2) := by
      rw [he₀]
      apply Real.exp_le_exp.mpr
      have hsum : ∑ ϱ ∈ N i, 2 * |z i ϱ| * (∑ j, σ j * (ϱ j : ℝ)) ^ 2 =
          2 * ∑ ϱ ∈ N i, |z i ϱ| * (∑ j, σ j * (ϱ j : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ϱ _ => by ring
      rw [hsum]
      have hkey : 2 * (β / D * (Q / β ^ 2)) = ε * Q / (2 * (1 + ε) * β) := by
        rw [hD]
        field_simp
        ring
      linarith only [hcl, hkey]
    calc e₀ * Zb i 0 ≤
          Real.exp (-∑ ϱ ∈ N i, 2 * |z i ϱ| * (∑ j, σ j * (ϱ j : ℝ)) ^ 2) * Zb i 0 :=
            mul_le_mul_of_nonneg_right hexp (hZb0pos i).le
      _ ≤ Zb i σ := hb
  -- Averaging.
  have hZσ : e₀ * ∫ φ, ∏ j, lam j (φ j) ∂μ ≤ ∫ φ, ∏ j, lam j ((φ + σ) j) ∂μ := by
    rw [hZ0eq, hshift, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have := hbranch i
      have hc := (hcpos i).le
      nlinarith only [this, hc]
  rw [le_div_iff₀ hZ0pos]
  have hnum' : ∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂μ =
      Real.exp (Q / (2 * β)) * ∫ φ, ∏ j, lam j ((φ + σ) j) ∂μ := hnum
  rw [hnum']
  have hexpeq : Real.exp (Q / (2 * (1 + ε) * β)) = Real.exp (Q / (2 * β)) * e₀ := by
    rw [he₀, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hexpeq, mul_assoc]
  exact mul_le_mul_of_nonneg_left hZσ (Real.exp_pos _).le

end Generic

/--
**KP Theorem 1.6 implies KP Theorem 1.5** (KP §3).

The conclusion is the statement of the
statement `weightedGFF_expMoment_lower_bound`, copied verbatim.
-/
theorem t15_of_t16Statement (h : t16Statement) :
    ∀ Γ : ℝ, 0 < Γ → ∀ η θ : ℝ, 0 ≤ θ → θ < 1 / 16 → ∀ ε : ℝ, 0 < ε →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (L : ℕ) (hL : 1 < L),
      let bounds : ∀ {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E),
          Λ.toSimpleGraph.Connected → Prop :=
        fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
          ∀ lam : Fin L × Fin L → ℝ → ℝ, (∀ j, IsSubGaussian Γ η θ β (lam j)) →
            0 < ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v) ∧
            ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ, Λ.IsLaplacianPseudoinverse T →
              ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
                Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β)) ≤
                  (∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)) /
                    ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)
      bounds (squareFree L) (squareFree_connected L hL) ∧
        (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL)) := by
  intro Γ hΓ η θ hθ0 hθ ε hε
  obtain ⟨β₀', c₁, hβ₀', hc₁, h16⟩ := h Γ hΓ η θ hθ0 hθ
  have hDpos : 0 < 4 * (1 + ε) / ε := by positivity
  obtain ⟨β₂, hβ₂, hthr⟩ := exists_claim32_threshold (144 * (4 * (1 + ε) / ε)) c₁
    (by positivity) hc₁
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  refine ⟨min β₀' (min (c₁ / Real.log 8) β₂),
    lt_min hβ₀' (lt_min (div_pos hc₁ hlog8) hβ₂), fun L hL => ?_⟩
  have hstep := h16 L hL
  dsimp only at hstep ⊢
  refine ⟨fun v β hβ hβlt lam hlam => ?_, fun hEven v β hβ hβlt lam hlam => ?_⟩
  · have h1 : β < β₀' := lt_of_lt_of_le hβlt (min_le_left _ _)
    have h2 : β < c₁ / Real.log 8 :=
      lt_of_lt_of_le hβlt ((min_le_right _ _).trans (min_le_left _ _))
    have h3 : β < β₂ := lt_of_lt_of_le hβlt ((min_le_right _ _).trans (min_le_right _ _))
    exact weightedBound_of_t16Data (squareFree L) (squareFree_connected L hL)
      (card_edgesWithin_densityDomain_squareFree_le L) ε hε c₁ β hβ h2 (hthr β hβ h3) v lam
      Γ η θ hlam (hstep.1 v β hβ h1 lam hlam)
  · have h1 : β < β₀' := lt_of_lt_of_le hβlt (min_le_left _ _)
    have h2 : β < c₁ / Real.log 8 :=
      lt_of_lt_of_le hβlt ((min_le_right _ _).trans (min_le_left _ _))
    have h3 : β < β₂ := lt_of_lt_of_le hβlt ((min_le_right _ _).trans (min_le_right _ _))
    exact weightedBound_of_t16Data (squarePeriodic L) (squarePeriodic_connected L hL)
      (card_edgesWithin_densityDomain_squarePeriodic_le L) ε hε c₁ β hβ h2 (hthr β hβ h3) v
      lam Γ η θ hlam (hstep.2 hEven v β hβ h1 lam hlam)


/--
KP Theorem 1.6 implies the `t15Statement` (definitionally the KP Theorem 1.5).
-/
theorem t15Statement_of_t16Statement : t16Statement → t15Statement :=
  t15_of_t16Statement

/--
KP Theorem 1.6 implies the statement of the KP Theorem 1.1, through
`t11_of_t15Statement`.
-/
theorem t11_of_t16Statement :
    t16Statement →
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ (L : ℕ) (hL : 1 < L),
        let bounds : ∀ {E : Type} [Fintype E]
            (Λ : Multigraph (Fin L × Fin L) E),
            Λ.toSimpleGraph.Connected → Prop :=
          fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
            (∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
              Multigraph.IsLaplacianPseudoinverse Λ T →
              ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
                ENNReal.ofReal (Real.exp
                    ((∑ j, f j * -(T f j)) / (2 * (1 + ε) * β))) ≤
                    ∫⁻ m, ENNReal.ofReal
                      (Real.exp (∑ j, (m j : ℝ) * f j))
                      ∂(integerGFFLaw Λ hΛ β hβ v) ∧
                  ENNReal.ofReal
                      ((∑ j, f j * -(T f j)) / ((1 + ε) * β)) ≤
                    ∫⁻ m, ENNReal.ofReal
                      ((∑ j, (m j : ℝ) * f j) ^ 2)
                      ∂(integerGFFLaw Λ hΛ β hβ v)) ∧
            ∀ j k : Fin L × Fin L,
              ENNReal.ofReal (c / β * Real.log
                (Λ.toSimpleGraph.dist j k + 1)) ≤
                ∫⁻ m, ENNReal.ofReal (((m j : ℝ) - m k) ^ 2)
                  ∂(integerGFFLaw Λ hΛ β hβ v)
        bounds (squareFree L) (squareFree_connected L hL) ∧
          (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL)) :=
  fun h => t11_of_t15Statement (t15Statement_of_t16Statement h)

end FroehlichSpencer.BKT.Reduction

end
