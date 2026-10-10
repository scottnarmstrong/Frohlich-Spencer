/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.Gas
public import FroehlichSpencer.BKT.Gaussian.WeightedGFF
public import FroehlichSpencer.BKT.Surface.WeightedGFFExpMoment
import Mathlib.Tactic

/-!
# FS81 Theorem 5.1 in finite volume, from the KP Theorem 1.5

The sine-Gordon state
`⟨·⟩_Λ(κ, z)` is KP's weighted functional `weightedGFFExpectation` with the weights
`hardCoreSineGordonInternal A z` (`1 + z cos φ` on `A`, `1` off `A`); `Coulomb/SineGordon.lean`
identifies it with the gas (FS81 (1.15)–(1.16)).

The threshold `κ₀` depends on `δ` and `α` only.

The printed statement fixes neither the boundary condition nor the domain shape ("free (or
periodic) b.c.", p. 564); FS81's free boundary condition (whole-plane potential restricted to
`Λ`, p. 529) is **not** the free-square graph Laplacian used here.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory

/-- The conclusion of FS81 Theorem 5.1 (5.4) on one finite domain `Λ`, with threshold `κ₀`:
for `κ > κ₀` and `0 ≤ z ≤ e^{κ/17 + α}`, `Z > 0` and
`⟨e^{u φ(f)}⟩ ≥ exp (u² κ (1 - δ) ⟨f, C f⟩ / 2)` for every zero-sum `f` and real `u`. -/
def HardCoreExpMomentBoundInternal {W : Type*} [Fintype W] [DecidableEq W] {E : Type*}
    [Fintype E] (Λ : Multigraph W E) (hΛ : Λ.toSimpleGraph.Connected) (δ α κ₀ : ℝ) : Prop :=
  ∀ (v : W) (A : Finset W) (κ : ℝ) (hκ : 0 < κ), κ₀ < κ →
    ∀ z : ℝ, 0 ≤ z → z ≤ Real.exp (κ / 17 + α) →
      0 < weightedGFFNormalizer Λ hΛ κ⁻¹ (inv_pos.2 hκ) v (hardCoreSineGordonInternal A z) ∧
      ∀ T : (W → ℝ) →ₗ[ℝ] W → ℝ, Λ.IsLaplacianPseudoinverse T →
        ∀ f : W → ℝ, ∑ j, f j = 0 → ∀ u : ℝ,
          Real.exp (u ^ 2 * κ * (1 - δ) * (∑ j, f j * -(T f j)) / 2) ≤
            weightedGFFExpectation Λ hΛ κ⁻¹ (inv_pos.2 hκ) v (hardCoreSineGordonInternal A z)
              (fun φ => Real.exp (u * ∑ j, φ j * f j))

/-- Transfer of the KP Theorem 1.5 bound on one domain to FS81 Theorem 5.1. -/
theorem hardCoreExpMomentBound_of_kp {W : Type*} [Fintype W] [DecidableEq W] {E : Type*}
    [Fintype E] (Λ : Multigraph W E) (hΛ : Λ.toSimpleGraph.Connected) (δ : ℝ) (hδ : 0 < δ)
    (α β₀ : ℝ) (hβ₀ : 0 < β₀)
    (H : ∀ (v : W) (β : ℝ) (hβ : 0 < β), β < β₀ →
      ∀ lam : W → ℝ → ℝ, (∀ j, IsSubGaussian (max 1 (Real.exp α / 2)) 0 (1 / 17) β (lam j)) →
        0 < ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v) ∧
        ∀ T : (W → ℝ) →ₗ[ℝ] W → ℝ, Λ.IsLaplacianPseudoinverse T →
          ∀ f : W → ℝ, ∑ j, f j = 0 →
            Real.exp ((∑ j, f j * -(T f j)) / (2 * (1 + δ) * β)) ≤
              (∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)) /
                ∫ φ, ∏ j, lam j (φ j) ∂(gffLaw Λ hΛ β hβ v)) :
    HardCoreExpMomentBoundInternal Λ hΛ δ α β₀⁻¹ := by
  intro v A κ hκ hκ₀ z hz hzκ
  have hβ : κ⁻¹ < β₀ := (inv_lt_comm₀ hκ hβ₀).2 hκ₀
  obtain ⟨hZ, hbd⟩ := H v κ⁻¹ (inv_pos.2 hκ) hβ (hardCoreSineGordonInternal A z)
    (isSubGaussian_hardCoreSineGordon A α κ z hz hzκ)
  refine ⟨hZ, fun T hT f hf u => ?_⟩
  have huf : ∑ j, (u • f) j = 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hf, mul_zero]
  have h := hbd T hT (u • f) huf
  have hQ : ∑ j, (u • f) j * -(T (u • f) j) = u ^ 2 * ∑ j, f j * -(T f j) := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hratio : (∫ φ, Real.exp (∑ j, φ j * (u • f) j) *
        ∏ j, hardCoreSineGordonInternal A z j (φ j) ∂(gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v)) /
      ∫ φ, ∏ j, hardCoreSineGordonInternal A z j (φ j) ∂(gffLaw Λ hΛ κ⁻¹ (inv_pos.2 hκ) v) =
      weightedGFFExpectation Λ hΛ κ⁻¹ (inv_pos.2 hκ) v (hardCoreSineGordonInternal A z)
        (fun φ => Real.exp (u * ∑ j, φ j * f j)) := by
    rw [weightedGFFExpectation_eq]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hQ, hratio] at h
  refine le_trans ?_ h
  apply Real.exp_le_exp.2
  have hTg : T = Λ.greenOp hΛ := Λ.greenOp_unique hΛ T hT.1 hT.2
  have hQnn : 0 ≤ ∑ j, f j * -(T f j) := by
    have := Λ.pairing_greenOp_nonneg hΛ f hf
    rw [hTg]
    simpa [Multigraph.pairing] using this
  obtain ⟨P, hP⟩ : ∃ P, P = u ^ 2 * κ * ∑ j, f j * -(T f j) := ⟨_, rfl⟩
  have hPnn : 0 ≤ P := by rw [hP]; positivity
  have hlhs : u ^ 2 * κ * (1 - δ) * (∑ j, f j * -(T f j)) / 2 = P * (1 - δ) / 2 := by
    rw [hP]; ring
  have hrhs : u ^ 2 * (∑ j, f j * -(T f j)) / (2 * (1 + δ) * κ⁻¹) = P / (2 * (1 + δ)) := by
    rw [hP]; field_simp
  rw [hlhs, hrhs, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hPnn (sq_nonneg δ)]

/-- **FS81 Theorem 5.1, finite volume** (J p. 564, (5.4)), for the hard-core gas on a free or
periodic square containing the charge region `A`: for each `δ > 0` and `α` there is `κ₀`,
independent of the volume, such that for `κ > κ₀` and `0 ≤ z ≤ e^{κ/17 + α}`,
`⟨e^{u φ(f)}⟩_Λ(κ, z) ≥ exp (u² κ (1 - δ) ⟨f, (-Δ)⁻¹ f⟩ / 2)` for every zero-sum `f`. -/
theorem hardCore_expMoment_lower_bound (δ : ℝ) (hδ : 0 < δ) (α : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ (L : ℕ) (hL : 1 < L),
      HardCoreExpMomentBoundInternal (squareFree L) (squareFree_connected L hL) δ α κ₀ ∧
        (Even L → HardCoreExpMomentBoundInternal (squarePeriodic L)
          (squarePeriodic_connected L hL) δ α κ₀) := by
  obtain ⟨β₀, hβ₀, H⟩ := weightedGFF_expMoment_lower_bound (max 1 (Real.exp α / 2))
    (zero_lt_one.trans_le (le_max_left _ _)) 0 (1 / 17) (by norm_num) (by norm_num) δ hδ
  refine ⟨β₀⁻¹, inv_pos.2 hβ₀, fun L hL => ?_⟩
  have h := H L hL
  dsimp only at h
  exact ⟨hardCoreExpMomentBound_of_kp _ _ δ hδ α β₀ hβ₀ h.1,
    fun he => hardCoreExpMomentBound_of_kp _ _ δ hδ α β₀ hβ₀ (h.2 he)⟩

end FroehlichSpencer.BKT.Coulomb
