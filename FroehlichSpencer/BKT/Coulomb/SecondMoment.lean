/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ExpMoment
import FroehlichSpencer.BKT.Coulomb.MomentCalculus
import Mathlib.Tactic

/-!
# FS81 Theorem A in finite volume: the field second moment

(1.19) with `c₁ = (1 - δ) κ`.

* `hasDerivAt_weightedGFFExpectation_pow_mul_exp`: for bounded continuous weights
  `∏_j λ_j(φ_j)` and zero-sum `f`, the moment functional `u ↦ 𝔼[X^k e^{u X}]`, `X = ⟨φ, f⟩`,
  is differentiable with derivative `𝔼[X^{k+1} e^{u X}]` (differentiation under the integral
  sign, `Coulomb/MomentCalculus.lean`, with the GFF exponential moments of KP (1.4)).

Hence
  `M(u) = 𝔼[e^{u X}]` is twice differentiable and `M''(0) = 𝔼[X²]`, a genuine integral against
  the signed measure `Z⁻¹ ∏_j λ_j(φ_j) dμ`.
* `two_mul_le_weightedGFFExpectation_sq`: `M(u) ≥ e^{A u²}` for all `u` and `Z ≠ 0` imply
  `𝔼[X²] ≥ 2A` (FS81 (5.5)).

Neither evenness nor analyticity of `M` is used.
* `hardCore_secondMoment_lower_bound`: **FS81 Theorem A in finite volume** for the hard-core gas
  on free and even periodic squares, uniform in the volume, from
  `hardCore_expMoment_lower_bound` ( KP Theorem 1.5).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory Filter Topology

variable {W : Type*} [Fintype W] [DecidableEq W] {E : Type*} [Fintype E]

/-! ### Bounded continuous sine-Gordon weights -/

omit [Fintype W] [DecidableEq W] in
theorem continuous_sineGordonWeight (N : ℕ) (lam : ℤ → ℝ) :
    Continuous (sineGordonWeightInternal N lam) := by
  unfold sineGordonWeightInternal
  fun_prop

omit [Fintype W] [DecidableEq W] in
theorem abs_sineGordonWeight_le (N : ℕ) (lam : ℤ → ℝ) (φ : ℝ) :
    |sineGordonWeightInternal N lam φ| ≤ ∑ n ∈ Finset.Icc (-(N : ℤ)) N, |lam n| := by
  unfold sineGordonWeightInternal
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-! ### The field: differentiability of the moment functional -/

section Field

variable (Λ : Multigraph W E) (hΛ : Λ.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : W)
  (lam : W → ℝ → ℝ)

omit [DecidableEq W] in
theorem integrable_exp_mul_pairing_gffLaw (f : W → ℝ) (hf : ∑ j, f j = 0) (c : ℝ) :
    Integrable (fun φ : W → ℝ => Real.exp (c * ∑ j, φ j * f j)) (gffLaw Λ hΛ β hβ v) := by
  have hcf : ∑ j, (c • f) j = 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hf, mul_zero]
  refine (integrable_exp_pairing_gffLaw Λ hΛ β hβ v (c • f) hcf).congr (ae_of_all _ fun φ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq W] in
/-- Differentiation of the weighted moment functional `u ↦ 𝔼[X^k e^{u X}]`, `X = ⟨φ, f⟩`. -/
theorem hasDerivAt_weightedGFFExpectation_pow_mul_exp
    (hWc : Continuous fun φ : W → ℝ => ∏ j, lam j (φ j)) {B : ℝ}
    (hWB : ∀ φ : W → ℝ, |∏ j, lam j (φ j)| ≤ B) (f : W → ℝ) (hf : ∑ j, f j = 0) (k : ℕ)
    (u : ℝ) :
    HasDerivAt (fun u => weightedGFFExpectation Λ hΛ β hβ v lam
        (fun φ => (∑ j, φ j * f j) ^ k * Real.exp (u * ∑ j, φ j * f j)))
      (weightedGFFExpectation Λ hΛ β hβ v lam
        (fun φ => (∑ j, φ j * f j) ^ (k + 1) * Real.exp (u * ∑ j, φ j * f j))) u := by
  unfold weightedGFFExpectation
  exact (hasDerivAt_integral_pow_mul_exp_mul (X := fun φ : W → ℝ => ∑ j, φ j * f j)
    (W := fun φ => ∏ j, lam j (φ j)) (by fun_prop) hWc.aestronglyMeasurable hWB
    (integrable_exp_mul_pairing_gffLaw Λ hΛ β hβ v f hf) k u).div_const _

omit [DecidableEq W] in
/-- FS81 (5.5): an exponential-moment lower bound `𝔼[e^{u φ(f)}] ≥ e^{A u²}` for the weighted
(signed) functional implies `𝔼[φ(f)²] ≥ 2A`; the second moment is a genuine integral. -/
theorem two_mul_le_weightedGFFExpectation_sq
    (hWc : Continuous fun φ : W → ℝ => ∏ j, lam j (φ j)) {B : ℝ}
    (hWB : ∀ φ : W → ℝ, |∏ j, lam j (φ j)| ≤ B) (f : W → ℝ) (hf : ∑ j, f j = 0) (A : ℝ)
    (hZ : weightedGFFNormalizer Λ hΛ β hβ v lam ≠ 0)
    (hlow : ∀ u : ℝ, Real.exp (A * u ^ 2) ≤
      weightedGFFExpectation Λ hΛ β hβ v lam (fun φ => Real.exp (u * ∑ j, φ j * f j))) :
    2 * A ≤ weightedGFFExpectation Λ hΛ β hβ v lam (fun φ => (∑ j, φ j * f j) ^ 2) := by
  have hd := hasDerivAt_weightedGFFExpectation_pow_mul_exp Λ hΛ β hβ v lam hWc hWB f hf
  have h := two_mul_le_of_exp_sq_le (M := fun u => weightedGFFExpectation Λ hΛ β hβ v lam
      (fun φ => (∑ j, φ j * f j) ^ 0 * Real.exp (u * ∑ j, φ j * f j)))
    (M' := fun u => weightedGFFExpectation Λ hΛ β hβ v lam
      (fun φ => (∑ j, φ j * f j) ^ (0 + 1) * Real.exp (u * ∑ j, φ j * f j)))
    (A := A) ?_ (Eventually.of_forall fun u => hd 0 u) (hd 1 0) ?_
  · simpa using h
  · simp only [pow_zero, one_mul, zero_mul, Real.exp_zero]
    unfold weightedGFFExpectation weightedGFFNormalizer at *
    simp only [one_mul]
    exact div_self hZ
  · exact Eventually.of_forall fun u => by simpa using hlow u

end Field

/-! ### FS81 Theorem A in finite volume (hard-core gas) -/

/-- The conclusion of FS81 Theorem A, (1.19) with `c₁ = (1 - δ) κ` (J pp. 532, 564–567), on one
domain: `⟨φ(f)²⟩_Λ(κ, z) ≥ (1 - δ) κ ⟨f, (-Δ)⁻¹ f⟩` for zero-sum `f`. -/
def HardCoreSecondMomentBoundInternal (Λ : Multigraph W E) (hΛ : Λ.toSimpleGraph.Connected)
    (δ α κ₀ : ℝ) : Prop :=
  ∀ (v : W) (A : Finset W) (κ : ℝ) (hκ : 0 < κ), κ₀ < κ →
    ∀ z : ℝ, 0 ≤ z → z ≤ Real.exp (κ / 17 + α) →
      ∀ T : (W → ℝ) →ₗ[ℝ] W → ℝ, Λ.IsLaplacianPseudoinverse T →
        ∀ f : W → ℝ, ∑ j, f j = 0 →
          (1 - δ) * κ * (∑ j, f j * -(T f j)) ≤
            weightedGFFExpectation Λ hΛ κ⁻¹ (inv_pos.2 hκ) v (hardCoreSineGordonInternal A z)
              (fun φ => (∑ j, φ j * f j) ^ 2)

theorem continuous_prod_hardCoreSineGordon (A : Finset W) (z : ℝ) :
    Continuous fun φ : W → ℝ => ∏ j, hardCoreSineGordonInternal A z j (φ j) :=
  continuous_finsetProd _ fun j _ =>
    (continuous_sineGordonWeight 1 _).comp (continuous_apply j)

theorem abs_prod_hardCoreSineGordon_le (A : Finset W) (z : ℝ) (φ : W → ℝ) :
    |∏ j, hardCoreSineGordonInternal A z j (φ j)| ≤
      ∏ j, ∑ n ∈ Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ),
        |regionWeightInternal A (hardCoreWeightInternal z) j n| := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => abs_sineGordonWeight_le _ _ _

/-- Theorem 5.1 implies Theorem A on each domain (FS81 (5.5)). -/
theorem hardCoreSecondMomentBound_of_expMomentBound (Λ : Multigraph W E)
    (hΛ : Λ.toSimpleGraph.Connected) (δ α κ₀ : ℝ)
    (h : HardCoreExpMomentBoundInternal Λ hΛ δ α κ₀) :
    HardCoreSecondMomentBoundInternal Λ hΛ δ α κ₀ := by
  intro v A κ hκ hκ₀ z hz hzκ T hT f hf
  obtain ⟨hZ, hbd⟩ := h v A κ hκ hκ₀ z hz hzκ
  have h2 := two_mul_le_weightedGFFExpectation_sq Λ hΛ κ⁻¹ (inv_pos.2 hκ) v
    (hardCoreSineGordonInternal A z) (continuous_prod_hardCoreSineGordon A z)
    (abs_prod_hardCoreSineGordon_le A z) f hf ((1 - δ) * κ * (∑ j, f j * -(T f j)) / 2)
    hZ.ne' fun u => by
      have := hbd T hT f hf u
      convert this using 2
      ring
  convert h2 using 1
  ring

/-- **FS81 Theorem A, finite volume** (J p. 532, (1.19); proof p. 564, (5.5), and p. 567), for
the hard-core gas on free and even periodic squares: for each `δ > 0` and `α` there is `κ₀`,
independent of the volume, such that `⟨φ(f)²⟩_Λ(κ, z) ≥ (1 - δ) κ ⟨f, (-Δ)⁻¹ f⟩` for
`κ > κ₀`, `0 ≤ z ≤ e^{κ/17 + α}` and every zero-sum `f`. -/
theorem hardCore_secondMoment_lower_bound (δ : ℝ) (hδ : 0 < δ) (α : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ (L : ℕ) (hL : 1 < L),
      HardCoreSecondMomentBoundInternal (squareFree L) (squareFree_connected L hL) δ α κ₀ ∧
        (Even L → HardCoreSecondMomentBoundInternal (squarePeriodic L)
          (squarePeriodic_connected L hL) δ α κ₀) := by
  obtain ⟨κ₀, hκ₀, h⟩ := hardCore_expMoment_lower_bound δ hδ α
  exact ⟨κ₀, hκ₀, fun L hL => ⟨hardCoreSecondMomentBound_of_expMomentBound _ _ δ α κ₀ (h L hL).1,
    fun he => hardCoreSecondMomentBound_of_expMomentBound _ _ δ α κ₀ ((h L hL).2 he)⟩⟩

end FroehlichSpencer.BKT.Coulomb
