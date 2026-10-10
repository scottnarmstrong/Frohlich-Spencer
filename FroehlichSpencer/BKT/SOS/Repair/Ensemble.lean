/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Repair.Lemmas

/-!
# The prefactor-one ensemble bound behind the SOS endpoint repair

FS81's proof of Theorem 7.3 loses a fixed prefactor `const·K` in (7.32), (7.35), (7.39)–(7.40), so
it cannot give (7.17) or, by differentiation at `ε = 0`, (7.18). The second-order comparison
replaces those comparisons by a second-order argument in the style of Kharash–Peled (Claims
3.1–3.2): along the path `t ↦ W_t` which turns on the real shift, the endpoint phases and the
observable, the ensemble exponent satisfies `W_0 = 0` and the reflection symmetry
`W_t(-φ) = W_{-t}(φ)`, and the reference ensemble measure is reflection invariant. Jensen then
removes the odd part, and the symmetric second difference leaves only `-½ sup |∂_t² W|`:

`∫ e^{W_1} dP ≥ e^{-B/2}` whenever `|∂_t² W_t| ≤ B` for `|t| ≤ 1`.

There is no fixed prefactor. The loss `B` is quadratic in the shift, phases and observable size.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Repair

open MeasureTheory

/-- The prefactor-one ensemble bound: under a reflection-invariant probability measure, an exponent
path with `W_0 = 0`, `W_t(-φ) = W_{-t}(φ)` and `|∂_t² W_t| ≤ B` on `|t| ≤ 1` has
`∫ e^{W_1} ≥ e^{-B/2}`. -/
theorem exp_neg_half_le_integral_exp {V : Type*} [Fintype V] {μ : Measure (V → ℝ)}
    [IsProbabilityMeasure μ] (hμ : Measure.map (fun φ => -φ) μ = μ)
    {W W' W'' : ℝ → (V → ℝ) → ℝ} {B : ℝ}
    (h0 : ∀ φ, W 0 φ = 0) (hsymm : ∀ t φ, W t (-φ) = W (-t) φ)
    (hd : ∀ φ s, |s| ≤ 1 → HasDerivAt (fun t => W t φ) (W' s φ) s)
    (hd' : ∀ φ s, |s| ≤ 1 → HasDerivAt (fun t => W' t φ) (W'' s φ) s)
    (hB : ∀ φ s, |s| ≤ 1 → |W'' s φ| ≤ B)
    (hint : Integrable (W 1) μ) (hexp : Integrable (fun φ => Real.exp (W 1 φ)) μ) :
    Real.exp (-(B / 2)) ≤ ∫ φ, Real.exp (W 1 φ) ∂μ := by
  refine le_trans ?_ (integral_exp_ge_exp_integral_even hμ hint hexp)
  apply Real.exp_le_exp.mpr
  have hpt : ∀ φ, -(B / 2) ≤ (W 1 φ + W 1 (-φ)) / 2 := by
    intro φ
    have h := add_neg_sub_two_mul_ge (g := fun t => W t φ) (g' := fun t => W' t φ)
      (g'' := fun t => W'' t φ) (t := 1)
      (fun s hs => hd φ s (by simpa using hs)) (fun s hs => hd' φ s (by simpa using hs))
      (fun s hs => hB φ s (by simpa using hs))
    simp only [one_pow, mul_one, h0 φ, mul_zero, sub_zero] at h
    rw [hsymm 1 φ]
    linarith
  have hconst : ∫ _φ : V → ℝ, -(B / 2) ∂μ = -(B / 2) := by simp
  rw [← hconst]
  have hneg : Integrable (fun φ => W 1 (-φ)) μ := by
    have hint' : Integrable (W 1) (Measure.map (fun φ : V → ℝ => -φ) μ) := by rw [hμ]; exact hint
    exact hint'.comp_measurable measurable_neg
  exact integral_mono (integrable_const _) ((hint.add hneg).div_const 2) hpt

/-- The final step of the repaired SOS argument: if each ensemble satisfies
`Z_𝒩(ε) ≥ e^{ε²(V/c - D Λ)} Z_𝒩` with prefactor one, `V ≥ max(V_min, c₁ log(1+|x|))` and
`2 c D Λ ≤ V_min`, then the moment generating function is at least `exp(ε² c₁ log(1+|x|)/(2c))`,
which is (7.17) with `β' = 2c/c₁`. -/
theorem exponent_lower_bound {ε V c D Λ c₁ ℓ : ℝ} (hc : 0 < c)
    (hV : c₁ * ℓ ≤ V) (hVΛ : 2 * c * (D * Λ) ≤ V) :
    ε ^ 2 * (c₁ * ℓ / (2 * c)) ≤ ε ^ 2 * (V / c - D * Λ) := by
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ε)
  rw [div_le_iff₀ (by positivity)]
  have h : (V / c - D * Λ) * (2 * c) = 2 * V - 2 * c * (D * Λ) := by field_simp
  rw [h]
  linarith

end FroehlichSpencer.BKT.SOS.Repair
