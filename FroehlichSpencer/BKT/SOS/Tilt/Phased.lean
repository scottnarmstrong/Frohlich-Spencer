/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.LocalFactor

/-!
# Character translation with a phase (the dipole tilt construction, FS81 (7.25)–(7.29) with the endpoint phases)

Under a law tilted by `e^{⟨Dφ, b⟩}`, the complex translation of a neutral character by `i a`
acquires the phase `e^{i ψ(a)}` with `ψ(a) = ⟨Da, b⟩` (`CharacterTranslationPhased`, a linear
`ψ`). The generic translation step then holds with every cosine phase `θ_i` shifted by
`ψ(a_i)`:

`∫ ∏_i [A_i + B_i cos θ_i] dμ = ∫ ∏_i [A_i + B_i e^{−⟨a_i, ϱ_i⟩} ½(e^{i(θ_i + ψ a_i)} R_{Da_i}
  + e^{−i(θ_i + ψ a_i)} R_{−Da_i})] dμ`

(`integral_prod_add_mul_cos_translate_phased`, and its local-factor form
`integral_prod_add_mul_cos_eq_localFactor_phased`). These shifts are FS81's endpoint phases
`α_ρ = ε(a_ρ(0) − a_ρ(x))` of (7.29). With `ψ = 0` this is the generic step of
`Generic/Translation.lean`, whose proof is followed line by line. The sign vector `n` picks up
`e^{iψ(Σ n_i a_i)} = Π_i e^{i n_i ψ(a_i)}`, which is the coefficient change `s ↦ s + ψ∘a`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Tilt

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Reduction (gffCharacter signSet mem_signSet)

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **Character translation with a linear phase `ψ`**: `μ` admits the complex translation
`φ ↦ φ + i a` of every neutral character, with the edge ratio at `Dφ + r` and the phase
`e^{iψ(a)}`. -/
structure CharacterTranslationPhased (μ : Measure (V → ℝ)) (D : (V → ℝ) →ₗ[ℝ] (E → ℝ))
    (w : ℂ → ℂ) (r : E → ℝ) (W : ℝ) (ψ : (V → ℝ) →ₗ[ℝ] ℝ) : Prop where
  integrable : ∀ τ a : V → ℝ, ∑ j, τ j = 0 → (∀ e, |D a e| ≤ W) →
    Integrable (fun φ => gffCharacter τ φ * edgeRatio w (D a) (D φ + r)) μ
  translate : ∀ τ a : V → ℝ, ∑ j, τ j = 0 → (∀ e, |D a e| ≤ W) →
    ∫ φ, gffCharacter τ φ ∂μ =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) * Complex.exp (((ψ a : ℝ) : ℂ) * I) *
        ∫ φ, gffCharacter τ φ * edgeRatio w (D a) (D φ + r) ∂μ

/-- **The phased translation step.** -/
theorem integral_prod_add_mul_cos_translate_phased (μ : Measure (V → ℝ)) [IsFiniteMeasure μ]
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (w : ℂ → ℂ) (r : E → ℝ) {W : ℝ} (hW0 : 0 ≤ W)
    (ψ : (V → ℝ) →ₗ[ℝ] ℝ) (hμ : CharacterTranslationPhased μ D w r W ψ)
    (hw : ∀ t : ℝ, w t ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ) (hneutral : ∀ i, ∑ j, ϱ i j = 0)
    (A B s : ι → ℝ) (a : ι → V → ℝ) (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, D (a i) e = 0 ∨ D (a i') e = 0)
    (hW : ∀ i e, |D (a i) e| ≤ W) :
    ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) ∂μ =
      ∫ φ, ∏ i, ((A i : ℂ) + ((B i * Real.exp (-∑ j, a i j * ϱ i j) : ℝ) : ℂ) *
        translatedCos w (D (a i)) (D φ + r) (∑ j, φ j * ϱ i j + (s i + ψ (a i)))) ∂μ := by
  classical
  set P := Fintype.piFinset fun _ : ι => signSet with hP
  set s' : ι → ℝ := fun i => s i + ψ (a i) with hs'
  set coef : (ι → ℤ) → ℂ := fun n =>
    ∏ i, (mixedCoeff (A i) (B i) (n i) * Complex.exp (I * ((n i : ℂ) * s i))) with hcoef
  set coef' : (ι → ℤ) → ℂ := fun n =>
    ∏ i, (mixedCoeff (A i) (B i) (n i) * Complex.exp (I * ((n i : ℂ) * s' i))) with hcoef'
  set τ : (ι → ℤ) → V → ℝ := fun n j => ∑ i, (n i : ℝ) * ϱ i j with hτ
  set an : (ι → ℤ) → V → ℝ := fun n j => ∑ i, (n i : ℝ) * a i j with han
  set ε : ι → ℝ := fun i => ∑ j, a i j * ϱ i j with hε
  have hτ0 : ∀ n, ∑ j, τ n j = 0 := by
    intro n
    simp only [hτ]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hneutral, mul_zero, Finset.sum_const_zero]
  have hstrip : ∀ n ∈ P, ∀ e, |D (an n) e| ≤ W := by
    intro n hn e
    have hn' : ∀ i, n i ∈ signSet := Fintype.mem_piFinset.mp hn
    rw [grad_signVector D a n, Finset.sum_apply]
    simpa [smul_eq_mul] using abs_signVector_grad_le D a hW0 hdisj hW n hn' e
  have hwx : ∀ φ : V → ℝ, ∀ e, w ((D φ + r) e) ≠ 0 := fun φ e => hw _
  -- the phase of a sign vector
  have hψan : ∀ n, ψ (an n) = ∑ i, (n i : ℝ) * ψ (a i) := by
    intro n
    have : an n = ∑ i, (n i : ℝ) • a i := by
      funext j
      simp [han, Finset.sum_apply, smul_eq_mul]
    rw [this, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hcoef_eq : ∀ n, coef n * Complex.exp (((ψ (an n) : ℝ) : ℂ) * I) = coef' n := by
    intro n
    simp only [hcoef, hcoef', hs']
    rw [hψan n]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  -- the left side, multiplied out
  have hleft : ∀ φ : V → ℝ,
      ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) =
        ∑ n ∈ P, coef n * gffCharacter (τ n) φ := by
    intro φ
    rw [prod_add_mul_cos_eq_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.prod_mul_distrib, prod_exp_eq_character n ϱ s φ, hcoef, ← mul_assoc,
      ← Finset.prod_mul_distrib]
  -- the right side, multiplied out
  have hright : ∀ φ : V → ℝ,
      ∏ i, ((A i : ℂ) + ((B i * Real.exp (-∑ j, a i j * ϱ i j) : ℝ) : ℂ) *
          translatedCos w (D (a i)) (D φ + r) (∑ j, φ j * ϱ i j + s' i)) =
        ∑ n ∈ P, coef' n * Complex.exp (-((∑ j, an n j * τ n j : ℝ) : ℂ)) *
          (gffCharacter (τ n) φ * edgeRatio w (D (an n)) (D φ + r)) := by
    intro φ
    rw [prod_translated_eq_sum A B (fun i => ∑ j, φ j * ϱ i j + s' i) ε w (fun i => D (a i))
      (D φ + r) (hwx φ)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hratio : edgeRatio w (D (an n)) (D φ + r) =
        ∏ i, edgeRatio w ((n i : ℝ) • D (a i)) (D φ + r) := by
      rw [grad_signVector D a n]
      refine edgeRatio_sum Finset.univ w _ _ (hwx φ) fun i _ i' _ hne e => ?_
      rcases hdisj i i' hne e with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
    have hpair : Complex.exp (-((∑ j, an n j * τ n j : ℝ) : ℂ)) =
        ∏ i, Complex.exp (-((n i : ℂ) ^ 2 * ε i)) := by
      rw [← Complex.exp_sum]
      congr 1
      simp only [han, hτ, hε]
      rw [pairing_signVector a ϱ horth n]
      push_cast
      rw [← Finset.sum_neg_distrib]
    rw [hratio, hpair]
    simp only [Finset.prod_mul_distrib]
    rw [prod_exp_eq_character n ϱ s' φ]
    simp only [hcoef', Finset.prod_mul_distrib]
    ring
  -- integrate
  have hint : ∀ n ∈ P, Integrable
      (fun φ => coef' n * Complex.exp (-((∑ j, an n j * τ n j : ℝ) : ℂ)) *
        (gffCharacter (τ n) φ * edgeRatio w (D (an n)) (D φ + r))) μ :=
    fun n hn => (hμ.integrable (τ n) (an n) (hτ0 n) (hstrip n hn)).const_mul _
  simp_rw [hleft]
  have hright' : ∀ φ : V → ℝ,
      ∏ i, ((A i : ℂ) + ((B i * Real.exp (-∑ j, a i j * ϱ i j) : ℝ) : ℂ) *
          translatedCos w (D (a i)) (D φ + r) (∑ j, φ j * ϱ i j + (s i + ψ (a i)))) =
        ∑ n ∈ P, coef' n * Complex.exp (-((∑ j, an n j * τ n j : ℝ) : ℂ)) *
          (gffCharacter (τ n) φ * edgeRatio w (D (an n)) (D φ + r)) := hright
  simp_rw [hright']
  rw [integral_finsetSum P fun n _ => (Reduction.integrable_gffCharacter μ (τ n)).const_mul _,
    integral_finsetSum P hint]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_const_mul, integral_const_mul,
    hμ.translate (τ n) (an n) (hτ0 n) (hstrip n hn), ← hcoef_eq n]
  ring

/-- **The phased translation step in local-factor form.** -/
theorem integral_prod_add_mul_cos_eq_localFactor_phased (μ : Measure (V → ℝ))
    [IsFiniteMeasure μ] (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (w : ℂ → ℂ) (c : ℝ → ℝ)
    (hc : ∀ u, c (-u) = c u) (r : E → ℝ) {W : ℝ} (hW0 : 0 ≤ W) (ψ : (V → ℝ) →ₗ[ℝ] ℝ)
    (hμ : CharacterTranslationPhased μ D w r W ψ)
    (hw : ∀ t : ℝ, w t ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (hneutral : ∀ i, ∑ j, ϱ i j = 0) (A B s : ι → ℝ) (a : ι → V → ℝ)
    (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, D (a i) e = 0 ∨ D (a i') e = 0)
    (hW : ∀ i e, |D (a i) e| ≤ W) :
    ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) ∂μ =
      ∫ φ, ∏ i, ((A i : ℂ) + ((B i * Real.exp (-translationEnergy c D (a i) (ϱ i)) : ℝ) : ℂ) *
        localFactor w c (D (a i)) (D φ + r) (∑ j, φ j * ϱ i j + (s i + ψ (a i)))) ∂μ := by
  rw [integral_prod_add_mul_cos_translate_phased μ D w r hW0 ψ hμ hw ϱ hneutral A B s a horth
    hdisj hW]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, mul_assoc, mul_assoc,
    exp_mul_translatedCos w hc D (a i) (ϱ i)]

end FroehlichSpencer.BKT.SOS.Tilt

end
