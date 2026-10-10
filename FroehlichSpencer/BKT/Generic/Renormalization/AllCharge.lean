/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.LocalFactor
public import FroehlichSpencer.BKT.Generic.EdgeLaw.Translation

/-!
# All-charge character translation (generic core)

`CharacterTranslation` (`Generic/Translation.lean`) asks for the translation of *neutral*
characters only, which is what KP's rooted law `gffLaw` and the rooted `edgeLaw` satisfy (their
root phase kills charged characters).

This module gives translation identities for densities of arbitrary charge. The multi-site
contour shift uses the edgewise strip condition `|∇a| ≤ W` along the deformation
(`Generic/EdgeLaw/MultiSiteShift.lean`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Reduction (gffCharacter signSet)
open FroehlichSpencer.BKT.Rotator.Contour (PinnedGraph)

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Complex translation of **every** character: the all-charge form of `CharacterTranslation`. -/
structure CharacterTranslationAll (μ : Measure (V → ℝ)) (D : (V → ℝ) →ₗ[ℝ] (E → ℝ))
    (w : ℂ → ℂ) (r : E → ℝ) (W : ℝ) : Prop where
  integrable : ∀ τ a : V → ℝ, (∀ e, |D a e| ≤ W) →
    Integrable (fun φ => gffCharacter τ φ * edgeRatio w (D a) (D φ + r)) μ
  translate : ∀ τ a : V → ℝ, (∀ e, |D a e| ≤ W) →
    ∫ φ, gffCharacter τ φ ∂μ =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, gffCharacter τ φ * edgeRatio w (D a) (D φ + r) ∂μ

/-- The all-charge translation implies the neutral one. -/
theorem CharacterTranslationAll.toCharacterTranslation {μ : Measure (V → ℝ)}
    {D : (V → ℝ) →ₗ[ℝ] (E → ℝ)} {w : ℂ → ℂ} {r : E → ℝ} {W : ℝ}
    (h : CharacterTranslationAll μ D w r W) : CharacterTranslation μ D w r W :=
  ⟨fun τ a _ ha => h.integrable τ a ha, fun τ a _ ha => h.translate τ a ha⟩

/-- **The generic translation step for densities of arbitrary charge.** -/
theorem integral_prod_add_mul_cos_translate_all (μ : Measure (V → ℝ)) [IsFiniteMeasure μ]
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (w : ℂ → ℂ) (r : E → ℝ) {W : ℝ} (hW0 : 0 ≤ W)
    (hμ : CharacterTranslationAll μ D w r W) (hw : ∀ t : ℝ, w t ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (A B s : ι → ℝ) (a : ι → V → ℝ) (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, D (a i) e = 0 ∨ D (a i') e = 0)
    (hW : ∀ i e, |D (a i) e| ≤ W) :
    ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) ∂μ =
      ∫ φ, ∏ i, ((A i : ℂ) + ((B i * Real.exp (-∑ j, a i j * ϱ i j) : ℝ) : ℂ) *
        translatedCos w (D (a i)) (D φ + r) (∑ j, φ j * ϱ i j + s i)) ∂μ := by
  classical
  set P := Fintype.piFinset fun _ : ι => signSet with hP
  -- the data of a sign vector
  set coef : (ι → ℤ) → ℂ := fun n =>
    ∏ i, (mixedCoeff (A i) (B i) (n i) * Complex.exp (I * ((n i : ℂ) * s i))) with hcoef
  set τ : (ι → ℤ) → V → ℝ := fun n j => ∑ i, (n i : ℝ) * ϱ i j with hτ
  set an : (ι → ℤ) → V → ℝ := fun n j => ∑ i, (n i : ℝ) * a i j with han
  set ε : ι → ℝ := fun i => ∑ j, a i j * ϱ i j with hε
  have hstrip : ∀ n ∈ P, ∀ e, |D (an n) e| ≤ W := by
    intro n hn e
    have hn' : ∀ i, n i ∈ signSet := Fintype.mem_piFinset.mp hn
    rw [grad_signVector D a n, Finset.sum_apply]
    simpa [smul_eq_mul] using abs_signVector_grad_le D a hW0 hdisj hW n hn' e
  have hwx : ∀ φ : V → ℝ, ∀ e, w ((D φ + r) e) ≠ 0 := fun φ e => hw _
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
          translatedCos w (D (a i)) (D φ + r) (∑ j, φ j * ϱ i j + s i)) =
        ∑ n ∈ P, coef n * Complex.exp (-((∑ j, an n j * τ n j : ℝ) : ℂ)) *
          (gffCharacter (τ n) φ * edgeRatio w (D (an n)) (D φ + r)) := by
    intro φ
    rw [prod_translated_eq_sum A B (fun i => ∑ j, φ j * ϱ i j + s i) ε w (fun i => D (a i))
      (D φ + r) (hwx φ)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : ∀ i, n i ∈ signSet := Fintype.mem_piFinset.mp hn
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
    rw [prod_exp_eq_character n ϱ s φ]
    simp only [hcoef, Finset.prod_mul_distrib]
    ring
  -- integrate
  have hint : ∀ n ∈ P, Integrable
      (fun φ => coef n * Complex.exp (-((∑ j, an n j * τ n j : ℝ) : ℂ)) *
        (gffCharacter (τ n) φ * edgeRatio w (D (an n)) (D φ + r))) μ :=
    fun n hn => (hμ.integrable (τ n) (an n) (hstrip n hn)).const_mul _
  simp_rw [hleft, hright]
  rw [integral_finsetSum P fun n _ => (Reduction.integrable_gffCharacter μ (τ n)).const_mul _,
    integral_finsetSum P hint]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_const_mul, integral_const_mul,
    hμ.translate (τ n) (an n) (hstrip n hn), mul_assoc]


/-- **The generic translation step for densities of arbitrary charge, normalized**: the all-charge
form of `integral_prod_add_mul_cos_eq_localFactor`. -/
theorem integral_prod_add_mul_cos_eq_localFactor_all (μ : Measure (V → ℝ)) [IsFiniteMeasure μ]
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (w : ℂ → ℂ) (c : ℝ → ℝ) (hc : ∀ u, c (-u) = c u)
    (r : E → ℝ) {W : ℝ} (hW0 : 0 ≤ W) (hμ : CharacterTranslationAll μ D w r W)
    (hw : ∀ t : ℝ, w t ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (A B s : ι → ℝ) (a : ι → V → ℝ)
    (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, D (a i) e = 0 ∨ D (a i') e = 0)
    (hW : ∀ i e, |D (a i) e| ≤ W) :
    ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) ∂μ =
      ∫ φ, ∏ i, ((A i : ℂ) + ((B i * Real.exp (-translationEnergy c D (a i) (ϱ i)) : ℝ) : ℂ) *
        localFactor w c (D (a i)) (D φ + r) (∑ j, φ j * ϱ i j + s i)) ∂μ := by
  rw [integral_prod_add_mul_cos_translate_all μ D w r hW0 hμ hw ϱ A B s a horth hdisj hW]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, mul_assoc, mul_assoc,
    exp_mul_translatedCos w hc D (a i) (ϱ i)]


theorem characterTranslationAll_pinnedEdgeLaw [DecidableEq V] (G : PinnedGraph V E)
    (hanchor : ∀ a : V → ℝ, pinnedGradLinear G a = 0 → a = 0)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) :
    CharacterTranslationAll (pinnedEdgeLaw G w) (pinnedGradLinear G) w (pinOffset G) W := by
  have hlaw : pinnedEdgeLaw G w = densityLaw (fun φ => (fun _ => (1 : ℝ)) φ *
      ∏ e, (w ((pinnedGradLinear G φ e + pinOffset G e : ℝ) : ℂ)).re) := by
    rw [pinnedEdgeLaw_eq_densityLaw]
    congr 1
    funext φ
    simp only [pinnedEdgeDensity, one_mul, realGrad_eq, Pi.add_apply]
  rw [hlaw]
  refine ⟨fun τ a haW => integrable_character_mul_edgeRatio hw _ _ _ τ a haW,
    fun τ a haW => ?_⟩
  refine translate_densityLaw hw (pinnedGradLinear G) (pinOffset G) (fun _ => 1)
    measurable_const (fun _ => zero_le_one) (fun _ => le_rfl) τ a haW (fun _ _ => rfl) ?_
  intro ha0
  by_contra hcon
  push Not at hcon
  exact ha0 (hanchor a (funext hcon))

end FroehlichSpencer.BKT.Generic

end
