/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeRatio
public import FroehlichSpencer.BKT.Reduction.SpinWaveTranslation

/-!
# Complex translation of an ensemble product (generic core)

This is the measure-dependent step of KP Theorem 1.6, isolated from the Gaussian law.

KP §2.3.3,
pp. 12–13, (2.18)–(2.20) (Kharash–Peled, first version)
translates every ensemble factor by its own spin wave; FS81 (4.36)–(4.41) and (6.18)–(6.20)
(J pp. 557–558, 579–580) does the same for a non-Gaussian edge weight, where the translated factor
is no longer a cosine.

**The interface.** `CharacterTranslation μ D w r W` says that a law `μ` on real fields, with
linear edge gradient `D` and real edge offsets `r`, admits the complex translation `φ ↦ φ + i a`
of every neutral character, for every real `a` whose gradient stays in the strip `|D a| ≤ W`:

`∫ e^{i⟨φ, τ⟩} dμ = e^{-⟨a, τ⟩} ∫ e^{i⟨φ, τ⟩} R_{D a}(D φ + r) dμ`,  `R` the edge ratio of `w`.

For the KP Gaussian law, `w(z) = e^{-β z²/2}` and `R` is a constant times a character, so the
right side is again a character (KP (2.19)).

For an edge-product law `∏_e w(D φ(e) + r(e)) dφ`
it is the contour shift of FS81 Lemma 4.3 in every coordinate at once.

**The theorem.** `integral_prod_add_mul_cos_translate`: for densities `ϱ_i` (real-valued, so
that FS81's marked charges `ξ ϱ₀ + ϱ` are included), factors `A_i + B_i cos(⟨φ, ϱ_i⟩ + s_i)`
(KP's `1 + K cos` and FS81's marked `cos` alike), and spin waves `a_i` with
`⟨a_i, ϱ_{i'}⟩ = 0` and disjoint gradient supports for `i ≠ i'`,

`∫ ∏_i [A_i + B_i cos θ_i] dμ = ∫ ∏_i [A_i + B_i e^{-⟨a_i, ϱ_i⟩} ½(e^{iθ_i} R_{D a_i} + e^{-iθ_i} R_{-D a_i})] dμ`.

The proof follows KP  (as in `Reduction.gffLaw_integral_prod_spinWave_translation`):
expand over signs `n ∈ {-1, 0, 1}^ι`, translate each character `τ_n = ∑ n_i ϱ_i` by
`a_n = ∑ n_i a_i`, use `⟨a_n, τ_n⟩ = ∑ n_i² ⟨a_i, ϱ_i⟩` and `R_{D a_n} = ∏_i R_{n_i D a_i}`
(gradient disjointness, `edgeRatio_sum`), and resum.

Gradient disjointness replaces KP's
`⟨a_i, Δ a_{i'}⟩ = 0`, which suffices only for a quadratic weight.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Reduction (gffCharacter signSet mem_signSet)

variable {V E : Type*} [Fintype V] [Fintype E]

/-- KP (2.19) / FS81 Lemma 4.3 for characters: `μ` admits the complex translation `φ ↦ φ + i a`
of every neutral character `e^{i⟨φ, τ⟩}`, for every real `a` with `|D a(e)| ≤ W`, with the edge
ratio of `w` at the shifted real gradients `D φ + r`; the translated integrand is integrable. -/
structure CharacterTranslation (μ : Measure (V → ℝ)) (D : (V → ℝ) →ₗ[ℝ] (E → ℝ))
    (w : ℂ → ℂ) (r : E → ℝ) (W : ℝ) : Prop where
  integrable : ∀ τ a : V → ℝ, ∑ j, τ j = 0 → (∀ e, |D a e| ≤ W) →
    Integrable (fun φ => gffCharacter τ φ * edgeRatio w (D a) (D φ + r)) μ
  translate : ∀ τ a : V → ℝ, ∑ j, τ j = 0 → (∀ e, |D a e| ≤ W) →
    ∫ φ, gffCharacter τ φ ∂μ =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, gffCharacter τ φ * edgeRatio w (D a) (D φ + r) ∂μ

/-! ## The sign expansion of `A + B cos t` -/

/-- The coefficient of `e^{int}` in `A + B cos t`, for `n ∈ {-1, 0, 1}`. -/
def mixedCoeff (A B : ℝ) (n : ℤ) : ℂ := if n = 0 then (A : ℂ) else (B : ℂ) / 2

/-- FS81 (6.18) before normalization: `½ (e^{iθ} R_b(x) + e^{-iθ} R_{-b}(x))`. -/
def translatedCos (w : ℂ → ℂ) (b x : E → ℝ) (θ : ℝ) : ℂ :=
  (Complex.exp (I * θ) * edgeRatio w b x + Complex.exp (-(I * θ)) * edgeRatio w (-b) x) / 2

/-- One factor, resummed over its sign:
`∑_{n ∈ {-1,0,1}} c(A, B, n) e^{inθ} e^{-n² ε} R_{n b}(x) = A + B e^{-ε} ½(e^{iθ} R_b + e^{-iθ} R_{-b})`. -/
lemma sum_signSet_term (A B θ ε : ℝ) (w : ℂ → ℂ) (b x : E → ℝ) (hw : ∀ e, w (x e) ≠ 0) :
    ∑ n ∈ signSet, mixedCoeff A B n * Complex.exp (I * ((n : ℂ) * θ)) *
        Complex.exp (-((n : ℂ) ^ 2 * ε)) * edgeRatio w ((n : ℝ) • b) x =
      (A : ℂ) + ((B * Real.exp (-ε) : ℝ) : ℂ) * translatedCos w b x θ := by
  have h0 : edgeRatio w ((((0 : ℤ) : ℝ)) • b) x = 1 := by
    rw [Int.cast_zero, zero_smul]; exact edgeRatio_zero w x hw
  have h1 : (((1 : ℤ) : ℝ)) • b = b := by rw [Int.cast_one, one_smul]
  have hm1 : (((-1 : ℤ) : ℝ)) • b = -b := by rw [Int.cast_neg, Int.cast_one, neg_one_smul]
  simp only [signSet]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, h0, h1,
    hm1]
  simp only [mixedCoeff, translatedCos, Complex.ofReal_mul, Complex.ofReal_exp]
  simp only [show ((-1 : ℤ) = 0) = False by decide, show ((1 : ℤ) = 0) = False by decide,
    ite_false, ite_true, Int.cast_neg, Int.cast_one, Int.cast_zero]
  push_cast
  simp only [zero_mul, mul_zero, neg_zero, Complex.exp_zero, mul_one, one_mul, neg_one_mul,
    one_pow, even_two, Even.neg_pow, zero_pow two_ne_zero, mul_neg]
  ring

/-- The product of resummed factors, multiplied out over sign vectors. -/
lemma prod_translated_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (A B θ ε : ι → ℝ)
    (w : ℂ → ℂ) (b : ι → E → ℝ) (x : E → ℝ) (hw : ∀ e, w (x e) ≠ 0) :
    ∏ i, ((A i : ℂ) + ((B i * Real.exp (-ε i) : ℝ) : ℂ) * translatedCos w (b i) x (θ i)) =
      ∑ n ∈ Fintype.piFinset fun _ : ι => signSet, ∏ i, (mixedCoeff (A i) (B i) (n i) *
        Complex.exp (I * ((n i : ℂ) * θ i)) * Complex.exp (-((n i : ℂ) ^ 2 * ε i)) *
          edgeRatio w ((n i : ℝ) • b i) x) := by
  simp_rw [← sum_signSet_term _ _ _ _ w _ x hw]
  exact Finset.prod_univ_sum _ _

/-- The product `∏_i (A_i + B_i cos θ_i)` multiplied out over sign vectors. -/
lemma prod_add_mul_cos_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (A B θ : ι → ℝ) :
    ((∏ i, (A i + B i * Real.cos (θ i)) : ℝ) : ℂ) =
      ∑ n ∈ Fintype.piFinset fun _ : ι => signSet,
        ∏ i, (mixedCoeff (A i) (B i) (n i) * Complex.exp (I * ((n i : ℂ) * θ i))) := by
  rw [Complex.ofReal_prod]
  have hone : ∀ i, ((A i + B i * Real.cos (θ i) : ℝ) : ℂ) =
      ∑ n ∈ signSet, mixedCoeff (A i) (B i) n * Complex.exp (I * ((n : ℂ) * θ i)) := by
    intro i
    have hcos : Complex.cos (θ i : ℂ) =
        (Complex.exp (I * θ i) + Complex.exp (I * (-(θ i : ℂ)))) / 2 := by
      rw [mul_comm I, mul_comm I, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,
        Complex.sin_neg]
      ring
    simp only [signSet, mixedCoeff]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [show ((-1 : ℤ) = 0) = False by decide, show ((1 : ℤ) = 0) = False by decide,
      ite_false, ite_true]
    push_cast
    rw [hcos]
    simp only [zero_mul, mul_zero, Complex.exp_zero, mul_one, neg_one_mul, one_mul]
    ring
  simp_rw [hone]
  exact Finset.prod_univ_sum _ _

/-! ## The translation of one sign vector -/

section SignVector

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The character of a sign vector, `e^{i ∑_i n_i θ_i} = e^{i ∑_i n_i s_i} e^{i⟨φ, ∑_i n_i ϱ_i⟩}`
for `θ_i = ⟨φ, ϱ_i⟩ + s_i`. -/
lemma prod_exp_eq_character (n : ι → ℤ) (ϱ : ι → V → ℝ) (s : ι → ℝ) (φ : V → ℝ) :
    ∏ i, Complex.exp (I * ((n i : ℂ) * ((∑ j, φ j * ϱ i j + s i : ℝ) : ℂ))) =
      (∏ i, Complex.exp (I * ((n i : ℂ) * s i))) *
        gffCharacter (fun j => ∑ i, (n i : ℝ) * ϱ i j) φ := by
  rw [← Complex.exp_sum, ← Complex.exp_sum, gffCharacter, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

omit [Fintype V] [Fintype E] [DecidableEq ι] in
/-- A sign vector's translation stays in the strip when the waves have disjoint gradients. -/
lemma abs_signVector_grad_le (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (a : ι → V → ℝ) {W : ℝ} (hW0 : 0 ≤ W)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, D (a i) e = 0 ∨ D (a i') e = 0)
    (hW : ∀ i e, |D (a i) e| ≤ W) (n : ι → ℤ) (hn : ∀ i, n i ∈ signSet) (e : E) :
    |∑ i, (n i : ℝ) * D (a i) e| ≤ W := by
  by_cases h : ∃ i, D (a i) e ≠ 0
  · obtain ⟨i₀, hi₀⟩ := h
    rw [Finset.sum_eq_single i₀ (fun i _ hne => by
        rw [(hdisj i₀ i (Ne.symm hne) e).resolve_left hi₀, mul_zero])
      (fun h => absurd (Finset.mem_univ i₀) h), abs_mul]
    have hn₀ : |(n i₀ : ℝ)| ≤ 1 := by
      rcases mem_signSet.mp (hn i₀) with h | h | h <;> simp [h]
    calc |(n i₀ : ℝ)| * |D (a i₀) e| ≤ 1 * |D (a i₀) e| :=
          mul_le_mul_of_nonneg_right hn₀ (abs_nonneg _)
      _ ≤ W := by rw [one_mul]; exact hW i₀ e
  · push Not at h
    simp only [h, mul_zero, Finset.sum_const_zero, abs_zero]
    exact hW0

omit [Fintype V] [Fintype E] [DecidableEq ι] in
/-- The gradient of a sign vector's translation, `D (∑_i n_i a_i) = ∑_i n_i D a_i`. -/
lemma grad_signVector (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (a : ι → V → ℝ) (n : ι → ℤ) :
    D (fun j => ∑ i, (n i : ℝ) * a i j) = ∑ i, (n i : ℝ) • D (a i) := by
  have : (fun j => ∑ i, (n i : ℝ) * a i j) = ∑ i, (n i : ℝ) • a i := by
    funext j
    simp [Finset.sum_apply, smul_eq_mul]
  rw [this, map_sum]
  simp only [map_smul]

/-- `⟨∑_i n_i a_i, ∑_i n_i ϱ_i⟩ = ∑_i n_i² ⟨a_i, ϱ_i⟩` when `⟨a_i, ϱ_{i'}⟩ = 0` for `i ≠ i'`. -/
lemma pairing_signVector (a ϱ : ι → V → ℝ) (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (n : ι → ℤ) :
    ∑ j, (∑ i, (n i : ℝ) * a i j) * (∑ i, (n i : ℝ) * ϱ i j) =
      ∑ i, (n i : ℝ) ^ 2 * ∑ j, a i j * ϱ i j := by
  have h := Reduction.pairing_sum_sum_of_orthogonal (fun i => (n i : ℝ)) (fun i => (n i : ℝ)) a ϱ
    (fun i i' hne => by simpa [Multigraph.pairing] using horth i i' hne)
  simp only [Multigraph.pairing] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end SignVector

/-! ## The translated ensemble product -/

/-- **Generic translation step of KP Theorem 1.6 / FS81 Theorem 6.1.** For a law with character
translations (`CharacterTranslation`), neutral real densities `ϱ_i`, factors
`A_i + B_i cos(⟨φ, ϱ_i⟩ + s_i)`, and real spin waves `a_i` with `⟨a_i, ϱ_{i'}⟩ = 0`, pairwise
disjoint gradient supports and gradients in the strip,
`∫ ∏_i [A_i + B_i cos θ_i] dμ = ∫ ∏_i [A_i + B_i e^{-⟨a_i, ϱ_i⟩} ½(e^{iθ_i} R_{D a_i} + e^{-iθ_i} R_{-D a_i})] dμ`,
with `R` evaluated at the shifted real gradients `D φ + r`. -/
theorem integral_prod_add_mul_cos_translate (μ : Measure (V → ℝ)) [IsFiniteMeasure μ]
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (w : ℂ → ℂ) (r : E → ℝ) {W : ℝ} (hW0 : 0 ≤ W)
    (hμ : CharacterTranslation μ D w r W) (hw : ∀ t : ℝ, w t ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ) (hneutral : ∀ i, ∑ j, ϱ i j = 0)
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
    fun n hn => (hμ.integrable (τ n) (an n) (hτ0 n) (hstrip n hn)).const_mul _
  simp_rw [hleft, hright]
  rw [integral_finsetSum P fun n _ => (Reduction.integrable_gffCharacter μ (τ n)).const_mul _,
    integral_finsetSum P hint]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_const_mul, integral_const_mul,
    hμ.translate (τ n) (an n) (hτ0 n) (hstrip n hn), mul_assoc]

end FroehlichSpencer.BKT.Generic

end
