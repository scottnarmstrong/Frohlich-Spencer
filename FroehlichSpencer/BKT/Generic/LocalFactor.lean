/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Translation

/-!
# Normalized local factors and the translation energy (generic core)

Fix a translation cost `c : ℝ → ℝ`, the exponent of FS81 (4.10)(iii)
`|w(t + iu)/w(t)| ≤ e^{c(u)}`.

Normalizing every edge ratio by `e^{-c}` splits the translated factor
of `Generic/Translation.lean` into a scalar and a bounded function:

`e^{-⟨a, ϱ⟩} ½(e^{iθ} R_{Da} + e^{-iθ} R_{-Da}) = e^{-E_c(a, ϱ)} F`,

with the **translation energy** `E_c(a, ϱ) = ⟨a, ϱ⟩ - ∑_e c(D a(e))` (KP (2.12) when
`c(u) = βu²/2`; FS81 (4.41) when `c(u) = c(β)u²`) and the **local factor**
`F = ½(e^{iθ} P_{Da} + e^{-iθ} P_{-Da})`, `P_b = R_b e^{-∑ c(b)}` (FS81 (6.18)–(6.19);
`F = F₂ cos θ - F₁ sin θ` in FS81's notation, compare `Rotator.Contour.localF₁`, `localF₂`).

* `integral_prod_add_mul_cos_eq_localFactor`: the generic translation step in normalized form.
* `norm_localFactor_le_one`: `|F| ≤ 1` under the ratio bound (FS81 (6.21)).
* `localFactor_im_eq_zero`: `F` is real when `w` commutes with conjugation on the strip (FS81
  (4.11)).
* `localFactor_neg`: `F(-x, -θ) = F(x, θ)` when `w` is even on the strip (FS81 Theorem 6.1 (2)).
* `localFactor_zero`: without a wave, `F = cos θ`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex

variable {V E : Type*} [Fintype V] [Fintype E]

/-- KP (2.12) / FS81 (4.41): the translation energy `E_c(a, ϱ) = ⟨a, ϱ⟩ - ∑_e c(D a(e))`. -/
def translationEnergy (c : ℝ → ℝ) (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (a ϱ : V → ℝ) : ℝ :=
  ∑ j, a j * ϱ j - ∑ e, c (D a e)

/-- FS81 (6.19): the normalized edge ratio `P_b(x) = R_b(x) e^{-∑_e c(b_e)}`. -/
def normalizedEdgeRatio (w : ℂ → ℂ) (c : ℝ → ℝ) (b x : E → ℝ) : ℂ :=
  edgeRatio w b x * Complex.exp (-((∑ e, c (b e) : ℝ) : ℂ))

/-- FS81 (6.18): the local factor `F = ½(e^{iθ} P_b(x) + e^{-iθ} P_{-b}(x))`. -/
def localFactor (w : ℂ → ℂ) (c : ℝ → ℝ) (b x : E → ℝ) (θ : ℝ) : ℂ :=
  (Complex.exp (I * θ) * normalizedEdgeRatio w c b x +
    Complex.exp (-(I * θ)) * normalizedEdgeRatio w c (-b) x) / 2

omit [Fintype V] in
/-- An even cost gives the same normalization to `b` and `-b`. -/
lemma sum_cost_neg {c : ℝ → ℝ} (hc : ∀ u, c (-u) = c u) (b : E → ℝ) :
    ∑ e, c ((-b) e) = ∑ e, c (b e) :=
  Finset.sum_congr rfl fun e _ => by rw [Pi.neg_apply, hc]

/-- The translated factor of `integral_prod_add_mul_cos_translate` in normalized form:
`e^{-⟨a, ϱ⟩} ½(e^{iθ} R_{Da} + e^{-iθ} R_{-Da}) = e^{-E_c(a, ϱ)} F`. -/
theorem exp_mul_translatedCos (w : ℂ → ℂ) {c : ℝ → ℝ} (hc : ∀ u, c (-u) = c u)
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (a ϱ : V → ℝ) (x : E → ℝ) (θ : ℝ) :
    ((Real.exp (-∑ j, a j * ϱ j) : ℝ) : ℂ) * translatedCos w (D a) x θ =
      ((Real.exp (-translationEnergy c D a ϱ) : ℝ) : ℂ) * localFactor w c (D a) x θ := by
  unfold translatedCos localFactor normalizedEdgeRatio translationEnergy
  rw [sum_cost_neg hc]
  set S : ℝ := ∑ e, c (D a e)
  have h : ((Real.exp (-(∑ j, a j * ϱ j - S)) : ℝ) : ℂ) * Complex.exp (-(S : ℂ)) =
      ((Real.exp (-∑ j, a j * ϱ j) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← h]
  ring

omit [Fintype V] in
/-- FS81 (6.21): `|P_b(x)| ≤ 1` when every edge ratio is bounded by `e^{c}` and `|b| ≤ W`. -/
theorem norm_normalizedEdgeRatio_le_one {w : ℂ → ℂ} {c : ℝ → ℝ} {W : ℝ}
    (hratio : ∀ t u : ℝ, |u| ≤ W → ‖w ((t : ℂ) + (u : ℂ) * I) / w t‖ ≤ Real.exp (c u))
    (b x : E → ℝ) (hb : ∀ e, |b e| ≤ W) : ‖normalizedEdgeRatio w c b x‖ ≤ 1 := by
  unfold normalizedEdgeRatio edgeRatio
  rw [norm_mul, norm_prod, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  calc (∏ e, ‖w ((x e : ℂ) + (b e : ℂ) * I) / w (x e)‖) * Real.exp (-∑ e, c (b e))
      ≤ (∏ e, Real.exp (c (b e))) * Real.exp (-∑ e, c (b e)) :=
        mul_le_mul_of_nonneg_right
          (Finset.prod_le_prod₀ (fun e _ => norm_nonneg _) fun e _ => hratio _ _ (hb e))
          (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_sum, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

omit [Fintype V] in
/-- FS81 (6.21): `|F| ≤ 1` under the ratio bound, when `|b| ≤ W`. -/
theorem norm_localFactor_le_one {w : ℂ → ℂ} {c : ℝ → ℝ} {W : ℝ}
    (hratio : ∀ t u : ℝ, |u| ≤ W → ‖w ((t : ℂ) + (u : ℂ) * I) / w t‖ ≤ Real.exp (c u))
    (b x : E → ℝ) (hb : ∀ e, |b e| ≤ W) (θ : ℝ) : ‖localFactor w c b x θ‖ ≤ 1 := by
  have hb' : ∀ e, |(-b) e| ≤ W := fun e => by rw [Pi.neg_apply, abs_neg]; exact hb e
  have hexp : ∀ s : ℝ, ‖Complex.exp (I * s)‖ = 1 := fun s => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I s
  have hexp' : ∀ s : ℝ, ‖Complex.exp (-(I * s))‖ = 1 := fun s => by
    rw [← mul_neg, mul_comm, ← Complex.ofReal_neg]; exact Complex.norm_exp_ofReal_mul_I _
  unfold localFactor
  rw [norm_div, Complex.norm_two]
  calc ‖Complex.exp (I * θ) * normalizedEdgeRatio w c b x +
        Complex.exp (-(I * θ)) * normalizedEdgeRatio w c (-b) x‖ / 2
      ≤ (‖Complex.exp (I * θ) * normalizedEdgeRatio w c b x‖ +
          ‖Complex.exp (-(I * θ)) * normalizedEdgeRatio w c (-b) x‖) / 2 :=
        div_le_div_of_nonneg_right (norm_add_le _ _) zero_le_two
    _ ≤ (1 + 1) / 2 := by
        rw [norm_mul, norm_mul, hexp, hexp', one_mul, one_mul]
        gcongr
        · exact norm_normalizedEdgeRatio_le_one hratio b x hb
        · exact norm_normalizedEdgeRatio_le_one hratio (-b) x hb'
    _ = 1 := by norm_num

omit [Fintype V] in
/-- Conjugation turns `P_b` into `P_{-b}` when `w(z̄) = w(z)‾` on the strip `|Im z| ≤ W`, the cost
is even and `|b| ≤ W`. -/
lemma conj_normalizedEdgeRatio {w : ℂ → ℂ} {c : ℝ → ℝ} {W : ℝ}
    (hconj : ∀ z : ℂ, |z.im| ≤ W → (starRingEnd ℂ) (w z) = w ((starRingEnd ℂ) z))
    (hc : ∀ u, c (-u) = c u) (b x : E → ℝ) (hb : ∀ e, |b e| ≤ W) :
    (starRingEnd ℂ) (normalizedEdgeRatio w c b x) = normalizedEdgeRatio w c (-b) x := by
  unfold normalizedEdgeRatio edgeRatio
  rw [map_mul, map_prod, sum_cost_neg hc, ← Complex.exp_conj, map_neg, Complex.conj_ofReal]
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  have h0 : 0 ≤ W := (abs_nonneg _).trans (hb e)
  rw [map_div₀, hconj _ (by simpa using hb e), hconj _ (by simpa using h0)]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.neg_apply,
    Complex.ofReal_neg]
  congr 2
  ring

omit [Fintype V] in
/-- FS81 (4.11): the local factor is real when `w(z̄) = w(z)‾` on the strip, the cost is even and
`|b| ≤ W`. -/
theorem localFactor_im_eq_zero {w : ℂ → ℂ} {c : ℝ → ℝ} {W : ℝ}
    (hconj : ∀ z : ℂ, |z.im| ≤ W → (starRingEnd ℂ) (w z) = w ((starRingEnd ℂ) z))
    (hc : ∀ u, c (-u) = c u) (b x : E → ℝ) (hb : ∀ e, |b e| ≤ W) (θ : ℝ) :
    (localFactor w c b x θ).im = 0 := by
  have hb' : ∀ e, |(-b) e| ≤ W := fun e => by rw [Pi.neg_apply, abs_neg]; exact hb e
  rw [← Complex.conj_eq_iff_im]
  unfold localFactor
  rw [map_div₀, map_add, map_mul, map_mul, conj_normalizedEdgeRatio hconj hc b x hb,
    conj_normalizedEdgeRatio hconj hc (-b) x hb', neg_neg, ← Complex.exp_conj, ← Complex.exp_conj, map_neg,
    map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring_nf

omit [Fintype V] in
/-- Evenness of `w` on the strip turns `P_b(-x)` into `P_{-b}(x)`, when `|b| ≤ W`. -/
lemma normalizedEdgeRatio_neg {w : ℂ → ℂ} {c : ℝ → ℝ} {W : ℝ}
    (heven : ∀ z : ℂ, |z.im| ≤ W → w (-z) = w z) (hc : ∀ u, c (-u) = c u) (b x : E → ℝ)
    (hb : ∀ e, |b e| ≤ W) :
    normalizedEdgeRatio w c b (-x) = normalizedEdgeRatio w c (-b) x := by
  unfold normalizedEdgeRatio edgeRatio
  rw [sum_cost_neg hc]
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  have h0 : 0 ≤ W := (abs_nonneg _).trans (hb e)
  have h1 : w (((-x) e : ℝ) : ℂ) = w ((x e : ℝ) : ℂ) := by
    rw [Pi.neg_apply, Complex.ofReal_neg, heven _ (by simpa using h0)]
  have h2 : w (((-x) e : ℝ) + ((b e : ℝ) : ℂ) * I) = w ((x e : ℂ) + (((-b) e : ℝ) : ℂ) * I) := by
    rw [← heven _ (by simpa using hb e)]
    congr 1
    simp only [Pi.neg_apply, Complex.ofReal_neg]
    ring
  rw [h1, h2]

omit [Fintype V] in
/-- FS81 Theorem 6.1 (2): `F(-x, -θ) = F(x, θ)` when `w` is even on the strip, the cost is even
and `|b| ≤ W`. -/
theorem localFactor_neg {w : ℂ → ℂ} {c : ℝ → ℝ} {W : ℝ}
    (heven : ∀ z : ℂ, |z.im| ≤ W → w (-z) = w z) (hc : ∀ u, c (-u) = c u) (b x : E → ℝ)
    (hb : ∀ e, |b e| ≤ W) (θ : ℝ) :
    localFactor w c b (-x) (-θ) = localFactor w c b x θ := by
  have hb' : ∀ e, |(-b) e| ≤ W := fun e => by rw [Pi.neg_apply, abs_neg]; exact hb e
  unfold localFactor
  rw [normalizedEdgeRatio_neg heven hc b x hb, normalizedEdgeRatio_neg heven hc (-b) x hb',
    neg_neg]
  push_cast
  ring_nf

omit [Fintype V] in
/-- Without a wave the local factor is the cosine: `F = cos θ` for `b = 0`, when `c(0) = 0`. -/
theorem localFactor_zero {w : ℂ → ℂ} {c : ℝ → ℝ} (hc0 : c 0 = 0) (x : E → ℝ)
    (hw : ∀ e, w (x e) ≠ 0) (θ : ℝ) : localFactor w c 0 x θ = Real.cos θ := by
  have h : normalizedEdgeRatio w c 0 x = 1 := by
    unfold normalizedEdgeRatio
    simp only [edgeRatio_zero w x hw, Pi.zero_apply, hc0, Finset.sum_const_zero,
      Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one]
  unfold localFactor
  rw [neg_zero, h, Complex.ofReal_cos, Complex.cos, mul_one, mul_one]
  ring_nf

/-- **Generic translation step, normalized** (KP §2.3.3; FS81 Theorem 6.1, (6.18)): under the
hypotheses of `integral_prod_add_mul_cos_translate` and an even cost `c`,
`∫ ∏_i [A_i + B_i cos θ_i] dμ = ∫ ∏_i [A_i + B_i e^{-E_c(a_i, ϱ_i)} F_i] dμ`, with
`F_i = localFactor w c (D a_i) (D φ + r) θ_i`. -/
theorem integral_prod_add_mul_cos_eq_localFactor (μ : Measure (V → ℝ)) [IsFiniteMeasure μ]
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (w : ℂ → ℂ) (c : ℝ → ℝ) (hc : ∀ u, c (-u) = c u)
    (r : E → ℝ) {W : ℝ} (hW0 : 0 ≤ W) (hμ : CharacterTranslation μ D w r W)
    (hw : ∀ t : ℝ, w t ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (hneutral : ∀ i, ∑ j, ϱ i j = 0) (A B s : ι → ℝ) (a : ι → V → ℝ)
    (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, D (a i) e = 0 ∨ D (a i') e = 0)
    (hW : ∀ i e, |D (a i) e| ≤ W) :
    ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) ∂μ =
      ∫ φ, ∏ i, ((A i : ℂ) + ((B i * Real.exp (-translationEnergy c D (a i) (ϱ i)) : ℝ) : ℂ) *
        localFactor w c (D (a i)) (D φ + r) (∑ j, φ j * ϱ i j + s i)) ∂μ := by
  rw [integral_prod_add_mul_cos_translate μ D w r hW0 hμ hw ϱ hneutral A B s a horth hdisj hW]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, mul_assoc, mul_assoc,
    exp_mul_translatedCos w hc D (a i) (ϱ i)]

end FroehlichSpencer.BKT.Generic

end
