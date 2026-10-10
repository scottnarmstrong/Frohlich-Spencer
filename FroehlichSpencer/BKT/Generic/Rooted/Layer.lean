/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.Offset

/-!
# The rooted (restricted-domain) charge layer

On the pinned carrier of FS81 (1.35), read on the augmented graph
`squareZero L` rooted at its wired vertex, the observable is the root-relative comb
`∏_x λ_x(ψ_x − ψ_root)`, and the terminal decomposition's `RootedLayerObstruction` shows that a nonconstant one-site
cosine product has no all-neutral character expansion on unrestricted fields.

This module states that interface and the translation consequences that do not depend on
the expansion domain.

A `RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁` consists of
* a finite convex expansion `∏_j λ_j(ψ_j) = ∑_i c_i ∏_{ϱ ∈ 𝒩_i} [1 + K_i(ϱ) cos⟨ψ, ϱ⟩]` for every
  `ψ` with `ψ root = 0` (`expand`), all densities neutral (`neutral`);
* the entropy bound `|K_i(ϱ)| ≤ e^{D₂ A(ϱ)} Z(ϱ)` (`entropy`);
* for every density, graded spin-wave data with the spin-wave clauses (`HasLayerWave`) whose pieces have
  their gradients on the edge set `S_i(ϱ)` (`wave`): the locality that replaces KP's square-domain
  volume bound, which fails on the wired carrier (its root has degree `4L`).

`RootedChargeLayer.IsLocal` records the remaining geometric clauses consumed by the moment bound
(`Generic/Rooted/Moment.lean`): a size `dsc(ϱ) ≥ 1` with `|S_i(ϱ)| ≤ Kv (dsc + 1)²`, an
integer routing of `ϱ` inside `S_i(ϱ)` with coefficients at most `∑|ϱ|`, bounded same-band overlap
of the sets `S_i(ϱ)`, and the cover bound `log₂(dsc + 1) ≤ A(ϱ)` (KP P2.1, first half).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic.SpinWave

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- **The rooted charge layer**: the restricted-domain variant of `ChargeLayer`. -/
structure RootedChargeLayer (G : Multigraph V E) (root : V) (lam : V → ℝ → ℝ)
    (centerOf : (V → ℤ) → V) (A Zent : (V → ℤ) → ℝ) (D₁ D₂ α K₀ K₁ : ℝ) where
  n : ℕ
  N : Fin n → Finset (V → ℤ)
  c : Fin n → ℝ
  K : Fin n → (V → ℤ) → ℝ
  S : Fin n → (V → ℤ) → Finset E
  c_pos : ∀ i, 0 < c i
  c_sum : ∑ i, c i = 1
  neutral : ∀ i, ∀ ϱ ∈ N i, ∑ j, ϱ j = 0
  expand : ∀ ψ : V → ℝ, ψ root = 0 →
    ∏ j, lam j (ψ j) = ∑ i, c i * ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, ψ j * (ϱ j : ℝ)))
  entropy : ∀ i, ∀ ϱ ∈ N i, |K i ϱ| ≤ Real.exp (D₂ * A ϱ) * Zent ϱ
  wave : ∀ i, ∀ ϱ ∈ N i, ∃ Wv : GradedSpinWave.{0, 0, 0} G (N i) centerOf ϱ,
    HasLayerWave G (N i) centerOf A D₁ α K₀ K₁ ϱ Wv ∧
      ∀ t e, G.grad (Wv.piece t) e ≠ 0 → e ∈ S i ϱ

variable {G : Multigraph V E} {root : V} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- The geometric clauses of a rooted layer consumed by the moment bound: sizes, local edge
counts, local integer routing, bounded same-band overlap, and the cover bound. -/
structure RootedChargeLayer.IsLocal
    (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (dsc : (V → ℤ) → ℕ) (Kv : ℝ) (Kov : ℕ) : Prop where
  ne_zero : ∀ i, ∀ ϱ ∈ CL.N i, ϱ ≠ 0
  one_le_dsc : ∀ i, ∀ ϱ ∈ CL.N i, 1 ≤ dsc ϱ
  card_le : ∀ i, ∀ ϱ ∈ CL.N i, ((CL.S i ϱ).card : ℝ) ≤ Kv * ((dsc ϱ : ℝ) + 1) ^ 2
  route : ∀ i, ∀ ϱ ∈ CL.N i, ∃ r : E → ℤ, (∀ e, r e ≠ 0 → e ∈ CL.S i ϱ) ∧
    (∀ e, |(r e : ℝ)| ≤ ∑ j, |(ϱ j : ℝ)|) ∧
    ∀ σ : V → ℝ, ∑ j, σ j * (ϱ j : ℝ) = ∑ e, (r e : ℝ) * G.grad σ e
  overlap : ∀ i (k : ℕ) (e : E) (T : Finset (V → ℤ)), T ⊆ CL.N i →
    (∀ ρ ∈ T, 2 ^ k - 1 ≤ dsc ρ ∧ dsc ρ ≤ 2 ^ (k + 1) - 2 ∧ e ∈ CL.S i ρ) → T.card ≤ Kov
  cover : ∀ i, ∀ ϱ ∈ CL.N i, Real.logb 2 (dsc ϱ + 1) ≤ A ϱ

/-! ## Waves, gain and activities -/

/-- The assembled spin wave of a density of a rooted layer (as `layerSpinWave`). -/
def rootedSpinWave (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) (ϱ : V → ℤ) : V → ℝ :=
  if h : ϱ ∈ CL.N i then envelopeWave (Classical.choose (CL.wave i ϱ h)) κ amp k₀ else 0

/-- The renormalized activity `z = K e^{−E_c(a, ϱ)}` of a rooted layer. -/
def rootedActivity (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (c : ℝ → ℝ) (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) (ϱ : V → ℤ) : ℝ :=
  CL.K i ϱ * Real.exp (-translationEnergy c (gradLinear G) (rootedSpinWave CL κ amp k₀ i ϱ)
    fun j => (ϱ j : ℝ))

/-- **The gain** `E_c(a_ϱ, ϱ) ≥ (λ/8) ∑_j |ϱ(j)| + λ/(8 D₁) A(ϱ)` (as `layer_gain`). -/
theorem rooted_gain (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) :
    amp / 8 * ∑ j, |(ϱ j : ℝ)| + amp / (8 * D₁) * A ϱ ≤
      translationEnergy c (gradLinear G) (rootedSpinWave CL κ amp k₀ i ϱ)
        fun j => (ϱ j : ℝ) := by
  classical
  set Wv := Classical.choose (CL.wave i ϱ hϱ) with hWv
  obtain ⟨⟨hα, hK0, hK1, hbase, hedge, hcover, -⟩, -⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
  let _ := Wv.finite
  have hwave : rootedSpinWave CL κ amp k₀ i ϱ = envelopeWave Wv κ amp k₀ := by
    simp only [rootedSpinWave, dite_eq_left hϱ, hWv]
  rw [hwave]
  have hα1 : 1 < α := by rw [← hα]; exact Wv.alpha_gt_one
  have hγ : 0 ≤ gradExponent α := (gradExponent_pos hα1).le
  have hcount : ∀ t, Wv.scale t < k₀ →
      ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤ 100 * 4 ^ k₀ := by
    intro t ht
    refine (hedge t).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact pow_le_pow_right₀ (by norm_num) ht.le
  have hquad : ∀ s, k₀ ≤ s →
      amp ≤ quadAmplitude κ Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) s := by
    intro s hs
    rw [hK0, hK1, hα]
    refine le_min hquad₁ (hquad₂.trans ?_)
    refine div_le_div_of_nonneg_right ?_ hK₁.le
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hγ
  have hK₀' : 0 < Wv.K₀ := by rw [hK0]; exact hK₀
  have hK₁' : 0 < Wv.K₁ := by rw [hK1]; exact hK₁
  have hampW' : amp * Wv.K₁ ≤ W := by rw [hK1]; exact hampW
  have hexp' : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * Wv.K₁) ≤ amp / 2 := by
    rw [hK1]; exact hexp
  have hgain := translationEnergy_envelopeWave_ge_gain Wv hc hκ hK₀' hK₁' hamp hampW' hk₀ hcount
    hexp' hquad
  refine le_trans ?_ hgain
  set X : ℝ := ∑ j, |(ϱ j : ℝ)|
  set S : ℝ := ((Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℝ)
  set Q : ℝ := ∑ t ∈ Finset.univ.filter (fun t => Wv.scale t = 0), |Wv.charge t|
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have hcov : A ϱ / D₁ ≤ X + S := by rw [div_le_iff₀ hD₁]; linarith [hcover]
  have h1 : amp / (8 * D₁) * A ϱ ≤ amp / 8 * (X + S) := by
    rw [show amp / (8 * D₁) * A ϱ = amp / 8 * (A ϱ / D₁) by field_simp]
    exact mul_le_mul_of_nonneg_left hcov (by positivity)
  have h2 : (1 / 2 : ℝ) * X ≤ Q := hbase
  nlinarith

/-- The P2.4 clauses of the assembled waves (as `layerSpinWave_clauses`). -/
theorem rootedSpinWave_clauses (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) :
    (∀ ϱ ∈ CL.N i, ∀ ϱ' ∈ G.comparableDensities (CL.N i) ϱ,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ' (centerOf ϱ'), rootedSpinWave CL κ amp k₀ i ϱ j = c) ∧
    (∀ ϱ ∈ CL.N i, Function.support (rootedSpinWave CL κ amp k₀ i ϱ) ⊆
      G.densityDomain ϱ (centerOf ϱ)) ∧
    ∀ ϱ ∈ CL.N i, ∀ ϱ' ∈ CL.N i, ϱ ≠ ϱ' →
      ∑ j, rootedSpinWave CL κ amp k₀ i ϱ j * (ϱ' j : ℝ) = 0 := by
  classical
  refine ⟨fun ϱ hϱ => ?_, fun ϱ hϱ => ?_, fun ϱ hϱ ϱ' hϱ' hne => ?_⟩
  · simp only [rootedSpinWave, dite_eq_left hϱ]
    exact envelopeWave_const_plus _ κ amp k₀
  · simp only [rootedSpinWave, dite_eq_left hϱ]
    exact envelopeWave_support_subset _ κ amp k₀
  · simp only [rootedSpinWave, dite_eq_left hϱ]
    set Wv := Classical.choose (CL.wave i ϱ hϱ)
    obtain ⟨⟨-, -, -, -, -, -, horth⟩, -⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
    let _ := Wv.finite
    simp only [envelopeWave, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [horth t ϱ' hϱ' (Ne.symm hne), mul_zero]

/-- An envelope wave has zero gradient on an edge where every piece has zero gradient. -/
theorem grad_envelopeWave_eq_zero {N₀ : Finset (V → ℤ)} {ρ : V → ℤ}
    (Wv : GradedSpinWave.{0, 0, 0} G N₀ centerOf ρ) (κ amp : ℝ) (k₀ : ℕ) {e : E}
    (hpiece : ∀ t, G.grad (Wv.piece t) e = 0) : G.grad (envelopeWave Wv κ amp k₀) e = 0 := by
  let _ := Wv.finite
  simp only [envelopeWave, Multigraph.grad]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun t _ => ?_
  have h := hpiece t
  simp only [Multigraph.grad] at h
  rw [← mul_sub, h, mul_zero]

/-- The gradient of an assembled wave lives on the local edge set `S_i(ϱ)`. -/
theorem grad_rootedSpinWave_mem (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) (e : E)
    (he : G.grad (rootedSpinWave CL κ amp k₀ i ϱ) e ≠ 0) : e ∈ CL.S i ϱ := by
  by_contra hS
  apply he
  obtain ⟨-, hloc⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
  simp only [rootedSpinWave, dite_eq_left hϱ]
  exact grad_envelopeWave_eq_zero _ κ amp k₀ fun t => by
    by_contra h
    exact hS (hloc t e h)

/-- The assembled waves have gradients at most `max(λK₁, 1)`. -/
theorem abs_grad_rootedSpinWave_le
    (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {κ : ℝ} (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) {amp : ℝ} (hamp : 0 ≤ amp) (k₀ : ℕ)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) (e : E) :
    |G.grad (rootedSpinWave CL κ amp k₀ i ϱ) e| ≤ max (amp * K₁) 1 := by
  classical
  obtain ⟨⟨-, hK0, hK1, -⟩, -⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
  simp only [rootedSpinWave, dite_eq_left hϱ]
  refine (abs_grad_envelopeWave_le _ hκ (by rw [hK0]; exact hK₀) (by rw [hK1]; exact hK₁)
    hamp k₀ e).trans ?_
  rw [hK1]

/-- **Decay of the renormalized activities**: with an exponential entropy bound and any
`0 ≤ ℓ ≤ A(ϱ)`, `|z_ϱ| ≤ e^{−b (∑|ϱ| + ℓ)}` for every `0 ≤ b ≤ λ/8 − a₁`,
`b ≤ λ/(8D₁) − D₂ − a₂`. -/
theorem abs_rootedActivity_le (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    {a₁ a₂ b : ℝ} (hZ : ∀ ϱ : V → ℤ, Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ))
    (hb0 : 0 ≤ b) (hb₁ : b ≤ amp / 8 - a₁) (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ A ϱ) :
    |rootedActivity CL c κ amp k₀ i ϱ| ≤ Real.exp (-b * (∑ j, |(ϱ j : ℝ)| + ℓ)) := by
  have hgain := rooted_gain CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂ i ϱ hϱ
  have hK := CL.entropy i ϱ hϱ
  have hZϱ := hZ ϱ
  set X : ℝ := ∑ j, |(ϱ j : ℝ)|
  set E' := translationEnergy c (gradLinear G) (rootedSpinWave CL κ amp k₀ i ϱ)
    fun j => (ϱ j : ℝ)
  have hA0 : 0 ≤ A ϱ := hℓ0.trans hℓ
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold rootedActivity
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |CL.K i ϱ| * Real.exp (-E')
      ≤ (Real.exp (D₂ * A ϱ) * Real.exp (a₁ * X + a₂ * A ϱ)) * Real.exp (-E') :=
        mul_le_mul_of_nonneg_right (hK.trans (mul_le_mul_of_nonneg_left hZϱ
          (Real.exp_pos _).le)) (Real.exp_pos _).le
    _ = Real.exp (D₂ * A ϱ + (a₁ * X + a₂ * A ϱ) - E') := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-b * (X + A ϱ)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : b * X ≤ (amp / 8 - a₁) * X := mul_le_mul_of_nonneg_right hb₁ hX0
        have h2 : b * A ϱ ≤ (amp / (8 * D₁) - D₂ - a₂) * A ϱ :=
          mul_le_mul_of_nonneg_right hb₂ hA0
        nlinarith
    _ ≤ Real.exp (-b * (X + ℓ)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith

/-! ## The renormalization identity for the root-relative observable -/

omit [Fintype E] [DecidableEq V] in
lemma atMostOneNonNeutral_of_neutral {N : Finset (V → ℤ)} (h : ∀ ϱ ∈ N, ∑ j, ϱ j = 0) :
    AtMostOneNonNeutral N :=
  fun ϱ₁ h₁ _ _ hne _ => absurd (h ϱ₁ h₁) hne

omit [Fintype E] [DecidableEq V] in
/-- A neutral density does not see a constant shift of the field. -/
lemma sum_sub_const_mul_eq {ϱ : V → ℤ} (hϱ : ∑ j, ϱ j = 0) (ψ : V → ℝ) (s : ℝ) :
    ∑ j, (ψ j - s) * (ϱ j : ℝ) = ∑ j, ψ j * (ϱ j : ℝ) := by
  have h : ∑ j, (ϱ j : ℝ) = 0 := by exact_mod_cast hϱ
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h, mul_zero, sub_zero]

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- **The T1.6-NG identity for the root-relative observable** under any rooted translation law. -/
theorem rooted_identity_of_law (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] (r : E → ℝ)
    (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hw : IsStripWeight w W c) (hμ : IsRootedTranslationLaw μ G w r W) {κ : ℝ} (hκ : 0 < κ)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W)
    (hW1 : 1 ≤ W) (k₀ : ℕ) (σ : V → ℝ) :
    ∫ φ, ((∏ j, lam j (φ j + σ j - (φ root + σ root)) : ℝ) : ℂ) ∂μ =
      ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.N i, ((1 : ℂ) +
        ((rootedActivity CL c κ amp k₀ i ϱ : ℝ) : ℂ) *
        localFactor w c (gradLinear G (rootedSpinWave CL κ amp k₀ i ϱ)) (gradLinear G φ + r)
          (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂μ := by
  classical
  have hgrad : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, |G.grad (rootedSpinWave CL κ amp k₀ i ϱ) e| ≤ W :=
    fun i ϱ hϱ e => (abs_grad_rootedSpinWave_le CL hκ hK₀ hK₁ hamp k₀ i ϱ hϱ e).trans
      (max_le hampW hW1)
  have hpt : ∀ φ : V → ℝ, ((∏ j, lam j (φ j + σ j - (φ root + σ root)) : ℝ) : ℂ) =
      ∑ i, (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
        (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ) := by
    intro φ
    have hexp := CL.expand (fun j => φ j + σ j - (φ root + σ root)) (sub_self _)
    beta_reduce at hexp
    rw [hexp, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_mul]
    congr 2
    refine Finset.prod_congr rfl fun ϱ hϱ => ?_
    have hs := sum_sub_const_mul_eq (CL.neutral i ϱ hϱ) (fun j => φ j + σ j) (φ root + σ root)
    beta_reduce at hs
    rw [hs]
  have hint : ∀ i, Integrable (fun φ : V → ℝ => (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
      (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)) μ := by
    intro i
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound ?_ (∏ ϱ ∈ CL.N i, (1 + |CL.K i ϱ|))
      (Filter.Eventually.of_forall fun φ => norm_prod_one_add_mul_cos_le _ _ _)
    refine (Complex.continuous_ofReal.comp
      (continuous_finsetProd _ fun ϱ _ => ?_)).aestronglyMeasurable
    fun_prop
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  congr 1
  have hP := FroehlichSpencer.BKT.neutralPart_eq_self (CL.neutral i)
  obtain ⟨hconst, hsupp, horth⟩ := rootedSpinWave_clauses CL κ amp k₀ i
  rw [← hP] at hconst hsupp horth
  have key := integral_ensemble_eq_of_law G μ hw r hμ (CL.N i)
    (atMostOneNonNeutral_of_neutral (CL.neutral i)) (CL.K i) σ centerOf
    (rootedSpinWave CL κ amp k₀ i) hconst hsupp horth
    (fun ϱ hϱ e => hgrad i ϱ (by rw [← hP]; exact hϱ) e)
  rw [key, hP]
  rfl

end FroehlichSpencer.BKT.Generic

end
