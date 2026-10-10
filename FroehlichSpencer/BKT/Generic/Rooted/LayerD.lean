/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Rooted.Layer

/-!
# The rooted charge layer with direct cross-density clauses

The translation translation step uses the spin-wave construction
graph-ball clauses of the spin waves (`GradedSpinWave.const_plus`, `supp` relative to the ensemble)
only to derive **cross-density gradient disjointness** (`grad_disjoint_of_spinWave_clauses`); gradient disjointness's
`integral_prod_add_mul_cos_eq_localFactor` needs only disjointness, orthogonality and `|∇a| ≤ W`.

On the wired carrier `squareZero L` the graph balls around boundary densities contain the wired
vertex and its whole neighbourhood, which makes the graph-ball clauses unnatural and, for two
boundary clusters under KP's center convention, unsatisfiable (`Generic/Wired/Obstructions.lean`,
boundary geometry).

`RootedChargeLayerD` therefore

* stores the waves as data, `wv i ϱ : GradedSpinWave G ∅ centerOf ϱ` (no cross-density constancy:
  `comparableDensities ∅ ϱ = ∅`), with the single-density translation clauses `HasLayerWave … ∅ …`;
* states the cross-density facts directly: orthogonality `⟨piece, ϱ′⟩ = 0` and gradient
  disjointness of the pieces of distinct densities;
* keeps the locality sets `S` of `RootedChargeLayer`.

`RootedChargeLayer.toD` shows that every the rooted charge layer `RootedChargeLayer` is a `RootedChargeLayerD` (the
disjointness follows from the graph-ball clauses), and `RootedChargeLayer.IsLocal.toD` transfers
the local geometry; so the D-form is a strict weakening of the rooted charge layer interface.

The translation consequences
(`rootedSpinWaveD`, `rootedD_gain`, `rootedActivityD`, …) and the identity for the root-relative
observable under any `CharacterTranslation` law (`rootedD_identity_of_law`) follow as for
`RootedChargeLayer`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic.SpinWave

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- **The rooted charge layer with direct cross-density clauses.** -/
structure RootedChargeLayerD (G : Multigraph V E) (root : V) (lam : V → ℝ → ℝ)
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
  wv : ∀ i, ∀ ϱ ∈ N i, GradedSpinWave.{0, 0, 0} G ∅ centerOf ϱ
  layer : ∀ i ϱ (h : ϱ ∈ N i), HasLayerWave G ∅ centerOf A D₁ α K₀ K₁ ϱ (wv i ϱ h)
  wv_local : ∀ i ϱ (h : ϱ ∈ N i) t e, G.grad ((wv i ϱ h).piece t) e ≠ 0 → e ∈ S i ϱ
  wv_orth : ∀ i ϱ (h : ϱ ∈ N i) t, ∀ ϱ' ∈ N i, ϱ' ≠ ϱ →
    ∑ j, (wv i ϱ h).piece t j * (ϱ' j : ℝ) = 0
  wv_disj : ∀ i ϱ (h : ϱ ∈ N i) ϱ' (h' : ϱ' ∈ N i), ϱ ≠ ϱ' → ∀ t t' e,
    G.grad ((wv i ϱ h).piece t) e = 0 ∨ G.grad ((wv i ϱ' h').piece t') e = 0

variable {G : Multigraph V E} {root : V} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- The local geometry of a `RootedChargeLayerD` (as `RootedChargeLayer.IsLocal`). -/
structure RootedChargeLayerD.IsLocal
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
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

/-! ## From the rooted charge layer interface -/

/-- Forget the cross-density constancy of a graded spin wave. -/
def SpinWave.GradedSpinWave.forget {N₀ : Finset (V → ℤ)} {ρ : V → ℤ}
    (Wv : GradedSpinWave.{0, 0, 0} G N₀ centerOf ρ) : GradedSpinWave.{0, 0, 0} G ∅ centerOf ρ :=
  { Wv with
    const_plus := fun t ρ' hρ' => by
      simp [Multigraph.comparableDensities] at hρ' }

theorem HasLayerWave.forget {N₀ : Finset (V → ℤ)} {ρ : V → ℤ}
    {Wv : GradedSpinWave.{0, 0, 0} G N₀ centerOf ρ}
    (h : HasLayerWave G N₀ centerOf A D₁ α K₀ K₁ ρ Wv) :
    HasLayerWave G ∅ centerOf A D₁ α K₀ K₁ ρ Wv.forget := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun _ _ h => absurd h (Finset.notMem_empty _)⟩

/-- Two pieces of the waves of distinct densities of one translation ensemble have disjoint gradients
(gradient disjointness's `grad_disjoint_of_spinWave_clauses`, applied to the single pieces). -/
theorem grad_piece_disjoint_of_clauses {N₀ : Finset (V → ℤ)} {ϱ ϱ' : V → ℤ} (hϱ : ϱ ∈ N₀)
    (hϱ' : ϱ' ∈ N₀) (hne : ϱ ≠ ϱ') (Wv : GradedSpinWave.{0, 0, 0} G N₀ centerOf ϱ)
    (Wv' : GradedSpinWave.{0, 0, 0} G N₀ centerOf ϱ') (t : Wv.ι) (t' : Wv'.ι) (e : E) :
    G.grad (Wv.piece t) e = 0 ∨ G.grad (Wv'.piece t') e = 0 := by
  classical
  set a : (V → ℤ) → V → ℝ := fun ρ =>
    if ρ = ϱ then Wv.piece t else if ρ = ϱ' then Wv'.piece t' else 0 with ha
  have haϱ : a ϱ = Wv.piece t := by simp [ha]
  have haϱ' : a ϱ' = Wv'.piece t' := by simp [ha, Ne.symm hne]
  have h := grad_disjoint_of_spinWave_clauses (G := G) N₀ centerOf a ?_ ?_ ϱ hϱ ϱ' hϱ' hne e
  · rwa [haϱ, haϱ'] at h
  · intro ρ _ ρ'' hρ''
    by_cases h1 : ρ = ϱ
    · subst h1
      rw [haϱ]
      exact Wv.const_plus t ρ'' hρ''
    · by_cases h2 : ρ = ϱ'
      · subst h2
        rw [haϱ']
        exact Wv'.const_plus t' ρ'' hρ''
      · exact ⟨0, fun j _ => by simp [ha, h1, h2]⟩
  · intro ρ _
    by_cases h1 : ρ = ϱ
    · subst h1
      rw [haϱ]
      exact Wv.supp t
    · by_cases h2 : ρ = ϱ'
      · subst h2
        rw [haϱ']
        exact Wv'.supp t'
      · intro j hj
        simp [ha, h1, h2] at hj

/-- **Every the rooted charge layer rooted layer is a `RootedChargeLayerD`.** -/
def RootedChargeLayer.toD (CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁) :
    RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁ where
  n := CL.n
  N := CL.N
  c := CL.c
  K := CL.K
  S := CL.S
  c_pos := CL.c_pos
  c_sum := CL.c_sum
  neutral := CL.neutral
  expand := CL.expand
  entropy := CL.entropy
  wv i ϱ h := (Classical.choose (CL.wave i ϱ h)).forget
  layer i ϱ h := (Classical.choose_spec (CL.wave i ϱ h)).1.forget
  wv_local i ϱ h := (Classical.choose_spec (CL.wave i ϱ h)).2
  wv_orth i ϱ h t ϱ' h' hne :=
    (Classical.choose_spec (CL.wave i ϱ h)).1.2.2.2.2.2.2 t ϱ' h' hne
  wv_disj i ϱ h ϱ' h' hne t t' e :=
    grad_piece_disjoint_of_clauses h h' hne (Classical.choose (CL.wave i ϱ h))
      (Classical.choose (CL.wave i ϱ' h')) t t' e

theorem RootedChargeLayer.IsLocal.toD
    {CL : RootedChargeLayer G root lam centerOf A Zent D₁ D₂ α K₀ K₁} {dsc : (V → ℤ) → ℕ}
    {Kv : ℝ} {Kov : ℕ} (h : CL.IsLocal dsc Kv Kov) : CL.toD.IsLocal dsc Kv Kov :=
  ⟨h.ne_zero, h.one_le_dsc, h.card_le, h.route, h.overlap, h.cover⟩

/-! ## Waves, gain and activities -/

/-- The assembled spin wave of a density of a `RootedChargeLayerD`. -/
def rootedSpinWaveD (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) (ϱ : V → ℤ) : V → ℝ :=
  if h : ϱ ∈ CL.N i then envelopeWave (CL.wv i ϱ h) κ amp k₀ else 0

/-- Its renormalized activity `z = K e^{−E_c(a, ϱ)}`. -/
def rootedActivityD (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (c : ℝ → ℝ) (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) (ϱ : V → ℤ) : ℝ :=
  CL.K i ϱ * Real.exp (-translationEnergy c (gradLinear G) (rootedSpinWaveD CL κ amp k₀ i ϱ)
    fun j => (ϱ j : ℝ))

/-- **The gain** (as `rooted_gain`). -/
theorem rootedD_gain (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) :
    amp / 8 * ∑ j, |(ϱ j : ℝ)| + amp / (8 * D₁) * A ϱ ≤
      translationEnergy c (gradLinear G) (rootedSpinWaveD CL κ amp k₀ i ϱ)
        fun j => (ϱ j : ℝ) := by
  classical
  set Wv := CL.wv i ϱ hϱ with hWv
  obtain ⟨hα, hK0, hK1, hbase, hedge, hcover, -⟩ := CL.layer i ϱ hϱ
  let _ := Wv.finite
  have hwave : rootedSpinWaveD CL κ amp k₀ i ϱ = envelopeWave Wv κ amp k₀ := by
    simp only [rootedSpinWaveD, dite_eq_left hϱ, hWv]
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

/-- The gradient of an assembled wave lives on `S_i(ϱ)`. -/
theorem grad_rootedSpinWaveD_mem
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) (e : E)
    (he : G.grad (rootedSpinWaveD CL κ amp k₀ i ϱ) e ≠ 0) : e ∈ CL.S i ϱ := by
  by_contra hS
  apply he
  simp only [rootedSpinWaveD, dite_eq_left hϱ]
  exact grad_envelopeWave_eq_zero _ κ amp k₀ fun t => by
    by_contra h
    exact hS (CL.wv_local i ϱ hϱ t e h)

/-- Assembled waves of distinct densities have disjoint gradients. -/
theorem grad_rootedSpinWaveD_disjoint
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) {ϱ ϱ' : V → ℤ} (hϱ : ϱ ∈ CL.N i) (hϱ' : ϱ' ∈ CL.N i)
    (hne : ϱ ≠ ϱ') (e : E) :
    G.grad (rootedSpinWaveD CL κ amp k₀ i ϱ) e = 0 ∨
      G.grad (rootedSpinWaveD CL κ amp k₀ i ϱ') e = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  simp only [rootedSpinWaveD, dite_eq_left hϱ, dite_eq_left hϱ'] at h1 h2
  have ht : ∃ t, G.grad ((CL.wv i ϱ hϱ).piece t) e ≠ 0 := by
    by_contra h
    push Not at h
    exact h1 (grad_envelopeWave_eq_zero _ κ amp k₀ h)
  have ht' : ∃ t', G.grad ((CL.wv i ϱ' hϱ').piece t') e ≠ 0 := by
    by_contra h
    push Not at h
    exact h2 (grad_envelopeWave_eq_zero _ κ amp k₀ h)
  obtain ⟨t, ht⟩ := ht
  obtain ⟨t', ht'⟩ := ht'
  rcases CL.wv_disj i ϱ hϱ ϱ' hϱ' hne t t' e with h | h
  · exact ht h
  · exact ht' h

/-- Assembled waves pair to zero with the other densities of the ensemble. -/
theorem rootedSpinWaveD_orth
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (κ amp : ℝ) (k₀ : ℕ) (i : Fin CL.n) {ϱ ϱ' : V → ℤ} (hϱ : ϱ ∈ CL.N i) (hϱ' : ϱ' ∈ CL.N i)
    (hne : ϱ ≠ ϱ') : ∑ j, rootedSpinWaveD CL κ amp k₀ i ϱ j * (ϱ' j : ℝ) = 0 := by
  classical
  simp only [rootedSpinWaveD, dite_eq_left hϱ]
  let _ := (CL.wv i ϱ hϱ).finite
  simp only [envelopeWave, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [CL.wv_orth i ϱ hϱ t ϱ' hϱ' (Ne.symm hne), mul_zero]

/-- The assembled waves have gradients at most `max(λK₁, 1)`. -/
theorem abs_grad_rootedSpinWaveD_le
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {κ : ℝ} (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) {amp : ℝ} (hamp : 0 ≤ amp) (k₀ : ℕ)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) (e : E) :
    |G.grad (rootedSpinWaveD CL κ amp k₀ i ϱ) e| ≤ max (amp * K₁) 1 := by
  obtain ⟨-, hK0, hK1, -⟩ := CL.layer i ϱ hϱ
  simp only [rootedSpinWaveD, dite_eq_left hϱ]
  refine (abs_grad_envelopeWave_le _ hκ (by rw [hK0]; exact hK₀) (by rw [hK1]; exact hK₁)
    hamp k₀ e).trans ?_
  rw [hK1]

/-- **Decay of the renormalized activities** (as `abs_rootedActivity_le`). -/
theorem abs_rootedActivityD_le
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {c : ℝ → ℝ} {κ κ' W : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    {a₁ a₂ b : ℝ} (hZ : ∀ ϱ : V → ℤ, Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ))
    (hb0 : 0 ≤ b) (hb₁ : b ≤ amp / 8 - a₁) (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂)
    (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ A ϱ) :
    |rootedActivityD CL c κ amp k₀ i ϱ| ≤ Real.exp (-b * (∑ j, |(ϱ j : ℝ)| + ℓ)) := by
  have hgain := rootedD_gain CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂ i ϱ hϱ
  have hK := CL.entropy i ϱ hϱ
  have hZϱ := hZ ϱ
  set X : ℝ := ∑ j, |(ϱ j : ℝ)|
  set E' := translationEnergy c (gradLinear G) (rootedSpinWaveD CL κ amp k₀ i ϱ)
    fun j => (ϱ j : ℝ)
  have hA0 : 0 ≤ A ϱ := hℓ0.trans hℓ
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold rootedActivityD
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

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- **The T1.6-NG identity for a `RootedChargeLayerD`** under any law with the character
translation property (all densities are neutral, so no charged density has to integrate out). -/
theorem rootedD_identity_of_law (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] (r : E → ℝ)
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hw : IsStripWeight w W c) (hμ : CharacterTranslation μ (gradLinear G) w r W) {κ : ℝ}
    (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) {amp : ℝ} (hamp : 0 ≤ amp)
    (hampW : amp * K₁ ≤ W) (hW1 : 1 ≤ W) (k₀ : ℕ) (σ : V → ℝ) :
    ∫ φ, ((∏ j, lam j (φ j + σ j - (φ root + σ root)) : ℝ) : ℂ) ∂μ =
      ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.N i, ((1 : ℂ) +
        ((rootedActivityD CL c κ amp k₀ i ϱ : ℝ) : ℂ) *
        localFactor w c (gradLinear G (rootedSpinWaveD CL κ amp k₀ i ϱ)) (gradLinear G φ + r)
          (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂μ := by
  classical
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
  set P := CL.N i
  have key := integral_prod_add_mul_cos_eq_localFactor μ (gradLinear G) w c hw.cost_even r
    hw.width_nonneg hμ hw.ofReal_ne_zero
    (ι := P) (fun ϱ j => ((ϱ : V → ℤ) j : ℝ))
    (fun ϱ => by exact_mod_cast CL.neutral i ϱ ϱ.2) (fun _ => 1) (fun ϱ => CL.K i ϱ)
    (fun ϱ => ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ)) (fun ϱ => rootedSpinWaveD CL κ amp k₀ i ϱ)
    (fun ϱ ϱ' hne => rootedSpinWaveD_orth CL κ amp k₀ i ϱ.2 ϱ'.2 fun h => hne (Subtype.ext h))
    (fun ϱ ϱ' hne e => by
      simp only [gradLinear_apply]
      exact grad_rootedSpinWaveD_disjoint CL κ amp k₀ i ϱ.2 ϱ'.2
        (fun h => hne (Subtype.ext h)) e)
    (fun ϱ e => by
      simp only [gradLinear_apply]
      exact (abs_grad_rootedSpinWaveD_le CL hκ hK₀ hK₁ hamp k₀ i ϱ ϱ.2 e).trans
        (max_le hampW hW1))
  have hl : ∀ φ : V → ℝ, (((∏ ϱ ∈ P, (1 + CL.K i ϱ *
      Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ)))) : ℝ) : ℂ) =
      ((∏ ϱ : P, (1 + CL.K i ϱ * Real.cos (∑ j, φ j * ((ϱ : V → ℤ) j : ℝ) +
        ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ))) : ℝ) : ℂ) := by
    intro φ
    rw [← Finset.prod_coe_sort P]
    congr 2
    funext ϱ
    congr 3
    exact sum_add_mul_eq φ σ ϱ
  simp_rw [hl]
  rw [key]
  congr 1
  funext φ
  rw [← Finset.prod_coe_sort P]
  rfl

end FroehlichSpencer.BKT.Generic

end
