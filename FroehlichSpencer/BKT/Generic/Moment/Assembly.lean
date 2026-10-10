/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.Branch
public import FroehlichSpencer.BKT.Generic.Moment.Packing
public import FroehlichSpencer.BKT.Generic.Moment.LayerActivity

/-!
# T1.5-NG: the exponential-moment lower bound of the non-Gaussian reference law (generic core)

Write `ρ₀ = edgeDensity G w v` for the rooted edge density and `ρ_θ = offsetEdgeDensity G w θ v`
for the density with every edge gradient shifted by the real field `θ`.

For an observable
`∏_j λ_j(φ_j)` that admits a charge layer (`ChargeLayer`,) and a shift `σ` of the
field, the main theorem `integral_shift_ge_of_chargeLayer` is

`exp(−κ ‖θ‖² − ε ∑_e ([∇σ(e)]²_{2π} + θ(e)²)) ∫ ρ₀(φ) ∏_j λ_j(φ_j) dφ
  ≤ ∫ ρ_θ(φ) ∏_j λ_j(φ_j + σ_j) dφ`,

where `κ` is the curvature constant of the weight (`HasCurvatureBound`, FS81 (6.28)),
`[t]_{2π} ∈ [−π, π)` is the reduced phase, and `ε` is the packing threshold (`hthr`; it can be
taken `≤ C e^{−b}` by `exists_touching_threshold`, with `b` the decay rate of the renormalized
activities).

In the XY application `θ + ∇σ` is the defect field after the change of variables
`φ ↦ φ + σ`, and the right side is the numerator `Z(η)` of the two-point function.

Proof (the KP T1.5 pattern):

1. **Expansion.** The T1.6-NG identity under the offset law
   (`offsetEdgeLaw_renormalization_identity`), at `(θ, σ)` and at `(0, 0)`, in Lebesgue form
   (`integral_mul_eq_sum_of_densityLaw`).

The renormalized factors are real
   (`ofReal_lineFactor_one`, `ofReal_lineFactor_zero`), and the phase shifts are reduced mod `2π`.
2. **Branch bound** (`integral_shiftProduct_ge`): the real shift, the per-factor Taylor step and
   symmetrization, for each ensemble.
3. **Packing** (`sum_shiftError_le`): the errors of one ensemble are at most
   `ε ∑_e ([∇σ]² + θ²)`, using the activity decay of `abs_layerActivity_le` (KP P2.1's
   `log₂(d+1) ≤ A`, the exponential entropy bound `hZ`) and the same-scale disjointness `hdisj`.
4. **Averaging** over the positive mixture weights `c_i`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-! ## The Lebesgue form of a density-law identity -/

omit [DecidableEq V] in
/-- An identity `∫ f d(ρ dφ/Z) = ∑ c_i ∫ g_i d(ρ dφ/Z)` between real integrands, read in the
complex integral, gives `∫ ρ f = ∑ c_i ∫ ρ g_i`. -/
theorem integral_mul_eq_sum_of_densityLaw {ρ : (V → ℝ) → ℝ} (hρ : ∀ φ, 0 ≤ ρ φ)
    (hmeas : Measurable ρ) (h0 : densityMass ρ ≠ 0) (htop : densityMass ρ ≠ ⊤) {n : ℕ}
    (c : Fin n → ℝ) (f : (V → ℝ) → ℝ) (g : Fin n → (V → ℝ) → ℝ) (F : Fin n → (V → ℝ) → ℂ)
    (hF : ∀ i φ, F i φ = (g i φ : ℂ))
    (h : ∫ φ, (f φ : ℂ) ∂densityLaw ρ = ∑ i, (c i : ℂ) * ∫ φ, F i φ ∂densityLaw ρ) :
    ∫ φ, ρ φ * f φ = ∑ i, c i * ∫ φ, ρ φ * g i φ := by
  have hF' : F = fun i φ => (g i φ : ℂ) := funext fun i => funext fun φ => hF i φ
  subst hF'
  simp only [integral_densityLaw hρ hmeas] at h
  have hcast : ∀ u : (V → ℝ) → ℝ,
      ∫ φ, (ρ φ : ℂ) * (u φ : ℂ) = ((∫ φ, ρ φ * u φ : ℝ) : ℂ) := fun u => by
    simp_rw [← Complex.ofReal_mul]; exact integral_ofReal
  simp only [hcast] at h
  set k : ℂ := (((densityMass ρ)⁻¹.toReal : ℝ) : ℂ) with hkdef
  have hk : k ≠ 0 := by
    rw [hkdef, Complex.ofReal_ne_zero]
    exact ENNReal.toReal_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr htop, ENNReal.inv_ne_top.mpr h0⟩
  have h' : k * ((∫ φ, ρ φ * f φ : ℝ) : ℂ) =
      k * ((∑ i, c i * ∫ φ, ρ φ * g i φ : ℝ) : ℂ) := by
    rw [h, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_mul]; ring
  exact_mod_cast mul_left_cancel₀ hk h'

/-! ## The renormalized factors are real -/

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

omit [Fintype V] [DecidableEq V] in
/-- At time `0` the line factor is the local factor. -/
theorem ofReal_lineFactor_zero (hw : IsStripWeight w W c) (b : E → ℝ) (hb : ∀ e, |b e| ≤ W)
    (x y : E → ℝ) (ph s : ℝ) :
    ((lineFactor w c b x y ph s 0 : ℝ) : ℂ) = localFactor w c b x ph := by
  unfold lineFactor
  rw [zero_smul, add_zero, zero_mul, add_zero]
  exact Complex.ext rfl (by rw [Complex.ofReal_im, localFactor_im_eq_zero hw.conj hw.cost_even b x hb])

omit [Fintype V] [DecidableEq V] in
/-- At time `1`, with the reduced phase shift, the line factor is the shifted local factor. -/
theorem ofReal_lineFactor_one (hw : IsStripWeight w W c) (b : E → ℝ) (hb : ∀ e, |b e| ≤ W)
    (x y : E → ℝ) (ph r : ℝ) :
    ((lineFactor w c b x y ph (toIcoMod Real.two_pi_pos (-Real.pi) r) 1 : ℝ) : ℂ) =
      localFactor w c b (x + y) (ph + r) := by
  unfold lineFactor
  rw [one_smul, one_mul]
  have hr : ph + r = ph + toIcoMod Real.two_pi_pos (-Real.pi) r +
      (toIcoDiv Real.two_pi_pos (-Real.pi) r : ℤ) * (2 * Real.pi) := by
    have := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos (-Real.pi) r
    rw [zsmul_eq_mul] at this
    linarith
  rw [hr, localFactor_add_two_pi_mul]
  exact Complex.ext rfl (by
    rw [Complex.ofReal_im, localFactor_im_eq_zero hw.conj hw.cost_even b _ hb])

omit [Fintype V] [Fintype E] [DecidableEq V] in
lemma gradLinear_eq (G : Multigraph V E) (f : V → ℝ) : gradLinear G f = G.grad f :=
  funext fun e => gradLinear_apply G f e

/-! ## The main theorem -/

variable {G : Multigraph V E} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- **T1.5-NG (FS81 ), generic in the charge layer and the strip weight.** See the module
docstring. The hypotheses are: the rooted-compatibility of the layer (`hroot`), nonzero densities
with admissible centers (`hne`, `hcenter`), KP's same-scale disjointness (`hdisj`), KP P2.1's
first half (`hAlog`), an edge-volume bound (`hvol`); the strip weight with its logarithmic-
derivative bounds (`hlog`, `hM`) and curvature (`hcurv`); the translation amplitude conditions; the entropy
bound `hZ` and the decay rate `b`; and the packing threshold `hthr`. -/
theorem integral_shift_ge_of_chargeLayer (hG : G.toSimpleGraph.Connected) (v : V)
    (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hroot : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i))
    (hne : ∀ i, ∀ ϱ ∈ CL.R i, ϱ ≠ 0)
    (hcenter : ∀ i, ∀ ϱ ∈ CL.R i, G.IsDensityCenter ϱ (centerOf ϱ))
    (hdisj : ∀ i, ∀ ϱ₁ ∈ CL.R i, ∀ ϱ₂ ∈ CL.R i, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
      G.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      G.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
      ∀ j₁ j₂ : V, G.IsDensityCenter ϱ₁ j₁ → G.IsDensityCenter ϱ₂ j₂ →
        G.densityDomain ϱ₁ j₁ ∩ G.densityDomain ϱ₂ j₂ = ∅)
    (hAlog : ∀ i, ∀ ϱ ∈ CL.R i, Real.logb 2 (G.densityDiameter ϱ + 1) ≤ A ϱ)
    {Kv : ℝ} (hKv : 0 ≤ Kv)
    (hvol : ∀ (ρ : V → ℤ) (j : V),
      ((edgesTouching G (G.densityDomain ρ j)).card : ℝ) ≤ Kv * ((G.densityDiameter ρ : ℝ) + 1) ^ 2)
    (hw : IsStripWeight w W c) (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) {M : ℝ → ℝ}
    (hlog : HasLogDerivBounds w W M) {κc : ℝ} (hcurv : HasCurvatureBound w κc)
    {κ κ' : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hM : ∀ u : ℝ, |u| ≤ max (amp * K₁) 1 → M u ≤ m)
    {a₁ a₂ b : ℝ} (hZ : ∀ ϱ : V → ℤ, Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ))
    (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁) (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂)
    {ε : ℝ} (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    (σ : V → ℝ) (θ : E → ℝ) :
    Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
        ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j) ≤
      ∫ φ, offsetEdgeDensity G w θ v φ * ∏ j, lam j (φ j + σ j) := by
  classical
  have hW : 0 < W := lt_of_lt_of_le one_pos hW1
  have hb0 : 0 ≤ b := le_trans (by positivity) hb8
  have hA'W : max (amp * K₁) 1 ≤ W := max_le hampW hW1
  set bb : Fin CL.n → (V → ℤ) → E → ℝ := fun i ϱ => G.grad (layerSpinWave CL κ amp k₀ i ϱ)
    with hbb
  set zz : Fin CL.n → (V → ℤ) → ℝ := layerActivity CL c κ amp k₀ with hzz
  set s : (V → ℤ) → ℝ := fun ϱ => toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ϱ j : ℝ))
    with hs
  set T : (V → ℤ) → ℝ := fun ϱ =>
    Real.sqrt (∑ e ∈ edgesTouching G (G.densityDomain ϱ (centerOf ϱ)), θ e ^ 2) with hT
  -- the per-density facts
  have hbA : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, |bb i ϱ e| ≤ max (amp * K₁) 1 := fun i ϱ hϱ e =>
    abs_grad_layerSpinWave_le CL hκ hK₀ hK₁ hamp k₀ i ϱ hϱ e
  have hbW : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, |bb i ϱ e| ≤ W := fun i ϱ hϱ e =>
    (hbA i ϱ hϱ e).trans hA'W
  have hneutral : ∀ i, ∀ ϱ ∈ CL.R i, ∑ j, ϱ j = 0 := fun i ϱ hϱ => by
    rw [(hroot i).1] at hϱ; exact (mem_neutralPart.mp hϱ).2
  have hdecay : ∀ i, ∀ ϱ ∈ CL.R i, |zz i ϱ| ≤
      Real.exp (-b * (∑ j, |(ϱ j : ℝ)| + Real.logb 2 (G.densityDiameter ϱ + 1))) :=
    fun i ϱ hϱ => abs_layerActivity_le CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂
      hZ hb0 hb₁ hb₂ i ϱ hϱ (hAlog i ϱ hϱ)
  have hz8 : ∀ i, ∀ ϱ ∈ CL.R i, |zz i ϱ| ≤ 1 / 8 := fun i ϱ hϱ =>
    abs_layerActivity_le_eighth hb8 (two_le_sum_abs_of_neutral ϱ (hne i ϱ hϱ) (hneutral i ϱ hϱ))
      (Real.logb_nonneg (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) (G.densityDiameter ϱ); linarith)) (hdecay i ϱ hϱ)
  have hsupp : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, bb i ϱ e ≠ 0 →
      e ∈ edgesTouching G (G.densityDomain ϱ (centerOf ϱ)) := fun i ϱ hϱ e he =>
    grad_ne_zero_mem_edgesTouching G ((layerSpinWave_clauses CL κ amp k₀ i).2.1 ϱ hϱ) he
  have hθT : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, bb i ϱ e ≠ 0 → |θ e| ≤ T ϱ := fun i ϱ hϱ e he =>
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun e => θ e ^ 2) (fun _ _ => sq_nonneg _)
      (hsupp i ϱ hϱ e he))
  -- the branch bounds and the packing
  have hbranch : ∀ i, Real.exp (-(κc * ∑ e, θ e ^ 2 + ∑ ϱ ∈ CL.R i, 8 * |zz i ϱ| *
        (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
        ∫ φ, edgeDensity G w v φ * shiftProduct G w c (CL.R i) (bb i) (zz i) θ s 0 φ ≤
      ∫ φ, offsetEdgeDensity G w θ v φ * shiftProduct G w c (CL.R i) (bb i) (zz i) θ s 1 φ :=
    fun i => integral_shiftProduct_ge G hG v hw hW hnzero hlog hcurv (CL.R i) (bb i) (zz i)
      (max (amp * K₁) 1) m (hbA i) hA'W hm0 hm1 hM (hz8 i) θ s T (hθT i)
  have hpack : ∀ i, ∑ ϱ ∈ CL.R i, 8 * |zz i ϱ| *
        (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2) ≤
      ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2) :=
    fun i => sum_shiftError_le G hG Kv hKv hvol (CL.R i) (hne i) (hneutral i) centerOf
      (hcenter i) (hdisj i) (bb i) (hsupp i) m hm0 hm1 (zz i) b ε (hdecay i) hthr σ θ
  -- the expansions in Lebesgue form
  have hid1 : ∫ φ, offsetEdgeDensity G w θ v φ * ∏ j, lam j (φ j + σ j) =
      ∑ i, CL.c i * ∫ φ, offsetEdgeDensity G w θ v φ *
        shiftProduct G w c (CL.R i) (bb i) (zz i) θ s 1 φ := by
    refine integral_mul_eq_sum_of_densityLaw (offsetEdgeDensity_nonneg G hw θ v)
      (measurable_offsetEdgeDensity G hw θ v) (densityMass_offsetEdgeDensity_ne_zero G hw θ v)
      (densityMass_offsetEdgeDensity_ne_top G hG hw θ v) CL.c _ _ _ (fun i φ => ?_)
      (offsetEdgeLaw_renormalization_identity hG v θ CL hroot hw hκ hK₀ hK₁ hamp hampW hW1 k₀ σ)
    unfold shiftProduct
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun ϱ hϱ => ?_
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul (zz i ϱ),
      ofReal_lineFactor_one hw _ (hbW i ϱ hϱ), gradLinear_eq, gradLinear_eq]
    rfl
  have hid0 : ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j) =
      ∑ i, CL.c i * ∫ φ, edgeDensity G w v φ *
        shiftProduct G w c (CL.R i) (bb i) (zz i) θ s 0 φ := by
    have h := offsetEdgeLaw_renormalization_identity hG v 0 CL hroot hw hκ hK₀ hK₁ hamp hampW
      hW1 k₀ 0
    simp only [Pi.zero_apply, add_zero, zero_mul, Finset.sum_const_zero] at h
    have h' := integral_mul_eq_sum_of_densityLaw (offsetEdgeDensity_nonneg G hw 0 v)
      (measurable_offsetEdgeDensity G hw 0 v) (densityMass_offsetEdgeDensity_ne_zero G hw 0 v)
      (densityMass_offsetEdgeDensity_ne_top G hG hw 0 v) CL.c (fun φ => ∏ j, lam j (φ j))
      (fun i φ => shiftProduct G w c (CL.R i) (bb i) (zz i) θ s 0 φ) _ (fun i φ => ?_) h
    · rwa [offsetEdgeDensity_zero] at h'
    unfold shiftProduct
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun ϱ hϱ => ?_
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul (zz i ϱ),
      ofReal_lineFactor_zero hw _ (hbW i ϱ hϱ), gradLinear_eq, gradLinear_eq]
    rfl
  -- averaging
  rw [hid0, hid1, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hint0 : 0 ≤ ∫ φ, edgeDensity G w v φ *
      shiftProduct G w c (CL.R i) (bb i) (zz i) θ s 0 φ :=
    integral_nonneg fun φ => mul_nonneg (edgeDensity_nonneg G hw v φ)
      (shiftProduct_pos hw G (CL.R i) (bb i) (hbW i) (zz i) (hz8 i) θ s 0 φ).le
  have hci := (CL.c_pos i).le
  calc _ = CL.c i * (Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
        ∫ φ, edgeDensity G w v φ * shiftProduct G w c (CL.R i) (bb i) (zz i) θ s 0 φ) := by ring
    _ ≤ CL.c i * ∫ φ, offsetEdgeDensity G w θ v φ *
        shiftProduct G w c (CL.R i) (bb i) (zz i) θ s 1 φ := by
      refine mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ?_) hint0) (hbranch i)) hci
      linarith [hpack i]

end FroehlichSpencer.BKT.Generic

end
