/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Rooted.Layer
public import FroehlichSpencer.BKT.Generic.Rooted.LocalPacking
public import FroehlichSpencer.BKT.Generic.Moment.Assembly

/-!
# T1.5-NG for a rooted charge layer (the pinned-carrier consumer)

The variant of `integral_shift_ge_of_chargeLayer` (`Generic/Moment/Assembly.lean`, FS81 )
that consumes a `RootedChargeLayer` (restricted-domain expansion, all densities neutral) with its
local geometry `RootedChargeLayer.IsLocal` instead of KP's square-domain volume bound. For the
root-relative observable `O(φ) = ∏_j λ_j(φ_j − φ_root)` and any shift `σ`, edge field `θ`:

`exp(−κ ‖θ‖² − ε ∑_e ([∇σ(e)]²_{2π} + θ(e)²)) ∫ ρ₀(φ) O(φ) dφ ≤ ∫ ρ_θ(φ) O(φ + σ) dφ`,

with `ρ₀ = edgeDensity G w root` and `ρ_θ = offsetEdgeDensity G w θ root`. The proof is the exponential-moment
proof with the rooted identity (`rooted_identity_of_law`) and the local packing
(`sum_shiftError_le_local`): identity → branch bound (`integral_shiftProduct_ge`, unchanged) →
packing → averaging.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
  {G : Multigraph V E} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- **T1.5-NG for a rooted charge layer.** See the module docstring. -/
theorem integral_shift_ge_of_rootedLayer (hG : G.toSimpleGraph.Connected) (v : V)
    (CL : RootedChargeLayer G v lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {dsc : (V → ℤ) → ℕ} {Kv : ℝ} {Kov : ℕ} (hloc : CL.IsLocal dsc Kv Kov) (hKv : 0 ≤ Kv)
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
      (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    (σ : V → ℝ) (θ : E → ℝ) :
    Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
        ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v) ≤
      ∫ φ, offsetEdgeDensity G w θ v φ * ∏ j, lam j (φ j + σ j - (φ v + σ v)) := by
  classical
  have hW : 0 < W := lt_of_lt_of_le one_pos hW1
  have hb0 : 0 ≤ b := le_trans (by positivity) hb8
  have hA'W : max (amp * K₁) 1 ≤ W := max_le hampW hW1
  set bb : Fin CL.n → (V → ℤ) → E → ℝ := fun i ϱ => G.grad (rootedSpinWave CL κ amp k₀ i ϱ)
    with hbb
  set zz : Fin CL.n → (V → ℤ) → ℝ := rootedActivity CL c κ amp k₀ with hzz
  set s : (V → ℤ) → ℝ := fun ϱ => toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ϱ j : ℝ))
    with hs
  set T : Fin CL.n → (V → ℤ) → ℝ := fun i ϱ => Real.sqrt (∑ e ∈ CL.S i ϱ, θ e ^ 2) with hT
  -- the per-density facts
  have hbA : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, |bb i ϱ e| ≤ max (amp * K₁) 1 := fun i ϱ hϱ e =>
    abs_grad_rootedSpinWave_le CL hκ hK₀ hK₁ hamp k₀ i ϱ hϱ e
  have hbW : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, |bb i ϱ e| ≤ W := fun i ϱ hϱ e =>
    (hbA i ϱ hϱ e).trans hA'W
  have hlogb : ∀ i, ∀ ϱ ∈ CL.N i, 0 ≤ Real.logb 2 (dsc ϱ + 1) := fun i ϱ _ =>
    Real.logb_nonneg (by norm_num) (by
      have := Nat.cast_nonneg (α := ℝ) (dsc ϱ); linarith)
  have hdecay : ∀ i, ∀ ϱ ∈ CL.N i, |zz i ϱ| ≤
      Real.exp (-b * (∑ j, |(ϱ j : ℝ)| + Real.logb 2 (dsc ϱ + 1))) :=
    fun i ϱ hϱ => abs_rootedActivity_le CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂
      hZ hb0 hb₁ hb₂ i ϱ hϱ (hlogb i ϱ hϱ) (hloc.cover i ϱ hϱ)
  have hz8 : ∀ i, ∀ ϱ ∈ CL.N i, |zz i ϱ| ≤ 1 / 8 := fun i ϱ hϱ =>
    abs_layerActivity_le_eighth hb8
      (two_le_sum_abs_of_neutral ϱ (hloc.ne_zero i ϱ hϱ) (CL.neutral i ϱ hϱ))
      (hlogb i ϱ hϱ) (hdecay i ϱ hϱ)
  have hsupp : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, bb i ϱ e ≠ 0 → e ∈ CL.S i ϱ := fun i ϱ hϱ e he =>
    grad_rootedSpinWave_mem CL κ amp k₀ i ϱ hϱ e he
  have hθT : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, bb i ϱ e ≠ 0 → |θ e| ≤ T i ϱ := fun i ϱ hϱ e he =>
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun e => θ e ^ 2) (fun _ _ => sq_nonneg _)
      (hsupp i ϱ hϱ e he))
  -- the branch bounds and the packing
  have hbranch : ∀ i, Real.exp (-(κc * ∑ e, θ e ^ 2 + ∑ ϱ ∈ CL.N i, 8 * |zz i ϱ| *
        (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T i ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T i ϱ ^ 2))) *
        ∫ φ, edgeDensity G w v φ * shiftProduct G w c (CL.N i) (bb i) (zz i) θ s 0 φ ≤
      ∫ φ, offsetEdgeDensity G w θ v φ * shiftProduct G w c (CL.N i) (bb i) (zz i) θ s 1 φ :=
    fun i => integral_shiftProduct_ge G hG v hw hW hnzero hlog hcurv (CL.N i) (bb i) (zz i)
      (max (amp * K₁) 1) m (hbA i) hA'W hm0 hm1 hM (hz8 i) θ s (T i) (hθT i)
  have hpack : ∀ i, ∑ ϱ ∈ CL.N i, 8 * |zz i ϱ| *
        (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T i ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T i ϱ ^ 2) ≤
      ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2) :=
    fun i => sum_shiftError_le_local G dsc (CL.S i) Kv hKv Kov (CL.N i) (hloc.ne_zero i)
      (CL.neutral i) (hloc.one_le_dsc i) (hloc.card_le i) (hloc.route i) (hloc.overlap i)
      (bb i) (hsupp i) m hm0 hm1 (zz i) b ε (hdecay i) hthr σ θ
  -- the expansions in Lebesgue form
  have hid1 : ∫ φ, offsetEdgeDensity G w θ v φ * ∏ j, lam j (φ j + σ j - (φ v + σ v)) =
      ∑ i, CL.c i * ∫ φ, offsetEdgeDensity G w θ v φ *
        shiftProduct G w c (CL.N i) (bb i) (zz i) θ s 1 φ := by
    refine integral_mul_eq_sum_of_densityLaw (offsetEdgeDensity_nonneg G hw θ v)
      (measurable_offsetEdgeDensity G hw θ v) (densityMass_offsetEdgeDensity_ne_zero G hw θ v)
      (densityMass_offsetEdgeDensity_ne_top G hG hw θ v) CL.c
      (fun φ => ∏ j, lam j (φ j + σ j - (φ v + σ v))) _ _ (fun i φ => ?_)
      (rooted_identity_of_law (offsetEdgeLaw G w θ v) θ CL hw
        (isRootedTranslationLaw_offsetEdgeLaw G hG hw θ v) hκ hK₀ hK₁ hamp hampW hW1 k₀ σ)
    unfold shiftProduct
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun ϱ hϱ => ?_
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul (zz i ϱ),
      ofReal_lineFactor_one hw _ (hbW i ϱ hϱ), gradLinear_eq, gradLinear_eq]
  have hid0 : ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v) =
      ∑ i, CL.c i * ∫ φ, edgeDensity G w v φ *
        shiftProduct G w c (CL.N i) (bb i) (zz i) θ s 0 φ := by
    have h := rooted_identity_of_law (offsetEdgeLaw G w 0 v) 0 CL hw
      (isRootedTranslationLaw_offsetEdgeLaw G hG hw 0 v) hκ hK₀ hK₁ hamp hampW hW1 k₀ 0
    simp only [Pi.zero_apply, add_zero, zero_mul, Finset.sum_const_zero] at h
    have h' := integral_mul_eq_sum_of_densityLaw (offsetEdgeDensity_nonneg G hw 0 v)
      (measurable_offsetEdgeDensity G hw 0 v) (densityMass_offsetEdgeDensity_ne_zero G hw 0 v)
      (densityMass_offsetEdgeDensity_ne_top G hG hw 0 v) CL.c (fun φ => ∏ j, lam j (φ j - φ v))
      (fun i φ => shiftProduct G w c (CL.N i) (bb i) (zz i) θ s 0 φ) _ (fun i φ => ?_) h
    · rwa [offsetEdgeDensity_zero] at h'
    unfold shiftProduct
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun ϱ hϱ => ?_
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul (zz i ϱ),
      ofReal_lineFactor_zero hw _ (hbW i ϱ hϱ), gradLinear_eq, gradLinear_eq]
  -- averaging
  rw [hid0, hid1, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hint0 : 0 ≤ ∫ φ, edgeDensity G w v φ *
      shiftProduct G w c (CL.N i) (bb i) (zz i) θ s 0 φ :=
    integral_nonneg fun φ => mul_nonneg (edgeDensity_nonneg G hw v φ)
      (shiftProduct_pos hw G (CL.N i) (bb i) (hbW i) (zz i) (hz8 i) θ s 0 φ).le
  have hci := (CL.c_pos i).le
  calc _ = CL.c i * (Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
        ∫ φ, edgeDensity G w v φ * shiftProduct G w c (CL.N i) (bb i) (zz i) θ s 0 φ) := by ring
    _ ≤ CL.c i * ∫ φ, offsetEdgeDensity G w θ v φ *
        shiftProduct G w c (CL.N i) (bb i) (zz i) θ s 1 φ := by
      refine mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ?_) hint0) (hbranch i)) hci
      linarith [hpack i]

end FroehlichSpencer.BKT.Generic

end
