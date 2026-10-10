/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Tilt.Branch
public import FroehlichSpencer.BKT.SOS.Tilt.Rooted
public import FroehlichSpencer.BKT.Generic.Rooted.MomentD

/-!
# The tilted moment bound for a rooted D-layer (the dipole tilt construction: FS81 (7.29)–(7.31), generic form)

`integral_shift_ge_of_rootedLayerD` with the tilt `e^{⟨∇φ, b⟩}` on the shifted side. For the
root-relative observable `O(φ) = ∏_j λ_j(φ_j − φ_root)`, any shift `σ`, edge field `θ` and tilt
`b` with `|b| ≤ η/2` (`η` the exponential rate of the weight):

`exp(−κ‖θ‖² − 2ε ∑_e ([∇σ(e)]²_{2π} + θ(e)²) − 16Λ) ∫ ρ₀ O ≤ ∫ e^{⟨∇φ, b⟩} ρ_θ(φ) O(φ + σ) dφ`,

where `Λ` bounds the **endpoint sums** `∑_ρ |z(ρ)| ⟨∇a_ρ, b⟩²` of every ensemble of the layer. The
proof is that of `integral_shift_ge_of_rootedLayerD` with the phased identity
(`rootedD_identity_of_law_phased` under the tilted law), the tilted branch bound
(`integral_shiftProduct_tilt_ge`), and the phase `s = [⟨σ, ρ⟩]_{2π} + ⟨∇a_ρ, b⟩`, whose square is at
most `2[⟨σ, ρ⟩]²_{2π} + 2⟨∇a_ρ, b⟩²`: the first part is packed as before
(`sum_shiftError_le_local`), the second is FS81's endpoint term (`Λ_end` of (★)).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Tilt

open MeasureTheory Complex Finset
open FroehlichSpencer.BKT.Generic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
  {G : Multigraph V E} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

omit [DecidableEq V] in
theorem densityMass_tiltDensity_ne_zero (G : Multigraph V E) (hw : IsStripWeight w W c)
    (θ b : E → ℝ) (v : V) : densityMass (tiltDensity G w θ b v) ≠ 0 := by
  intro h0
  apply densityMass_offsetEdgeDensity_ne_zero G hw θ v
  rw [densityMass, lintegral_eq_zero_iff (measurable_tiltDensity G hw θ b v).ennreal_ofReal]
    at h0
  rw [densityMass,
    lintegral_eq_zero_iff (measurable_offsetEdgeDensity G hw θ v).ennreal_ofReal]
  filter_upwards [h0] with φ hφ
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hφ ⊢
  unfold tiltDensity at hφ
  by_contra hpos
  exact absurd hφ (not_le.mpr (mul_pos (Real.exp_pos _) (not_le.mp hpos)))

theorem densityMass_tiltDensity_ne_top (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (hw : IsStripWeight w W c) {η K : ℝ} (hη : 0 < η) (hexp : HasExpMajorant w W η K)
    (θ b : E → ℝ) (hb : ∀ e, |b e| ≤ η / 2) (v : V) :
    densityMass (tiltDensity G w θ b v) ≠ ⊤ :=
  (integrable_tiltDensity G hG hw hη hexp θ b hb v).lintegral_lt_top.ne

omit [Fintype V] [DecidableEq V] in
/-- At time `1`, with the reduced phase plus an extra phase `p`, the line factor is the shifted
local factor. -/
theorem ofReal_lineFactor_one_add (hw : IsStripWeight w W c) (b : E → ℝ)
    (hb : ∀ e, |b e| ≤ W) (x y : E → ℝ) (ph r p : ℝ) :
    ((lineFactor w c b x y ph (toIcoMod Real.two_pi_pos (-Real.pi) r + p) 1 : ℝ) : ℂ) =
      localFactor w c b (x + y) (ph + (r + p)) := by
  unfold lineFactor
  rw [one_smul, one_mul]
  have hr : ph + (r + p) = ph + (toIcoMod Real.two_pi_pos (-Real.pi) r + p) +
      (toIcoDiv Real.two_pi_pos (-Real.pi) r : ℤ) * (2 * Real.pi) := by
    have := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos (-Real.pi) r
    rw [zsmul_eq_mul] at this
    linarith
  rw [hr, localFactor_add_two_pi_mul]
  exact Complex.ext rfl (by
    rw [Complex.ofReal_im, localFactor_im_eq_zero hw.conj hw.cost_even b _ hb])

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- The error of a phase `s + p` splits into twice the error of `s` and the endpoint term. -/
lemma shiftError_add_le {z s p X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    8 * |z| * ((s + p) ^ 2 + X + Y) ≤ 2 * (8 * |z| * (s ^ 2 + X + Y)) + 16 * (|z| * p ^ 2) := by
  have h : (s + p) ^ 2 + X + Y ≤ 2 * (s ^ 2 + X + Y) + 2 * p ^ 2 := by
    nlinarith [sq_nonneg (s - p)]
  calc 8 * |z| * ((s + p) ^ 2 + X + Y) ≤ 8 * |z| * (2 * (s ^ 2 + X + Y) + 2 * p ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * (8 * |z| * (s ^ 2 + X + Y)) + 16 * (|z| * p ^ 2) := by ring

/-- **The untilted rooted comb integral is nonnegative**: the expansion of the layer writes it as a
convex combination of integrals of products of factors `1 + zF ≥ 7/8`. -/
theorem integral_edgeDensity_rootedLayerD_nonneg (hG : G.toSimpleGraph.Connected) (v : V)
    (CL : RootedChargeLayerD G v lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {dsc : (V → ℤ) → ℕ} {Kv : ℝ} {Kov : ℕ} (hloc : CL.IsLocal dsc Kv Kov)
    (hw : IsStripWeight w W c) {κ κ' : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp)
    (hampW : amp * K₁ ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    {a₁ a₂ b : ℝ} (hZ : ∀ ϱ : V → ℤ, Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ))
    (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁) (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂) :
    0 ≤ ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v) := by
  classical
  have hb0 : 0 ≤ b := le_trans (by positivity) hb8
  have hA'W : max (amp * K₁) 1 ≤ W := max_le hampW hW1
  set bb : Fin CL.n → (V → ℤ) → E → ℝ := fun i ϱ => G.grad (rootedSpinWaveD CL κ amp k₀ i ϱ)
    with hbb
  set zz : Fin CL.n → (V → ℤ) → ℝ := rootedActivityD CL c κ amp k₀ with hzz
  have hbW : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, |bb i ϱ e| ≤ W := fun i ϱ hϱ e =>
    (abs_grad_rootedSpinWaveD_le CL hκ hK₀ hK₁ hamp k₀ i ϱ hϱ e).trans hA'W
  have hlogb : ∀ i, ∀ ϱ ∈ CL.N i, 0 ≤ Real.logb 2 (dsc ϱ + 1) := fun i ϱ _ =>
    Real.logb_nonneg (by norm_num) (by
      have := Nat.cast_nonneg (α := ℝ) (dsc ϱ); linarith)
  have hz8 : ∀ i, ∀ ϱ ∈ CL.N i, |zz i ϱ| ≤ 1 / 8 := fun i ϱ hϱ =>
    abs_layerActivity_le_eighth hb8
      (two_le_sum_abs_of_neutral ϱ (hloc.ne_zero i ϱ hϱ) (CL.neutral i ϱ hϱ))
      (hlogb i ϱ hϱ) (abs_rootedActivityD_le CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁
        hquad₂ hZ hb0 hb₁ hb₂ i ϱ hϱ (hlogb i ϱ hϱ) (hloc.cover i ϱ hϱ))
  have hid0 : ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v) =
      ∑ i, CL.c i * ∫ φ, edgeDensity G w v φ *
        shiftProduct G w c (CL.N i) (bb i) (zz i) 0 0 0 φ := by
    have h := rootedD_identity_of_law (offsetEdgeLaw G w 0 v) 0 CL hw
      (characterTranslation_offsetEdgeLaw G hG hw 0 v) hκ hK₀ hK₁ hamp hampW hW1 k₀ 0
    simp only [Pi.zero_apply, add_zero, zero_mul, Finset.sum_const_zero] at h
    have h' := integral_mul_eq_sum_of_densityLaw (offsetEdgeDensity_nonneg G hw 0 v)
      (measurable_offsetEdgeDensity G hw 0 v) (densityMass_offsetEdgeDensity_ne_zero G hw 0 v)
      (densityMass_offsetEdgeDensity_ne_top G hG hw 0 v) CL.c (fun φ => ∏ j, lam j (φ j - φ v))
      (fun i φ => shiftProduct G w c (CL.N i) (bb i) (zz i) 0 0 0 φ) _ (fun i φ => ?_) h
    · rwa [offsetEdgeDensity_zero] at h'
    unfold shiftProduct
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun ϱ hϱ => ?_
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul (zz i ϱ),
      ofReal_lineFactor_zero hw _ (hbW i ϱ hϱ), gradLinear_eq, gradLinear_eq]
  rw [hid0]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (CL.c_pos i).le (integral_nonneg fun φ =>
    mul_nonneg (edgeDensity_nonneg G hw v φ)
      (shiftProduct_pos hw G (CL.N i) (bb i) (hbW i) (zz i) (hz8 i) 0 0 0 φ).le)

/-- **The tilted moment bound for a rooted charge layer.** See the module docstring. The
hypotheses are those of `integral_shift_ge_of_rootedLayerD`, an exponential majorant of the weight
with `|b| ≤ η/2`, and the endpoint bound `hΛ`. -/
theorem integral_tilt_ge_of_rootedLayerD (hG : G.toSimpleGraph.Connected) (v : V)
    (CL : RootedChargeLayerD G v lam centerOf A Zent D₁ D₂ α K₀ K₁)
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
    {η K : ℝ} (hη : 0 < η) (hwexp : HasExpMajorant w W η K) (bt : E → ℝ)
    (hbt : ∀ e, |bt e| ≤ η / 2) {Λ : ℝ}
    (hΛ : ∀ i, ∑ ϱ ∈ CL.N i, |rootedActivityD CL c κ amp k₀ i ϱ| *
      tiltExponent (gradLinear G) bt (rootedSpinWaveD CL κ amp k₀ i ϱ) ^ 2 ≤ Λ)
    (σ : V → ℝ) (θ : E → ℝ) :
    Real.exp (-(κc * ∑ e, θ e ^ 2) -
        2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2) -
        16 * Λ) *
        ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v) ≤
      ∫ φ, tiltDensity G w θ bt v φ * ∏ j, lam j (φ j + σ j - (φ v + σ v)) := by
  classical
  have hW : 0 < W := lt_of_lt_of_le one_pos hW1
  have hb0 : 0 ≤ b := le_trans (by positivity) hb8
  have hA'W : max (amp * K₁) 1 ≤ W := max_le hampW hW1
  set bb : Fin CL.n → (V → ℤ) → E → ℝ := fun i ϱ => G.grad (rootedSpinWaveD CL κ amp k₀ i ϱ)
    with hbb
  set zz : Fin CL.n → (V → ℤ) → ℝ := rootedActivityD CL c κ amp k₀ with hzz
  set p : Fin CL.n → (V → ℤ) → ℝ := fun i ϱ =>
    tiltExponent (gradLinear G) bt (rootedSpinWaveD CL κ amp k₀ i ϱ) with hp
  set s : Fin CL.n → (V → ℤ) → ℝ := fun i ϱ =>
    toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ϱ j : ℝ)) + p i ϱ with hs
  set T : Fin CL.n → (V → ℤ) → ℝ := fun i ϱ => Real.sqrt (∑ e ∈ CL.S i ϱ, θ e ^ 2) with hT
  -- the per-density facts
  have hbA : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, |bb i ϱ e| ≤ max (amp * K₁) 1 := fun i ϱ hϱ e =>
    abs_grad_rootedSpinWaveD_le CL hκ hK₀ hK₁ hamp k₀ i ϱ hϱ e
  have hbW : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, |bb i ϱ e| ≤ W := fun i ϱ hϱ e =>
    (hbA i ϱ hϱ e).trans hA'W
  have hlogb : ∀ i, ∀ ϱ ∈ CL.N i, 0 ≤ Real.logb 2 (dsc ϱ + 1) := fun i ϱ _ =>
    Real.logb_nonneg (by norm_num) (by
      have := Nat.cast_nonneg (α := ℝ) (dsc ϱ); linarith)
  have hdecay : ∀ i, ∀ ϱ ∈ CL.N i, |zz i ϱ| ≤
      Real.exp (-b * (∑ j, |(ϱ j : ℝ)| + Real.logb 2 (dsc ϱ + 1))) :=
    fun i ϱ hϱ => abs_rootedActivityD_le CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂
      hZ hb0 hb₁ hb₂ i ϱ hϱ (hlogb i ϱ hϱ) (hloc.cover i ϱ hϱ)
  have hz8 : ∀ i, ∀ ϱ ∈ CL.N i, |zz i ϱ| ≤ 1 / 8 := fun i ϱ hϱ =>
    abs_layerActivity_le_eighth hb8
      (two_le_sum_abs_of_neutral ϱ (hloc.ne_zero i ϱ hϱ) (CL.neutral i ϱ hϱ))
      (hlogb i ϱ hϱ) (hdecay i ϱ hϱ)
  have hsupp : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, bb i ϱ e ≠ 0 → e ∈ CL.S i ϱ := fun i ϱ hϱ e he =>
    grad_rootedSpinWaveD_mem CL κ amp k₀ i ϱ hϱ e he
  have hθT : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, bb i ϱ e ≠ 0 → |θ e| ≤ T i ϱ := fun i ϱ hϱ e he =>
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun e => θ e ^ 2) (fun _ _ => sq_nonneg _)
      (hsupp i ϱ hϱ e he))
  -- the branch bounds and the packing
  have hbranch : ∀ i, Real.exp (-(κc * ∑ e, θ e ^ 2 + ∑ ϱ ∈ CL.N i, 8 * |zz i ϱ| *
        (s i ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T i ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T i ϱ ^ 2))) *
        ∫ φ, edgeDensity G w v φ * shiftProduct G w c (CL.N i) (bb i) (zz i) θ (s i) 0 φ ≤
      ∫ φ, tiltDensity G w θ bt v φ * shiftProduct G w c (CL.N i) (bb i) (zz i) θ (s i) 1 φ :=
    fun i => integral_shiftProduct_tilt_ge G hG v hw hW hnzero hlog hcurv hη hwexp bt hbt
      (CL.N i) (bb i) (zz i) (max (amp * K₁) 1) m (hbA i) hA'W hm0 hm1 hM (hz8 i) θ (s i) (T i)
      (hθT i)
  have hpack : ∀ i, ∑ ϱ ∈ CL.N i, 8 * |zz i ϱ| *
        (s i ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T i ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T i ϱ ^ 2) ≤
      2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2) +
        16 * Λ := by
    intro i
    have h0 := sum_shiftError_le_local G dsc (CL.S i) Kv hKv Kov (CL.N i) (hloc.ne_zero i)
      (CL.neutral i) (hloc.one_le_dsc i) (hloc.card_le i) (hloc.route i) (hloc.overlap i)
      (bb i) (hsupp i) m hm0 hm1 (zz i) b ε (hdecay i) hthr σ θ
    have h1 : ∑ ϱ ∈ CL.N i, 8 * |zz i ϱ| *
          (s i ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T i ϱ) ^ 2 +
            ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T i ϱ ^ 2) ≤
        ∑ ϱ ∈ CL.N i, (2 * (8 * |zz i ϱ| *
          (toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ϱ j : ℝ)) ^ 2 +
            (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T i ϱ) ^ 2 +
            ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T i ϱ ^ 2)) +
          16 * (|zz i ϱ| * p i ϱ ^ 2)) :=
      Finset.sum_le_sum fun ϱ _ => shiftError_add_le (sq_nonneg _) (by positivity)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 := hΛ i
    rw [mul_assoc]
    linarith
  -- the expansions in Lebesgue form
  have hid1 : ∫ φ, tiltDensity G w θ bt v φ * ∏ j, lam j (φ j + σ j - (φ v + σ v)) =
      ∑ i, CL.c i * ∫ φ, tiltDensity G w θ bt v φ *
        shiftProduct G w c (CL.N i) (bb i) (zz i) θ (s i) 1 φ := by
    refine integral_mul_eq_sum_of_densityLaw (tiltDensity_nonneg G hw θ bt v)
      (measurable_tiltDensity G hw θ bt v) (densityMass_tiltDensity_ne_zero G hw θ bt v)
      (densityMass_tiltDensity_ne_top G hG hw hη hwexp θ bt hbt v) CL.c
      (fun φ => ∏ j, lam j (φ j + σ j - (φ v + σ v))) _ _ (fun i φ => ?_)
      (rootedD_identity_of_law_phased (tiltLaw G w θ bt v) θ CL hw (tiltLinear (gradLinear G) bt)
        (characterTranslationPhased_tiltLaw G hG hw hη hwexp θ bt hbt v) hκ hK₀ hK₁ hamp hampW
        hW1 k₀ σ)
    unfold shiftProduct
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun ϱ hϱ => ?_
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul (zz i ϱ),
      ofReal_lineFactor_one_add hw _ (hbW i ϱ hϱ), gradLinear_eq, gradLinear_eq,
      tiltLinear_apply]
  have hid0 : ∫ φ, edgeDensity G w v φ * ∏ j, lam j (φ j - φ v) =
      ∑ i, CL.c i * ∫ φ, edgeDensity G w v φ *
        shiftProduct G w c (CL.N i) (bb i) (zz i) θ (s i) 0 φ := by
    have h := rootedD_identity_of_law (offsetEdgeLaw G w 0 v) 0 CL hw
      (characterTranslation_offsetEdgeLaw G hG hw 0 v) hκ hK₀ hK₁ hamp hampW hW1 k₀ 0
    simp only [Pi.zero_apply, add_zero, zero_mul, Finset.sum_const_zero] at h
    have h' := integral_mul_eq_sum_of_densityLaw (offsetEdgeDensity_nonneg G hw 0 v)
      (measurable_offsetEdgeDensity G hw 0 v) (densityMass_offsetEdgeDensity_ne_zero G hw 0 v)
      (densityMass_offsetEdgeDensity_ne_top G hG hw 0 v) CL.c (fun φ => ∏ j, lam j (φ j - φ v))
      (fun i φ => shiftProduct G w c (CL.N i) (bb i) (zz i) θ (s i) 0 φ) _ (fun i φ => ?_) h
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
      shiftProduct G w c (CL.N i) (bb i) (zz i) θ (s i) 0 φ :=
    integral_nonneg fun φ => mul_nonneg (edgeDensity_nonneg G hw v φ)
      (shiftProduct_pos hw G (CL.N i) (bb i) (hbW i) (zz i) (hz8 i) θ (s i) 0 φ).le
  have hci := (CL.c_pos i).le
  calc _ = CL.c i * (Real.exp (-(κc * ∑ e, θ e ^ 2) -
        2 * ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2) -
        16 * Λ) *
        ∫ φ, edgeDensity G w v φ * shiftProduct G w c (CL.N i) (bb i) (zz i) θ (s i) 0 φ) := by
        ring
    _ ≤ CL.c i * ∫ φ, tiltDensity G w θ bt v φ *
        shiftProduct G w c (CL.N i) (bb i) (zz i) θ (s i) 1 φ := by
      refine mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ?_) hint0) (hbranch i)) hci
      linarith [hpack i]

end FroehlichSpencer.BKT.SOS.Tilt

end
