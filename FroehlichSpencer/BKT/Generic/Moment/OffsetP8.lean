/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.OffsetBranch
public import FroehlichSpencer.BKT.Generic.Moment.KPLayer

/-!
# The paired-offset T1.5-NG estimate

This module assembles the offset translation identity and the paired-offset branch bound for an arbitrary
charge layer, then instantiates it on KP's even periodic square. The exponential cost is the same
as for zero background and is uniform in the background edge field `r`. The conclusion compares
the two unmarked laws at `r` and `-r` with the corresponding marked laws at `r + θ` and `-r + θ`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

variable {G : Multigraph V E} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- **Paired-offset T1.5-NG, generic in the charge layer and strip weight.** The constants in the
non-Gaussian exponential-moment estimate are independent of the background edge field `r`. -/
theorem integral_shift_ge_of_chargeLayer_oppositeOffsetPair (hG : G.toSimpleGraph.Connected)
    (v : V) (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
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
      ((edgesTouching G (G.densityDomain ρ j)).card : ℝ) ≤
        Kv * ((G.densityDiameter ρ : ℝ) + 1) ^ 2)
    (hw : IsStripWeight w W c) (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {M : ℝ → ℝ} (hlog : HasLogDerivBounds w W M) {κc : ℝ} (hcurv : HasCurvatureBound w κc)
    {κ κ' : ℝ} (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hD₁ : 0 < D₁)
    {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ max (amp * K₁) 1 → M u ≤ m)
    {a₁ a₂ b : ℝ}
    (hZ : ∀ ϱ : V → ℤ,
      Zent ϱ ≤ Real.exp (a₁ * ∑ j, |(ϱ j : ℝ)| + a₂ * A ϱ))
    (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁)
    (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂)
    {ε : ℝ} (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    (σ : V → ℝ) (r θ : E → ℝ) :
    Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
        ((∫ φ, offsetEdgeDensity G w r v φ * ∏ j, lam j (φ j)) +
          (∫ φ, offsetEdgeDensity G w (-r) v φ * ∏ j, lam j (φ j))) ≤
      (∫ φ, offsetEdgeDensity G w (r + θ) v φ * ∏ j, lam j (φ j + σ j)) +
        (∫ φ, offsetEdgeDensity G w (-r + θ) v φ * ∏ j, lam j (φ j + σ j)) := by
  classical
  have hW : 0 < W := lt_of_lt_of_le one_pos hW1
  have hb0 : 0 ≤ b := le_trans (by positivity) hb8
  have hA'W : max (amp * K₁) 1 ≤ W := max_le hampW hW1
  let bb : Fin CL.n → (V → ℤ) → E → ℝ := fun i ϱ =>
    G.grad (layerSpinWave CL κ amp k₀ i ϱ)
  let zz : Fin CL.n → (V → ℤ) → ℝ := layerActivity CL c κ amp k₀
  let s : (V → ℤ) → ℝ := fun ϱ =>
    toIcoMod Real.two_pi_pos (-Real.pi) (∑ j, σ j * (ϱ j : ℝ))
  let T : (V → ℤ) → ℝ := fun ϱ =>
    Real.sqrt (∑ e ∈ edgesTouching G (G.densityDomain ϱ (centerOf ϱ)), θ e ^ 2)
  have hbA : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, |bb i ϱ e| ≤ max (amp * K₁) 1 := by
    intro i ϱ hϱ e
    exact abs_grad_layerSpinWave_le CL hκ hK₀ hK₁ hamp k₀ i ϱ hϱ e
  have hbW : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, |bb i ϱ e| ≤ W := fun i ϱ hϱ e =>
    (hbA i ϱ hϱ e).trans hA'W
  have hneutral : ∀ i, ∀ ϱ ∈ CL.R i, ∑ j, ϱ j = 0 := by
    intro i ϱ hϱ
    rw [(hroot i).1] at hϱ
    exact (mem_neutralPart.mp hϱ).2
  have hdecay : ∀ i, ∀ ϱ ∈ CL.R i, |zz i ϱ| ≤
      Real.exp (-b * (∑ j, |(ϱ j : ℝ)| + Real.logb 2 (G.densityDiameter ϱ + 1))) := by
    intro i ϱ hϱ
    exact abs_layerActivity_le CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂
      hZ hb0 hb₁ hb₂ i ϱ hϱ (hAlog i ϱ hϱ)
  have hz8 : ∀ i, ∀ ϱ ∈ CL.R i, |zz i ϱ| ≤ 1 / 8 := by
    intro i ϱ hϱ
    exact abs_layerActivity_le_eighth hb8
      (two_le_sum_abs_of_neutral ϱ (hne i ϱ hϱ) (hneutral i ϱ hϱ))
      (Real.logb_nonneg (by norm_num) (by
        have hdiam := Nat.cast_nonneg (α := ℝ) (G.densityDiameter ϱ)
        linarith)) (hdecay i ϱ hϱ)
  have hsupp : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, bb i ϱ e ≠ 0 →
      e ∈ edgesTouching G (G.densityDomain ϱ (centerOf ϱ)) := by
    intro i ϱ hϱ e he
    exact grad_ne_zero_mem_edgesTouching G
      ((layerSpinWave_clauses CL κ amp k₀ i).2.1 ϱ hϱ) he
  have hθT : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, bb i ϱ e ≠ 0 → |θ e| ≤ T ϱ := by
    intro i ϱ hϱ e he
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun e => θ e ^ 2)
      (fun _ _ => sq_nonneg _) (hsupp i ϱ hϱ e he))

  /- The translation identity is used at each endpoint offset. -/
  have hIdent0 : ∀ r₀ : E → ℝ,
      ∫ φ, offsetEdgeDensity G w r₀ v φ * ∏ j, lam j (φ j) =
        ∑ i, CL.c i * ∫ φ, offsetEdgeDensity G w r₀ v φ *
          offsetShiftProduct G w c (CL.R i) (bb i) (zz i) r₀ θ s 0 φ := by
    intro r₀
    have hP6 := offsetEdgeLaw_renormalization_identity hG v r₀ CL hroot hw hκ hK₀ hK₁
      hamp hampW hW1 k₀ 0
    simp only [Pi.zero_apply, add_zero, zero_mul, Finset.sum_const_zero] at hP6
    simp only [offsetEdgeLaw] at hP6
    have hLeb := integral_mul_eq_sum_of_densityLaw
      (offsetEdgeDensity_nonneg G hw r₀ v)
      (measurable_offsetEdgeDensity G hw r₀ v)
      (densityMass_offsetEdgeDensity_ne_zero G hw r₀ v)
      (densityMass_offsetEdgeDensity_ne_top G hG hw r₀ v) CL.c
      (fun φ => ∏ j, lam j (φ j))
      (fun i φ => offsetShiftProduct G w c (CL.R i) (bb i) (zz i) r₀ θ s 0 φ)
      _
      (fun i φ => by
        unfold offsetShiftProduct
        rw [Complex.ofReal_prod]
        refine Finset.prod_congr rfl fun ϱ hϱ => ?_
        rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul (zz i ϱ),
          ofReal_lineFactor_zero hw (bb i ϱ) (fun e => hbW i ϱ hϱ e)
            (G.grad φ + r₀) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ),
          gradLinear_eq, gradLinear_eq]
        rfl) hP6
    exact hLeb

  have hIdent1 (r₀ : E → ℝ) :
      ∫ φ, offsetEdgeDensity G w (r₀ + θ) v φ * ∏ j, lam j (φ j + σ j) =
        ∑ i, CL.c i * ∫ φ, offsetEdgeDensity G w (r₀ + θ) v φ *
          offsetShiftProduct G w c (CL.R i) (bb i) (zz i) r₀ θ s 1 φ := by
    have hP6 := offsetEdgeLaw_renormalization_identity hG v (r₀ + θ) CL hroot hw hκ hK₀ hK₁
      hamp hampW hW1 k₀ σ
    simp only [offsetEdgeLaw] at hP6
    have hLeb := integral_mul_eq_sum_of_densityLaw
      (offsetEdgeDensity_nonneg G hw (r₀ + θ) v)
      (measurable_offsetEdgeDensity G hw (r₀ + θ) v)
      (densityMass_offsetEdgeDensity_ne_zero G hw (r₀ + θ) v)
      (densityMass_offsetEdgeDensity_ne_top G hG hw (r₀ + θ) v) CL.c
      (fun φ => ∏ j, lam j (φ j + σ j))
      (fun i φ => offsetShiftProduct G w c (CL.R i) (bb i) (zz i) r₀ θ s 1 φ)
      _
      (fun i φ => by
        unfold offsetShiftProduct
        rw [Complex.ofReal_prod]
        refine Finset.prod_congr rfl fun ϱ hϱ => ?_
        rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul (zz i ϱ),
          ofReal_lineFactor_one hw (bb i ϱ) (fun e => hbW i ϱ hϱ e)
            (G.grad φ + r₀) θ (∑ j, φ j * (ϱ j : ℝ))
            (∑ j, σ j * (ϱ j : ℝ)),
          gradLinear_eq, gradLinear_eq]
        have hgrad : G.grad φ + r₀ + θ = G.grad φ + (r₀ + θ) := by
          funext e
          simp only [Pi.add_apply]
          ring
        rw [hgrad]
        rfl) hP6
    exact hLeb

  have hbranch : ∀ i,
      Real.exp (-(κc * ∑ e, θ e ^ 2 + ∑ ϱ ∈ CL.R i, 8 * |zz i ϱ| *
        (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
        ((∫ φ, offsetEdgeDensity G w r v φ *
            offsetShiftProduct G w c (CL.R i) (bb i) (zz i) r θ s 0 φ) +
          (∫ φ, offsetEdgeDensity G w (-r) v φ *
            offsetShiftProduct G w c (CL.R i) (bb i) (zz i) (-r) θ s 0 φ)) ≤
      (∫ φ, offsetEdgeDensity G w (r + θ) v φ *
          offsetShiftProduct G w c (CL.R i) (bb i) (zz i) r θ s 1 φ) +
        (∫ φ, offsetEdgeDensity G w (-r + θ) v φ *
          offsetShiftProduct G w c (CL.R i) (bb i) (zz i) (-r) θ s 1 φ) := by
    intro i
    exact integral_shiftProduct_ge_oppositeOffsetPair hG v hw hW hnzero hlog hcurv
      (CL.R i) (bb i) (zz i) (max (amp * K₁) 1) m
      (hbA i) hA'W hm0 hm1 hM (hz8 i) r θ s T (hθT i)

  have hpack : ∀ i, ∑ ϱ ∈ CL.R i, 8 * |zz i ϱ| *
        (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2) ≤
      ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2) := by
    intro i
    exact sum_shiftError_le G hG Kv hKv hvol (CL.R i) (hne i) (hneutral i) centerOf
      (hcenter i) (hdisj i) (bb i) (hsupp i) m hm0 hm1 (zz i) b ε (hdecay i) hthr σ θ

  let A₀ : Fin CL.n → ℝ := fun i =>
    ∫ φ, offsetEdgeDensity G w r v φ * offsetShiftProduct G w c (CL.R i) (bb i) (zz i) r θ s 0 φ
  let A₁ : Fin CL.n → ℝ := fun i =>
    ∫ φ, offsetEdgeDensity G w (-r) v φ * offsetShiftProduct G w c (CL.R i) (bb i) (zz i) (-r) θ s 0 φ
  let B₀ : Fin CL.n → ℝ := fun i =>
    ∫ φ, offsetEdgeDensity G w (r + θ) v φ * offsetShiftProduct G w c (CL.R i) (bb i) (zz i) r θ s 1 φ
  let B₁ : Fin CL.n → ℝ := fun i =>
    ∫ φ, offsetEdgeDensity G w (-r + θ) v φ * offsetShiftProduct G w c (CL.R i) (bb i) (zz i) (-r) θ s 1 φ
  have hterm : ∀ i, Real.exp (-(κc * ∑ e, θ e ^ 2) -
      ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
      (A₀ i + A₁ i) ≤ B₀ i + B₁ i := by
    intro i
    have hbase0 : 0 ≤ A₀ i + A₁ i := by
      refine add_nonneg ?_ ?_
      · exact integral_nonneg fun φ => mul_nonneg
          (offsetEdgeDensity_nonneg G hw r v φ)
          (offsetShiftProduct_pos hw G (CL.R i) (bb i) (hbW i) (zz i) (hz8 i)
            r θ s 0 φ).le
      · exact integral_nonneg fun φ => mul_nonneg
          (offsetEdgeDensity_nonneg G hw (-r) v φ)
          (offsetShiftProduct_pos hw G (CL.R i) (bb i) (hbW i) (zz i) (hz8 i)
            (-r) θ s 0 φ).le
    have hExp : Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) ≤
      Real.exp (-(κc * ∑ e, θ e ^ 2 + ∑ ϱ ∈ CL.R i, 8 * |zz i ϱ| *
        (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) := by
      apply Real.exp_le_exp.mpr
      linarith [hpack i]
    have hbranch' : Real.exp (-(κc * ∑ e, θ e ^ 2 + ∑ ϱ ∈ CL.R i, 8 * |zz i ϱ| *
        (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
        (A₀ i + A₁ i) ≤ B₀ i + B₁ i := by
      simpa only [A₀, A₁, B₀, B₁] using hbranch i
    calc
      _ ≤ Real.exp (-(κc * ∑ e, θ e ^ 2 + ∑ ϱ ∈ CL.R i, 8 * |zz i ϱ| *
          (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
            ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
          (A₀ i + A₁ i) := mul_le_mul_of_nonneg_right hExp hbase0
      _ ≤ B₀ i + B₁ i := hbranch'

  have hsum : ∑ i, CL.c i *
        (Real.exp (-(κc * ∑ e, θ e ^ 2) -
          ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
          (A₀ i + A₁ i)) ≤ ∑ i, CL.c i * (B₀ i + B₁ i) :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hterm i) (CL.c_pos i).le

  rw [hIdent0 r, hIdent0 (-r), hIdent1 r, hIdent1 (-r)]
  change Real.exp (-(κc * ∑ e, θ e ^ 2) -
      ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
      ((∑ i, CL.c i * A₀ i) + (∑ i, CL.c i * A₁ i)) ≤
    (∑ i, CL.c i * B₀ i) + (∑ i, CL.c i * B₁ i)
  have hleft : Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
      ((∑ i, CL.c i * A₀ i) + (∑ i, CL.c i * A₁ i)) =
      ∑ i, CL.c i * (Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
        (A₀ i + A₁ i)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    ring
  have hright : (∑ i, CL.c i * B₀ i) + (∑ i, CL.c i * B₁ i) =
      ∑ i, CL.c i * (B₀ i + B₁ i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    ring
  rw [hleft, hright]
  exact hsum

/-! ## KP's square-periodic instance -/

/-- **Paired-offset T1.5-NG on KP's periodic square**. This is the periodic KP-layer instance of
`integral_shift_ge_of_chargeLayer_oppositeOffsetPair`; its constants are independent of the fixed
background offset `r`. -/
theorem integral_shift_ge_squarePeriodic_oppositeOffsetPair {L : ℕ} (hL : 1 < L)
    (hEven : Even L) (lam : Fin L × Fin L → ℝ → ℝ)
    (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hNq : ∀ j, 0 < Nq j)
    (hcut : ∀ j q, Nq j < q → lamHat j q = 0)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hζpos : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) {a₁ : ℝ}
    (hleaf : ∀ j q, mixtureLeaf Nq lamHat ζ j q ≤ Real.exp (a₁ * q))
    (v : Fin L × Fin L) {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
    (hw : IsStripWeight w W c) (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {M : ℝ → ℝ} (hlog : HasLogDerivBounds w W M) {κc : ℝ}
    (hcurv : HasCurvatureBound w κc) {κ κ' : ℝ}
    (hc : IsCostEnvelope c κ κ' W) (hκ : 0 < κ) {amp : ℝ} (hamp : 0 ≤ amp)
    (hampW : amp * 28 ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ max (amp * 28) 1 → M u ≤ m)
    {b : ℝ} (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁)
    (hb₂ : b ≤ amp / (8 * kpD₁) - 200) {ε : ℝ}
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      2 * (8 * (64 + 2 * 64 ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ ε)
    (σ : Fin L × Fin L → ℝ) (r θ : (SquarePeriodicEdge L) → ℝ) :
    Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) ((squarePeriodic L).grad σ e) ^ 2 +
          θ e ^ 2)) *
        ((∫ φ, offsetEdgeDensity (squarePeriodic L) w r v φ * ∏ j, lam j (φ j)) +
          (∫ φ, offsetEdgeDensity (squarePeriodic L) w (-r) v φ * ∏ j, lam j (φ j))) ≤
      (∫ φ, offsetEdgeDensity (squarePeriodic L) w (r + θ) v φ *
          ∏ j, lam j (φ j + σ j)) +
        (∫ φ, offsetEdgeDensity (squarePeriodic L) w (-r + θ) v φ *
          ∏ j, lam j (φ j + σ j)) := by
  classical
  let Λ := squarePeriodic L
  have hΛ : Λ.toSimpleGraph.Connected := squarePeriodic_connected L hL
  have hdist : ∀ x y, latticeDistance .periodic L x y = Λ.toSimpleGraph.dist x y :=
    fun _ _ => rfl
  have hB : SpinWaves.BipartiteDegreeFour Λ :=
    SpinWaves.squarePeriodicBipartiteDegreeFour L hEven hL
  have h46 : SpinWaves.L46Step .periodic Λ :=
    (SpinWaves.BoundaryShellPacking.l46Statement_holds L hL).2 hEven
  have h21 : Reduction.P21Step .periodic L kpD₁ := (p21Step_kpD₁ hL).2 hEven
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → Λ.IsDensityCenter ϱ j := by
    intro ϱ
    by_cases h : ϱ = 0
    · exact ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), fun h' => absurd h h'⟩
    · obtain ⟨j, hj⟩ := Λ.exists_isDensityCenter ϱ h
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  obtain ⟨CL, hCL⟩ := exists_kpChargeLayer .periodic hL (Or.inr hEven) Λ hΛ hdist hB
    h46 kpD₁_pos.le h21 centerOf hcenter lam Nq lamHat ζ hNq hcut hlam hζpos hζsum
  have hne : ∀ i, ∀ ϱ ∈ CL.R i, ϱ ≠ 0 := fun i ϱ hϱ => by
    rw [(hCL i).1] at hϱ
    exact (hCL i).2.2.1.1 ϱ (mem_neutralPart.mp hϱ).1
  have hdisj : ∀ i, ∀ ϱ₁ ∈ CL.R i, ∀ ϱ₂ ∈ CL.R i, ϱ₁ ≠ ϱ₂ →
      ∀ k : ℕ, 1 ≤ k →
        Λ.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
        Λ.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
        ∀ j₁ j₂, Λ.IsDensityCenter ϱ₁ j₁ → Λ.IsDensityCenter ϱ₂ j₂ →
          Λ.densityDomain ϱ₁ j₁ ∩ Λ.densityDomain ϱ₂ j₂ = ∅ := by
    intro i ϱ₁ h₁ ϱ₂ h₂ hne' k hk hd₁ hd₂ j₁ j₂ hj₁ hj₂
    rw [(hCL i).1] at h₁ h₂
    exact Reduction.densityDomain_inter_eq_empty .periodic Λ hΛ hdist
      ((hCL i).2.2.2.1 ϱ₁ (mem_neutralPart.mp h₁).1 ϱ₂ (mem_neutralPart.mp h₂).1 hne')
      hk hd₁ hd₂ hj₁ hj₂
  have hAlog : ∀ i, ∀ ϱ ∈ CL.R i,
      Real.logb 2 (Λ.densityDiameter ϱ + 1) ≤ chargeCoverCost .periodic L ϱ := by
    intro i ϱ hϱ
    have h := (h21 (fun ϱ k => sharedMinimumSquareCover .periodic L ϱ (by omega) k)
      ϱ (hne i ϱ hϱ)).1
    rwa [chargeDiameter_eq_densityDiameter .periodic Λ hdist] at h
  exact integral_shift_ge_of_chargeLayer_oppositeOffsetPair hΛ v CL
    (fun i => ⟨(hCL i).1, (hCL i).2.1⟩) hne
    (fun i ϱ hϱ => hcenter ϱ (hne i ϱ hϱ)) hdisj hAlog (by norm_num)
    (card_edgesTouching_densityDomain_squarePeriodic_le hL hEven) hw hnzero hlog hcurv hc hκ
    (by norm_num) (by norm_num) kpD₁_pos hamp hampW hW1 hk₀ hexp hquad₁ hquad₂ hm0 hm1 hM
    (a₂ := 0) (fun ϱ => (prod_mixtureLeaf_le Nq lamHat ζ hζpos hleaf ϱ).trans_eq (by
      rw [zero_mul, add_zero])) hb8 hb₁ (by rw [sub_zero]; exact hb₂) hthr σ r θ

/-! ## KP's square-periodic instance -/

end FroehlichSpencer.BKT.Generic

end
