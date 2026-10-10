/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.GridBranch
public import FroehlichSpencer.BKT.Generic.Moment.Assembly
import Mathlib.Tactic

/-!
# T1.5-NG on the compact clock box

The compact clock analogue of `Generic/Moment/Assembly.lean`'s `integral_shift_ge_of_chargeLayer`
(FS81 , (6.10)–(6.44)). For an observable `∏_j λ_j(φ_j)` with a charge layer, a site shift `σ`
and a bond offset `θ`, `integral_gridShift_ge_of_chargeLayer` gives

`exp(−κ‖θ‖² − ε ∑_e ([∇σ(e)]²_{2π} + θ(e)²)) ∫ ρ₀ ∏_j λ_j(φ_j) dν ≤ ∫ ρ_θ ∏_j λ_j(φ_j + σ_j) dν`

on the compact box measure `ν = gridBoxMeasure n V`, with `ρ_θ = compactClockBondProduct (·) θ`.
The proof is the generic KP T1.5 pattern:
* the T1.6-NG identity under the offset measure (`gridOffset_renormalization_of_chargeLayer`), at
  `(θ, σ)` and at `(0, 0)`;
* the compact branch bound (`integral_gridShiftProduct_ge`);
* KP's packing estimate (`sum_shiftError_le`);
* averaging over the mixture weights.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open MeasureTheory Complex Finset
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-! ### The renormalized factors are real -/

omit [Fintype V] [DecidableEq V] in
theorem ofReal_lineFactor_clock_zero {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W)
    (b : E → ℝ) (hb : ∀ e, |b e| ≤ W) (x y : E → ℝ) (ph s : ℝ) :
    ((lineFactor (clockEdgeWeight β n) (clockShiftCost β n) b x y ph s 0 : ℝ) : ℂ) =
      localFactor (clockEdgeWeight β n) (clockShiftCost β n) b x ph := by
  have hw := clockEdgeWeight_isLocalStripWeight hβ hn hW
  unfold lineFactor
  rw [zero_smul, add_zero, zero_mul, add_zero]
  exact Complex.ext rfl (by rw [Complex.ofReal_im, localFactor_im_eq_zero hw.conj hw.cost_even b x hb])

omit [Fintype V] [DecidableEq V] in
theorem ofReal_lineFactor_clock_one {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W)
    (b : E → ℝ) (hb : ∀ e, |b e| ≤ W) (x y : E → ℝ) (ph r : ℝ) :
    ((lineFactor (clockEdgeWeight β n) (clockShiftCost β n) b x y ph
        (toIcoMod Real.two_pi_pos (-Real.pi) r) 1 : ℝ) : ℂ) =
      localFactor (clockEdgeWeight β n) (clockShiftCost β n) b (x + y) (ph + r) := by
  have hw := clockEdgeWeight_isLocalStripWeight hβ hn hW
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

/-! ### From the complex identity under the offset measure to a real density identity -/

omit [DecidableEq V] in
theorem integral_ofReal_gridOffset {β n : ℝ} (G : Multigraph V E) (θ : E → ℝ)
    (f : (V → ℝ) → ℝ) :
    ∫ φ, ((f φ : ℝ) : ℂ) ∂gridOffsetMeasure β n G θ =
      ((∫ φ, compactClockBondProduct G β n φ θ * f φ ∂gridBoxMeasure n V : ℝ) : ℂ) := by
  rw [integral_complex_ofReal, integral_gridOffsetMeasure]
  simp only [smul_eq_mul]

/-! ### The compact T1.5 -/

variable {G : Multigraph V E} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- **T1.5-NG on the compact clock box**, generic in the charge layer. See the module docstring.
The hypotheses are those of `integral_shift_ge_of_chargeLayer`, with the clock weight in place of
the strip weight. -/
theorem integral_gridShift_ge_of_chargeLayer (hG : G.toSimpleGraph.Connected)
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
    {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β) {W : ℝ} {M : ℝ → ℝ}
    (hlog : HasLogDerivBounds (clockEdgeWeight β n) W M)
    {κc : ℝ} (hcurv : HasCurvatureBound (clockEdgeWeight β n) κc)
    {κ κ' : ℝ} (hc : IsCostEnvelope (clockShiftCost β n) κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W)
    (hW1 : 1 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
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
        ∫ φ, compactClockBondProduct G β n φ 0 * ∏ j, lam j (φ j) ∂gridBoxMeasure n V ≤
      ∫ φ, compactClockBondProduct G β n φ θ * ∏ j, lam j (φ j + σ j) ∂gridBoxMeasure n V := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hW : 0 < W := lt_of_lt_of_le one_pos hW1
  have hb0 : 0 ≤ b := le_trans (by positivity) hb8
  have hA'W : max (amp * K₁) 1 ≤ W := max_le hampW hW1
  set w := clockEdgeWeight β n with hwdef
  set cc := clockShiftCost β n with hccdef
  set bb : Fin CL.n → (V → ℤ) → E → ℝ := fun i ϱ => G.grad (layerSpinWave CL κ amp k₀ i ϱ)
    with hbb
  set zz : Fin CL.n → (V → ℤ) → ℝ := layerActivity CL cc κ amp k₀ with hzz
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
        ∫ φ, compactClockBondProduct G β n φ 0 *
          shiftProduct G w cc (CL.R i) (bb i) (zz i) θ s 0 φ ∂gridBoxMeasure n V ≤
      ∫ φ, compactClockBondProduct G β n φ θ *
          shiftProduct G w cc (CL.R i) (bb i) (zz i) θ s 1 φ ∂gridBoxMeasure n V :=
    fun i => integral_gridShiftProduct_ge G hβ hn' hW.le hlog hcurv (CL.R i) (bb i) (zz i)
      (max (amp * K₁) 1) m (hbA i) hA'W hm0 hm1 hM (hz8 i) θ s T (hθT i)
  have hpack : ∀ i, ∑ ϱ ∈ CL.R i, 8 * |zz i ϱ| *
        (s ϱ ^ 2 + (((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((univ.filter fun e => bb i ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2) ≤
      ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2) :=
    fun i => sum_shiftError_le G hG Kv hKv hvol (CL.R i) (hne i) (hneutral i) centerOf
      (hcenter i) (hdisj i) (bb i) (hsupp i) m hm0 hm1 (zz i) b ε (hdecay i) hthr σ θ
  -- the expansions
  have hexpand : ∀ (θ' : E → ℝ) (σ' : V → ℝ) (t : ℝ)
      (hline : ∀ i, ∀ ϱ ∈ CL.R i, ∀ φ : V → ℝ,
        ((1 : ℂ) + (zz i ϱ : ℂ) * localFactor w cc (gradLinear G (layerSpinWave CL κ amp k₀ i ϱ))
          (gradLinear G φ + θ') (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ' j * (ϱ j : ℝ))) =
        ((1 + zz i ϱ * lineFactor w cc (bb i ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t
          : ℝ) : ℂ)),
      ∫ φ, compactClockBondProduct G β n φ θ' * ∏ j, lam j (φ j + σ' j) ∂gridBoxMeasure n V =
        ∑ i, CL.c i * ∫ φ, compactClockBondProduct G β n φ θ' *
          shiftProduct G w cc (CL.R i) (bb i) (zz i) θ s t φ ∂gridBoxMeasure n V := by
    intro θ' σ' t hline
    have h := gridOffset_renormalization_of_chargeLayer hn hβ θ' CL hroot κ amp k₀ σ'
    rw [integral_ofReal_gridOffset] at h
    have hR : ∀ i, ∫ φ, ∏ ϱ ∈ CL.R i, ((1 : ℂ) +
        (layerActivity CL (clockShiftCost β n) κ amp k₀ i ϱ : ℂ) *
          localFactor (clockEdgeWeight β n) (clockShiftCost β n)
            (gradLinear G (layerSpinWave CL κ amp k₀ i ϱ))
            (gradLinear G φ + θ') (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ' j * (ϱ j : ℝ)))
          ∂gridOffsetMeasure β n G θ' =
        ((∫ φ, compactClockBondProduct G β n φ θ' *
          shiftProduct G w cc (CL.R i) (bb i) (zz i) θ s t φ ∂gridBoxMeasure n V : ℝ) : ℂ) := by
      intro i
      rw [← integral_ofReal_gridOffset]
      refine integral_congr_ae (ae_of_all _ fun φ => ?_)
      simp only [shiftProduct, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun ϱ hϱ => hline i ϱ hϱ φ
    simp_rw [hR] at h
    exact_mod_cast h
  have hid1 := hexpand θ σ 1 (fun i ϱ hϱ φ => by
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul,
      ofReal_lineFactor_clock_one hβ hn' hW.le _ (hbW i ϱ hϱ), gradLinear_eq, gradLinear_eq])
  have hid0 := hexpand 0 0 0 (fun i ϱ hϱ φ => by
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul,
      ofReal_lineFactor_clock_zero hβ hn' hW.le _ (hbW i ϱ hϱ), gradLinear_eq, gradLinear_eq]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    rfl)
  simp only [Pi.zero_apply, add_zero] at hid0
  -- averaging
  rw [hid0, hid1, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hint0 : 0 ≤ ∫ φ, compactClockBondProduct G β n φ 0 *
      shiftProduct G w cc (CL.R i) (bb i) (zz i) θ s 0 φ ∂gridBoxMeasure n V :=
    integral_nonneg fun φ => mul_nonneg (compactClockBondProduct_pos G β n φ 0).le
      (shiftProduct_clock_pos hβ hn' hW.le G (CL.R i) (bb i) (hbW i) (zz i) (hz8 i) θ s 0 φ).le
  have hci := (CL.c_pos i).le
  calc _ = CL.c i * (Real.exp (-(κc * ∑ e, θ e ^ 2) -
        ε * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) (G.grad σ e) ^ 2 + θ e ^ 2)) *
        ∫ φ, compactClockBondProduct G β n φ 0 *
          shiftProduct G w cc (CL.R i) (bb i) (zz i) θ s 0 φ ∂gridBoxMeasure n V) := by ring
    _ ≤ CL.c i * ∫ φ, compactClockBondProduct G β n φ θ *
          shiftProduct G w cc (CL.R i) (bb i) (zz i) θ s 1 φ ∂gridBoxMeasure n V := by
      refine mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ?_) hint0) (hbranch i)) hci
      linarith [hpack i]

end FroehlichSpencer.BKT.Clock.Disorder

end
