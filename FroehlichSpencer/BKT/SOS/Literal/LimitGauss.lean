/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.Cutoff
public import FroehlichSpencer.BKT.SOS.Literal.Extended
public import Mathlib.Analysis.Convolution

/-!
# Gaussian fields on the box: completing the square, Thomson, Fourier positivity (the comb-inserted SOS construction)

For bond precisions `p_e > 0` the quadratic form `Q_p(φ) = Σ_e p_e (∇φ(e))²` on the zero-exterior
box is positive definite.

* `exists_gaussB_eq`: for every `f` there is `b` with `2 B_p(b, ψ) = ⟨f, ψ⟩` for all `ψ`
  (`b = (2M_p)⁻¹ f`), so `⟨f, φ⟩ − Q_p(φ) = Q_p(b) − Q_p(φ − b)` (`sum_mul_sub_gaussQ`).
* `gaussQ_le_of_flow` (Thomson): if `Σ_e θ_e ∇ψ(e) = ⟨f, ψ⟩` for all `ψ`, then
  `Q_p(b) ≤ Σ_e θ_e² / (4p_e)`.
* `exists_gaussChar_schwartz`: `φ ↦ e^{−Q_p(φ−b)} e^{2πi Σ_e ξ_e ∇φ(e)}` is a Schwartz function.
* `exists_integral_char_gauss_eq_nonneg`: the Fourier transform of `e^{−Q_p}` at any linear
  functional is real and nonnegative (`e^{−Q} = C⁻¹ e^{−2Q} * e^{−2Q}`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Complex Filter Topology
open scoped SchwartzMap Real
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.SOS.Roughening
open FroehlichSpencer.BKT.Rotator (multiEuclideanFourierCoefficient)

variable {L : ℕ}

/-! ## The quadratic form -/

/-- The quadratic form `Q_p(φ) = Σ_e p_e (∇φ(e))²`. -/
def gaussQ (p : SquareZeroBond L → ℝ) (φ : Site L → ℝ) : ℝ :=
  ∑ e, p e * pinnedGrad L φ e ^ 2

/-- The bilinear form of `Q_p`. -/
def gaussB (p : SquareZeroBond L → ℝ) (φ ψ : Site L → ℝ) : ℝ :=
  ∑ e, p e * (pinnedGrad L φ e * pinnedGrad L ψ e)

theorem gaussB_self (p : SquareZeroBond L → ℝ) (φ : Site L → ℝ) :
    gaussB p φ φ = gaussQ p φ := by
  unfold gaussB gaussQ
  exact Finset.sum_congr rfl fun e _ => by ring

theorem gaussB_comm (p : SquareZeroBond L → ℝ) (φ ψ : Site L → ℝ) :
    gaussB p φ ψ = gaussB p ψ φ := by
  unfold gaussB
  exact Finset.sum_congr rfl fun e _ => by ring

theorem gaussQ_sub (p : SquareZeroBond L → ℝ) (φ b : Site L → ℝ) :
    gaussQ p (φ - b) = gaussQ p φ - 2 * gaussB p φ b + gaussQ p b := by
  unfold gaussQ gaussB
  simp only [map_sub, Pi.sub_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem gaussQ_nonneg {p : SquareZeroBond L → ℝ} (hp : ∀ e, 0 ≤ p e) (φ : Site L → ℝ) :
    0 ≤ gaussQ p φ :=
  Finset.sum_nonneg fun e _ => mul_nonneg (hp e) (sq_nonneg _)

theorem gaussQ_neg (p : SquareZeroBond L → ℝ) (φ : Site L → ℝ) : gaussQ p (-φ) = gaussQ p φ := by
  unfold gaussQ
  simp only [map_neg, Pi.neg_apply, neg_sq]

theorem gaussQ_const_mul (c : ℝ) (p : SquareZeroBond L → ℝ) (φ : Site L → ℝ) :
    gaussQ (fun e => c * p e) φ = c * gaussQ p φ := by
  unfold gaussQ
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem gaussQ_smul (p : SquareZeroBond L → ℝ) (a : ℝ) (φ : Site L → ℝ) :
    gaussQ p (a • φ) = a ^ 2 * gaussQ p φ := by
  unfold gaussQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem eq_zero_of_gaussQ_eq_zero (hL : 1 < L) {p : SquareZeroBond L → ℝ} (hp : ∀ e, 0 < p e)
    {φ : Site L → ℝ} (h : gaussQ p φ = 0) : φ = 0 := by
  have hz : ∀ e, pinnedGrad L φ e = 0 := by
    intro e
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun e _ =>
      mul_nonneg (hp e).le (sq_nonneg (pinnedGrad L φ e))).mp h e (Finset.mem_univ e)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (hp e).ne'
    · exact pow_eq_zero_iff two_ne_zero |>.mp h1
  refine pinnedGrad_injective hL ?_
  funext e
  rw [hz e, map_zero, Pi.zero_apply]

/-- `B_p(b, ·)` as a linear functional. -/
def gaussBFun (p : SquareZeroBond L → ℝ) (b : Site L → ℝ) : (Site L → ℝ) →ₗ[ℝ] ℝ :=
  (Fintype.linearCombination ℝ fun e => p e * pinnedGrad L b e) ∘ₗ pinnedGrad L

theorem gaussBFun_apply (p : SquareZeroBond L → ℝ) (b ψ : Site L → ℝ) :
    gaussBFun p b ψ = gaussB p b ψ := by
  unfold gaussBFun gaussB
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun e _ => by rw [smul_eq_mul]; ring

theorem gaussB_eq_sum_single (p : SquareZeroBond L → ℝ) (b ψ : Site L → ℝ) :
    gaussB p b ψ = ∑ v, ψ v * gaussB p b (Pi.single v 1) := by
  rw [← gaussBFun_apply, LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [smul_eq_mul, ← gaussBFun_apply]
  congr 2
  funext w
  rw [Pi.single_apply]
  exact if_congr eq_comm rfl rfl

/-- The operator `b ↦ (v ↦ 2 B_p(b, 1_v))`, i.e. `2M_p`. -/
def gaussOp (p : SquareZeroBond L → ℝ) : (Site L → ℝ) →ₗ[ℝ] (Site L → ℝ) where
  toFun b v := 2 * gaussB p b (Pi.single v 1)
  map_add' b c := by
    funext v
    simp only [gaussB, map_add, Pi.add_apply]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun e _ => by ring
  map_smul' a b := by
    funext v
    simp only [gaussB, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring

/-- **Completing the square**: there is `b` with `2 B_p(b, ψ) = ⟨f, ψ⟩` for all `ψ`. -/
theorem exists_gaussB_eq (hL : 1 < L) {p : SquareZeroBond L → ℝ} (hp : ∀ e, 0 < p e)
    (f : Site L → ℝ) : ∃ b : Site L → ℝ, ∀ ψ, 2 * gaussB p b ψ = ∑ v, f v * ψ v := by
  have hinj : Function.Injective (gaussOp p) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have hQ : gaussQ p b = 0 := by
      rw [← gaussB_self, gaussB_eq_sum_single]
      refine Finset.sum_eq_zero fun v _ => ?_
      have := congrFun hb v
      simp only [gaussOp, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      rw [show gaussB p b (Pi.single v 1) = 0 by linarith, mul_zero]
    exact eq_zero_of_gaussQ_eq_zero hL hp hQ
  obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.mp hinj f
  refine ⟨b, fun ψ => ?_⟩
  rw [gaussB_eq_sum_single, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have := congrFun hb v
  simp only [gaussOp, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [← this]
  ring

/-- `⟨f, φ⟩ − Q_p(φ) = Q_p(b) − Q_p(φ − b)`. -/
theorem sum_mul_sub_gaussQ {p : SquareZeroBond L → ℝ} {f b : Site L → ℝ}
    (hb : ∀ ψ, 2 * gaussB p b ψ = ∑ v, f v * ψ v) (φ : Site L → ℝ) :
    ∑ v, f v * φ v - gaussQ p φ = gaussQ p b - gaussQ p (φ - b) := by
  rw [gaussQ_sub, ← hb φ, gaussB_comm]
  ring

/-- **Thomson's principle**: a flow `θ` with divergence `f` bounds `Q_p(b) ≤ Σ_e θ_e²/(4p_e)`. -/
theorem gaussQ_le_of_flow {p : SquareZeroBond L → ℝ} (hp : ∀ e, 0 < p e)
    {f b : Site L → ℝ} {θ : SquareZeroBond L → ℝ}
    (hθ : ∀ ψ, ∑ e, θ e * pinnedGrad L ψ e = ∑ v, f v * ψ v)
    (hb : ∀ ψ, 2 * gaussB p b ψ = ∑ v, f v * ψ v) :
    gaussQ p b ≤ ∑ e, θ e ^ 2 / (4 * p e) := by
  have h1 : 2 * gaussQ p b = ∑ e, θ e * pinnedGrad L b e := by rw [← gaussB_self, hb, hθ]
  have h2 : ∑ e, θ e * pinnedGrad L b e ≤
      ∑ e, (θ e ^ 2 / (4 * p e) + p e * pinnedGrad L b e ^ 2) := by
    refine Finset.sum_le_sum fun e _ => ?_
    have hpe := hp e
    have h0 : 0 ≤ p e * (pinnedGrad L b e - θ e / (2 * p e)) ^ 2 := by positivity
    have key : p e * (pinnedGrad L b e - θ e / (2 * p e)) ^ 2 =
        θ e ^ 2 / (4 * p e) + p e * pinnedGrad L b e ^ 2 - θ e * pinnedGrad L b e := by
      field_simp
      ring
    linarith
  rw [Finset.sum_add_distrib] at h2
  have h3 : gaussQ p b = ∑ e, p e * pinnedGrad L b e ^ 2 := rfl
  linarith

/-! ## Schwartz Gaussian characters -/

theorem exists_gaussChar_schwartz_one {a : ℝ} (ha : 0 < a) (s ξ : ℝ) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ t : ℝ,
      g t = cexp (-(a : ℂ) * ((t : ℂ) - s) ^ 2) * cexp (2 * π * I * ξ * t) := by
  refine exists_schwartz_of_strip
    (F := fun z => cexp (-(a : ℂ) * (z - s) ^ 2) * cexp (2 * π * I * ξ * z)) (R₀ := 1) (r := 1 / 2)
    (η := 1)
    (K := Real.exp (a / 4 + π * |ξ| + |s| + 1 / (4 * a))) (by norm_num) (by norm_num)
    one_pos (fun z _ => by fun_prop) (fun t u hu => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add, one_mul]
  have hre1 : (-(a : ℂ) * (((t : ℂ) + (u : ℂ) * I) - s) ^ 2).re =
      -(a * ((t - s) ^ 2 - u ^ 2)) := by
    simp only [sq, mul_re, neg_re, ofReal_re, ofReal_im, sub_re, add_re, mul_im, I_re, I_im,
      sub_im, add_im, neg_im]
    ring
  have hre2 : (2 * π * I * ξ * ((t : ℂ) + (u : ℂ) * I)).re = -(2 * π * ξ * u) := by
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im, re_ofNat,
      im_ofNat]
    ring
  rw [hre1, hre2, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hu2 : u ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hu
    nlinarith
  have hξu : -(2 * π * ξ * u) ≤ π * |ξ| := by
    have h1 : -(ξ * u) ≤ |ξ| * |u| := by
      rw [← abs_mul]; exact neg_le_abs _
    have h2 : |ξ| * |u| ≤ |ξ| * (1 / 2) := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    nlinarith [Real.pi_pos]
  have hts : |t| - |s| - 1 / (4 * a) ≤ a * (t - s) ^ 2 := by
    have h1 : |t| - |s| ≤ |t - s| := abs_sub_abs_le_abs_sub t s
    have h2 : 0 ≤ a * (|t - s| - 1 / (2 * a)) ^ 2 := by positivity
    have h3 : a * (|t - s| - 1 / (2 * a)) ^ 2 = a * (t - s) ^ 2 - |t - s| + 1 / (4 * a) := by
      rw [sub_sq, mul_add, mul_sub, sq_abs]
      field_simp
      ring
    linarith
  nlinarith

/-- The Gaussian character `e^{−Q_p(φ−b)} e^{2πi Σ_e ξ_e ∇φ(e)}`. -/
def gaussChar (p : SquareZeroBond L → ℝ) (b : Site L → ℝ) (ξ : SquareZeroBond L → ℝ)
    (φ : Site L → ℝ) : ℂ :=
  ((Real.exp (-gaussQ p (φ - b)) : ℝ) : ℂ) *
    cexp (2 * π * I * ∑ e, ((ξ e : ℂ) * (pinnedGrad L φ e : ℂ)))

/-- **The Gaussian characters are Schwartz.** -/
theorem exists_gaussChar_schwartz (hL : 1 < L) {p : SquareZeroBond L → ℝ} (hp : ∀ e, 0 < p e)
    (b : Site L → ℝ) (ξ : SquareZeroBond L → ℝ) :
    ∃ F : 𝓢(Site L → ℝ, ℂ), ∀ φ, F φ = gaussChar p b ξ φ := by
  classical
  choose g hg using fun e => exists_gaussChar_schwartz_one (hp e) (pinnedGrad L b e) (ξ e)
  obtain ⟨Fb, hFb⟩ := exists_schwartz_pi_product_family g
  let grad : (Site L → ℝ) →L[ℝ] (SquareZeroBond L → ℝ) := (pinnedGrad L).toContinuousLinearMap
  obtain ⟨K, -, hanti⟩ :=
    (pinnedGrad L).injective_iff_antilipschitz.mp (pinnedGrad_injective hL)
  have hanti' : AntilipschitzWith K grad := hanti
  refine ⟨(SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti') Fb,
    fun φ => ?_⟩
  rw [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply, hFb]
  simp only [grad, LinearMap.coe_toContinuousLinearMap', hg]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, ← Complex.exp_sum, gaussChar,
    Complex.ofReal_exp, Finset.mul_sum]
  congr 1
  · congr 1
    unfold gaussQ
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_sub, Pi.sub_apply]
    push_cast
    ring
  · congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    ring

theorem gaussChar_zero_zero (p : SquareZeroBond L → ℝ) (φ : Site L → ℝ) :
    gaussChar p 0 0 φ = ((Real.exp (-gaussQ p φ) : ℝ) : ℂ) := by
  simp [gaussChar]

theorem integrable_exp_neg_gaussQ (hL : 1 < L) {p : SquareZeroBond L → ℝ} (hp : ∀ e, 0 < p e) :
    Integrable fun φ : Site L → ℝ => Real.exp (-gaussQ p φ) := by
  obtain ⟨F, hF⟩ := exists_gaussChar_schwartz hL hp 0 0
  refine F.integrable.norm.congr (Eventually.of_forall fun φ => ?_)
  simp only [hF, gaussChar_zero_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem continuous_gaussQ (p : SquareZeroBond L → ℝ) : Continuous (gaussQ (L := L) p) := by
  unfold gaussQ
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  exact continuous_finsetSum _ fun e _ =>
    continuous_const.mul (((continuous_apply e).comp hg).pow 2)

theorem gaussB_smul_right (p : SquareZeroBond L → ℝ) (a : ℝ) (φ ψ : Site L → ℝ) :
    gaussB p φ (a • ψ) = a * gaussB p φ ψ := by
  unfold gaussB
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The parallelogram identity `2Q(φ − z) + 2Q(z) = Q(φ) + 4Q(z − φ/2)`. -/
theorem gaussQ_parallelogram (p : SquareZeroBond L → ℝ) (φ z : Site L → ℝ) :
    2 * gaussQ p (φ - z) + 2 * gaussQ p z =
      gaussQ p φ + 4 * gaussQ p (z - (1 / 2 : ℝ) • φ) := by
  rw [gaussQ_sub, gaussQ_sub, gaussQ_smul, gaussB_smul_right, gaussB_comm p z φ]
  ring

/-- **The convolution square**: `∫ e^{−2Q(φ−z)} e^{−2Q(z)} dz = C e^{−Q(φ)}`. -/
theorem integral_gauss_conv (p : SquareZeroBond L → ℝ) (φ : Site L → ℝ) :
    ∫ z, Real.exp (-gaussQ (fun e => 2 * p e) (φ - z)) * Real.exp (-gaussQ (fun e => 2 * p e) z) =
      (∫ w, Real.exp (-gaussQ (fun e => 4 * p e) w)) * Real.exp (-gaussQ p φ) := by
  have hpt : ∀ z, Real.exp (-gaussQ (fun e => 2 * p e) (φ - z)) *
      Real.exp (-gaussQ (fun e => 2 * p e) z) =
      Real.exp (-gaussQ (fun e => 4 * p e) (z - (1 / 2 : ℝ) • φ)) * Real.exp (-gaussQ p φ) := by
    intro z
    rw [← Real.exp_add, ← Real.exp_add, gaussQ_const_mul, gaussQ_const_mul, gaussQ_const_mul]
    congr 1
    have := gaussQ_parallelogram p φ z
    linarith
  simp_rw [hpt]
  rw [integral_mul_const]
  congr 1
  exact integral_sub_right_eq_self (fun w => Real.exp (-gaussQ (fun e => 4 * p e) w)) _

theorem integrable_gauss_prod (hL : 1 < L) {p : SquareZeroBond L → ℝ} (hp : ∀ e, 0 < p e) :
    Integrable (fun q : (Site L → ℝ) × (Site L → ℝ) =>
      Real.exp (-gaussQ p (q.1 - q.2)) * Real.exp (-gaussQ p q.2)) (volume.prod volume) := by
  have h := MeasureTheory.Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_exp_neg_gaussQ hL hp) (integrable_exp_neg_gaussQ hL hp)
  refine h.congr (Eventually.of_forall fun q => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  ring

/-- **Fourier positivity of the Gaussian**: `∫ e^{iλ(ψ)} e^{−Q_p(ψ)} dψ` is real and `≥ 0` for every
linear functional `λ`. -/
theorem exists_integral_char_gauss_eq_nonneg (hL : 1 < L) {p : SquareZeroBond L → ℝ}
    (hp : ∀ e, 0 < p e) (lam : (Site L → ℝ) →ₗ[ℝ] ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ∫ ψ, cexp (((lam ψ : ℝ) : ℂ) * I) * ((Real.exp (-gaussQ p ψ) : ℝ) : ℂ) = r := by
  have hp2 : ∀ e, 0 < 2 * p e := fun e => by linarith [hp e]
  have hp4 : ∀ e, 0 < 4 * p e := fun e => by linarith [hp e]
  set g : (Site L → ℝ) → ℝ := fun ψ => Real.exp (-gaussQ (fun e => 2 * p e) ψ) with hg
  have hgi : Integrable g := integrable_exp_neg_gaussQ hL hp2
  have hgc : Continuous g := Real.continuous_exp.comp (continuous_gaussQ _).neg
  set C : ℝ := ∫ w, Real.exp (-gaussQ (fun e => 4 * p e) w) with hC
  have hCpos : 0 < C := by
    rw [hC, integral_pos_iff_support_of_nonneg (fun w => (Real.exp_pos _).le)
      (integrable_exp_neg_gaussQ hL hp4)]
    have hsupp : Function.support (fun w : Site L → ℝ =>
        Real.exp (-gaussQ (fun e => 4 * p e) w)) = Set.univ :=
      Set.eq_univ_of_forall fun w => (Real.exp_pos _).ne'
    rw [hsupp, Measure.measure_univ_pos]
    exact NeZero.ne _
  set χ : (Site L → ℝ) → ℂ := fun ψ => cexp (((lam ψ : ℝ) : ℂ) * I) with hχ
  have hχn : ∀ ψ, ‖χ ψ‖ = 1 := fun ψ => by
    simp only [hχ, Complex.norm_exp, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_zero, Real.exp_zero]
  have hχc : Continuous χ := by
    have : Continuous lam := lam.continuous_of_finiteDimensional
    fun_prop
  have hχadd : ∀ ψ z, χ (ψ + z) = χ ψ * χ z := fun ψ z => by
    simp only [hχ, map_add, ofReal_add, add_mul, Complex.exp_add]
  -- the transform of `g` is real
  set gh : ℂ := ∫ ψ, χ ψ * (g ψ : ℂ) with hgh
  have hgh_real : (starRingEnd ℂ) gh = gh := by
    rw [hgh, ← integral_conj]
    have hneg := (FroehlichSpencer.BKT.Generic.measurePreserving_neg_pi (V := Site L)).integral_comp
      (Homeomorph.neg (Site L → ℝ)).measurableEmbedding (fun ψ => χ ψ * (g ψ : ℂ))
    rw [← hneg]
    refine integral_congr_ae (Eventually.of_forall fun ψ => ?_)
    simp only [hχ, hg, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, ofReal_neg,
      gaussQ_neg, Complex.conj_I]
    congr 2
    ring
  -- Fubini
  have hprodR := integrable_gauss_prod hL hp2
  have hprod : Integrable (fun q : (Site L → ℝ) × (Site L → ℝ) =>
      χ q.1 * ((g (q.1 - q.2) * g q.2 : ℝ) : ℂ)) (volume.prod volume) := by
    refine hprodR.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun q => ?_)
    · exact (hχc.comp continuous_fst).mul (Complex.continuous_ofReal.comp
        ((hgc.comp (continuous_fst.sub continuous_snd)).mul (hgc.comp continuous_snd)))
    · rw [norm_mul, hχn, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
  have hconv : ∀ ψ, ((Real.exp (-gaussQ p ψ) : ℝ) : ℂ) =
      ((C⁻¹ : ℝ) : ℂ) * ∫ z, ((g (ψ - z) * g z : ℝ) : ℂ) := by
    intro ψ
    rw [integral_complex_ofReal, integral_gauss_conv, ← Complex.ofReal_mul, ← mul_assoc,
      inv_mul_cancel₀ hCpos.ne', one_mul]
  have hinner : ∀ z, ∫ ψ, χ ψ * ((g (ψ - z) : ℝ) : ℂ) = χ z * gh := by
    intro z
    rw [← integral_add_right_eq_self (fun ψ => χ ψ * ((g (ψ - z) : ℝ) : ℂ)) z, hgh,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ψ => ?_)
    simp only [add_sub_cancel_right, hχadd]
    ring
  have hmain : ∫ ψ, χ ψ * ((Real.exp (-gaussQ p ψ) : ℝ) : ℂ) = ((C⁻¹ : ℝ) : ℂ) * (gh * gh) := by
    simp_rw [hconv]
    have h1 : ∀ ψ, χ ψ * (((C⁻¹ : ℝ) : ℂ) * ∫ z, ((g (ψ - z) * g z : ℝ) : ℂ)) =
        ((C⁻¹ : ℝ) : ℂ) * ∫ z, χ ψ * ((g (ψ - z) * g z : ℝ) : ℂ) := fun ψ => by
      rw [integral_const_mul]; ring
    simp_rw [h1]
    rw [integral_const_mul, integral_integral_swap hprod]
    congr 1
    have h2 : ∀ z, ∫ ψ, χ ψ * ((g (ψ - z) * g z : ℝ) : ℂ) = ((g z : ℝ) : ℂ) * (χ z * gh) := by
      intro z
      rw [← hinner z, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ψ => ?_)
      push_cast
      ring
    simp_rw [h2]
    rw [show (fun z => ((g z : ℝ) : ℂ) * (χ z * gh)) = fun z => (χ z * ((g z : ℝ) : ℂ)) * gh by
      funext z; ring, integral_mul_const, hgh]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, gh = r := ⟨gh.re, (Complex.conj_eq_iff_re.mp hgh_real).symm⟩
  refine ⟨C⁻¹ * (r * r), mul_nonneg (inv_nonneg.mpr hCpos.le) (mul_self_nonneg _), ?_⟩
  rw [hmain, hr]
  push_cast
  ring

/-! ## The comb against a Gaussian character -/

/-- The linear functional `ψ ↦ −2π⟨k, ψ⟩ + 2π Σ_e ξ_e ∇ψ(e)`. -/
def charFunctional (k : Site L → ℤ) (ξ : SquareZeroBond L → ℝ) : (Site L → ℝ) →ₗ[ℝ] ℝ :=
  (-2 * π) • Fintype.linearCombination ℝ (fun v => (k v : ℝ)) +
    (2 * π) • (Fintype.linearCombination ℝ ξ ∘ₗ pinnedGrad L)

theorem charFunctional_apply (k : Site L → ℤ) (ξ : SquareZeroBond L → ℝ) (ψ : Site L → ℝ) :
    charFunctional k ξ ψ =
      -2 * π * ∑ v, ψ v * (k v : ℝ) + 2 * π * ∑ e, ξ e * pinnedGrad L ψ e := by
  simp only [charFunctional, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Fintype.linearCombination_apply, smul_eq_mul]
  congr 2
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

theorem fourierCoeff_gaussChar_zero (p : SquareZeroBond L → ℝ) (ξ : SquareZeroBond L → ℝ)
    (k : Site L → ℤ) :
    multiEuclideanFourierCoefficient (gaussChar p 0 ξ) k =
      ∫ ψ, cexp (((charFunctional k ξ ψ : ℝ) : ℂ) * I) *
        ((Real.exp (-gaussQ p ψ) : ℝ) : ℂ) := by
  unfold multiEuclideanFourierCoefficient
  refine integral_congr_ae (Eventually.of_forall fun ψ => ?_)
  have hE : (((-2 * π * ∑ i, ψ i * (k i : ℝ) : ℝ) : ℂ) * I) +
      2 * π * I * ∑ e, ((ξ e : ℂ) * (pinnedGrad L ψ e : ℂ)) =
      ((charFunctional k ξ ψ : ℝ) : ℂ) * I := by
    rw [charFunctional_apply]
    push_cast
    ring
  calc cexp (((-2 * π * ∑ i, ψ i * (k i : ℝ) : ℝ) : ℂ) * I) * gaussChar p 0 ξ ψ
      = ((Real.exp (-gaussQ p ψ) : ℝ) : ℂ) * cexp ((((-2 * π * ∑ i, ψ i * (k i : ℝ) : ℝ) : ℂ) * I) +
          2 * π * I * ∑ e, ((ξ e : ℂ) * (pinnedGrad L ψ e : ℂ))) := by
        rw [gaussChar, sub_zero, Complex.exp_add]; ring
    _ = _ := by rw [hE]; ring

theorem fourierCoeff_gaussChar_shift (p : SquareZeroBond L → ℝ) (b : Site L → ℝ)
    (ξ : SquareZeroBond L → ℝ) (k : Site L → ℤ) :
    multiEuclideanFourierCoefficient (gaussChar p b ξ) k =
      cexp (((charFunctional k ξ b : ℝ) : ℂ) * I) *
        multiEuclideanFourierCoefficient (gaussChar p 0 ξ) k := by
  rw [fourierCoeff_gaussChar_zero]
  unfold multiEuclideanFourierCoefficient
  rw [← integral_add_right_eq_self _ b, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun φ => ?_)
  have hE : (((-2 * π * ∑ i, (φ + b) i * (k i : ℝ) : ℝ) : ℂ) * I) +
      2 * π * I * ∑ e, ((ξ e : ℂ) * (pinnedGrad L (φ + b) e : ℂ)) =
      ((charFunctional k ξ b : ℝ) : ℂ) * I + ((charFunctional k ξ φ : ℝ) : ℂ) * I := by
    rw [charFunctional_apply, charFunctional_apply]
    simp only [map_add, Pi.add_apply]
    push_cast
    simp only [add_mul, mul_add, Finset.sum_add_distrib]
    ring
  calc cexp (((-2 * π * ∑ i, (φ + b) i * (k i : ℝ) : ℝ) : ℂ) * I) * gaussChar p b ξ (φ + b)
      = ((Real.exp (-gaussQ p φ) : ℝ) : ℂ) *
          cexp ((((-2 * π * ∑ i, (φ + b) i * (k i : ℝ) : ℝ) : ℂ) * I) +
            2 * π * I * ∑ e, ((ξ e : ℂ) * (pinnedGrad L (φ + b) e : ℂ))) := by
        rw [gaussChar, add_sub_cancel_right, Complex.exp_add]; ring
    _ = _ := by rw [hE, Complex.exp_add]; ring

/-- **The comb against a shifted Gaussian character**: `|Θ(b)| ≤ Θ(0)`, where
`Θ(b) = Σ_{n ∈ ℤ^A} ∫ e^{−Q_p(n⊕y−b)} e^{2πi⟨ξ,∇(n⊕y)⟩} dy` (partial Poisson summation and
`exists_integral_char_gauss_eq_nonneg`). -/
theorem norm_tsum_marginal_gaussChar_le (hL : 1 < L) {p : SquareZeroBond L → ℝ}
    (hp : ∀ e, 0 < p e) (A : Finset (Site L)) (b : Site L → ℝ) (ξ : SquareZeroBond L → ℝ)
    {F F₀ : 𝓢(Site L → ℝ, ℂ)} (hF : ∀ φ, F φ = gaussChar p b ξ φ)
    (hF₀ : ∀ φ, F₀ φ = gaussChar p 0 ξ φ) :
    ‖∑' n : {x // x ∈ A} → ℤ, marginalPi (· ∈ A) F (fun i => (n i : ℝ))‖ ≤
      (∑' n : {x // x ∈ A} → ℤ, marginalPi (· ∈ A) F₀ (fun i => (n i : ℝ))).re := by
  obtain ⟨heq, hsum, -⟩ := tsum_fourier_extZero_eq_tsum_marginal (· ∈ A) F
  obtain ⟨heq₀, -, -⟩ := tsum_fourier_extZero_eq_tsum_marginal (· ∈ A) F₀
  rw [← heq, ← heq₀]
  have hFf : (F : (Site L → ℝ) → ℂ) = gaussChar p b ξ := funext hF
  have hF₀f : (F₀ : (Site L → ℝ) → ℂ) = gaussChar p 0 ξ := funext hF₀
  rw [hFf, hF₀f]
  rw [hFf] at hsum
  have hcoef : ∀ k : Site L → ℤ, ∃ r : ℝ, 0 ≤ r ∧
      multiEuclideanFourierCoefficient (gaussChar p 0 ξ) k = r := fun k => by
    rw [fourierCoeff_gaussChar_zero]
    exact exists_integral_char_gauss_eq_nonneg hL hp (charFunctional k ξ)
  choose r hr0 hr using hcoef
  have hnorm : ∀ k, ‖multiEuclideanFourierCoefficient (gaussChar p b ξ) k‖ = r k := fun k => by
    rw [fourierCoeff_gaussChar_shift, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, hr,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 k)]
  have hsumn := summable_norm_iff.mpr hsum
  calc ‖∑' q : {x // x ∈ A} → ℤ,
        multiEuclideanFourierCoefficient (gaussChar p b ξ) (extZeroInt (· ∈ A) q)‖
      ≤ ∑' q : {x // x ∈ A} → ℤ,
          ‖multiEuclideanFourierCoefficient (gaussChar p b ξ) (extZeroInt (· ∈ A) q)‖ :=
        norm_tsum_le_tsum_norm hsumn
    _ = ∑' q : {x // x ∈ A} → ℤ, r (extZeroInt (· ∈ A) q) := tsum_congr fun q => hnorm _
    _ = (∑' q : {x // x ∈ A} → ℤ,
          multiEuclideanFourierCoefficient (gaussChar p 0 ξ) (extZeroInt (· ∈ A) q)).re := by
        simp_rw [hr]
        rw [← Complex.ofReal_tsum, Complex.ofReal_re]

end FroehlichSpencer.BKT.SOS.Literal

end
