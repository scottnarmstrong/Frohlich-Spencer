/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.System
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Complex translation of the angles and the McBryan–Spencer inequality

For real `a : V → ℝ`, the shifted evaluation sends the formal character `e_m` to
`θ ↦ exp(i m·(θ + i a)) = exp(i m·θ) exp(-m·a)`. Character orthogonality makes the integral of a
shifted trigonometric polynomial independent of `a`; summing the exponential series by dominated
convergence, the same holds for `∫ e^{in·(θ+ia)} exp(H(θ + ia)) dθ` with `H` the cosine energy.
This is the contour shift `θ ↦ θ + ia` of McBryan–Spencer (external input `X:MS`), proved here
without complex integration. Bounding the shifted integrand by its modulus gives, for nonnegative
couplings and every `a`,
`⟨cos(n·θ)⟩ ≤ exp(-n·a + Σ_e J_e (cosh(d_e·a) - 1))`.
-/

@[expose] public section

open AddMonoidAlgebra MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Transition

variable {V : Type*} [Fintype V]

theorem phase_add_frequency (m n : Frequency V) (θ : V → ℝ) :
    phase (m + n) θ = phase m θ + phase n θ := by
  simp [phase, add_mul, Finset.sum_add_distrib]

theorem phase_zero_frequency (θ : V → ℝ) : phase (0 : Frequency V) θ = 0 := by
  simp [phase]

theorem phase_zero_angle (m : Frequency V) : phase m 0 = 0 := by
  simp [phase]

/-- The shifted characters `θ ↦ exp(i m·θ) exp(-m·a)`. -/
def shiftCharacter (a : V → ℝ) : Multiplicative (Frequency V) →* ((V → ℝ) → ℂ) where
  toFun m θ := character m.toAdd θ * (Real.exp (-phase m.toAdd a) : ℂ)
  map_one' := by
    funext θ
    simp [character_zero, phase_zero_frequency]
  map_mul' m n := by
    funext θ
    simp only [toAdd_mul, character_add, phase_add_frequency, neg_add, Real.exp_add,
      Complex.ofReal_mul, Pi.mul_apply]
    ring

/-- Evaluation of formal trigonometric polynomials at the complex angles `θ + i a`. -/
def shiftEval (a : V → ℝ) : TrigAlgebra V →ₐ[ℝ] ((V → ℝ) → ℂ) :=
  AddMonoidAlgebra.lift ℝ _ _ (shiftCharacter a)

theorem shiftEval_single (a : V → ℝ) (m : Frequency V) (r : ℝ) (θ : V → ℝ) :
    shiftEval a (single m r) θ = (r : ℂ) * (character m θ * (Real.exp (-phase m a) : ℂ)) := by
  rw [shiftEval, lift_single, Pi.smul_apply, Complex.real_smul]
  rfl

theorem continuous_shiftEval (a : V → ℝ) (P : TrigAlgebra V) : Continuous (shiftEval a P) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero =>
      rw [map_zero]
      exact continuous_const
  | add P Q hP hQ =>
      rw [map_add]
      exact hP.add hQ
  | single m r =>
      have h : shiftEval a (single m r) =
          fun θ => (r : ℂ) * (character m θ * (Real.exp (-phase m a) : ℂ)) :=
        funext (shiftEval_single a m r)
      rw [h]
      have := continuous_character m
      fun_prop

theorem exists_norm_shiftEval_le (a : V → ℝ) (P : TrigAlgebra V) :
    ∃ C, ∀ θ, ‖shiftEval a P θ‖ ≤ C := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, fun θ => by simp⟩
  | add P Q hP hQ =>
      obtain ⟨C₁, h₁⟩ := hP
      obtain ⟨C₂, h₂⟩ := hQ
      refine ⟨C₁ + C₂, fun θ => ?_⟩
      rw [map_add, Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add (h₁ θ) (h₂ θ))
  | single m r =>
      refine ⟨|r| * Real.exp (-phase m a), fun θ => ?_⟩
      rw [shiftEval_single, norm_mul, norm_mul, norm_character, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        one_mul]

theorem shiftEval_zero_single (n : Frequency V) (θ : V → ℝ) :
    shiftEval 0 (single n 1) θ = character n θ := by
  rw [shiftEval_single, phase_zero_angle]
  simp

theorem norm_shiftEval_single_one (a : V → ℝ) (n : Frequency V) (θ : V → ℝ) :
    ‖shiftEval a (single n 1) θ‖ = Real.exp (-phase n a) := by
  rw [shiftEval_single, norm_mul, norm_mul, norm_character, Complex.norm_real, Complex.norm_real]
  simp [abs_of_pos (Real.exp_pos _)]

/-- The formal cosine `cos(m·θ) = (e_m + e_{-m})/2`. -/
def cosElem (m : Frequency V) : TrigAlgebra V :=
  (1 / 2 : ℝ) • (single m 1 + single (-m) 1)

theorem shiftEval_cosElem (a : V → ℝ) (m : Frequency V) (θ : V → ℝ) :
    shiftEval a (cosElem m) θ =
      Complex.cos ((phase m θ : ℂ) + (phase m a : ℂ) * Complex.I) := by
  simp only [cosElem, map_smul, map_add, Pi.smul_apply, Pi.add_apply, shiftEval_single,
    character_eq_exp, phase_neg, Complex.real_smul, Complex.ofReal_exp]
  rw [Complex.cos]
  have h₁ : ((phase m θ : ℂ) + (phase m a : ℂ) * Complex.I) * Complex.I =
      (phase m θ : ℂ) * Complex.I + ((-phase m a : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have h₂ : -((phase m θ : ℂ) + (phase m a : ℂ) * Complex.I) * Complex.I =
      ((-phase m θ : ℝ) : ℂ) * Complex.I + ((- -phase m a : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h₁, h₂, Complex.exp_add, Complex.exp_add]
  push_cast
  ring

theorem re_shiftEval_cosElem (a : V → ℝ) (m : Frequency V) (θ : V → ℝ) :
    (shiftEval a (cosElem m) θ).re = Real.cos (phase m θ) * Real.cosh (phase m a) := by
  rw [shiftEval_cosElem, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp [Complex.mul_re, Complex.cos_ofReal_re]

variable {E : Type*} [Fintype E]

/-- The formal cosine energy `Σ_e J_e cos(d_e·θ)`. -/
def energyElem (d : E → Frequency V) (J : E → ℝ) : TrigAlgebra V :=
  ∑ e, J e • cosElem (d e)

theorem shiftEval_energyElem (a : V → ℝ) (d : E → Frequency V) (J : E → ℝ) (θ : V → ℝ) :
    shiftEval a (energyElem d J) θ = ∑ e, (J e : ℂ) * shiftEval a (cosElem (d e)) θ := by
  simp [energyElem, map_sum, Complex.real_smul]

theorem re_shiftEval_energyElem (a : V → ℝ) (d : E → Frequency V) (J : E → ℝ) (θ : V → ℝ) :
    (shiftEval a (energyElem d J) θ).re =
      ∑ e, J e * (Real.cos (phase (d e) θ) * Real.cosh (phase (d e) a)) := by
  rw [shiftEval_energyElem, Complex.re_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Complex.re_ofReal_mul, re_shiftEval_cosElem]

theorem shiftEval_zero_energyElem (d : E → Frequency V) (J : E → ℝ) (θ : V → ℝ) :
    shiftEval 0 (energyElem d J) θ = (cosineEnergy d J θ : ℂ) := by
  rw [shiftEval_energyElem, cosineEnergy]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [shiftEval_cosElem, phase_zero_angle]
  simp

/-- The real part of the shifted energy is at most the energy plus `Σ_e J_e (cosh(d_e·a) - 1)`. -/
theorem re_shiftEval_energyElem_le (a : V → ℝ) (d : E → Frequency V) {J : E → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (θ : V → ℝ) :
    (shiftEval a (energyElem d J) θ).re ≤
      cosineEnergy d J θ + ∑ e, J e * (Real.cosh (phase (d e) a) - 1) := by
  rw [re_shiftEval_energyElem, cosineEnergy, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have hc : 0 ≤ Real.cosh (phase (d e) a) - 1 := by
    linarith [Real.one_le_cosh (phase (d e) a)]
  have h1 := Real.cos_le_one (phase (d e) θ)
  nlinarith [hJ e, mul_le_mul_of_nonneg_left h1 hc]

variable [DecidableEq V]

theorem integrable_shiftEval (a : V → ℝ) (P : TrigAlgebra V) :
    Integrable (shiftEval a P) (rotatorRawAngleMeasure V) := by
  obtain ⟨C, hC⟩ := exists_norm_shiftEval_le a P
  exact Integrable.of_bound (continuous_shiftEval a P).aestronglyMeasurable C (ae_of_all _ hC)

/-- Character orthogonality for shifted polynomials: the integral does not depend on the shift. -/
theorem integral_shiftEval (a : V → ℝ) (P : TrigAlgebra V) :
    ∫ θ, shiftEval a P θ ∂rotatorRawAngleMeasure V =
      (((2 * π) ^ Fintype.card V * P.coeff 0 : ℝ) : ℂ) := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
      simp only [map_add, Pi.add_apply]
      rw [integral_add (integrable_shiftEval a P) (integrable_shiftEval a Q), hP, hQ, coeff_add,
        Finsupp.add_apply]
      push_cast
      ring
  | single m r =>
      simp_rw [shiftEval_single]
      rw [integral_const_mul, integral_mul_const, integral_character, coeff_single,
        Finsupp.single_apply]
      by_cases hm : m = 0
      · subst hm
        simp only [ite_true, phase_zero_frequency, neg_zero, Real.exp_zero]
        push_cast
        ring
      · simp [hm]

/-- The partial sums of the exponential series of `shiftEval a Q`, integrated against
`shiftEval a P`, converge to the shifted integral; their values do not depend on `a`. -/
theorem tendsto_integral_shiftEval_mul_exp (a : V → ℝ) (P Q : TrigAlgebra V) :
    Tendsto (fun N => ∑ k ∈ Finset.range N,
        ((((2 * π) ^ Fintype.card V * (P * Q ^ k).coeff 0) / (Nat.factorial k : ℝ) : ℝ) : ℂ))
      atTop (𝓝 (∫ θ, shiftEval a P θ * Complex.exp (shiftEval a Q θ)
        ∂rotatorRawAngleMeasure V)) := by
  obtain ⟨CP, hCP⟩ := exists_norm_shiftEval_le a P
  obtain ⟨CQ, hCQ⟩ := exists_norm_shiftEval_le a Q
  have hCP0 : 0 ≤ CP := (norm_nonneg _).trans (hCP 0)
  let G : ℕ → (V → ℝ) → ℂ := fun N θ =>
    shiftEval a P θ * ∑ k ∈ Finset.range N, (shiftEval a Q θ) ^ k / (Nat.factorial k : ℂ)
  have hGint (N : ℕ) : ∫ θ, G N θ ∂rotatorRawAngleMeasure V = ∑ k ∈ Finset.range N,
      ((((2 * π) ^ Fintype.card V * (P * Q ^ k).coeff 0) / (Nat.factorial k : ℝ) : ℝ) : ℂ) := by
    have hG : (fun θ => G N θ) = fun θ => ∑ k ∈ Finset.range N,
        shiftEval a (P * Q ^ k) θ / (Nat.factorial k : ℂ) := by
      funext θ
      simp only [G, Finset.mul_sum, map_mul, map_pow, Pi.mul_apply, Pi.pow_apply, mul_div_assoc]
    rw [hG, integral_finsetSum _ fun k _ => (integrable_shiftEval a _).div_const _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_div, integral_shiftEval]
    push_cast
    ring
  have hlim := tendsto_integral_of_dominated_convergence (μ := rotatorRawAngleMeasure V) (F := G)
    (f := fun θ => shiftEval a P θ * Complex.exp (shiftEval a Q θ))
    (fun _ => CP * Real.exp CQ) (fun N => ?_) (integrable_const _) (fun N => ?_) ?_
  · simpa only [hGint] using hlim
  · refine Continuous.aestronglyMeasurable ?_
    exact (continuous_shiftEval a P).mul
      (continuous_finsetSum _ fun k _ => ((continuous_shiftEval a Q).pow k).div_const _)
  · refine ae_of_all _ fun θ => ?_
    rw [norm_mul]
    refine mul_le_mul (hCP θ) ?_ (norm_nonneg _) hCP0
    calc ‖∑ k ∈ Finset.range N, (shiftEval a Q θ) ^ k / (Nat.factorial k : ℂ)‖
        ≤ ∑ k ∈ Finset.range N, ‖shiftEval a Q θ‖ ^ k / (Nat.factorial k : ℝ) := by
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
          rw [norm_div, norm_pow, Complex.norm_natCast]
      _ ≤ Real.exp ‖shiftEval a Q θ‖ := Real.sum_le_exp_of_nonneg (norm_nonneg _) N
      _ ≤ Real.exp CQ := Real.exp_le_exp.mpr (hCQ θ)
  · refine ae_of_all _ fun θ => ?_
    refine Tendsto.const_mul _ ?_
    have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (shiftEval a Q θ)).tendsto_sum_nat
    rw [← Complex.exp_eq_exp_ℂ] at h
    refine h.congr fun N => Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul, inv_mul_eq_div]

/-- **The contour shift.** The integral of `e^{in·(θ+ia)} exp(H(θ + ia))`-type expressions does
not depend on the imaginary translation `a`. -/
theorem integral_shiftEval_mul_exp_eq (a : V → ℝ) (P Q : TrigAlgebra V) :
    ∫ θ, shiftEval a P θ * Complex.exp (shiftEval a Q θ) ∂rotatorRawAngleMeasure V =
      ∫ θ, shiftEval 0 P θ * Complex.exp (shiftEval 0 Q θ) ∂rotatorRawAngleMeasure V :=
  tendsto_nhds_unique (tendsto_integral_shiftEval_mul_exp a P Q)
    (tendsto_integral_shiftEval_mul_exp 0 P Q)

/-- **McBryan–Spencer inequality** for cosine interactions. For nonnegative couplings and every real
`a : V → ℝ`, `⟨cos(n·θ)⟩ ≤ exp(-n·a + Σ_e J_e (cosh(d_e·a) - 1))`. -/
theorem integral_cos_cosineGibbs_le_exp (d : E → Frequency V) {J : E → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (n : Frequency V) (a : V → ℝ) :
    ∫ θ, Real.cos (phase n θ) ∂cosineGibbs d J ≤
      Real.exp (-phase n a + ∑ e, J e * (Real.cosh (phase (d e) a) - 1)) := by
  set K := ∑ e, J e * (Real.cosh (phase (d e) a) - 1)
  set Q := energyElem d J
  have hZ := cosinePartition_pos d J
  rw [integral_cosineGibbs, div_le_iff₀ hZ]
  -- the real integral is the real part of the complex one
  have hchar : ∀ θ, shiftEval 0 (single n 1) θ * Complex.exp (shiftEval 0 Q θ) =
      character n θ * (cosineWeight d J θ : ℂ) := fun θ => by
    rw [shiftEval_zero_single, shiftEval_zero_energyElem, cosineWeight, Complex.ofReal_exp]
  have hint0 : Integrable (fun θ => character n θ * (cosineWeight d J θ : ℂ))
      (rotatorRawAngleMeasure V) := by
    refine Integrable.of_bound ((continuous_character n).mul
      (Complex.continuous_ofReal.comp (continuous_cosineWeight d J))).aestronglyMeasurable
      (Real.exp (∑ e, |J e|)) (ae_of_all _ fun θ => ?_)
    rw [norm_mul, norm_character, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (cosineWeight_pos d J θ)]
    exact cosineWeight_le d J θ
  have hre : ∫ θ, Real.cos (phase n θ) * cosineWeight d J θ ∂rotatorRawAngleMeasure V =
      (∫ θ, character n θ * (cosineWeight d J θ : ℂ) ∂rotatorRawAngleMeasure V).re := by
    have h := integral_re hint0
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    simp only
    rw [character_eq_exp, Complex.exp_mul_I]
    simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im]
  -- shift the contour
  have hshift := integral_shiftEval_mul_exp_eq a (single n 1) Q
  simp_rw [hchar] at hshift
  rw [hre, ← hshift]
  -- bound by the modulus
  have hbound : ∀ θ, ‖shiftEval a (single n 1) θ * Complex.exp (shiftEval a Q θ)‖ ≤
      Real.exp (-phase n a + K) * cosineWeight d J θ := fun θ => by
    rw [norm_mul, norm_shiftEval_single_one, Complex.norm_exp, cosineWeight, ← Real.exp_add,
      ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := re_shiftEval_energyElem_le a d hJ θ
    linarith
  obtain ⟨CP, hCP⟩ := exists_norm_shiftEval_le a (single n 1)
  obtain ⟨CQ, hCQ⟩ := exists_norm_shiftEval_le a Q
  have hint : Integrable (fun θ => shiftEval a (single n 1) θ * Complex.exp (shiftEval a Q θ))
      (rotatorRawAngleMeasure V) := by
    refine Integrable.of_bound (((continuous_shiftEval a _).mul
      (Complex.continuous_exp.comp (continuous_shiftEval a Q)))).aestronglyMeasurable
      (CP * Real.exp CQ) (ae_of_all _ fun θ => ?_)
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_mul (hCP θ) (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hCQ θ)))
      (Real.exp_pos _).le ((norm_nonneg _).trans (hCP θ))
  calc (∫ θ, shiftEval a (single n 1) θ * Complex.exp (shiftEval a Q θ)
        ∂rotatorRawAngleMeasure V).re
      ≤ ‖∫ θ, shiftEval a (single n 1) θ * Complex.exp (shiftEval a Q θ)
          ∂rotatorRawAngleMeasure V‖ := Complex.re_le_norm _
    _ ≤ ∫ θ, ‖shiftEval a (single n 1) θ * Complex.exp (shiftEval a Q θ)‖
          ∂rotatorRawAngleMeasure V := norm_integral_le_integral_norm _
    _ ≤ ∫ θ, Real.exp (-phase n a + K) * cosineWeight d J θ ∂rotatorRawAngleMeasure V :=
        integral_mono hint.norm ((integrable_cosineWeight d J).const_mul _) hbound
    _ = Real.exp (-phase n a + K) * cosinePartition d J := by
        rw [integral_const_mul, cosinePartition]

end FroehlichSpencer.BKT.Rotator.Transition

end
