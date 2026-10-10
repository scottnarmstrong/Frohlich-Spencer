/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.Positivity
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Ginibre's inequalities for cosine interactions

A finite family of integer frequency vectors `d e` with real couplings `J e` defines the Gibbs
measure `Z⁻¹ exp(Σ_e J_e cos(d_e·θ)) ∏_x dθ_x` on `[-π, π)^V`. The plane rotator of FS81 (1.26),
J p. 533, is the case `d_e = δ_i - δ_j` for the nearest-neighbour pairs `(ij) ⊂ Λ`, with `J_e = β`.
For nonnegative couplings we prove, by Ginibre's duplicated-variable argument (external input
`X:Ginibre`, proved here in full):

* **Ginibre I:** `⟨cos(n·θ)⟩ ≥ 0`;
* **Ginibre II:** `⟨cos(n·θ) cos(m·θ)⟩ ≥ ⟨cos(n·θ)⟩ ⟨cos(m·θ)⟩`;
* **monotonicity:** `⟨cos(n·θ)⟩` is nondecreasing in every coupling;
* the reflection symmetry `⟨sin(n·θ)⟩ = 0`, used for FS81 (1.29);
* the transfer of expectations along a site embedding that preserves the energy, which with
  monotonicity gives the free-boundary domain monotonicity.
-/

@[expose] public section

open AddMonoidAlgebra MeasureTheory
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The cosine energy `Σ_e J_e cos(d_e·θ)`; the Boltzmann weight is its exponential. -/
def cosineEnergy (d : E → Frequency V) (J : E → ℝ) (θ : V → ℝ) : ℝ :=
  ∑ e, J e * Real.cos (phase (d e) θ)

/-- The Boltzmann weight `exp(Σ_e J_e cos(d_e·θ))`. -/
def cosineWeight (d : E → Frequency V) (J : E → ℝ) (θ : V → ℝ) : ℝ :=
  Real.exp (cosineEnergy d J θ)

variable [DecidableEq V] in
/-- The raw partition integral over `[-π, π)^V`. -/
def cosinePartition (d : E → Frequency V) (J : E → ℝ) : ℝ :=
  ∫ θ, cosineWeight d J θ ∂rotatorRawAngleMeasure V

variable [DecidableEq V] in
/-- The normalized Gibbs measure of the cosine interaction. -/
def cosineGibbs (d : E → Frequency V) (J : E → ℝ) : Measure (V → ℝ) :=
  (rotatorRawAngleMeasure V).withDensity fun θ =>
    ENNReal.ofReal (cosineWeight d J θ / cosinePartition d J)

theorem continuous_phase (m : Frequency V) : Continuous (phase m) := by
  unfold phase
  fun_prop

theorem phase_neg_angle (m : Frequency V) (θ : V → ℝ) : phase m (-θ) = -phase m θ := by
  simp [phase, Finset.sum_neg_distrib]

theorem continuous_cosineEnergy (d : E → Frequency V) (J : E → ℝ) :
    Continuous (cosineEnergy d J) := by
  unfold cosineEnergy
  have h := fun e => continuous_phase (d e)
  fun_prop

theorem continuous_cosineWeight (d : E → Frequency V) (J : E → ℝ) :
    Continuous (cosineWeight d J) :=
  Real.continuous_exp.comp (continuous_cosineEnergy d J)

theorem cosineWeight_pos (d : E → Frequency V) (J : E → ℝ) (θ : V → ℝ) :
    0 < cosineWeight d J θ :=
  Real.exp_pos _

theorem abs_cosineEnergy_le (d : E → Frequency V) (J : E → ℝ) (θ : V → ℝ) :
    |cosineEnergy d J θ| ≤ ∑ e, |J e| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem cosineWeight_le (d : E → Frequency V) (J : E → ℝ) (θ : V → ℝ) :
    cosineWeight d J θ ≤ Real.exp (∑ e, |J e|) :=
  Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_cosineEnergy_le d J θ))

theorem cosineEnergy_neg (d : E → Frequency V) (J : E → ℝ) (θ : V → ℝ) :
    cosineEnergy d J (-θ) = cosineEnergy d J θ := by
  simp [cosineEnergy, phase_neg_angle]

theorem dupEval_sum_cosPair (d : E → Frequency V) (a b : E → ℝ) (z : (V → ℝ) × (V → ℝ)) :
    dupEval V (∑ e, (a e • cosPair (d e) 1 + b e • cosPair (d e) (-1))) z =
      ((cosineEnergy d (fun e => a e + b e) z.1 + cosineEnergy d (fun e => a e - b e) z.2 : ℝ) :
        ℂ) := by
  simp only [map_sum, map_add, map_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
    dupEval_cosPair, Complex.real_smul, cosineEnergy]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

variable [DecidableEq V]

/-- A bounded continuous function times the Boltzmann weight is integrable. -/
theorem integrable_mul_cosineWeight (d : E → Frequency V) (J : E → ℝ) {f : (V → ℝ) → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ θ, |f θ| ≤ C) :
    Integrable (fun θ => f θ * cosineWeight d J θ) (rotatorRawAngleMeasure V) := by
  refine Integrable.of_bound (hf.mul (continuous_cosineWeight d J)).aestronglyMeasurable
    (C * Real.exp (∑ e, |J e|)) (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (cosineWeight_pos d J θ)]
  exact mul_le_mul (hC θ) (cosineWeight_le d J θ) (cosineWeight_pos d J θ).le
    ((abs_nonneg _).trans (hC θ))

theorem integrable_cosineWeight (d : E → Frequency V) (J : E → ℝ) :
    Integrable (cosineWeight d J) (rotatorRawAngleMeasure V) := by
  simpa using integrable_mul_cosineWeight d J (f := fun _ => 1) continuous_const
    (C := 1) (fun _ => by simp)

theorem rotatorRawAngleMeasure_univ_ne_zero : rotatorRawAngleMeasure V Set.univ ≠ 0 := by
  unfold rotatorRawAngleMeasure
  rw [← Set.pi_univ (Set.univ : Set V), Measure.pi_pi]
  simp [Real.volume_Ico, Real.pi_pos]

/-- The partition integral is positive. -/
theorem cosinePartition_pos (d : E → Frequency V) (J : E → ℝ) : 0 < cosinePartition d J := by
  rw [cosinePartition, integral_pos_iff_support_of_nonneg
    (fun θ => (cosineWeight_pos d J θ).le) (integrable_cosineWeight d J)]
  have hsupp : Function.support (cosineWeight d J) = Set.univ := by
    ext θ
    simp [(cosineWeight_pos d J θ).ne']
  rw [hsupp]
  exact pos_iff_ne_zero.mpr rotatorRawAngleMeasure_univ_ne_zero

/-- Expectations under the cosine Gibbs measure are ratios of raw integrals. -/
theorem integral_cosineGibbs (d : E → Frequency V) (J : E → ℝ) (f : (V → ℝ) → ℝ) :
    ∫ θ, f θ ∂cosineGibbs d J =
      (∫ θ, f θ * cosineWeight d J θ ∂rotatorRawAngleMeasure V) / cosinePartition d J := by
  have hZ := cosinePartition_pos d J
  have hden : Measurable fun θ : V → ℝ =>
      ENNReal.ofReal (cosineWeight d J θ / cosinePartition d J) :=
    ((continuous_cosineWeight d J).measurable.div_const _).ennreal_ofReal
  rw [cosineGibbs, integral_withDensity_eq_integral_toReal_smul hden
    (ae_of_all _ fun θ => ENNReal.ofReal_lt_top), ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (div_nonneg (cosineWeight_pos d J θ).le hZ.le), smul_eq_mul]
  ring

instance isProbabilityMeasure_cosineGibbs (d : E → Frequency V) (J : E → ℝ) :
    IsProbabilityMeasure (cosineGibbs d J) := by
  constructor
  have hZ := cosinePartition_pos d J
  rw [cosineGibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_cosineWeight d J).div_const _)
      (ae_of_all _ fun θ => div_nonneg (cosineWeight_pos d J θ).le hZ.le),
    integral_div, ← cosinePartition, div_self hZ.ne', ENNReal.ofReal_one]

/-! ### The duplicated system -/

/-- The doubled raw angle measure on `(θ, θ')`. -/
abbrev dupMeasure (V : Type*) [Fintype V] [DecidableEq V] : Measure ((V → ℝ) × (V → ℝ)) :=
  (rotatorRawAngleMeasure V).prod (rotatorRawAngleMeasure V)

/-- The master inequality: an element of Ginibre's cone integrates nonnegatively against the
duplicated weight `exp(H_{J₁}(θ) + H_{J₂}(θ'))` whenever `0 ≤ J₂ ≤ J₁`. -/
theorem integral_mul_dupWeight_nonneg (d : E → Frequency V) {J₁ J₂ : E → ℝ}
    (h₂ : ∀ e, 0 ≤ J₂ e) (h₁₂ : ∀ e, J₂ e ≤ J₁ e) {P : DupTrigAlgebra V} (hP : IsGinibre P)
    {F : (V → ℝ) × (V → ℝ) → ℝ} (hF : ∀ z, dupEval V P z = (F z : ℂ)) :
    0 ≤ ∫ z, F z * (cosineWeight d J₁ z.1 * cosineWeight d J₂ z.2) ∂dupMeasure V := by
  set a : E → ℝ := fun e => (J₁ e + J₂ e) / 2
  set b : E → ℝ := fun e => (J₁ e - J₂ e) / 2
  have ha : ∀ e, 0 ≤ a e := fun e => by
    have := h₂ e
    have := h₁₂ e
    simp only [a]
    linarith
  have hb : ∀ e, 0 ≤ b e := fun e => by
    have := h₁₂ e
    simp only [b]
    linarith
  have hQ : IsGinibre (∑ e, (a e • cosPair (d e) 1 + b e • cosPair (d e) (-1))) :=
    IsGinibre.sum _ fun e _ =>
      ((isGinibre_cosPair (d e) (by norm_num)).smul (ha e)).add
        ((isGinibre_cosPair (d e) (by norm_num)).smul (hb e))
  have hab₁ : (fun e => a e + b e) = J₁ := by
    funext e
    simp only [a, b]
    ring
  have hab₂ : (fun e => a e - b e) = J₂ := by
    funext e
    simp only [a, b]
    ring
  have h := integral_mul_exp_nonneg hP hQ hF (fun z => by rw [dupEval_sum_cosPair d a b z])
  simp only [hab₁, hab₂, Real.exp_add] at h
  exact h

/-- Integrals of product functions against the doubled measure factor. -/
theorem integral_dupMeasure_mul (f g : (V → ℝ) → ℝ) :
    ∫ z, f z.1 * g z.2 ∂dupMeasure V =
      (∫ θ, f θ ∂rotatorRawAngleMeasure V) * ∫ θ, g θ ∂rotatorRawAngleMeasure V :=
  integral_prod_mul f g

theorem integrable_dupMeasure_mul {f g : (V → ℝ) → ℝ}
    (hf : Integrable f (rotatorRawAngleMeasure V)) (hg : Integrable g (rotatorRawAngleMeasure V)) :
    Integrable (fun z : (V → ℝ) × (V → ℝ) => f z.1 * g z.2) (dupMeasure V) :=
  hf.mul_prod hg

/-- The duplicated integral behind the second inequality:
`∫∫ (f(θ) - f(θ'))(g(θ) - g(θ')) w(θ) w(θ') = 2 (∫ f g w ∫ w - ∫ f w ∫ g w)`. -/
theorem integral_dupMeasure_diff_mul_diff {f g w : (V → ℝ) → ℝ}
    (hfgw : Integrable (fun θ => f θ * g θ * w θ) (rotatorRawAngleMeasure V))
    (hfw : Integrable (fun θ => f θ * w θ) (rotatorRawAngleMeasure V))
    (hgw : Integrable (fun θ => g θ * w θ) (rotatorRawAngleMeasure V))
    (hw : Integrable w (rotatorRawAngleMeasure V)) :
    ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) * (w z.1 * w z.2) ∂dupMeasure V =
      2 * ((∫ θ, f θ * g θ * w θ ∂rotatorRawAngleMeasure V) * (∫ θ, w θ ∂rotatorRawAngleMeasure V) -
        (∫ θ, f θ * w θ ∂rotatorRawAngleMeasure V) * ∫ θ, g θ * w θ ∂rotatorRawAngleMeasure V) := by
  have h₁ : (fun z : (V → ℝ) × (V → ℝ) => (f z.1 - f z.2) * (g z.1 - g z.2) * (w z.1 * w z.2)) =
      fun z => ((f z.1 * g z.1 * w z.1) * w z.2 + w z.1 * (f z.2 * g z.2 * w z.2)) -
        ((f z.1 * w z.1) * (g z.2 * w z.2) + (g z.1 * w z.1) * (f z.2 * w z.2)) := by
    funext z
    ring
  have i₁ := integrable_dupMeasure_mul hfgw hw
  have i₂ := integrable_dupMeasure_mul hw hfgw
  have i₃ := integrable_dupMeasure_mul hfw hgw
  have i₄ := integrable_dupMeasure_mul hgw hfw
  have i₁₂ : Integrable (fun z : (V → ℝ) × (V → ℝ) =>
      (f z.1 * g z.1 * w z.1) * w z.2 + w z.1 * (f z.2 * g z.2 * w z.2)) (dupMeasure V) :=
    i₁.add i₂
  have i₃₄ : Integrable (fun z : (V → ℝ) × (V → ℝ) =>
      (f z.1 * w z.1) * (g z.2 * w z.2) + (g z.1 * w z.1) * (f z.2 * w z.2)) (dupMeasure V) :=
    i₃.add i₄
  rw [h₁, integral_sub i₁₂ i₃₄, integral_add i₁ i₂, integral_add i₃ i₄,
    integral_dupMeasure_mul (fun θ => f θ * g θ * w θ) w,
    integral_dupMeasure_mul w (fun θ => f θ * g θ * w θ),
    integral_dupMeasure_mul (fun θ => f θ * w θ) (fun θ => g θ * w θ),
    integral_dupMeasure_mul (fun θ => g θ * w θ) (fun θ => f θ * w θ)]
  ring

/-- The duplicated integral behind monotonicity:
`∫∫ (f(θ) - f(θ')) w'(θ) w(θ') = ∫ f w' ∫ w - ∫ w' ∫ f w`. -/
theorem integral_dupMeasure_diff {f w w' : (V → ℝ) → ℝ}
    (hfw' : Integrable (fun θ => f θ * w' θ) (rotatorRawAngleMeasure V))
    (hfw : Integrable (fun θ => f θ * w θ) (rotatorRawAngleMeasure V))
    (hw : Integrable w (rotatorRawAngleMeasure V)) (hw' : Integrable w' (rotatorRawAngleMeasure V)) :
    ∫ z, (f z.1 - f z.2) * (w' z.1 * w z.2) ∂dupMeasure V =
      (∫ θ, f θ * w' θ ∂rotatorRawAngleMeasure V) * (∫ θ, w θ ∂rotatorRawAngleMeasure V) -
        (∫ θ, w' θ ∂rotatorRawAngleMeasure V) * ∫ θ, f θ * w θ ∂rotatorRawAngleMeasure V := by
  have h₁ : (fun z : (V → ℝ) × (V → ℝ) => (f z.1 - f z.2) * (w' z.1 * w z.2)) =
      fun z => (f z.1 * w' z.1) * w z.2 - w' z.1 * (f z.2 * w z.2) := by
    funext z
    ring
  rw [h₁, integral_sub (integrable_dupMeasure_mul hfw' hw) (integrable_dupMeasure_mul hw' hfw),
    integral_dupMeasure_mul (fun θ => f θ * w' θ) w,
    integral_dupMeasure_mul w' (fun θ => f θ * w θ)]

/-! ### Ginibre's inequalities -/

theorem integrable_cos_mul_cosineWeight (d : E → Frequency V) (J : E → ℝ) (n : Frequency V) :
    Integrable (fun θ => Real.cos (phase n θ) * cosineWeight d J θ) (rotatorRawAngleMeasure V) :=
  integrable_mul_cosineWeight d J (Real.continuous_cos.comp (continuous_phase n))
    (fun _ => Real.abs_cos_le_one _)

/-- **Ginibre's first inequality.** For nonnegative couplings, `⟨cos(n·θ)⟩ ≥ 0`. -/
theorem integral_cos_cosineGibbs_nonneg (d : E → Frequency V) {J : E → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (n : Frequency V) : 0 ≤ ∫ θ, Real.cos (phase n θ) ∂cosineGibbs d J := by
  rw [integral_cosineGibbs]
  have hZ := cosinePartition_pos d J
  refine div_nonneg ?_ hZ.le
  have hP : IsGinibre ((1 / 2 : ℝ) • (cosPair n 1 + cosPair n (-1))) :=
    ((isGinibre_cosPair n (by norm_num)).add (isGinibre_cosPair n (by norm_num))).smul
      (by norm_num)
  have h := integral_mul_dupWeight_nonneg d hJ (fun e => le_rfl) hP
    (F := fun z => Real.cos (phase n z.1)) (fun z => by
      simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, dupEval_cosPair,
        Complex.real_smul]
      push_cast
      ring)
  have hfac : (fun z : (V → ℝ) × (V → ℝ) =>
      Real.cos (phase n z.1) * (cosineWeight d J z.1 * cosineWeight d J z.2)) =
      fun z => (Real.cos (phase n z.1) * cosineWeight d J z.1) * cosineWeight d J z.2 := by
    funext z
    ring
  rw [hfac, integral_dupMeasure_mul (fun θ => Real.cos (phase n θ) * cosineWeight d J θ)
    (cosineWeight d J), ← cosinePartition] at h
  exact nonneg_of_mul_nonneg_left h hZ

theorem integral_cos_cosineGibbs_le_one (d : E → Frequency V) (J : E → ℝ) (n : Frequency V) :
    ∫ θ, Real.cos (phase n θ) ∂cosineGibbs d J ≤ 1 := by
  rw [integral_cosineGibbs, div_le_one (cosinePartition_pos d J), cosinePartition]
  refine integral_mono (integrable_cos_mul_cosineWeight d J n) (integrable_cosineWeight d J)
    fun θ => ?_
  exact mul_le_of_le_one_left (cosineWeight_pos d J θ).le (Real.cos_le_one _)

/-- **Ginibre's second inequality.** For nonnegative couplings,
`⟨cos(n·θ)⟩ ⟨cos(m·θ)⟩ ≤ ⟨cos(n·θ) cos(m·θ)⟩`. -/
theorem integral_cos_mul_cos_cosineGibbs_ge (d : E → Frequency V) {J : E → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (n m : Frequency V) :
    (∫ θ, Real.cos (phase n θ) ∂cosineGibbs d J) * (∫ θ, Real.cos (phase m θ) ∂cosineGibbs d J) ≤
      ∫ θ, Real.cos (phase n θ) * Real.cos (phase m θ) ∂cosineGibbs d J := by
  simp only [integral_cosineGibbs]
  have hZ := cosinePartition_pos d J
  have hP : IsGinibre ((1 / 2 : ℝ) • (cosPair n (-1) * cosPair m (-1))) :=
    ((isGinibre_cosPair n (by norm_num)).mul (isGinibre_cosPair m (by norm_num))).smul
      (by norm_num)
  have h := integral_mul_dupWeight_nonneg d hJ (fun e => le_rfl) hP
    (F := fun z => (1 / 2 : ℝ) * ((Real.cos (phase n z.1) - Real.cos (phase n z.2)) *
      (Real.cos (phase m z.1) - Real.cos (phase m z.2)))) (fun z => by
        simp only [map_smul, map_mul, Pi.smul_apply, Pi.mul_apply, dupEval_cosPair,
          Complex.real_smul]
        push_cast
        ring)
  have hnm : Integrable
      (fun θ => Real.cos (phase n θ) * Real.cos (phase m θ) * cosineWeight d J θ)
      (rotatorRawAngleMeasure V) :=
    integrable_mul_cosineWeight d J
      ((Real.continuous_cos.comp (continuous_phase n)).mul
        (Real.continuous_cos.comp (continuous_phase m))) (C := 1)
      (fun θ => by
        rw [abs_mul]
        nlinarith [Real.abs_cos_le_one (phase n θ), Real.abs_cos_le_one (phase m θ),
          abs_nonneg (Real.cos (phase n θ)), abs_nonneg (Real.cos (phase m θ))])
  have hexp : (fun z : (V → ℝ) × (V → ℝ) =>
      (1 / 2 : ℝ) * ((Real.cos (phase n z.1) - Real.cos (phase n z.2)) *
        (Real.cos (phase m z.1) - Real.cos (phase m z.2))) *
          (cosineWeight d J z.1 * cosineWeight d J z.2)) =
      fun z => (1 / 2 : ℝ) * ((Real.cos (phase n z.1) - Real.cos (phase n z.2)) *
        (Real.cos (phase m z.1) - Real.cos (phase m z.2)) *
          (cosineWeight d J z.1 * cosineWeight d J z.2)) := by
    funext z
    ring
  rw [hexp, integral_const_mul, integral_dupMeasure_diff_mul_diff hnm
    (integrable_cos_mul_cosineWeight d J n) (integrable_cos_mul_cosineWeight d J m)
    (integrable_cosineWeight d J), ← cosinePartition] at h
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hZ hZ) hZ]
  nlinarith

/-- **Monotonicity in the couplings.** For `0 ≤ J ≤ J'`, `⟨cos(n·θ)⟩_J ≤ ⟨cos(n·θ)⟩_{J'}`. -/
theorem integral_cos_cosineGibbs_mono (d : E → Frequency V) {J J' : E → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (hJJ' : ∀ e, J e ≤ J' e) (n : Frequency V) :
    ∫ θ, Real.cos (phase n θ) ∂cosineGibbs d J ≤ ∫ θ, Real.cos (phase n θ) ∂cosineGibbs d J' := by
  simp only [integral_cosineGibbs]
  have hZ := cosinePartition_pos d J
  have hZ' := cosinePartition_pos d J'
  have h := integral_mul_dupWeight_nonneg d hJ hJJ' (isGinibre_cosPair n (σ := -1) (by norm_num))
    (F := fun z => Real.cos (phase n z.1) - Real.cos (phase n z.2)) (fun z => by
      rw [dupEval_cosPair]
      push_cast
      ring)
  rw [integral_dupMeasure_diff (integrable_cos_mul_cosineWeight d J' n)
    (integrable_cos_mul_cosineWeight d J n) (integrable_cosineWeight d J)
    (integrable_cosineWeight d J'), ← cosinePartition, ← cosinePartition] at h
  rw [div_le_div_iff₀ hZ hZ']
  linarith

/-- **Reflection symmetry.** `⟨sin(n·θ)⟩ = 0` for every coupling. -/
theorem integral_sin_cosineGibbs (d : E → Frequency V) (J : E → ℝ) (n : Frequency V) :
    ∫ θ, Real.sin (phase n θ) ∂cosineGibbs d J = 0 := by
  rw [integral_cosineGibbs]
  have h := integral_neg_rotatorRawAngleMeasure V
    (fun θ => Real.sin (phase n θ) * cosineWeight d J θ)
  simp only [phase_neg_angle, Real.sin_neg, cosineWeight, cosineEnergy_neg, neg_mul,
    integral_neg] at h
  have h0 : ∫ θ, Real.sin (phase n θ) * cosineWeight d J θ ∂rotatorRawAngleMeasure V = 0 := by
    simp only [cosineWeight]
    linarith
  rw [h0, zero_div]

/-! ### Transfer along site embeddings -/

/-- If the energy of a larger system is the energy of a smaller one evaluated on the restricted
angles, then expectations of functions of the restricted angles agree. -/
theorem integral_comp_cosineGibbs {V' E' : Type*} [Fintype V'] [DecidableEq V'] [Fintype E']
    (d : E → Frequency V) (J : E → ℝ) (d' : E' → Frequency V') (J' : E' → ℝ) {ι : V → V'}
    (hι : Function.Injective ι)
    (hH : ∀ θ' : V' → ℝ, cosineEnergy d' J' θ' = cosineEnergy d J (θ' ∘ ι))
    {f : (V → ℝ) → ℝ} (hf : Measurable f) :
    ∫ θ', f (θ' ∘ ι) ∂cosineGibbs d' J' = ∫ θ, f θ ∂cosineGibbs d J := by
  have hw : ∀ θ', cosineWeight d' J' θ' = cosineWeight d J (θ' ∘ ι) := fun θ' => by
    rw [cosineWeight, cosineWeight, hH]
  have hc : (0 : ℝ) < (2 * π) ^ (Fintype.card V' - Fintype.card V) := by positivity
  rw [integral_cosineGibbs, integral_cosineGibbs, cosinePartition, cosinePartition]
  simp_rw [hw]
  rw [integral_comp_rotatorRawAngleMeasure hι (f := fun θ => f θ * cosineWeight d J θ)
      (hf.mul (continuous_cosineWeight d J).measurable).aestronglyMeasurable,
    integral_comp_rotatorRawAngleMeasure hι (f := cosineWeight d J)
      (continuous_cosineWeight d J).aestronglyMeasurable,
    mul_div_mul_left _ _ hc.ne']

/-- **Domain monotonicity.** Let a smaller system embed into a larger one, in the sense that the
larger frequencies with some couplings `0 ≤ J'' ≤ J'` reproduce the smaller energy on the
restricted angles. Then `⟨cos(n·θ)⟩` increases from the smaller system to the larger one. -/
theorem integral_cos_cosineGibbs_le_of_embedding {V' E' : Type*} [Fintype V'] [DecidableEq V']
    [Fintype E'] (d : E → Frequency V) (J : E → ℝ) (d' : E' → Frequency V') {J' J'' : E' → ℝ}
    (hJ'' : ∀ e, 0 ≤ J'' e) (hJ''J' : ∀ e, J'' e ≤ J' e) {ι : V → V'}
    (hι : Function.Injective ι)
    (hH : ∀ θ' : V' → ℝ, cosineEnergy d' J'' θ' = cosineEnergy d J (θ' ∘ ι))
    (n : Frequency V) (n' : Frequency V') (hn : ∀ θ' : V' → ℝ, phase n' θ' = phase n (θ' ∘ ι)) :
    ∫ θ, Real.cos (phase n θ) ∂cosineGibbs d J ≤
      ∫ θ', Real.cos (phase n' θ') ∂cosineGibbs d' J' := by
  have h := integral_comp_cosineGibbs d J d' J'' hι hH
    (f := fun θ => Real.cos (phase n θ))
    (Real.continuous_cos.comp (continuous_phase n)).measurable
  simp_rw [← hn] at h
  rw [← h]
  exact integral_cos_cosineGibbs_mono d' hJ'' hJ''J' n'

end FroehlichSpencer.BKT.Rotator.Ginibre

end
