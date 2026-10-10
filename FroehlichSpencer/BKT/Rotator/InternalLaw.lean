/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.FreeBox
public import FroehlichSpencer.BKT.Rotator.CurrentIntegration
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The finite internal plane-rotator law

This is the free-box spin law with all internal nearest-neighbour bonds and the raw angle
representatives in `[-π,π)`. The partition integral is positive, so its Gibbs density defines an
internal probability measure. The current-integration identities are stated separately in
`CurrentIntegration.lean`; connecting that series to this density uses the cosine Fourier expansion.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

variable (L : ℕ)

private instance rotatorLawAngleCoordinate_isFiniteMeasure :
    IsFiniteMeasure (volume.restrict (Ico (-Real.pi) Real.pi)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, Real.volume_Ico]
  exact ENNReal.ofReal_lt_top

/-- Real angle representatives at every free spin site. -/
abbrev RotatorAngleConfiguration := RotatorSpinSite L → ℝ

/-- The real plane-rotator Boltzmann factor on one internal bond. -/
def rotatorBondDensity (β : ℝ) (θ : RotatorAngleConfiguration L)
    (e : RotatorInternalBond L) : ℝ :=
  Real.exp (β * Real.cos
    (θ ((rotatorFreeGraph L).src e) - θ ((rotatorFreeGraph L).tgt e)))

/-- The plane-rotator Boltzmann density, with one factor for every internal bond. -/
def rotatorSpinDensity (β : ℝ) (θ : RotatorAngleConfiguration L) : ℝ :=
  ∏ e, rotatorBondDensity L β θ e

/-- Its raw finite-volume partition integral. -/
def rotatorPartitionIntegralInternal (β : ℝ) : ℝ :=
  ∫ θ, rotatorSpinDensity L β θ ∂rotatorRawAngleMeasure (RotatorSpinSite L)

/-- The integer spin character used in the marked two-point function. -/
def rotatorSpinCharacter (a x : RotatorSpinSite L) (ξ : ℤ)
    (θ : RotatorAngleConfiguration L) : ℂ :=
  Complex.exp (Complex.I * (ξ : ℂ) * ((θ a - θ x : ℝ) : ℂ))

/-- The normalized internal free-box plane-rotator Gibbs measure. -/
def rotatorMeasureInternal (β : ℝ) : Measure (RotatorAngleConfiguration L) :=
  (rotatorRawAngleMeasure (RotatorSpinSite L)).withDensity fun θ =>
    ENNReal.ofReal (rotatorSpinDensity L β θ / rotatorPartitionIntegralInternal L β)

theorem rotatorBondDensity_pos (β : ℝ) (θ : RotatorAngleConfiguration L)
    (e : RotatorInternalBond L) : 0 < rotatorBondDensity L β θ e :=
  Real.exp_pos _

theorem rotatorSpinDensity_pos (β : ℝ) (θ : RotatorAngleConfiguration L) :
    0 < rotatorSpinDensity L β θ := by
  unfold rotatorSpinDensity
  exact Finset.prod_pos fun e he => rotatorBondDensity_pos L β θ e

theorem continuous_rotatorSpinDensity (β : ℝ) :
    Continuous (rotatorSpinDensity L β) := by
  unfold rotatorSpinDensity rotatorBondDensity
  fun_prop

private theorem rotatorSpinDensity_le_bound (β : ℝ)
    (θ : RotatorAngleConfiguration L) :
    rotatorSpinDensity L β θ ≤ ∏ _e : RotatorInternalBond L, Real.exp |β| := by
  unfold rotatorSpinDensity rotatorBondDensity
  apply Finset.prod_le_prod₀
  · intro e he
    exact (Real.exp_pos _).le
  · intro e he
    apply Real.exp_le_exp.mpr
    calc
      β * Real.cos
          (θ ((rotatorFreeGraph L).src e) - θ ((rotatorFreeGraph L).tgt e)) ≤
          |β * Real.cos
            (θ ((rotatorFreeGraph L).src e) - θ ((rotatorFreeGraph L).tgt e))| := le_abs_self _
      _ = |β| * |Real.cos
            (θ ((rotatorFreeGraph L).src e) - θ ((rotatorFreeGraph L).tgt e))| := abs_mul _ _
      _ ≤ |β| * 1 := by
        exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |β| := by ring

private theorem rotatorSpinDensity_integrable (β : ℝ) :
    Integrable (rotatorSpinDensity L β)
      (rotatorRawAngleMeasure (RotatorSpinSite L)) := by
  let μ := rotatorRawAngleMeasure (RotatorSpinSite L)
  have hμ : IsFiniteMeasure μ := by
    dsimp [μ, rotatorRawAngleMeasure]
    infer_instance
  have hcont := continuous_rotatorSpinDensity L β
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards with θ
  rw [Real.norm_of_nonneg (rotatorSpinDensity_pos L β θ).le]
  exact rotatorSpinDensity_le_bound L β θ

private theorem rotatorRawAngleMeasure_univ_pos :
    0 < rotatorRawAngleMeasure (RotatorSpinSite L) Set.univ := by
  unfold rotatorRawAngleMeasure
  rw [← Set.pi_univ (Set.univ : Set (RotatorSpinSite L)), Measure.pi_pi]
  simp [Real.volume_Ico]
  positivity

/-- Positivity of the free-box spin partition integral. -/
theorem rotatorPartitionIntegralInternal_pos (β : ℝ) :
    0 < rotatorPartitionIntegralInternal L β := by
  rw [rotatorPartitionIntegralInternal,
    integral_pos_iff_support_of_nonneg (fun θ => (rotatorSpinDensity_pos L β θ).le)
      (rotatorSpinDensity_integrable L β)]
  have hsupp : Function.support (rotatorSpinDensity L β) = Set.univ := by
    ext θ
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (rotatorSpinDensity_pos L β θ)
  rw [hsupp]
  exact rotatorRawAngleMeasure_univ_pos L

/-- Total mass of the normalized internal spin law. -/
theorem rotatorMeasureInternal_univ (β : ℝ) :
    rotatorMeasureInternal L β Set.univ = 1 := by
  have hZ := rotatorPartitionIntegralInternal_pos L β
  have hweight := rotatorSpinDensity_integrable L β
  have hscaled : Integrable
      (fun θ : RotatorAngleConfiguration L =>
        rotatorSpinDensity L β θ * (rotatorPartitionIntegralInternal L β)⁻¹)
      (rotatorRawAngleMeasure (RotatorSpinSite L)) :=
    hweight.mul_const _
  have hnonneg : 0 ≤ᵐ[rotatorRawAngleMeasure (RotatorSpinSite L)]
      fun θ : RotatorAngleConfiguration L =>
        rotatorSpinDensity L β θ * (rotatorPartitionIntegralInternal L β)⁻¹ := by
    filter_upwards with θ
    exact mul_nonneg (rotatorSpinDensity_pos L β θ).le (inv_nonneg.mpr hZ.le)
  calc
    rotatorMeasureInternal L β Set.univ =
        ∫⁻ θ, ENNReal.ofReal
          (rotatorSpinDensity L β θ / rotatorPartitionIntegralInternal L β)
          ∂rotatorRawAngleMeasure (RotatorSpinSite L) := by
      rw [rotatorMeasureInternal, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ]
    _ = ENNReal.ofReal
        (∫ θ, rotatorSpinDensity L β θ /
          rotatorPartitionIntegralInternal L β
          ∂rotatorRawAngleMeasure (RotatorSpinSite L)) := by
      simpa only [div_eq_mul_inv] using
        (ofReal_integral_eq_lintegral_ofReal hscaled hnonneg).symm
    _ = 1 := by
      have hintegral :
          (∫ θ, rotatorSpinDensity L β θ /
              rotatorPartitionIntegralInternal L β
              ∂rotatorRawAngleMeasure (RotatorSpinSite L)) =
          (∫ θ, rotatorSpinDensity L β θ
              ∂rotatorRawAngleMeasure (RotatorSpinSite L)) *
                (rotatorPartitionIntegralInternal L β)⁻¹ := by
        calc
          (∫ θ, rotatorSpinDensity L β θ /
              rotatorPartitionIntegralInternal L β
              ∂rotatorRawAngleMeasure (RotatorSpinSite L)) =
            ∫ θ, rotatorSpinDensity L β θ *
              (rotatorPartitionIntegralInternal L β)⁻¹
              ∂rotatorRawAngleMeasure (RotatorSpinSite L) := by
                apply integral_congr_ae
                exact ae_of_all _ fun θ => div_eq_mul_inv _ _
          _ = (∫ θ, rotatorSpinDensity L β θ
                ∂rotatorRawAngleMeasure (RotatorSpinSite L)) *
                  (rotatorPartitionIntegralInternal L β)⁻¹ :=
            integral_mul_const _ _
      rw [hintegral, ← rotatorPartitionIntegralInternal]
      simp [hZ.ne']

instance rotatorMeasureInternal_isProbability (β : ℝ) :
    IsProbabilityMeasure (rotatorMeasureInternal L β) :=
  IsProbabilityMeasure.mk (rotatorMeasureInternal_univ L β)

/-- The marked two-point expectation under the internal spin law is the raw marked integral against
the normalized Boltzmann density. This is the measure-theoretic normalization used when the
Fourier/current expansion is substituted. -/
theorem rotatorMeasureInternal_character_integral (β : ℝ)
    (a x : RotatorSpinSite L) (ξ : ℤ) :
    (∫ θ, rotatorSpinCharacter L a x ξ θ ∂rotatorMeasureInternal L β) =
      (∫ θ,
        ((rotatorSpinDensity L β θ / rotatorPartitionIntegralInternal L β : ℝ) : ℂ) *
          rotatorSpinCharacter L a x ξ θ
        ∂rotatorRawAngleMeasure (RotatorSpinSite L)) := by
  have hZ := rotatorPartitionIntegralInternal_pos L β
  have hden : Measurable fun θ : RotatorAngleConfiguration L =>
      ENNReal.ofReal
        (rotatorSpinDensity L β θ / rotatorPartitionIntegralInternal L β) := by
    exact ((continuous_rotatorSpinDensity L β).measurable.div_const _).ennreal_ofReal
  have htop : ∀ᵐ θ ∂rotatorRawAngleMeasure (RotatorSpinSite L),
      ENNReal.ofReal
        (rotatorSpinDensity L β θ / rotatorPartitionIntegralInternal L β) < ⊤ := by
    filter_upwards with θ
    exact ENNReal.ofReal_lt_top
  rw [rotatorMeasureInternal]
  rw [integral_withDensity_eq_integral_toReal_smul hden htop]
  have hreal (θ : RotatorAngleConfiguration L) :
      (ENNReal.ofReal
        (rotatorSpinDensity L β θ / rotatorPartitionIntegralInternal L β)).toReal =
          rotatorSpinDensity L β θ / rotatorPartitionIntegralInternal L β := by
    rw [ENNReal.toReal_ofReal]
    exact div_nonneg (rotatorSpinDensity_pos L β θ).le hZ.le
  apply integral_congr_ae
  filter_upwards with θ
  rw [hreal, RCLike.real_smul_eq_coe_mul]
  rfl

end FroehlichSpencer.BKT.Rotator

end
