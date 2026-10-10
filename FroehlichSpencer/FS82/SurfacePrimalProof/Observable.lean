/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.SurfacePrimal.SourcePrimalFieldStrength
public import FroehlichSpencer.FS82.PrimalInterface.PrimalBridge
public import FroehlichSpencer.FS82.Wilson.PrimalFieldStrength
import Mathlib.Tactic

@[expose] public section
open MeasureTheory
namespace FroehlichSpencer.FS82.SurfaceInfinite

theorem sourcePrimalGaussian_eq_villainWeight (β x : ℝ) :
    (∑' n : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * n) ^ 2)) =
      Wilson.villainWeight β x := by
  unfold Wilson.villainWeight
  rw [← (Equiv.neg ℤ).tsum_eq fun m : ℤ =>
    Real.exp (-(β / 2) * (x - 2 * Real.pi * m) ^ 2)]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply, Int.cast_neg]
  congr 1
  ring

theorem villainWeight_deriv_sub_two_pi_mul_int (β x : ℝ) (hβ : 0 < β) (k : ℤ) :
    deriv (fun y : ℝ => Wilson.villainWeight β (y - 2 * Real.pi * k)) x =
      deriv (Wilson.villainWeight β) x := by
  have hf := Wilson.villainWeight_hasDerivAt_fourier β (x - 2 * Real.pi * k) hβ
  have hshift : HasDerivAt
      (fun y : ℝ => Wilson.villainWeight β (y - 2 * Real.pi * k))
      (deriv (Wilson.villainWeight β) (x - 2 * Real.pi * k)) x := by
    have hid : HasDerivAt (fun y : ℝ => y - 2 * Real.pi * k) 1 x := by
      convert (hasDerivAt_id x).sub_const (2 * Real.pi * k) using 1; simp
    have hcomp := hf.comp x hid
    convert hcomp using 1
    · rfl
    · rw [hf.deriv]
      ring
  have hfun : (fun y : ℝ => Wilson.villainWeight β (y - 2 * Real.pi * k)) =
      Wilson.villainWeight β := by
    funext y
    exact PrimalInterface.villainWeight_sub_two_pi_mul_int β y k
  have hsame := hshift.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (congrFun hfun.symm))
  exact hshift.deriv.trans hsame.deriv.symm

theorem villainCircleFieldStrength_angleToCircle (β x : ℝ) (hβ : 0 < β) :
    Wilson.villainCircleFieldStrength β (PrimalInterface.angleToCircle x) =
      Wilson.villainFieldStrengthRepresentative β x := by
  have hcoe : ((Wilson.circleRepresentative (PrimalInterface.angleToCircle x) : ℝ) : UnitAddCircle) =
      ((x / (2 * Real.pi) : ℝ) : UnitAddCircle) := Wilson.circleRepresentative_coe _
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp hcoe)
  have hrep : 2 * Real.pi * Wilson.circleRepresentative (PrimalInterface.angleToCircle x) =
      x - 2 * Real.pi * k := by
    have hk' : (k : ℝ) = -Wilson.circleRepresentative (PrimalInterface.angleToCircle x) + x / (2 * Real.pi) := by
      simpa using hk
    rw [hk']
    field_simp
    ring
  have hderiv : deriv (Wilson.villainWeight β) (2 * Real.pi *
      Wilson.circleRepresentative (PrimalInterface.angleToCircle x)) =
      deriv (Wilson.villainWeight β) x := by
    rw [hrep]
    have h := villainWeight_deriv_sub_two_pi_mul_int β x hβ k
    have hf := Wilson.villainWeight_hasDerivAt_fourier β
      (x - 2 * Real.pi * k) hβ
    have hid : HasDerivAt (fun y : ℝ => y - 2 * Real.pi * k) 1 x := by
      convert (hasDerivAt_id x).sub_const (2 * Real.pi * k) using 1
      simp
    have hc := hf.comp x hid
    have hchain : deriv (fun y : ℝ => Wilson.villainWeight β
        (y - 2 * Real.pi * k)) x =
        deriv (Wilson.villainWeight β) (x - 2 * Real.pi * k) := by
      have hcomp : HasDerivAt (fun y : ℝ => Wilson.villainWeight β
          (y - 2 * Real.pi * k)) (deriv (Wilson.villainWeight β)
          (x - 2 * Real.pi * k)) x := by
        convert hc using 1
        · rfl
        · rw [hf.deriv]
          ring
      exact hcomp.deriv
    rw [hchain] at h
    exact h
  have hnum : Wilson.villainCircleFieldStrengthNumerator β (PrimalInterface.angleToCircle x) =
      Wilson.villainFieldStrengthNumerator β x := by
    rw [Wilson.villainCircleFieldStrengthNumerator_eq_representative β _ hβ]
    unfold Wilson.villainFieldStrengthNumerator
    rw [hderiv]
  have hden : Wilson.villainCircleWeight β (PrimalInterface.angleToCircle x) =
      Wilson.villainWeight β x := by
    rw [Wilson.villainCircleWeight_eq_periodized β (PrimalInterface.angleToCircle x) hβ]
    exact PrimalInterface.villainWeight_circleRepresentative β x
  unfold Wilson.villainCircleFieldStrength Wilson.villainFieldStrengthRepresentative
  rw [hnum, hden]

theorem sourcePrimalFieldStrength_eq_circle (R : Surface.RectBox4)
    (β : ℝ) (hβ : 0 < β) (θ : Surface.PrimalLinks R → ℝ)
    (p : Surface.PrimalPlaquettes R) :
    sourcePrimalFieldStrength R β hβ θ p =
      Wilson.primalFieldStrength β (PrimalInterface.toCircleConfig R θ) (PrimalInterface.plaquetteEquiv R p) := by
  unfold sourcePrimalFieldStrength Wilson.primalFieldStrength
  rw [PrimalInterface.primalPlaquetteFlux_toCircleConfig]
  change (-Complex.I) *
      ((deriv (fun y : ℝ => ∑' n : ℤ,
        Real.exp (-(β / 2) * (y + 2 * Real.pi * n) ^ 2))
        (Surface.primalPlaquetteCurl R θ p) : ℝ) : ℂ) /
        ((∑' n : ℤ, Real.exp (-(β / 2) *
          (Surface.primalPlaquetteCurl R θ p + 2 * Real.pi * n) ^ 2) : ℝ) : ℂ) =
      Wilson.villainCircleFieldStrength β
        (PrimalInterface.angleToCircle (Surface.primalPlaquetteCurl R θ p))
  let x := Surface.primalPlaquetteCurl R θ p
  rw [show (fun y : ℝ => ∑' n : ℤ,
      Real.exp (-(β / 2) * (y + 2 * Real.pi * n) ^ 2)) = Wilson.villainWeight β by
        funext y
        exact sourcePrimalGaussian_eq_villainWeight β y]
  rw [sourcePrimalGaussian_eq_villainWeight β x,
    villainCircleFieldStrength_angleToCircle β x hβ]
  rfl

end FroehlichSpencer.FS82.SurfaceInfinite

end
