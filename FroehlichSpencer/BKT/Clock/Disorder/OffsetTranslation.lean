/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.IntegerTranslation
import Mathlib.Tactic

/-!
# Character translation under an offset clock density

The residual field in a vortex-pair decomposition is not generally a graph gradient. This module
extends the compact contour translation identity to an arbitrary fixed real bond offset, the
measure needed on the shifted side of the disorder estimate.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open MeasureTheory Complex
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Generic (edgeRatio)
open FroehlichSpencer.BKT.Reduction (gffCharacter norm_gffCharacter)

variable {d : ℕ} {E : Type} [Fintype E]

/-- The unnormalized clock density with a fixed real edge offset. -/
def clockOffsetDensity (β n : ℝ) (G : Multigraph (Fin d) E) (θ : E → ℝ)
    (φ : Fin d → ℝ) : ℝ :=
  ∏ e, Real.exp (β * Real.cos ((G.grad φ e + θ e) / n))

private theorem clockOffsetDensity_complexProduct (β n : ℝ)
    (G : Multigraph (Fin d) E) (θ : E → ℝ) (φ : Fin d → ℝ) :
    (clockOffsetDensity β n G θ φ : ℂ) =
      ∏ e, clockEdgeWeight β n ((G.grad φ e + θ e : ℝ) : ℂ) := by
  unfold clockOffsetDensity
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro e he
  exact (clockEdgeWeight_ofReal β n (G.grad φ e + θ e)).symm

private def offsetClockContourIntegrand (β n : ℝ) (G : Multigraph (Fin d) E)
    (τ : Fin d → ℝ) (θ : E → ℝ) (z : Fin d → ℂ) : ℂ :=
  clockComplexCharacter τ z *
    ∏ e, clockEdgeWeight β n (z (G.src e) - z (G.tgt e) + (θ e : ℂ))

private theorem offsetClockContourIntegrand_differentiable (β n : ℝ)
    (G : Multigraph (Fin d) E) (τ : Fin d → ℝ) (θ : E → ℝ) :
    Differentiable ℂ (offsetClockContourIntegrand β n G τ θ) := by
  unfold offsetClockContourIntegrand clockComplexCharacter clockEdgeWeight
  fun_prop

private theorem offsetClockCharacter_periodic {n : ℝ} (τ : Fin d → ℝ)
    (hτ : ClockCompatibleCharge n τ) (j : Fin d) (z : Fin d → ℂ) :
    clockComplexCharacter τ (Function.update z j (z j + (clockAnglePeriod n : ℂ))) =
      clockComplexCharacter τ z := by
  obtain ⟨k, hk⟩ := hτ j
  have hsum :
      (∑ i, Function.update z j (z j + (clockAnglePeriod n : ℂ)) i * (τ i : ℂ)) =
        (∑ i, z i * (τ i : ℂ)) + (clockAnglePeriod n : ℂ) * (τ j : ℂ) := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun i => Function.update z j (z j + (clockAnglePeriod n : ℂ)) i * (τ i : ℂ))
      (Finset.mem_univ j)]
    rw [← Finset.sum_erase_add Finset.univ (fun i => z i * (τ i : ℂ)) (Finset.mem_univ j)]
    simp only [Function.update_self]
    have hrest :
        (∑ i ∈ Finset.univ.erase j,
          Function.update z j (z j + (clockAnglePeriod n : ℂ)) i * (τ i : ℂ)) =
          ∑ i ∈ Finset.univ.erase j, z i * (τ i : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hrest]
    ring
  have hkC : (n : ℂ) * (τ j : ℂ) = (k : ℂ) := by exact_mod_cast hk
  have hphase :
      Complex.exp (Complex.I * ((clockAnglePeriod n : ℂ) * (τ j : ℂ))) = 1 := by
    have harg : Complex.I * ((clockAnglePeriod n : ℂ) * (τ j : ℂ)) =
        (k : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [clockAnglePeriod]
      push_cast
      calc
        Complex.I * (2 * ↑Real.pi * ↑n * ↑(τ j)) =
            (↑n * ↑(τ j)) * (2 * ↑Real.pi * Complex.I) := by ring
        _ = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by rw [hkC]
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  unfold clockComplexCharacter
  rw [hsum, mul_add, Complex.exp_add, hphase, mul_one]

private theorem offsetClockEdgeProduct_periodic (β n : ℝ) (hn : 0 < n)
    (G : Multigraph (Fin d) E) (θ : E → ℝ) (j : Fin d) (z : Fin d → ℂ) :
    (∏ e, clockEdgeWeight β n
        (Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.src e) -
          Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.tgt e) + (θ e : ℂ))) =
      ∏ e, clockEdgeWeight β n (z (G.src e) - z (G.tgt e) + (θ e : ℂ)) := by
  apply Finset.prod_congr rfl
  intro e he
  by_cases hs : G.src e = j
  · have ht : G.tgt e ≠ j := by
      intro h
      exact G.src_ne_tgt e (hs.trans h.symm)
    have harg :
        Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.src e) -
          Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.tgt e) + (θ e : ℂ) =
        (z (G.src e) - z (G.tgt e) + (θ e : ℂ)) + (clockAnglePeriod n : ℂ) := by
      rw [hs, Function.update_self, Function.update_of_ne ht]
      ring
    rw [harg]
    exact clockEdgeWeight_periodic β n hn.ne' _
  · by_cases ht : G.tgt e = j
    · have hs' : G.src e ≠ j := hs
      have harg :
          Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.src e) -
            Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.tgt e) + (θ e : ℂ) =
          (z (G.src e) - z (G.tgt e) + (θ e : ℂ)) - (clockAnglePeriod n : ℂ) := by
        rw [Function.update_of_ne hs', ht, Function.update_self]
        ring
      rw [harg]
      have hper := clockEdgeWeight_periodic β n hn.ne'
        (z (G.src e) - z (G.tgt e) + (θ e : ℂ) - (clockAnglePeriod n : ℂ))
      have heq : z (G.src e) - z (G.tgt e) + (θ e : ℂ) -
          (clockAnglePeriod n : ℂ) + (clockAnglePeriod n : ℂ) =
          z (G.src e) - z (G.tgt e) + (θ e : ℂ) := by ring
      rw [heq] at hper
      exact hper.symm
    · simp only [Function.update_of_ne hs, Function.update_of_ne ht]

private theorem offsetClockContourIntegrand_periodic (β n : ℝ) (hn : 0 < n)
    (G : Multigraph (Fin d) E) (τ : Fin d → ℝ) (hτ : ClockCompatibleCharge n τ)
    (θ : E → ℝ) :
    ∀ j z, offsetClockContourIntegrand β n G τ θ
      (Function.update z j (z j + (clockAnglePeriod n : ℂ))) =
        offsetClockContourIntegrand β n G τ θ z := by
  intro j z
  unfold offsetClockContourIntegrand
  rw [offsetClockCharacter_periodic τ hτ j z,
    offsetClockEdgeProduct_periodic β n hn G θ j z]

private theorem offsetClockCharacter_shift (τ φ a : Fin d → ℝ) :
    clockComplexCharacter τ (complexAngleField φ a) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) * gffCharacter τ φ := by
  unfold clockComplexCharacter gffCharacter complexAngleField
  have hsplit :
      (∑ j, ((φ j : ℂ) + (a j : ℂ) * Complex.I) * (τ j : ℂ)) =
        (∑ j, (φ j : ℂ) * (τ j : ℂ)) +
          ∑ j, (a j : ℂ) * Complex.I * (τ j : ℂ) := by
    calc
      _ = ∑ j, ((φ j : ℂ) * (τ j : ℂ) + (a j : ℂ) * Complex.I * (τ j : ℂ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := Finset.sum_add_distrib
  have hreal :
      (∑ j, (a j : ℂ) * Complex.I * (τ j : ℂ)) =
        (∑ j, a j * τ j : ℝ) * Complex.I := by
    calc
      _ = ∑ j, ((a j * τ j : ℝ) : ℂ) * Complex.I := by
        apply Finset.sum_congr rfl
        intro j hj
        push_cast
        ring
      _ = (∑ j, ((a j * τ j : ℝ) : ℂ)) * Complex.I := by rw [Finset.sum_mul]
      _ = _ := by rw [← Complex.ofReal_sum]
  have harg : Complex.I *
      (∑ j, ((φ j : ℂ) + (a j : ℂ) * Complex.I) * (τ j : ℂ)) =
        -((∑ j, a j * τ j : ℝ) : ℂ) +
          Complex.I * ∑ j, (φ j : ℂ) * (τ j : ℂ) := by
    rw [hsplit, hreal]
    push_cast
    rw [mul_add]
    have hI : ∀ x : ℂ, Complex.I * (x * Complex.I) = -x := by
      intro x
      calc
        Complex.I * (x * Complex.I) = (Complex.I * Complex.I) * x := by ring
        _ = -x := by rw [Complex.I_mul_I]; ring
    rw [hI (∑ j, (a j : ℂ) * (τ j : ℂ))]
    ring_nf
  rw [harg, Complex.exp_add]

private theorem offsetClockContourIntegrand_integrable (β n : ℝ) (hβ : 0 ≤ β)
    (hn : 0 < n) (G : Multigraph (Fin d) E) (τ c : Fin d → ℝ) (θ : E → ℝ) :
    Integrable (fun φ => offsetClockContourIntegrand β n G τ θ
      (complexAngleField φ c))
      (compactAngleBaseMeasure (clockAnglePeriod n)) := by
  let A : ℝ := ∑ e : E, |G.grad c e|
  let B : ℝ := Real.exp (|∑ j, c j * τ j|) *
      Real.exp (β * Real.exp (A / n)) ^ Fintype.card E
  have hfield : Continuous (fun φ => complexAngleField φ c) := by
    unfold complexAngleField
    fun_prop
  have hcont : Continuous (fun φ => offsetClockContourIntegrand β n G τ θ
      (complexAngleField φ c)) :=
    (offsetClockContourIntegrand_differentiable β n G τ θ).continuous.comp hfield
  refine Integrable.of_bound hcont.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun φ => ?_)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAedge : ∀ e, |G.grad c e| ≤ A := by
    intro e
    dsimp [A]
    exact Finset.single_le_sum (f := fun e' => |G.grad c e'|)
      (fun e' _ => abs_nonneg _) (Finset.mem_univ e)
  have hgrad (e : E) :
      complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e) +
          (θ e : ℂ) =
        ((G.grad φ e + θ e : ℝ) : ℂ) + ((G.grad c e : ℝ) : ℂ) * Complex.I := by
    change ((φ (G.src e) : ℂ) + (c (G.src e) : ℂ) * Complex.I) -
        ((φ (G.tgt e) : ℂ) + (c (G.tgt e) : ℂ) * Complex.I) + (θ e : ℂ) =
      ((φ (G.src e) - φ (G.tgt e) + θ e : ℝ) : ℂ) +
        ((c (G.src e) - c (G.tgt e) : ℝ) : ℂ) * Complex.I
    push_cast
    ring_nf
  have hedge (e : E) :
      ‖clockEdgeWeight β n (complexAngleField φ c (G.src e) -
        complexAngleField φ c (G.tgt e) + (θ e : ℂ))‖ ≤
        Real.exp (β * Real.exp (A / n)) := by
    rw [hgrad e]
    exact clockEdgeWeight_compact_rect_bound β n hβ hn A
      (G.grad φ e + θ e) (G.grad c e) (hAedge e)
  have hprod :
      ‖∏ e, clockEdgeWeight β n
        (complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e) + (θ e : ℂ))‖ ≤
        Real.exp (β * Real.exp (A / n)) ^ Fintype.card E := by
    rw [norm_prod]
    calc
      ∏ e, ‖clockEdgeWeight β n
          (complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e) + (θ e : ℂ))‖ ≤
          ∏ _e : E, Real.exp (β * Real.exp (A / n)) := by
            apply Finset.prod_le_prod₀
            · intro e he
              positivity
            · intro e he
              exact hedge e
      _ = _ := by simp
  have hchar : ‖clockComplexCharacter τ (complexAngleField φ c)‖ ≤
      Real.exp |∑ j, c j * τ j| := by
    rw [offsetClockCharacter_shift, norm_mul, Complex.norm_exp,
      norm_gffCharacter, mul_one]
    have hre : (-((∑ j, c j * τ j : ℝ) : ℂ)).re = -(∑ j, c j * τ j) := by simp
    rw [hre]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    ‖offsetClockContourIntegrand β n G τ θ (complexAngleField φ c)‖ =
        ‖clockComplexCharacter τ (complexAngleField φ c)‖ *
          ‖∏ e, clockEdgeWeight β n
            (complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e) + (θ e : ℂ))‖ := by
          rw [offsetClockContourIntegrand, norm_mul]
    _ ≤ Real.exp |∑ j, c j * τ j| *
          Real.exp (β * Real.exp (A / n)) ^ Fintype.card E :=
        mul_le_mul hchar hprod (norm_nonneg _) (by positivity)
    _ = B := rfl

private theorem offsetClockContour_shift_pointwise (β n : ℝ)
    (G : Multigraph (Fin d) E) (τ φ a : Fin d → ℝ) (θ : E → ℝ) :
    offsetClockContourIntegrand β n G τ θ (complexAngleField φ a) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ((clockOffsetDensity β n G θ φ : ℂ) * gffCharacter τ φ *
          edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ + θ)) := by
  unfold offsetClockContourIntegrand
  rw [offsetClockCharacter_shift]
  have hgrad (e : E) :
      complexAngleField φ a (G.src e) - complexAngleField φ a (G.tgt e) +
          (θ e : ℂ) = ((G.grad φ e + θ e : ℝ) : ℂ) +
            ((G.grad a e : ℝ) : ℂ) * Complex.I := by
    change ((φ (G.src e) : ℂ) + (a (G.src e) : ℂ) * Complex.I) -
        ((φ (G.tgt e) : ℂ) + (a (G.tgt e) : ℂ) * Complex.I) + (θ e : ℂ) =
      ((φ (G.src e) - φ (G.tgt e) + θ e : ℝ) : ℂ) +
        ((a (G.src e) - a (G.tgt e) : ℝ) : ℂ) * Complex.I
    push_cast
    ring_nf
  have hprod :
      ∏ e, clockEdgeWeight β n
          (complexAngleField φ a (G.src e) - complexAngleField φ a (G.tgt e) + (θ e : ℂ)) =
        (clockOffsetDensity β n G θ φ : ℂ) *
          edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ + θ) := by
    unfold edgeRatio clockOffsetDensity
    rw [Complex.ofReal_prod]
    simp_rw [clockEdgeWeight_ofReal]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e he
    have harg := hgrad e
    have hden : clockEdgeWeight β n ((G.grad φ e + θ e : ℝ) : ℂ) ≠ 0 :=
      clockEdgeWeight_ne_zero β n _
    rw [harg]
    field_simp [hden]
    have hbase : (G.grad φ + θ) e = G.grad φ e + θ e := rfl
    have hreal : (Real.exp (β * Real.cos ((G.grad φ + θ) e / n)) : ℂ) =
        clockEdgeWeight β n ((G.grad φ e + θ e : ℝ) : ℂ) := by
      simpa only [hbase] using (clockEdgeWeight_ofReal β n (G.grad φ e + θ e)).symm
    rw [hreal]
    rw [hbase]
    rw [(clockEdgeWeight_ofReal β n (G.grad φ e + θ e)).symm]
    ring
  rw [hprod]
  ring

/-- Compact character translation for the clock edge product with an arbitrary fixed real bond
offset. -/
theorem integral_clockOffsetCharacterTranslation {n β : ℝ} (hn : 0 < n)
    (hβ : 0 ≤ β) (G : Multigraph (Fin d) E) (τ a : Fin d → ℝ)
    (hτ : ClockCompatibleCharge n τ) (θ : E → ℝ) :
    ∫ φ, ((clockOffsetDensity β n G θ φ : ℝ) : ℂ) * gffCharacter τ φ
      ∂clockAngleBaseMeasure n =
    Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
      ∫ φ, ((clockOffsetDensity β n G θ φ : ℝ) : ℂ) * gffCharacter τ φ *
        edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ + θ)
      ∂clockAngleBaseMeasure n := by
  let F := offsetClockContourIntegrand β n G τ θ
  have hP : 0 < clockAnglePeriod n := by
    unfold clockAnglePeriod
    positivity
  have hF : Differentiable ℂ F := by
    dsimp [F]
    exact offsetClockContourIntegrand_differentiable β n G τ θ
  have hperiodic : ∀ j z,
      F (Function.update z j (z j + (clockAnglePeriod n : ℂ))) = F z :=
    offsetClockContourIntegrand_periodic β n hn G τ hτ θ
  have hint : ∀ c : Fin d → ℝ,
      Integrable (fun φ => F (complexAngleField φ c))
        (compactAngleBaseMeasure (clockAnglePeriod n)) := by
    intro c
    exact offsetClockContourIntegrand_integrable β n hβ hn G τ c θ
  have hshift : compactAngleIntegral (clockAnglePeriod n) F 0 =
      compactAngleIntegral (clockAnglePeriod n) F a :=
    compactAngleIntegral_complexShift hP F hF hperiodic a hint
  have hcontour :
      ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n =
        ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n := by
    simpa [compactAngleIntegral, clockAngleBaseMeasure] using hshift
  have hleft :
      ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n =
        ∫ φ, ((clockOffsetDensity β n G θ φ : ℝ) : ℂ) * gffCharacter τ φ
          ∂clockAngleBaseMeasure n := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun φ => by
      have hz : complexAngleField φ 0 = fun j => (φ j : ℂ) := by
        funext j
        simp [complexAngleField]
      change offsetClockContourIntegrand β n G τ θ
        (complexAngleField φ 0) = _
      rw [hz]
      change clockComplexCharacter τ (fun j => (φ j : ℂ)) *
        (∏ e, clockEdgeWeight β n
          ((φ (G.src e) : ℂ) - (φ (G.tgt e) : ℂ) + (θ e : ℂ))) =
          ((clockOffsetDensity β n G θ φ : ℝ) : ℂ) * gffCharacter τ φ
      have hprod :
          (∏ e, clockEdgeWeight β n
            ((φ (G.src e) : ℂ) - (φ (G.tgt e) : ℂ) + (θ e : ℂ))) =
          ∏ e, clockEdgeWeight β n ((G.grad φ e + θ e : ℝ) : ℂ) := by
        apply Finset.prod_congr rfl
        intro e he
        congr 1
        simp [Multigraph.grad]
      rw [hprod]
      rw [clockOffsetDensity_complexProduct]
      rw [show clockComplexCharacter τ (fun j => (φ j : ℂ)) = gffCharacter τ φ from rfl]
      exact mul_comm (gffCharacter τ φ)
        (∏ e, clockEdgeWeight β n ((G.grad φ e + θ e : ℝ) : ℂ))
  have hright :
      ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n =
        Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
          ∫ φ, ((clockOffsetDensity β n G θ φ : ℝ) : ℂ) * gffCharacter τ φ *
            edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ + θ)
            ∂clockAngleBaseMeasure n := by
    calc
      _ = ∫ φ, Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
            ((clockOffsetDensity β n G θ φ : ℂ) * gffCharacter τ φ *
              edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ + θ))
            ∂clockAngleBaseMeasure n := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun φ => by
            change offsetClockContourIntegrand β n G τ θ
              (complexAngleField φ a) = _
            exact offsetClockContour_shift_pointwise β n G τ φ a θ
      _ = _ := by rw [integral_const_mul]
  calc
    _ = ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n := hleft.symm
    _ = ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n := hcontour
    _ = _ := hright

end FroehlichSpencer.BKT.Clock.Disorder

end
