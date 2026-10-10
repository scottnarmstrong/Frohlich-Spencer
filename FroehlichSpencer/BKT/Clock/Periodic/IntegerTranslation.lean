/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.CharacterTranslation
public import FroehlichSpencer.BKT.Generic.LocalFactor

/-!
# Compact-periodic translation for integer charges

The generic T1.6 translation theorem accepts every neutral real-valued charge.

A compact torus
instead requires each site frequency to be compatible with the period.

This module proves the
compact contour identity without a neutrality premise, then specializes it to integer-valued
charges.

This proves the compact-specific character-translation step that the proof of
`Generic.edgeLaw_integral_ensemble_eq` needs to replace: the neutral KP charge-layer densities are
integer-valued, hence period-compatible.

It does not supply the rest of `IsStripWeight`-based T1.6
assembly or the scale induction.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic (edgeRatio translatedCos translationEnergy localFactor)
open FroehlichSpencer.BKT.Reduction (gffCharacter norm_gffCharacter)

variable {d : ℕ} {E : Type*} [Fintype E]

private theorem complexCharacter_periodic_compatible {n : ℝ} (τ : Fin d → ℝ)
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

private theorem complexEdgeProduct_periodic (β n : ℝ) (hn : 0 < n)
    (G : Multigraph (Fin d) E) (j : Fin d) (z : Fin d → ℂ) :
    clockComplexEdgeProduct β n G
        (Function.update z j (z j + (clockAnglePeriod n : ℂ))) =
      clockComplexEdgeProduct β n G z := by
  unfold clockComplexEdgeProduct
  apply Finset.prod_congr rfl
  intro e he
  by_cases hs : G.src e = j
  · have ht : G.tgt e ≠ j := by
      intro h
      exact G.src_ne_tgt e (hs.trans h.symm)
    have harg : Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.src e) -
          Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.tgt e) =
        (z (G.src e) - z (G.tgt e)) + (clockAnglePeriod n : ℂ) := by
      rw [hs, Function.update_self, Function.update_of_ne ht]
      ring
    rw [harg]
    exact clockEdgeWeight_periodic β n hn.ne' _
  · by_cases ht : G.tgt e = j
    · have hs' : G.src e ≠ j := hs
      have harg : Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.src e) -
            Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.tgt e) =
        (z (G.src e) - z (G.tgt e)) - (clockAnglePeriod n : ℂ) := by
        rw [Function.update_of_ne hs', ht, Function.update_self]
        ring
      rw [harg]
      have hper := clockEdgeWeight_periodic β n hn.ne'
        (z (G.src e) - z (G.tgt e) - (clockAnglePeriod n : ℂ))
      have heq : z (G.src e) - z (G.tgt e) - (clockAnglePeriod n : ℂ) +
          (clockAnglePeriod n : ℂ) = z (G.src e) - z (G.tgt e) := by ring
      rw [heq] at hper
      exact hper.symm
    · simp only [Function.update_of_ne hs, Function.update_of_ne ht]

private theorem contourIntegrand_periodic_compatible (β n : ℝ) (hn : 0 < n)
    (G : Multigraph (Fin d) E) (τ : Fin d → ℝ) (hτ : ClockCompatibleCharge n τ) :
    ∀ j z, clockContourIntegrand β n G τ
      (Function.update z j (z j + (clockAnglePeriod n : ℂ))) = clockContourIntegrand β n G τ z := by
  intro j z
  unfold clockContourIntegrand
  rw [complexCharacter_periodic_compatible τ hτ j z,
    complexEdgeProduct_periodic β n hn G j z]

private theorem complexCharacter_shift (τ φ a : Fin d → ℝ) :
    clockComplexCharacter τ (complexAngleField φ a) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) * gffCharacter τ φ := by
  unfold clockComplexCharacter gffCharacter complexAngleField
  have hsum :
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
    rw [hsum, hreal]
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

private theorem complexCharacter_ofReal (τ φ : Fin d → ℝ) :
    clockComplexCharacter τ (fun j => (φ j : ℂ)) = gffCharacter τ φ := rfl

private theorem contourIntegrand_integrable (β n : ℝ) (hβ : 0 ≤ β) (hn : 0 < n)
    (G : Multigraph (Fin d) E) (τ c : Fin d → ℝ) :
    Integrable (fun φ => clockContourIntegrand β n G τ (complexAngleField φ c))
      (compactAngleBaseMeasure (d := d) (clockAnglePeriod n)) := by
  let A : ℝ := ∑ e : E, |G.grad c e|
  let B : ℝ := Real.exp (|∑ j, c j * τ j|) *
      Real.exp (β * Real.exp (A / n)) ^ Fintype.card E
  have hfield : Continuous (fun φ => complexAngleField φ c) := by
    unfold complexAngleField
    fun_prop
  have hcont : Continuous
      (fun φ => clockContourIntegrand β n G τ (complexAngleField φ c)) :=
    (differentiable_clockContourIntegrand β n G τ).continuous.comp hfield
  refine Integrable.of_bound hcont.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun φ => ?_)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAedge : ∀ e, |G.grad c e| ≤ A := by
    intro e
    dsimp [A]
    exact Finset.single_le_sum (f := fun e' => |G.grad c e'|)
      (fun e' _ => abs_nonneg _) (Finset.mem_univ e)
  have hgrad (e : E) :
      complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e) =
        ((G.grad (φ : Fin d → ℝ) e : ℝ) : ℂ) +
          ((G.grad (c : Fin d → ℝ) e : ℝ) : ℂ) * Complex.I := by
    change ((φ (G.src e) : ℂ) + (c (G.src e) : ℂ) * Complex.I) -
        ((φ (G.tgt e) : ℂ) + (c (G.tgt e) : ℂ) * Complex.I) =
      ((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ) +
        ((c (G.src e) - c (G.tgt e) : ℝ) : ℂ) * Complex.I
    push_cast
    ring_nf
  have hedge (e : E) :
      ‖clockEdgeWeight β n (complexAngleField φ c (G.src e) -
        complexAngleField φ c (G.tgt e))‖ ≤ Real.exp (β * Real.exp (A / n)) := by
    rw [hgrad e]
    exact clockEdgeWeight_compact_rect_bound β n hβ hn A (G.grad φ e) (G.grad c e)
      (hAedge e)
  have hprod : ‖clockComplexEdgeProduct β n G (complexAngleField φ c)‖ ≤
      Real.exp (β * Real.exp (A / n)) ^ Fintype.card E := by
    unfold clockComplexEdgeProduct
    rw [norm_prod]
    calc
      ∏ e, ‖clockEdgeWeight β n (complexAngleField φ c (G.src e) -
          complexAngleField φ c (G.tgt e))‖ ≤
          ∏ _e : E, Real.exp (β * Real.exp (A / n)) := by
            apply Finset.prod_le_prod₀
            · intro e he
              positivity
            · intro e he
              exact hedge e
      _ = _ := by simp
  have hchar : ‖clockComplexCharacter τ (complexAngleField φ c)‖ ≤
      Real.exp |∑ j, c j * τ j| := by
    rw [complexCharacter_shift τ φ c, norm_mul, Complex.norm_exp,
      norm_gffCharacter, mul_one]
    have hre : (-(∑ j, c j * τ j : ℝ) : ℂ).re = -(∑ j, c j * τ j) := by simp
    rw [hre]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    ‖clockContourIntegrand β n G τ (complexAngleField φ c)‖ =
        ‖clockComplexCharacter τ (complexAngleField φ c)‖ *
          ‖clockComplexEdgeProduct β n G (complexAngleField φ c)‖ := by
          rw [clockContourIntegrand, norm_mul]
    _ ≤ Real.exp |∑ j, c j * τ j| *
          Real.exp (β * Real.exp (A / n)) ^ Fintype.card E :=
        mul_le_mul hchar hprod (norm_nonneg _) (by positivity)
    _ = B := rfl

private theorem integral_clockBoxLaw_as_base (β n : ℝ) (hβ : 0 ≤ β)
    (G : Multigraph (Fin d) E) (f : (Fin d → ℝ) → ℂ) :
    ∫ φ, f φ ∂clockBoxLaw β n G =
      (((clockBoxMass β n G)⁻¹).toReal : ℂ) *
        ∫ φ, (clockBoxDensity β n G φ : ℂ) * f φ ∂clockAngleBaseMeasure n := by
  let ρ := clockBoxDensity β n G
  have hρmeas : Measurable ρ := by dsimp [ρ]; exact measurable_clockBoxDensity β n G
  have hρnonneg : ∀ φ, 0 ≤ ρ φ := fun φ => by
    dsimp [ρ]
    exact (le_of_lt (pow_pos (Real.exp_pos _) _)).trans (clockBoxDensity_bounds G hβ φ).1
  have hbase :
      ∫ φ, f φ ∂(clockAngleBaseMeasure n).withDensity (fun φ => ENNReal.ofReal (ρ φ)) =
        ∫ φ, (ρ φ : ℂ) * f φ ∂clockAngleBaseMeasure n := by
    calc
      _ = ∫ φ, (ENNReal.ofReal (ρ φ)).toReal • f φ ∂clockAngleBaseMeasure n :=
        integral_withDensity_eq_integral_toReal_smul (ENNReal.measurable_ofReal.comp hρmeas)
          (Filter.Eventually.of_forall fun φ => ENNReal.ofReal_lt_top) f
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with φ
        simp [ENNReal.toReal_ofReal (hρnonneg φ), Complex.real_smul]
  change ∫ φ, f φ ∂((clockBoxMass β n G)⁻¹ •
    (clockAngleBaseMeasure n).withDensity fun φ => ENNReal.ofReal (ρ φ)) = _
  rw [integral_smul_measure, hbase, Complex.real_smul]

private theorem complexEdgeProduct_ofReal (β n : ℝ) (G : Multigraph (Fin d) E)
    (φ : Fin d → ℝ) :
    clockComplexEdgeProduct β n G (fun j => (φ j : ℂ)) =
      (clockBoxDensity β n G φ : ℂ) := by
  simp only [clockComplexEdgeProduct, clockBoxDensity, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro e he
  rw [← Complex.ofReal_sub]
  simp only [Multigraph.grad, clockEdgeWeight_ofReal, Complex.ofReal_re]

private theorem complexEdgeProduct_shift (β n : ℝ) (G : Multigraph (Fin d) E)
    (φ a : Fin d → ℝ) :
    clockComplexEdgeProduct β n G (complexAngleField φ a) =
      (clockBoxDensity β n G φ : ℂ) *
        edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ) := by
  have hgrad (e : E) :
      complexAngleField φ a (G.src e) - complexAngleField φ a (G.tgt e) =
        ((G.grad φ e : ℝ) : ℂ) + ((G.grad a e : ℝ) : ℂ) * Complex.I := by
    change ((φ (G.src e) : ℂ) + (a (G.src e) : ℂ) * Complex.I) -
        ((φ (G.tgt e) : ℂ) + (a (G.tgt e) : ℂ) * Complex.I) =
      ((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ) +
        ((a (G.src e) - a (G.tgt e) : ℝ) : ℂ) * Complex.I
    push_cast
    ring_nf
  have hreal :
      (∏ e, clockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ)) =
        (clockBoxDensity β n G φ : ℂ) := by
    simpa [clockComplexEdgeProduct, Multigraph.grad] using
      complexEdgeProduct_ofReal β n G φ
  unfold clockComplexEdgeProduct edgeRatio
  calc
    ∏ e, clockEdgeWeight β n (complexAngleField φ a (G.src e) -
        complexAngleField φ a (G.tgt e)) =
      ∏ e, clockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ) *
        (clockEdgeWeight β n (((G.grad φ e : ℝ) : ℂ) +
            ((G.grad a e : ℝ) : ℂ) * Complex.I) /
          clockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ)) := by
        apply Finset.prod_congr rfl
        intro e he
        rw [hgrad e]
        field_simp [clockEdgeWeight_ne_zero]
    _ = (∏ e, clockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ)) *
          ∏ e, (clockEdgeWeight β n (((G.grad φ e : ℝ) : ℂ) +
              ((G.grad a e : ℝ) : ℂ) * Complex.I) /
            clockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ)) := Finset.prod_mul_distrib
    _ = _ := by rw [hreal]

private theorem contourIntegrand_shiftPointwise (β n : ℝ) (G : Multigraph (Fin d) E)
    (τ φ a : Fin d → ℝ) :
    clockContourIntegrand β n G τ (complexAngleField φ a) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ((clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
          edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ)) := by
  unfold clockContourIntegrand
  rw [complexCharacter_shift, complexEdgeProduct_shift]
  ring

/-- Compact character translation needs sitewise period compatibility, but not neutrality. The
neutrality binder in the periodic clock model's interface is only needed by its source-facing specialization; charged
integer modes use this extension when a charge-layer ensemble is reduced. -/
theorem integral_clockBoxLaw_characterTranslation_compatible {n β : ℝ} (hn : 0 < n)
    (hβ : 0 ≤ β) {G : Multigraph (Fin d) E} (τ a : Fin d → ℝ)
    (hτ : ClockCompatibleCharge n τ) :
    ∫ φ, gffCharacter τ φ ∂clockBoxLaw β n G =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, gffCharacter τ φ * edgeRatio (clockEdgeWeight β n)
          (G.grad a) (G.grad φ) ∂clockBoxLaw β n G := by
  let F := clockContourIntegrand β n G τ
  have hP : 0 < clockAnglePeriod n := by
    unfold clockAnglePeriod
    positivity
  have hF : Differentiable ℂ F := by
    dsimp [F]
    exact differentiable_clockContourIntegrand β n G τ
  have hperiodic : ∀ j z, F (Function.update z j (z j + (clockAnglePeriod n : ℂ))) = F z :=
    contourIntegrand_periodic_compatible β n hn G τ hτ
  have hint : ∀ c : Fin d → ℝ,
      Integrable (fun φ => F (complexAngleField φ c))
        (compactAngleBaseMeasure (clockAnglePeriod n)) := by
    intro c
    exact contourIntegrand_integrable β n hβ hn G τ c
  have hshift : compactAngleIntegral (clockAnglePeriod n) F 0 =
      compactAngleIntegral (clockAnglePeriod n) F a :=
    compactAngleIntegral_complexShift hP F hF hperiodic a hint
  have hcontour :
      ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n =
        ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n := by
    simpa [compactAngleIntegral, clockAngleBaseMeasure] using hshift
  have hleft :
      ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n =
        ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ
          ∂clockAngleBaseMeasure n := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun φ => by
      have hz : complexAngleField φ 0 = fun j => (φ j : ℂ) := by
        funext j
        simp [complexAngleField]
      change clockContourIntegrand β n G τ (complexAngleField φ 0) = _
      rw [hz, clockContourIntegrand, complexCharacter_ofReal,
        complexEdgeProduct_ofReal]
      ring
  have hright :
      ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n =
        Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
          ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
            edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ)
            ∂clockAngleBaseMeasure n := by
    calc
      _ = ∫ φ, Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
            ((clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
              edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ))
            ∂clockAngleBaseMeasure n := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun φ => by
            change clockContourIntegrand β n G τ (complexAngleField φ a) = _
            exact contourIntegrand_shiftPointwise β n G τ φ a
      _ = _ := by rw [integral_const_mul]
  have hbase :
      ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ
          ∂clockAngleBaseMeasure n =
        Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
          ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
            edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ)
            ∂clockAngleBaseMeasure n := by
    calc
      _ = ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n := hleft.symm
      _ = ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n := hcontour
      _ = _ := hright
  have hLawL := integral_clockBoxLaw_as_base β n hβ G (gffCharacter τ)
  have hLawR := integral_clockBoxLaw_as_base β n hβ G
    (fun φ => gffCharacter τ φ * edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ))
  have hLawR_assoc :
      (((clockBoxMass β n G)⁻¹).toReal : ℂ) *
          ∫ φ, (clockBoxDensity β n G φ : ℂ) *
            (gffCharacter τ φ * edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ))
            ∂clockAngleBaseMeasure n =
        (((clockBoxMass β n G)⁻¹).toReal : ℂ) *
          ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
            edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ)
            ∂clockAngleBaseMeasure n := by
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun φ => by ring
  calc
    ∫ φ, gffCharacter τ φ ∂clockBoxLaw β n G =
        (((clockBoxMass β n G)⁻¹).toReal : ℂ) *
          ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ
            ∂clockAngleBaseMeasure n := hLawL
    _ = Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
          ((((clockBoxMass β n G)⁻¹).toReal : ℂ) *
            ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
              edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ)
              ∂clockAngleBaseMeasure n) := by rw [hbase]; ring
    _ = _ := by rw [← hLawR_assoc, hLawR]

def intChargeReal {V : Type*} (τ : V → ℤ) : V → ℝ := fun j => (τ j : ℝ)

theorem natClock_intCharge_compatible (N : ℕ) (τ : Fin d → ℤ) :
    ClockCompatibleCharge (N : ℝ) (intChargeReal τ) := by
  intro j
  refine ⟨(N : ℤ) * τ j, ?_⟩
  dsimp [intChargeReal]
  push_cast
  ring


end FroehlichSpencer.BKT.Clock.Periodic

end
