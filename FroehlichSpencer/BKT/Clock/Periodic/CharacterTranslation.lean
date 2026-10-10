/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.Translation
public import FroehlichSpencer.BKT.Generic.EdgeRatio
public import FroehlichSpencer.BKT.Reduction.SpinWaveTranslation

/-!
# Character translation for the compact clock law

The compact torus permits a character translation when every site frequency is compatible with
the angle period: `n * τ(j)` is an integer.

This is stronger than neutrality.

The contour shift is
proved on the compact fundamental box, where periodic side integrals cancel.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Generic (edgeRatio)
open FroehlichSpencer.BKT.Reduction (gffCharacter norm_gffCharacter)

variable {d : ℕ} {E : Type*} [Fintype E]

/-- The sitewise period compatibility required for a character on the compact clock torus. -/
def ClockCompatibleCharge (n : ℝ) (τ : Fin d → ℝ) : Prop :=
  ∀ j, ∃ k : ℤ, n * τ j = k

/-- The entire extension of a real linear character to complex fields. -/
def clockComplexCharacter (τ : Fin d → ℝ) (z : Fin d → ℂ) : ℂ :=
  Complex.exp (Complex.I * ∑ j, z j * (τ j : ℂ))

/-- The complex edge product of the compact clock weight. -/
def clockComplexEdgeProduct (β n : ℝ) (G : Multigraph (Fin d) E)
    (z : Fin d → ℂ) : ℂ :=
  ∏ e, clockEdgeWeight β n (z (G.src e) - z (G.tgt e))

/-- The holomorphic integrand whose compact contour shift gives the character identity. -/
def clockContourIntegrand (β n : ℝ) (G : Multigraph (Fin d) E) (τ : Fin d → ℝ)
    (z : Fin d → ℂ) : ℂ :=
  clockComplexCharacter τ z * clockComplexEdgeProduct β n G z

private theorem clockEdgeWeight_periodic_sub (β n : ℝ) (hn : n ≠ 0) (z : ℂ) :
    clockEdgeWeight β n (z - (clockAnglePeriod n : ℂ)) = clockEdgeWeight β n z := by
  have h := clockEdgeWeight_periodic β n hn (z - (clockAnglePeriod n : ℂ))
  have hz : z - (clockAnglePeriod n : ℂ) + (clockAnglePeriod n : ℂ) = z := by ring
  rw [hz] at h
  exact h.symm

private theorem clockComplexCharacter_ofReal (τ φ : Fin d → ℝ) :
    clockComplexCharacter τ (fun j => (φ j : ℂ)) = gffCharacter τ φ := by
  rfl

private theorem clockComplexCharacter_shift (τ φ a : Fin d → ℝ) :
    clockComplexCharacter τ (complexAngleField φ a) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) * gffCharacter τ φ := by
  unfold clockComplexCharacter gffCharacter complexAngleField
  have harg : Complex.I * ∑ j, ((φ j : ℂ) + (a j : ℂ) * Complex.I) * (τ j : ℂ) =
      -((∑ j, a j * τ j : ℝ) : ℂ) + Complex.I * ∑ j, (φ j : ℂ) * (τ j : ℂ) := by
    have hsplit :
        (∑ j, ((φ j : ℂ) + (a j : ℂ) * Complex.I) * (τ j : ℂ)) =
          (∑ j, (φ j : ℂ) * (τ j : ℂ)) + ∑ j, (a j : ℂ) * Complex.I * (τ j : ℂ) := by
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
    rw [hsplit, hreal]
    push_cast
    have hI : ∀ x : ℂ, Complex.I * (x * Complex.I) = -x := by
      intro x
      calc
        Complex.I * (x * Complex.I) = (Complex.I * Complex.I) * x := by ring
        _ = -x := by rw [Complex.I_mul_I]; ring
    rw [mul_add, hI]
    ring
  rw [harg, Complex.exp_add]

private theorem clockComplexCharacter_periodic {n : ℝ}
    (τ : Fin d → ℝ) (hτ : ClockCompatibleCharge n τ) (j : Fin d)
    (z : Fin d → ℂ) :
    clockComplexCharacter τ (Function.update z j (z j + (clockAnglePeriod n : ℂ))) =
      clockComplexCharacter τ z := by
  obtain ⟨k, hk⟩ := hτ j
  have hsum :
      (∑ i, Function.update z j (z j + (clockAnglePeriod n : ℂ)) i * (τ i : ℂ)) =
        (∑ i, z i * (τ i : ℂ)) + (clockAnglePeriod n : ℂ) * (τ j : ℂ) := by
    have hrest :
        (∑ i ∈ Finset.univ.erase j,
            Function.update z j (z j + (clockAnglePeriod n : ℂ)) i * (τ i : ℂ)) =
          ∑ i ∈ Finset.univ.erase j, z i * (τ i : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [Function.update_of_ne hij]
    rw [← Finset.sum_erase_add Finset.univ
      (fun i => Function.update z j (z j + (clockAnglePeriod n : ℂ)) i * (τ i : ℂ))
      (Finset.mem_univ j)]
    rw [← Finset.sum_erase_add Finset.univ (fun i => z i * (τ i : ℂ)) (Finset.mem_univ j)]
    simp only [Function.update_self]
    rw [hrest]
    ring
  have hkC : (n : ℂ) * (τ j : ℂ) = (k : ℂ) := by exact_mod_cast hk
  have hphase : Complex.exp (Complex.I * ((clockAnglePeriod n : ℂ) * (τ j : ℂ))) = 1 := by
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

private theorem clockComplexEdgeProduct_periodic (β n : ℝ) (hn : 0 < n)
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
          Function.update z j (z j + ↑(clockAnglePeriod n)) (G.tgt e) =
        (z (G.src e) - z (G.tgt e)) + (clockAnglePeriod n : ℂ) := by
      rw [hs]
      simp [Function.update_of_ne ht]
      ring
    rw [harg]
    exact clockEdgeWeight_periodic β n hn.ne' _
  · by_cases ht : G.tgt e = j
    · have hs' : G.src e ≠ j := hs
      have harg : Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.src e) -
            Function.update z j (z j + ↑(clockAnglePeriod n)) (G.tgt e) =
          (z (G.src e) - z (G.tgt e)) - (clockAnglePeriod n : ℂ) := by
        rw [ht]
        simp [Function.update_of_ne hs']
        ring
      rw [harg]
      exact clockEdgeWeight_periodic_sub β n hn.ne' _
    · simp [Function.update_of_ne hs, Function.update_of_ne ht]

/-- The compact contour integrand is entire. -/
theorem differentiable_clockContourIntegrand (β n : ℝ) (G : Multigraph (Fin d) E)
    (τ : Fin d → ℝ) : Differentiable ℂ (clockContourIntegrand β n G τ) := by
  unfold clockContourIntegrand clockComplexCharacter clockComplexEdgeProduct
    clockEdgeWeight
  fun_prop

private theorem clockContourIntegrand_periodic (β n : ℝ) (hn : 0 < n)
    (G : Multigraph (Fin d) E) (τ : Fin d → ℝ) (hτ : ClockCompatibleCharge n τ) :
    ∀ j z, clockContourIntegrand β n G τ
      (Function.update z j (z j + (clockAnglePeriod n : ℂ))) =
        clockContourIntegrand β n G τ z := by
  intro j z
  unfold clockContourIntegrand
  rw [clockComplexCharacter_periodic τ hτ j z,
    clockComplexEdgeProduct_periodic β n hn G j z]

private theorem clockBoxDensity_nonneg {β n : ℝ} (hβ : 0 ≤ β)
    (G : Multigraph (Fin d) E) (φ : Fin d → ℝ) : 0 ≤ clockBoxDensity β n G φ := by
  exact (le_of_lt (pow_pos (Real.exp_pos _) _)).trans (clockBoxDensity_bounds G hβ φ).1

private theorem integral_clockBoxLaw_as_base {β n : ℝ} (hβ : 0 ≤ β)
    (G : Multigraph (Fin d) E) (f : (Fin d → ℝ) → ℂ) :
    ∫ φ, f φ ∂clockBoxLaw β n G =
      (((clockBoxMass β n G)⁻¹).toReal : ℂ) *
        ∫ φ, (clockBoxDensity β n G φ : ℂ) * f φ ∂clockAngleBaseMeasure n := by
  let ρ := clockBoxDensity β n G
  have hρmeas : Measurable ρ := by dsimp [ρ]; exact measurable_clockBoxDensity β n G
  have hρnonneg : ∀ φ, 0 ≤ ρ φ := fun φ => by dsimp [ρ]; exact clockBoxDensity_nonneg hβ G φ
  have hbase :
      ∫ φ, f φ ∂(clockAngleBaseMeasure n).withDensity (fun φ => ENNReal.ofReal (ρ φ)) =
        ∫ φ, (ρ φ : ℂ) * f φ ∂clockAngleBaseMeasure n := by
    calc
      _ = ∫ φ, (ENNReal.ofReal (ρ φ)).toReal • f φ ∂clockAngleBaseMeasure n :=
        integral_withDensity_eq_integral_toReal_smul
          (ENNReal.measurable_ofReal.comp hρmeas)
          (Filter.Eventually.of_forall fun φ => ENNReal.ofReal_lt_top) f
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with φ
        simp [ENNReal.toReal_ofReal (hρnonneg φ), Complex.real_smul]
  change ∫ φ, f φ ∂((clockBoxMass β n G)⁻¹ •
    (clockAngleBaseMeasure n).withDensity fun φ => ENNReal.ofReal (ρ φ)) = _
  rw [integral_smul_measure, hbase, Complex.real_smul]

private theorem clockContourIntegrand_integrable {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n)
    (G : Multigraph (Fin d) E) (τ c : Fin d → ℝ) :
    Integrable (fun φ => clockContourIntegrand β n G τ (complexAngleField φ c))
      (compactAngleBaseMeasure (d := d) (clockAnglePeriod n)) := by
  let A : ℝ := ∑ e : E, |G.grad c e|
  let B : ℝ := Real.exp (|∑ j, c j * τ j|) *
    Real.exp (β * Real.exp (A / n)) ^ Fintype.card E
  have hfield : Continuous (fun φ => complexAngleField φ c) := by
    unfold complexAngleField
    fun_prop
  have hcont : Continuous (fun φ => clockContourIntegrand β n G τ (complexAngleField φ c)) :=
    (differentiable_clockContourIntegrand β n G τ).continuous.comp hfield
  refine Integrable.of_bound hcont.aestronglyMeasurable B (Filter.Eventually.of_forall fun φ => ?_)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAedge : ∀ e, |G.grad c e| ≤ A := by
    intro e
    dsimp [A]
    calc
      |G.grad c e| ≤ ∑ e' : E, |G.grad c e'| :=
        Finset.single_le_sum (f := fun e' => |G.grad c e'|)
          (fun e' _ => abs_nonneg _) (Finset.mem_univ e)
      _ = A := rfl
  have hgrad (e : E) :
      complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e) =
        ((G.grad (φ : Fin d → ℝ) e : ℝ) : ℂ) +
          ((G.grad (c : Fin d → ℝ) e : ℝ) : ℂ) * Complex.I := by
    change ((φ (G.src e) : ℂ) + (c (G.src e) : ℂ) * Complex.I) -
        ((φ (G.tgt e) : ℂ) + (c (G.tgt e) : ℂ) * Complex.I) =
      (((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ)) +
        (((c (G.src e) - c (G.tgt e) : ℝ) : ℂ)) * Complex.I
    push_cast
    ring
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
            · intro e he; positivity
            · intro e he; exact hedge e
      _ = _ := by simp
  have hchar : ‖clockComplexCharacter τ (complexAngleField φ c)‖ ≤
      Real.exp |∑ j, c j * τ j| := by
    rw [clockComplexCharacter_shift τ φ c, norm_mul, Complex.norm_exp,
      norm_gffCharacter, mul_one]
    have hre : (-(∑ j, c j * τ j : ℝ) : ℂ).re = -(∑ j, c j * τ j) := by simp
    rw [hre]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  calc
    ‖clockContourIntegrand β n G τ (complexAngleField φ c)‖ =
        ‖clockComplexCharacter τ (complexAngleField φ c)‖ *
          ‖clockComplexEdgeProduct β n G (complexAngleField φ c)‖ := by
          rw [clockContourIntegrand, norm_mul]
    _ ≤ Real.exp |∑ j, c j * τ j| *
          Real.exp (β * Real.exp (A / n)) ^ Fintype.card E := mul_le_mul hchar hprod
            (norm_nonneg _) (by positivity)
    _ = B := rfl

private theorem clockComplexEdgeProduct_ofReal {β n : ℝ} (G : Multigraph (Fin d) E)
    (φ : Fin d → ℝ) :
    clockComplexEdgeProduct β n G (fun j => (φ j : ℂ)) =
      (clockBoxDensity β n G φ : ℂ) := by
  simp only [clockComplexEdgeProduct, clockBoxDensity, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro e he
  have hreal := clockEdgeWeight_ofReal β n (φ (G.src e) - φ (G.tgt e))
  have hweight : clockEdgeWeight β n ((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ) =
      ((clockEdgeWeight β n ((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ)).re : ℂ) := by
    calc
      clockEdgeWeight β n ((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ) =
          (Real.exp (β * Real.cos ((φ (G.src e) - φ (G.tgt e)) / n)) : ℂ) := hreal
      _ = ((Real.exp (β * Real.cos ((φ (G.src e) - φ (G.tgt e)) / n)) : ℂ).re : ℂ) := by
        simp only [Complex.ofReal_re]
      _ = ((clockEdgeWeight β n
          ((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ)).re : ℂ) := by rw [hreal]
  have harg : (φ (G.src e) : ℂ) - (φ (G.tgt e) : ℂ) =
      ((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ) := by push_cast; ring
  rw [Multigraph.grad, harg]
  exact hweight

private theorem clockComplexEdgeProduct_shift {β n : ℝ} (G : Multigraph (Fin d) E)
    (φ a : Fin d → ℝ) :
    clockComplexEdgeProduct β n G (complexAngleField φ a) =
      (clockBoxDensity β n G φ : ℂ) *
        edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ) := by
  have hgrad (e : E) :
      complexAngleField φ a (G.src e) - complexAngleField φ a (G.tgt e) =
        ((G.grad (φ : Fin d → ℝ) e : ℝ) : ℂ) +
          ((G.grad (a : Fin d → ℝ) e : ℝ) : ℂ) * Complex.I := by
    change ((φ (G.src e) : ℂ) + (a (G.src e) : ℂ) * Complex.I) -
        ((φ (G.tgt e) : ℂ) + (a (G.tgt e) : ℂ) * Complex.I) =
      (((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ)) +
        (((a (G.src e) - a (G.tgt e) : ℝ) : ℂ)) * Complex.I
    push_cast
    ring
  have hreal :
      (∏ e, clockEdgeWeight β n ((G.grad (φ : Fin d → ℝ) e : ℝ) : ℂ)) =
        (clockBoxDensity β n G φ : ℂ) := by
    simpa [clockComplexEdgeProduct, Multigraph.grad] using
      (clockComplexEdgeProduct_ofReal (β := β) (n := n) G φ)
  unfold clockComplexEdgeProduct edgeRatio
  calc
    ∏ e, clockEdgeWeight β n (complexAngleField φ a (G.src e) -
        complexAngleField φ a (G.tgt e)) =
      ∏ e, clockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ) *
        (clockEdgeWeight β n (((G.grad φ e : ℝ) : ℂ) +
            ((G.grad a e : ℝ) : ℂ) * Complex.I) /
          clockEdgeWeight β n ((G.grad (φ : Fin d → ℝ) e : ℝ) : ℂ)) := by
        apply Finset.prod_congr rfl
        intro e he
        rw [hgrad e]
        have hne := clockEdgeWeight_ne_zero β n ((G.grad (φ : Fin d → ℝ) e : ℝ) : ℂ)
        field_simp [hne]
    _ = (∏ e, clockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ)) *
          ∏ e, (clockEdgeWeight β n (((G.grad φ e : ℝ) : ℂ) +
              ((G.grad a e : ℝ) : ℂ) * Complex.I) /
            clockEdgeWeight β n ((G.grad (φ : Fin d → ℝ) e : ℝ) : ℂ)) :=
        Finset.prod_mul_distrib
    _ = (clockBoxDensity β n G φ : ℂ) *
          edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ) := by
        rw [hreal]
        rfl

private theorem clockContourIntegrand_shiftPointwise {β n : ℝ}
    (G : Multigraph (Fin d) E) (τ φ a : Fin d → ℝ) :
    clockContourIntegrand β n G τ (complexAngleField φ a) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ((clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
          edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ)) := by
  unfold clockContourIntegrand
  rw [clockComplexCharacter_shift τ φ a, clockComplexEdgeProduct_shift]
  ring

private theorem clockContourIntegrand_zeroPointwise {β n : ℝ}
    (G : Multigraph (Fin d) E) (τ φ : Fin d → ℝ) :
    clockContourIntegrand β n G τ (complexAngleField φ 0) =
      (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ := by
  have hz : complexAngleField φ 0 = fun j => (φ j : ℂ) := by
    funext j
    simp [complexAngleField]
  rw [hz]
  rw [clockContourIntegrand, clockComplexCharacter_ofReal, clockComplexEdgeProduct_ofReal]
  ring

/-- The finite-volume compact clock law admits the source character translation, provided each
site frequency is period-compatible. Neutrality is retained as the charge condition used by the
FS81 branch argument. -/
theorem integral_clockBoxLaw_characterTranslation {n β : ℝ} (hn : 0 < n) (hβ : 0 ≤ β)
    {G : Multigraph (Fin d) E} (τ a : Fin d → ℝ)
    (_hneutral : ∑ j, τ j = 0) (hτ : ClockCompatibleCharge n τ) :
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
    clockContourIntegrand_periodic β n hn G τ hτ
  have hint : ∀ c : Fin d → ℝ,
      Integrable (fun φ => F (complexAngleField φ c))
        (compactAngleBaseMeasure (clockAnglePeriod n)) := by
    intro c
    exact clockContourIntegrand_integrable hβ hn G τ c
  have hshift : compactAngleIntegral (clockAnglePeriod n) F 0 =
      compactAngleIntegral (clockAnglePeriod n) F a :=
    compactAngleIntegral_complexShift hP F hF hperiodic a hint
  have hcontour :
      ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n =
        ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n := by
    simpa [compactAngleIntegral, clockAngleBaseMeasure] using hshift
  have hleft :
      ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n =
        ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ ∂clockAngleBaseMeasure n := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun φ => clockContourIntegrand_zeroPointwise G τ φ
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
          exact Filter.Eventually.of_forall fun φ => clockContourIntegrand_shiftPointwise G τ φ a
      _ = _ := by rw [integral_const_mul]
  have hbase :
      ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ ∂clockAngleBaseMeasure n =
        Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
          ∫ φ, (clockBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
            edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ)
            ∂clockAngleBaseMeasure n := by
    calc
      _ = ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n := hleft.symm
      _ = ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n := hcontour
      _ = _ := hright
  have hLawL := integral_clockBoxLaw_as_base (β := β) (n := n) hβ G (gffCharacter τ)
  have hLawR := integral_clockBoxLaw_as_base (β := β) (n := n) hβ G
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
    _ = Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
          ∫ φ, gffCharacter τ φ * edgeRatio (clockEdgeWeight β n)
            (G.grad a) (G.grad φ) ∂clockBoxLaw β n G := by rw [← hLawR_assoc, hLawR]

end FroehlichSpencer.BKT.Clock.Periodic

end
