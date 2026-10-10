/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.EntireWeight
public import FroehlichSpencer.BKT.Clock.Compact.Law
import Mathlib.Tactic

/-!
# The compact Villain law and its character translation

The continuous Villain law on the compact box `(−πn, πn]^V` after `φ = nθ`, the Villain analogue
of `Clock.Compact.clockLaw`. The marked expansion for Theorem 7.1(2) uses one property of the law:
the compatible characters translate exactly along every real shift. That is the content here.

* `villainBoxDensity`, `villainBoxLaw`: the normalized product of `v_β(∇φ/n)` on `Fin d`;
* `villainCompactLaw β n G`: the law on a finite vertex set, transported along `siteEquiv`;
* **`integral_villainCompactLaw_characterTranslation`**:
  `∫ χ_τ dμ = e^{−⟨a, τ⟩} ∫ χ_τ R_{∇a}(∇φ) dμ` for every compatible `τ` and every real `a`, with the
  Villain edge ratio `R`. The proof is the compact contour shift of `Clock/Periodic/Translation.lean`;
  the Villain weight is entire and `2πn`-periodic (`VillainEntire.lean`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open MeasureTheory Complex
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic (edgeRatio)
open FroehlichSpencer.BKT.Reduction (gffCharacter norm_gffCharacter)

/-! ### Bounds on the Villain weight -/

theorem villainWeight_ge {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    Real.exp (-(β / 2) * Real.pi ^ 2) ≤ villainWeight β x := by
  have hy := toIcoMod_mem_Ico Real.two_pi_pos (-Real.pi) x
  have hyx : toIcoMod Real.two_pi_pos (-Real.pi) x =
      x + 2 * Real.pi * ((-(toIcoDiv Real.two_pi_pos (-Real.pi) x) : ℤ) : ℝ) := by
    rw [← self_sub_toIcoDiv_zsmul Real.two_pi_pos, zsmul_eq_mul]
    push_cast
    ring
  have hsum := VillainWeight.villainWeight_summable hβ x
  have hterm : Real.exp (-(β / 2) * (x + 2 * Real.pi *
      ((-(toIcoDiv Real.two_pi_pos (-Real.pi) x) : ℤ) : ℝ)) ^ 2) ≤ villainWeight β x := by
    unfold villainWeight
    exact hsum.le_tsum _ fun m _ => (Real.exp_pos _).le
  refine le_trans ?_ hterm
  apply Real.exp_le_exp.mpr
  rw [← hyx]
  have hy2 : toIcoMod Real.two_pi_pos (-Real.pi) x ^ 2 ≤ Real.pi ^ 2 := by
    have h1 : -Real.pi ≤ toIcoMod Real.two_pi_pos (-Real.pi) x := hy.1
    have h2 : toIcoMod Real.two_pi_pos (-Real.pi) x < -Real.pi + 2 * Real.pi := hy.2
    nlinarith [Real.pi_pos]
  nlinarith

/-! ### The box law -/

section Box

variable {d : ℕ} {E : Type*} [Fintype E]

/-- The unnormalized Villain box density `∏_e v_β(∇φ_e / n)`. -/
def villainBoxDensity (β n : ℝ) (G : Multigraph (Fin d) E) (φ : Fin d → ℝ) : ℝ :=
  ∏ e, villainWeight β (G.grad φ e / n)

/-- The finite unnormalized Villain measure on the compact box. -/
def villainBoxMeasure (β n : ℝ) (G : Multigraph (Fin d) E) : Measure (Fin d → ℝ) :=
  (clockAngleBaseMeasure n).withDensity fun φ => ENNReal.ofReal (villainBoxDensity β n G φ)

/-- The finite-box partition function of the compact Villain law. -/
def villainBoxMass (β n : ℝ) (G : Multigraph (Fin d) E) : ENNReal :=
  villainBoxMeasure β n G Set.univ

/-- The normalized compact Villain law on `Fin d`. -/
def villainBoxLaw (β n : ℝ) (G : Multigraph (Fin d) E) : Measure (Fin d → ℝ) :=
  (villainBoxMass β n G)⁻¹ • villainBoxMeasure β n G

theorem continuous_villainBoxDensity {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (G : Multigraph (Fin d) E) : Continuous (villainBoxDensity β n G) := by
  unfold villainBoxDensity
  refine continuous_finsetProd _ fun e _ => ?_
  have hre : (fun x : ℝ => villainWeight β (x / n)) =
      fun x : ℝ => (villainClockEdgeWeight β n (x : ℂ)).re := by
    funext x
    rw [villainClockEdgeWeight_ofReal, Complex.ofReal_re]
  have hcw : Continuous fun x : ℝ => villainWeight β (x / n) := by
    rw [hre]
    exact Complex.continuous_re.comp
      ((continuous_villainClockEdgeWeight β hβ hn).comp Complex.continuous_ofReal)
  exact hcw.comp (by unfold Multigraph.grad; fun_prop)

theorem villainBoxDensity_bounds {β : ℝ} (hβ : 0 < β) (n : ℝ) (G : Multigraph (Fin d) E)
    (φ : Fin d → ℝ) :
    Real.exp (-(β / 2) * Real.pi ^ 2) ^ Fintype.card E ≤ villainBoxDensity β n G φ ∧
      villainBoxDensity β n G φ ≤ villainWeight β 0 ^ Fintype.card E := by
  unfold villainBoxDensity
  constructor
  · calc
      Real.exp (-(β / 2) * Real.pi ^ 2) ^ Fintype.card E =
          ∏ _e : E, Real.exp (-(β / 2) * Real.pi ^ 2) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
          fun e _ => villainWeight_ge hβ _
  · calc
      ∏ e, villainWeight β (G.grad φ e / n) ≤ ∏ _e : E, villainWeight β 0 :=
        Finset.prod_le_prod₀ (fun _ _ => (VillainWeight.villainWeight_pos hβ _).le)
          fun e _ => villainWeight_le_zero hβ _
      _ = _ := by simp

theorem villainBoxMass_eq_lintegral (β n : ℝ) (G : Multigraph (Fin d) E) :
    villainBoxMass β n G = ∫⁻ φ, ENNReal.ofReal (villainBoxDensity β n G φ)
      ∂clockAngleBaseMeasure n := by
  rw [villainBoxMass, villainBoxMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem villainBoxMass_pos {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (G : Multigraph (Fin d) E) : 0 < villainBoxMass β n G := by
  rw [villainBoxMass_eq_lintegral]
  have hlower : ∀ φ, ENNReal.ofReal (Real.exp (-(β / 2) * Real.pi ^ 2) ^ Fintype.card E) ≤
      ENNReal.ofReal (villainBoxDensity β n G φ) := fun φ =>
    ENNReal.ofReal_le_ofReal (villainBoxDensity_bounds hβ n G φ).1
  have h := lintegral_mono (μ := clockAngleBaseMeasure n) hlower
  rw [lintegral_const] at h
  have hconst : 0 < ENNReal.ofReal (Real.exp (-(β / 2) * Real.pi ^ 2) ^ Fintype.card E) :=
    ENNReal.ofReal_pos.mpr (pow_pos (Real.exp_pos _) _)
  have hbase : 0 < clockAngleBaseMeasure (d := d) n Set.univ :=
    pos_iff_ne_zero.mpr (measure_clockAngleBase_univ_ne_zero hn)
  exact lt_of_lt_of_le (ENNReal.mul_pos hconst.ne' hbase.ne') h

theorem villainBoxMass_ne_top {β : ℝ} (hβ : 0 < β) (n : ℝ) (G : Multigraph (Fin d) E) :
    villainBoxMass β n G ≠ ⊤ := by
  rw [villainBoxMass_eq_lintegral]
  have hupper : ∀ φ, ENNReal.ofReal (villainBoxDensity β n G φ) ≤
      ENNReal.ofReal (villainWeight β 0 ^ Fintype.card E) := fun φ =>
    ENNReal.ofReal_le_ofReal (villainBoxDensity_bounds hβ n G φ).2
  have h := lintegral_mono (μ := clockAngleBaseMeasure n) hupper
  rw [lintegral_const] at h
  exact ne_of_lt (lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr measure_clockAngleBase_univ_ne_top)))

theorem isProbabilityMeasure_villainBoxLaw {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (G : Multigraph (Fin d) E) : IsProbabilityMeasure (villainBoxLaw β n G) := by
  refine ⟨?_⟩
  change (villainBoxMass β n G)⁻¹ * villainBoxMass β n G = 1
  exact ENNReal.inv_mul_cancel (villainBoxMass_pos hβ hn G).ne' (villainBoxMass_ne_top hβ n G)

theorem integral_villainBoxLaw_as_base {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (G : Multigraph (Fin d) E) (f : (Fin d → ℝ) → ℂ) :
    ∫ φ, f φ ∂villainBoxLaw β n G =
      (((villainBoxMass β n G)⁻¹).toReal : ℂ) *
        ∫ φ, (villainBoxDensity β n G φ : ℂ) * f φ ∂clockAngleBaseMeasure n := by
  let ρ := villainBoxDensity β n G
  have hρmeas : Measurable ρ := (continuous_villainBoxDensity hβ hn G).measurable
  have hρnonneg : ∀ φ, 0 ≤ ρ φ := fun φ =>
    (pow_pos (Real.exp_pos _) _).le.trans (villainBoxDensity_bounds hβ n G φ).1
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
  change ∫ φ, f φ ∂((villainBoxMass β n G)⁻¹ •
    (clockAngleBaseMeasure n).withDensity fun φ => ENNReal.ofReal (ρ φ)) = _
  rw [integral_smul_measure, hbase, Complex.real_smul]

end Box

/-! ### The contour translation on the box -/

section Contour

variable {d : ℕ} {E : Type} [Fintype E]

theorem villainBoxDensity_complexProduct (β n : ℝ) (G : Multigraph (Fin d) E)
    (φ : Fin d → ℝ) :
    (villainBoxDensity β n G φ : ℂ) = ∏ e, villainClockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ) := by
  unfold villainBoxDensity
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun e _ => (villainClockEdgeWeight_ofReal β n _).symm

/-- The holomorphic contour integrand of the Villain box law. -/
def villainContourIntegrand (β n : ℝ) (G : Multigraph (Fin d) E) (τ : Fin d → ℝ)
    (z : Fin d → ℂ) : ℂ :=
  clockComplexCharacter τ z * ∏ e, villainClockEdgeWeight β n (z (G.src e) - z (G.tgt e))

theorem villainContourIntegrand_differentiable {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (G : Multigraph (Fin d) E) (τ : Fin d → ℝ) :
    Differentiable ℂ (villainContourIntegrand β n G τ) := by
  have hw := differentiable_villainClockEdgeWeight β hβ hn
  have h1 : Differentiable ℂ (fun z : Fin d → ℂ => clockComplexCharacter τ z) := by
    unfold clockComplexCharacter
    fun_prop
  have h2 : Differentiable ℂ (fun z : Fin d → ℂ =>
      ∏ e, villainClockEdgeWeight β n (z (G.src e) - z (G.tgt e))) := by
    fun_prop
  exact h1.mul h2

theorem villainCharacter_periodic {n : ℝ} (τ : Fin d → ℝ) (hτ : ClockCompatibleCharge n τ)
    (j : Fin d) (z : Fin d → ℂ) :
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

theorem villainEdgeProduct_periodic (β : ℝ) {n : ℝ} (hn : 0 < n) (G : Multigraph (Fin d) E)
    (j : Fin d) (z : Fin d → ℂ) :
    (∏ e, villainClockEdgeWeight β n
        (Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.src e) -
          Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.tgt e))) =
      ∏ e, villainClockEdgeWeight β n (z (G.src e) - z (G.tgt e)) := by
  apply Finset.prod_congr rfl
  intro e _
  by_cases hs : G.src e = j
  · have ht : G.tgt e ≠ j := fun h => G.src_ne_tgt e (hs.trans h.symm)
    have harg :
        Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.src e) -
          Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.tgt e) =
        (z (G.src e) - z (G.tgt e)) + (clockAnglePeriod n : ℂ) := by
      rw [hs, Function.update_self, Function.update_of_ne ht]
      ring
    rw [harg]
    exact villainClockEdgeWeight_periodic β hn.ne' _
  · by_cases ht : G.tgt e = j
    · have harg :
          Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.src e) -
            Function.update z j (z j + (clockAnglePeriod n : ℂ)) (G.tgt e) =
          (z (G.src e) - z (G.tgt e)) - (clockAnglePeriod n : ℂ) := by
        rw [Function.update_of_ne hs, ht, Function.update_self]
        ring
      rw [harg]
      have hper := villainClockEdgeWeight_periodic β hn.ne'
        (z (G.src e) - z (G.tgt e) - (clockAnglePeriod n : ℂ))
      rw [sub_add_cancel] at hper
      exact hper.symm
    · simp only [Function.update_of_ne hs, Function.update_of_ne ht]

theorem villainContourIntegrand_periodic (β : ℝ) {n : ℝ} (hn : 0 < n)
    (G : Multigraph (Fin d) E) (τ : Fin d → ℝ) (hτ : ClockCompatibleCharge n τ) :
    ∀ j z, villainContourIntegrand β n G τ
      (Function.update z j (z j + (clockAnglePeriod n : ℂ))) =
        villainContourIntegrand β n G τ z := by
  intro j z
  unfold villainContourIntegrand
  rw [villainCharacter_periodic τ hτ j z, villainEdgeProduct_periodic β hn G j z]

theorem villainCharacter_shift (τ φ a : Fin d → ℝ) :
    clockComplexCharacter τ (complexAngleField φ a) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) * gffCharacter τ φ := by
  unfold clockComplexCharacter gffCharacter complexAngleField
  have hsplit :
      (∑ j, ((φ j : ℂ) + (a j : ℂ) * Complex.I) * (τ j : ℂ)) =
        (∑ j, (φ j : ℂ) * (τ j : ℂ)) + ∑ j, (a j : ℂ) * Complex.I * (τ j : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hreal : (∑ j, (a j : ℂ) * Complex.I * (τ j : ℂ)) = (∑ j, a j * τ j : ℝ) * Complex.I := by
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have harg : Complex.I * (∑ j, ((φ j : ℂ) + (a j : ℂ) * Complex.I) * (τ j : ℂ)) =
      -((∑ j, a j * τ j : ℝ) : ℂ) + Complex.I * ∑ j, (φ j : ℂ) * (τ j : ℂ) := by
    rw [hsplit, hreal, mul_add]
    have hI : Complex.I * (((∑ j, a j * τ j : ℝ) : ℂ) * Complex.I) =
        -((∑ j, a j * τ j : ℝ) : ℂ) := by
      rw [show Complex.I * (((∑ j, a j * τ j : ℝ) : ℂ) * Complex.I) =
        (Complex.I * Complex.I) * ((∑ j, a j * τ j : ℝ) : ℂ) by ring, Complex.I_mul_I]
      ring
    rw [hI]
    ring
  rw [harg, Complex.exp_add]

theorem villainContourIntegrand_integrable {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (G : Multigraph (Fin d) E) (τ c : Fin d → ℝ) :
    Integrable (fun φ => villainContourIntegrand β n G τ (complexAngleField φ c))
      (compactAngleBaseMeasure (clockAnglePeriod n)) := by
  let A : ℝ := ∑ e : E, |G.grad c e|
  let K : ℝ := Real.exp (β * A ^ 2 / (2 * n ^ 2)) * villainWeight β 0
  let B : ℝ := Real.exp (|∑ j, c j * τ j|) * K ^ Fintype.card E
  have hfield : Continuous (fun φ => complexAngleField φ c) := by
    unfold complexAngleField
    fun_prop
  have hcont : Continuous (fun φ => villainContourIntegrand β n G τ (complexAngleField φ c)) :=
    (villainContourIntegrand_differentiable hβ hn G τ).continuous.comp hfield
  refine Integrable.of_bound hcont.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun φ => ?_)
  have hAedge : ∀ e, |G.grad c e| ≤ A := fun e =>
    Finset.single_le_sum (f := fun e' => |G.grad c e'|) (fun e' _ => abs_nonneg _)
      (Finset.mem_univ e)
  have hgrad (e : E) :
      complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e) =
        ((G.grad φ e : ℝ) : ℂ) + ((G.grad c e : ℝ) : ℂ) * Complex.I := by
    change ((φ (G.src e) : ℂ) + (c (G.src e) : ℂ) * Complex.I) -
        ((φ (G.tgt e) : ℂ) + (c (G.tgt e) : ℂ) * Complex.I) =
      ((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ) + ((c (G.src e) - c (G.tgt e) : ℝ) : ℂ) * Complex.I
    push_cast
    ring
  have hK : 0 ≤ K := by
    have := (VillainWeight.villainWeight_pos hβ 0).le
    positivity
  have hprod : ‖∏ e, villainClockEdgeWeight β n
      (complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e))‖ ≤
        K ^ Fintype.card E := by
    rw [norm_prod]
    calc
      ∏ e, ‖villainClockEdgeWeight β n
          (complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e))‖ ≤
          ∏ _e : E, K := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro e _
        rw [hgrad e]
        exact villainClockEdgeWeight_compact_rect_bound β hβ hn A _ _ (hAedge e)
      _ = _ := by simp
  have hchar : ‖clockComplexCharacter τ (complexAngleField φ c)‖ ≤
      Real.exp |∑ j, c j * τ j| := by
    rw [villainCharacter_shift, norm_mul, Complex.norm_exp, norm_gffCharacter, mul_one]
    have hre : (-((∑ j, c j * τ j : ℝ) : ℂ)).re = -(∑ j, c j * τ j) := by simp
    rw [hre]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  calc
    ‖villainContourIntegrand β n G τ (complexAngleField φ c)‖ =
        ‖clockComplexCharacter τ (complexAngleField φ c)‖ *
          ‖∏ e, villainClockEdgeWeight β n
            (complexAngleField φ c (G.src e) - complexAngleField φ c (G.tgt e))‖ := by
          rw [villainContourIntegrand, norm_mul]
    _ ≤ Real.exp |∑ j, c j * τ j| * K ^ Fintype.card E :=
        mul_le_mul hchar hprod (norm_nonneg _) (by positivity)

theorem villainContour_shift_pointwise {β : ℝ} (hβ : 0 < β) (n : ℝ) (G : Multigraph (Fin d) E)
    (τ φ a : Fin d → ℝ) :
    villainContourIntegrand β n G τ (complexAngleField φ a) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ((villainBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
          edgeRatio (villainClockEdgeWeight β n) (G.grad a) (G.grad φ)) := by
  unfold villainContourIntegrand
  rw [villainCharacter_shift]
  have hgrad (e : E) :
      complexAngleField φ a (G.src e) - complexAngleField φ a (G.tgt e) =
        ((G.grad φ e : ℝ) : ℂ) + ((G.grad a e : ℝ) : ℂ) * Complex.I := by
    change ((φ (G.src e) : ℂ) + (a (G.src e) : ℂ) * Complex.I) -
        ((φ (G.tgt e) : ℂ) + (a (G.tgt e) : ℂ) * Complex.I) =
      ((φ (G.src e) - φ (G.tgt e) : ℝ) : ℂ) + ((a (G.src e) - a (G.tgt e) : ℝ) : ℂ) * Complex.I
    push_cast
    ring
  have hprod :
      ∏ e, villainClockEdgeWeight β n
          (complexAngleField φ a (G.src e) - complexAngleField φ a (G.tgt e)) =
        (villainBoxDensity β n G φ : ℂ) *
          edgeRatio (villainClockEdgeWeight β n) (G.grad a) (G.grad φ) := by
    unfold edgeRatio
    rw [villainBoxDensity_complexProduct, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    have hden : villainClockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ) ≠ 0 :=
      villainClockEdgeWeight_ofReal_ne_zero β n _ hβ
    rw [hgrad e]
    field_simp [hden]
  rw [hprod]
  ring

/-- **The compact Villain contour translation on the box.** -/
theorem integral_villainBoxCharacterTranslation {n β : ℝ} (hn : 0 < n) (hβ : 0 < β)
    (G : Multigraph (Fin d) E) (τ a : Fin d → ℝ) (hτ : ClockCompatibleCharge n τ) :
    ∫ φ, (villainBoxDensity β n G φ : ℂ) * gffCharacter τ φ ∂clockAngleBaseMeasure n =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, (villainBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
          edgeRatio (villainClockEdgeWeight β n) (G.grad a) (G.grad φ)
          ∂clockAngleBaseMeasure n := by
  let F := villainContourIntegrand β n G τ
  have hP : 0 < clockAnglePeriod n := by
    unfold clockAnglePeriod
    positivity
  have hshift : compactAngleIntegral (clockAnglePeriod n) F 0 =
      compactAngleIntegral (clockAnglePeriod n) F a :=
    compactAngleIntegral_complexShift hP F (villainContourIntegrand_differentiable hβ hn G τ)
      (villainContourIntegrand_periodic β hn G τ hτ) a
      (fun c => villainContourIntegrand_integrable hβ hn G τ c)
  have hcontour :
      ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n =
        ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n := by
    simpa [compactAngleIntegral, clockAngleBaseMeasure] using hshift
  have hleft :
      ∫ φ, F (complexAngleField φ 0) ∂clockAngleBaseMeasure n =
        ∫ φ, (villainBoxDensity β n G φ : ℂ) * gffCharacter τ φ ∂clockAngleBaseMeasure n := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun φ => by
      have h := villainContour_shift_pointwise hβ n G τ φ 0
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Complex.ofReal_zero, neg_zero,
        Complex.exp_zero, one_mul] at h
      change villainContourIntegrand β n G τ (complexAngleField φ 0) = _
      rw [h]
      have hg : G.grad (0 : Fin d → ℝ) = 0 := by
        funext e
        simp [Multigraph.grad]
      rw [hg, Generic.edgeRatio_zero _ _ fun e => villainClockEdgeWeight_ofReal_ne_zero β n _ hβ,
        mul_one]
  have hright :
      ∫ φ, F (complexAngleField φ a) ∂clockAngleBaseMeasure n =
        Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
          ∫ φ, (villainBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
            edgeRatio (villainClockEdgeWeight β n) (G.grad a) (G.grad φ)
            ∂clockAngleBaseMeasure n := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun φ =>
      villainContour_shift_pointwise hβ n G τ φ a)
  rw [← hleft, hcontour, hright]

/-- The compatible character translation for the normalized Villain box law. -/
theorem integral_villainBoxLaw_characterTranslation {n β : ℝ} (hn : 0 < n) (hβ : 0 < β)
    (G : Multigraph (Fin d) E) (τ a : Fin d → ℝ) (hτ : ClockCompatibleCharge n τ) :
    ∫ φ, gffCharacter τ φ ∂villainBoxLaw β n G =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, gffCharacter τ φ * edgeRatio (villainClockEdgeWeight β n) (G.grad a) (G.grad φ)
          ∂villainBoxLaw β n G := by
  rw [integral_villainBoxLaw_as_base hβ hn, integral_villainBoxLaw_as_base hβ hn,
    integral_villainBoxCharacterTranslation hn hβ G τ a hτ]
  have h : ∀ φ, (villainBoxDensity β n G φ : ℂ) * gffCharacter τ φ *
      edgeRatio (villainClockEdgeWeight β n) (G.grad a) (G.grad φ) =
      (villainBoxDensity β n G φ : ℂ) * (gffCharacter τ φ *
        edgeRatio (villainClockEdgeWeight β n) (G.grad a) (G.grad φ)) := fun φ => by ring
  simp_rw [h]
  ring

end Contour

/-! ### The law on a finite vertex set -/

section Law

variable {V : Type} [Fintype V] {E : Type} [Fintype E]

/-- **The compact Villain law on a finite vertex set**: the normalized product of the Villain
weights `v_β(∇φ/n)` on the box `(−πn, πn]^V`. -/
def villainCompactLaw (β n : ℝ) (G : Multigraph V E) : Measure (V → ℝ) :=
  (villainBoxLaw β n (relabelGraph G (siteEquiv V))).map (pullField V)

theorem isProbabilityMeasure_villainCompactLaw {β n : ℝ} (G : Multigraph V E) (hβ : 0 < β)
    (hn : 0 < n) : IsProbabilityMeasure (villainCompactLaw β n G) := by
  have := isProbabilityMeasure_villainBoxLaw hβ hn (relabelGraph G (siteEquiv V))
  unfold villainCompactLaw
  infer_instance

theorem integral_villainCompactLaw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β n : ℝ) (G : Multigraph V E) (f : (V → ℝ) → F) :
    ∫ φ, f φ ∂villainCompactLaw β n G =
      ∫ φ, f (pullField V φ) ∂villainBoxLaw β n (relabelGraph G (siteEquiv V)) :=
  measurableEmbedding_pullField.integral_map _

/-- **The compact Villain character translation on a finite vertex set**: for a charge with
`n τ(j) ∈ ℤ` and every real shift `a`, `∫ χ_τ dμ = e^{−⟨a, τ⟩} ∫ χ_τ R_{∇a}(∇φ) dμ`. -/
theorem integral_villainCompactLaw_characterTranslation {n β : ℝ} (hn : 0 < n) (hβ : 0 < β)
    (G : Multigraph V E) (τ a : V → ℝ) (hτ : IsClockCompatible n τ) :
    ∫ φ, gffCharacter τ φ ∂villainCompactLaw β n G =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, gffCharacter τ φ * edgeRatio (villainClockEdgeWeight β n) (G.grad a) (G.grad φ)
          ∂villainCompactLaw β n G := by
  set e := siteEquiv V
  set G' := relabelGraph G e
  set τ' : Fin (Fintype.card V) → ℝ := fun j => τ (e.symm j)
  set a' : Fin (Fintype.card V) → ℝ := fun j => a (e.symm j)
  have hτ' : ClockCompatibleCharge n τ' := fun j => hτ (e.symm j)
  have hga : G'.grad a' = G.grad a := by
    funext x
    simp only [Multigraph.grad, G', relabelGraph, a', Equiv.symm_apply_apply]
  have hsum : ∑ j, a' j * τ' j = ∑ j, a j * τ j :=
    e.symm.sum_comp fun j => a j * τ j
  rw [integral_villainCompactLaw, integral_villainCompactLaw]
  simp_rw [gffCharacter_pullField, grad_pullField]
  have key := integral_villainBoxLaw_characterTranslation hn hβ G' τ' a' hτ'
  rw [hga, hsum] at key
  exact key

end Law

end FroehlichSpencer.BKT.Clock.VillainClock

end
