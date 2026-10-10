/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
public import FroehlichSpencer.BKT.Ginibre.Models
public import FroehlichSpencer.BKT.Rotator.Ginibre.Measure
public import FroehlichSpencer.BKT.Fourier.PeriodizedGaussian
public import FroehlichSpencer.BKT.Clock.Window.MasslessWindow
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# The complex two-point observable for the clock, rotator and Villain models

FS81 writes the two-point function as a complex character expectation. Reflection makes its sine
part vanish for each finite free Gibbs measure and hence in the free limit. The clock reflection is
the permutation `j ↦ -j` of the `N` clock atoms, represented by angles in `[0,2π)`; the nonzero
labels reflect to `2π - θ`, so the `2π` periodicity of integer characters is used explicitly.
-/

@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Window

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Source

variable {V : Type*} [Fintype V]

end FroehlichSpencer.BKT.Clock.Source

namespace FroehlichSpencer.BKT.Ginibre.FreeModel

/-- The finite-volume sine part of the character two-point function of a free model. -/
def twoPointSine (M : FreeModel) (ξ : ℤ) (Λ : Finset (ℤ × ℤ))
    (u v : ℤ × ℤ) : ℝ :=
  ∫ θ, Real.sin (ξ * (latticeAngle θ u - latticeAngle θ v)) ∂M.gibbs Λ

/-- The complex finite-volume character expectation corresponding to `FreeModel.twoPoint`. -/
def complexTwoPoint (M : FreeModel) (ξ : ℤ) (Λ : Finset (ℤ × ℤ))
    (u v : ℤ × ℤ) : ℂ :=
  ∫ θ, Complex.exp ((phase (twoPointFrequency Λ ξ u v) θ : ℂ) * Complex.I) ∂M.gibbs Λ

/-- The complex free-limit correlation, defined as the complexification of the proved real limit. -/
def complexTwoPointLimit (M : FreeModel) (ξ : ℤ) (u v : ℤ × ℤ) : ℂ :=
  (M.twoPointLimit ξ u v : ℂ)

end FroehlichSpencer.BKT.Ginibre.FreeModel

namespace FroehlichSpencer.BKT.Clock.Source

/-- The character phase of the finite two-point observable. -/
theorem phase_twoPointFrequency_source (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ)
    (θ : Λ → ℝ) :
    phase (twoPointFrequency Λ ξ u v) θ = ξ * (latticeAngle θ u - latticeAngle θ v) :=
  phase_twoPointFrequency ξ u v θ

end FroehlichSpencer.BKT.Clock.Source

namespace FroehlichSpencer.BKT.Ginibre.FreeModel

variable {V : Type*} [Fintype V]

/-- A reflected configuration changes the character phase to its negative, up to an integer turn,
and leaves the Gibbs weight unchanged; the sine expectation is then zero. -/
theorem twoPointSine_zero_of_reflection
    (M : FreeModel) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ)
    (R : (Λ → ℝ) → (Λ → ℝ))
    (hpres : MeasurePreserving R (siteProduct M.ν Λ) (siteProduct M.ν Λ))
    (hphase : ∀ θ, ∃ k : ℤ,
      phase (twoPointFrequency Λ ξ u v) (R θ) =
        -phase (twoPointFrequency Λ ξ u v) θ + (k : ℝ) * (2 * Real.pi))
    (hweight : ∀ θ,
      pairWeight (bondFrequency Λ) (M.bondWeight Λ) (R θ) =
        pairWeight (bondFrequency Λ) (M.bondWeight Λ) θ) :
    M.twoPointSine ξ Λ u v = 0 := by
  let n := twoPointFrequency Λ ξ u v
  let w := M.bondWeight Λ
  let f : (Λ → ℝ) → ℝ := fun θ => Real.sin (phase n θ) *
    pairWeight (bondFrequency Λ) w θ
  have hw : ∀ b : Λ × Λ, IsBondWeight (M.bondWeight Λ b) := M.isBondWeight_bondWeight Λ
  have hfcont : Continuous f :=
    (Real.continuous_sin.comp (continuous_phase n)).mul
      (continuous_pairWeight hw)
  have hf : AEStronglyMeasurable f (siteProduct M.ν Λ) := hfcont.aestronglyMeasurable
  have hchange : ∫ θ, f (R θ) ∂siteProduct M.ν Λ =
      ∫ θ, f θ ∂siteProduct M.ν Λ := by
    calc
      ∫ θ, f (R θ) ∂siteProduct M.ν Λ =
          ∫ θ, f θ ∂(siteProduct M.ν Λ).map R :=
            (integral_map hpres.measurable.aemeasurable
              (by simpa [hpres.map_eq] using hf)).symm
      _ = ∫ θ, f θ ∂siteProduct M.ν Λ := by rw [hpres.map_eq]
  have hodd : (fun θ => f (R θ)) = fun θ => -f θ := by
    funext θ
    dsimp [f]
    obtain ⟨k, hk⟩ := hphase θ
    rw [hk, Real.sin_add_int_mul_two_pi, Real.sin_neg, hweight]
    ring
  rw [hodd, integral_neg] at hchange
  have hzero : ∫ θ, f θ ∂siteProduct M.ν Λ = 0 := by linarith
  rw [twoPointSine]
  change ∫ θ, Real.sin (ξ * (latticeAngle θ u - latticeAngle θ v)) ∂
    pairGibbs M.ν (bondFrequency Λ) (M.bondWeight Λ) = 0
  rw [integral_pairGibbs M.mass_ne_zero hw]
  have hnum : ∫ θ, Real.sin (ξ * (latticeAngle θ u - latticeAngle θ v)) *
      pairWeight (bondFrequency Λ) (M.bondWeight Λ) θ ∂siteProduct M.ν Λ = 0 := by
    simpa [f, n, w, phase_twoPointFrequency] using hzero
  rw [hnum]
  simp

/-- Reflection sends an even single-edge weight product to itself. -/
theorem pairWeight_neg_of_even (M : FreeModel) (Λ : Finset (ℤ × ℤ))
    (hEven : ∀ x, M.w (-x) = M.w x) (θ : Λ → ℝ) :
    pairWeight (bondFrequency Λ) (M.bondWeight Λ) (-θ) =
      pairWeight (bondFrequency Λ) (M.bondWeight Λ) θ := by
  unfold pairWeight
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [phase_neg_angle]
  unfold FreeModel.bondWeight
  split_ifs
  · exact hEven _
  · rfl

/-- The two-point complex character is the real cosine expectation whenever the sine part vanishes. -/
theorem complexTwoPoint_eq_ofReal_twoPoint_of_sine_zero
    (M : FreeModel) (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ)
    (hsin : M.twoPointSine ξ Λ u v = 0) :
    M.complexTwoPoint ξ Λ u v = (M.twoPoint ξ Λ u v : ℂ) := by
  have hprob : IsProbabilityMeasure (M.gibbs Λ) := by
    unfold gibbs
    exact isProbabilityMeasure_pairGibbs M.mass_ne_zero (M.isBondWeight_bondWeight Λ)
  have hfinite : IsFiniteMeasure (M.gibbs Λ) := by
    have hz : IsZeroOrProbabilityMeasure (M.gibbs Λ) := ⟨Or.inr hprob.measure_univ⟩
    exact @IsZeroOrProbabilityMeasure.toIsFiniteMeasure (Λ → ℝ) _ (M.gibbs Λ) hz
  have hcont : Continuous (fun θ : Λ → ℝ => phase (twoPointFrequency Λ ξ u v) θ) :=
    continuous_phase _
  have hc : Integrable
      (fun θ : Λ → ℝ => Real.cos (phase (twoPointFrequency Λ ξ u v) θ)) (M.gibbs Λ) :=
    @Integrable.of_bound (Λ → ℝ) ℝ _ inferInstance (M.gibbs Λ) hfinite
      (fun θ => Real.cos (phase (twoPointFrequency Λ ξ u v) θ))
      (Real.continuous_cos.comp hcont).aestronglyMeasurable 1
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable
      (fun θ : Λ → ℝ => Real.sin (phase (twoPointFrequency Λ ξ u v) θ)) (M.gibbs Λ) :=
    @Integrable.of_bound (Λ → ℝ) ℝ _ inferInstance (M.gibbs Λ) hfinite
      (fun θ => Real.sin (phase (twoPointFrequency Λ ξ u v) θ))
      (Real.continuous_sin.comp hcont).aestronglyMeasurable 1
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hchar (θ : Λ → ℝ) :
      Complex.exp ((phase (twoPointFrequency Λ ξ u v) θ : ℂ) * Complex.I) =
        (Real.cos (phase (twoPointFrequency Λ ξ u v) θ) : ℂ) +
          (Real.sin (phase (twoPointFrequency Λ ξ u v) θ) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I]
  have hsin' : ∫ θ : Λ → ℝ,
      Real.sin (phase (twoPointFrequency Λ ξ u v) θ) ∂M.gibbs Λ = 0 := by
    simpa [twoPointSine, phase_twoPointFrequency] using hsin
  rw [complexTwoPoint, M.twoPoint_eq_integral_cos]
  simp_rw [hchar]
  rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, hsin']
  simp

end FroehlichSpencer.BKT.Ginibre.FreeModel

namespace FroehlichSpencer.BKT.Clock.Source

variable {V : Type*} [Fintype V]

/-- For a circle single-site measure, simultaneous angle reflection preserves its product law. -/
theorem circleProductMeasurePreservingNeg (V : Type*) [Fintype V] [DecidableEq V] :
    MeasurePreserving (fun θ : V → ℝ => -θ) (siteProduct circleMeasure V)
      (siteProduct circleMeasure V) := by
  refine ⟨measurable_neg, ?_⟩
  simpa only [siteProduct_circle] using map_neg_rotatorRawAngleMeasure V

/-- Reflection symmetry for a circle-based model whose bond weight is even. -/
theorem circleModel_twoPointSine_zero (M : FreeModel) (ξ : ℤ) (Λ : Finset (ℤ × ℤ))
    (u v : ℤ × ℤ) (hν : M.ν = circleMeasure) (hEven : ∀ x, M.w (-x) = M.w x) :
    M.twoPointSine ξ Λ u v = 0 := by
  apply M.twoPointSine_zero_of_reflection ξ Λ u v (fun θ => -θ)
  · simpa [hν] using circleProductMeasurePreservingNeg Λ
  · intro θ
    exact ⟨0, by simp [phase_neg_angle]⟩
  · intro θ
    exact M.pairWeight_neg_of_even Λ hEven θ

/-- Reflection of a clock angle in `[0,2π)`, represented by a point in the same interval. -/
def clockReflectAngle (x : ℝ) : ℝ := if x = 0 then 0 else 2 * Real.pi - x

/-- The reflected index on the `N` clock atoms. -/
def clockReflectIndex (N : ℕ) (hN : 0 < N) (j : Fin N) : Fin N :=
  if hj : j.val = 0 then ⟨0, hN⟩ else ⟨N - j.val, by omega⟩

theorem clockReflectIndex_involutive (N : ℕ) (hN : 0 < N) (j : Fin N) :
    clockReflectIndex N hN (clockReflectIndex N hN j) = j := by
  apply Fin.ext
  by_cases hj : j.val = 0
  · simp [clockReflectIndex, hj]
  · have hnot : N - j.val ≠ 0 := by omega
    simp [clockReflectIndex, hj, hnot]
    omega

/-- The label-reflection permutation `j ↦ -j` on `Fin N`. -/
def clockReflectEquiv (N : ℕ) (hN : 0 < N) : Fin N ≃ Fin N :=
  { toFun := clockReflectIndex N hN
    invFun := clockReflectIndex N hN
    left_inv := clockReflectIndex_involutive N hN
    right_inv := clockReflectIndex_involutive N hN }

/-- A clock atom as its representative in `[0,2π)`. -/
def clockRepresentative (N : ℕ) (j : Fin N) : ℝ := 2 * Real.pi * (j.val : ℝ) / N

theorem clockReflect_representative (N : ℕ) (hN : 0 < N) (j : Fin N) :
    clockReflectAngle (clockRepresentative N j) =
      clockRepresentative N (clockReflectIndex N hN j) := by
  by_cases hj : j.val = 0
  · simp [clockReflectAngle, clockRepresentative, clockReflectIndex, hj]
  · have hangle : clockRepresentative N j ≠ 0 := by
      unfold clockRepresentative
      have hjpos : (0 : ℝ) < (j.val : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
      positivity
    simp only [clockReflectAngle, hangle, ite_false, clockReflectIndex, dite_eq_right hj]
    unfold clockRepresentative
    rw [Nat.cast_sub (Nat.le_of_lt j.isLt)]
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp [hNreal]

theorem map_clockMeasure_clockReflectAngle (N : ℕ) (hN : 0 < N) :
    (clockMeasure N).map clockReflectAngle = clockMeasure N := by
  have hmeas : Measurable clockReflectAngle := by
    unfold clockReflectAngle
    exact measurable_const.piecewise (measurableSet_singleton 0)
      (measurable_const.sub measurable_id)
  unfold clockMeasure
  rw [Measure.map_finset_sum' hmeas.aemeasurable]
  simp only [Measure.map_dirac' hmeas]
  change (∑ j : Fin N, Measure.dirac
      (clockReflectAngle (clockRepresentative N j))) =
    ∑ j : Fin N, Measure.dirac (clockRepresentative N j)
  calc
    _ = ∑ j : Fin N, Measure.dirac (clockRepresentative N (clockReflectIndex N hN j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [clockReflect_representative]
    _ = ∑ j : Fin N, Measure.dirac (clockRepresentative N j) :=
      Equiv.sum_comp (clockReflectEquiv N hN)
        (fun j : Fin N => Measure.dirac (clockRepresentative N j))

/-- The coordinatewise clock reflection preserves the product clock measure. -/
theorem clockProductMeasurePreservingReflect (N : ℕ) (hN : 0 < N)
    (V : Type*) [Fintype V] :
    MeasurePreserving (fun θ : V → ℝ => fun x => clockReflectAngle (θ x))
      (siteProduct (clockMeasure N) V) (siteProduct (clockMeasure N) V) := by
  have hmeas : Measurable clockReflectAngle := by
    unfold clockReflectAngle
    exact measurable_const.piecewise (measurableSet_singleton 0)
      (measurable_const.sub measurable_id)
  have hmap := Measure.pi_map_pi (μ := fun _ : V => clockMeasure N)
    (f := fun _ x => clockReflectAngle x) (fun _ => hmeas.aemeasurable)
  simp only [map_clockMeasure_clockReflectAngle N hN] at hmap
  exact ⟨by fun_prop, by simpa [siteProduct] using hmap⟩

/-- The clock reflection has the form `x ↦ -x + 2πk`, so integer characters change sign. -/
theorem phase_clockReflect (n : Frequency V) (θ : V → ℝ) :
    ∃ k : ℤ, phase n (fun x => clockReflectAngle (θ x)) =
      -phase n θ + (k : ℝ) * (2 * Real.pi) := by
  let k : ℤ := ∑ x, n x * (if θ x = 0 then 0 else 1)
  refine ⟨k, ?_⟩
  unfold phase
  calc
    (∑ x, (n x : ℝ) * clockReflectAngle (θ x)) =
        ∑ x, ((n x : ℝ) * (-θ x) +
          (n x : ℝ) * ((if θ x = 0 then 0 else 1 : ℤ) : ℝ) * (2 * Real.pi)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [clockReflectAngle]
      split_ifs with h
      · simp [h]
      · ring
    _ = -phase n θ + (k : ℝ) * (2 * Real.pi) := by
      simp [k, phase, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        Finset.sum_mul, Int.cast_sum]

/-- The clock free Gibbs weight is invariant under the reflected representatives. -/
theorem clockModel_pairWeight_reflect (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β)
    (Λ : Finset (ℤ × ℤ)) (θ : Λ → ℝ) :
    pairWeight (bondFrequency Λ) ((clockModel N hN β hβ).bondWeight Λ)
      (fun x => clockReflectAngle (θ x)) =
    pairWeight (bondFrequency Λ) ((clockModel N hN β hβ).bondWeight Λ) θ := by
  unfold pairWeight
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [FreeModel.bondWeight]
  split_ifs with hstep
  · obtain ⟨k, hk⟩ := phase_clockReflect (bondFrequency Λ b) θ
    rw [hk]
    simp [clockModel, expCosWeight, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  · rfl

/-- **The clock sine part vanishes** in every finite free Gibbs measure, using the permutation of
clock atoms and the `2π` periodicity of the integer-frequency observable. -/
theorem clockModel_twoPointSine_zero (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β)
    (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (clockModel N hN β hβ).twoPointSine ξ Λ u v = 0 := by
  apply FreeModel.twoPointSine_zero_of_reflection (clockModel N hN β hβ) ξ Λ u v
    (fun θ x => clockReflectAngle (θ x))
  · exact clockProductMeasurePreservingReflect N hN Λ
  · exact phase_clockReflect (twoPointFrequency Λ ξ u v)
  · exact clockModel_pairWeight_reflect N hN β hβ Λ

/-- **The rotator sine part vanishes** in every finite free Gibbs measure. -/
theorem rotatorModel_twoPointSine_zero (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (rotatorModel β hβ).twoPointSine ξ Λ u v = 0 := by
  apply circleModel_twoPointSine_zero (rotatorModel β hβ) ξ Λ u v rfl
  intro x
  simp [rotatorModel, expCosWeight, Real.cos_neg]

/-- **The Villain sine part vanishes** in every finite free Gibbs measure. -/
theorem villainModel_twoPointSine_zero (β : ℝ) (hβ : 0 < β) (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (villainModel β hβ).twoPointSine ξ Λ u v = 0 := by
  apply circleModel_twoPointSine_zero (villainModel β hβ) ξ Λ u v rfl
  intro x
  exact VillainWeight.villainWeight_neg β x

/-- The complex character equals the real clock correlation in every finite free box. -/
theorem clockModel_complexTwoPoint_eq_real (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β)
    (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (clockModel N hN β hβ).complexTwoPoint ξ Λ u v =
      ((clockModel N hN β hβ).twoPoint ξ Λ u v : ℂ) :=
  FreeModel.complexTwoPoint_eq_ofReal_twoPoint_of_sine_zero _ _ _ _ _
    (clockModel_twoPointSine_zero N hN β hβ ξ Λ u v)

/-- The complex character equals the real rotator correlation in every finite free box. -/
theorem rotatorModel_complexTwoPoint_eq_real (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (rotatorModel β hβ).complexTwoPoint ξ Λ u v =
      ((rotatorModel β hβ).twoPoint ξ Λ u v : ℂ) :=
  FreeModel.complexTwoPoint_eq_ofReal_twoPoint_of_sine_zero _ _ _ _ _
    (rotatorModel_twoPointSine_zero β hβ ξ Λ u v)

/-- The complex character equals the real Villain correlation in every finite free box. -/
theorem villainModel_complexTwoPoint_eq_real (β : ℝ) (hβ : 0 < β) (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    (villainModel β hβ).complexTwoPoint ξ Λ u v =
      ((villainModel β hβ).twoPoint ξ Λ u v : ℂ) :=
  FreeModel.complexTwoPoint_eq_ofReal_twoPoint_of_sine_zero _ _ _ _ _
    (villainModel_twoPointSine_zero β hβ ξ Λ u v)

/-- The complex clock correlations converge to the complexification of the free real limit. -/
theorem clockModel_complexTwoPointLimit_tendsto (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β)
    (ξ : ℤ) (u v : ℤ × ℤ) :
    Tendsto (fun L : ℕ =>
      (clockModel N hN β hβ).complexTwoPoint ξ (freeBox L) u v) atTop
      (𝓝 ((clockModel N hN β hβ).complexTwoPointLimit ξ u v)) := by
  have hreal := (clockModel N hN β hβ).tendsto_twoPointLimit ξ u v
  have hcomplex := (Complex.continuous_ofReal.tendsto _).comp hreal
  simpa only [clockModel_complexTwoPoint_eq_real, FreeModel.complexTwoPointLimit,
    Function.comp_def] using hcomplex

/-- The complex rotator correlations converge to the complexification of the free real limit. -/
theorem rotatorModel_complexTwoPointLimit_tendsto (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (u v : ℤ × ℤ) :
    Tendsto (fun L : ℕ =>
      (rotatorModel β hβ).complexTwoPoint ξ (freeBox L) u v) atTop
      (𝓝 ((rotatorModel β hβ).complexTwoPointLimit ξ u v)) := by
  have hreal := (rotatorModel β hβ).tendsto_twoPointLimit ξ u v
  have hcomplex := (Complex.continuous_ofReal.tendsto _).comp hreal
  simpa only [rotatorModel_complexTwoPoint_eq_real, FreeModel.complexTwoPointLimit,
    Function.comp_def] using hcomplex

/-- The complex Villain correlations converge to the complexification of the free real limit. -/
theorem villainModel_complexTwoPointLimit_tendsto (β : ℝ) (hβ : 0 < β) (ξ : ℤ)
    (u v : ℤ × ℤ) :
    Tendsto (fun L : ℕ =>
      (villainModel β hβ).complexTwoPoint ξ (freeBox L) u v) atTop
      (𝓝 ((villainModel β hβ).complexTwoPointLimit ξ u v)) := by
  have hreal := (villainModel β hβ).tendsto_twoPointLimit ξ u v
  have hcomplex := (Complex.continuous_ofReal.tendsto _).comp hreal
  simpa only [villainModel_complexTwoPoint_eq_real, FreeModel.complexTwoPointLimit,
    Function.comp_def] using hcomplex

end FroehlichSpencer.BKT.Clock.Source

namespace FroehlichSpencer.BKT.Ginibre.FreeModel

/-- The complex free limit equals the real Ginibre limit. -/
theorem complexTwoPointLimit_eq_ofReal (M : FreeModel) (ξ : ℤ) (u v : ℤ × ℤ) :
    M.complexTwoPointLimit ξ u v = (M.twoPointLimit ξ u v : ℂ) := rfl

/-- The sine part of every complex free-limit correlation is zero. -/
theorem complexTwoPointLimit_im_zero (M : FreeModel) (ξ : ℤ) (u v : ℤ × ℤ) :
    Complex.im (M.complexTwoPointLimit ξ u v) = 0 := by
  rw [complexTwoPointLimit_eq_ofReal]
  simp

end FroehlichSpencer.BKT.Ginibre.FreeModel

namespace FroehlichSpencer.BKT.Clock.Source

/-- FS81 Theorem 7.1(1), with the complex expectations read by their real parts. -/
theorem clock_complex_dominates_rotator_finite (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β)
    (ξ : ℤ) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    Complex.re ((rotatorModel β hβ).complexTwoPoint ξ Λ u v) ≤
      Complex.re ((clockModel N hN β hβ).complexTwoPoint ξ Λ u v) := by
  rw [rotatorModel_complexTwoPoint_eq_real, clockModel_complexTwoPoint_eq_real,
    Complex.ofReal_re, Complex.ofReal_re, rotatorModel_twoPoint]
  exact freeTwoPoint_le_clock N hN hβ ξ Λ u v

/-- FS81 Theorem 7.1(1), in the free thermodynamic limit and read by real parts. -/
theorem clock_complex_dominates_rotator_limit (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β)
    (ξ : ℤ) (u v : ℤ × ℤ) :
    Complex.re ((rotatorModel β hβ).complexTwoPointLimit ξ u v) ≤
      Complex.re ((clockModel N hN β hβ).complexTwoPointLimit ξ u v) := by
  rw [FreeModel.complexTwoPointLimit_eq_ofReal, FreeModel.complexTwoPointLimit_eq_ofReal,
    Complex.ofReal_re, Complex.ofReal_re, rotatorModel_twoPointLimit]
  exact freeTwoPointLimit_le_clock N hN hβ ξ u v

/-- FS81 (7.3), restated for the complex clock function via its real part. -/
theorem clock_theorem73_complex :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ), Tendsto β' atTop atTop ∧
      ∀ (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β →
        1 / (4 * Real.pi) < β' β ∧ ∀ (ξ : ℤ) (u v : ℤ × ℤ),
          Real.exp (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) *
              ((l1Dist u v : ℝ) + 1) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β' β))) ≤
            Complex.re ((clockModel n hn β hβ).complexTwoPointLimit ξ u v) := by
  obtain ⟨β₀, β', hβ', h73⟩ := clock_theorem73
  refine ⟨β₀, β', hβ', fun n hn β hβ hβ₀ => ?_⟩
  obtain ⟨hb, hlower⟩ := h73 n hn β hβ hβ₀
  exact ⟨hb, fun ξ u v => by
    simpa only [clockCorr, FreeModel.complexTwoPointLimit_eq_ofReal, Complex.ofReal_re] using
      hlower ξ u v⟩

end FroehlichSpencer.BKT.Clock.Source

end
