/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Reduction.TendstoKubo
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Norm
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.GaussianLaw
public import FroehlichSpencer.Surface.GreenFunctionSpec
public import FroehlichSpencer.Surface.LatticeLength
public import FroehlichSpencer.Surface.GaussianBoundedDensity
public import FroehlichSpencer.Surface.GaussianProbability
public import FroehlichSpencer.Surface.IntegratedDensityOfStatesSpec
public import FroehlichSpencer.Surface.IsDiffusionCoefficient
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Theorem 1.2 implies Theorem 1.1
-/

public section

open MeasureTheory Topology

namespace FroehlichSpencer.Reduction

/--
The exact T1.2 proposition, copied binder-for-binder as a local premise for
the conditional reduction.
-/
@[expose] def greenProbabilityBoundStatement (ν : ℕ) (hν : 0 < ν) : Prop :=
  ∃ (largeDisorder : ℝ → ℝ → ℝ)
      (highEnergy : ℝ → ℝ → ℝ → ℝ)
      (Kp : ℝ → ℝ)
      (Kgauss : ℝ → ℝ → ℝ → ℝ),
      (∀ p m, 0 < m → 0 < p → 0 < largeDisorder p m) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 < highEnergy γ p m) ∧
      (∀ p, 0 < p → 0 ≤ Kp p) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 ≤ Kgauss γ p m) ∧
      ∀ (m p : ℝ), 0 < m → 0 < p →
        ∀ (law : Measure ℝ), [IsProbabilityMeasure law] →
        ∀ (E : ℝ) (x : Site ν),
          ∀ (N : ℝ), 0 < N →
            let S : Set (Configuration ν) :=
              {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
                ‖greenFunction ν hν
                    ((E : ℂ) + (ε : ℂ) * Complex.I) (by simpa using hε)
                    v (0 : Site ν) x‖ ≤
                  Real.exp (m * (N - latticeLength ν x))}
            ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder p m) →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kp p / Real.rpow N p) ≤
                    configurationMeasure ν law S) ∧
              (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
                highEnergy γ p m ≤ |E - 2 * (ν : ℝ)| →
                MeasurableSet S ∧
                  ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p) ≤
                    configurationMeasure ν law S)

/-- The exact T1.1 proposition appearing as the result type of the surface
theorem. -/
@[expose] def theorem11Statement (ν : ℕ) (hν : 0 < ν) : Prop :=
  ∃ largeDisorder : ℝ, 0 < largeDisorder ∧
    ∃ highEnergy : {γ : ℝ // 0 < γ} → ℝ,
      (∀ γ : {γ : ℝ // 0 < γ}, 0 < highEnergy γ) ∧
      (∀ (law : Measure ℝ) [IsProbabilityMeasure law]
        (δ : ℝ) (hlaw : HasBoundedDensity law δ),
        δ⁻¹ ≤ largeDisorder →
        ∀ E r : ℝ,
          HasDerivAt (integratedDensityOfStates ν hν law δ hlaw) r E →
          0 < r →
            ∃! D : ℝ,
              is_diffusion_coefficient ν hν law E r D ∧ D = 0) ∧
      (∀ (γ : ℝ) (hγ : 0 < γ),
        ∀ E r : ℝ,
          highEnergy ⟨γ, hγ⟩ < |E - 2 * (ν : ℝ)| →
          HasDerivAt
            (integratedDensityOfStates ν hν (gaussianLaw γ hγ)
              (Real.sqrt (2 * Real.pi * γ))
              (has_bounded_density_gaussian_law γ hγ)) r E →
          0 < r →
            ∃! D : ℝ,
              is_diffusion_coefficient ν hν (gaussianLaw γ hγ) E r D ∧ D = 0)

private theorem existsUnique_zero_diffusion
    (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ) [IsProbabilityMeasure law]
    (E r : ℝ) (hr : 0 < r)
    (hlim : Filter.Tendsto
      (fun ε : {ε : ℝ // ε ≠ 0} => kuboQuantity ν hν law E ε)
      (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0)) :
    ∃! D : ℝ, is_diffusion_coefficient ν hν law E r D ∧ D = 0 := by
  refine ⟨0, ?_, ?_⟩
  · constructor
    · change 0 < r ∧ 0 ≤ (0 : ℝ) ∧ Filter.Tendsto
        (fun ε : {ε : ℝ // ε ≠ 0} => kuboQuantity ν hν law E ε)
        (Filter.comap Subtype.val (𝓝[>] (0 : ℝ)))
        (𝓝 (ENNReal.ofReal (r * 0)))
      exact ⟨hr, le_rfl, by simpa using hlim⟩
    · rfl
  · intro D hD
    exact hD.2

/--
Conditional reduction of Theorem 1.1 from the exact T1.2 statement.

The square in the Kubo integrand gives exponent `2m(N-|x|)` in the good term;
this is the corrected factor in the printed (1.25).
-/
theorem theorem_1_1_of_green_probability_bound_statement
    (ν : ℕ) (hν : 0 < ν)
    (hT12 : greenProbabilityBoundStatement ν hν) :
    theorem11Statement ν hν := by
  rcases hT12 with ⟨largeDisorder, highEnergy, Kp, Kgauss,
    hLargeDisorder, hHighEnergy, hKp, hKgauss, hEvents⟩
  let p : ℝ := ((ν + 5 : ℕ) : ℝ)
  let m : ℝ := 1
  have hm : 0 < m := by norm_num [m]
  have hpAbove : (ν : ℝ) + 2 < p := by
    dsimp [p]
    norm_num
  have hp : 0 < p := lt_trans (by positivity) hpAbove
  refine ⟨largeDisorder p m, hLargeDisorder p m hm hp,
    (fun γ : {γ : ℝ // 0 < γ} => highEnergy γ.1 p m), ?_, ?_, ?_⟩
  · intro γ
    exact hHighEnergy γ.1 p m γ.2 hm hp
  · intro law instLaw δ hlaw hδ E r _hDeriv hr
    have hEventsR : ∀ R : ℝ, 1 ≤ R → ∀ x : Site ν,
        MeasurableSet (greenDecayEvent ν hν E m (dyadicGreenScale ν R x) x) ∧
        ENNReal.ofReal (1 - Kp p / Real.rpow (dyadicGreenScale ν R x) p) ≤
          configurationMeasure ν law
            (greenDecayEvent ν hν E m (dyadicGreenScale ν R x) x) := by
      intro R hR x
      have hN : 0 < dyadicGreenScale ν R x := by
        unfold dyadicGreenScale
        positivity
      have hbound := hEvents m p hm hp law E x (dyadicGreenScale ν R x) hN
      have hregime : ∃ δ' : ℝ,
          HasBoundedDensity law δ' ∧ δ'⁻¹ ≤ largeDisorder p m :=
        ⟨δ, hlaw, hδ⟩
      simpa [greenDecayEvent, p, m] using hbound.1 hregime
    have hlim := kubo_tendsto_zero_of_dyadic_events ν hν law E m (Kp p)
      hm (hKp p hp) hEventsR
    exact existsUnique_zero_diffusion ν hν law E r hr hlim
  · intro γ hγ E r hEnergy _hDeriv hr
    have hEventsR : ∀ R : ℝ, 1 ≤ R → ∀ x : Site ν,
        MeasurableSet
          (greenDecayEvent ν hν E m (dyadicGreenScale ν R x) x) ∧
        ENNReal.ofReal
            (1 - Kgauss γ p m /
              Real.rpow (dyadicGreenScale ν R x) p) ≤
          configurationMeasure ν (gaussianLaw γ hγ)
            (greenDecayEvent ν hν E m (dyadicGreenScale ν R x) x) := by
      intro R hR x
      have hN : 0 < dyadicGreenScale ν R x := by
        unfold dyadicGreenScale
        positivity
      have hbound := hEvents m p hm hp (gaussianLaw γ hγ) E x
        (dyadicGreenScale ν R x) hN
      have henergy' : highEnergy γ p m ≤ |E - 2 * (ν : ℝ)| := by
        exact le_of_lt hEnergy
      simpa [greenDecayEvent, p, m] using
        hbound.2 γ hγ rfl henergy'
    have hlim := kubo_tendsto_zero_of_dyadic_events ν hν
      (gaussianLaw γ hγ) E m (Kgauss γ p m) hm
      (hKgauss γ p m hγ hm hp) hEventsR
    exact existsUnique_zero_diffusion ν hν (gaussianLaw γ hγ) E r hr hlim

end FroehlichSpencer.Reduction

end
