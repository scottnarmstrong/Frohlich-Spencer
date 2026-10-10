/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.PrimalMeasure
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The finite free-box Wilson and `ℤ_N` models

This is the finite free-box convention explicitly permitted after (3.8): all
links and plaquettes of `Cubical.Box 4` are included, with normalized Haar
measure on every link.

The Wilson plaquette factor is `exp (β cos dθ)`.

The finite interpolation uses the normalized factor
`ξ(h) exp (h cos (N θ))` on each link.
-/

public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Wilson
open MeasureTheory
open scoped BigOperators

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The real part of the `n`th character of the unit circle; it is
`cos(2π n θ)` in the paper's angle convention. -/
@[expose] def circleCosCharacter (n : ℕ) (z : UnitAddCircle) : ℝ :=
  (fourier (T := (1 : ℝ)) (n : ℤ) z).re

theorem continuous_circleCosCharacter (n : ℕ) :
    Continuous (circleCosCharacter n) := by
  exact Complex.continuous_re.comp (fourier (T := (1 : ℝ)) (n : ℤ)).continuous


/-- The Wilson Boltzmann factor for one primal plaquette. -/
@[expose] def wilsonPlaquetteFactor (β : ℝ) (z : UnitAddCircle) : ℝ :=
  Real.exp (β * circleCosCharacter 1 z)

theorem wilsonPlaquetteFactor_pos (β : ℝ) (z : UnitAddCircle) :
    0 < wilsonPlaquetteFactor β z := Real.exp_pos _

theorem continuous_wilsonPlaquetteFactor (β : ℝ) :
    Continuous (wilsonPlaquetteFactor β) := by
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_circleCosCharacter 1))

/-- Wilson's action on the full set of primal plaquettes in the free box. -/
@[expose] def wilsonActionDensity {B : Box 4} (β : ℝ)
    (θ : PrimalAngleConfig B) : ℝ :=
  ∏ p : PrimalPlaquettes B,
    wilsonPlaquetteFactor β (primalPlaquetteFlux θ p)

theorem continuous_wilsonActionDensity {B : Box 4} (β : ℝ) :
    Continuous (wilsonActionDensity (B := B) β) := by
  classical
  unfold wilsonActionDensity
  refine continuous_finsetProd Finset.univ ?_
  intro p hp
  exact (continuous_wilsonPlaquetteFactor β).comp (continuous_primalPlaquetteFlux p)

theorem wilsonActionDensity_pos {B : Box 4} (β : ℝ) (θ : PrimalAngleConfig B) :
    0 < wilsonActionDensity β θ := by
  classical
  unfold wilsonActionDensity
  exact Finset.prod_pos fun p hp => wilsonPlaquetteFactor_pos β _

/-- The free-box Wilson partition function, integrating all box links. -/
@[expose] def wilsonPartitionFunction {B : Box 4} (β : ℝ) : ℝ :=
  ∫ θ : PrimalAngleConfig B, wilsonActionDensity β θ


/-- The single-link pinning partition factor in (3.8), using normalized Haar.
This equals the displayed `1/(2π)` integral because Haar has mass one. -/
@[expose] def pinningNormalizer (N : ℕ) (h : NNReal) : ℝ :=
  ∫ z : UnitAddCircle, Real.exp ((h : ℝ) * circleCosCharacter N z)

theorem continuous_pinningIntegrand (N : ℕ) (h : NNReal) :
    Continuous (fun z : UnitAddCircle => Real.exp ((h : ℝ) * circleCosCharacter N z)) := by
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_circleCosCharacter N))

theorem pinningIntegrand_integrable (N : ℕ) (h : NNReal) :
    Integrable (fun z : UnitAddCircle => Real.exp ((h : ℝ) * circleCosCharacter N z)) := by
  apply MeasureTheory.integrableOn_univ.mp
  exact (continuous_pinningIntegrand N h).continuousOn.integrableOn_compact isCompact_univ

theorem pinningNormalizer_pos (N : ℕ) (h : NNReal) : 0 < pinningNormalizer N h := by
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
    (continuous_pinningIntegrand N h)
    (pinningIntegrand_integrable N h)
    (fun z => (Real.exp_pos _).le)
    (x := 0) (Real.exp_ne_zero _)

theorem pinningNormalizer_zero (N : ℕ) : pinningNormalizer N 0 = 1 := by
  simp [pinningNormalizer]

/-- The scalar `ξ(h)` of (3.8). -/
@[expose] def pinningNormalization (N : ℕ) (h : NNReal) : ℝ :=
  (pinningNormalizer N h)⁻¹

theorem pinningNormalization_pos (N : ℕ) (h : NNReal) :
    0 < pinningNormalization N h := inv_pos.mpr (pinningNormalizer_pos N h)

theorem pinningNormalization_zero (N : ℕ) : pinningNormalization N 0 = 1 := by
  simp [pinningNormalization, pinningNormalizer_zero]

/-- The normalized local `ℤ_N`-pinning factor in (3.7). -/
@[expose] def znPinningFactor (N : ℕ) (h : NNReal) (z : UnitAddCircle) : ℝ :=
  pinningNormalization N h * Real.exp ((h : ℝ) * circleCosCharacter N z)

theorem znPinningFactor_pos (N : ℕ) (h : NNReal) (z : UnitAddCircle) :
    0 < znPinningFactor N h z :=
  mul_pos (pinningNormalization_pos N h) (Real.exp_pos _)

theorem znPinningFactor_zero (N : ℕ) (z : UnitAddCircle) :
    znPinningFactor N 0 z = 1 := by
  simp [znPinningFactor, pinningNormalization_zero]

theorem continuous_znPinningFactor (N : ℕ) (h : NNReal) :
    Continuous (znPinningFactor N h) := by
  exact continuous_const.mul (continuous_pinningIntegrand N h)

/-- The normalized pinning factor on all links of the finite box. -/
@[expose] def znPinningDensity {B : Box 4} (N : ℕ) (h : NNReal)
    (θ : PrimalAngleConfig B) : ℝ :=
  ∏ e : PrimalLinks B, znPinningFactor N h (θ e)

theorem continuous_znPinningDensity {B : Box 4} (N : ℕ) (h : NNReal) :
    Continuous (znPinningDensity (B := B) N h) := by
  classical
  unfold znPinningDensity
  refine continuous_finsetProd Finset.univ ?_
  intro e he
  exact (continuous_znPinningFactor N h).comp (continuous_apply e)

theorem znPinningDensity_pos {B : Box 4} (N : ℕ) (h : NNReal)
    (θ : PrimalAngleConfig B) : 0 < znPinningDensity N h θ := by
  classical
  unfold znPinningDensity
  exact Finset.prod_pos fun e he => znPinningFactor_pos N h (θ e)


/-- The unnormalized finite interpolation density from (3.7), against product
normalized Haar measure on all box links. -/
@[expose] def finiteZNWeight {B : Box 4} (β : ℝ) (N : ℕ) (h : NNReal)
    (θ : PrimalAngleConfig B) : ℝ :=
  wilsonActionDensity β θ * znPinningDensity N h θ

theorem continuous_finiteZNWeight {B : Box 4} (β : ℝ) (N : ℕ) (h : NNReal) :
    Continuous (finiteZNWeight (B := B) β N h) := by
  exact (continuous_wilsonActionDensity β).mul (continuous_znPinningDensity N h)

theorem finiteZNWeight_pos {B : Box 4} (β : ℝ) (N : ℕ) (h : NNReal)
    (θ : PrimalAngleConfig B) : 0 < finiteZNWeight β N h θ :=
  mul_pos (wilsonActionDensity_pos β θ) (znPinningDensity_pos N h θ)


/-- The finite interpolation partition function `Z^h_{β,B}` of (3.8). -/
@[expose] def finiteZNPartitionFunction {B : Box 4} (β : ℝ) (N : ℕ) (h : NNReal) : ℝ :=
  ∫ θ : PrimalAngleConfig B, finiteZNWeight β N h θ

theorem finiteZNWeight_integrable {B : Box 4} (β : ℝ) (N : ℕ) (h : NNReal) :
    Integrable (finiteZNWeight (B := B) β N h) := by
  apply MeasureTheory.integrableOn_univ.mp
  exact (continuous_finiteZNWeight β N h).continuousOn.integrableOn_compact isCompact_univ

theorem finiteZNPartitionFunction_pos {B : Box 4} (β : ℝ) (N : ℕ) (h : NNReal) :
    0 < finiteZNPartitionFunction (B := B) β N h := by
  classical
  let θ₀ : PrimalAngleConfig B := fun _ => 0
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
    (continuous_finiteZNWeight β N h)
    (finiteZNWeight_integrable β N h)
    (fun θ => (finiteZNWeight_pos β N h θ).le)
    (finiteZNWeight_pos β N h θ₀).ne'


/-- The source's `Z^h_{β,B}` in (3.8), expressed relative to the normalized
finite free-box Wilson law. -/
@[expose] def finiteZNRelativePartitionFunction {B : Box 4} (β : ℝ) (N : ℕ)
    (h : NNReal) : ℝ :=
  finiteZNPartitionFunction (B := B) β N h / wilsonPartitionFunction (B := B) β


/-- The finite-volume `ℤ_N` configuration space. -/
abbrev ZNConfig (B : Box 4) (N : ℕ) := PrimalLinks B → Fin N

/-- The `k`th `N`th root of unity, expressed in `UnitAddCircle = ℝ/ℤ`. -/
@[expose] def znRoot (N : ℕ) (k : Fin N) : UnitAddCircle :=
  ((k.val : ℝ) / (N : ℝ) : UnitAddCircle)


/-- Inclusion of discrete link configurations into the circle-valued link
configuration space. -/
@[expose] def znConfigAsCircle {B : Box 4} (N : ℕ) (a : ZNConfig B N) :
    PrimalAngleConfig B := fun e => znRoot N (a e)

/-- The literal finite discrete Wilson weight at the `h = ∞` endpoint. -/
@[expose] def discreteZNWeight {B : Box 4} (β : ℝ) (N : ℕ) (a : ZNConfig B N) : ℝ :=
  wilsonActionDensity β (znConfigAsCircle N a)

theorem discreteZNWeight_pos {B : Box 4} (β : ℝ) (N : ℕ) (a : ZNConfig B N) :
    0 < discreteZNWeight β N a :=
  wilsonActionDensity_pos β _

/-- The finite free-boundary partition function of the discrete `ℤ_N` Wilson
model, with counting measure on every link. -/
@[expose] def discreteZNPartitionFunction {B : Box 4} (β : ℝ) (N : ℕ) : ℝ :=
  ∑ a : ZNConfig B N, discreteZNWeight β N a

theorem discreteZNPartitionFunction_pos {B : Box 4} (β : ℝ) (N : ℕ)
    (hN : 0 < N) : 0 < discreteZNPartitionFunction (B := B) β N := by
  classical
  apply Finset.sum_pos
  · intro a ha
    exact discreteZNWeight_pos β N a
  · exact Finset.univ_nonempty_iff.mpr ⟨fun _ => ⟨0, hN⟩⟩


end

end FroehlichSpencer.FS82.ZN

end
