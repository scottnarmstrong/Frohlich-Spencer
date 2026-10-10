/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.PrimalWeight
public import FroehlichSpencer.FS82.Wilson.PrimalStokes
public import FroehlichSpencer.FS82.Cubical.DualStokes
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Finite-volume primal Villain variables

Finite primal link angles are represented by the unit additive circle, rescaled
by `2π` in the literal Villain weight.  The circle Haar measure is normalized
and the boundary is free: every link of the finite box is integrated.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

noncomputable section

open FroehlichSpencer.FS82.Cubical
open MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- Finite links of the primal box. -/
abbrev PrimalLinks (B : Box 4) := {c : Cell 4 B // cellDegree c = 1}

/-- Finite plaquettes of the primal box. -/
abbrev PrimalPlaquettes (B : Box 4) := {c : Cell 4 B // cellDegree c = 2}

noncomputable instance primalLinksFintype {B : Box 4} : Fintype (PrimalLinks B) :=
  Fintype.ofFinite _

noncomputable instance primalPlaquettesFintype {B : Box 4} : Fintype (PrimalPlaquettes B) :=
  Fintype.ofFinite _

/-- The literal periodized Gaussian evaluated at the physical angle represented
by a unit-circle point. -/
@[expose] noncomputable def villainCircleWeight (β : ℝ) (z : UnitAddCircle) : ℝ :=
  (villainCircleFourierMap β z).re

theorem villainCircleWeight_continuous (β : ℝ) :
    Continuous (villainCircleWeight β) := by
  exact Complex.continuous_re.comp (villainCircleFourierMap β).continuous

theorem villainCircleWeight_eq_periodized (β : ℝ) (z : UnitAddCircle)
    (hβ : 0 < β) :
    villainCircleWeight β z =
      villainWeight β (2 * Real.pi * circleRepresentative z) := by
  rw [villainCircleWeight, villainCircleFourierMap_apply β z hβ,
    Complex.ofReal_re]

theorem villainCircleWeight_pos (β : ℝ) (z : UnitAddCircle) (hβ : 0 < β) :
    0 < villainCircleWeight β z := by
  rw [villainCircleWeight_eq_periodized β z hβ]
  exact villainWeight_pos β (2 * Real.pi * circleRepresentative z) hβ

/-- The finite product torus of primal link angles. -/
abbrev PrimalAngleConfig (B : Box 4) := PrimalLinks B → UnitAddCircle

/-- The integer-chain pairing with a circle-valued 1-cochain. -/
@[expose] noncomputable def circleChainPairing {B : Box 4}
    (q : Chain 4 B) (f : Cell 4 B → UnitAddCircle) : UnitAddCircle :=
  Finsupp.linearCombination ℤ f q

@[simp] theorem circleChainPairing_add {B : Box 4}
    (q r : Chain 4 B) (f : Cell 4 B → UnitAddCircle) :
    circleChainPairing (q + r) f = circleChainPairing q f + circleChainPairing r f := by
  simp [circleChainPairing, map_add]


/-- Extend primal link angles by zero to all cells not of degree one. -/
@[expose] def primalCircleCochain {B : Box 4}
    (θ : PrimalAngleConfig B) : Cell 4 B → UnitAddCircle := fun c =>
  if h : cellDegree c = 1 then θ ⟨c, h⟩ else 0

theorem continuous_primalCircleCochain_apply {B : Box 4} (c : Cell 4 B) :
    Continuous (fun θ : PrimalAngleConfig B => primalCircleCochain θ c) := by
  classical
  by_cases h : cellDegree c = 1
  · simpa [primalCircleCochain, h] using
      (continuous_apply (⟨c, h⟩ : PrimalLinks B))
  · simpa [primalCircleCochain, h] using (continuous_const : Continuous fun _ : PrimalAngleConfig B => (0 : UnitAddCircle))

/-- The circle-valued plaquette curl, defined from the repository's cubical
boundary incidence. -/
@[expose] noncomputable def primalPlaquetteFlux {B : Box 4}
    (θ : PrimalAngleConfig B) (p : PrimalPlaquettes B) : UnitAddCircle :=
  circleChainPairing (boundary (Finsupp.single p.1 1)) (primalCircleCochain θ)

theorem continuous_circleChainPairing {B : Box 4} (q : Chain 4 B) :
    Continuous (fun θ : PrimalAngleConfig B =>
      circleChainPairing q (primalCircleCochain θ)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero =>
      simpa [circleChainPairing] using
        (continuous_const : Continuous fun _ : PrimalAngleConfig B => (0 : UnitAddCircle))
  | add q r hq hr =>
      simp only [circleChainPairing, map_add]
      exact hq.add hr
  | single c n =>
      simp only [circleChainPairing, Finsupp.linearCombination_single]
      exact (continuous_primalCircleCochain_apply c).zsmul n

theorem continuous_primalPlaquetteFlux {B : Box 4} (p : PrimalPlaquettes B) :
    Continuous (fun θ : PrimalAngleConfig B => primalPlaquetteFlux θ p) := by
  exact continuous_circleChainPairing (boundary (Finsupp.single p.1 1))

/-- Circle-valued coboundary, defined as the transpose of the cubical boundary. -/
@[expose] noncomputable def circleCochainCoboundary {B : Box 4}
    (f : Cell 4 B → UnitAddCircle) : Cell 4 B → UnitAddCircle := fun c =>
  circleChainPairing (boundary (Finsupp.single c 1)) f

theorem circleChainPairing_boundary_eq_coboundary {B : Box 4}
    (q : Chain 4 B) (f : Cell 4 B → UnitAddCircle) :
    circleChainPairing (boundary q) f =
      circleChainPairing q (circleCochainCoboundary f) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [circleChainPairing]
  | add q r hq hr =>
      rw [map_add, circleChainPairing_add, hq, hr, ← circleChainPairing_add]
  | single c n =>
      have hsingle : Finsupp.single c n = n • Finsupp.single c (1 : ℤ) := by
        ext x
        by_cases hx : x = c <;> simp [hx]
      calc
        circleChainPairing (boundary (Finsupp.single c n)) f =
            circleChainPairing (n • boundary (Finsupp.single c 1)) f := by
              rw [hsingle, map_smul]
        _ = n • circleChainPairing (boundary (Finsupp.single c 1)) f := by
              simp [circleChainPairing]
        _ = circleChainPairing (Finsupp.single c n) (circleCochainCoboundary f) := by
              rw [hsingle]
              simp [circleChainPairing, circleCochainCoboundary]

/-- The free-boundary finite-volume Villain density on every link of the
finite box. -/
@[expose] noncomputable def primalVillainDensity {B : Box 4} (β : ℝ)
    (θ : PrimalAngleConfig B) : ℝ :=
  ∏ p : PrimalPlaquettes B, villainCircleWeight β (primalPlaquetteFlux θ p)

theorem primalVillainDensity_continuous {B : Box 4} (β : ℝ) :
    Continuous (primalVillainDensity (B := B) β) := by
  classical
  unfold primalVillainDensity
  refine continuous_finsetProd Finset.univ ?_
  intro p hp
  exact (villainCircleWeight_continuous β).comp (continuous_primalPlaquetteFlux p)

/-- The free-boundary primal partition function, with normalized Haar measure
on each link angle. -/
@[expose] noncomputable def primalVillainPartition {B : Box 4} (β : ℝ) : ℝ :=
  ∫ θ : PrimalAngleConfig B, primalVillainDensity (B := B) β θ

theorem primalVillainDensity_pos {B : Box 4} (β : ℝ) (θ : PrimalAngleConfig B)
    (hβ : 0 < β) : 0 < primalVillainDensity (B := B) β θ := by
  classical
  unfold primalVillainDensity
  exact Finset.prod_pos fun p hp => villainCircleWeight_pos β (primalPlaquetteFlux θ p) hβ

theorem primalVillainPartition_integrable {B : Box 4} (β : ℝ) :
    Integrable (primalVillainDensity (B := B) β) := by
  apply MeasureTheory.integrableOn_univ.mp
  exact (primalVillainDensity_continuous (B := B) β).continuousOn.integrableOn_compact
    isCompact_univ

theorem primalVillainPartition_pos {B : Box 4} (β : ℝ) (hβ : 0 < β) :
    0 < primalVillainPartition (B := B) β := by
  classical
  let θ₀ : PrimalAngleConfig B := fun _ => 0
  have hcont := primalVillainDensity_continuous (B := B) β
  have hint := primalVillainPartition_integrable (B := B) β
  have hnonneg : ∀ θ, 0 ≤ primalVillainDensity (B := B) β θ :=
    fun θ => (primalVillainDensity_pos β θ hβ).le
  have hzero : primalVillainDensity (B := B) β θ₀ ≠ 0 :=
    (primalVillainDensity_pos β θ₀ hβ).ne'
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero hcont hint hnonneg hzero


/-- Wilson observable of the oriented boundary of an integer plaquette sheet. -/
@[expose] noncomputable def primalWilsonObservable {B : Box 4}
    (θ : PrimalAngleConfig B) (S : Chain 4 B) : ℂ :=
  fourier (T := (1 : ℝ)) 1 (circleChainPairing (boundary S) (primalCircleCochain θ))

theorem continuous_primalWilsonObservable {B : Box 4} (S : Chain 4 B) :
    Continuous (primalWilsonObservable (B := B) · S) := by
  exact (fourier (T := (1 : ℝ)) 1).continuous.comp
    (continuous_circleChainPairing (boundary S))


/-- The unnormalized Wilson integral in free finite volume. -/
@[expose] noncomputable def primalWilsonNumerator {B : Box 4} (β : ℝ)
    (S : Chain 4 B) : ℂ :=
  ∫ θ : PrimalAngleConfig B,
    (primalVillainDensity (B := B) β θ : ℂ) * primalWilsonObservable θ S


/-- Normalized finite-volume Villain expectation of the Wilson observable. -/
@[expose] noncomputable def primalWilsonExpectation {B : Box 4} (β : ℝ)
    (S : Chain 4 B) : ℂ :=
  primalWilsonNumerator β S / (primalVillainPartition (B := B) β : ℂ)

end

end FroehlichSpencer.FS82.Wilson

end
