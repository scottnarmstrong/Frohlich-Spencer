/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.Incidence
public import FroehlichSpencer.FS82.Wilson.PrimalMeasure
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Finite free-box Villain XY law

The spin angles live on the degree-zero cells of `Cubical.Box D`; every
degree-one cell contributes one periodized-Gaussian bond factor.  The angle
measure is normalized Haar measure on the finite product torus.
-/

public section

namespace FroehlichSpencer.FS82.XY

noncomputable section

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Wilson
open MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- Sites of a finite cubical box. -/
abbrev XYSites {D : ℕ} (B : Box D) := {c : Cell D B // cellDegree c = 0}

/-- Oriented positive-coordinate nearest-neighbour bonds of a finite cubical
box. -/
abbrev XYBonds {D : ℕ} (B : Box D) := {c : Cell D B // cellDegree c = 1}

noncomputable instance xySitesFintype {D : ℕ} {B : Box D} : Fintype (XYSites B) :=
  Fintype.ofFinite _

noncomputable instance xyBondsFintype {D : ℕ} {B : Box D} : Fintype (XYBonds B) :=
  Fintype.ofFinite _

/-- A site-angle configuration, with no boundary angles fixed. -/
abbrev XYAngleConfig {D : ℕ} (B : Box D) := XYSites B → UnitAddCircle

/-- Pair an integer cubical chain with a circle-valued cochain. -/
@[expose] noncomputable def xyCircleChainPairing {D : ℕ} {B : Box D}
    (q : Chain D B) (f : Cell D B → UnitAddCircle) : UnitAddCircle :=
  Finsupp.linearCombination ℤ f q

@[simp] theorem xyCircleChainPairing_add {D : ℕ} {B : Box D}
    (q r : Chain D B) (f : Cell D B → UnitAddCircle) :
    xyCircleChainPairing (q + r) f = xyCircleChainPairing q f + xyCircleChainPairing r f := by
  simp [xyCircleChainPairing, map_add]

@[simp] theorem xyCircleChainPairing_smul {D : ℕ} {B : Box D}
    (n : ℤ) (q : Chain D B) (f : Cell D B → UnitAddCircle) :
    xyCircleChainPairing (n • q) f = n • xyCircleChainPairing q f := by
  simp [xyCircleChainPairing, map_smul]

/-- Extend site angles by zero to the other cubical cells. -/
@[expose] def xyAngleCochain {D : ℕ} {B : Box D}
    (θ : XYAngleConfig B) : Cell D B → UnitAddCircle := fun c =>
  if h : cellDegree c = 0 then θ ⟨c, h⟩ else 0

theorem continuous_xyAngleCochain_apply {D : ℕ} {B : Box D} (c : Cell D B) :
    Continuous (fun θ : XYAngleConfig B => xyAngleCochain θ c) := by
  classical
  by_cases h : cellDegree c = 0
  · simpa [xyAngleCochain, h] using
      (continuous_apply (⟨c, h⟩ : XYSites B))
  · simpa [xyAngleCochain, h] using
      (continuous_const : Continuous fun _ : XYAngleConfig B => (0 : UnitAddCircle))

/-- The oriented angle difference across a bond, as the coboundary of the
site-angle cochain. -/
@[expose] noncomputable def xyBondDifference {D : ℕ} {B : Box D}
    (θ : XYAngleConfig B) (b : XYBonds B) : UnitAddCircle :=
  xyCircleChainPairing (boundary (Finsupp.single b.1 1)) (xyAngleCochain θ)

theorem continuous_xyCircleChainPairing {D : ℕ} {B : Box D} (q : Chain D B) :
    Continuous (fun θ : XYAngleConfig B =>
      xyCircleChainPairing q (xyAngleCochain θ)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero =>
      simpa [xyCircleChainPairing] using
        (continuous_const : Continuous fun _ : XYAngleConfig B => (0 : UnitAddCircle))
  | add q r hq hr =>
      simp only [xyCircleChainPairing, map_add]
      exact hq.add hr
  | single c n =>
      simp only [xyCircleChainPairing, Finsupp.linearCombination_single]
      exact (continuous_xyAngleCochain_apply c).zsmul n

theorem continuous_xyBondDifference {D : ℕ} {B : Box D} (b : XYBonds B) :
    Continuous (fun θ : XYAngleConfig B => xyBondDifference θ b) :=
  continuous_xyCircleChainPairing (boundary (Finsupp.single b.1 1))

/-- The free-boundary Villain density: all bonds in the box are included. -/
@[expose] noncomputable def xyVillainDensity {D : ℕ} {B : Box D} (β : ℝ)
    (θ : XYAngleConfig B) : ℝ :=
  ∏ b : XYBonds B, villainCircleWeight β (xyBondDifference θ b)

theorem xyVillainDensity_continuous {D : ℕ} {B : Box D} (β : ℝ) :
    Continuous (xyVillainDensity (B := B) β) := by
  classical
  unfold xyVillainDensity
  refine continuous_finsetProd Finset.univ ?_
  intro b hb
  exact (villainCircleWeight_continuous β).comp (continuous_xyBondDifference b)

/-- The finite-box XY Villain partition function, using normalized Haar angle
measure at every site. -/
@[expose] noncomputable def xyVillainPartition {D : ℕ} {B : Box D} (β : ℝ) : ℝ :=
  ∫ θ : XYAngleConfig B, xyVillainDensity (B := B) β θ

theorem xyVillainDensity_pos {D : ℕ} {B : Box D} (β : ℝ)
    (θ : XYAngleConfig B) (hβ : 0 < β) :
    0 < xyVillainDensity (B := B) β θ := by
  classical
  unfold xyVillainDensity
  exact Finset.prod_pos fun b hb => villainCircleWeight_pos β (xyBondDifference θ b) hβ

theorem xyVillainPartition_integrable {D : ℕ} {B : Box D} (β : ℝ) :
    Integrable (xyVillainDensity (B := B) β) := by
  apply MeasureTheory.integrableOn_univ.mp
  exact (xyVillainDensity_continuous (B := B) β).continuousOn.integrableOn_compact
    isCompact_univ

theorem xyVillainPartition_pos {D : ℕ} {B : Box D} (β : ℝ) (hβ : 0 < β) :
    0 < xyVillainPartition (B := B) β := by
  classical
  let θ₀ : XYAngleConfig B := fun _ => 0
  have hcont := xyVillainDensity_continuous (B := B) β
  have hint := xyVillainPartition_integrable (B := B) β
  have hnonneg : ∀ θ, 0 ≤ xyVillainDensity (B := B) β θ :=
    fun θ => (xyVillainDensity_pos β θ hβ).le
  have hzero : xyVillainDensity (B := B) β θ₀ ≠ 0 :=
    (xyVillainDensity_pos β θ₀ hβ).ne'
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero hcont hint hnonneg hzero


/-- The endpoint character `exp(i(θₓ−θᵧ))` in the unit-circle convention. -/
@[expose] def xyEndpointCharacter {D : ℕ} {B : Box D}
    (θ : XYAngleConfig B) (x y : XYSites B) : ℂ :=
  fourier (T := (1 : ℝ)) 1 (θ x - θ y)

/-- The spin dot product, represented as the real part of the endpoint
character (the usual `cos(θₓ−θᵧ)`). -/
@[expose] def xyEndpointCos {D : ℕ} {B : Box D}
    (θ : XYAngleConfig B) (x y : XYSites B) : ℝ :=
  (xyEndpointCharacter θ x y).re


theorem continuous_xyEndpointCharacter {D : ℕ} {B : Box D} (x y : XYSites B) :
    Continuous (fun θ : XYAngleConfig B => xyEndpointCharacter θ x y) := by
  exact (fourier (T := (1 : ℝ)) 1).continuous.comp
    ((continuous_apply x).sub (continuous_apply y))


/-- The unnormalized complex endpoint-spin integral. -/
@[expose] noncomputable def xyEndpointCharacterNumerator {D : ℕ} {B : Box D}
    (β : ℝ) (x y : XYSites B) : ℂ :=
  ∫ θ : XYAngleConfig B,
    (xyVillainDensity (B := B) β θ : ℂ) * xyEndpointCharacter θ x y

theorem xyEndpointCharacterNumerator_integrable {D : ℕ} {B : Box D}
    (β : ℝ) (x y : XYSites B) :
    Integrable fun θ : XYAngleConfig B =>
      (xyVillainDensity (B := B) β θ : ℂ) * xyEndpointCharacter θ x y := by
  have hcont : Continuous fun θ : XYAngleConfig B =>
      (xyVillainDensity (B := B) β θ : ℂ) * xyEndpointCharacter θ x y := by
    exact (Complex.continuous_ofReal.comp (xyVillainDensity_continuous (B := B) β)).mul
      (continuous_xyEndpointCharacter x y)
  apply MeasureTheory.integrableOn_univ.mp
  exact hcont.continuousOn.integrableOn_compact isCompact_univ

/-- The unnormalized real spin-dot integral. -/
@[expose] noncomputable def xyEndpointCosNumerator {D : ℕ} {B : Box D}
    (β : ℝ) (x y : XYSites B) : ℝ :=
  ∫ θ : XYAngleConfig B, xyVillainDensity (B := B) β θ * xyEndpointCos θ x y


/-- The normalized finite-volume complex spin expectation. -/
@[expose] noncomputable def xyEndpointCharacterExpectation {D : ℕ} {B : Box D}
    (β : ℝ) (x y : XYSites B) : ℂ :=
  xyEndpointCharacterNumerator β x y / (xyVillainPartition (B := B) β : ℂ)

/-- The normalized finite-volume expectation of `cos(θₓ−θᵧ)`. -/
@[expose] noncomputable def xyEndpointCosExpectation {D : ℕ} {B : Box D}
    (β : ℝ) (x y : XYSites B) : ℝ :=
  xyEndpointCosNumerator β x y / xyVillainPartition (B := B) β

theorem xyEndpointCosExpectation_eq_re_characterExpectation {D : ℕ} {B : Box D}
    (β : ℝ) (_hβ : 0 < β) (x y : XYSites B) :
    xyEndpointCosExpectation β x y = (xyEndpointCharacterExpectation β x y).re := by
  have hInt := xyEndpointCharacterNumerator_integrable (B := B) β x y
  have hnum : xyEndpointCosNumerator β x y = (xyEndpointCharacterNumerator β x y).re := by
    unfold xyEndpointCosNumerator xyEndpointCharacterNumerator
    calc
      _ = ∫ θ : XYAngleConfig B,
          ((xyVillainDensity (B := B) β θ : ℂ) * xyEndpointCharacter θ x y).re := by
            apply integral_congr_ae
            filter_upwards with θ
            simp [xyEndpointCos, Complex.mul_re]
      _ = _ := integral_re hInt
  unfold xyEndpointCosExpectation xyEndpointCharacterExpectation
  rw [hnum]
  exact (Complex.div_ofReal_re _ _).symm


end

end FroehlichSpencer.FS82.XY

end
