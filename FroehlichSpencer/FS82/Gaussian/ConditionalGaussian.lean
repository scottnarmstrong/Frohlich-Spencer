/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Chart-level conditioning on a plaquette-independent link set

The selected coordinates of a finite curl chart have a diagonal precision block.
This file records the resulting square completion and its product Gaussian
normalization for the literal unnormalized chart density.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace FroehlichSpencer.FS82.Gaussian.ConditionalGaussian

variable {C P : Type*} [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]

/-- Use the standard subtype enumeration consistently across finite chart measures. -/
local instance (priority := 2000) selectedCoordFintype (B : Finset C) :
    Fintype {c : C // c ∈ B} := Subtype.fintype _

local instance (priority := 2000) retainedCoordFintype (B : Finset C) :
    Fintype {c : C // c ∉ B} := Subtype.fintype _

/-- The retained field associated with coordinates on the complement of `B`. -/
def retainedField (B : Finset C) (y : {c : C // c ∉ B} → ℝ) : C → ℝ :=
  fun c => if h : c ∈ B then 0 else y ⟨c, h⟩

/-- The selected coordinate field associated with coordinates on `B`. -/
def selectedField (B : Finset C) (x : {c : C // c ∈ B} → ℝ) : C → ℝ :=
  fun c => if h : c ∈ B then x ⟨c, h⟩ else 0

/-- Plaquette precision of a selected link. -/
def linkMass (s : P → C → ℝ) (b : C) : ℝ :=
  ∑ p : P, (s p b) ^ 2

/-- Linear term seen by a selected link after the retained coordinates are fixed. -/
def linkOffset (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (b : C) : ℝ :=
  ∑ p : P, s p b *
    FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlField s
      (retainedField B y) p

/-- The retained quadratic form after integrating the selected coordinates. -/
noncomputable def reducedEnergy (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) : ℝ :=
  FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy s (retainedField B y) -
    ∑ b ∈ B, (linkOffset s B y b) ^ 2 / linkMass s b

/-- The full chart field assembled from retained and selected coordinates. -/
def assemble (B : Finset C) (y : {c : C // c ∉ B} → ℝ)
    (x : {c : C // c ∈ B} → ℝ) : C → ℝ := retainedField B y + selectedField B x

omit [DecidableEq P] in
/-- The selected block square completion, with the exact conditional mean
`-linkOffset/linkMass`. -/
theorem curlEnergy_eq_reducedEnergy_add_squares (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (x : {c : C // c ∈ B} → ℝ)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b) :
    FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy s (assemble B y x) =
      reducedEnergy s B y +
        ∑ b ∈ B, linkMass s b *
          (selectedField B x b + linkOffset s B y b / linkMass s b) ^ 2 := by
  classical
  let xfull : C → ℝ := selectedField B x
  have hdecomp :=
    FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy_decompose_selected
      s B (retainedField B y) xfull hsep
  have hfield : selectedField B x =
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.selectedPart B xfull := by
    funext c
    by_cases hc : c ∈ B <;> simp [selectedField, xfull,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.selectedPart, hc]
  rw [← hfield] at hdecomp
  have hdecomp' :
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy s (assemble B y x) =
        FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy s (retainedField B y) +
          ∑ b ∈ B, (linkMass s b * xfull b ^ 2 +
            2 * linkOffset s B y b * xfull b) := by
    change FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy s
        (retainedField B y + selectedField B x) = _
    simpa [linkMass, linkOffset,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.selectedDiagonalMass,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.selectedLinearOffset,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlField] using hdecomp
  rw [hdecomp']
  rw [show (∑ b ∈ B,
      (linkMass s b * xfull b ^ 2 + 2 * linkOffset s B y b * xfull b)) =
      ∑ b ∈ B,
        (linkMass s b * (xfull b + linkOffset s B y b / linkMass s b) ^ 2 -
          (linkOffset s B y b) ^ 2 / linkMass s b) by
        apply Finset.sum_congr rfl
        intro b hb
        exact FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.selectedQuadratic_completeSquare
          (linkMass s b) (linkOffset s B y b) (xfull b) (hn b hb)]
  unfold reducedEnergy
  rw [Finset.sum_sub_distrib]
  simp [xfull, selectedField]
  ring

/-- A translated one-dimensional Gaussian integral. -/
theorem shiftedGaussianIntegral (a c : ℝ) :
    (∫ x : ℝ, Real.exp (-a * (x + c) ^ 2)) = Real.sqrt (Real.pi / a) := by
  calc
    (∫ x : ℝ, Real.exp (-a * (x + c) ^ 2)) =
        ∫ x : ℝ, (fun x : ℝ => Real.exp (-a * x ^ 2)) (x + c) := by rfl
    _ = ∫ x : ℝ, Real.exp (-a * x ^ 2) :=
      integral_add_right_eq_self (fun x : ℝ => Real.exp (-a * x ^ 2)) c
    _ = Real.sqrt (Real.pi / a) := integral_gaussian a

/-- The normalizing constant for one selected coordinate. -/
noncomputable def linkGaussianMass (β n : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * β / n)

/-- The literal real-valued density in the user's unnormalized chart measure. -/
noncomputable def chartWeight (β : ℝ) (s : P → C → ℝ) (x : C → ℝ) : ℝ :=
  Real.exp (-(1 / (2 * β)) *
    FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy s x)

/-- The normalized conditional density of the selected coordinates given `y`. -/
noncomputable def selectedConditionalWeight (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (x : {c : C // c ∈ B} → ℝ) : ℝ :=
  (∏ b : {c : C // c ∈ B},
      Real.exp (-(linkMass s b.1 / (2 * β)) *
        (x b + linkOffset s B y b.1 / linkMass s b.1) ^ 2)) /
    (∏ b : {c : C // c ∈ B}, linkGaussianMass β (linkMass s b.1))

/-- The unnormalized density of the retained-coordinate marginal. -/
noncomputable def reducedWeight (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) : ℝ :=
  Real.exp (-(1 / (2 * β)) * reducedEnergy s B y) *
    ∏ b : {c : C // c ∈ B}, linkGaussianMass β (linkMass s b.1)


noncomputable def chartMeasure (β : ℝ) (s : P → C → ℝ) : Measure (C → ℝ) :=
  (volume : Measure (C → ℝ)).withDensity
    (fun x => ENNReal.ofReal (chartWeight β s x))

omit [DecidableEq C] [DecidableEq P] in
/-- The chart measure uses exactly the literal `ENNReal.ofReal exp` density, and its Bochner
integrals are the corresponding real weighted-volume integrals. -/
theorem chartMeasure_integral_eq (β : ℝ) (s : P → C → ℝ) (F : (C → ℝ) → ℝ) :
    (∫ x, F x ∂chartMeasure β s) =
      ∫ x, chartWeight β s x * F x := by
  rw [chartMeasure, integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards [] with x
    change (ENNReal.ofReal (Real.exp _) ).toReal * F x = Real.exp _ * F x
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  · fun_prop [chartWeight,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlEnergy,
      FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic.curlField]
  · filter_upwards [] with x
    exact ENNReal.ofReal_lt_top

/-- The retained-coordinate marginal density obtained by integrating the selected block. -/
noncomputable def reducedMeasure (β : ℝ) (s : P → C → ℝ) (B : Finset C) :
    Measure ({c : C // c ∉ B} → ℝ) :=
  volume.withDensity (fun y => ENNReal.ofReal (reducedWeight β s B y))

/-- Measurable coordinate split from the full chart to retained coordinates followed by selected
coordinates. -/
noncomputable def chartSplitEquiv (B : Finset C) :
    (C → ℝ) ≃ᵐ (({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ)) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : C => ℝ) (fun c => c ∈ B)).trans
    MeasurableEquiv.prodComm

omit [Fintype C] in
/-- The inverse of the measurable split is the coordinate assembly used in the energy identity. -/
theorem chartSplitEquiv_symm_apply (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (x : {c : C // c ∈ B} → ℝ) :
    (chartSplitEquiv B).symm (y, x) = assemble B y x := by
  classical
  funext c
  by_cases hc : c ∈ B
  · change ((Equiv.piEquivPiSubtypeProd (fun c => c ∈ B) (fun _ : C => ℝ)).symm
      (x, y)) c = _
    simp [assemble, selectedField, retainedField, hc]
  · change ((Equiv.piEquivPiSubtypeProd (fun c => c ∈ B) (fun _ : C => ℝ)).symm
      (x, y)) c = _
    simp [assemble, selectedField, retainedField, hc]

omit [Fintype P] [DecidableEq P] in
/-- Splitting the product measure on a finite chart into retained and selected coordinates
preserves measure. By `volume_pi`, each `Measure.pi` here is the Euclidean volume on its finite
coordinate space. -/
theorem chartSplitEquiv_measurePreserving (B : Finset C) :
    MeasurePreserving (chartSplitEquiv B)
      (Measure.pi (fun _ : C => (volume : Measure ℝ)))
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))) := by
  classical
  let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : C => ℝ) (fun c => c ∈ B)
  have hsplit : MeasurePreserving split (Measure.pi (fun _ : C => (volume : Measure ℝ)))
      ((Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ)))) :=
    measurePreserving_piEquivPiSubtypeProd
      (fun _ : C => (volume : Measure ℝ)) (fun c => c ∈ B)
  have hswap := Measure.measurePreserving_swap
    (μ := Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))
    (ν := Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ)))
  have h := hswap.comp hsplit
  convert h using 1
  rfl

omit [Fintype P] [DecidableEq P] in
/-- Fubini's theorem in the finite chart coordinates `U × B`. The source measure is the pi volume
on `C → ℝ`; the two coordinate pi volumes are the Euclidean volumes by `volume_pi`. -/
theorem chartFubini_pi (B : Finset C)
    (F : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) → ℝ)
    (hF : Integrable F
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ))))) :
    (∫ x : C → ℝ, F (chartSplitEquiv B x)
      ∂Measure.pi (fun _ : C => (volume : Measure ℝ))) =
      ∫ y : {c : C // c ∉ B} → ℝ,
        ∫ x : {c : C // c ∈ B} → ℝ, F (y, x)
          ∂Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ))
        ∂Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ)) := by
  classical
  rw [(chartSplitEquiv_measurePreserving B).integral_comp' F]
  exact integral_prod F hF

/-- The mass of the completed-square factor is exactly the source normalizer. -/
theorem completedSquare_link_mass (β n m : ℝ)
    (hβ : 0 < β) (hn : 0 < n) :
    (∫ x : ℝ, Real.exp (-(n / (2 * β)) * (x + m) ^ 2)) =
      linkGaussianMass β n := by
  rw [shiftedGaussianIntegral (n / (2 * β)) m]
  unfold linkGaussianMass
  congr 1
  field_simp [ne_of_gt hβ, ne_of_gt hn]

/-- The one-coordinate Gaussian normalizer is positive. -/
theorem linkGaussianMass_pos (β n : ℝ) (hβ : 0 < β) (hn : 0 < n) :
    0 < linkGaussianMass β n := by
  unfold linkGaussianMass
  apply Real.sqrt_pos.2
  positivity

omit [DecidableEq P] in
/-- The selected Gaussian normalizer after integrating the full finite block. -/
theorem completedSquare_block_mass (β : ℝ) (B : Finset C) (s : P → C → ℝ)
    (y : {c : C // c ∉ B} → ℝ) (hβ : 0 < β)
    (hn : ∀ b ∈ B, 0 < linkMass s b) :
    (∫ x : {c : C // c ∈ B} → ℝ,
      ∏ b : {c : C // c ∈ B},
        Real.exp (-(linkMass s b.1 / (2 * β)) *
          (x b + linkOffset s B y b.1 / linkMass s b.1) ^ 2)) =
      ∏ b : {c : C // c ∈ B}, linkGaussianMass β (linkMass s b.1) := by
  classical
  let D := {c : C // c ∈ B}
  let f : D → ℝ → ℝ := fun b z => Real.exp (-(linkMass s b.1 / (2 * β)) *
    (z + linkOffset s B y b.1 / linkMass s b.1) ^ 2)
  calc
    (∫ x : {c : C // c ∈ B} → ℝ,
        ∏ b : {c : C // c ∈ B},
          Real.exp (-(linkMass s b.1 / (2 * β)) *
            (x b + linkOffset s B y b.1 / linkMass s b.1) ^ 2)) =
        ∏ b : {c : C // c ∈ B},
          ∫ z : ℝ, Real.exp (-(linkMass s b.1 / (2 * β)) *
            (z + linkOffset s B y b.1 / linkMass s b.1) ^ 2) := by
          simpa [D, f] using integral_fintype_prod_volume_eq_prod f
    _ = ∏ b : {c : C // c ∈ B}, linkGaussianMass β (linkMass s b.1) := by
          apply Finset.prod_congr rfl
          intro b hb
          exact completedSquare_link_mass β (linkMass s b.1)
            (linkOffset s B y b.1 / linkMass s b.1) hβ (hn b.1 b.2)

omit [DecidableEq P] in
/-- The selected conditional density has total mass one. -/
theorem selectedConditionalWeight_integral (β : ℝ) (B : Finset C)
    (s : P → C → ℝ) (y : {c : C // c ∉ B} → ℝ) (hβ : 0 < β)
    (hn : ∀ b ∈ B, 0 < linkMass s b) :
    (∫ x : {c : C // c ∈ B} → ℝ, selectedConditionalWeight β s B y x) = 1 := by
  classical
  let mass : ℝ := ∏ b : {c : C // c ∈ B}, linkGaussianMass β (linkMass s b.1)
  let gauss : ({c : C // c ∈ B} → ℝ) → ℝ := fun x =>
    ∏ b : {c : C // c ∈ B},
      Real.exp (-(linkMass s b.1 / (2 * β)) *
        (x b + linkOffset s B y b.1 / linkMass s b.1) ^ 2)
  have hpos : 0 < mass := by
    apply Finset.prod_pos
    intro b hb
    exact linkGaussianMass_pos β (linkMass s b.1) hβ (hn b.1 b.2)
  have hfun : selectedConditionalWeight β s B y = fun x => mass⁻¹ * gauss x := by
    funext x
    simp [selectedConditionalWeight, mass, gauss, div_eq_mul_inv, mul_comm]
  rw [hfun, integral_const_mul, completedSquare_block_mass β B s y hβ hn]
  dsimp [mass]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

/-- The conditional mean in a selected coordinate, with the sign fixed by the positive curl
quadratic action. -/
noncomputable def selectedMean (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (b : {c : C // c ∈ B}) : ℝ :=
  -linkOffset s B y b.1 / linkMass s b.1

/-- Pairing of a full chart field with a link functional. -/
def chartPairing (f x : C → ℝ) : ℝ := ∑ c : C, f c * x c

/-- The retained observable after integrating out selected coordinates, as in one-link renormalization. -/
noncomputable def renormalizedFunctional (s : P → C → ℝ) (B : Finset C)
    (f : C → ℝ) (y : {c : C // c ∉ B} → ℝ) : ℝ :=
  chartPairing f (assemble B y (selectedMean s B y))

/-- The local covariance pairing on the selected set belonging to current `i`. -/
noncomputable def selectedCovariancePairing (s : P → C → ℝ) (Bᵢ : Finset C)
    (τ ρ : C → ℝ) : ℝ :=
  ∑ b ∈ Bᵢ, τ b * ρ b / linkMass s b

/-- The common tilt prefactor `c_B(t,τ)` from one-link renormalization. -/
noncomputable def chartTiltConstant (β t : ℝ) (s : P → C → ℝ) (B : Finset C)
    (τ : C → ℝ) : ℝ :=
  Real.exp (β * t ^ 2 / 2 * ∑ b ∈ B, τ b ^ 2 / linkMass s b)

/-- The one-link renormalization renormalized activity for a selected current. -/
noncomputable def renormalizedActivity (β K : ℝ) (s : P → C → ℝ)
    (Bᵢ : Finset C) (ρ : C → ℝ) : ℝ :=
  K * Real.exp (-(β / 2) * ∑ b ∈ Bᵢ, ρ b ^ 2 / linkMass s b)

/-- The local phase increment in one-link renormalization. -/
noncomputable def chartTiltPhase (β t : ℝ) (s : P → C → ℝ)
    (Bᵢ : Finset C) (τ ρ : C → ℝ) : ℝ :=
  β * t * selectedCovariancePairing s Bᵢ τ ρ

omit [Fintype C] [DecidableEq C] [DecidableEq P] in
/-- The common tilt prefactor is one at zero tilt. -/
theorem chartTiltConstant_zero (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (τ : C → ℝ) : chartTiltConstant β 0 s B τ = 1 := by
  simp [chartTiltConstant]

omit [Fintype C] [DecidableEq C] [DecidableEq P] in
/-- The extra local phase vanishes at zero tilt. -/
theorem chartTiltPhase_zero (β : ℝ) (s : P → C → ℝ)
    (Bᵢ : Finset C) (τ ρ : C → ℝ) : chartTiltPhase β 0 s Bᵢ τ ρ = 0 := by
  simp [chartTiltPhase]

omit [Fintype C] [DecidableEq C] [DecidableEq P] in
/-- The absolute-value activity estimate in one-link renormalization, with equality for nonnegative activity. -/
theorem renormalizedActivity_le_abs (β K : ℝ) (s : P → C → ℝ)
    (Bᵢ : Finset C) (ρ : C → ℝ) :
    renormalizedActivity β K s Bᵢ ρ ≤
      |K| * Real.exp (-(β / 2) * ∑ b ∈ Bᵢ, ρ b ^ 2 / linkMass s b) := by
  unfold renormalizedActivity
  exact mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_nonneg _)

omit [Fintype C] [DecidableEq C] [DecidableEq P] in
theorem renormalizedActivity_eq_abs_of_nonneg (β K : ℝ) (s : P → C → ℝ)
    (Bᵢ : Finset C) (ρ : C → ℝ) (hK : 0 ≤ K) :
    renormalizedActivity β K s Bᵢ ρ =
      |K| * Real.exp (-(β / 2) * ∑ b ∈ Bᵢ, ρ b ^ 2 / linkMass s b) := by
  rw [renormalizedActivity, abs_of_nonneg hK]

omit [DecidableEq P] in
/-- Pointwise disintegration of the literal chart density. The right-hand side is the reduced
marginal density times the normalized conditional density, so arbitrary explicit observable
factors may be multiplied into both sides before integrating over the selected coordinates. -/
theorem chartWeight_factorization (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (x : {c : C // c ∈ B} → ℝ)
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b) :
    chartWeight β s (assemble B y x) =
      reducedWeight β s B y * selectedConditionalWeight β s B y x := by
  classical
  rw [chartWeight, curlEnergy_eq_reducedEnergy_add_squares s B y x hsep hn]
  unfold reducedWeight selectedConditionalWeight
  have hsum :
      -(1 / (2 * β)) *
          (reducedEnergy s B y +
            ∑ b ∈ B, linkMass s b *
              (selectedField B x b + linkOffset s B y b / linkMass s b) ^ 2) =
        -(1 / (2 * β)) * reducedEnergy s B y +
          ∑ b ∈ B,
            -(linkMass s b / (2 * β)) *
              (selectedField B x b + linkOffset s B y b / linkMass s b) ^ 2 := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hexp :
      (∏ b ∈ B, Real.exp (-(linkMass s b / (2 * β)) *
        (selectedField B x b + linkOffset s B y b / linkMass s b) ^ 2)) =
        ∏ b : {c : C // c ∈ B}, Real.exp (-(linkMass s b.1 / (2 * β)) *
          (x b + linkOffset s B y b.1 / linkMass s b.1) ^ 2) := by
    rw [← Finset.prod_attach]
    rw [Finset.attach_eq_univ]
    apply Finset.prod_congr ?_ ?_
    · ext b
      simp
    · intro b hb
      simp [selectedField]
  rw [hsum, Real.exp_add, Real.exp_sum, hexp]
  have hmass :
      (∏ b : {c : C // c ∈ B}, linkGaussianMass β (linkMass s b.1)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro b _
    exact linkGaussianMass_pos β (linkMass s b.1) hβ (hn b.1 b.2)
  field_simp [hmass]

omit [DecidableEq P] in
/-- Integrating out selected coordinates at fixed retained coordinates. The identity includes an
arbitrary explicit integrand, and the coefficient is exactly the reduced marginal density. -/
theorem conditionalChartIntegral (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (y : {c : C // c ∉ B} → ℝ) (F : ({c : C // c ∈ B} → ℝ) → ℝ)
    (μ : Measure ({c : C // c ∈ B} → ℝ)) (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b) :
    (∫ x, chartWeight β s (assemble B y x) * F x ∂μ) =
      reducedWeight β s B y *
        (∫ x, selectedConditionalWeight β s B y x * F x ∂μ) := by
  have hfun : (fun x => chartWeight β s (assemble B y x) * F x) =
      fun x => reducedWeight β s B y * (selectedConditionalWeight β s B y x * F x) := by
    funext x
    rw [chartWeight_factorization β s B y x hβ hsep hn]
    ring
  rw [hfun, integral_const_mul]

omit [DecidableEq P] in
/-- Fubini plus the conditional Gaussian calculation, on the requested measurable equivalence
`C → ℝ ≃ᵐ (U → ℝ) × (B → ℝ)`. `F` can include the tilt and all current factors. -/
theorem chartDensity_fubini (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (F : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) → ℝ)
    (hF : Integrable (fun z =>
      chartWeight β s (assemble B z.1 z.2) * F z)
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))))
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b) :
    (∫ x : C → ℝ, chartWeight β s x * F (chartSplitEquiv B x)
      ∂Measure.pi (fun _ : C => (volume : Measure ℝ))) =
      ∫ y : {c : C // c ∉ B} → ℝ,
        reducedWeight β s B y *
          (∫ x : {c : C // c ∈ B} → ℝ,
            selectedConditionalWeight β s B y x * F (y, x)
            ∂Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))
        ∂Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ)) := by
  classical
  let G : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) → ℝ := fun z =>
    chartWeight β s (assemble B z.1 z.2) * F z
  have hG : Integrable G
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))) := by
    simpa [G] using hF
  calc
    (∫ x : C → ℝ, chartWeight β s x * F (chartSplitEquiv B x)
        ∂Measure.pi (fun _ : C => (volume : Measure ℝ))) =
      ∫ x : C → ℝ, G (chartSplitEquiv B x)
        ∂Measure.pi (fun _ : C => (volume : Measure ℝ)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          have hchart : assemble B ((chartSplitEquiv B x).1) ((chartSplitEquiv B x).2) = x := by
            rw [← chartSplitEquiv_symm_apply B ((chartSplitEquiv B x).1)
              ((chartSplitEquiv B x).2)]
            exact MeasurableEquiv.symm_apply_apply (chartSplitEquiv B) x
          simp only [G]
          exact congrArg (fun q : ℝ => q * F (chartSplitEquiv B x))
            (congrArg (chartWeight β s) hchart.symm)
    _ = ∫ y : {c : C // c ∉ B} → ℝ,
          ∫ x : {c : C // c ∈ B} → ℝ, G (y, x)
            ∂Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ))
          ∂Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ)) :=
        chartFubini_pi B G hG
    _ = ∫ y : {c : C // c ∉ B} → ℝ,
          reducedWeight β s B y *
            (∫ x : {c : C // c ∈ B} → ℝ,
              selectedConditionalWeight β s B y x * F (y, x)
              ∂Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))
          ∂Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact conditionalChartIntegral β s B y (fun x => F (y, x))
          (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ))) hβ hsep hn


omit [DecidableEq P] in
/-- Fubini for the literal unnormalized chart measure. The reduced measure has density
`reducedWeight`, and the selected conditional density is normalized. -/
theorem chartMeasure_fubini (β : ℝ) (s : P → C → ℝ) (B : Finset C)
    (F : ({c : C // c ∉ B} → ℝ) × ({c : C // c ∈ B} → ℝ) → ℝ)
    (hF : Integrable (fun z => chartWeight β s (assemble B z.1 z.2) * F z)
      ((Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))))
    (hβ : 0 < β)
    (hsep : ∀ p, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0)
    (hn : ∀ b ∈ B, 0 < linkMass s b) :
    (∫ x : C → ℝ, F (chartSplitEquiv B x) ∂chartMeasure β s) =
      ∫ y : {c : C // c ∉ B} → ℝ,
        reducedWeight β s B y *
          (∫ x : {c : C // c ∈ B} → ℝ,
            selectedConditionalWeight β s B y x * F (y, x)
            ∂Measure.pi (fun _ : {c : C // c ∈ B} => (volume : Measure ℝ)))
        ∂Measure.pi (fun _ : {c : C // c ∉ B} => (volume : Measure ℝ)) := by
  rw [chartMeasure_integral_eq]
  rw [volume_pi]
  exact chartDensity_fubini β s B F hF hβ hsep hn


end FroehlichSpencer.FS82.Gaussian.ConditionalGaussian

end
