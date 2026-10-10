/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib
public import FroehlichSpencer.Surface.InfiniteGreenWellDefined
public import FroehlichSpencer.Surface.IDSWellDefined
public import FroehlichSpencer.Surface.T12Lambda
public import FroehlichSpencer.Surface.T12
public import FroehlichSpencer.Surface.Theorem11
public import FroehlichSpencer.Surface.GreenAlmostSure

-- Reset the auxiliary-lemma cache between copied source modules.
-- This preserves generated proof names without changing definitions or assumptions.
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
public section
namespace FroehlichSpencer
theorem _root_.FSComparator.FS83.existsUnique_squareSummable_greenSolution (ν : ℕ) (hν : 0 < ν) (z : ℂ)
    (hz : z.im ≠ 0) (v : Site ν → ℝ) (y : Site ν) :
    ∃! ψ : Site ν → ℂ,
      Summable (fun x => ‖ψ x‖ ^ 2) ∧
      ∀ x, -(latticeLaplacian ν ψ x) + ((v x : ℂ) - z) * ψ x = if x = y then 1 else 0 :=
  by exact FroehlichSpencer.existsUnique_squareSummable_greenSolution ν hν z hz v y
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer
theorem _root_.FSComparator.FS83.existsUnique_integratedDensityOfStates (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (δ : ℝ) (hlaw : HasBoundedDensity law δ) :
    ∃! N : ℝ → ℝ,
      ∀ᵐ v ∂configurationMeasure ν law, ∀ E : ℝ,
        Filter.Tendsto
          (fun L : ℕ =>
            (finiteEigenvalueCount ν
              (Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ))
              E v : ℝ) /
            ((Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ))
          Filter.atTop (nhds (N E)) :=
  by exact FroehlichSpencer.existsUnique_integratedDensityOfStates ν hν law δ hlaw
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer
theorem _root_.FSComparator.FS83.finiteVolumeGreen_probability_bound (ν : ℕ) (hν : 0 < ν) :
    ∃ (largeDisorder : ℝ → ℝ → ℝ)
      (highEnergy : ℝ → ℝ → ℝ → ℝ)
      (Kp : ℝ → ℝ)
      (Kgauss : ℝ → ℝ → ℝ → ℝ),
      (∀ p m, 0 < m → 0 < p → 0 < largeDisorder p m) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 < highEnergy γ p m) ∧
      (∀ p, 0 < p → 0 ≤ Kp p) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 ≤ Kgauss γ p m) ∧
      ∀ (m p : ℝ), 0 < m → 0 < p →
        ∀ (law : Measure ℝ), [MeasureTheory.IsProbabilityMeasure law] →
        ∀ (E : ℝ) (Λ : Finset (Site ν)) (x : Site ν),
          (h0 : (0 : Site ν) ∈ Λ) → (hx : x ∈ Λ) →
        ∀ (N : ℝ), 0 < N →
          let S : Set (Configuration ν) :=
            {v | ∀ ε : ℝ, ∀ hε : ε ≠ 0,
              ‖finiteGreen ν Λ v E ε hε ⟨0, h0⟩ ⟨x, hx⟩‖ ≤
                Real.exp (m * (N - latticeLength ν x))}
          ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder p m) →
              MeasurableSet S ∧
                ENNReal.ofReal (1 - Kp p / Real.rpow N p) ≤ configurationMeasure ν law S) ∧
            (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
              highEnergy γ p m ≤ |E - 2 * (ν : ℝ)| →
              MeasurableSet S ∧
                ENNReal.ofReal (1 - Kgauss γ p m / Real.rpow N p) ≤
                  configurationMeasure ν law S) :=
  by exact FroehlichSpencer.finiteVolumeGreen_probability_bound ν hν
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer
theorem _root_.FSComparator.FS83.green_probability_bound (ν : ℕ) (hν : 0 < ν) :
    ∃ (largeDisorder : ℝ → ℝ → ℝ)
      (highEnergy : ℝ → ℝ → ℝ → ℝ)
      (Kp : ℝ → ℝ)
      (Kgauss : ℝ → ℝ → ℝ → ℝ),
      (∀ p m, 0 < m → 0 < p → 0 < largeDisorder p m) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 < highEnergy γ p m) ∧
      (∀ p, 0 < p → 0 ≤ Kp p) ∧
      (∀ γ p m, 0 < γ → 0 < m → 0 < p → 0 ≤ Kgauss γ p m) ∧
      ∀ (m p : ℝ), 0 < m → 0 < p →
        ∀ (law : Measure ℝ), [MeasureTheory.IsProbabilityMeasure law] →
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
                    configurationMeasure ν law S) :=
  by exact FroehlichSpencer.green_probability_bound ν hν
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
public section
open MeasureTheory
namespace FroehlichSpencer
theorem _root_.FSComparator.FS83.theorem_1_1 (ν : ℕ) (hν : 0 < ν) :
    ∃ largeDisorder : ℝ, 0 < largeDisorder ∧
      ∃ highEnergy : {γ : ℝ // 0 < γ} → ℝ,
        (∀ γ : {γ : ℝ // 0 < γ}, 0 < highEnergy γ) ∧
        (∀ (law : Measure ℝ) [MeasureTheory.IsProbabilityMeasure law]
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
                (Real.sqrt (2 * Real.pi * γ)) (has_bounded_density_gaussian_law γ hγ))
              r E →
            0 < r →
            ∃! D : ℝ,
              is_diffusion_coefficient ν hν (gaussianLaw γ hγ) E r D ∧ D = 0) :=
  by exact FroehlichSpencer.theorem_1_1 ν hν
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer
theorem _root_.FSComparator.FS83.green_almostSure_decay (ν : ℕ) (hν : 0 < ν) :
    ∃ (largeDisorder : ℝ → ℝ) (highEnergy : ℝ → ℝ → ℝ),
      (∀ m, 0 < m → 0 < largeDisorder m) ∧
      (∀ γ m, 0 < γ → 0 < m → 0 < highEnergy γ m) ∧
      ∀ (m : ℝ), 0 < m →
        ∀ (law : Measure ℝ), [MeasureTheory.IsProbabilityMeasure law] →
        ∀ (E : ℝ),
          let S : Set (Configuration ν) :=
            {v | ∃ R : ℝ, ∀ x : Site ν, R ≤ latticeLength ν x →
              ∀ ε : ℝ, ∀ hε : ε ≠ 0,
                ‖greenFunction ν hν
                    ((E : ℂ) + (ε : ℂ) * Complex.I) (by simpa using hε)
                    v (0 : Site ν) x‖ ≤
                  Real.exp (-(m / 2) * latticeLength ν x)}
          ((∃ δ : ℝ, HasBoundedDensity law δ ∧ δ⁻¹ ≤ largeDisorder m) →
              MeasurableSet S ∧ configurationMeasure ν law S = 1) ∧
            (∀ (γ : ℝ) (hγ : 0 < γ), law = gaussianLaw γ hγ →
              highEnergy γ m ≤ |E - 2 * (ν : ℝ)| →
              MeasurableSet S ∧ configurationMeasure ν law S = 1) :=
  by exact FroehlichSpencer.green_almostSure_decay ν hν
end FroehlichSpencer
end
