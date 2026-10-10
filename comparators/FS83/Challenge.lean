/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib

-- Reset the auxiliary-lemma cache between copied source modules.
-- This preserves generated proof names without changing definitions or assumptions.
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
abbrev Site (ν : ℕ) := Fin ν → ℤ
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
@[expose] def latticeLaplacian (ν : ℕ) (f : Site ν → ℂ) (x : Site ν) : ℂ :=
  ∑ k : Fin ν,
    ((f (x + Pi.single k (1 : ℤ)) - f x) +
      (f (x - Pi.single k (1 : ℤ)) - f x))
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
theorem existsUnique_squareSummable_greenSolution (ν : ℕ) (hν : 0 < ν) (z : ℂ)
    (hz : z.im ≠ 0) (v : Site ν → ℝ) (y : Site ν) :
    ∃! ψ : Site ν → ℂ,
      Summable (fun x => ‖ψ x‖ ^ 2) ∧
      ∀ x, -(latticeLaplacian ν ψ x) + ((v x : ℂ) - z) * ψ x = if x = y then 1 else 0 := by sorry
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer
@[expose] def HasBoundedDensity (law : Measure ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ g : ℝ → ENNReal,
    Measurable g ∧
    law = volume.withDensity g ∧
    ∀ t, g t ≤ ENNReal.ofReal (δ⁻¹)
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
abbrev Configuration (ν : ℕ) := Site ν → ℝ
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer
@[expose] noncomputable def configurationMeasure (ν : ℕ) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] : Measure (Configuration ν) :=
  Measure.infinitePi (fun _ : Site ν => law)
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open scoped Matrix
namespace FroehlichSpencer
@[expose] noncomputable def dirichletLaplacian (ν : ℕ) (Λ : Finset (Site ν)) :
    Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ := by
  classical
  let forward : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ := fun x y =>
    ∑ k : Fin ν, if y.1 = x.1 + Pi.single k (1 : ℤ) then 1 else 0
  exact
    forward + forwardᴴ - ((2 * ν : ℕ) : ℂ) •
      (1 : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ)
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped Matrix
@[expose] public section
namespace FroehlichSpencer
@[expose] noncomputable def hamiltonian (ν : ℕ) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ := by
  classical
  exact -dirichletLaplacian ν Λ + Matrix.diagonal (fun x => (v x.1 : ℂ))
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped Matrix
@[expose] public section
namespace FroehlichSpencer
theorem hamiltonian_isHermitian (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) :
    (hamiltonian ν Λ v).IsHermitian := by sorry
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
@[expose] noncomputable def finiteEigenvalueCount (ν : ℕ) (Λ : Finset (Site ν))
    (E : ℝ) (v : Site ν → ℝ) : ℕ := by
  classical
  exact Finset.card (Finset.univ.filter fun x : {x : Site ν // x ∈ Λ} =>
    (hamiltonian_isHermitian ν Λ v).eigenvalues x ≤ E)
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer
theorem existsUnique_integratedDensityOfStates (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (δ : ℝ) (hlaw : HasBoundedDensity law δ) :
    ∃! N : ℝ → ℝ,
      ∀ᵐ v ∂configurationMeasure ν law, ∀ E : ℝ,
        Filter.Tendsto
          (fun L : ℕ =>
            (finiteEigenvalueCount ν
              (Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ))
              E v : ℝ) /
            ((Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ))
          Filter.atTop (nhds (N E)) := by sorry
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped Matrix
@[expose] public section
namespace FroehlichSpencer
@[expose] noncomputable def finiteGreen (ν : ℕ) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) (E ε : ℝ) (_hε : ε ≠ 0)
    (x y : {x : Site ν // x ∈ Λ}) : ℂ :=
  ((hamiltonian ν Λ v - ((E : ℂ) + (ε : ℂ) * Complex.I) •
      (1 : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ))⁻¹) x y
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
@[expose] public section
namespace FroehlichSpencer
@[expose] noncomputable def gaussianLaw (γ : ℝ) (hγ : 0 < γ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 ⟨γ, le_of_lt hγ⟩
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
@[expose] noncomputable def latticeLength (ν : ℕ) (x : Site ν) : ℝ :=
  Real.sqrt (∑ i : Fin ν, (x i : ℝ) ^ 2)
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
@[expose] noncomputable def greenFunction (ν : ℕ) (hν : 0 < ν) (z : ℂ)
    (hz : z.im ≠ 0) (v : Site ν → ℝ) (x y : Site ν) : ℂ :=
  (Classical.choose
    (existsUnique_squareSummable_greenSolution ν hν z hz v y).exists) x
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
theorem greenFunction_spec (ν : ℕ) (hν : 0 < ν) (z : ℂ) (hz : z.im ≠ 0)
    (v : Site ν → ℝ) (y : Site ν) :
    ∀ ψ : Site ν → ℂ,
      (Summable (fun x => ‖ψ x‖ ^ 2) ∧
        ∀ x, -(latticeLaplacian ν ψ x) + ((v x : ℂ) - z) * ψ x =
          if x = y then 1 else 0) ↔
      ψ = fun x => greenFunction ν hν z hz v x y := by sorry
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
theorem has_bounded_density_gaussian_law (γ : ℝ) (hγ : 0 < γ) :
    HasBoundedDensity (gaussianLaw γ hγ) (Real.sqrt (2 * Real.pi * γ)) := by sorry
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
namespace FroehlichSpencer
instance instIsProbabilityMeasureFSGaussianLaw (γ : ℝ) (hγ : 0 < γ) :
    MeasureTheory.IsProbabilityMeasure (gaussianLaw γ hγ) := by
  change MeasureTheory.IsProbabilityMeasure
    (ProbabilityTheory.gaussianReal 0 ⟨γ, le_of_lt hγ⟩)
  exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
    ⟨γ, le_of_lt hγ⟩
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory
namespace FroehlichSpencer
@[expose] noncomputable def integratedDensityOfStates (ν : ℕ) (hν : 0 < ν)
    (law : Measure ℝ) [MeasureTheory.IsProbabilityMeasure law] (δ : ℝ)
    (hlaw : HasBoundedDensity law δ) : ℝ → ℝ :=
  Classical.choose (existsUnique_integratedDensityOfStates ν hν law δ hlaw).exists
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory
namespace FroehlichSpencer
theorem integratedDensityOfStates_spec (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (δ : ℝ) (hlaw : HasBoundedDensity law δ) :
    (∀ᵐ v ∂configurationMeasure ν law, ∀ E : ℝ,
      Filter.Tendsto
        (fun L : ℕ =>
          (finiteEigenvalueCount ν
            (Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)) E v : ℝ) /
            ((Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ))
        Filter.atTop (nhds (integratedDensityOfStates ν hν law δ hlaw E))) ∧
      ∀ N' : ℝ → ℝ,
        (∀ᵐ v ∂configurationMeasure ν law, ∀ E : ℝ,
          Filter.Tendsto
            (fun L : ℕ =>
              (finiteEigenvalueCount ν
                (Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)) E v : ℝ) /
                ((Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ))
            Filter.atTop (nhds (N' E))) →
        N' = integratedDensityOfStates ν hν law δ hlaw := by sorry
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory
namespace FroehlichSpencer
@[expose] noncomputable def kuboQuantity (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (E : ℝ) (ε : {ε : ℝ // ε ≠ 0}) : ENNReal :=
  ENNReal.ofReal (2 * ε.1 ^ 2 / (Real.pi * (ν : ℝ))) *
    ∑' x : Site ν,
      ENNReal.ofReal ((latticeLength ν x) ^ 2) *
        ∫⁻ v : Configuration ν,
          ENNReal.ofReal
            (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
              (by simpa using ε.2) v 0 x‖ ^ 2)
          ∂configurationMeasure ν law
end FroehlichSpencer
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open MeasureTheory Topology
namespace FroehlichSpencer
@[expose] def is_diffusion_coefficient (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (E r D : ℝ) : Prop :=
  0 < r ∧ 0 ≤ D ∧
    Filter.Tendsto
      (fun ε : {ε : ℝ // ε ≠ 0} => kuboQuantity ν hν law E ε)
      (Filter.comap Subtype.val (𝓝[>] (0 : ℝ)))
      (𝓝 (ENNReal.ofReal (r * D)))
end FroehlichSpencer
end


run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
public section
namespace FroehlichSpencer
theorem _root_.FSComparator.FS83.existsUnique_squareSummable_greenSolution (ν : ℕ) (hν : 0 < ν) (z : ℂ)
    (hz : z.im ≠ 0) (v : Site ν → ℝ) (y : Site ν) :
    ∃! ψ : Site ν → ℂ,
      Summable (fun x => ‖ψ x‖ ^ 2) ∧
      ∀ x, -(latticeLaplacian ν ψ x) + ((v x : ℂ) - z) * ψ x = if x = y then 1 else 0 :=
  by sorry
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
  by sorry
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
  by sorry
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
  by sorry
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
  by sorry
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
  by sorry
end FroehlichSpencer
end
