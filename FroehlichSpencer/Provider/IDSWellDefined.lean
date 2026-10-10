/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Filter.AtTopBot.Basic
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.FiniteEigenvalueCount
public import FroehlichSpencer.IDS.Assembly
import FroehlichSpencer.Infra.Stieltjes.Existence
import FroehlichSpencer.Infra.Stieltjes.Lipschitz
import FroehlichSpencer.Infra.Stieltjes.Continuity
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.existsUnique_integratedDensityOfStates`

This module contains `FroehlichSpencer.Provider.existsUnique_integratedDensityOfStates`, the
proof of the statement `FroehlichSpencer.existsUnique_integratedDensityOfStates` (file
`FroehlichSpencer/Surface/IDSWellDefined.lean`).

Proof: the averaged measures `νs L = E[idsMeasure (cube L) v]` are probability measures whose
Stieltjes transforms converge to `E[G(z; 0, 0)]`; Prokhorov gives a limit probability measure `μ`,
which has no atoms by the Wegner bound.

Almost surely the transforms of `idsMeasure (cube L) v`
converge on a countable dense subset of the upper half-plane, hence the distribution functions
converge at every `E`; `N E = μ (-∞, E]`.

Uniqueness: two almost sure sets intersect.
-/

@[expose] public section

namespace FroehlichSpencer.Provider

open MeasureTheory ProbabilityTheory Complex Filter Topology Set FroehlichSpencer.IDS

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
          Filter.atTop (nhds (N E)) := by
  set P := configurationMeasure ν law with hP
  set s : ℂ → ℂ := fun z => ∫ w, latticeGreen ν z w 0 0 ∂P with hs
  have : IsProbabilityMeasure P := by rw [hP]; unfold configurationMeasure; infer_instance
  have hne : ∀ L : ℕ, (Infra.cube ν L).Nonempty := fun L =>
    Finset.card_pos.1 (Infra.card_cube_pos ν L)
  have hprob : ∀ L v, IsProbabilityMeasure (idsMeasure ν (Infra.cube ν L) v) := fun L v =>
    isProbabilityMeasure_idsMeasure ν (hne L) v
  have hκ : ∀ L v, (idsKernel ν (Infra.cube ν L) v).real univ = 1 := fun L v => by
    rw [idsKernel_apply]
    have := hprob L v
    simp
  let νs : ℕ → Measure ℝ := fun L => P.bind (idsKernel ν (Infra.cube ν L))
  have hνprob : ∀ L, IsProbabilityMeasure (νs L) := fun L => by
    refine ⟨?_⟩
    show (P.bind (idsKernel ν (Infra.cube ν L))) univ = 1
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    have : ∀ v, idsKernel ν (Infra.cube ν L) v univ = 1 := fun v => by
      rw [idsKernel_apply]
      have := hprob L v
      exact measure_univ
    simp [this]
  have hνS : ∀ z : ℂ, 0 < z.im →
      Tendsto (fun L => Infra.stieltjes (νs L) z) atTop (𝓝 (s z)) := by
    intro z hz
    refine Infra.tendsto_stieltjes_bind_of_ae_tendsto P (M := 1) (fun n ω => ?_) hz ?_
    · exact (hκ n ω).le
    · filter_upwards [ae_tendsto_stieltjes_idsMeasure hν law hz] with v hv
      simpa only [idsKernel_apply] using hv
  obtain ⟨μ, hμprob, hμS⟩ := Infra.exists_isProbabilityMeasure_stieltjes_eq hνS
    (tendsto_mul_integral_latticeGreen ν law)
  have hatom : ∀ E, μ {E} = 0 := fun E =>
    Infra.measure_singleton_eq_zero_of_tendsto_stieltjes (μs := νs) (M := 1)
      (fun n => by have := hνprob n; simp)
      (D := {z | 0 < z.im}) subset_closure
      (fun z hz => by rw [hμS z hz]; exact hνS z hz)
      (ρ := δ⁻¹) (fun n a b hab => measureReal_bind_idsKernel_Ioc_le ν _ law hlaw hab) E
  obtain ⟨D, hDc, hDsub, hDd⟩ := Infra.exists_countable_subset_upperHalfPlane_dense
  have hae : ∀ᵐ v ∂P, ∀ z ∈ D, Tendsto
      (fun L => Infra.stieltjes (idsMeasure ν (Infra.cube ν L) v) z) atTop (𝓝 (s z)) := by
    rw [ae_ball_iff hDc]
    exact fun z hz => ae_tendsto_stieltjes_idsMeasure hν law (hDsub hz)
  have hlim : ∀ᵐ v ∂P, ∀ E : ℝ, Tendsto
      (fun L : ℕ => (finiteEigenvalueCount ν
        (Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)) E v : ℝ) /
        ((Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ))
      atTop (𝓝 (μ.real (Set.Iic E))) := by
    filter_upwards [hae] with v hv E
    have := Infra.tendsto_measure_Iic_of_tendsto_stieltjes
      (μs := fun L => idsMeasure ν (Infra.cube ν L) v)
      (μ := μ) hDd (fun z hz => by rw [hμS z (hDsub hz)]; exact hv z hz)
      (by
        have h1 : ∀ L, (idsMeasure ν (Infra.cube ν L) v).real univ = 1 := fun L => by
          have := hprob L v
          simp
        have h2 : μ.real univ = 1 := by simp
        simp only [h1, h2]
        exact tendsto_const_nhds) (hatom E)
    simpa only [idsMeasure_real_Iic, ← idsCube_eq_cube] using this
  refine ⟨fun E => μ.real (Set.Iic E), hlim, ?_⟩
  intro N hN
  obtain ⟨v, hv1, hv2⟩ := (hN.and hlim).exists
  funext E
  exact tendsto_nhds_unique (hv1 E) (hv2 E)

end FroehlichSpencer.Provider
