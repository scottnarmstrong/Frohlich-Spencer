/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.Gauge
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic

/-!
# Theorem D for the full free-boundary Villain measure

The finite-volume power estimate and every-limit-point conclusion transfer from the root-pinned
measure to the full free-boundary Villain measure by the gauge adapter.

This module does not assert
uniqueness of the thermodynamic limit.

`FreeModel.twoPoint_mono_domain` applies to a `FreeModel`: its finite single-site measure on `ℝ`
must carry `HasRealFourier` and `HasEquivKernel` data, its bond weights must satisfy `IsGinibrePair`
for `(w,w)` and `(w,1)`, and its two-point frequency is an integer.

The zero-exterior law here is
on integer-valued heights with `I_β` difference weights and a pinned exterior; its observable has
real frequency `ξ` with `0 < ξ < 1`.

It therefore has neither a current `FreeModel` instance nor
the integer-frequency `twoPoint` form required by that theorem.

In particular, positivity of the
Fourier coefficients of `I_β` and of the pinning factor alone does not establish the required
Ginibre-pair comparisons for the full finite-volume Gibbs weights.

A Ginibre domain comparison
proved directly for the zero-exterior integer-height law and fractional characters, or a proved
reduction to a `FreeModel` integer-harmonic two-point function with all the stated Fourier-kernel
and Ginibre-pair hypotheses, is still needed to deduce convergence.
-/

@[expose] public section

open Filter Topology
open FroehlichSpencer.BKT.VillainDisorder.Dirichlet

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

/-- The full free-boundary Villain disorder expectation in the centered box of radius `R`; zero
is used only when the fixed axial string does not fit. -/
def dirichletFullCenteredDisorder (R n : ℕ) (β ξ : ℝ) (hβ : 0 < β) : ℝ :=
  if hn : n ≤ R then dirichletFullFreeVillainDisorderExpectation R n hn β ξ hβ else 0

/-- Gauge invariance makes the full-measure centered sequence termwise equal to the root-pinned
sequence used in the finite D3 proof. -/
@[simp] theorem dirichletFullCenteredDisorder_eq_rooted
    (R n : ℕ) (β ξ : ℝ) (hβ : 0 < β) :
    dirichletFullCenteredDisorder R n β ξ hβ = dirichletCenteredDisorder R n β ξ hβ := by
  unfold dirichletFullCenteredDisorder dirichletCenteredDisorder
  split_ifs with hn
  · exact dirichletFullFreeVillainDisorderExpectation_eq_rooted R n hn β ξ hβ
  · rfl

/-- The marked Fejér input gives the same power estimate for the full free-boundary Villain measure.
The constants and all finite-volume quantifiers are exactly those of the rooted statement. -/
theorem dirichletFullFreeBox_bound_of_fejerInput
    (hFejer : RootedDirichletFejerGlobalInput) :
    ∃ c : ℝ, 0 < c ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        ∃ β₀ : ℝ, ∃ hβ₀ : 0 < β₀,
          ∀ β : ℝ, ∀ hβlarge : β₀ < β,
            ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
              ∀ n : ℕ, ∀ _hnpos : 1 ≤ n,
                ∃ R₀ : ℕ, n ≤ R₀ ∧
                  ∀ R : ℕ, ∀ _hbuffer : R₀ ≤ R, ∀ hn : n ≤ R,
                    let hβ' : 0 < β := lt_trans hβ₀ hβlarge
                    0 ≤ dirichletFullFreeVillainDisorderExpectation R n hn β ξ hβ' ∧
                    dirichletFullFreeVillainDisorderExpectation R n hn β ξ hβ' ≤
                      2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β)) := by
  simpa only [dirichletFullFreeVillainDisorderExpectation_eq_rooted] using
    rootedDirichletFreeBox_bound_of_fejerInput hFejer

/-- The full free-boundary centered expectations lie in `[-1,1]`; non-fitting values are zero. -/
theorem dirichletFullCenteredDisorder_mem_Icc_one
    (R n : ℕ) (β ξ : ℝ) (hβ : 0 < β) (hnpos : 1 ≤ n) :
    dirichletFullCenteredDisorder R n β ξ hβ ∈ Set.Icc (-1) 1 := by
  simpa only [dirichletFullCenteredDisorder_eq_rooted] using
    dirichletCenteredDisorder_mem_Icc_one R n β ξ hβ hnpos

/-- Full-measure Theorem D: the centered expectations have the FS81 power bound eventually,
admit a convergent subsequence, and every cluster point obeys the same bound. -/
theorem dirichletFullTheoremD_thermodynamicLimit
    (hFejer : RootedDirichletFejerGlobalInput) :
    ∃ c : ℝ, 0 < c ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        ∃ β₀ : ℝ, ∃ _hβ₀ : 0 < β₀,
          ∀ β : ℝ, ∀ hβ : 0 < β, ∀ _hβlarge : β₀ < β,
            ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
              ∀ n : ℕ, ∀ _hnpos : 1 ≤ n,
                (∀ᶠ R in atTop, n ≤ R) ∧
                (∀ R : ℕ, dirichletFullCenteredDisorder R n β ξ hβ ∈ Set.Icc (-1) 1) ∧
                (∀ᶠ R in atTop,
                  dirichletFullCenteredDisorder R n β ξ hβ ∈ Set.Icc 0
                    (2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β)))) ∧
                (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
                  Tendsto (fun k => dirichletFullCenteredDisorder (φ k) n β ξ hβ)
                    atTop (𝓝 ℓ)) ∧
                ∀ ℓ : ℝ,
                  MapClusterPt ℓ atTop (fun R => dirichletFullCenteredDisorder R n β ξ hβ) →
                    ℓ ∈ Set.Icc 0
                      (2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))) := by
  simpa only [dirichletFullCenteredDisorder_eq_rooted] using
    rootedDirichletTheoremD_thermodynamicLimit hFejer

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet
