/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Candidate rooted finite-volume Gaussian free field density

The pointwise density in KP (1.3), p. 2, with the interval at the selected
root used to remove the constant mode. The normalized probability measure is
defined only after integrability and positivity of its partition function are
established.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

open Multigraph

variable {V : Type u} {E : Type v}

/-- The root window `φ(v) ∈ [-π,π)`, as in the finite-volume density in KP
(1.3), p. 2. -/
def gffRootWindow (root : V) : Set (V → ℝ) :=
  {φ | φ root ∈ Set.Ico (-Real.pi) Real.pi}

/-- The unnormalized KP rooted Gaussian free field density, with each edge
counted once; KP (1.3), p. 2. -/
noncomputable def gffDensity (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (β : ℝ) (root : V) (φ : V → ℝ) : ℝ :=
  Set.indicator (gffRootWindow root)
    (fun ψ => Real.exp (-(β / 2) * G.energy ψ)) φ

/-- On the root window, the candidate density is exactly the KP exponential
weight from (1.3), p. 2. -/
theorem gffDensity_of_root_mem (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (β : ℝ) (root : V) (φ : V → ℝ)
    (hφ : φ root ∈ Set.Ico (-Real.pi) Real.pi) :
    gffDensity G β root φ = Real.exp (-(β / 2) * G.energy φ) := by
  have hw : φ ∈ gffRootWindow root := hφ
  change Set.indicator (gffRootWindow root)
      (fun ψ : V → ℝ => Real.exp (-(β / 2) * G.energy ψ)) φ = _
  rw [Set.indicator_of_mem hw]

/-- Outside the root window, the candidate density vanishes. -/
theorem gffDensity_of_root_not_mem (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (β : ℝ) (root : V) (φ : V → ℝ)
    (hφ : φ root ∉ Set.Ico (-Real.pi) Real.pi) :
    gffDensity G β root φ = 0 := by
  have hw : φ ∉ gffRootWindow root := hφ
  change Set.indicator (gffRootWindow root)
      (fun ψ : V → ℝ => Real.exp (-(β / 2) * G.energy ψ)) φ = _
  rw [Set.indicator_of_notMem hw]

end FroehlichSpencer.BKT
