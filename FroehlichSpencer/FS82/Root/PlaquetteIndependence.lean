/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.AdaptiveTree
import all FroehlichSpencer.FS82.Currents.AdaptiveTree

/-!
# plaquette independence, unfolded

`Currents.AdaptiveTree.PlaquetteIndependent` is not exposed outside its module.

The root needs
both directions of its definition: to prove it for the selected links of a separated family of
currents (a union of colour classes of different currents), and to read off the separation of
selected chords.

This module imports the private scope of `Currents.AdaptiveTree` and states the
definition as an `Iff`.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents.AdaptiveTree
open FroehlichSpencer.FS82.Currents.SourceLinkColoring

/-- The definition of plaquette independence, for use outside its module. -/
theorem plaquetteIndependent_iff {B : SourceBox} (S : Finset (SourceDualOneCells B)) :
    PlaquetteIndependent S ↔
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ¬ ∃ p : SourceDualTwoCells B, linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p :=
  Iff.rfl

end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
