/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.NonsummabilityPrimalLimit

/-!
Containment and C4 orientation gates for the FS82 §2.11 primal add-on.

The containment argument is a finite-union consequence of cube exhaustion.
-/

@[expose] public section

open FroehlichSpencer.FS82.Infinite.Fourier

namespace FroehlichSpencer.FS82.Infinite.Nonsummability

/-- Every fixed finite averaging box and displacement fit in all sufficiently
large cubes. No value is assigned to an out-of-cube face. -/
theorem primalPackage_validCube_eventually (n : ℕ) (d : LatticePoint) :
    ∃ N₀, ∀ N ≥ N₀, primalFølnerValidCube N n d := by
  classical
  let P : Finset GlobalIntegerPlaquette := (latticeShiftBox n).biUnion fun a =>
    spectralPairPlaquettes (latticeShiftPoint a) (d + latticeShiftPoint a)
  obtain ⟨N₀, hN₀⟩ := exists_cube_threshold_for_plaquettes P
  refine ⟨N₀, ?_⟩
  intro N hN a ha p hp
  exact hN₀ N hN p (Finset.mem_biUnion.mpr ⟨a, ha, hp⟩)


end FroehlichSpencer.FS82.Infinite.Nonsummability
end
