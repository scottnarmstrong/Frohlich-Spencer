/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Surface.RealLatticeBoundary
public import FroehlichSpencer.FS82.Infinite.GlobalVariational
public import FroehlichSpencer.FS82.Gaussian.LatticePath
import Mathlib.Tactic

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceInfiniteProof

private theorem surface_boundary_single (c : FroehlichSpencer.FS82.Cubical.LatticeCell 4) :
    FroehlichSpencer.FS82.Surface.realLatticeBoundary (Finsupp.single c (1 : ℝ)) =
      FroehlichSpencer.FS82.Infinite.globalBoundary (Finsupp.single c 1) := by
  rw [FroehlichSpencer.FS82.Infinite.globalBoundary,
    FroehlichSpencer.FS82.Gaussian.realLatticeBoundary_basis]
  simp only [FroehlichSpencer.FS82.Surface.realLatticeBoundary,
    FroehlichSpencer.FS82.Surface.realifyLatticeLinearMap,
    FroehlichSpencer.FS82.Surface.latticeBoundary,
    FroehlichSpencer.FS82.Surface.latticeBasis,
    Finsupp.linearCombination_single, one_smul]
  rfl

theorem surface_boundary_eq_global
    (q : FroehlichSpencer.FS82.Surface.RealLatticeChain) :
    FroehlichSpencer.FS82.Surface.realLatticeBoundary q =
      FroehlichSpencer.FS82.Infinite.globalBoundary q := by
  have hbasis (c : FroehlichSpencer.FS82.Cubical.LatticeCell 4) :
      FroehlichSpencer.FS82.Surface.realLatticeBoundary (Finsupp.single c (1 : ℝ)) =
        FroehlichSpencer.FS82.Infinite.globalBoundary (Finsupp.single c 1) :=
    surface_boundary_single c
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => rw [map_add, map_add, hq, hr]
  | single c a =>
      have hs : Finsupp.single c a = a • Finsupp.single c (1 : ℝ) := by
        ext x
        by_cases hx : x = c <;> simp [hx]
      rw [hs, map_smul, map_smul, hbasis]

end FroehlichSpencer.FS82.SurfaceInfiniteProof

end
