/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.RealLatticeChain
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquetteAxes
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquette
public import FroehlichSpencer.FS82.SurfaceInfinite.CellDegree
public import FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquetteField

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

noncomputable def fillingPlaquetteEmbedding (σ : GlobalPlaquetteField) :
    {c : LatticeCell // c ∈ σ.1.support} ↪ GlobalPlaquette where
  toFun c := ⟨c.1, σ.2 c.1 c.2⟩
  inj' := by
    intro a b h
    exact Subtype.ext (congrArg (fun p : GlobalPlaquette => p.1) h)

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
