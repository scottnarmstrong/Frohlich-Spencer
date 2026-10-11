/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.CentredCube
public import FroehlichSpencer.FS82.SurfaceInfinite.InCube
public import FroehlichSpencer.FS82.Surface.PrimalPlaquettes
public import FroehlichSpencer.FS82.Surface.PrimalVillainLaw

@[expose] public section
open MeasureTheory Filter Topology
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.SurfaceInfinite

/-- The finite C4 complementary primal face of a contained global dual face.
Containment is an input; no value is assigned outside the cube. -/
noncomputable def sourceC4PrimalFace (N : ℕ) (hN : 0 < N)
    (p : GlobalPlaquette)
    (hp : inCube (Surface.centredCube N hN) p) :
    Surface.PrimalPlaquettes (Surface.centredCube N hN) := by
  let R := Surface.centredCube N hN
  let d : Surface.DualPlaquettes R := Classical.choose hp
  let c : Surface.PrimalCell R := fun i =>
    match d.1 i with
    | Sum.inl v => Sum.inr v
    | Sum.inr e => Sum.inl e
  refine ⟨c, ?_⟩
  have hc : ∀ i : Fin 4, (c i).isRight = true ↔ ¬ (d.1 i).isRight = true := by
    intro i
    dsimp only [c]
    cases d.1 i with
    | inl _ => exact iff_of_true rfl Bool.false_ne_true
    | inr _ => exact iff_of_false Bool.false_ne_true (not_not_intro rfl)
  exact (congrArg Finset.card ((Finset.filter_congr fun i _ => hc i).trans
      (Finset.compl_filter _).symm)).trans ((Finset.card_compl _).trans (congrArg (4 - ·) d.2))
end FroehlichSpencer.FS82.SurfaceInfinite
end
