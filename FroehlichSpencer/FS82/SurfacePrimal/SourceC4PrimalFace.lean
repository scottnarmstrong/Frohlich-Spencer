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
  have haxes :
      (Finset.univ.filter fun i : Fin 4 => (c i).isRight) =
    (Finset.univ.filter fun i : Fin 4 => ¬ (d.1 i).isRight) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases hi : d.1 i <;> simp [c, hi]
  have hcomp :
      (Finset.univ.filter fun i : Fin 4 => ¬ (d.1 i).isRight) =
    (Finset.univ.filter fun i : Fin 4 => (d.1 i).isRight)ᶜ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  have hcard :
      (Finset.univ.filter fun i : Fin 4 => ¬ (d.1 i).isRight).card =
        4 - Surface.dualCellDegree R d := by
    rw [hcomp, Finset.card_compl]
    change 4 - (Finset.univ.filter (fun i : Fin 4 => (d.1 i).isRight)).card =
      4 - (Finset.univ.filter (fun i : Fin 4 => (d.1 i).isRight)).card
    rfl
  have hd : Surface.dualCellDegree R d = 2 := d.2
  rw [Surface.primalCellDegree, haxes]
  rw [hcard, hd]
end FroehlichSpencer.FS82.SurfaceInfinite
end
