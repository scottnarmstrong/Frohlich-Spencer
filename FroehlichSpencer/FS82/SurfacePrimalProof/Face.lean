/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.SurfacePrimal.SourceC4PrimalFace
public import FroehlichSpencer.FS82.PrimalInterface.LatticeBridge
public import FroehlichSpencer.FS82.Infinite.NonsummabilityPrimal
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.FiniteLawBridge
import Mathlib.Tactic

@[expose] public section
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Infinite.Nonsummability
namespace FroehlichSpencer.FS82.SurfaceInfinite

theorem sourceC4PrimalFace_eq_primalFace (N : ℕ) (hN : 0 < N)
    (p : GlobalPlaquette)
    (hp : inCube (Surface.centredCube N hN) p) :
    FroehlichSpencer.FS82.PrimalInterface.plaquetteEquiv (Surface.centredCube N hN)
        (sourceC4PrimalFace N hN p hp) =
      primalPlaquetteOfGlobal N p ((source_inCube_iff N hN p).mp hp) := by
  let hpInt : PlaquetteInCube N p := (source_inCube_iff N hN p).mp hp
  let d : Surface.DualPlaquettes (Surface.centredCube N hN) := Classical.choose hp
  let qsrc : SourceDualTwoCells (cube N) := ⟨d.1, d.2⟩
  have hsrc : cubePlaquetteEmbedding N qsrc = p.1 := by
    have h : Surface.dualCellEmbeddingC1 (Surface.centredCube N hN) d.1 = p.1 := Classical.choose_spec hp
    rw [Surface.c1Cell_bridge] at h
    exact h
  have hq : cubePlaquettePreimage N p hpInt = qsrc := by
    apply (cubePlaquetteEmbedding N).injective
    exact (cubePlaquetteEmbedding_preimage N p hpInt).trans hsrc.symm
  apply Subtype.ext
  change (sourceC4PrimalFace N hN p hp).1 =
    Cubical.primalDualCellEquiv.symm (cubePlaquettePreimage N p hpInt).1
  rw [hq]
  funext i
  simp only [sourceC4PrimalFace]
  dsimp only [qsrc, d, Cubical.primalDualCellEquiv, Equiv.coe_fn_symm_mk]
  cases h : (Classical.choose hp).1 i <;> rfl

/-- The finite chosen dual face has precisely the source C1 centred-cube
embedding, including the vertex offset by one. -/
theorem sourceC4PrimalFace_embedding (N : ℕ) (hN : 0 < N)
    (p : GlobalPlaquette) (hp : inCube (Surface.centredCube N hN) p) :
    Surface.dualCellEmbeddingC1 (Surface.centredCube N hN)
      (Classical.choose hp).1 = p.1 := Classical.choose_spec hp

/-- Each endpoint in the selected dual plane has C4 coordinate sign minus one. -/
theorem sourcePrimalC4_endpoint_sign (x : LatticePoint) :
    Gaussian.latticeCellOrientationSign (dualCurvatureAt x).1 = -1 :=
  spectralPlaquetteOrientation x

/-- Both endpoint signs cancel in the pair insertion. -/
theorem sourcePrimalC4_pair_sign (x y : LatticePoint) :
    Gaussian.latticeCellOrientationSign (dualCurvatureAt x).1 *
      Gaussian.latticeCellOrientationSign (dualCurvatureAt y).1 = 1 := by
  rw [sourcePrimalC4_endpoint_sign, sourcePrimalC4_endpoint_sign]
  norm_num

end FroehlichSpencer.FS82.SurfaceInfinite

end
