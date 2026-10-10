/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Green
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverse

/-!
# Provider for `FroehlichSpencer.BKT.existsUnique_isLaplacianPseudoinverse`

This module will contain `FroehlichSpencer.BKT.Provider.existsUnique_isLaplacianPseudoinverse`, the proof of the
statement `FroehlichSpencer.BKT.existsUnique_isLaplacianPseudoinverse` (file `FroehlichSpencer/BKT/Surface/LaplacianPseudoinverseWellDefined.lean`).

-/

@[expose] public section

namespace FroehlichSpencer.BKT.Provider

open Multigraph

universe u v

/-- The connected finite graph Laplacian has the unique KP (1.2)
pseudoinverse, obtained by inverting the Laplacian on its mean-zero subspace. -/
theorem existsUnique_isLaplacianPseudoinverse {V : Type u} {E : Type v} [Fintype V]
    [Fintype E] [DecidableEq V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) :
    ∃! T : (V → ℝ) →ₗ[ℝ] V → ℝ, G.IsLaplacianPseudoinverse T := by
  let hGc : G.Connected := hG
  refine ⟨G.greenOp hGc, ?_, ?_⟩
  · constructor
    · intro f hf
      exact ⟨G.laplacian_greenOp_of_sum_eq_zero hGc f hf,
        G.greenOp_laplacian_of_sum_eq_zero hGc f hf⟩
    · intro c
      exact G.greenOp_const hGc c
  · intro T hT
    rcases hT with ⟨hT, hTc⟩
    exact G.greenOp_unique hGc T hT hTc

end FroehlichSpencer.BKT.Provider

end
