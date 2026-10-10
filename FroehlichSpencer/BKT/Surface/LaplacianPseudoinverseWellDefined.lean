/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverse
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph
import FroehlichSpencer.BKT.Provider.LaplacianPseudoinverseWellDefined

/-! # Well-definedness of the pseudoinverse of the Laplacian -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

universe u v

/--
on a finite connected multigraph, exactly one linear map satisfies KP (1.2).
-/
theorem existsUnique_isLaplacianPseudoinverse {V : Type u} {E : Type v} [Fintype V]
    [Fintype E] [DecidableEq V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) :
    ∃! T : (V → ℝ) →ₗ[ℝ] V → ℝ, G.IsLaplacianPseudoinverse T :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.existsUnique_isLaplacianPseudoinverse G hG
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
