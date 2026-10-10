/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import FroehlichSpencer.Surface.Laplacian
import FroehlichSpencer.Provider.InfiniteGreenWellDefined

/-! # Infinite-volume Green solution -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer

/--
existence and uniqueness of the square-summable Green solution.
-/
theorem existsUnique_squareSummable_greenSolution (ν : ℕ) (hν : 0 < ν) (z : ℂ)
    (hz : z.im ≠ 0) (v : Site ν → ℝ) (y : Site ν) :
    ∃! ψ : Site ν → ℂ,
      Summable (fun x => ‖ψ x‖ ^ 2) ∧
      ∀ x, -(latticeLaplacian ν ψ x) + ((v x : ℂ) - z) * ψ x = if x = y then 1 else 0 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.Provider.existsUnique_squareSummable_greenSolution ν hν z hz v y
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer

end
-- FROZEN_ANCHOR_SUFFIX_END
