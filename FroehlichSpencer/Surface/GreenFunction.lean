/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.InfiniteGreenWellDefined

/-! # Infinite-volume Green function -/

public section

namespace FroehlichSpencer

/-- The infinite-volume Green function, defined as the unique square-summable
solution with source at y. -/
@[expose] noncomputable def greenFunction (ν : ℕ) (hν : 0 < ν) (z : ℂ)
    (hz : z.im ≠ 0) (v : Site ν → ℝ) (x y : Site ν) : ℂ :=
  (Classical.choose
    (existsUnique_squareSummable_greenSolution ν hν z hz v y).exists) x

end FroehlichSpencer

end
