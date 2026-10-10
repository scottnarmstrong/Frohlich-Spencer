/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
import FroehlichSpencer.BKT.Provider.PlaneRotatorTransition

/-! # The Kosterlitz–Thouless transition of the two-dimensional plane rotator -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the existence of a Kosterlitz–Thouless transition in the two-dimensional plane
rotator (FS81 abstract and J p. 575: "the lower bound (6.1) establishes the existence of a transition
in this model"; combines Theorem C with (1.30) and (1.31)).

There is `β_c > 0` such that for
`0 ≤ β < β_c` the infinite-volume two-point function `⟨S_j · S_ℓ⟩(β)` decays exponentially, and for
`β > β_c` it does not decay exponentially but still tends to `0` uniformly as `|j - ℓ| → ∞` (no
long-range order); `|·|` is the Euclidean norm.
-/
theorem planeRotator_kosterlitzThouless_transition :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), β < βc →
        ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), βc < β →
        (¬ ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
        ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ j ℓ : ℤ × ℤ,
          R ≤ Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2) →
            planeRotatorCorrelation β hβ 1 j ℓ ≤ ε) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.planeRotator_kosterlitzThouless_transition
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
