/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
import FroehlichSpencer.BKT.Provider.PlaneRotatorPowerLawUpper

/-! # A McBryan–Spencer power-law upper bound for the plane rotator (FS81 (1.31), weak form) -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
a weak form of FS81 (1.31) (J p. 533, McBryan–Spencer [14], cited, not an FS81
theorem): there is an absolute `c > 0` such that for every `β > 0` there is `K` with
`0 ≤ ⟨S_j · S_ℓ⟩(β) ≤ K (1 + |j - ℓ|)^{-c min(1, 1/β)}` for all sites, `|·|` the Euclidean norm.

(1.31) itself has the exponent `1/((2π + ε) β)` for every `ε > 0`, with `K = K(ε, β)`.
-/
theorem planeRotator_powerLaw_upper_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 0 ≤ β), 0 < β → ∃ K : ℝ, ∀ j ℓ : ℤ × ℤ,
      0 ≤ planeRotatorCorrelation β hβ 1 j ℓ ∧
        planeRotatorCorrelation β hβ 1 j ℓ ≤
          K * (1 + Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)) ^
            (-(c * min 1 (1 / β))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.planeRotator_powerLaw_upper_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
