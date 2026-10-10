/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ConditionLambda
public import FroehlichSpencer.BKT.Surface.CoulombGasSummable
import FroehlichSpencer.BKT.Provider.CoulombGasSummability

/-! # Summability of the Coulomb gas under Condition λ -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the summability gate of the Coulomb gas objects.

For all parameters `α` and `ε`
there is a `β₀` such that for every constant `C` and every `β > β₀`, every `λ` satisfying
Condition λ with the constant `C` and the parameters `α`, `ε` at `β` (FS81 J p. 530) gives a
summable gas (`IsCoulombGasSummable β λ`): its partition function (1.8), its fractional-charge
correlations (1.23) and its field second moments (1.16) are convergent series.
-/
theorem conditionLambda_isCoulombGasSummable :
    ∀ α ε : ℝ, ∃ β₀ : ℝ, ∀ C β : ℝ, β₀ < β → ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
      IsCoulombGasSummable β lam :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.conditionLambda_isCoulombGasSummable
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
