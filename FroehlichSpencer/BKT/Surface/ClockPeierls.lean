/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockLongRangeOrder
import FroehlichSpencer.BKT.Provider.ClockPeierls

/-! # The low-temperature phase of the `ℤ_n` clock model -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the low-temperature (ordered) phase of the `ℤ_n` clock models (FS81 §7.1, Remark 2,
J p. 585: "For β>β̄_c, the ℤ_n-symmetry of the model is spontaneously broken.

That β̄_c is finite is
seen by a standard Peierls argument.").

For every `n ≥ 2` there is a finite threshold `β̄` such that
for every `β > β̄` every harmonic `ξ` of the clock two-point function has long-range order.
-/
theorem clock_lowTemperature_longRangeOrder :
    ∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∃ βbar : ℝ, ∀ (β : ℝ) (hβ : 0 ≤ β), βbar < β →
      ∀ ξ : ℤ, IsClockLongRangeOrder n hn β hβ ξ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.clock_lowTemperature_longRangeOrder
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
