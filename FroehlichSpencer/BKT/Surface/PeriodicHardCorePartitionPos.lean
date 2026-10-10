/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.PeriodicHardCorePartition
import FroehlichSpencer.BKT.Provider.PeriodicHardCorePartitionPos

/-! # Positivity of the periodic hard-core sine-Gordon partition function -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the hard-core sine-Gordon partition function on a periodic square is positive,
for every activity `z` (the neutral charge expansion of (1.15) has nonnegative terms and the
vacuum term `1`), so the sine-Gordon expectations (1.16) on `Λ_L^per` are well defined.
-/
theorem periodicHardCorePartition_pos (β : ℝ) (hβ : 0 < β) (z : ℝ) (Λ : Finset (ℤ × ℤ))
    (L : ℕ) (hL : 1 < L) : 0 < periodicHardCorePartition β hβ z Λ L hL :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.periodicHardCorePartition_pos β hβ z Λ L hL
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
