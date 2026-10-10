/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockExpDecay
import FroehlichSpencer.BKT.Provider.ClockHighTemperature

/-! # The high-temperature phase of the `ℤ_n` clock model -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the high-temperature (disordered) phase of the `ℤ_n` clock models (FS81 §7.1,
J p. 589: "This behavior contrasts the one for β<β_c (unbroken ℤ_n-symmetry) …, where connected
correlations have exponential fall-off").

There is `β_h > 0` such that for every `n ≥ 2` and every
`0 ≤ β < β_h` the fundamental harmonic `⟨cos (θ_0 - θ_x)⟩^{(n)}(β)` decays exponentially; `β_h` does
not depend on `n`.

(In the `ℤ_n`-symmetric free state the one-point function vanishes, so this is
the connected two-point function.)
-/
theorem clock_highTemperature_expDecay :
    ∃ βh : ℝ, 0 < βh ∧ ∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), β < βh →
      IsClockExpDecay n hn β hβ 1 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.clock_highTemperature_expDecay
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
