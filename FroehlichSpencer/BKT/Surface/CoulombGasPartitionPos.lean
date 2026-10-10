/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.CoulombGasPartition
import FroehlichSpencer.BKT.Provider.CoulombGasPartitionPos

/-! # Positivity of the partition function of a lattice Coulomb gas -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/-- the positivity gate. If `dλ` is a positive measure on `ℤ` (FS81 (1.6)) with a
vacancy, `λ(0) > 0`, then on the domain of summability the partition function
(1.8) of the gas in every finite region `Λ ⊂ ℤ²` is positive, `Z_Λ > 0`, so that the ratios (1.9),
(1.16) and (1.23) are well defined. The positive vacancy assumption is implicit in the printed argument. -/
theorem coulombGasPartition_pos (β : ℝ) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0)
    (hS : IsCoulombGasSummable β lam) (Λ : Finset (ℤ × ℤ)) :
    0 < coulombGasPartition β lam hS Λ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.coulombGasPartition_pos β lam hlam hlam0 hS Λ
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
