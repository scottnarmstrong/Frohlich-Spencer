/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Combinatorics.Animals

/-!
# Uniform count of connected plaquette supports

The graph used by the small-activity expansion joins plaquettes that share a
link. Once its degree is bounded by twenty, the generic lattice-animal theorem
gives the `400^k` count used in the small-activity expansion.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open SimpleGraph

/-- A degree-twenty graph has at most `400^k` connected `k`-vertex supports
containing a prescribed root. -/
theorem card_areaAnimals_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [G.LocallyFinite]
    (hdeg : ∀ v, G.degree v ≤ 20) (x : V) (k : ℕ) (hk : 1 ≤ k) :
    (FroehlichSpencer.Infra.animals G x k).card ≤ 400 ^ k := by
  have hgeneric := FroehlichSpencer.Infra.card_animals_le
    (G := G) hdeg x k
  have hexp : 20 ^ (2 * (k - 1)) = 400 ^ (k - 1) := by
    rw [pow_mul]
    norm_num
  rw [hexp] at hgeneric
  calc
    (FroehlichSpencer.Infra.animals G x k).card ≤ 400 ^ (k - 1) := hgeneric
    _ ≤ 400 ^ k := by
      apply Nat.pow_le_pow_right
      · omega
      · omega

end FroehlichSpencer.FS82.Wilson

end
