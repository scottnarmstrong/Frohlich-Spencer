/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import FroehlichSpencer.BKT.Surface.CoulombGasWeight

/-! # The domain of summability of a lattice Coulomb gas -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The Coulomb gas with a priori weights `λ` at inverse temperature `β` (FS81 (1.5)–(1.8), free
boundary conditions) is summable with every exponential moment of the total absolute charge: for
every finite region `Λ ⊂ ℤ²` and every `t ∈ ℝ` the series `∑_{q : Λ → ℤ} w(q) exp(t ∑_j |q(j)|)`
of the weights `w = coulombGasWeight β λ Λ` converges. The partition function (1.8), the
fractional-charge correlations (1.23) and the second moments of the sine-Gordon field (1.16) are
series dominated by these; this is their common domain of definition. -/
def IsCoulombGasSummable (β : ℝ) (lam : ℤ → ℝ) : Prop :=
  ∀ (Λ : Finset (ℤ × ℤ)) (t : ℝ),
    Summable fun q : Λ → ℤ => coulombGasWeight β lam Λ q * Real.exp (t * ∑ j, |(q j : ℝ)|)

end FroehlichSpencer.BKT

end
