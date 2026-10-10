/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # FS81's disorder operator for the Villain model on the wired box -/

@[expose] public section

namespace FroehlichSpencer.BKT

/--
FS81's disorder operator (1.32) (J p. 534) for the Villain model (`f_β = v_β`, (1.27):
`v_β(t) = ∑_{m ∈ ℤ} exp (-(β/2) (t + 2πm)²)`, a convergent series only for `β > 0`, the carrier of
the operator as of `villainLaw`) on the angle configurations
`θ : Option (Fin L × Fin L) → ℝ` of the wired box `Λ_L^zero` of the `villainLaw` (`θ none` is
the wired angle).

With the site `o` of the box in the role of `0` and `x = o + (n, 0)`,
`D^ξ_{ox}(θ) = ∏_{m=1}^{n} v_β(θ_{o+(m,1)} - θ_{o+(m,0)} + 2πξ) / v_β(θ_{o+(m,1)} - θ_{o+(m,0)})`.

The `n` bonds of the string lie in the box (`o₁ + n < L`, `o₂ + 1 < L`).
-/
noncomputable def wiredVillainDisorder (L : ℕ) (β : ℝ) (_hβ : 0 < β) (ξ : ℝ) (o : Fin L × Fin L)
    (n : ℕ) (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) (θ : Option (Fin L × Fin L) → ℝ) : ℝ :=
  let v : ℝ → ℝ := fun t => ∑' m : ℤ, Real.exp (-(β / 2) * (t + 2 * Real.pi * m) ^ 2)
  ∏ m : Fin n,
    v (θ (some (⟨o.1.val + m.val + 1, by omega⟩, ⟨o.2.val + 1, hfit.2⟩)) -
        θ (some (⟨o.1.val + m.val + 1, by omega⟩, o.2)) + 2 * Real.pi * ξ) /
      v (θ (some (⟨o.1.val + m.val + 1, by omega⟩, ⟨o.2.val + 1, hfit.2⟩)) -
        θ (some (⟨o.1.val + m.val + 1, by omega⟩, o.2)))

end FroehlichSpencer.BKT

end
