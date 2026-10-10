/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # FS81's disorder operator for the Villain model in a finite region -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81's disorder operator (1.32) (J p. 534) for the Villain model (`f_β = v_β`, (1.27):
`v_β(t) = ∑_{m ∈ ℤ} exp (-(β/2) (t + 2πm)²)`, a convergent series only for `β > 0`, the carrier of
the operator as of `freeVillainLaw`), with `x = (n, 0)`:
`D^ξ_{0x}(θ) = ∏_{m=1}^{n} v_β(θ_{(m,1)} - θ_{(m,0)} + 2πξ) / v_β(θ_{(m,1)} - θ_{(m,0)})`, on the
angle configurations `θ : Λ → ℝ` of a finite region `Λ ⊂ ℤ²` containing the `2n` sites `(m, 0)`,
`(m, 1)`, `m = 1, …, n`, of the string. -/
noncomputable def freeVillainDisorder (β : ℝ) (_hβ : 0 < β) (ξ : ℝ) (Λ : Finset (ℤ × ℤ)) (n : ℕ)
    (hΛ : ∀ m : Fin n, (((m : ℕ) : ℤ) + 1, (0 : ℤ)) ∈ Λ ∧ (((m : ℕ) : ℤ) + 1, (1 : ℤ)) ∈ Λ)
    (θ : Λ → ℝ) : ℝ :=
  let v : ℝ → ℝ := fun t => ∑' m : ℤ, Real.exp (-(β / 2) * (t + 2 * Real.pi * m) ^ 2)
  ∏ m : Fin n,
    v (θ ⟨(((m : ℕ) : ℤ) + 1, 1), (hΛ m).2⟩ - θ ⟨(((m : ℕ) : ℤ) + 1, 0), (hΛ m).1⟩ +
        2 * Real.pi * ξ) /
      v (θ ⟨(((m : ℕ) : ℤ) + 1, 1), (hΛ m).2⟩ - θ ⟨(((m : ℕ) : ℤ) + 1, 0), (hΛ m).1⟩)

end FroehlichSpencer.BKT

end
