/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # The disorder operator of the rotator and clock models -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81's disorder operator (1.32) (J p. 534) with `f_β = r_β`, where `r_β(t) = exp (β cos t)`
(J p. 533) is the bond weight of the plane rotator and of the `ℤ_n` clock models (7.1), at
`x = (r, 0)`:
`D^ξ_{0x}(θ) = ∏_{m=1}^{r} r_β(θ_{(m,1)} - θ_{(m,0)} + 2πξ) / r_β(θ_{(m,1)} - θ_{(m,0)})`, on the
angle configurations `θ : Λ → ℝ` of a finite region `Λ ⊂ ℤ²` containing the `2r` sites `(m, 0)`,
`(m, 1)`, `m = 1, …, r`, of the string. (FS81 (7.5) says that its `D^ξ_{0x}` is "defined as in
(1.31)"; (1.31) is the spin-correlation bound, and the definition is (1.32).)
-/
noncomputable def clockDisorderOperator (β ξ : ℝ) (Λ : Finset (ℤ × ℤ)) (r : ℕ)
    (hΛ : ∀ m : Fin r, (((m : ℕ) : ℤ) + 1, (0 : ℤ)) ∈ Λ ∧ (((m : ℕ) : ℤ) + 1, (1 : ℤ)) ∈ Λ)
    (θ : Λ → ℝ) : ℝ :=
  ∏ m : Fin r,
    Real.exp (β * Real.cos (θ ⟨(((m : ℕ) : ℤ) + 1, 1), (hΛ m).2⟩ -
        θ ⟨(((m : ℕ) : ℤ) + 1, 0), (hΛ m).1⟩ + 2 * Real.pi * ξ)) /
      Real.exp (β * Real.cos (θ ⟨(((m : ℕ) : ℤ) + 1, 1), (hΛ m).2⟩ -
        θ ⟨(((m : ℕ) : ℤ) + 1, 0), (hΛ m).1⟩))

end FroehlichSpencer.BKT

end
