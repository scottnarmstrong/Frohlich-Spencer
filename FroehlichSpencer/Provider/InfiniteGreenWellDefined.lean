/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Lattice.Kernel
public import FroehlichSpencer.Infra.Green.Existence
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.existsUnique_squareSummable_greenSolution`

This module contains `FroehlichSpencer.Provider.existsUnique_squareSummable_greenSolution`, the
proof of the statement `FroehlichSpencer.existsUnique_squareSummable_greenSolution` (file
`FroehlichSpencer/Surface/InfiniteGreenWellDefined.lean`).

Proof: the generic existence and uniqueness theorem `Infra.existsUnique_memℓp_eq_single` for the
lattice kernel `hoppingKernel ν` (row bound `2ν`) with potential `v + 2ν`
(`FroehlichSpencer/Lattice/Kernel.lean`).

The hypothesis `0 < ν` of the statement is not
needed (binder `_hν`).
-/

public section

namespace FroehlichSpencer.Provider

theorem existsUnique_squareSummable_greenSolution (ν : ℕ) (_hν : 0 < ν) (z : ℂ)
    (hz : z.im ≠ 0) (v : Site ν → ℝ) (y : Site ν) :
    ∃! ψ : Site ν → ℂ,
      Summable (fun x => ‖ψ x‖ ^ 2) ∧
      ∀ x, -(latticeLaplacian ν ψ x) + ((v x : ℂ) - z) * ψ x = if x = y then 1 else 0 := by
  classical
  have key := Infra.existsUnique_memℓp_eq_single (a := hoppingKernel ν) (K := 2 * ν)
    (hoppingKernel_symm ν) (hoppingKernel_finite ν) (sum_norm_hoppingKernel_le ν)
    (fun x => v x + 2 * (ν : ℝ)) hz y
  have hmem : ∀ ψ : Site ν → ℂ, Memℓp ψ 2 ↔ Summable (fun x => ‖ψ x‖ ^ 2) := by
    intro ψ
    rw [memℓp_gen_iff (by norm_num)]
    simp
  have heq : ∀ ψ : Site ν → ℂ, (∀ x, ∑' w, hoppingKernel ν x w * ψ w +
        (((fun x => v x + 2 * (ν : ℝ)) x : ℝ) - z) * ψ x = (Pi.single y 1 : Site ν → ℂ) x) ↔
      ∀ x, -(latticeLaplacian ν ψ x) + ((v x : ℂ) - z) * ψ x = if x = y then 1 else 0 := by
    intro ψ
    refine forall_congr' fun x => ?_
    rw [tsum_hoppingKernel_mul, Pi.single_apply]
    push_cast
    constructor <;> intro h <;> linear_combination h
  simpa only [hmem, heq] using key

end FroehlichSpencer.Provider

end
