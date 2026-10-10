/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.GreenFunctionSpec
public import FroehlichSpencer.Lattice.Kernel
import Mathlib.Analysis.Normed.Lp.lpSpace
import FroehlichSpencer.Infra.Green.APriori

/-! # The Green-function pointwise a-priori bound -/

public section

namespace FroehlichSpencer.Reduction

/-- The infinite-volume Green function has the resolvent bound supplied by the
generic square-summable a-priori estimate. -/
theorem norm_greenFunction_le (ν : ℕ) (hν : 0 < ν) (z : ℂ) (hz : z.im ≠ 0)
    (v : Site ν → ℝ) (x y : Site ν) :
    ‖greenFunction ν hν z hz v x y‖ ≤ 1 / |z.im| := by
  let ψ : Site ν → ℂ := fun w => greenFunction ν hν z hz v w y
  have hψ : Summable (fun w => ‖ψ w‖ ^ 2) ∧
      ∀ w, -(latticeLaplacian ν ψ w) + ((v w : ℂ) - z) * ψ w =
        if w = y then 1 else 0 := by
    simpa [ψ] using
      ((greenFunction_spec ν hν z hz v y ψ).mpr rfl)
  have hmem : Memℓp ψ 2 ↔ Summable (fun w => ‖ψ w‖ ^ 2) := by
    rw [memℓp_gen_iff (by norm_num)]
    simp
  have hkernel : ∀ w, ∑' q, hoppingKernel ν w q * ψ q +
      (((v w + 2 * (ν : ℝ)) : ℝ) - z) * ψ w =
        (Pi.single y (1 : ℂ) : Site ν → ℂ) w := by
    intro w
    rw [tsum_hoppingKernel_mul]
    simp only [Pi.single_apply]
    have heq := hψ.2 w
    push_cast
    linear_combination heq
  apply Infra.norm_le_one_div_of_eq_single
    (a := hoppingKernel ν) (K := 2 * (ν : ℝ))
    (hoppingKernel_symm ν) (hoppingKernel_finite ν)
    (sum_norm_hoppingKernel_le ν) (fun w => v w + 2 * (ν : ℝ)) hz
    (y := y) (ψ := ψ) (hψ := hmem.mpr hψ.1) (h := hkernel) x

end FroehlichSpencer.Reduction

end
