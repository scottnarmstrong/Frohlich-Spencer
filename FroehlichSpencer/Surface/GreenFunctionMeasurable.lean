/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.GreenFunctionSpec
public import FroehlichSpencer.Surface.ConfigurationSpace
public import FroehlichSpencer.IDS.Green
import Mathlib.Tactic

/-! # Measurability of the source Green function -/

public section

open MeasureTheory

namespace FroehlichSpencer

/-- The Green function selected from W1 is measurable in the configuration. -/
@[fun_prop]
theorem measurable_green_function (ν : ℕ) (hν : 0 < ν) (z : ℂ) (hz : z.im ≠ 0)
    (y x : Site ν) :
    Measurable fun v : Configuration ν => greenFunction ν hν z hz v x y := by
  have hlat : Measurable fun v : Configuration ν =>
      IDS.latticeGreen ν z v y x := IDS.measurable_latticeGreen hz y x
  intro s hs
  apply (hlat (t := s) hs).congr
  ext v
  simp only [Set.mem_preimage]
  let ψ : Site ν → ℂ := fun w => IDS.latticeGreen ν z v y w
  have hmem : Memℓp ψ 2 := by
    have h := (IDS.latticeGreen_spec hz v y).1
    change Memℓp (fun w => IDS.latticeGreen ν z v y w) 2
    exact h
  have hsquare : Summable fun w => ‖ψ w‖ ^ 2 := by
    rw [memℓp_gen_iff (by norm_num)] at hmem
    simpa [ψ] using hmem
  have hequation : ∀ w,
      -(latticeLaplacian ν ψ w) + ((v w : ℂ) - z) * ψ w = if w = y then 1 else 0 := by
    intro w
    have h := (IDS.latticeGreen_spec hz v y).2 w
    rw [tsum_hoppingKernel_mul] at h
    rw [Pi.single_apply] at h
    push_cast at h
    dsimp [ψ]
    linear_combination h
  have hEq := (greenFunction_spec ν hν z hz v y ψ).mp ⟨hsquare, hequation⟩
  exact Iff.of_eq (congrArg (fun w : ℂ => w ∈ s) (congrFun hEq x))

end FroehlichSpencer

end
