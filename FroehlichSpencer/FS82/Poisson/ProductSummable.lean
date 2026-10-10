module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

theorem summable_prod_of_summable {α β : Type*} (f : α → ℂ) (g : β → ℂ)
    (hf : Summable f) (hg : Summable g) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  have hF : Summable (fun x => ‖f x‖) := hf.norm
  have hG : Summable (fun y => ‖g y‖) := hg.norm
  have hiter : Summable (fun x => ∑' y, ‖f x‖ * ‖g y‖) := by
    have hmul := hF.mul_right (∑' y, ‖g y‖)
    refine hmul.congr fun x => ?_
    exact (hG.tsum_mul_left ‖f x‖).symm
  have hreal : Summable (fun p : α × β => ‖f p.1‖ * ‖g p.2‖) :=
    (summable_prod_of_nonneg (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      ⟨fun x => hG.mul_left ‖f x‖, hiter⟩
  apply Summable.of_norm_bounded hreal
  intro p
  simp

end FroehlichSpencer.FS82.Poisson
