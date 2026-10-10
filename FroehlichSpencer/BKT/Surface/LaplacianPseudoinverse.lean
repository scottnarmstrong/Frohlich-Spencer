/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Real.Basic
public import FroehlichSpencer.BKT.Surface.Laplacian

/-! # The pseudoinverse of the Laplacian (KP (1.2)) -/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

/-- KP (1.2): the linear map `T` is `Δ⁻¹`, the Moore–Penrose pseudoinverse of the Laplacian,
characterized by `Δ (T f) = T (Δ f) = f` for every `f` with `∑ j, f j = 0`, and `T f = 0` for
constant `f`. KP call `-Δ⁻¹` the Green function. -/
def Multigraph.IsLaplacianPseudoinverse {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) : Prop :=
  (∀ f : V → ℝ, ∑ j, f j = 0 → G.laplacian (T f) = f ∧ T (G.laplacian f) = f) ∧
    ∀ c : ℝ, T (fun _ => c) = 0

end FroehlichSpencer.BKT

end
