module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import FroehlichSpencer.BKT.Surface.FreeVillainDisorder

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

/-- FS81 (1.32) with fβ=vβ on the positive vertical seam in the free square. The
coordinates are recentered from `[-L,L]²` to `[0,2L]²`. -/
noncomputable def villainClockDisorderObservable (β : ℝ) (_hβ : 0 < β) (ξ : ℝ)
    (L r : ℕ) (Λ : Finset (ℤ × ℤ))
    (hΛ : ∀ m : Fin r,
      ((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ)) ∈ Λ ∧
        ((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ) + 1) ∈ Λ)
    (θ : Λ → ℝ) : ℝ :=
  let v : ℝ → ℝ := fun t => ∑' m : ℤ, Real.exp (-(β / 2) * (t + 2 * Real.pi * m) ^ 2)
  ∏ m : Fin r,
    v (θ ⟨((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ) + 1), (hΛ m).2⟩ -
      θ ⟨((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ)), (hΛ m).1⟩ + 2 * Real.pi * ξ) /
      v (θ ⟨((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ) + 1), (hΛ m).2⟩ -
        θ ⟨((((L : ℕ) + m.val + 1 : ℕ) : ℤ), (L : ℤ)), (hΛ m).1⟩)

end FroehlichSpencer.BKT

end
