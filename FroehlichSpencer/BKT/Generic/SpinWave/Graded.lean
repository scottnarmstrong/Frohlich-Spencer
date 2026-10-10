/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.LocalFactor
public import FroehlichSpencer.BKT.SpinWaves.Prop47
public import FroehlichSpencer.BKT.Reduction.P24Assembly
public import FroehlichSpencer.BKT.SpinWaves.BoundaryShellPacking

/-! # Graded spin-wave data

The pieces are the unit sign waves from KP Lemma 4.5 (scale zero) and the flattened square
profiles from KP Proposition 4.7 (positive scales).  Their geometric, charge, energy and gradient
estimates are recorded together so that a cost-envelope argument can choose amplitudes without
introducing a Gaussian hypothesis.  The square-profile gradient estimate is proved in
`GradientBounds.lean`; the sign-wave construction is in `Base.lean`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.SpinWave

universe u v w

variable {V : Type u} {E : Type v}

/-- A finite graded family of spin-wave pieces with the estimates used by the non-quadratic
cost argument .  Scale zero is reserved for the base sign waves; a square profile at
geometric scale `k` is assigned grade `k`.

`countPerScale k` is the combinatorial envelope supplied by the selected square-cover theorem.
The structure itself is independent of the underlying probability measure and of the cost. -/
structure GradedSpinWave [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (ρ : V → ℤ) where
  ι : Type w
  [finite : Fintype ι]
  alpha : ℝ
  alpha_gt_one : 1 < alpha
  K₀ : ℝ
  K₀_nonneg : 0 ≤ K₀
  K₁ : ℝ
  K₁_nonneg : 0 ≤ K₁
  scale : ι → ℕ
  piece : ι → V → ℝ
  charge : ι → ℝ
  countPerScale : ℕ → ℝ
  countPerScale_nonneg : ∀ k, 0 ≤ countPerScale k
  count : ∀ k, ((Finset.univ.filter fun t : ι => scale t = k).card : ℝ) ≤
    countPerScale k
  grad_disjoint : ∀ t t', t ≠ t' → ∀ e,
    G.grad (piece t) e = 0 ∨ G.grad (piece t') e = 0
  const_plus : ∀ t, ∀ ρ' ∈ G.comparableDensities N₀ ρ,
    ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ρ' (centerOf ρ'), piece t j = c
  supp : ∀ t, Function.support (piece t) ⊆ G.densityDomain ρ (centerOf ρ)
  pairing : ∀ t,
    Multigraph.pairing (piece t) (fun j => (ρ j : ℝ)) = charge t
  charge_ge_one : ∀ t, 1 ≤ |charge t|
  energy_le : ∀ t, G.energy (piece t) ≤ K₀ * charge t ^ 2
  grad_le : ∀ t e,
    |G.grad (piece t) e| ≤
      K₁ * (2 : ℝ) ^ (-(1 - 1 / alpha) * (scale t : ℝ))

end FroehlichSpencer.BKT.Generic.SpinWave

end
