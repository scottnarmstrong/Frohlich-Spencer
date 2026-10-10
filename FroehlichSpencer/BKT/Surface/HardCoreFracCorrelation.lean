/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import FroehlichSpencer.BKT.Surface.CoulombPotential

/-! # The fractional-charge correlation of the hard-core Coulomb gas -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81 (1.23) (J p. 532): the correlation of two opposite fractional charges `±ξ` at the sites
`a, b` of a finite region `Λ ⊂ ℤ²` in the hard-core gas ((1.10): `λ(0) = 1`, `λ(±1) = z/2`,
`λ(q) = 0` otherwise; `z ≥ 0`, so that `dλ` is a positive measure, (1.6)) with free boundary
conditions (J p. 529 (i)),
`G_{ξ,Λ}(a, b) = Z_Λ⁻¹ ∑_{q_Λ} exp [-β E(q_Λ + ξ (δ_a - δ_b))] ∏_{j ∈ Λ} λ(q(j))`, where
`Z_Λ = ∑_{q_Λ} exp [-β E(q_Λ)] ∏_{j ∈ Λ} λ(q(j))` (1.8). The sums run over the charge
configurations `q : Λ → {-1, 0, 1}` (the support of `λ`) of total charge `∑_j q(j) = 0`: with free
boundary conditions a configuration of nonzero total charge has infinite energy ((1.14), J p. 531),
and the fractional dipole `ξ (δ_a - δ_b)` is neutral. (This gives the non-neutral configurations
zero weight only for `β > 0`; for `β ≤ 0` the restriction to neutral configurations is a convention
of the formula's extension.) The energy is (1.4),
`E(ρ) = ½ ∑_{i, j ∈ Λ} ρ(i) ρ(j) C(i - j)` with `C = coulombPotential` (normalized by `C(0) = 0`;
the normalization does not enter the energy of a neutral `ρ`). The configuration `q = 0` gives
`Z_Λ ≥ 1`. The formula is written for every real `β`; FS81's inverse temperature is `β > 0`. -/
noncomputable def hardCoreFracCorrelation (β z : ℝ) (_hz : 0 ≤ z) (ξ : ℝ) (Λ : Finset (ℤ × ℤ))
    (a b : Λ) : ℝ :=
  let E : (Λ → ℝ) → ℝ := fun ρ =>
    (∑ i, ∑ j, ρ i * ρ j * coulombPotential ((i : ℤ × ℤ) - j)) / 2
  let w : (Λ → ℤ) → ℝ := fun q =>
    if ∑ j, q j = 0 then ∏ j, (if q j = 0 then 1 else z / 2) else 0
  let f : Λ → ℝ := fun j => (if j = a then ξ else 0) - (if j = b then ξ else 0)
  (∑ q ∈ Fintype.piFinset fun _ : Λ => Finset.Icc (-1 : ℤ) 1,
      w q * Real.exp (-β * E (fun j => (q j : ℝ) + f j))) /
    ∑ q ∈ Fintype.piFinset fun _ : Λ => Finset.Icc (-1 : ℤ) 1,
      w q * Real.exp (-β * E (fun j => (q j : ℝ)))

end FroehlichSpencer.BKT

end
