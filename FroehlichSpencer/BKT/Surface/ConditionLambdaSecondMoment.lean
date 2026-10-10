/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finsupp.Basic
public import FroehlichSpencer.BKT.Surface.CoulombGasPartition

/-! # The second moment of the sine-Gordon field of a lattice Coulomb gas -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81 (1.16)–(1.17) (J p. 531): the second moment `⟨φ(g)²⟩_Λ(β, λ)` of the sine-Gordon field of
the Coulomb gas with a priori weights `λ` in a finite region `Λ ⊂ ℤ²` with free boundary conditions,
for a real test function `g` supported in `Λ` with `∑_j g(j) = 0`. The state (1.16) is
`Z_Λ⁻¹ ∏_{j ∈ Λ} λ̂(φ(j)) dμ_β(φ)`, `λ̂(φ) = ∑_q λ(q) e^{iqφ}`, with the Gaussian `dμ_β` of
covariance `β(-Δ)⁻¹`. By (1.15) its pairing with an observable is the sum over the charge
configurations `q : Λ → ℤ` of `∏_j λ(q(j))` times the Gaussian integral of the observable against
`e^{iφ(q)}`; for `φ(g)²` that integral is `(β ⟨g, C g⟩ - β² ⟨q, C g⟩²) exp[-β E(q)]`. So
`⟨φ(g)²⟩_Λ = Z_Λ⁻¹ ∑_q w(q) (β ⟨g, C g⟩ - β² ⟨q, C g⟩²)`, the real-space form of (1.17), with the
weights `w = coulombGasWeight β λ Λ` (non-neutral `q` have weight `0`, (1.14)), the partition
function `Z_Λ` (1.8), `C = coulombPotential`, `⟨g, C g⟩ = ∑_{x, y} g(x) g(y) C(x - y)` and
`⟨q, C g⟩ = ∑_{i ∈ Λ} ∑_y q(i) g(y) C(i - y)`. It is defined for a positive measure `dλ` (1.6) with
a vacancy `λ(0) > 0`, so that `Z_Λ > 0`, on the domain `IsCoulombGasSummable β λ`,
and for `β > 0`, FS81's inverse temperature, for which the Gaussian `dμ_β` exists. The positive vacancy assumption is implicit in the printed argument. -/
noncomputable def conditionLambdaSecondMoment (β : ℝ) (_hβ : 0 < β) (lam : ℤ → ℝ)
    (_hlam : ∀ q, 0 ≤ lam q) (_hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam)
    (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (_hgΛ : g.support ⊆ Λ)
    (_hg : (g.sum fun _ a => a) = 0) : ℝ :=
  (∑' q : Λ → ℤ, coulombGasWeight β lam Λ q *
      (β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) -
        β ^ 2 * (∑ i, (q i : ℝ) * g.sum fun y b => b * coulombPotential ((i : ℤ × ℤ) - y)) ^ 2)) /
    coulombGasPartition β lam hS Λ

end FroehlichSpencer.BKT

end
