/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.SpinWave.Graded

/-!
# The charge-layer interface of the T1.6-NG assembly (generic core)

The charge layer is everything the assembly consumes from the combinatorics of charges: KP Theorem
2.2 (the convex expansion and its activity bound), KP Proposition 2.1 (the cover bound) and the
geometry of KP Proposition 2.4 (graded spin waves).

It is stated abstractly so that

A `ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁` consists of

* a finite convex expansion `∏_j λ_j(ψ_j) = ∑_i c_i ∏_{ϱ ∈ 𝒩_i} [1 + K_i(ϱ) cos⟨ψ, ϱ⟩]`
  (`expand`, `c_pos`, `c_sum`);
* for each ensemble, the subfamily `ℛ_i ⊆ 𝒩_i` of densities to be translated (`R`, `R_sub`); the
  densities of `𝒩_i ∖ ℛ_i` are disposed of by the law (under KP's rooted law, the one charged
  density integrates out);
* the entropy bound `|K_i(ϱ)| ≤ e^{D₂ A(ϱ)} Z(ϱ)` for `ϱ ∈ ℛ_i` (`entropy`; KP T2.2(d) with
  `A = A(ϱ)` the cover cost);
* for each `ϱ ∈ ℛ_i`, graded spin-wave data `Wv` relative to `ℛ_i` (`wave`, `HasLayerWave`):
  scale-zero pieces carry at least half of the linear mass `∑_j |ϱ(j)|`; every piece's gradient is
  supported on at most `100 · 4^{scale}` edges; the cover bound
  `A(ϱ) ≤ D₁ (∑_j |ϱ(j)| + #{pieces of positive scale})` (KP P2.1); and every piece pairs to
  zero with every other density of `ℛ_i` (the input of KP's orthogonality).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open FroehlichSpencer.BKT.Generic.SpinWave

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- The clauses of the graded spin-wave data of one translated density `ϱ ∈ ℛ` that the assembly
consumes. -/
def HasLayerWave (G : Multigraph V E) (R : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (A : (V → ℤ) → ℝ) (D₁ α K₀ K₁ : ℝ) (ϱ : V → ℤ) (Wv : GradedSpinWave G R centerOf ϱ) :
    Prop :=
  Wv.alpha = α ∧ Wv.K₀ = K₀ ∧ Wv.K₁ = K₁ ∧
    ((1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤
      ∑ t ∈ (letI := Wv.finite; Finset.univ.filter fun t => Wv.scale t = 0), |Wv.charge t|) ∧
    (∀ t, ((Finset.univ.filter fun e => G.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤
      100 * 4 ^ Wv.scale t) ∧
    A ϱ ≤ D₁ * (∑ j, |(ϱ j : ℝ)| +
      ((letI := Wv.finite; (Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℕ) : ℝ)) ∧
    ∀ t, ∀ ϱ' ∈ R, ϱ' ≠ ϱ → ∑ j, Wv.piece t j * (ϱ' j : ℝ) = 0

/-- **The charge-layer interface** of the T1.6-NG assembly: the clauses consumed from KP T2.2,
P2.1 and the P2.4 geometry (or their FS81 Appendix D analogues). -/
structure ChargeLayer (G : Multigraph V E) (lam : V → ℝ → ℝ) (centerOf : (V → ℤ) → V)
    (A Zent : (V → ℤ) → ℝ) (D₁ D₂ α K₀ K₁ : ℝ) where
  n : ℕ
  N : Fin n → Finset (V → ℤ)
  R : Fin n → Finset (V → ℤ)
  c : Fin n → ℝ
  K : Fin n → (V → ℤ) → ℝ
  c_pos : ∀ i, 0 < c i
  c_sum : ∑ i, c i = 1
  R_sub : ∀ i, R i ⊆ N i
  expand : ∀ ψ : V → ℝ,
    ∏ j, lam j (ψ j) = ∑ i, c i * ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, ψ j * (ϱ j : ℝ)))
  entropy : ∀ i, ∀ ϱ ∈ R i, |K i ϱ| ≤ Real.exp (D₂ * A ϱ) * Zent ϱ
  wave : ∀ i, ∀ ϱ ∈ R i, ∃ Wv : GradedSpinWave.{0, 0, 0} G (R i) centerOf ϱ,
    HasLayerWave G (R i) centerOf A D₁ α K₀ K₁ ϱ Wv

end FroehlichSpencer.BKT.Generic

end
