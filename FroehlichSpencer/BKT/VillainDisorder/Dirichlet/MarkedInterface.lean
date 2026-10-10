/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.FejerLayerWitness
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.Carrier
public import FroehlichSpencer.BKT.Generic.Marked.Expansion
public import FroehlichSpencer.BKT.Gaussian.ComplexTranslation
import Mathlib.Tactic

/-!
# The input interface of the rooted marked estimate

Theorem D in FS81's boundary condition (1.35) needs the Dirichlet version of Theorem B: the
Fejér marked ratio on the rooted square `squareZero`, uniformly in the cutoff. The rooted Fejér witness
`RootedFejerLayerWitness` (`rootedFejerLayer_exists`) supplies:
- the branch expansion of the rooted Fejér product;
- for each branch ensemble, member waves with the D-form clauses;
- the activity and cover bounds.

That is enough for the branch normalizers, through the comparison of FS81 (5.35). The marked
terms need more. Expanding `cos(ξ⟨φ, ϱ₀⟩) ∏_N (1 + K cos)` over the clusters `C` of an adjacency
(`cos_mul_prod_eq_sum_clusters`) produces the real composites
`σ = ξ ϱ₀ + ∑_T m − ∑_{C ∖ T} m` (`rootedMarkedComposite`). Each marked term must be renormalized
with:
- a wave for `σ` (fractional charges at the mark, integer charges elsewhere);
- waves for the remainder that are orthogonal to `σ`.

These are FS81 Theorem 4.1 with one fractional density (Theorem 2.3), in Appendix D form. They
are not determined by the rooted Fejér witness, whose waves serve the branch ensembles only.

* `RootedMarkedTermData`: the renormalization data of one marked term, exactly the hypotheses of
  `gffLaw_integral_cos_mul_prod_translation`. It includes the remainder renormalized activities
  `≤ 1` and a lower bound on the composite energy.
* `RootedMarkedBranchClause`: per branch, a monotone adjacency, the neighbour-weight bound of
  the exploration weights, and the marked-term data with composite gain
  `γ (∑_{m ∈ C} cost m + ℓ)`.
* **`RootedFejerMarkedExtension`**: the clause on every branch of some rooted Fejér witness, on every
  buffered square, with gain rate `γ₀ η²/τ`, cost `layerA` and `ℓ = log₂(n + 1)`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Rotator

/-! ### The mark and the marked composites -/

/-- The dipole mark `δ_{center} − δ_{axial}` on the faces of the rooted square. -/
def rootedDipoleMark (R n : ℕ) (hn : n ≤ R) : RotatorDualFace (sideLength R) → ℤ :=
  fun j => if j = some (center R) then 1 else if j = some (axialSite R n hn) then -1 else 0

/-! ### The marked-term renormalization data -/

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- The real marked composite `ξ ϱ₀ + ∑_{m ∈ T} m − ∑_{m ∈ C ∖ T} m` of a cluster `C` and an
orientation `T ⊆ C` (the argument produced by `cos_mul_prod_eq_sum_clusters`). -/
def rootedMarkedComposite (ξ : ℝ) (ρ₀ : V → ℤ) (C T : Finset (V → ℤ)) : V → ℝ :=
  fun j => ξ * (ρ₀ j : ℝ) + ∑ m ∈ T, (m j : ℝ) - ∑ m ∈ C \ T, (m j : ℝ)

/-- **Renormalization data for one marked term** (FS81 Theorem 4.1 with one fractional density,
Appendix D form): waves `a₀` for the composite `σ` and `a ϱ` for the remainder `R`, mutually
orthogonal in the sense of `gffLaw_integral_cos_mul_prod_translation`. Each remainder member's
renormalized activity is at most one, and the composite's KP energy is at least `gain`. -/
def RootedMarkedTermData (G : Multigraph V E) (τ : ℝ) (K : (V → ℤ) → ℝ) (σ : V → ℝ)
    (R : Finset (V → ℤ)) (gain : ℝ) : Prop :=
  ∃ (a₀ : V → ℝ) (a : (V → ℤ) → V → ℝ),
    (∀ ϱ ∈ R, Multigraph.pairing a₀ (fun j => (ϱ j : ℝ)) = 0) ∧
    (∀ ϱ ∈ R, Multigraph.pairing (a ϱ) σ = 0) ∧
    (∀ ϱ ∈ R, ∀ ϱ' ∈ R, ϱ ≠ ϱ' → Multigraph.pairing (a ϱ) (fun j => (ϱ' j : ℝ)) = 0) ∧
    (∀ ϱ ∈ R, Multigraph.pairing a₀ (G.laplacian (a ϱ)) = 0) ∧
    (∀ ϱ ∈ R, ∀ ϱ' ∈ R, ϱ ≠ ϱ' → Multigraph.pairing (a ϱ) (G.laplacian (a ϱ')) = 0) ∧
    (∀ ϱ ∈ R, |K ϱ| *
      Real.exp (-gffTranslationEnergy G τ (a ϱ) (fun j => (ϱ j : ℝ))) ≤ 1) ∧
    gain ≤ gffTranslationEnergy G τ a₀ σ

/-- **The marked clause for one branch**: an adjacency on the members of the branch ensemble
`N` (monotone, so that `cos_mul_prod_eq_sum_clusters` applies), with
* `neighbour`: the members adjacent to a cluster `C` but outside it, weighted by
  `e^{−s₀ cost}`, are bounded by `K_nb (1 + ∑_C cost + ℓ)`;
* `term`: every cluster `C` and orientation `T ⊆ C` has marked-term renormalization data whose
  composite gain is at least `γ (∑_{m ∈ C} cost m + ℓ)`.
Here `ℓ` carries the decay of the observable: `ℓ = log₂(n + 1)` for a dipole of length `n`. -/
structure RootedMarkedBranchClause (G : Multigraph V E) (τ : ℝ) (N : Finset (V → ℤ))
    (K : (V → ℤ) → ℝ) (cost : (V → ℤ) → ℝ) (ξ : ℝ) (ρ₀ : V → ℤ)
    (adj : (V → ℤ) → Finset (V → ℤ) → Prop) (s₀ Knb γ ℓ : ℝ) : Prop where
  mono : AdjMonotone adj
  neighbour : ∀ C ∈ clusters adj N,
    ∑ m ∈ N \ (C ∪ remainder adj N C), Real.exp (-s₀ * cost m) ≤
      Knb * (1 + ∑ m ∈ C, cost m + ℓ)
  term : ∀ C ∈ clusters adj N, ∀ T ⊆ C,
    RootedMarkedTermData G τ K (rootedMarkedComposite ξ ρ₀ C T) (remainder adj N C)
      (γ * (∑ m ∈ C, cost m + ℓ))

/-! ### The marked Fejér input interface on the rooted Fejér layer -/

/-- **The marked extension of the rooted Fejér layer** (the input of marked Fejér beyond the rooted Fejér witness).
There are absolute constants `γ₀ > 0`, `s₀`, `K_nb` such that for every gap `η ∈ (0, 1/2]`
there is `τ₀ > 0` with the following property. For every GFF parameter `τ ∈ (0, τ₀)`, every
`ξ` with `η ≤ min(ξ, 1 − ξ)` and every dipole length `n ≥ 1` there is a buffer `R₀ ≥ n` such
that on every square `R ≥ R₀` and at every Fejér cutoff `N ≥ 1` some rooted Fejér witness carries:
* an adjacency on its branch ensembles;
* for every branch, the marked clause with cost `layerA`, the dipole mark, composite gain rate
  `γ₀ η²/τ` and decay length `ℓ = log₂(n + 1)`.
The rooted Fejér witness itself (`rootedFejerLayer_exists`) provides the branch expansion, the member
waves and the activity bounds; this Prop adds only the marked geometry of FS81 Theorems 2.3 and
4.1 in Appendix D form. -/
def RootedFejerMarkedExtension : Prop :=
  ∃ γ₀ s₀ Knb : ℝ, 0 < γ₀ ∧ 0 ≤ Knb ∧
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τ : ℝ, 0 < τ → τ < τ₀ →
      ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
      ∀ n : ℕ, 1 ≤ n → ∃ R₀ : ℕ, n ≤ R₀ ∧
        ∀ R : ℕ, R₀ ≤ R → ∀ (hn : n ≤ R) (N : ℕ), 1 ≤ N →
          ∃ (W : RootedFejerLayerWitness (sideLength R) N)
            (adj : (RotatorDualFace (sideLength R) → ℤ) →
              Finset (RotatorDualFace (sideLength R) → ℤ) → Prop),
            ∀ i : Fin W.layer.n,
              RootedMarkedBranchClause (graph R) τ (W.layer.N i) (W.layer.K i) layerA ξ
                (rootedDipoleMark R n hn) adj s₀ Knb (γ₀ * η ^ 2 / τ)
                (Real.logb 2 ((n : ℝ) + 1))

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
