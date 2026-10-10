/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.DensityNeighbourhood
import FroehlichSpencer.BKT.SpinWaves.Initial

/-!
# Spin waves of distinct densities have disjoint gradient supports

This module derives it from the support and constancy
clauses (1)–(2) of KP Proposition 2.4 (`Reduction.P24Step`; KP p. 11, (2.15)–(2.16)):

* `a_ϱ` is constant on `D⁺(ϱ')` for every comparable `ϱ' ∈ 𝒩₀(ϱ)` (`d(ϱ') ≤ 2 d(ϱ)`);
* `supp a_ϱ ⊆ D(ϱ)`.

For distinct `ϱ, ϱ'`, one of the two is comparable to the other.

If `ϱ'` is, every edge with a
nonzero gradient of `a_{ϱ'}` has an endpoint in `D(ϱ')` and the other in `D⁺(ϱ')`, where `a_ϱ` is
constant.

The argument is measure-agnostic: it uses no Gaussian structure, and it is the gradient
form of KP's orthogonality `⟨a_ϱ, Δ a_{ϱ'}⟩ = 0` (`Reduction.spinWave_orthogonality`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

variable {V : Type*} {E : Type*} [Fintype V] (G : Multigraph V E)

/-- Both endpoints of an edge lie in `D⁺_x(ϱ)` when one of them lies in `D_x(ϱ)`. -/
lemma endpoints_mem_densityDomainPlus {ϱ : V → ℤ} {x : V} (e : E)
    (h : G.src e ∈ G.densityDomain ϱ x ∨ G.tgt e ∈ G.densityDomain ϱ x) :
    G.src e ∈ G.densityDomainPlus ϱ x ∧ G.tgt e ∈ G.densityDomainPlus ϱ x := by
  classical
  have hst : G.toSimpleGraph.Adj (G.src e) (G.tgt e) :=
    SpinWaves.adj_toSimpleGraph G ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  rcases h with h | h
  · exact ⟨⟨G.src e, h, Or.inl rfl⟩, ⟨G.src e, h, Or.inr hst.symm⟩⟩
  · exact ⟨⟨G.tgt e, h, Or.inr hst⟩, ⟨G.tgt e, h, Or.inl rfl⟩⟩

/-- If `f` is constant on `D⁺_x(ϱ)` and `supp g ⊆ D_x(ϱ)`, then `f` has zero gradient on every
edge where `g` has a nonzero gradient. -/
lemma grad_eq_zero_of_grad_ne_zero {ϱ : V → ℤ} {x : V} {f g : V → ℝ} {c : ℝ}
    (hf : ∀ j ∈ G.densityDomainPlus ϱ x, f j = c) (hg : Function.support g ⊆ G.densityDomain ϱ x)
    (e : E) (hge : G.grad g e ≠ 0) : G.grad f e = 0 := by
  have hend : G.src e ∈ G.densityDomain ϱ x ∨ G.tgt e ∈ G.densityDomain ϱ x := by
    by_contra hc
    push Not at hc
    have hs : g (G.src e) = 0 := by
      by_contra hs; exact hc.1 (hg hs)
    have ht : g (G.tgt e) = 0 := by
      by_contra ht; exact hc.2 (hg ht)
    exact hge (by rw [Multigraph.grad, hs, ht, sub_zero])
  obtain ⟨hs, ht⟩ := endpoints_mem_densityDomainPlus G e hend
  rw [Multigraph.grad, hf _ hs, hf _ ht, sub_self]

/-- FS81 (6.20) from the clauses of KP Proposition 2.4: spin waves of distinct densities of `𝒩₀`
have disjoint gradient supports. -/
theorem grad_disjoint_of_spinWave_clauses (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (a : (V → ℤ) → V → ℝ)
    (hconst : ∀ ϱ ∈ N₀, ∀ ϱ' ∈ G.comparableDensities N₀ ϱ,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ' (centerOf ϱ'), a ϱ j = c)
    (hsupp : ∀ ϱ ∈ N₀, Function.support (a ϱ) ⊆ G.densityDomain ϱ (centerOf ϱ)) :
    ∀ ϱ ∈ N₀, ∀ ϱ' ∈ N₀, ϱ ≠ ϱ' → ∀ e, G.grad (a ϱ) e = 0 ∨ G.grad (a ϱ') e = 0 := by
  intro ϱ hϱ ϱ' hϱ' hne e
  by_cases hle : G.densityDiameter ϱ' ≤ 2 * G.densityDiameter ϱ
  · obtain ⟨c, hc⟩ := hconst ϱ hϱ ϱ' (G.mem_comparableDensities.mpr ⟨hϱ', hle, hne⟩)
    by_cases h' : G.grad (a ϱ') e = 0
    · exact Or.inr h'
    · exact Or.inl (grad_eq_zero_of_grad_ne_zero G hc (hsupp ϱ' hϱ') e h')
  · have hle' : G.densityDiameter ϱ ≤ 2 * G.densityDiameter ϱ' := by omega
    obtain ⟨c, hc⟩ := hconst ϱ' hϱ' ϱ (G.mem_comparableDensities.mpr ⟨hϱ, hle', hne.symm⟩)
    by_cases h : G.grad (a ϱ) e = 0
    · exact Or.inl h
    · exact Or.inr (grad_eq_zero_of_grad_ne_zero G hc (hsupp ϱ hϱ) e h)

end FroehlichSpencer.BKT.Generic

end
