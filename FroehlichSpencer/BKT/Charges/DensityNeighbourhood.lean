/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ChargeEnsemble
public import FroehlichSpencer.BKT.Surface.DensityDomain
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import FroehlichSpencer.BKT.Charges.DensityRouting

/-!
# Neutral subensembles, comparable densities and enlarged domains

KP §2.3, pp. 11–12 (Kharash–Peled, first version):

* (2.13) the neutral part `𝒩₀` of an ensemble (KP write `𝒩₀ = 𝒩 ∖ {ϱ_c}`, which is the
  neutral part when `𝒩` has at most one non-neutral density, Theorem 2.2(a));
* (2.15) `𝒩₀(ϱ) = {ϱ' ∈ 𝒩₀ : d(ϱ') ≤ 2 d(ϱ), ϱ ≠ ϱ'}`;
* (2.16) `D⁺(ϱ) = {j ∈ Λ : dist (j, D(ϱ)) ≤ 1}`.

All three are stated on the carriers: `Multigraph`, `Multigraph.densityDiameter` and the
centered domain `Multigraph.densityDomain` of KP (1.11).

`D⁺` is defined with the center `j` of
`D_j(ϱ)` explicit, as for the domain.

The point-to-set distance is unfolded as "equal to
or adjacent to a point of `D_j(ϱ)`"; on a connected graph this is `dist ≤ 1`
(`Multigraph.mem_densityDomainPlus_iff_dist`).
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

/-- The neutral part of a finite family of densities (KP (2.13)). -/
def neutralPart {V : Type u} [Fintype V] (N : Finset (V → ℤ)) : Finset (V → ℤ) :=
  N.filter fun ϱ => ∑ j, ϱ j = 0

theorem mem_neutralPart {V : Type u} [Fintype V] {N : Finset (V → ℤ)} {ϱ : V → ℤ} :
    ϱ ∈ neutralPart N ↔ ϱ ∈ N ∧ ∑ j, ϱ j = 0 :=
  Finset.mem_filter

theorem neutralPart_subset {V : Type u} [Fintype V] (N : Finset (V → ℤ)) :
    neutralPart N ⊆ N :=
  Finset.filter_subset _ _

/-- A subfamily of an ensemble is an ensemble; in particular the neutral part. -/
theorem IsChargeEnsemble.neutralPart {V : Type u} [Fintype V] {N : Finset (V → ℤ)}
    (hN : IsChargeEnsemble N) : IsChargeEnsemble (neutralPart N) :=
  ⟨fun ϱ hϱ => hN.1 ϱ (neutralPart_subset N hϱ),
    fun ϱ₁ h₁ ϱ₂ h₂ => hN.2 ϱ₁ (neutralPart_subset N h₁) ϱ₂ (neutralPart_subset N h₂)⟩

/-- KP (2.13): if `ϱ_c` is non-neutral and every non-neutral density of `𝒩` equals `ϱ_c`, the
neutral part is `𝒩 ∖ {ϱ_c}`. -/
theorem neutralPart_eq_erase {V : Type u} [Fintype V] [DecidableEq (V → ℤ)]
    {N : Finset (V → ℤ)} {ϱc : V → ℤ} (hcQ : ∑ j, ϱc j ≠ 0)
    (honly : ∀ ϱ ∈ N, ∑ j, ϱ j ≠ 0 → ϱ = ϱc) : neutralPart N = N.erase ϱc := by
  ext ϱ
  rw [mem_neutralPart, Finset.mem_erase]
  constructor
  · rintro ⟨hϱ, hQ⟩
    exact ⟨fun h => hcQ (h ▸ hQ), hϱ⟩
  · rintro ⟨hne, hϱ⟩
    exact ⟨hϱ, by_contra fun hQ => hne (honly ϱ hϱ hQ)⟩

/-- KP (2.13): if every density of `𝒩` is neutral, the neutral part is `𝒩`. -/
theorem neutralPart_eq_self {V : Type u} [Fintype V] {N : Finset (V → ℤ)}
    (hN : ∀ ϱ ∈ N, ∑ j, ϱ j = 0) : neutralPart N = N :=
  Finset.filter_true_of_mem hN

namespace Multigraph

variable {V : Type u} {E : Type v} [Fintype V] (G : Multigraph V E)

/-- KP (2.15): the densities of `𝒩₀` other than `ϱ` whose diameter is at most `2 d(ϱ)`. -/
noncomputable def comparableDensities (N₀ : Finset (V → ℤ)) (ϱ : V → ℤ) : Finset (V → ℤ) := by
  classical
  exact N₀.filter fun ϱ' => G.densityDiameter ϱ' ≤ 2 * G.densityDiameter ϱ ∧ ϱ ≠ ϱ'

theorem mem_comparableDensities {N₀ : Finset (V → ℤ)} {ϱ ϱ' : V → ℤ} :
    ϱ' ∈ G.comparableDensities N₀ ϱ ↔
      ϱ' ∈ N₀ ∧ G.densityDiameter ϱ' ≤ 2 * G.densityDiameter ϱ ∧ ϱ ≠ ϱ' := by
  classical
  simp [comparableDensities]

theorem comparableDensities_subset (N₀ : Finset (V → ℤ)) (ϱ : V → ℤ) :
    G.comparableDensities N₀ ϱ ⊆ N₀ := fun _ h =>
  ((G.mem_comparableDensities).1 h).1

/-- KP (2.16): `D⁺_j(ϱ)`, the vertices at graph distance at most one from the centered domain
`D_j(ϱ)`, written as "equal or adjacent to a point of `D_j(ϱ)`". -/
def densityDomainPlus (ϱ : V → ℤ) (j : V) : Set V :=
  {ℓ | ∃ m ∈ G.densityDomain ϱ j, ℓ = m ∨ G.toSimpleGraph.Adj ℓ m}

theorem mem_densityDomainPlus {ϱ : V → ℤ} {j ℓ : V} :
    ℓ ∈ G.densityDomainPlus ϱ j ↔
      ∃ m ∈ G.densityDomain ϱ j, ℓ = m ∨ G.toSimpleGraph.Adj ℓ m :=
  Iff.rfl

theorem densityDomain_subset_densityDomainPlus (ϱ : V → ℤ) (j : V) :
    G.densityDomain ϱ j ⊆ G.densityDomainPlus ϱ j := fun ℓ hℓ =>
  ⟨ℓ, hℓ, Or.inl rfl⟩

/-- On a connected graph, `D⁺_j(ϱ)` is `{ℓ : dist (ℓ, D_j(ϱ)) ≤ 1}` (KP (2.16)). -/
theorem mem_densityDomainPlus_iff_dist (hG : G.toSimpleGraph.Connected) {ϱ : V → ℤ}
    {j ℓ : V} :
    ℓ ∈ G.densityDomainPlus ϱ j ↔ ∃ m ∈ G.densityDomain ϱ j, G.toSimpleGraph.dist ℓ m ≤ 1 := by
  refine exists_congr fun m => and_congr_right fun _ => ?_
  constructor
  · rintro (rfl | hadj)
    · simp
    · exact (SimpleGraph.dist_eq_one_iff_adj.mpr hadj).le
  · intro hle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · exact Or.inl ((hG.preconnected ℓ m).dist_eq_zero_iff.mp h0)
    · exact Or.inr (SimpleGraph.dist_eq_one_iff_adj.mp h1)

/-- A vertex of `D⁺_j(ϱ)` is within distance `2 d(ϱ)` of the center. -/
theorem dist_le_of_mem_densityDomainPlus (hG : G.toSimpleGraph.Connected) {ϱ : V → ℤ}
    {j ℓ : V} (hℓ : ℓ ∈ G.densityDomainPlus ϱ j) :
    G.toSimpleGraph.dist ℓ j ≤ 2 * G.densityDiameter ϱ := by
  obtain ⟨m, hm, hle⟩ := (G.mem_densityDomainPlus_iff_dist hG).1 hℓ
  have htri := hG.dist_triangle (u := ℓ) (v := m) (w := j)
  have hm' : G.toSimpleGraph.dist m j < 2 * G.densityDiameter ϱ := hm
  omega

/-- On a connected graph, the support of a nonzero neutral density lies in its domain
`D_j(ϱ)` for every admissible center `j` (KP p. 5). -/
theorem mem_densityDomain_of_center (hG : G.toSimpleGraph.Connected) {ϱ : V → ℤ}
    (hsum : ∑ x, ϱ x = 0) {j : V} (hj : G.IsDensityCenter ϱ j) {x : V} (hx : ϱ x ≠ 0) :
    x ∈ G.densityDomain ϱ j := by
  have hd := G.one_le_densityDiameter_of_neutral hG ϱ (fun h => hj.1 (by simp [h])) hsum
  have hx' := G.dist_le_densityDiameter_of_center ϱ j hj x hx
  show G.toSimpleGraph.dist x j < 2 * G.densityDiameter ϱ
  omega

/-- On a connected graph, the support of a nonzero neutral density lies in `D⁺_j(ϱ)`. -/
theorem mem_densityDomainPlus_of_center (hG : G.toSimpleGraph.Connected) {ϱ : V → ℤ}
    (hsum : ∑ x, ϱ x = 0) {j : V} (hj : G.IsDensityCenter ϱ j) {x : V} (hx : ϱ x ≠ 0) :
    x ∈ G.densityDomainPlus ϱ j :=
  G.densityDomain_subset_densityDomainPlus ϱ j (G.mem_densityDomain_of_center hG hsum hj hx)

end Multigraph

end FroehlichSpencer.BKT

end
