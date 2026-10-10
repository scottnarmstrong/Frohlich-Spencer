/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.DensityNeighbourhood
public import FroehlichSpencer.BKT.Charges.TorusDistance
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Finite induced components of KP's enlarged density domains

KP Lemma 4.6 (p. 24) uses the connected components of the union of the sets `D⁺(ρ)`.

We realize
that finite union as a `Finset`, then take connected components in the graph induced on its
subtype.

Thus the component carrier is genuinely finite and each component is induced and
connected.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SpinWaves

universe u v

variable {V : Type u} {E : Type v} [Fintype V]

/-- The finite union `⋃_{ρ ∈ N₀} D⁺_centerOf(ρ)(ρ)` from KP Lemma 4.6, p. 24. -/
noncomputable def densityPlusUnion (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ ρ ∈ N₀, x ∈ G.densityDomainPlus ρ (centerOf ρ)

/-- Membership in the finite union of enlarged density domains. -/
theorem mem_densityPlusUnion (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (x : V) :
    x ∈ densityPlusUnion G N₀ centerOf ↔
      ∃ ρ ∈ N₀, x ∈ G.densityDomainPlus ρ (centerOf ρ) := by
  simp [densityPlusUnion]

/-- Adding one density to the ensemble adds exactly its `D⁺` carrier to the finite union. -/
theorem mem_densityPlusUnion_insert [DecidableEq (V → ℤ)] (G : Multigraph V E)
    (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V) (ρ : V → ℤ) (x : V) :
    x ∈ densityPlusUnion G (insert ρ N₀) centerOf ↔
      x ∈ G.densityDomainPlus ρ (centerOf ρ) ∨ x ∈ densityPlusUnion G N₀ centerOf := by
  rw [mem_densityPlusUnion]
  simp only [Finset.mem_insert]
  constructor
  · rintro ⟨σ, (rfl | hσ), hx⟩
    · exact Or.inl hx
    · exact Or.inr ((mem_densityPlusUnion G N₀ centerOf x).2 ⟨σ, hσ, hx⟩)
  · rintro (hx | hx)
    · exact ⟨ρ, by simp, hx⟩
    · rcases (mem_densityPlusUnion G N₀ centerOf x).1 hx with ⟨σ, hσ, hσx⟩
      exact ⟨σ, by simp [hσ], hσx⟩

/-- The graph induced on the finite union of the `D⁺` domains. -/
noncomputable def densityPlusInducedGraph (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) : SimpleGraph (densityPlusUnion G N₀ centerOf) :=
  SimpleGraph.induce (densityPlusUnion G N₀ centerOf : Set V) G.toSimpleGraph

/-- A connected component of the finite induced union in KP Lemma 4.6. -/
abbrev DensityPlusComponent (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) :=
  (densityPlusInducedGraph G N₀ centerOf).ConnectedComponent

/-- The ambient vertex set underlying a `D⁺` component. -/
noncomputable def densityPlusComponentVertices (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c : DensityPlusComponent G N₀ centerOf) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ hx : x ∈ densityPlusUnion G N₀ centerOf,
      (densityPlusInducedGraph G N₀ centerOf).connectedComponentMk ⟨x, hx⟩ = c

/-- A vertex belongs to the component carrier precisely when its induced-graph component class
is `c`. -/
theorem mem_densityPlusComponentVertices (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c : DensityPlusComponent G N₀ centerOf) (x : V) :
    x ∈ densityPlusComponentVertices G N₀ centerOf c ↔
      ∃ hx : x ∈ densityPlusUnion G N₀ centerOf,
        (densityPlusInducedGraph G N₀ centerOf).connectedComponentMk ⟨x, hx⟩ = c := by
  simp [densityPlusComponentVertices]

/-- Every `D⁺` component is connected in its induced subgraph, by the connected-component
construction. -/
theorem densityPlusComponent_connected (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c : DensityPlusComponent G N₀ centerOf) :
    (c.toSimpleGraph).Connected :=
  SimpleGraph.ConnectedComponent.connected_toSimpleGraph c

/-- Densities whose enlarged domain lies inside one induced component of the KP union. -/
noncomputable def densitiesContainedInComponent (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c : DensityPlusComponent G N₀ centerOf) : Finset (V → ℤ) := by
  classical
  exact N₀.filter fun ρ =>
    ∀ x ∈ G.densityDomainPlus ρ (centerOf ρ),
      x ∈ densityPlusComponentVertices G N₀ centerOf c

/-- Exact membership characterization of the densities assigned to one component. -/
theorem mem_densitiesContainedInComponent (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c : DensityPlusComponent G N₀ centerOf) (ρ : V → ℤ) :
    ρ ∈ densitiesContainedInComponent G N₀ centerOf c ↔
      ρ ∈ N₀ ∧ ∀ x ∈ G.densityDomainPlus ρ (centerOf ρ),
        x ∈ densityPlusComponentVertices G N₀ centerOf c := by
  simp [densitiesContainedInComponent]

/-- Every point in a density's enlarged domain belongs to its assigned component. -/
theorem densityDomainPlus_subset_componentVertices (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c : DensityPlusComponent G N₀ centerOf)
    {ρ : V → ℤ} (hρ : ρ ∈ densitiesContainedInComponent G N₀ centerOf c) :
    G.densityDomainPlus ρ (centerOf ρ) ⊆ densityPlusComponentVertices G N₀ centerOf c := by
  exact ((mem_densitiesContainedInComponent G N₀ centerOf c ρ).1 hρ).2

/-- For a neutral density with an admissible center, every support point lies in the component
that contains its `D⁺` domain. -/
theorem densitySupport_subset_componentVertices (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected)
    (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (c : DensityPlusComponent G N₀ centerOf) {ρ : V → ℤ}
    (hρcomponent : ρ ∈ densitiesContainedInComponent G N₀ centerOf c)
    (hρneutral : ∑ x, ρ x = 0) (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    {x : V} (hx : ρ x ≠ 0) :
    x ∈ densityPlusComponentVertices G N₀ centerOf c := by
  apply densityDomainPlus_subset_componentVertices G N₀ centerOf c hρcomponent
  exact G.mem_densityDomainPlus_of_center hG hρneutral hρcenter hx

/-- The induced graph on a neutral density's enlarged domain is connected. Every point is
adjacent to the centered ball `D(ρ)`, and a shortest path from that ball point to the center stays
inside the ball (KP (1.11), (2.16); KP p. 24). -/
theorem densityDomainPlus_induce_connected [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (ρ : V → ℤ) (center : V)
    (hneutral : ∑ x, ρ x = 0) (hcenter : G.IsDensityCenter ρ center) :
    (G.toSimpleGraph.induce (G.densityDomainPlus ρ center)).Connected := by
  classical
  let A := G.densityDomainPlus ρ center
  let H := G.toSimpleGraph.induce A
  have hdiam : 1 ≤ G.densityDiameter ρ :=
    G.one_le_densityDiameter_of_neutral hG ρ (fun h => hcenter.1 (by simp [h])) hneutral
  have hcenterD : center ∈ G.densityDomain ρ center := by
    change G.toSimpleGraph.dist center center < 2 * G.densityDiameter ρ
    simp only [G.toSimpleGraph.dist_self]
    omega
  have hcenterA : center ∈ A := G.densityDomain_subset_densityDomainPlus ρ center hcenterD
  have hreach (x : A) : H.Reachable x ⟨center, hcenterA⟩ := by
    obtain ⟨m, hmD, hxm⟩ := G.mem_densityDomainPlus.mp x.2
    have hmA : m ∈ A := G.densityDomain_subset_densityDomainPlus ρ center hmD
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist m center
    have hpSupport : ∀ z ∈ p.support, z ∈ A := by
      intro z hz
      have hlen := SimpleGraph.Walk.length_dropUntil_le_length p hz
      have hdist : G.toSimpleGraph.dist z center ≤ (p.dropUntil z hz).length :=
        SimpleGraph.dist_le (p.dropUntil z hz)
      have hzD : z ∈ G.densityDomain ρ center := by
        change G.toSimpleGraph.dist z center < 2 * G.densityDiameter ρ
        change G.toSimpleGraph.dist m center < 2 * G.densityDiameter ρ at hmD
        omega
      exact G.densityDomain_subset_densityDomainPlus ρ center hzD
    have hpath : H.Reachable ⟨m, hmA⟩ ⟨center, hcenterA⟩ := by
      refine ⟨p.induce A hpSupport⟩
    have hxm' : H.Reachable x ⟨m, hmA⟩ := by
      rcases hxm with hxm | hxm
      · subst m
        exact ⟨SimpleGraph.Walk.nil⟩
      · exact ⟨(SimpleGraph.induce_adj.mpr hxm).toWalk⟩
    exact hxm'.trans hpath
  refine { preconnected := ?_, nonempty := ⟨⟨center, hcenterA⟩⟩ }
  intro x y
  exact (hreach x).trans (hreach y).symm

/-- If one point of a neutral density's enlarged domain lies in an induced-union component, the
whole enlarged domain lies in that component. -/
theorem densityDomainPlus_subset_componentVertices_of_mem [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (c : DensityPlusComponent G N₀ centerOf) {ρ : V → ℤ}
    (hρ : ρ ∈ N₀) (hneutral : ∑ x, ρ x = 0)
    (hcenter : G.IsDensityCenter ρ (centerOf ρ)) {x : V}
    (hx : x ∈ G.densityDomainPlus ρ (centerOf ρ))
    (hxc : x ∈ densityPlusComponentVertices G N₀ centerOf c) :
    G.densityDomainPlus ρ (centerOf ρ) ⊆ densityPlusComponentVertices G N₀ centerOf c := by
  have hA := densityDomainPlus_induce_connected G hG ρ (centerOf ρ) hneutral hcenter
  have hsub : G.densityDomainPlus ρ (centerOf ρ) ⊆
      (densityPlusUnion G N₀ centerOf : Set V) := by
    intro y hy
    exact (mem_densityPlusUnion G N₀ centerOf y).2 ⟨ρ, hρ, hy⟩
  intro y hy
  have hyUnion : y ∈ densityPlusUnion G N₀ centerOf := hsub hy
  have hxUnion : x ∈ densityPlusUnion G N₀ centerOf := hsub hx
  have hreachA := hA.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  have hreachUnion := hreachA.map
    (G.toSimpleGraph.induceHomOfLE hsub).toHom
  rcases (mem_densityPlusComponentVertices G N₀ centerOf c x).1 hxc with
    ⟨_, hxc'⟩
  have hcompEq :
      (densityPlusInducedGraph G N₀ centerOf).connectedComponentMk ⟨y, hyUnion⟩ =
        (densityPlusInducedGraph G N₀ centerOf).connectedComponentMk ⟨x, hxUnion⟩ :=
    SimpleGraph.ConnectedComponent.sound hreachUnion |>.symm
  apply (mem_densityPlusComponentVertices G N₀ centerOf c y).2
  exact ⟨hyUnion, hcompEq.trans hxc'⟩

/-- Every nonempty component density family has a density of maximal KP diameter. The uniqueness
of this maximizer is the additional conclusion of the L4.6 finite-scale induction. -/
theorem exists_maximalDiameter_density (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c : DensityPlusComponent G N₀ centerOf)
    (hne : (densitiesContainedInComponent G N₀ centerOf c).Nonempty) :
    ∃ ρ ∈ densitiesContainedInComponent G N₀ centerOf c,
      ∀ ρ' ∈ densitiesContainedInComponent G N₀ centerOf c,
        G.densityDiameter ρ' ≤ G.densityDiameter ρ := by
  exact Finset.exists_max_image _ G.densityDiameter hne

/-- The diameter `d(E)` of a finite `D⁺` component, measured in the ambient graph as in KP p. 24.
-/
noncomputable def densityPlusComponentDiameter (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c : DensityPlusComponent G N₀ centerOf) : ℕ := by
  classical
  let E₀ := densityPlusComponentVertices G N₀ centerOf c
  exact (E₀ ×ˢ E₀).sup fun p => G.toSimpleGraph.dist p.1 p.2

/-- Any two vertices of a component are separated by at most its diameter. -/
theorem dist_le_densityPlusComponentDiameter (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c : DensityPlusComponent G N₀ centerOf)
    {x y : V} (hx : x ∈ densityPlusComponentVertices G N₀ centerOf c)
    (hy : y ∈ densityPlusComponentVertices G N₀ centerOf c) :
    G.toSimpleGraph.dist x y ≤ densityPlusComponentDiameter G N₀ centerOf c := by
  classical
  let E₀ := densityPlusComponentVertices G N₀ centerOf c
  have hxy : (x, y) ∈ E₀ ×ˢ E₀ := Finset.mem_product.mpr ⟨hx, hy⟩
  have hle := Finset.le_sup (f := fun p => G.toSimpleGraph.dist p.1 p.2) hxy
  simpa [densityPlusComponentDiameter, E₀] using hle

/-- The graph distance between two finite component vertex sets, using the minimum convention
for distance between sets. -/
noncomputable def densityPlusComponentDistance (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c c' : DensityPlusComponent G N₀ centerOf) : ℕ := by
  classical
  let dists := ((densityPlusComponentVertices G N₀ centerOf c) ×ˢ
    (densityPlusComponentVertices G N₀ centerOf c')).image fun p =>
      G.toSimpleGraph.dist p.1 p.2
  exact if h : dists.Nonempty then dists.min' h else 0

/-- The component-set distance is no larger than any distance between chosen vertices. -/
theorem densityPlusComponentDistance_le (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c c' : DensityPlusComponent G N₀ centerOf) {x y : V}
    (hx : x ∈ densityPlusComponentVertices G N₀ centerOf c)
    (hy : y ∈ densityPlusComponentVertices G N₀ centerOf c') :
    densityPlusComponentDistance G N₀ centerOf c c' ≤ G.toSimpleGraph.dist x y := by
  classical
  let pairs := densityPlusComponentVertices G N₀ centerOf c ×ˢ
    densityPlusComponentVertices G N₀ centerOf c'
  let dists := pairs.image fun p => G.toSimpleGraph.dist p.1 p.2
  have hmem : G.toSimpleGraph.dist x y ∈ dists := by
    apply Finset.mem_image.mpr
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  have hne : dists.Nonempty := ⟨_, hmem⟩
  have hmin := Finset.min'_le dists (G.toSimpleGraph.dist x y) hmem
  change (if h : dists.Nonempty then dists.min' h else 0) ≤ _
  rw [dite_eq_left hne]
  exact hmin

/-- If both component vertex sets are nonempty, their minimum distance is attained. -/
theorem densityPlusComponentDistance_attained (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) (c c' : DensityPlusComponent G N₀ centerOf)
    (hc : (densityPlusComponentVertices G N₀ centerOf c).Nonempty)
    (hc' : (densityPlusComponentVertices G N₀ centerOf c').Nonempty) :
    ∃ x ∈ densityPlusComponentVertices G N₀ centerOf c,
      ∃ y ∈ densityPlusComponentVertices G N₀ centerOf c',
        densityPlusComponentDistance G N₀ centerOf c c' = G.toSimpleGraph.dist x y := by
  classical
  let pairs := densityPlusComponentVertices G N₀ centerOf c ×ˢ
    densityPlusComponentVertices G N₀ centerOf c'
  let dists := pairs.image fun p => G.toSimpleGraph.dist p.1 p.2
  have hpairs : pairs.Nonempty := by
    rcases hc with ⟨x, hx⟩
    rcases hc' with ⟨y, hy⟩
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  have hdists : dists.Nonempty := Finset.image_nonempty.mpr hpairs
  let dist := dists.min' hdists
  have hdist : dist ∈ dists := Finset.min'_mem dists hdists
  rcases Finset.mem_image.mp hdist with ⟨⟨x, y⟩, hp, hxy⟩
  rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
  refine ⟨x, hx, y, hy, ?_⟩
  simpa [densityPlusComponentDistance, pairs, dists, hdists] using hxy.symm

/-- The distance from a finite `D⁺` component to the support of a distinguished density. -/
noncomputable def densityPlusComponentRootDistance [DecidableEq V]
    (G : Multigraph V E) (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (c : DensityPlusComponent G N₀ centerOf) (ρstar : V → ℤ) : ℕ := by
  classical
  let roots := Finset.univ.filter fun y => ρstar y ≠ 0
  let dists := ((densityPlusComponentVertices G N₀ centerOf c) ×ˢ roots).image fun p =>
    G.toSimpleGraph.dist p.1 p.2
  exact if h : dists.Nonempty then dists.min' h else 0

/-- If the component and distinguished support are nonempty, their minimum distance is attained.
-/
theorem densityPlusComponentRootDistance_attained [DecidableEq V]
    (G : Multigraph V E) (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (c : DensityPlusComponent G N₀ centerOf) (ρstar : V → ℤ)
    (hc : (densityPlusComponentVertices G N₀ centerOf c).Nonempty)
    (hroot : ∃ y, ρstar y ≠ 0) :
    ∃ x ∈ densityPlusComponentVertices G N₀ centerOf c, ∃ y, ρstar y ≠ 0 ∧
      densityPlusComponentRootDistance G N₀ centerOf c ρstar = G.toSimpleGraph.dist x y := by
  classical
  let roots := Finset.univ.filter fun y => ρstar y ≠ 0
  let pairs := densityPlusComponentVertices G N₀ centerOf c ×ˢ roots
  let dists := pairs.image fun p => G.toSimpleGraph.dist p.1 p.2
  have hpairs : pairs.Nonempty := by
    rcases hc with ⟨x, hx⟩
    rcases hroot with ⟨y, hy⟩
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩⟩
  have hdists : dists.Nonempty := Finset.image_nonempty.mpr hpairs
  let dist := dists.min' hdists
  have hdist : dist ∈ dists := Finset.min'_mem dists hdists
  rcases Finset.mem_image.mp hdist with ⟨⟨x, y⟩, hp, hxy⟩
  rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
  refine ⟨x, hx, y, (Finset.mem_filter.mp hy).2, ?_⟩
  simpa [densityPlusComponentRootDistance, roots, pairs, dists, hdists] using hxy.symm

/-- The external vertex boundary of a `D⁺` component: vertices outside it adjacent to a component
vertex (KP p. 24). -/
noncomputable def densityPlusExternalBoundary [Fintype E] (G : Multigraph V E)
    (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (c : DensityPlusComponent G N₀ centerOf) : Finset V := by
  classical
  let E₀ := densityPlusComponentVertices G N₀ centerOf c
  exact Finset.univ.filter fun x => x ∉ E₀ ∧ ∃ y ∈ E₀, G.Adj x y


theorem squarePeriodic_component_distance (L : ℕ) (x y : Fin L × Fin L) :
    (squarePeriodic L).toSimpleGraph.dist x y =
      cyclicDist L x.1 y.1 + cyclicDist L x.2 y.2 :=
  squarePeriodic_dist_eq_cyclicDist L x y

/--
The graph distance between the supports of two densities, with the KP graph distance
and the minimum convention for distance between sets.

This is an internal candidate for the
set-distance notation in Theorem 2.2(b).
-/
noncomputable def densitySupportDistance {E : Type v} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (ρ σ : V → ℤ) : ℕ := by
  classical
  let distances := ((Finset.univ.filter fun x => ρ x ≠ 0) ×ˢ
    (Finset.univ.filter fun y => σ y ≠ 0)).image fun p =>
      G.toSimpleGraph.dist p.1 p.2
  exact if h : distances.Nonempty then distances.min' h else 0

/--
Exact KP set-distance characterization of `densitySupportDistance`: it is the minimum of the
 graph distances over `supp ρ × supp σ` (and equals zero for an empty support).
-/
theorem densitySupportDistance_eq_support_minimum {E : Type v} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (ρ σ : V → ℤ) :
    densitySupportDistance G ρ σ =
      (let distances := ((Finset.univ.filter fun x => ρ x ≠ 0) ×ˢ
        (Finset.univ.filter fun y => σ y ≠ 0)).image
          (fun p => G.toSimpleGraph.dist p.1 p.2)
       if h : distances.Nonempty then distances.min' h else 0) := rfl

/-- If both supports are nonempty, `densitySupportDistance` is attained by support points. -/
theorem densitySupportDistance_attained {E : Type v} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (ρ σ : V → ℤ)
    (hρ : ∃ x, ρ x ≠ 0) (hσ : ∃ y, σ y ≠ 0) :
    ∃ x y, ρ x ≠ 0 ∧ σ y ≠ 0 ∧
      densitySupportDistance G ρ σ = G.toSimpleGraph.dist x y := by
  classical
  obtain ⟨x, hx⟩ := hρ
  obtain ⟨y, hy⟩ := hσ
  let supportPair := (Finset.univ.filter fun x => ρ x ≠ 0) ×ˢ
    (Finset.univ.filter fun y => σ y ≠ 0)
  let distances := supportPair.image fun p => G.toSimpleGraph.dist p.1 p.2
  have hxmem : x ∈ Finset.univ.filter fun x => ρ x ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hymem : y ∈ Finset.univ.filter fun y => σ y ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  have hdistances : distances.Nonempty := by
    refine ⟨G.toSimpleGraph.dist x y, ?_⟩
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hxmem, hymem⟩, rfl⟩
  have hmin := Finset.min'_mem distances hdistances
  rcases Finset.mem_image.mp hmin with ⟨⟨a, b⟩, hab, hminEq⟩
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  refine ⟨a, b, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, ?_⟩
  simpa [densitySupportDistance, supportPair, distances, hdistances] using hminEq.symm

/-- The set-distance minimum is no larger than the distance between any chosen support points.
-/
theorem densitySupportDistance_le {E : Type v} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (ρ σ : V → ℤ) {x y : V}
    (hx : ρ x ≠ 0) (hy : σ y ≠ 0) :
    densitySupportDistance G ρ σ ≤ G.toSimpleGraph.dist x y := by
  classical
  let supportPair := (Finset.univ.filter fun x => ρ x ≠ 0) ×ˢ
    (Finset.univ.filter fun y => σ y ≠ 0)
  let distances := supportPair.image fun p => G.toSimpleGraph.dist p.1 p.2
  have hxmem : x ∈ Finset.univ.filter fun x => ρ x ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hymem : y ∈ Finset.univ.filter fun y => σ y ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  have hmem : G.toSimpleGraph.dist x y ∈ distances :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hxmem, hymem⟩, rfl⟩
  have hdistances : distances.Nonempty := ⟨_, hmem⟩
  have hmin := Finset.min'_le distances (G.toSimpleGraph.dist x y) hmem
  change (if h : distances.Nonempty then distances.min' h else 0) ≤ _
  rw [dite_eq_left hdistances]
  exact hmin

/-- For neutral densities assigned to two components, their support distance is at most the
component distance plus the two component diameters. -/
theorem densitySupportDistance_le_componentDistance_add {E : Type v} [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (c c' : DensityPlusComponent G N₀ centerOf) {ρ σ : V → ℤ}
    (hρcomponent : ρ ∈ densitiesContainedInComponent G N₀ centerOf c)
    (hσcomponent : σ ∈ densitiesContainedInComponent G N₀ centerOf c')
    (hρneutral : ∑ x, ρ x = 0) (hσneutral : ∑ x, σ x = 0)
    (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    (hσcenter : G.IsDensityCenter σ (centerOf σ))
    (hρsupport : ∃ x, ρ x ≠ 0) (hσsupport : ∃ y, σ y ≠ 0) :
    densitySupportDistance G ρ σ ≤
      densityPlusComponentDistance G N₀ centerOf c c' +
        densityPlusComponentDiameter G N₀ centerOf c +
        densityPlusComponentDiameter G N₀ centerOf c' := by
  obtain ⟨x, hx⟩ := hρsupport
  obtain ⟨y, hy⟩ := hσsupport
  have hxcomp := densitySupport_subset_componentVertices G hG N₀ centerOf c
    hρcomponent hρneutral hρcenter hx
  have hycomp := densitySupport_subset_componentVertices G hG N₀ centerOf c'
    hσcomponent hσneutral hσcenter hy
  have hcompNonempty : (densityPlusComponentVertices G N₀ centerOf c).Nonempty := ⟨x, hxcomp⟩
  have hcomp'Nonempty : (densityPlusComponentVertices G N₀ centerOf c').Nonempty := ⟨y, hycomp⟩
  obtain ⟨u, hu, v, hv, huv⟩ := densityPlusComponentDistance_attained
    G N₀ centerOf c c' hcompNonempty hcomp'Nonempty
  have hxu : G.toSimpleGraph.dist x u ≤ densityPlusComponentDiameter G N₀ centerOf c :=
    dist_le_densityPlusComponentDiameter G N₀ centerOf c hxcomp hu
  have hyv : G.toSimpleGraph.dist v y ≤ densityPlusComponentDiameter G N₀ centerOf c' := by
    rw [G.toSimpleGraph.dist_comm]
    exact dist_le_densityPlusComponentDiameter G N₀ centerOf c' hycomp hv
  have hxy : G.toSimpleGraph.dist x y ≤
      densityPlusComponentDiameter G N₀ centerOf c +
        densityPlusComponentDistance G N₀ centerOf c c' +
        densityPlusComponentDiameter G N₀ centerOf c' := by
    calc
      G.toSimpleGraph.dist x y ≤ G.toSimpleGraph.dist x u + G.toSimpleGraph.dist u y :=
        hG.dist_triangle (u := x) (v := u) (w := y)
      _ ≤ G.toSimpleGraph.dist x u +
          (G.toSimpleGraph.dist u v + G.toSimpleGraph.dist v y) :=
        Nat.add_le_add_left (hG.dist_triangle (u := u) (v := v) (w := y)) _
      _ ≤ _ := by rw [huv]; omega
  exact (densitySupportDistance_le G ρ σ hx hy).trans (by omega)

/-- For a neutral density assigned to a component, its support distance to a distinguished
density is at most the component-to-support distance plus the component diameter. -/
theorem densitySupportDistance_le_componentRootDistance_add {E : Type v} [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (N₀ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (c : DensityPlusComponent G N₀ centerOf) {ρ ρstar : V → ℤ}
    (hρcomponent : ρ ∈ densitiesContainedInComponent G N₀ centerOf c)
    (hρneutral : ∑ x, ρ x = 0) (hρcenter : G.IsDensityCenter ρ (centerOf ρ))
    (hρsupport : ∃ x, ρ x ≠ 0) (hrootSupport : ∃ y, ρstar y ≠ 0) :
    densitySupportDistance G ρ ρstar ≤
      densityPlusComponentRootDistance G N₀ centerOf c ρstar +
        densityPlusComponentDiameter G N₀ centerOf c := by
  obtain ⟨x, hx⟩ := hρsupport
  have hxcomp := densitySupport_subset_componentVertices G hG N₀ centerOf c
    hρcomponent hρneutral hρcenter hx
  have hcompNonempty : (densityPlusComponentVertices G N₀ centerOf c).Nonempty := ⟨x, hxcomp⟩
  obtain ⟨u, hu, y, hy, huy⟩ := densityPlusComponentRootDistance_attained
    G N₀ centerOf c ρstar hcompNonempty hrootSupport
  have hxu : G.toSimpleGraph.dist x u ≤ densityPlusComponentDiameter G N₀ centerOf c :=
    dist_le_densityPlusComponentDiameter G N₀ centerOf c hxcomp hu
  have hxy : G.toSimpleGraph.dist x y ≤
      densityPlusComponentDiameter G N₀ centerOf c +
        densityPlusComponentRootDistance G N₀ centerOf c ρstar := by
    calc
      G.toSimpleGraph.dist x y ≤ G.toSimpleGraph.dist x u + G.toSimpleGraph.dist u y :=
        hG.dist_triangle (u := x) (v := u) (w := y)
      _ ≤ densityPlusComponentDiameter G N₀ centerOf c +
          densityPlusComponentRootDistance G N₀ centerOf c ρstar := by
        rw [← huy]
        exact Nat.add_le_add_right hxu _
  exact (densitySupportDistance_le G ρ ρstar hx hy).trans (by omega)

/--
The single named T2.2(b) input for Lemma 4.6.

For two neutral densities it gives KP's
`M[min(d(ρ),d(σ))]^α` separation; for a neutral density and the distinguished charged density it
gives KP's `M d(ρ)^α` separation.

Distances are the graph distances between supports.
-/
structure KPTheorem22bSeparation {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (N₀ : Finset (V → ℤ))
    (ρstar : V → ℤ) (M α : ℝ) : Prop where
  /-- T2.2(b), neutral-neutral pair case. -/
  neutral_pair : ∀ ρ ∈ N₀, ∀ σ ∈ N₀, ρ ≠ σ →
    M * (↑(min (G.densityDiameter ρ) (G.densityDiameter σ)) : ℝ) ^ α ≤
      (↑(densitySupportDistance G ρ σ) : ℝ)
  /-- T2.2(b), a neutral density separated from the distinguished charged density. -/
  root_pair : ∀ ρ ∈ N₀, ρ ≠ ρstar →
    M * (↑(G.densityDiameter ρ) : ℝ) ^ α ≤
      (↑(densitySupportDistance G ρ ρstar) : ℝ)

/-- Pointwise T2.2(b) separation for two neutral supports, extracted from the single named
`KPTheorem22bSeparation` input. -/
theorem KPTheorem22bSeparation.neutral_support_distance {E : Type v}
    [Fintype E] [DecidableEq V] {G : Multigraph V E} {N₀ : Finset (V → ℤ)}
    {ρstar ρ σ : V → ℤ} {M α : ℝ}
    (hsep : KPTheorem22bSeparation G N₀ ρstar M α)
    (hρ : ρ ∈ N₀) (hσ : σ ∈ N₀) (hne : ρ ≠ σ)
    {x y : V} (hx : ρ x ≠ 0) (hy : σ y ≠ 0) :
    M * (↑(min (G.densityDiameter ρ) (G.densityDiameter σ)) : ℝ) ^ α ≤
      (↑(G.toSimpleGraph.dist x y) : ℝ) := by
  exact le_trans (hsep.neutral_pair ρ hρ σ hσ hne) <|
    Nat.cast_le.mpr (densitySupportDistance_le G ρ σ hx hy)

/-- Pointwise T2.2(b) separation from the distinguished charged density, extracted from the
single named `KPTheorem22bSeparation` input. -/
theorem KPTheorem22bSeparation.root_support_distance {E : Type v}
    [Fintype E] [DecidableEq V] {G : Multigraph V E} {N₀ : Finset (V → ℤ)}
    {ρstar ρ : V → ℤ} {M α : ℝ}
    (hsep : KPTheorem22bSeparation G N₀ ρstar M α)
    (hρ : ρ ∈ N₀) (hne : ρ ≠ ρstar) {x y : V}
    (hx : ρ x ≠ 0) (hy : ρstar y ≠ 0) :
    M * (↑(G.densityDiameter ρ) : ℝ) ^ α ≤
      (↑(G.toSimpleGraph.dist x y) : ℝ) := by
  exact le_trans (hsep.root_pair ρ hρ hne) <|
    Nat.cast_le.mpr (densitySupportDistance_le G ρ ρstar hx hy)

/-- On a connected finite graph, each enlarged density domain has KP diameter at most `4d(ρ)`.
The two unit enlargements contribute one each, and the centered domain has radius `<2d(ρ)`.
-/
theorem densityDomainPlus_diameter_le_four {E : Type v} [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (ρ : V → ℤ) (center : V) {x y : V}
    (hx : x ∈ G.densityDomainPlus ρ center) (hy : y ∈ G.densityDomainPlus ρ center) :
    G.toSimpleGraph.dist x y ≤ 4 * G.densityDiameter ρ := by
  obtain ⟨a, ha, hxa⟩ := (G.mem_densityDomainPlus_iff_dist hG).mp hx
  obtain ⟨b, hb, hyb⟩ := (G.mem_densityDomainPlus_iff_dist hG).mp hy
  have hab : G.toSimpleGraph.dist a b ≤
      G.toSimpleGraph.dist a center + G.toSimpleGraph.dist center b :=
    hG.dist_triangle (u := a) (v := center) (w := b)
  have hxy : G.toSimpleGraph.dist x y ≤
      G.toSimpleGraph.dist x a + G.toSimpleGraph.dist a b +
        G.toSimpleGraph.dist b y := by
    calc
      G.toSimpleGraph.dist x y ≤
          G.toSimpleGraph.dist x a + G.toSimpleGraph.dist a y :=
        hG.dist_triangle (u := x) (v := a) (w := y)
      _ ≤ G.toSimpleGraph.dist x a +
          (G.toSimpleGraph.dist a b + G.toSimpleGraph.dist b y) := by
        exact Nat.add_le_add_left (hG.dist_triangle (u := a) (v := b) (w := y)) _
      _ = _ := by simp [Nat.add_assoc]
  have hxa' : G.toSimpleGraph.dist x a ≤ 1 := hxa
  have hyb' : G.toSimpleGraph.dist b y ≤ 1 := by
    rw [G.toSimpleGraph.dist_comm]
    exact hyb
  change G.toSimpleGraph.dist a center < 2 * G.densityDiameter ρ at ha
  change G.toSimpleGraph.dist b center < 2 * G.densityDiameter ρ at hb
  have hb' : G.toSimpleGraph.dist center b < 2 * G.densityDiameter ρ := by
    rwa [G.toSimpleGraph.dist_comm]
  omega

/--
If T2.2(b)'s support separation exceeds the two `D⁺` diameter bounds, the enlarged density
domains are disjoint.
-/
theorem densityDomainPlus_disjoint_of_scale {E : Type v} [Fintype E] [DecidableEq V]
    {G : Multigraph V E} {N₀ : Finset (V → ℤ)} {ρstar ρ σ : V → ℤ} {M α : ℝ}
    (hsep : KPTheorem22bSeparation G N₀ ρstar M α)
    (hG : G.toSimpleGraph.Connected) {centerρ centerσ : V}
    (hρmem : ρ ∈ N₀) (hσmem : σ ∈ N₀) (hne : ρ ≠ σ)
    (hρneutral : ∑ x, ρ x = 0) (hσneutral : ∑ x, σ x = 0)
    (hρcenter : G.IsDensityCenter ρ centerρ) (hσcenter : G.IsDensityCenter σ centerσ)
    (hscale : (↑(4 * G.densityDiameter ρ + 4 * G.densityDiameter σ) : ℝ) <
      M * (↑(min (G.densityDiameter ρ) (G.densityDiameter σ)) : ℝ) ^ α) :
    Disjoint (G.densityDomainPlus ρ centerρ) (G.densityDomainPlus σ centerσ) := by
  rw [Set.disjoint_left]
  intro x hxρ hxσ
  have hcρ : centerρ ∈ G.densityDomainPlus ρ centerρ :=
    G.mem_densityDomainPlus_of_center hG hρneutral hρcenter hρcenter.1
  have hcσ : centerσ ∈ G.densityDomainPlus σ centerσ :=
    G.mem_densityDomainPlus_of_center hG hσneutral hσcenter hσcenter.1
  have hρx := densityDomainPlus_diameter_le_four G hG ρ centerρ hcρ hxρ
  have hxσ := densityDomainPlus_diameter_le_four G hG σ centerσ hxσ hcσ
  have hgeom : G.toSimpleGraph.dist centerρ centerσ ≤
      4 * G.densityDiameter ρ + 4 * G.densityDiameter σ := by
    calc
      G.toSimpleGraph.dist centerρ centerσ ≤
          G.toSimpleGraph.dist centerρ x + G.toSimpleGraph.dist x centerσ :=
        hG.dist_triangle (u := centerρ) (v := x) (w := centerσ)
      _ ≤ 4 * G.densityDiameter ρ + 4 * G.densityDiameter σ := Nat.add_le_add hρx hxσ
  have hsupport := hsep.neutral_support_distance hρmem hσmem hne hρcenter.1 hσcenter.1
  have hreal : (↑(G.toSimpleGraph.dist centerρ centerσ) : ℝ) ≤
      ↑(4 * G.densityDiameter ρ + 4 * G.densityDiameter σ) := by exact_mod_cast hgeom
  have hcontr := le_trans hsupport hreal
  exact (not_lt_of_ge hcontr) hscale

/-- Distinct neutral enlarged domains cannot even be adjacent when their T2.2(b) support
separation exceeds both diameter bounds and one edge. This is the exclusion used when adjoining
one density to a finite union in the proof of KP Lemma 4.6. -/
theorem densityDomainPlus_no_adj_of_scale {E : Type v} [Fintype E] [DecidableEq V]
    {G : Multigraph V E} {N₀ : Finset (V → ℤ)} {ρstar ρ σ : V → ℤ} {M α : ℝ}
    (hsep : KPTheorem22bSeparation G N₀ ρstar M α)
    (hG : G.toSimpleGraph.Connected) {centerρ centerσ x y : V}
    (hρmem : ρ ∈ N₀) (hσmem : σ ∈ N₀) (hne : ρ ≠ σ)
    (hρneutral : ∑ z, ρ z = 0) (hσneutral : ∑ z, σ z = 0)
    (hρcenter : G.IsDensityCenter ρ centerρ) (hσcenter : G.IsDensityCenter σ centerσ)
    (hx : x ∈ G.densityDomainPlus ρ centerρ) (hy : y ∈ G.densityDomainPlus σ centerσ)
    (hxy : G.toSimpleGraph.Adj x y)
    (hscale : (↑(4 * G.densityDiameter ρ + 4 * G.densityDiameter σ + 1) : ℝ) <
      M * (↑(min (G.densityDiameter ρ) (G.densityDiameter σ)) : ℝ) ^ α) : False := by
  have hcρ : centerρ ∈ G.densityDomainPlus ρ centerρ :=
    G.mem_densityDomainPlus_of_center hG hρneutral hρcenter hρcenter.1
  have hcσ : centerσ ∈ G.densityDomainPlus σ centerσ :=
    G.mem_densityDomainPlus_of_center hG hσneutral hσcenter hσcenter.1
  have hρx := densityDomainPlus_diameter_le_four G hG ρ centerρ hcρ hx
  have hyσ := densityDomainPlus_diameter_le_four G hG σ centerσ hy hcσ
  have hdist : G.toSimpleGraph.dist centerρ centerσ ≤
      4 * G.densityDiameter ρ + 4 * G.densityDiameter σ + 1 := by
    calc
      G.toSimpleGraph.dist centerρ centerσ ≤
          G.toSimpleGraph.dist centerρ x + G.toSimpleGraph.dist x y +
            G.toSimpleGraph.dist y centerσ := by
        calc
          G.toSimpleGraph.dist centerρ centerσ ≤
              G.toSimpleGraph.dist centerρ x + G.toSimpleGraph.dist x centerσ :=
            hG.dist_triangle (u := centerρ) (v := x) (w := centerσ)
          _ ≤ G.toSimpleGraph.dist centerρ x +
              (G.toSimpleGraph.dist x y + G.toSimpleGraph.dist y centerσ) :=
            Nat.add_le_add_left (hG.dist_triangle (u := x) (v := y) (w := centerσ)) _
          _ = _ := by omega
      _ ≤ 4 * G.densityDiameter ρ + 1 + 4 * G.densityDiameter σ := by
        have hxy' : G.toSimpleGraph.dist x y = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr hxy
        omega
      _ = _ := by omega
  have hsupport := hsep.neutral_support_distance hρmem hσmem hne hρcenter.1 hσcenter.1
  have hreal : (↑(G.toSimpleGraph.dist centerρ centerσ) : ℝ) ≤
      ↑(4 * G.densityDiameter ρ + 4 * G.densityDiameter σ + 1) := by exact_mod_cast hdist
  exact (not_lt_of_ge (le_trans hsupport hreal)) hscale

end FroehlichSpencer.BKT.SpinWaves

end
