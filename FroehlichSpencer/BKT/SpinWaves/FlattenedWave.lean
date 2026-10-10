/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Components
public import FroehlichSpencer.BKT.FiniteGraph.Basic
import FroehlichSpencer.BKT.SpinWaves.Initial

/-!
# Radial profiles flattened on the `D⁺` components (KP (4.26))

A profile depending only on the graph distance `D(j) = dist(j, s)` to a finite set
`s` is made constant on each connected component `E` of a `D⁺` union by evaluating it at one
representative `x_E ∈ E`.

The representative is chosen in the plateau `D ≤ r` if `E` meets it,
otherwise in the zero region `D ≥ S + 1` if `E` meets that, otherwise arbitrarily (the choice rule
of KP (4.26)).

The profile used here is the clamped linear ramp `ψ = clamp((S + 1 - D)/(S + 1 - r), 0, 1)`: it is
`1` on `D ≤ r`, `0` on `D ≥ S + 1`, and changes by at most `1/(S + 1 - r)` along an edge.

(KP use a
clamped logarithm; any profile with these three properties serves, and the ramp needs no
logarithm inequality, cf.

`energy_flattenedProfile_le` is the edge decomposition of  (4): an edge inside one component
contributes nothing; an edge outside all components contributes at most `1/(S+1-r)²` and only
near `s`; an edge between a component `E` and its external boundary contributes at most
`(d(E)+1)²/(S+1-r)²`, and only when `E` comes within `S + 1` of `s`.

With the endpoint-degree bound
`4`, the Dirichlet energy is at most
`4 |{D ≤ S+1}| / (S+1-r)² + ∑_{relevant E} 4 |∂^ext E| (d(E)+1)² / (S+1-r)²`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SpinWaves.P47

open Multigraph

universe u v

variable {V : Type u} {E : Type v}

/-! ## Distance to a finite set -/

/-- The graph distance from `j` to a finite set `s` (zero when `s` is empty). -/
def setDist (G : Multigraph V E) (s : Finset V) (j : V) : ℕ :=
  if h : s.Nonempty then s.inf' h (fun y => G.toSimpleGraph.dist j y) else 0

theorem setDist_le (G : Multigraph V E) {s : Finset V} {j y : V} (hy : y ∈ s) :
    setDist G s j ≤ G.toSimpleGraph.dist j y := by
  rw [setDist, dite_eq_left ⟨y, hy⟩]
  exact Finset.inf'_le _ hy

theorem exists_setDist_eq (G : Multigraph V E) {s : Finset V} (hs : s.Nonempty) (j : V) :
    ∃ y ∈ s, setDist G s j = G.toSimpleGraph.dist j y := by
  rw [setDist, dite_eq_left hs]
  exact Finset.exists_mem_eq_inf' hs _

theorem setDist_le_iff (G : Multigraph V E) {s : Finset V} (hs : s.Nonempty) (j : V) (R : ℕ) :
    setDist G s j ≤ R ↔ ∃ y ∈ s, G.toSimpleGraph.dist j y ≤ R := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := exists_setDist_eq G hs j
    exact ⟨y, hy, heq ▸ h⟩
  · rintro ⟨y, hy, h⟩
    exact (setDist_le G hy).trans h

theorem setDist_eq_zero_of_mem (G : Multigraph V E) {s : Finset V} {y : V} (hy : y ∈ s) :
    setDist G s y = 0 := by
  have := setDist_le G (j := y) hy
  rw [SimpleGraph.dist_self] at this
  omega

/-- The distance to a set is `1`-Lipschitz for the graph distance. -/
theorem setDist_le_add (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) {s : Finset V}
    (hs : s.Nonempty) (u w : V) :
    setDist G s u ≤ setDist G s w + G.toSimpleGraph.dist u w := by
  obtain ⟨y, hy, heq⟩ := exists_setDist_eq G hs w
  calc setDist G s u ≤ G.toSimpleGraph.dist u y := setDist_le G hy
    _ ≤ G.toSimpleGraph.dist u w + G.toSimpleGraph.dist w y := hG.dist_triangle
    _ = setDist G s w + G.toSimpleGraph.dist u w := by rw [heq]; ring

/-! ## The clamped ramp -/

/-- `ψ(t) = clamp((S + 1 - t)/(S + 1 - r), 0, 1)`. -/
def ramp (r S t : ℕ) : ℝ :=
  max 0 (min 1 ((((S + 1 : ℕ) : ℝ) - t) / ((S + 1 - r : ℕ) : ℝ)))

theorem ramp_eq_one {r S t : ℕ} (hrS : r ≤ S) (ht : t ≤ r) : ramp r S t = 1 := by
  have hpos : (0 : ℝ) < ((S + 1 - r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < S + 1 - r)
  have hge : (1 : ℝ) ≤ (((S + 1 : ℕ) : ℝ) - t) / ((S + 1 - r : ℕ) : ℝ) := by
    rw [le_div_iff₀ hpos, one_mul, Nat.cast_sub (by omega : r ≤ S + 1)]
    have : (t : ℝ) ≤ r := by exact_mod_cast ht
    linarith
  rw [ramp, min_eq_left hge, max_eq_right zero_le_one]

theorem ramp_eq_zero {r S t : ℕ} (hrS : r ≤ S) (ht : S + 1 ≤ t) : ramp r S t = 0 := by
  have hpos : (0 : ℝ) < ((S + 1 - r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < S + 1 - r)
  have hle : (((S + 1 : ℕ) : ℝ) - t) / ((S + 1 - r : ℕ) : ℝ) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hpos.le
    have : ((S + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  rw [ramp, min_eq_right (hle.trans zero_le_one), max_eq_left hle]

/-- The ramp is `1/(S + 1 - r)`-Lipschitz. -/
theorem abs_ramp_sub_le {r S : ℕ} (hrS : r ≤ S) (t t' : ℕ) :
    |ramp r S t - ramp r S t'| ≤ |(t : ℝ) - t'| / ((S + 1 - r : ℕ) : ℝ) := by
  have hpos : (0 : ℝ) < ((S + 1 - r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < S + 1 - r)
  set q : ℝ := ((S + 1 - r : ℕ) : ℝ)
  have hlip : ∀ x y : ℝ, |max 0 (min 1 x) - max 0 (min 1 y)| ≤ |x - y| := by
    intro x y
    have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 x) 0 (min 1 y)
    have h2 := abs_min_sub_min_le_max (1 : ℝ) x 1 y
    simp only [sub_self, abs_zero] at h1 h2
    rw [max_eq_right (abs_nonneg (min 1 x - min 1 y))] at h1
    rw [max_eq_right (abs_nonneg (x - y))] at h2
    exact h1.trans h2
  calc |ramp r S t - ramp r S t'|
      ≤ |(((S + 1 : ℕ) : ℝ) - t) / q - (((S + 1 : ℕ) : ℝ) - t') / q| := hlip _ _
    _ = |(t : ℝ) - t'| / q := by
        rw [← sub_div, abs_div, abs_of_pos hpos]
        congr 1
        rw [abs_sub_comm]
        congr 1
        ring

/-! ## Flattening on components -/

section Flatten

variable [Fintype V] (G : Multigraph V E) (N₁ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)

/-- The component of a vertex of the `D⁺` union. -/
def componentOf (j : V) (hj : j ∈ densityPlusUnion G N₁ centerOf) :
    DensityPlusComponent G N₁ centerOf :=
  (densityPlusInducedGraph G N₁ centerOf).connectedComponentMk ⟨j, hj⟩

theorem mem_componentVertices_componentOf (j : V) (hj : j ∈ densityPlusUnion G N₁ centerOf) :
    j ∈ densityPlusComponentVertices G N₁ centerOf (componentOf G N₁ centerOf j hj) :=
  (mem_densityPlusComponentVertices G N₁ centerOf _ j).2 ⟨hj, rfl⟩

theorem componentOf_eq_of_mem {c : DensityPlusComponent G N₁ centerOf} {j : V}
    (hjc : j ∈ densityPlusComponentVertices G N₁ centerOf c)
    (hj : j ∈ densityPlusUnion G N₁ centerOf) : componentOf G N₁ centerOf j hj = c := by
  obtain ⟨_, h⟩ := (mem_densityPlusComponentVertices G N₁ centerOf c j).1 hjc
  exact h

theorem componentVertices_nonempty (c : DensityPlusComponent G N₁ centerOf) :
    (densityPlusComponentVertices G N₁ centerOf c).Nonempty := by
  obtain ⟨x, rfl⟩ := c.exists_rep
  exact ⟨x.1, (mem_densityPlusComponentVertices G N₁ centerOf _ x.1).2 ⟨x.2, rfl⟩⟩

/-- Adjacent vertices of the union lie in the same component. -/
theorem componentOf_eq_of_adj {u w : V} (hu : u ∈ densityPlusUnion G N₁ centerOf)
    (hw : w ∈ densityPlusUnion G N₁ centerOf) (hadj : G.toSimpleGraph.Adj u w) :
    componentOf G N₁ centerOf u hu = componentOf G N₁ centerOf w hw := by
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  exact SimpleGraph.induce_adj.mpr hadj

/-- The KP (4.26) choice of a representative `x_E`: a plateau point (`D ≤ r`) if there is one,
else a zero-region point (`D ≥ S + 1`) if there is one, else any point of `E`. -/
def componentRep (D : V → ℕ) (r S : ℕ) (c : DensityPlusComponent G N₁ centerOf) : V := by
  classical
  exact if h₁ : ∃ x ∈ densityPlusComponentVertices G N₁ centerOf c, D x ≤ r then h₁.choose
    else if h₂ : ∃ x ∈ densityPlusComponentVertices G N₁ centerOf c, S + 1 ≤ D x then h₂.choose
    else (componentVertices_nonempty G N₁ centerOf c).choose

theorem componentRep_mem (D : V → ℕ) (r S : ℕ) (c : DensityPlusComponent G N₁ centerOf) :
    componentRep G N₁ centerOf D r S c ∈ densityPlusComponentVertices G N₁ centerOf c := by
  classical
  unfold componentRep
  split_ifs with h₁ h₂
  · exact h₁.choose_spec.1
  · exact h₂.choose_spec.1
  · exact (componentVertices_nonempty G N₁ centerOf c).choose_spec

theorem componentRep_plateau (D : V → ℕ) (r S : ℕ) (c : DensityPlusComponent G N₁ centerOf)
    (h : ∃ x ∈ densityPlusComponentVertices G N₁ centerOf c, D x ≤ r) :
    D (componentRep G N₁ centerOf D r S c) ≤ r := by
  classical
  unfold componentRep
  rw [dite_eq_left h]
  exact h.choose_spec.2

theorem componentRep_zero (D : V → ℕ) (r S : ℕ) (c : DensityPlusComponent G N₁ centerOf)
    (h₁ : ¬∃ x ∈ densityPlusComponentVertices G N₁ centerOf c, D x ≤ r)
    (h : ∃ x ∈ densityPlusComponentVertices G N₁ centerOf c, S + 1 ≤ D x) :
    S + 1 ≤ D (componentRep G N₁ centerOf D r S c) := by
  classical
  unfold componentRep
  rw [dite_eq_right h₁, dite_eq_left h]
  exact h.choose_spec.2

/-- The flattening of `f`: on each component its value at the representative, `f` elsewhere. -/
def flatten (f : V → ℝ) (rep : DensityPlusComponent G N₁ centerOf → V) (j : V) : ℝ := by
  classical
  exact if h : j ∈ densityPlusUnion G N₁ centerOf then f (rep (componentOf G N₁ centerOf j h))
    else f j

theorem flatten_of_mem_component (f : V → ℝ) (rep : DensityPlusComponent G N₁ centerOf → V)
    {c : DensityPlusComponent G N₁ centerOf} {j : V}
    (hj : j ∈ densityPlusComponentVertices G N₁ centerOf c) :
    flatten G N₁ centerOf f rep j = f (rep c) := by
  classical
  have hjU : j ∈ densityPlusUnion G N₁ centerOf :=
    ((mem_densityPlusComponentVertices G N₁ centerOf c j).1 hj).1
  rw [flatten, dite_eq_left hjU, componentOf_eq_of_mem G N₁ centerOf hj hjU]

theorem flatten_of_not_mem (f : V → ℝ) (rep : DensityPlusComponent G N₁ centerOf → V) {j : V}
    (hj : j ∉ densityPlusUnion G N₁ centerOf) : flatten G N₁ centerOf f rep j = f j := by
  classical
  rw [flatten, dite_eq_right hj]

/-- The components as a finite set (every component has a vertex in the union). -/
def componentFinset : Finset (DensityPlusComponent G N₁ centerOf) := by
  classical
  exact (densityPlusUnion G N₁ centerOf).attach.image fun j => componentOf G N₁ centerOf j.1 j.2

theorem mem_componentFinset (c : DensityPlusComponent G N₁ centerOf) :
    c ∈ componentFinset G N₁ centerOf := by
  classical
  obtain ⟨x, hx⟩ := componentVertices_nonempty G N₁ centerOf c
  have hxU := ((mem_densityPlusComponentVertices G N₁ centerOf c x).1 hx).1
  unfold componentFinset
  exact Finset.mem_image.mpr ⟨⟨x, hxU⟩, Finset.mem_attach _ _,
    componentOf_eq_of_mem G N₁ centerOf hx hxU⟩

end Flatten

/-! ## Edge counting and the energy of the flattened ramp -/

section Energy

variable [Fintype V] [DecidableEq V] [Fintype E] (G : Multigraph V E)

omit [Fintype V] in
/-- Under the endpoint-degree bound `4`, at most `4|A|` edges touch a finite set `A`. -/
theorem card_edges_touching_le
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4) (A : Finset V) :
    (Finset.univ.filter fun e => G.src e ∈ A ∨ G.tgt e ∈ A).card ≤ 4 * A.card := by
  classical
  have hsub : (Finset.univ.filter fun e => G.src e ∈ A ∨ G.tgt e ∈ A) ⊆
      A.biUnion (fun j => Finset.univ.filter fun e => G.src e = j) ∪
        A.biUnion (fun j => Finset.univ.filter fun e => G.tgt e = j) := by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨_, h, by simp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp⟩)
  calc (Finset.univ.filter fun e => G.src e ∈ A ∨ G.tgt e ∈ A).card
      ≤ (A.biUnion (fun j => Finset.univ.filter fun e => G.src e = j)).card +
          (A.biUnion (fun j => Finset.univ.filter fun e => G.tgt e = j)).card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    _ ≤ ∑ j ∈ A, (Finset.univ.filter fun e => G.src e = j).card +
          ∑ j ∈ A, (Finset.univ.filter fun e => G.tgt e = j).card :=
        Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ = ∑ j ∈ A, ((Finset.univ.filter fun e => G.src e = j).card +
          (Finset.univ.filter fun e => G.tgt e = j).card) := Finset.sum_add_distrib.symm
    _ ≤ ∑ _j ∈ A, 4 := Finset.sum_le_sum fun j _ => hdeg j
    _ = 4 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- `|D(a) - D(b)| ≤ dist(a, b)` for the distance to a nonempty set. -/
theorem abs_setDist_sub_le (hG : G.toSimpleGraph.Connected) {s : Finset V} (hs : s.Nonempty)
    (a b : V) :
    |((setDist G s a : ℕ) : ℝ) - (setDist G s b : ℕ)| ≤ (G.toSimpleGraph.dist a b : ℝ) := by
  have h1 := setDist_le_add G hG hs a b
  have h2 := setDist_le_add G hG hs b a
  rw [SimpleGraph.dist_comm] at h2
  rw [abs_le]
  constructor
  · have : ((setDist G s b : ℕ) : ℝ) ≤ setDist G s a + G.toSimpleGraph.dist a b := by
      exact_mod_cast h2
    linarith
  · have : ((setDist G s a : ℕ) : ℝ) ≤ setDist G s b + G.toSimpleGraph.dist a b := by
      exact_mod_cast h1
    linarith

variable (N₁ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)

/-- Components meeting `{D ≤ S + 1}`: the only ones whose boundary edges carry energy. -/
def relevantComponents (s : Finset V) (S : ℕ) : Finset (DensityPlusComponent G N₁ centerOf) := by
  classical
  exact (componentFinset G N₁ centerOf).filter fun c =>
    ∃ p ∈ densityPlusComponentVertices G N₁ centerOf c, setDist G s p ≤ S + 1

omit [DecidableEq V] [Fintype E] in
open scoped Classical in
/-- The boundary case of the edge decomposition: a vertex `x` of a component next to a vertex
`y`. -/
theorem sq_ramp_rep_sub_le (hG : G.toSimpleGraph.Connected) {s : Finset V} (hs : s.Nonempty)
    {r S : ℕ} (hrS : r ≤ S) {x y : V} (hxy : G.toSimpleGraph.Adj x y)
    (hx : x ∈ densityPlusUnion G N₁ centerOf) :
    (ramp r S (setDist G s (componentRep G N₁ centerOf (setDist G s) r S
        (componentOf G N₁ centerOf x hx))) - ramp r S (setDist G s y)) ^ 2 ≤
      if componentOf G N₁ centerOf x hx ∈ relevantComponents G N₁ centerOf s S then
        ((densityPlusComponentDiameter G N₁ centerOf (componentOf G N₁ centerOf x hx) : ℝ) + 1)
          ^ 2 / ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0 := by
  classical
  have hqpos : (0 : ℝ) < ((S + 1 - r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < S + 1 - r)
  have hxc := mem_componentVertices_componentOf G N₁ centerOf x hx
  have hrepc := componentRep_mem G N₁ centerOf (setDist G s) r S (componentOf G N₁ centerOf x hx)
  have hdxy : G.toSimpleGraph.dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxy
  split_ifs with hrel
  · have hdrep : G.toSimpleGraph.dist (componentRep G N₁ centerOf (setDist G s) r S
          (componentOf G N₁ centerOf x hx)) y ≤
        densityPlusComponentDiameter G N₁ centerOf (componentOf G N₁ centerOf x hx) + 1 := by
      have h1 := dist_le_densityPlusComponentDiameter G N₁ centerOf _ hrepc hxc
      have h2 := hG.dist_triangle (u := componentRep G N₁ centerOf (setDist G s) r S
        (componentOf G N₁ centerOf x hx)) (v := x) (w := y)
      omega
    have hDl := abs_setDist_sub_le G hG hs (componentRep G N₁ centerOf (setDist G s) r S
      (componentOf G N₁ centerOf x hx)) y
    have hdrepR : (G.toSimpleGraph.dist (componentRep G N₁ centerOf (setDist G s) r S
        (componentOf G N₁ centerOf x hx)) y : ℝ) ≤
        (densityPlusComponentDiameter G N₁ centerOf (componentOf G N₁ centerOf x hx) : ℝ) + 1 := by
      exact_mod_cast hdrep
    have hbound := (abs_ramp_sub_le hrS _ _).trans
      (div_le_div_of_nonneg_right (hDl.trans hdrepR) hqpos.le)
    calc _ = |ramp r S (setDist G s (componentRep G N₁ centerOf (setDist G s) r S
            (componentOf G N₁ centerOf x hx))) - ramp r S (setDist G s y)| ^ 2 := (sq_abs _).symm
      _ ≤ (((densityPlusComponentDiameter G N₁ centerOf (componentOf G N₁ centerOf x hx) : ℝ)
            + 1) / ((S + 1 - r : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbound 2
      _ = _ := div_pow _ _ _
  · have hfar : ∀ p ∈ densityPlusComponentVertices G N₁ centerOf (componentOf G N₁ centerOf x hx),
        S + 2 ≤ setDist G s p := by
      intro p hp
      by_contra hlt
      apply hrel
      unfold relevantComponents
      exact Finset.mem_filter.mpr ⟨mem_componentFinset G N₁ centerOf _, p, hp, by omega⟩
    have hrep0 := hfar _ hrepc
    have h1 := setDist_le_add G hG hs x y
    have hx2 := hfar x hxc
    rw [hdxy] at h1
    rw [ramp_eq_zero hrS (by omega), ramp_eq_zero hrS (by omega), sub_self, sq, mul_zero]

open scoped Classical in

theorem sq_flatten_ramp_edge_le (hG : G.toSimpleGraph.Connected) {s : Finset V}
    (hs : s.Nonempty) {r S : ℕ} (hrS : r ≤ S) (e : E) :
    (G.grad (flatten G N₁ centerOf (fun j => ramp r S (setDist G s j))
        (componentRep G N₁ centerOf (setDist G s) r S)) e) ^ 2 ≤
      (if setDist G s (G.src e) ≤ S + 1 then 1 / ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) +
        ∑ c ∈ relevantComponents G N₁ centerOf s S,
          (if G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
              G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c then
            ((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 /
              ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) := by
  classical
  have hqpos : (0 : ℝ) < ((S + 1 - r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < S + 1 - r)
  have hadj : G.toSimpleGraph.Adj (G.src e) (G.tgt e) :=
    adj_toSimpleGraph G ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  have hdist1 : G.toSimpleGraph.dist (G.src e) (G.tgt e) = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have hfirst_nonneg : 0 ≤ (if setDist G s (G.src e) ≤ S + 1 then
      1 / ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) := by
    split_ifs <;> positivity
  have hsum_nonneg : 0 ≤ ∑ c ∈ relevantComponents G N₁ centerOf s S,
      (if G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
          G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c then
        ((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 /
          ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) :=
    Finset.sum_nonneg fun c _ => by split_ifs <;> positivity
  -- the boundary term is one summand of the sum
  have hcomp : ∀ (x y : V) (hx : x ∈ densityPlusUnion G N₁ centerOf),
      G.toSimpleGraph.Adj x y → y ∉ densityPlusUnion G N₁ centerOf →
      (y = G.src e ∨ y = G.tgt e) →
      (if componentOf G N₁ centerOf x hx ∈ relevantComponents G N₁ centerOf s S then
        ((densityPlusComponentDiameter G N₁ centerOf (componentOf G N₁ centerOf x hx) : ℝ) + 1)
          ^ 2 / ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) ≤
      ∑ c ∈ relevantComponents G N₁ centerOf s S,
        (if G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
            G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c then
          ((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 /
            ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) := by
    intro x y hx hxy hy hyuw
    split_ifs with hrel
    · have hxc := mem_componentVertices_componentOf G N₁ centerOf x hx
      have hyB : y ∈ densityPlusExternalBoundary G N₁ centerOf (componentOf G N₁ centerOf x hx) := by
        unfold densityPlusExternalBoundary
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun h => hy ((mem_densityPlusComponentVertices G N₁ centerOf _ y).1 h).1, x, hxc,
          adj_fromSimpleGraph G hxy.symm⟩
      refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := fun c =>
        if G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
            G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c then
          ((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 /
            ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) (fun c _ => by split_ifs <;> positivity) hrel)
      rw [ite_eq_left (by rcases hyuw with h | h <;> rw [h] at hyB <;> tauto)]
    · exact hsum_nonneg
  unfold Multigraph.grad
  by_cases hu : G.src e ∈ densityPlusUnion G N₁ centerOf <;>
    by_cases hw : G.tgt e ∈ densityPlusUnion G N₁ centerOf
  · rw [flatten_of_mem_component G N₁ centerOf _ _ (mem_componentVertices_componentOf G N₁ centerOf _ hu),
      flatten_of_mem_component G N₁ centerOf _ _ (mem_componentVertices_componentOf G N₁ centerOf _ hw),
      componentOf_eq_of_adj G N₁ centerOf hu hw hadj, sub_self, sq, mul_zero]
    exact add_nonneg hfirst_nonneg hsum_nonneg
  · rw [flatten_of_mem_component G N₁ centerOf _ _ (mem_componentVertices_componentOf G N₁ centerOf _ hu),
      flatten_of_not_mem G N₁ centerOf _ _ hw]
    exact ((sq_ramp_rep_sub_le G N₁ centerOf hG hs hrS hadj hu).trans
      (hcomp _ _ hu hadj hw (Or.inr rfl))).trans (le_add_of_nonneg_left hfirst_nonneg)
  · rw [flatten_of_not_mem G N₁ centerOf _ _ hu,
      flatten_of_mem_component G N₁ centerOf _ _ (mem_componentVertices_componentOf G N₁ centerOf _ hw),
      ← neg_sub, neg_sq]
    exact ((sq_ramp_rep_sub_le G N₁ centerOf hG hs hrS hadj.symm hw).trans
      (hcomp _ _ hw hadj.symm hu (Or.inl rfl))).trans (le_add_of_nonneg_left hfirst_nonneg)
  · rw [flatten_of_not_mem G N₁ centerOf _ _ hu, flatten_of_not_mem G N₁ centerOf _ _ hw]
    refine le_trans ?_ (le_add_of_nonneg_right hsum_nonneg)
    have h1 := setDist_le_add G hG hs (G.src e) (G.tgt e)
    have h2 := setDist_le_add G hG hs (G.tgt e) (G.src e)
    rw [hdist1] at h1
    rw [SimpleGraph.dist_comm, hdist1] at h2
    by_cases hDu : setDist G s (G.src e) ≤ S + 1
    · rw [ite_eq_left hDu]
      have hDl := abs_setDist_sub_le G hG hs (G.src e) (G.tgt e)
      rw [hdist1, Nat.cast_one] at hDl
      have hb := (abs_ramp_sub_le hrS (setDist G s (G.src e)) (setDist G s (G.tgt e))).trans
        (div_le_div_of_nonneg_right hDl hqpos.le)
      calc _ = |ramp r S (setDist G s (G.src e)) - ramp r S (setDist G s (G.tgt e))| ^ 2 :=
            (sq_abs _).symm
        _ ≤ (1 / ((S + 1 - r : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = 1 / ((S + 1 - r : ℕ) : ℝ) ^ 2 := by rw [div_pow, one_pow]
    · rw [ite_eq_right hDu, ramp_eq_zero hrS (by omega), ramp_eq_zero hrS (by omega), sub_self,
        sq, mul_zero]


theorem energy_flatten_ramp_le (hG : G.toSimpleGraph.Connected)
    (hdeg : ∀ j, (Finset.univ.filter fun e => G.src e = j).card +
      (Finset.univ.filter fun e => G.tgt e = j).card ≤ 4)
    {s : Finset V} (hs : s.Nonempty) {r S : ℕ} (hrS : r ≤ S) :
    G.energy (flatten G N₁ centerOf (fun j => ramp r S (setDist G s j))
        (componentRep G N₁ centerOf (setDist G s) r S)) ≤
      4 * ((Finset.univ.filter fun j => setDist G s j ≤ S + 1).card : ℝ) /
          ((S + 1 - r : ℕ) : ℝ) ^ 2 +
        ∑ c ∈ relevantComponents G N₁ centerOf s S,
          4 * ((densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) *
            ((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 /
              ((S + 1 - r : ℕ) : ℝ) ^ 2 := by
  classical
  set q : ℝ := ((S + 1 - r : ℕ) : ℝ) with hq
  have hqpos : 0 < q := by rw [hq]; exact_mod_cast (by omega : 0 < S + 1 - r)
  set A := Finset.univ.filter fun j => setDist G s j ≤ S + 1
  unfold Multigraph.energy
  refine (Finset.sum_le_sum fun e _ => sq_flatten_ramp_edge_le G N₁ centerOf hG hs hrS e).trans ?_
  rw [Finset.sum_add_distrib]
  apply add_le_add
  · -- edges near `s`
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcount : (Finset.univ.filter fun e => setDist G s (G.src e) ≤ S + 1).card ≤ 4 * A.card :=
      (Finset.card_le_card (fun e he => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact Or.inl (by simpa [A] using he))).trans (card_edges_touching_le G hdeg A)
    have hcountR : ((Finset.univ.filter fun e => setDist G s (G.src e) ≤ S + 1).card : ℝ) ≤
        4 * (A.card : ℝ) := by exact_mod_cast hcount
    calc ((Finset.univ.filter fun e => setDist G s (G.src e) ≤ S + 1).card : ℝ) * (1 / q ^ 2)
        ≤ 4 * (A.card : ℝ) * (1 / q ^ 2) := by gcongr
      _ = 4 * (A.card : ℝ) / q ^ 2 := by ring
  · -- boundary edges of the relevant components
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcount := card_edges_touching_le G hdeg (densityPlusExternalBoundary G N₁ centerOf c)
    have hcountR : ((Finset.univ.filter fun e =>
        G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
          G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) ≤
        4 * ((densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) := by
      exact_mod_cast hcount
    have hnn : 0 ≤ ((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 / q ^ 2 := by
      positivity
    calc _ ≤ 4 * ((densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) *
          (((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 / q ^ 2) :=
          mul_le_mul_of_nonneg_right hcountR hnn
      _ = _ := by ring

end Energy

end FroehlichSpencer.BKT.SpinWaves.P47

end
