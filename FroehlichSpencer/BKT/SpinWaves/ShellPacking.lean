/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Lemma46Arithmetic
public import FroehlichSpencer.BKT.Lattice2D.LogLowerBound
public import FroehlichSpencer.BKT.Charges.TorusDistance
public import FroehlichSpencer.BKT.Charges.L41Span
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds
public import FroehlichSpencer.BKT.Bridge.SquareCarriers

/-!
# Shell packing input for KP Lemma 4.6

The shell counts below use the free and periodic square carriers.

The separated-path
lemma is the one-dimensional packing step used on the at most four clipped sides of a free
diamond shell (or on a periodic shell cycle), as in  and
-/

@[expose] public section

namespace FroehlichSpencer.BKT.SpinWaves

universe u v

open Lattice2D

private theorem natDist_eq_intAbs_toNat (a b : ℕ) :
    Nat.dist a b = (|((a : ℤ) - b)|).toNat := by
  by_cases hab : a ≤ b
  · rw [Nat.dist_eq_sub_of_le hab]
    have hnonpos : (a : ℤ) - (b : ℤ) ≤ 0 := by omega
    rw [abs_of_nonpos hnonpos]
    have hcast : ((b - a : ℕ) : ℤ) = (b : ℤ) - a := by omega
    have hdiff : -((a : ℤ) - b) = (b : ℤ) - a := by ring
    rw [hdiff, ← hcast, Int.toNat_natCast]
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    rw [Nat.dist_eq_sub_of_le_right hba]
    have hnonneg : 0 ≤ (a : ℤ) - (b : ℤ) := by omega
    rw [abs_of_nonneg hnonneg]
    have hcast : ((a - b : ℕ) : ℤ) = (a : ℤ) - b := by omega
    rw [← hcast, Int.toNat_natCast]

private theorem squareFreeEdge_coordinate_dist_sum_eq_one {L : ℕ}
    (e : SquareFreeEdge L) :
    Nat.dist e.1.1.1.val e.1.2.1.val +
      Nat.dist e.1.1.2.val e.1.2.2.val = 1 := by
  have hshape := e.property.2
  let dx : ℤ := |(e.1.1.1.val : ℤ) - e.1.2.1.val|
  let dy : ℤ := |(e.1.1.2.val : ℤ) - e.1.2.2.val|
  have hshape' : ({dx, dy} : Finset ℤ) = {0, 1} := by
    simpa [dx, dy] using hshape
  have hdxmem : dx ∈ ({0, 1} : Finset ℤ) := by
    rw [← hshape']
    simp [dx]
  have hdymem : dy ∈ ({0, 1} : Finset ℤ) := by
    rw [← hshape']
    simp [dy]
  have hdx : dx = 0 ∨ dx = 1 := by simpa using hdxmem
  have hdy : dy = 0 ∨ dy = 1 := by simpa using hdymem
  have hnot00 : ¬ (dx = 0 ∧ dy = 0) := by
    rintro ⟨hdx0, hdy0⟩
    rw [hdx0, hdy0] at hshape'
    have hone : (1 : ℤ) ∈ ({0, 1} : Finset ℤ) := by simp
    rw [← hshape'] at hone
    simp at hone
  have hnot11 : ¬ (dx = 1 ∧ dy = 1) := by
    rintro ⟨hdx1, hdy1⟩
    rw [hdx1, hdy1] at hshape'
    have hzero : (0 : ℤ) ∈ ({0, 1} : Finset ℤ) := by simp
    rw [← hshape'] at hzero
    simp at hzero
  have hsum : dx.toNat + dy.toNat = 1 := by
    rcases hdx with hdx | hdx <;> rcases hdy with hdy | hdy
    · exact False.elim (hnot00 ⟨hdx, hdy⟩)
    · rw [hdx, hdy]
      norm_num
    · rw [hdx, hdy]
      norm_num
    · exact False.elim (hnot11 ⟨hdx, hdy⟩)
  rw [natDist_eq_intAbs_toNat, natDist_eq_intAbs_toNat]
  change dx.toNat + dy.toNat = 1
  exact hsum

private theorem squareFree_adj_coordinate_dist_sum_eq_one {L : ℕ}
    {x y : SquareFreeVertex L}
    (hxy : (squareFree L).toSimpleGraph.Adj x y) :
    Nat.dist x.1.val y.1.val + Nat.dist x.2.val y.2.val = 1 := by
  rcases (freeAdj_iff_edgeRelation L x y).mp hxy with ⟨_, e, he | he⟩
  · rw [← he.1, ← he.2]
    exact squareFreeEdge_coordinate_dist_sum_eq_one e
  · rw [← he.1, ← he.2]
    simpa [Nat.dist_comm] using squareFreeEdge_coordinate_dist_sum_eq_one e

private theorem natAbsDiff_eq_natDist (a b : ℕ) :
    (if a ≤ b then b - a else a - b) = Nat.dist a b := by
  by_cases hab : a ≤ b
  · simp [hab, Nat.dist_eq_sub_of_le hab]
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    simp [hab, Nat.dist_eq_sub_of_le_right hba]

private theorem freeRadius_triangle {L : ℕ} (p q r : SquareFreeVertex L) :
    freeRadius p r ≤ freeRadius p q + freeRadius q r := by
  unfold freeRadius
  have h₁ := Nat.dist.triangle_inequality p.1.val q.1.val r.1.val
  have h₂ := Nat.dist.triangle_inequality p.2.val q.2.val r.2.val
  omega

private theorem freeRadius_le_walk_length {L : ℕ} {p q : SquareFreeVertex L}
    (w : (squareFree L).toSimpleGraph.Walk p q) : freeRadius p q ≤ w.length := by
  induction w with
  | nil => simp [freeRadius]
  | @cons a b c hab tail ih =>
      have hstep : freeRadius a b = 1 :=
        squareFree_adj_coordinate_dist_sum_eq_one hab
      calc
        freeRadius a c ≤ freeRadius a b + freeRadius b c := freeRadius_triangle a b c
        _ ≤ 1 + tail.length := by rw [hstep]; exact Nat.add_le_add_left ih 1
        _ = (SimpleGraph.Walk.cons hab tail).length := by simp [Nat.add_comm]

/-- The finite external vertex boundary of one canonical enlarged density domain. -/
noncomputable def densityDomainPlusExternalBoundary {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] (G : Multigraph V E) (ρ : V → ℤ) (j : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    x ∉ G.densityDomainPlus ρ j ∧
      ∃ y ∈ G.densityDomainPlus ρ j, G.toSimpleGraph.Adj x y

theorem mem_densityDomainPlusExternalBoundary {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] (G : Multigraph V E) (ρ : V → ℤ) (j x : V) :
    x ∈ densityDomainPlusExternalBoundary G ρ j ↔
      x ∉ G.densityDomainPlus ρ j ∧
        ∃ y ∈ G.densityDomainPlus ρ j, G.toSimpleGraph.Adj x y := by
  simp [densityDomainPlusExternalBoundary]

private theorem exists_adjacent_firstStep_of_pos_dist {V : Type u}
    (G : SimpleGraph V) (hG : G.Connected) {x z : V} (hpos : 0 < G.dist x z) :
    ∃ y, G.Adj x y ∧ G.dist y z + 1 = G.dist x z := by
  obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist x z
  cases w with
  | nil => simp at hpos
  | @cons a b c hab tail =>
      have hlen : tail.length + 1 = G.dist x z := by simpa using hw
      have hxb : G.dist x b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab
      have htri : G.dist x z ≤ G.dist x b + G.dist b z :=
        SimpleGraph.Connected.dist_triangle hG
      have htri' : G.dist x z ≤ 1 + G.dist b z := by rw [hxb] at htri; exact htri
      have htail : G.dist b z ≤ tail.length := SimpleGraph.dist_le tail
      refine ⟨b, hab, ?_⟩
      omega

private theorem mem_densityDomainPlus_iff_dist_le {V : Type u} {E : Type v}
    [Fintype V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    {ρ : V → ℤ} {j x : V} (hdiam : 1 ≤ G.densityDiameter ρ) :
    x ∈ G.densityDomainPlus ρ j ↔
      G.toSimpleGraph.dist x j ≤ 2 * G.densityDiameter ρ := by
  constructor
  · exact G.dist_le_of_mem_densityDomainPlus hG
  · intro hdist
    by_cases hlt : G.toSimpleGraph.dist x j < 2 * G.densityDiameter ρ
    · exact G.densityDomain_subset_densityDomainPlus ρ j hlt
    · have heq : G.toSimpleGraph.dist x j = 2 * G.densityDiameter ρ := by omega
      have hpos : 0 < G.toSimpleGraph.dist x j := by rw [heq]; omega
      obtain ⟨y, hxy, hy⟩ := exists_adjacent_firstStep_of_pos_dist
        G.toSimpleGraph hG hpos
      have hyD : y ∈ G.densityDomain ρ j := by
        change G.toSimpleGraph.dist y j < 2 * G.densityDiameter ρ
        omega
      exact G.mem_densityDomainPlus.2 ⟨y, hyD, Or.inr hxy⟩

/--
The external vertex boundary of `D⁺_j(ρ)` is exactly the graph-distance sphere of radius
`2 d(ρ)+1`.

This uses only the definition (2.16) and geodesics in the connected graph.
-/
theorem mem_densityDomainPlusExternalBoundary_iff_dist_eq {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (ρ : V → ℤ) (j x : V) (hdiam : 1 ≤ G.densityDiameter ρ) :
    x ∈ densityDomainPlusExternalBoundary G ρ j ↔
      G.toSimpleGraph.dist x j = 2 * G.densityDiameter ρ + 1 := by
  rw [mem_densityDomainPlusExternalBoundary]
  constructor
  · rintro ⟨hxout, y, hy, hxy⟩
    have hxball := (mem_densityDomainPlus_iff_dist_le G hG hdiam).not.mp hxout
    have hyball := (mem_densityDomainPlus_iff_dist_le G hG hdiam).mp hy
    have hxgt : 2 * G.densityDiameter ρ < G.toSimpleGraph.dist x j :=
      Nat.lt_of_not_ge hxball
    have hxy' : G.toSimpleGraph.dist x y = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hxy
    have htriangle : G.toSimpleGraph.dist x j ≤
        G.toSimpleGraph.dist x y + G.toSimpleGraph.dist y j :=
      SimpleGraph.Connected.dist_triangle hG
    omega
  · intro hx
    have hxout : x ∉ G.densityDomainPlus ρ j := by
      intro hxmem
      have hxball := (mem_densityDomainPlus_iff_dist_le G hG hdiam).mp hxmem
      omega
    have hpos : 0 < G.toSimpleGraph.dist x j := by rw [hx]; omega
    obtain ⟨y, hxy, hy⟩ := exists_adjacent_firstStep_of_pos_dist G.toSimpleGraph hG hpos
    have hyball : G.toSimpleGraph.dist y j ≤ 2 * G.densityDiameter ρ := by omega
    have hymem : y ∈ G.densityDomainPlus ρ j :=
      (mem_densityDomainPlus_iff_dist_le G hG hdiam).2 hyball
    exact ⟨hxout, y, hymem, hxy⟩

private theorem exists_room_in_one_direction (L r : ℕ) (hL : 2 * r < L)
    (a : Fin L) : r ≤ a.val ∨ r ≤ L - 1 - a.val := by
  by_contra h
  have ha : a.val < r := by omega
  have hright : L - 1 - a.val < r := by omega
  omega

/-- Move a coordinate by `t` units in a direction that has room for `r` steps. -/
private def freeCoordMove {L : ℕ} (a : Fin L) (r : ℕ)
    (hroom : r ≤ a.val ∨ r ≤ L - 1 - a.val) (t : ℕ) (ht : t ≤ r) : Fin L := by
  classical
  by_cases hleft : r ≤ a.val
  · exact ⟨a.val - t, by omega⟩
  · have hright : r ≤ L - 1 - a.val := hroom.resolve_left hleft
    exact ⟨a.val + t, by omega⟩

private theorem freeCoordMove_val {L : ℕ} (a : Fin L) (r : ℕ)
    (hroom : r ≤ a.val ∨ r ≤ L - 1 - a.val) (t : ℕ) (ht : t ≤ r) :
    (freeCoordMove a r hroom t ht).val = if r ≤ a.val then a.val - t else a.val + t := by
  by_cases hleft : r ≤ a.val
  · simp [freeCoordMove, hleft]
  · simp [freeCoordMove, hleft]

private theorem natDist_freeCoordMove {L : ℕ} (a : Fin L) (r : ℕ)
    (hroom : r ≤ a.val ∨ r ≤ L - 1 - a.val) (t : ℕ) (ht : t ≤ r) :
    Nat.dist a.val (freeCoordMove a r hroom t ht).val = t := by
  rw [freeCoordMove_val]
  by_cases h : r ≤ a.val
  · simp [h, Nat.dist]
    omega
  · have hr := hroom.resolve_left h
    simp [h, Nat.dist]

private theorem freeCoordMove_injective {L : ℕ} (a : Fin L) (r : ℕ)
    (hroom : r ≤ a.val ∨ r ≤ L - 1 - a.val) :
    Function.Injective (fun t : Fin (r + 1) => freeCoordMove a r hroom t.1 (by omega)) := by
  intro t u h
  have ht := congrArg Fin.val h
  rw [freeCoordMove_val, freeCoordMove_val] at ht
  by_cases hleft : r ≤ a.val
  · simp [hleft] at ht
    exact Fin.ext (by omega)
  · simp [hleft] at ht
    exact Fin.ext (by omega)

/-- The free square's radius-`r` shell has at least `r+1` points whenever the square has room
for a radius-`r` diamond. The witnesses run along one clipped diamond side. -/
theorem freeRadius_shell_card_ge {L : ℕ} (p : SquareFreeVertex L) (r : ℕ)
    (hL : 2 * r < L) :
    r + 1 ≤ (Finset.univ.filter (fun x : SquareFreeVertex L => freeRadius p x = r)).card := by
  classical
  let hx := exists_room_in_one_direction L r hL p.1
  let hy := exists_room_in_one_direction L r hL p.2
  let point : Fin (r + 1) → SquareFreeVertex L := fun t =>
    (freeCoordMove p.1 r hx t.1 (by omega),
      freeCoordMove p.2 r hy (r - t.1) (by omega))
  have hpoint : ∀ t, freeRadius p (point t) = r := by
    intro t
    simp only [point, freeRadius]
    rw [natDist_freeCoordMove p.1 r hx t.1 (by omega),
      natDist_freeCoordMove p.2 r hy (r - t.1) (by omega)]
    omega
  have hinj : Function.Injective point := by
    intro t u htu
    have hfirst := congrArg Prod.fst htu
    exact freeCoordMove_injective p.1 r hx hfirst
  let f : Fin (r + 1) → ↥(Finset.univ.filter
      (fun x : SquareFreeVertex L => freeRadius p x = r)) := fun t =>
    ⟨point t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpoint t⟩⟩
  have hf : Function.Injective f := by
    intro t u h
    exact hinj (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f hf
  calc
    r + 1 = Fintype.card (Fin (r + 1)) := by simp
    _ ≤ Fintype.card ↥(Finset.univ.filter
        (fun x : SquareFreeVertex L => freeRadius p x = r)) := hcard
    _ = (Finset.univ.filter
        (fun x : SquareFreeVertex L => freeRadius p x = r)).card :=
          Fintype.card_coe _

private theorem torusRadius_adj_change_le {L : ℕ} [NeZero L] (hL : 2 < L)
    (p x y : TorusVertex L)
    (hxy : (torusGraph L hL).toSimpleGraph.Adj x y) :
    torusRadius p x ≤ torusRadius p y + 1 ∧ torusRadius p y ≤ torusRadius p x + 1 := by
  change (SimpleGraph.fromRel (Multigraph.Adj (torusGraph L hL))).Adj x y at hxy
  have hxy' : x ≠ y ∧
      (Multigraph.Adj (torusGraph L hL) x y ∨ Multigraph.Adj (torusGraph L hL) y x) := by
    exact (SimpleGraph.fromRel_adj _ _ _).mp hxy
  have hadj : Multigraph.Adj (torusGraph L hL) x y := by
    rcases hxy'.2 with h | h
    · exact h
    · rcases h with ⟨e, he | he⟩
      · exact ⟨e, Or.inr he⟩
      · exact ⟨e, Or.inl he⟩
  rcases hadj with ⟨e, he | he⟩
  · have hs := torusRadius_edge_step hL p e
    rw [he.1, he.2] at hs
    exact hs
  · have hs := torusRadius_edge_step hL p e
    rw [he.2, he.1] at hs
    exact ⟨hs.2, hs.1⟩

private theorem torusRadius_le_walk_length {L : ℕ} [NeZero L] (hL : 2 < L)
    (p x y : TorusVertex L)
    (w : (torusGraph L hL).toSimpleGraph.Walk x y) :
    torusRadius p y ≤ torusRadius p x + w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab tail ih =>
      calc
        torusRadius p c ≤ torusRadius p b + tail.length := ih
        _ ≤ torusRadius p a + 1 + tail.length :=
          Nat.add_le_add_right (torusRadius_adj_change_le hL p a b hab).2 _
        _ = torusRadius p a + (tail.length + 1) := by omega

/-- On the internal right/up torus carrier, graph distance is the coordinate cyclic radius.
The lower inequality follows by applying the one-step radius bound along a shortest walk. -/
theorem torusGraph_dist_eq_torusRadius {L : ℕ} [NeZero L] (hL : 2 < L)
    (p q : TorusVertex L) :
    (torusGraph L hL).toSimpleGraph.dist p q = torusRadius p q := by
  apply le_antisymm
  · exact torus_distance_le_radius hL p q
  · obtain ⟨w, hw⟩ := (torusGraph_connected L hL).exists_walk_length_eq_dist p q
    have h := torusRadius_le_walk_length hL p p q w
    rw [hw] at h
    have hself : torusRadius p p = 0 := by simp [torusRadius, torusCoordDistance]
    rw [hself] at h
    omega

/--
The periodic carrier's graph-distance sphere has the usual square-torus shell
cardinality bound.
-/
theorem squarePeriodic_distShell_card_le {L : ℕ} [NeZero L] (hL : 2 < L)
    (p : Fin L × Fin L) (r : ℕ) :
    (Finset.univ.filter (fun x : Fin L × Fin L =>
      (squarePeriodic L).toSimpleGraph.dist p x = r)).card ≤ 4 * (r + 1) := by
  classical
  let I := squarePeriodicTorusIsomorphism (L := L) hL
  let target := Finset.univ.filter (fun y : TorusVertex L =>
    torusRadius (I.vertices p) y = r)
  let f : ↥(Finset.univ.filter (fun x : Fin L × Fin L =>
      (squarePeriodic L).toSimpleGraph.dist p x = r)) → ↥target := fun x =>
    ⟨I.vertices x.1, by
      have hdist := I.dist_eq (squarePeriodic_connected L (by omega)) p x.1
      change I.vertices x.1 ∈ Finset.univ.filter
        (fun y : TorusVertex L => torusRadius (I.vertices p) y = r)
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · rw [← torusGraph_dist_eq_torusRadius hL (I.vertices p) (I.vertices x.1), hdist]
        exact (Finset.mem_filter.mp x.2).2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact I.vertices.injective (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f hf
  calc
    (Finset.univ.filter (fun x : Fin L × Fin L =>
        (squarePeriodic L).toSimpleGraph.dist p x = r)).card
      = Fintype.card ↥(Finset.univ.filter (fun x : Fin L × Fin L =>
          (squarePeriodic L).toSimpleGraph.dist p x = r)) := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ↥target := hcard
    _ = target.card := Fintype.card_coe _
    _ ≤ 4 * (r + 1) := by
      simpa [target] using torusRadius_shell_card_le (I.vertices p) r

private def torusShellPoint {L : ℕ} [NeZero L] (p : TorusVertex L) (r : ℕ)
    (t : Fin (r + 1)) : TorusVertex L :=
  (p.1 + (t.val : ZMod L), p.2 + ((r - t.val : ℕ) : ZMod L))

private theorem torusRadius_torusShellPoint {L : ℕ} [NeZero L]
    (p : TorusVertex L) (r : ℕ) (hL : 2 * r < L) (t : Fin (r + 1)) :
    torusRadius p (torusShellPoint p r t) = r := by
  have ht : t.val < L := by omega
  have hu : r - t.val < L := by omega
  have htHalf : t.val ≤ L - t.val := by omega
  have huHalf : r - t.val ≤ L - (r - t.val) := by omega
  have hfirst : ((torusShellPoint p r t).1 - p.1).val = t.val := by
    dsimp [torusShellPoint]
    rw [add_sub_cancel_left, ZMod.val_natCast_of_lt ht]
  have hsecond : ((torusShellPoint p r t).2 - p.2).val = r - t.val := by
    dsimp [torusShellPoint]
    rw [add_sub_cancel_left, ZMod.val_natCast_of_lt hu]
  simp only [torusRadius, torusCoordDistance, hfirst, hsecond,
    Nat.min_eq_left htHalf, Nat.min_eq_left huHalf]
  omega

private theorem torusShellPoint_injective {L : ℕ} [NeZero L]
    (p : TorusVertex L) (r : ℕ) (hL : 2 * r < L) :
    Function.Injective (torusShellPoint p r) := by
  intro t u htu
  have hfirst := congrArg Prod.fst htu
  have hcast : (t.val : ZMod L) = (u.val : ZMod L) := add_left_cancel hfirst
  have htL : t.val < L := by omega
  have huL : u.val < L := by omega
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt htL, ZMod.val_natCast_of_lt huL] at hval
  exact Fin.ext hval

/-- The internal periodic radius-`r` shell has at least `r+1` points when `L>2r`. -/
theorem torusRadius_shell_card_ge {L : ℕ} [NeZero L]
    (p : TorusVertex L) (r : ℕ) (hL : 2 * r < L) :
    r + 1 ≤ (Finset.univ.filter (fun x : TorusVertex L => torusRadius p x = r)).card := by
  classical
  let f : Fin (r + 1) → ↥(Finset.univ.filter
      (fun x : TorusVertex L => torusRadius p x = r)) := fun t =>
    ⟨torusShellPoint p r t,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, torusRadius_torusShellPoint p r hL t⟩⟩
  have hf : Function.Injective f := by
    intro t u h
    exact torusShellPoint_injective p r hL (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f hf
  calc
    r + 1 = Fintype.card (Fin (r + 1)) := by simp
    _ ≤ Fintype.card ↥(Finset.univ.filter
        (fun x : TorusVertex L => torusRadius p x = r)) := hcard
    _ = (Finset.univ.filter
        (fun x : TorusVertex L => torusRadius p x = r)).card := Fintype.card_coe _

/--
The periodic radius-`r` shell has at least `r+1` points under `L>2r`.
-/
theorem squarePeriodic_distShell_card_ge {L : ℕ} [NeZero L] (hside : 2 < L)
    (p : Fin L × Fin L) (r : ℕ) (hL : 2 * r < L) :
    r + 1 ≤ (Finset.univ.filter (fun x : Fin L × Fin L =>
      (squarePeriodic L).toSimpleGraph.dist p x = r)).card := by
  classical
  let I := squarePeriodicTorusIsomorphism (L := L) hside
  let source := Finset.univ.filter (fun y : TorusVertex L =>
    torusRadius (I.vertices p) y = r)
  let target := Finset.univ.filter (fun x : Fin L × Fin L =>
    (squarePeriodic L).toSimpleGraph.dist p x = r)
  let f : ↥source → ↥target := fun y =>
    ⟨I.vertices.symm y.1, by
      have hdist := I.dist_eq (squarePeriodic_connected L (by omega)) p (I.vertices.symm y.1)
      have happly : I.vertices (I.vertices.symm y.1) = y.1 := I.vertices.apply_symm_apply _
      rw [happly, torusGraph_dist_eq_torusRadius hside] at hdist
      change I.vertices.symm y.1 ∈ Finset.univ.filter
        (fun x : Fin L × Fin L => (squarePeriodic L).toSimpleGraph.dist p x = r)
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · rw [← hdist]
        exact (Finset.mem_filter.mp y.2).2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact I.vertices.symm.injective (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f hf
  have hsource := torusRadius_shell_card_ge (I.vertices p) r hL
  calc
    r + 1 ≤ source.card := by simpa [source] using hsource
    _ = Fintype.card ↥source := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ↥target := hcard
    _ = target.card := Fintype.card_coe _

/--
On the free square, graph distance is the coordinate Manhattan distance.
-/
theorem squareFree_dist_eq_freeRadius {L : ℕ} (hL : 1 < L)
    (p q : SquareFreeVertex L) :
    (squareFree L).toSimpleGraph.dist p q = freeRadius p q := by
  apply le_antisymm
  · have h := freeDistance_le_coordinateSum L p q
    change (squareFree L).toSimpleGraph.dist p q ≤ _ at h
    have hcoord :
        (if p.1.val ≤ q.1.val then q.1.val - p.1.val else p.1.val - q.1.val) +
        (if p.2.val ≤ q.2.val then q.2.val - p.2.val else p.2.val - q.2.val) =
          freeRadius p q := by
      simp only [freeRadius]
      rw [← natAbsDiff_eq_natDist p.1.val q.1.val,
        ← natAbsDiff_eq_natDist p.2.val q.2.val]
    rw [hcoord] at h
    exact h
  · obtain ⟨w, hw⟩ := (squareFree_connected L hL).exists_walk_length_eq_dist p q
    have hwalk := freeRadius_le_walk_length w
    simpa [hw] using hwalk

/-- A subset of a finite path whose distinct selected vertices are at graph distance at least
`s` has at most `n / s + 1` members.  This is the pathwise packing estimate used in  -/
theorem card_finset_of_natDist_separated_le (n s : ℕ) (hs : 0 < s)
    (S : Finset (Fin n))
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → s ≤ Nat.dist i.val j.val) :
    S.card ≤ n / s + 1 := by
  classical
  let code : ↥S → Fin (n / s + 1) := fun i =>
    ⟨i.1.val / s, Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.le_of_lt i.1.isLt))⟩
  have hcode : Function.Injective code := by
    intro i j hij
    have hq : i.1.val / s = j.1.val / s := congrArg Fin.val hij
    by_contra hneSubtype
    have hne : i.1 ≠ j.1 := by
      intro heq
      exact hneSubtype (Subtype.ext heq)
    have hsep' := hsep i.1 i.2 j.1 j.2 hne
    have hmodi := Nat.mod_lt i.1.val hs
    have hmodj := Nat.mod_lt j.1.val hs
    have hdeci := Nat.mod_add_div i.1.val s
    have hdecj := Nat.mod_add_div j.1.val s
    rw [← hq] at hdecj
    have hdist : Nat.dist i.1.val j.1.val < s := by
      rw [Nat.dist]
      omega
    omega
  have hcard := Fintype.card_le_of_injective code hcode
  simpa [code] using hcard

/-- A pathwise packing bound when ambient graph distance is at most twice the difference of the
path parameters, as on one side of a Manhattan diamond. -/
theorem card_finset_of_doubledNatDist_separated_le (n s : ℕ) (hs : 0 < s)
    (S : Finset (Fin n))
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → s ≤ 2 * Nat.dist i.val j.val) :
    S.card ≤ n / ((s + 1) / 2) + 1 := by
  let q := (s + 1) / 2
  have hq : 0 < q := by dsimp [q]; omega
  have hsep' : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → q ≤ Nat.dist i.val j.val := by
    intro i hi j hj hne
    have h := hsep i hi j hj hne
    dsimp [q]
    omega
  simpa [q] using card_finset_of_natDist_separated_le n q hq S hsep'

/--
's free clipped-rectangle shell bound, in the `freeRadius` coordinates of the
free square.

Clipping by the rectangle only removes points from the full-grid shell.
-/
theorem freeClippedRectangle_shell_card_le {L : ℕ} (p : SquareFreeVertex L) (k : ℕ) :
    (Finset.univ.filter (fun x : SquareFreeVertex L => freeRadius p x = k)).card ≤
      4 * (k + 1) :=
  freeRadius_shell_card_le p k

/--
's periodic shell count on the torus, using cyclic `ℓ¹` distance.
-/
theorem periodicCyclicShell_card_le {L : ℕ} [NeZero L] (p : TorusVertex L) (k : ℕ) :
    (Finset.univ.filter (fun x : TorusVertex L => torusRadius p x = k)).card ≤
      4 * (k + 1) :=
  torusRadius_shell_card_le p k


def lemma46StrongBoundaryInvariant {V : Type u} {E : Type v} [Fintype V]
    [Fintype E] (G : Multigraph V E) (I : Finset (V → ℤ))
    (centerOf : (V → ℤ) → V) : Prop :=
  ∀ c : DensityPlusComponent G I centerOf,
    (densitiesContainedInComponent G I centerOf c).Nonempty →
      ∃ ρ ∈ densitiesContainedInComponent G I centerOf c,
        (∀ σ ∈ densitiesContainedInComponent G I centerOf c,
          σ ≠ ρ → G.densityDiameter σ < G.densityDiameter ρ) ∧
        densityPlusComponentDiameter G I centerOf c ≤ 5 * G.densityDiameter ρ ∧
        (densityPlusExternalBoundary G I centerOf c).card ≤ 16 * G.densityDiameter ρ

/-- If the inductive shell estimate is available for a component, its external boundary satisfies
the third conclusion of KP Lemma 4.6.  The comparison `d(ρ_E) ≤ d(E)` follows because the support
of the centered neutral density lies in its `D⁺` component.  The constants leave the source's
stronger `16 d(ρ_E)` estimate intact and yield the requested `64 d(E)` form. -/
theorem lemma46_externalBoundary_card_le_of_strongInvariant
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    {G : Multigraph V E} (hG : G.toSimpleGraph.Connected)
    (I : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (hneutral : ∀ ρ ∈ I, ∑ x, ρ x = 0)
    (hcenter : ∀ ρ ∈ I, G.IsDensityCenter ρ (centerOf ρ))
    (hstrong : lemma46StrongBoundaryInvariant G I centerOf)
    (c : DensityPlusComponent G I centerOf)
    (hfamily : (densitiesContainedInComponent G I centerOf c).Nonempty) :
    (densityPlusExternalBoundary G I centerOf c).card ≤
      64 * densityPlusComponentDiameter G I centerOf c := by
  obtain ⟨ρ, hρ, _, _, hboundary⟩ := hstrong c hfamily
  have hρI : ρ ∈ I :=
    (mem_densitiesContainedInComponent G I centerOf c ρ).1 hρ |>.1
  have hρsupport : ∀ x, ρ x ≠ 0 →
      x ∈ densityPlusComponentVertices G I centerOf c := by
    intro x hx
    exact densitySupport_subset_componentVertices G hG I centerOf c hρ
      (hneutral ρ hρI) (hcenter ρ hρI) hx
  have hρdiam : G.densityDiameter ρ ≤ densityPlusComponentDiameter G I centerOf c := by
    unfold Multigraph.densityDiameter
    apply Finset.sup_le
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    have hp₁' : ρ p.1 ≠ 0 := (Finset.mem_filter.mp hp₁).2
    have hp₂' : ρ p.2 ≠ 0 := (Finset.mem_filter.mp hp₂).2
    exact dist_le_densityPlusComponentDiameter G I centerOf c
      (hρsupport p.1 hp₁') (hρsupport p.2 hp₂')
  calc
    (densityPlusExternalBoundary G I centerOf c).card ≤ 16 * G.densityDiameter ρ :=
      hboundary
    _ ≤ 16 * densityPlusComponentDiameter G I centerOf c :=
      Nat.mul_le_mul_left 16 hρdiam
    _ ≤ 64 * densityPlusComponentDiameter G I centerOf c := by omega

/--
: on the free square, the external boundary of `D⁺_j(ρ)` is exactly the
graph-distance sphere of radius `2d(ρ)+1`.
-/
theorem squareFree_densityDomainPlusExternalBoundary_iff_dist_eq {L : ℕ}
    (ρ : SquareFreeVertex L → ℤ) (hρ : ρ ≠ 0) (hneutral : ∑ x, ρ x = 0)
    (j x : SquareFreeVertex L)
    (hL : 2 * (2 * (squareFree L).densityDiameter ρ + 1) < L) :
    x ∈ densityDomainPlusExternalBoundary (squareFree L) ρ j ↔
      (squareFree L).toSimpleGraph.dist x j = 2 * (squareFree L).densityDiameter ρ + 1 := by
  have hside : 1 < L := by omega
  have hconn := squareFree_connected L hside
  have hdiam := (squareFree L).one_le_densityDiameter_of_neutral hconn ρ hρ hneutral
  exact mem_densityDomainPlusExternalBoundary_iff_dist_eq
    (squareFree L) hconn ρ j x hdiam

/--
: periodic -carrier counterpart of
`squareFree_densityDomainPlusExternalBoundary_iff_dist_eq`.
-/
theorem squarePeriodic_densityDomainPlusExternalBoundary_iff_dist_eq {L : ℕ} [NeZero L]
    (ρ : (Fin L × Fin L) → ℤ) (hρ : ρ ≠ 0) (hneutral : ∑ x, ρ x = 0)
    (j x : Fin L × Fin L)
    (hL : 2 * (2 * (squarePeriodic L).densityDiameter ρ + 1) < L) :
    x ∈ densityDomainPlusExternalBoundary (squarePeriodic L) ρ j ↔
      (squarePeriodic L).toSimpleGraph.dist x j =
        2 * (squarePeriodic L).densityDiameter ρ + 1 := by
  have hside : 2 < L := by omega
  have hconn := squarePeriodic_connected L (by omega)
  have hdiam := (squarePeriodic L).one_le_densityDiameter_of_neutral hconn ρ hρ hneutral
  exact mem_densityDomainPlusExternalBoundary_iff_dist_eq
    (squarePeriodic L) hconn ρ j x hdiam

/--
: for a nonzero neutral density on the free square, the external boundary of
`D⁺_j(ρ)` is the radius-`2d(ρ)+1` shell and has between `2d(ρ)+2` and `16d(ρ)` vertices.

The room condition is the source's `L>2r`.
-/
theorem squareFree_densityDomainPlus_boundary_shell_card_bounds {L : ℕ}
    (ρ : SquareFreeVertex L → ℤ) (hρ : ρ ≠ 0) (hneutral : ∑ x, ρ x = 0)
    (j : SquareFreeVertex L)
    (hL : 2 * (2 * (squareFree L).densityDiameter ρ + 1) < L) :
    2 * (squareFree L).densityDiameter ρ + 2 ≤
        (densityDomainPlusExternalBoundary (squareFree L) ρ j).card ∧
      (densityDomainPlusExternalBoundary (squareFree L) ρ j).card ≤
        16 * (squareFree L).densityDiameter ρ := by
  classical
  let d := (squareFree L).densityDiameter ρ
  let r := 2 * d + 1
  have hside : 1 < L := by omega
  have hconn := squareFree_connected L hside
  have hdiam : 1 ≤ d := (squareFree L).one_le_densityDiameter_of_neutral
    hconn ρ hρ hneutral
  have hrroom : 2 * r < L := by simpa [r, d] using hL
  have hsphere : densityDomainPlusExternalBoundary (squareFree L) ρ j =
      Finset.univ.filter (fun x : SquareFreeVertex L => freeRadius j x = r) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hx := squareFree_densityDomainPlusExternalBoundary_iff_dist_eq
      ρ hρ hneutral j x (by simpa [d] using hL)
    rw [squareFree_dist_eq_freeRadius hside x j] at hx
    simpa [r, d, freeRadius, Nat.dist_comm] using hx
  rw [hsphere]
  constructor
  · have hge := freeRadius_shell_card_ge j r hrroom
    omega
  · calc
      (Finset.univ.filter (fun x : SquareFreeVertex L => freeRadius j x = r)).card ≤
          4 * (r + 1) := freeClippedRectangle_shell_card_le j r
      _ ≤ 16 * d := by dsimp [r]; omega

/-- : periodic counterpart of `squareFree_densityDomainPlus_boundary_shell_card_bounds`.
The proof transports the sphere to the internal right/up torus graph and uses its cyclic-radius
shell count. -/
theorem squarePeriodic_densityDomainPlus_boundary_shell_card_bounds {L : ℕ} [NeZero L]
    (ρ : (Fin L × Fin L) → ℤ) (hρ : ρ ≠ 0) (hneutral : ∑ x, ρ x = 0)
    (j : Fin L × Fin L)
    (hL : 2 * (2 * (squarePeriodic L).densityDiameter ρ + 1) < L) :
    2 * (squarePeriodic L).densityDiameter ρ + 2 ≤
        (densityDomainPlusExternalBoundary (squarePeriodic L) ρ j).card ∧
      (densityDomainPlusExternalBoundary (squarePeriodic L) ρ j).card ≤
        16 * (squarePeriodic L).densityDiameter ρ := by
  classical
  let d := (squarePeriodic L).densityDiameter ρ
  let r := 2 * d + 1
  have hside : 2 < L := by omega
  have hconn := squarePeriodic_connected L (by omega)
  have hdiam : 1 ≤ d := (squarePeriodic L).one_le_densityDiameter_of_neutral
    hconn ρ hρ hneutral
  have hrroom : 2 * r < L := by simpa [r, d] using hL
  have hsphere : densityDomainPlusExternalBoundary (squarePeriodic L) ρ j =
      Finset.univ.filter (fun x : Fin L × Fin L =>
        (squarePeriodic L).toSimpleGraph.dist x j = r) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact squarePeriodic_densityDomainPlusExternalBoundary_iff_dist_eq
      ρ hρ hneutral j x (by simpa [d] using hL)
  rw [hsphere]
  constructor
  · have hge := squarePeriodic_distShell_card_ge hside j r hrroom
    have hge' : r + 1 ≤
        (Finset.univ.filter (fun x : Fin L × Fin L =>
          (squarePeriodic L).toSimpleGraph.dist x j = r)).card := by
      simpa only [SimpleGraph.dist_comm] using hge
    clear hge
    have hge := hge'
    omega
  · calc
      (Finset.univ.filter (fun x : Fin L × Fin L =>
          (squarePeriodic L).toSimpleGraph.dist x j = r)).card ≤ 4 * (r + 1) := by
        simpa [SimpleGraph.dist_comm] using squarePeriodic_distShell_card_le hside j r
      _ ≤ 16 * d := by dsimp [r]; omega

end FroehlichSpencer.BKT.SpinWaves

end
