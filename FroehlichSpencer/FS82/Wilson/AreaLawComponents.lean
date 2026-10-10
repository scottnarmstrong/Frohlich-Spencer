/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawSupportGraph
public import FroehlichSpencer.FS82.Wilson.AreaLawEnergy
public import FroehlichSpencer.FS82.Wilson.AreaLawSource
public import FroehlichSpencer.FS82.Wilson.DualityInteger
public import FroehlichSpencer.Infra.Combinatorics.Animals
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Connected components of an integer plaquette mode

The nonzero plaquettes of a Fourier mode split into connected components in
the link-sharing graph. This file records their supports and the exact finite
decomposition of the mode into the restrictions to those supports.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

@[expose] def areaLawRectangleHorizontalLink {B : Box 4}
    (x : Fin (B 0)) (y : Fin (B 1 + 1)) : Cell 4 B :=
  edgeCell (vertexUpdate (wilsonRectangleBaseCell B) 1 y) 0 x

@[expose] def areaLawRectangleVerticalLink {B : Box 4}
    (x : Fin (B 0 + 1)) (y : Fin (B 1)) : Cell 4 B :=
  edgeCell (vertexUpdate (wilsonRectangleBaseCell B) 0 x) 1 y

@[expose] noncomputable def areaLawRectangleHorizontalRow {B : Box 4}
    (L : ℕ) (hL : L ≤ B 0) (y : Fin (B 1 + 1)) : Chain 4 B :=
  ∑ i : Fin L,
    basisChain (areaLawRectangleHorizontalLink (Fin.castLE hL i) y)

@[expose] noncomputable def areaLawRectangleVerticalColumn {B : Box 4}
    (T : ℕ) (hT : T ≤ B 1) (x : Fin (B 0 + 1)) : Chain 4 B :=
  ∑ j : Fin T,
    basisChain (areaLawRectangleVerticalLink x (Fin.castLE hT j))

private theorem finSum_sub_succ_eq_endpoints {G : Type*} [AddCommGroup G]
    (n : ℕ) (f : ℕ → G) :
    (∑ i : Fin n, (f i.val - f (i.val + 1))) = f 0 - f n := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f i - f (i + 1)) n]
  calc
    (∑ i ∈ Finset.range n, (f i - f (i + 1))) =
        ∑ i ∈ Finset.range n, -(f (i + 1) - f i) := by
          apply Finset.sum_congr rfl
          intro i hi
          abel
    _ = - ∑ i ∈ Finset.range n, (f (i + 1) - f i) := by
          rw [Finset.sum_neg_distrib]
    _ = -(f n - f 0) := by rw [Finset.sum_range_sub]
    _ = f 0 - f n := by abel

private theorem finSum_succ_sub_eq_endpoints {G : Type*} [AddCommGroup G]
    (n : ℕ) (f : ℕ → G) :
    (∑ i : Fin n, (f (i.val + 1) - f i.val)) = f n - f 0 := by
  have h := finSum_sub_succ_eq_endpoints n f
  calc
    (∑ i : Fin n, (f (i.val + 1) - f i.val)) =
        ∑ i : Fin n, -(f i.val - f (i.val + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          abel
    _ = - ∑ i : Fin n, (f i.val - f (i.val + 1)) := by
          rw [Finset.sum_neg_distrib]
    _ = f n - f 0 := by rw [h]; abel

theorem wilsonRectanglePlaquette_boundary_explicit {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (i : Fin L) (j : Fin T) :
    boundary (basisChain (wilsonRectanglePlaquette hL hT i j)) =
      basisChain (areaLawRectangleHorizontalLink (Fin.castLE hL i)
        ⟨j.val, by omega⟩) +
      basisChain (areaLawRectangleVerticalLink ⟨i.val + 1, by omega⟩
        (Fin.castLE hT j)) -
      basisChain (areaLawRectangleHorizontalLink (Fin.castLE hL i)
        ⟨j.val + 1, by omega⟩) -
        basisChain (areaLawRectangleVerticalLink ⟨i.val, by omega⟩
        (Fin.castLE hT j)) := by
  classical
  let p := wilsonRectanglePlaquette hL hT i j
  have hset0 : (Finset.univ.filter fun k : Fin 4 =>
      k < 0 ∧ coordIsEdge (p k)) = ∅ := by
    ext k
    simp
  have hset1 : (Finset.univ.filter fun k : Fin 4 =>
      k < 1 ∧ coordIsEdge (p k)) = {0} := by
    ext k
    fin_cases k <;> simp [p, wilsonRectanglePlaquette, edgeCell,
      wilsonRectangleBaseCell, coordIsEdge]
  have hrank0 : cellRankBefore p 0 = 0 := by
    unfold cellRankBefore
    rw [hset0]
    simp
  have hrank1 : cellRankBefore p 1 = 1 := by
    unfold cellRankBefore
    rw [hset1]
    simp
  change boundary (basisChain p) = _
  rw [boundary_basis]
  unfold boundaryBasis
  simp only [Fin.sum_univ_succ]
  rw [hrank0]
  have hrank1' : cellRankBefore p (Fin.succ 0) = 1 := by simpa using hrank1
  rw [hrank1']
  have hright : upperFace p 0 (Fin.castLE hL i) =
      areaLawRectangleVerticalLink ⟨i.val + 1, by omega⟩ (Fin.castLE hT j) := by
    funext k
    fin_cases k <;> simp [p, wilsonRectanglePlaquette, upperFace,
      areaLawRectangleVerticalLink, edgeCell, vertexUpdate,
      wilsonRectangleBaseCell]
  have hleft : lowerFace p 0 (Fin.castLE hL i) =
      areaLawRectangleVerticalLink ⟨i.val, by omega⟩ (Fin.castLE hT j) := by
    funext k
    fin_cases k <;> simp [p, wilsonRectanglePlaquette, lowerFace,
      areaLawRectangleVerticalLink, edgeCell, vertexUpdate,
      wilsonRectangleBaseCell]
  have htop : upperFace p 1 (Fin.castLE hT j) =
      areaLawRectangleHorizontalLink (Fin.castLE hL i) ⟨j.val + 1, by omega⟩ := by
    funext k
    fin_cases k <;> simp [p, wilsonRectanglePlaquette, upperFace,
      areaLawRectangleHorizontalLink, edgeCell, vertexUpdate,
      wilsonRectangleBaseCell]
  have hbottom : lowerFace p 1 (Fin.castLE hT j) =
      areaLawRectangleHorizontalLink (Fin.castLE hL i) ⟨j.val, by omega⟩ := by
    funext k
    fin_cases k <;> simp [p, wilsonRectanglePlaquette, lowerFace,
      areaLawRectangleHorizontalLink, edgeCell, vertexUpdate,
      wilsonRectangleBaseCell]
  have hp0 : p 0 = Sum.inr (Fin.castLE hL i) := by
    simp [p, wilsonRectanglePlaquette, edgeCell]
  have hp1 : p 1 = Sum.inr (Fin.castLE hT j) := by
    simp [p, wilsonRectanglePlaquette, edgeCell]
  have hp2 : p 2 = Sum.inl ⟨0, Nat.zero_lt_succ (B 2)⟩ := by
    simp [p, wilsonRectanglePlaquette, edgeCell, wilsonRectangleBaseCell]
  have hp3 : p 3 = Sum.inl ⟨0, Nat.zero_lt_succ (B 3)⟩ := by
    simp [p, wilsonRectanglePlaquette, edgeCell, wilsonRectangleBaseCell]
  have hp1' : p (Fin.succ 0) = Sum.inr (Fin.castLE hT j) := by simpa using hp1
  have hp2' : p (Fin.succ 0).succ = Sum.inl ⟨0, Nat.zero_lt_succ (B 2)⟩ := by
    simpa using hp2
  have hp3' : p (Fin.succ 0).succ.succ =
      Sum.inl ⟨0, Nat.zero_lt_succ (B 3)⟩ := by simpa using hp3
  have htop' : upperFace p (Fin.succ 0) (Fin.castLE hT j) =
      areaLawRectangleHorizontalLink (Fin.castLE hL i) ⟨j.val + 1, by omega⟩ := by
    simpa using htop
  have hbottom' : lowerFace p (Fin.succ 0) (Fin.castLE hT j) =
      areaLawRectangleHorizontalLink (Fin.castLE hL i) ⟨j.val, by omega⟩ := by
    simpa using hbottom
  simp only [hp0, hp1', hp2', hp3', hright, hleft, htop', hbottom']
  simp only [Fin.sum_univ_zero]
  abel_nf

theorem wilsonRectangleLoop_eq_perimeterRows {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) :
    wilsonRectangleLoop L T hL hT =
      areaLawRectangleHorizontalRow L hL
          ⟨0, Nat.zero_lt_succ (B 1)⟩ -
        areaLawRectangleHorizontalRow L hL
          ⟨T, Nat.lt_succ_of_le hT⟩ +
        areaLawRectangleVerticalColumn T hT
          ⟨L, Nat.lt_succ_of_le hL⟩ -
        areaLawRectangleVerticalColumn T hT
          ⟨0, Nat.zero_lt_succ (B 0)⟩ := by
  classical
  let H (i : Fin L) (j : ℕ) : Chain 4 B :=
    if hj : j ≤ B 1 then
      basisChain (areaLawRectangleHorizontalLink (Fin.castLE hL i)
        ⟨j, Nat.lt_succ_of_le hj⟩)
    else 0
  let V (i : ℕ) (j : Fin T) : Chain 4 B :=
    if hi : i ≤ B 0 then
      basisChain (areaLawRectangleVerticalLink
        ⟨i, Nat.lt_succ_of_le hi⟩ (Fin.castLE hT j))
    else 0
  have hhorizontal (i : Fin L) :
      (∑ j : Fin T, (H i j.val - H i (j.val + 1))) = H i 0 - H i T := by
    apply finSum_sub_succ_eq_endpoints
  have hverical (j : Fin T) :
      (∑ i : Fin L, (V (i.val + 1) j - V i.val j)) =
        V L j - V 0 j := by
    exact finSum_succ_sub_eq_endpoints L (fun i => V i j)
  unfold wilsonRectangleLoop wilsonRectangleSheet
  rw [map_sum, Fintype.sum_prod_type]
  simp_rw [wilsonRectanglePlaquette_boundary_explicit]
  have hHbottom (i : Fin L) (j : Fin T) :
      basisChain (areaLawRectangleHorizontalLink (Fin.castLE hL i)
        ⟨j.val, by omega⟩) = H i j.val := by
    have hj : j.val ≤ B 1 := by omega
    simp [H, hj]
  have hHtop (i : Fin L) (j : Fin T) :
      basisChain (areaLawRectangleHorizontalLink (Fin.castLE hL i)
        ⟨j.val + 1, by omega⟩) = H i (j.val + 1) := by
    have hj : j.val + 1 ≤ B 1 := by omega
    simp [H, hj]
  have hVleft (i : Fin L) (j : Fin T) :
      basisChain (areaLawRectangleVerticalLink
        ⟨i.val, by omega⟩ (Fin.castLE hT j)) = V i.val j := by
    have hi : i.val ≤ B 0 := by omega
    simp [V, hi]
  have hVright (i : Fin L) (j : Fin T) :
      basisChain (areaLawRectangleVerticalLink
        ⟨i.val + 1, by omega⟩ (Fin.castLE hT j)) = V (i.val + 1) j := by
    have hi : i.val + 1 ≤ B 0 := by omega
    simp [V, hi]
  simp_rw [hHbottom, hHtop, hVleft, hVright]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hH0 :
      (∑ i : Fin L, H i 0) =
        areaLawRectangleHorizontalRow L hL
          ⟨0, Nat.zero_lt_succ (B 1)⟩ := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [H]
  have hHT :
      (∑ i : Fin L, H i T) =
        areaLawRectangleHorizontalRow L hL
          ⟨T, Nat.lt_succ_of_le hT⟩ := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [H, hT]
  have hVL :
      (∑ j : Fin T, V L j) =
        areaLawRectangleVerticalColumn T hT
          ⟨L, Nat.lt_succ_of_le hL⟩ := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [V, hL]
  have hV0 :
      (∑ j : Fin T, V 0 j) =
        areaLawRectangleVerticalColumn T hT
          ⟨0, Nat.zero_lt_succ (B 0)⟩ := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [V]
  have hHdiff :
      (∑ i : Fin L, ∑ j : Fin T, H i j.val) -
        (∑ i : Fin L, ∑ j : Fin T, H i (j.val + 1)) =
        (∑ i : Fin L, H i 0) - (∑ i : Fin L, H i T) := by
    calc
      _ = ∑ i : Fin L, ∑ j : Fin T,
            (H i j.val - H i (j.val + 1)) := by
              rw [← Finset.sum_sub_distrib]
              apply Fintype.sum_congr
              intro i
              rw [← Finset.sum_sub_distrib]
      _ = ∑ i : Fin L, (H i 0 - H i T) := by
              apply Fintype.sum_congr
              intro i
              exact hhorizontal i
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hVrightSum :
      (∑ i : Fin L, ∑ j : Fin T, V (i.val + 1) j) =
        ∑ j : Fin T, ∑ i : Fin L, V (i.val + 1) j := by
    rw [Finset.sum_comm]
  have hVleftSum :
      (∑ i : Fin L, ∑ j : Fin T, V i.val j) =
        ∑ j : Fin T, ∑ i : Fin L, V i.val j := by
    rw [Finset.sum_comm]
  have hVdiff :
      (∑ i : Fin L, ∑ j : Fin T, V (i.val + 1) j) -
        (∑ i : Fin L, ∑ j : Fin T, V i.val j) =
        (∑ j : Fin T, V L j) - (∑ j : Fin T, V 0 j) := by
    calc
      _ = (∑ j : Fin T, ∑ i : Fin L, V (i.val + 1) j) -
            (∑ j : Fin T, ∑ i : Fin L, V i.val j) := by
              rw [hVrightSum, hVleftSum]
      _ = ∑ j : Fin T, ∑ i : Fin L,
            (V (i.val + 1) j - V i.val j) := by
              rw [← Finset.sum_sub_distrib]
              apply Fintype.sum_congr
              intro j
              rw [← Finset.sum_sub_distrib]
      _ = ∑ j : Fin T, (V L j - V 0 j) := by
              apply Fintype.sum_congr
              intro j
              exact hverical j
      _ = _ := by rw [Finset.sum_sub_distrib]
  calc
    (∑ i : Fin L, ∑ j : Fin T, H i j.val) +
        (∑ i : Fin L, ∑ j : Fin T, V (i.val + 1) j) -
        (∑ i : Fin L, ∑ j : Fin T, H i (j.val + 1)) -
        (∑ i : Fin L, ∑ j : Fin T, V i.val j) =
        ((∑ i : Fin L, ∑ j : Fin T, H i j.val) -
          (∑ i : Fin L, ∑ j : Fin T, H i (j.val + 1))) +
        ((∑ i : Fin L, ∑ j : Fin T, V (i.val + 1) j) -
          (∑ i : Fin L, ∑ j : Fin T, V i.val j)) := by abel
    _ = ((∑ i : Fin L, H i 0) - (∑ i : Fin L, H i T)) +
        ((∑ j : Fin T, V L j) - (∑ j : Fin T, V 0 j)) := by
          rw [hHdiff, hVdiff]
    _ = _ := by rw [hH0, hHT, hVL, hV0]; abel

/-- The link-sharing graph induced on the nonzero plaquettes of a mode. -/
noncomputable def nonzeroPlaquetteGraph {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) : SimpleGraph {p : PrimalPlaquettes B // m p ≠ 0} :=
  (plaquetteLinkGraph (B := B)).induce {p | m p ≠ 0}


noncomputable instance nonzeroPlaquetteGraphComponentFintype {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) : Fintype (nonzeroPlaquetteGraph m).ConnectedComponent :=
  Fintype.ofFinite _

/-- The plaquettes in one connected component of the nonzero support. -/
noncomputable def plaquetteModeComponentSupport {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) : Finset (PrimalPlaquettes B) := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ hp : m p ≠ 0, (nonzeroPlaquetteGraph m).connectedComponentMk ⟨p, hp⟩ = c

theorem mem_plaquetteModeComponentSupport_iff {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent)
    (p : PrimalPlaquettes B) :
    p ∈ plaquetteModeComponentSupport m c ↔
      ∃ hp : m p ≠ 0, (nonzeroPlaquetteGraph m).connectedComponentMk ⟨p, hp⟩ = c := by
  classical
  simp [plaquetteModeComponentSupport]

theorem mem_plaquetteModeComponentSupport_iff_componentMk {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) (p : PrimalPlaquettes B) (hp : m p ≠ 0)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    p ∈ plaquetteModeComponentSupport m c ↔
      (nonzeroPlaquetteGraph m).connectedComponentMk ⟨p, hp⟩ = c := by
  rw [mem_plaquetteModeComponentSupport_iff]
  constructor
  · rintro ⟨hp', hcomp⟩
    have hproof : hp' = hp := Subsingleton.elim _ _
    subst hp'
    exact hcomp
  · intro hcomp
    exact ⟨hp, hcomp⟩

/-- Restriction of a plaquette mode to one nonzero-support component. -/
@[expose] noncomputable def plaquetteModeComponentField {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) : PrimalPlaquettes B → ℤ :=
  fun p => if p ∈ plaquetteModeComponentSupport m c then m p else 0

/-- The complementary field after removing one nonzero-support component. -/
@[expose] noncomputable def plaquetteModeComponentRemainder {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) : PrimalPlaquettes B → ℤ :=
  fun p => if p ∈ plaquetteModeComponentSupport m c then 0 else m p

theorem plaquetteModeComponentField_add_remainder {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    plaquetteModeComponentField m c + plaquetteModeComponentRemainder m c = m := by
  classical
  funext p
  by_cases hp : p ∈ plaquetteModeComponentSupport m c
  · simp [plaquetteModeComponentField, plaquetteModeComponentRemainder, hp]
  · simp [plaquetteModeComponentField, plaquetteModeComponentRemainder, hp]

theorem plaquetteModeChain_add {B : Box 4}
    (m n : PrimalPlaquettes B → ℤ) :
    plaquetteModeChain (m + n) = plaquetteModeChain m + plaquetteModeChain n := by
  classical
  ext x
  by_cases hx : cellDegree x = 2
  · let p : PrimalPlaquettes B := ⟨x, hx⟩
    change plaquetteModeChain (m + n) x =
      (plaquetteModeChain m + plaquetteModeChain n) x
    rw [plaquetteModeChain_apply (m + n) p, Finsupp.add_apply,
      plaquetteModeChain_apply m p, plaquetteModeChain_apply n p]
    rfl
  · have hzero (f : PrimalPlaquettes B → ℤ) : plaquetteModeChain f x = 0 := by
      by_contra hne
      exact hx ((plaquetteModeChain_homogeneousSupport f) x
        (Finsupp.mem_support_iff.mpr hne))
    simp [hzero]

theorem plaquetteModeChain_eq_component_add_remainder {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    plaquetteModeChain m =
      plaquetteModeChain (plaquetteModeComponentField m c) +
        plaquetteModeChain (plaquetteModeComponentRemainder m c) := by
  calc
    plaquetteModeChain m =
        plaquetteModeChain
          (plaquetteModeComponentField m c +
            plaquetteModeComponentRemainder m c) := by
          rw [plaquetteModeComponentField_add_remainder]
    _ = plaquetteModeChain (plaquetteModeComponentField m c) +
          plaquetteModeChain (plaquetteModeComponentRemainder m c) :=
      plaquetteModeChain_add _ _


theorem plaquetteModeComponentSupport_nonadjacent {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    {c d : (nonzeroPlaquetteGraph m).ConnectedComponent} (hcd : c ≠ d)
    {p q : PrimalPlaquettes B}
    (hp : p ∈ plaquetteModeComponentSupport m c)
    (hq : q ∈ plaquetteModeComponentSupport m d) :
    ¬ (plaquetteLinkGraph (B := B)).Adj p q := by
  intro hadj
  have hpm := (mem_plaquetteModeComponentSupport_iff m c p).mp hp
  have hqm := (mem_plaquetteModeComponentSupport_iff m d q).mp hq
  have hadj' : (nonzeroPlaquetteGraph m).Adj
      ⟨p, hpm.choose⟩ ⟨q, hqm.choose⟩ := SimpleGraph.induce_adj.mpr hadj
  have hcomp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj'
  exact hcd (hpm.choose_spec.symm.trans (hcomp.trans hqm.choose_spec))

theorem plaquetteModeComponentField_sum_eq {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) :
    (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
      plaquetteModeComponentField m c) = m := by
  classical
  funext p
  by_cases hp : m p = 0
  · simp [plaquetteModeComponentField, hp]
  · let c₀ := (nonzeroPlaquetteGraph m).connectedComponentMk ⟨p, hp⟩
    have hmem (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
        p ∈ plaquetteModeComponentSupport m c ↔ c₀ = c := by
      rw [mem_plaquetteModeComponentSupport_iff_componentMk m p hp]
    have hterm (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
        plaquetteModeComponentField m c p =
          if h : c = c₀ then m p else 0 := by
      simp [plaquetteModeComponentField, hmem c, eq_comm]
    simp only [Finset.sum_apply]
    simp_rw [hterm]
    simp

/-- The plaquette chains of all nonzero-support components sum exactly to the
original mode chain. -/
theorem plaquetteModeChain_component_sum_eq {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) :
    (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
      plaquetteModeChain (plaquetteModeComponentField m c)) =
        plaquetteModeChain m := by
  classical
  ext x
  by_cases hx : cellDegree x = 2
  · let p : PrimalPlaquettes B := ⟨x, hx⟩
    have hsumField := congrFun (plaquetteModeComponentField_sum_eq m) p
    have hsumField' :
        (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
          plaquetteModeComponentField m c p) = m p := by
      simpa only [Finset.sum_apply] using hsumField
    have hEval :
        (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
          plaquetteModeChain (plaquetteModeComponentField m c)) x =
            ∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
              plaquetteModeChain (plaquetteModeComponentField m c) x := by
      exact finsupp_finset_sum_apply Finset.univ
        (fun c : (nonzeroPlaquetteGraph m).ConnectedComponent =>
          plaquetteModeChain (plaquetteModeComponentField m c)) x
    calc
      (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
        plaquetteModeChain (plaquetteModeComponentField m c)) x =
          ∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
            plaquetteModeChain (plaquetteModeComponentField m c) x := hEval
      _ = ∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
            plaquetteModeComponentField m c p := by
              apply Finset.sum_congr rfl
              intro c hc
              exact plaquetteModeChain_apply _ p
      _ = m p := hsumField'
      _ = plaquetteModeChain m x := by
            simpa [p] using (plaquetteModeChain_apply m p).symm
  · have hzero (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
        plaquetteModeChain (plaquetteModeComponentField m c) x = 0 := by
      by_contra hne
      exact hx ((plaquetteModeChain_homogeneousSupport
        (plaquetteModeComponentField m c)) x (Finsupp.mem_support_iff.mpr hne))
    have hzeroM : plaquetteModeChain m x = 0 := by
      by_contra hne
      exact hx ((plaquetteModeChain_homogeneousSupport m) x
        (Finsupp.mem_support_iff.mpr hne))
    rw [finsupp_finset_sum_apply Finset.univ
      (fun c : (nonzeroPlaquetteGraph m).ConnectedComponent =>
        plaquetteModeChain (plaquetteModeComponentField m c)) x]
    simp [hzero, hzeroM]

theorem plaquetteModeComponentField_support {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    plaquetteFieldSupport (plaquetteModeComponentField m c) =
      plaquetteModeComponentSupport m c := by
  classical
  ext p
  by_cases hp : m p = 0
  · simp [plaquetteFieldSupport, plaquetteModeComponentField,
      plaquetteModeComponentSupport, hp]
  · simp [plaquetteFieldSupport, plaquetteModeComponentField, hp]

theorem plaquetteModeComponentSupport_connected {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    ((plaquetteLinkGraph (B := B)).induce
      (plaquetteModeComponentSupport m c : Set (PrimalPlaquettes B))).Connected := by
  classical
  let H := nonzeroPlaquetteGraph m
  let G := plaquetteLinkGraph (B := B)
  let f : c.toSimpleGraph →g
      G.induce (plaquetteModeComponentSupport m c : Set (PrimalPlaquettes B)) :=
    { toFun := fun x => ⟨x.1.1, by
        apply (mem_plaquetteModeComponentSupport_iff m c x.1.1).2
        exact ⟨x.1.2,
          (SimpleGraph.ConnectedComponent.mem_supp_iff c x.1).mp x.2⟩
      ⟩
      map_rel' := by
        intro x y hxy
        exact hxy }
  have hsurj : Function.Surjective f := by
    intro y
    rcases (mem_plaquetteModeComponentSupport_iff m c y.1).mp y.2 with
      ⟨hy, hc⟩
    refine ⟨⟨⟨y.1, hy⟩, ?_⟩, ?_⟩
    · exact (SimpleGraph.ConnectedComponent.mem_supp_iff c ⟨y.1, hy⟩).mpr hc
    · apply Subtype.ext
      rfl
  exact SimpleGraph.Connected.map f hsurj c.connected_toSimpleGraph

theorem plaquetteModeComponentSupport_mem_animals {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) {root : PrimalPlaquettes B}
    (hroot : root ∈ plaquetteModeComponentSupport m c) :
    plaquetteModeComponentSupport m c ∈
      FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) root
        (plaquetteModeComponentSupport m c).card := by
  classical
  rw [FroehlichSpencer.Infra.mem_animals]
  exact ⟨hroot, rfl, plaquetteModeComponentSupport_connected m c⟩

end FroehlichSpencer.FS82.Wilson

end
