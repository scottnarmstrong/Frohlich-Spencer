/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.DualityFinite
public import FroehlichSpencer.FS82.Wilson.AreaLawAnimals
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finsupp.BigOperators

/-!
# Link-connected support graph for dual plaquette fields

Two plaquettes are adjacent when both have nonzero boundary coefficient on a
common link. Its connected sets are the polymers in the dual high-temperature
expansion.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

/-- The two codimension-one faces in the `i` direction, viewed as cells. -/
private def plaquetteAxisBoundaryFaces {B : Box 4}
    (p : PrimalPlaquettes B) (i : Fin 4) : Finset (Cell 4 B) :=
  match p.1 i with
  | Sum.inl _ => ∅
  | Sum.inr e => {upperFace p.1 i e, lowerFace p.1 i e}

/-- A plaquette boundary has at most two link cells from each active axis. -/
private theorem axisBoundaryBasis_support_subset_faces {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) :
    (axisBoundaryBasis c i).support ⊆
      (match c i with
       | Sum.inl _ => (∅ : Finset (Cell 4 B))
       | Sum.inr e => {upperFace c i e, lowerFace c i e}) := by
  classical
  cases hi : c i with
  | inl v => simp [axisBoundaryBasis, hi]
  | inr e =>
      intro x hx
      simp only [axisBoundaryBasis, hi, Finsupp.mem_support_iff] at hx
      by_contra hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      simp [basisChain, hnot.1, hnot.2] at hx

private theorem support_sum_subset_biUnion {ι α : Type*} [DecidableEq ι]
    [DecidableEq α] [AddCommMonoid ℤ] (s : Finset ι) (f : ι → α →₀ ℤ) :
    (∑ i ∈ s, f i).support ⊆ s.biUnion fun i => (f i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.biUnion_insert]
      exact Finsupp.support_add.trans (Finset.union_subset_union
        (Finset.Subset.rfl) ih)

private noncomputable def plaquetteBoundarySideCells {B : Box 4}
    (p : PrimalPlaquettes B) : Finset (Cell 4 B) :=
  (cellAxes p.1).biUnion (plaquetteAxisBoundaryFaces p)

/-- The cubical boundary support is contained in the union of its four
possible side cells. -/
private theorem plaquetteBoundary_support_subset_sides {B : Box 4}
    (p : PrimalPlaquettes B) :
    (boundary (Finsupp.single p.1 (1 : ℤ))).support ⊆
      plaquetteBoundarySideCells p := by
  classical
  have hboundary : boundary (Finsupp.single p.1 (1 : ℤ)) =
      ∑ i : Fin 4, axisBoundaryBasis p.1 i := by
    simp [boundary, axisBoundary, Finsupp.linearCombination_single]
  intro l hl
  rw [hboundary] at hl
  have hmem := support_sum_subset_biUnion (Finset.univ : Finset (Fin 4))
    (fun i : Fin 4 => axisBoundaryBasis p.1 i) hl
  rcases Finset.mem_biUnion.mp hmem with ⟨i, hi, hli⟩
  have hface := axisBoundaryBasis_support_subset_faces p.1 i hli
  have haxis : i ∈ cellAxes p.1 := by
    cases hp : p.1 i with
    | inl v => simp [hp] at hface
    | inr e =>
        simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hp]
        rfl
  exact Finset.mem_biUnion.mpr ⟨i, haxis, by
    simpa [plaquetteAxisBoundaryFaces] using hface⟩

private theorem plaquetteBoundarySideCells_card_le_four {B : Box 4}
    (p : PrimalPlaquettes B) : (plaquetteBoundarySideCells p).card ≤ 4 := by
  classical
  unfold plaquetteBoundarySideCells
  calc
    ((cellAxes p.1).biUnion (plaquetteAxisBoundaryFaces p)).card ≤
        ∑ i ∈ cellAxes p.1, (plaquetteAxisBoundaryFaces p i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ cellAxes p.1, 2 := by
      apply Finset.sum_le_sum
      intro i hi
      cases hp : p.1 i with
        | inl v => simp [plaquetteAxisBoundaryFaces, hp]
        | inr e =>
          rw [plaquetteAxisBoundaryFaces, hp]
          change Finset.card (insert (upperFace p.1 i e)
            ({lowerFace p.1 i e} : Finset (Cell 4 B))) ≤ 2
          calc
            _ ≤ ({lowerFace p.1 i e} : Finset (Cell 4 B)).card + 1 :=
              Finset.card_insert_le _ _
            _ = 2 := by simp
    _ = (cellAxes p.1).card * 2 := by simp [Finset.sum_const]
    _ = 4 := by
      have hdegree : (cellAxes p.1).card = 2 := p.2
      rw [hdegree]

/-- The links on the boundary of one oriented plaquette. -/
@[expose] noncomputable def plaquetteBoundaryLinks {B : Box 4}
    (p : PrimalPlaquettes B) : Finset (PrimalLinks B) :=
  Finset.univ.filter fun l =>
    (boundary (Finsupp.single p.1 (1 : ℤ))) l.1 ≠ 0

/-- A cubical plaquette has at most four links in its boundary. -/
theorem plaquetteBoundaryLinks_card_le_four {B : Box 4}
    (p : PrimalPlaquettes B) : (plaquetteBoundaryLinks p).card ≤ 4 := by
  classical
  calc
    (plaquetteBoundaryLinks p).card ≤ (plaquetteBoundarySideCells p).card :=
      Finset.card_le_card_of_injOn Subtype.val
        (by
          intro l hl
          have hcoef : (boundary (Finsupp.single p.1 (1 : ℤ))) l.1 ≠ 0 :=
            (Finset.mem_filter.mp hl).2
          have hsupport : l.1 ∈
              (boundary (Finsupp.single p.1 (1 : ℤ))).support :=
            Finsupp.mem_support_iff.mpr hcoef
          exact plaquetteBoundary_support_subset_sides p hsupport)
        (by
          intro l hl l' hl' heq
          exact Subtype.ext heq)
    _ ≤ 4 := plaquetteBoundarySideCells_card_le_four p

private theorem boundaryLink_has_face {B : Box 4}
    (p : PrimalPlaquettes B) (l : PrimalLinks B)
    (hl : l ∈ plaquetteBoundaryLinks p) :
    ∃ i ∈ cellAxes p.1,
      (∃ e, p.1 i = Sum.inr e ∧ l.1 = upperFace p.1 i e) ∨
      (∃ e, p.1 i = Sum.inr e ∧ l.1 = lowerFace p.1 i e) := by
  have hcoef : (boundary (Finsupp.single p.1 (1 : ℤ))) l.1 ≠ 0 :=
    (Finset.mem_filter.mp hl).2
  have hsupport : l.1 ∈ (boundary (Finsupp.single p.1 (1 : ℤ))).support :=
    Finsupp.mem_support_iff.mpr hcoef
  have hside := plaquetteBoundary_support_subset_sides p hsupport
  rcases Finset.mem_biUnion.mp hside with ⟨i, hi, hface⟩
  cases hp : p.1 i with
  | inl v => simp [plaquetteAxisBoundaryFaces, hp] at hface
  | inr e =>
      have haxes : i ∈ cellAxes p.1 := by
        simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hp]
        rfl
      simp only [plaquetteAxisBoundaryFaces, hp, Finset.mem_insert,
        Finset.mem_singleton] at hface
      rcases hface with hface | hface
      · exact ⟨i, haxes, Or.inl ⟨e, hp, hface⟩⟩
      · exact ⟨i, haxes, Or.inr ⟨e, hp, hface⟩⟩

private noncomputable def plaquettesAtLinkLowerFace {B : Box 4}
    (l : PrimalLinks B) (i : Fin 4) : Finset (PrimalPlaquettes B) :=
  Finset.univ.filter fun p => ∃ e, p.1 i = Sum.inr e ∧
    l.1 = lowerFace p.1 i e

private noncomputable def plaquettesAtLinkUpperFace {B : Box 4}
    (l : PrimalLinks B) (i : Fin 4) : Finset (PrimalPlaquettes B) :=
  Finset.univ.filter fun p => ∃ e, p.1 i = Sum.inr e ∧
    l.1 = upperFace p.1 i e

private theorem cell_eq_of_same_lower_face {B : Box 4} {p q : Cell 4 B}
    {i : Fin 4} {e e' : Fin (B i)}
    (hp : p i = Sum.inr e) (hq : q i = Sum.inr e')
    (hface : lowerFace p i e = lowerFace q i e') : p = q := by
  funext k
  by_cases hk : k = i
  · subst k
    have hv := congrFun hface i
    simp [lowerFace, vertexUpdate] at hv
    have he : e = e' := Fin.ext hv
    rw [hp, hq, he]
  · have hv := congrFun hface k
    simp [lowerFace, vertexUpdate, hk] at hv
    exact hv

private theorem cell_eq_of_same_upper_face {B : Box 4} {p q : Cell 4 B}
    {i : Fin 4} {e e' : Fin (B i)}
    (hp : p i = Sum.inr e) (hq : q i = Sum.inr e')
    (hface : upperFace p i e = upperFace q i e') : p = q := by
  funext k
  by_cases hk : k = i
  · subst k
    have hv := congrFun hface i
    simp [upperFace, vertexUpdate] at hv
    have he : e = e' := Fin.ext hv
    rw [hp, hq, he]
  · have hv := congrFun hface k
    simp [upperFace, vertexUpdate, hk] at hv
    exact hv

private theorem plaquettesAtLinkLowerFace_card_le_one {B : Box 4}
    (l : PrimalLinks B) (i : Fin 4) :
    (plaquettesAtLinkLowerFace l i).card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro p q hp hq
  rcases (Finset.mem_filter.mp hp).2 with ⟨e, hpe, hpl⟩
  rcases (Finset.mem_filter.mp hq).2 with ⟨e', hqe, hql⟩
  apply Subtype.ext
  exact cell_eq_of_same_lower_face hpe hqe (hpl.symm.trans hql)

private theorem plaquettesAtLinkUpperFace_card_le_one {B : Box 4}
    (l : PrimalLinks B) (i : Fin 4) :
    (plaquettesAtLinkUpperFace l i).card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro p q hp hq
  rcases (Finset.mem_filter.mp hp).2 with ⟨e, hpe, hpl⟩
  rcases (Finset.mem_filter.mp hq).2 with ⟨e', hqe, hql⟩
  apply Subtype.ext
  exact cell_eq_of_same_upper_face hpe hqe (hpl.symm.trans hql)

private noncomputable def plaquettesAtLinkByAxis {B : Box 4}
    (l : PrimalLinks B) (i : Fin 4) : Finset (PrimalPlaquettes B) :=
  plaquettesAtLinkLowerFace l i ∪ plaquettesAtLinkUpperFace l i

private theorem plaquettesAtLinkByAxis_card_le_two {B : Box 4}
    (l : PrimalLinks B) (i : Fin 4) :
    (plaquettesAtLinkByAxis l i).card ≤ 2 := by
  unfold plaquettesAtLinkByAxis
  calc
    (plaquettesAtLinkLowerFace l i ∪ plaquettesAtLinkUpperFace l i).card ≤
        (plaquettesAtLinkLowerFace l i).card +
          (plaquettesAtLinkUpperFace l i).card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (plaquettesAtLinkLowerFace_card_le_one l i)
      (plaquettesAtLinkUpperFace_card_le_one l i)
    _ = 2 := by norm_num

/-- At most six plaquettes meet a fixed link: choose one of the other three
coordinate directions and one of the two endpoint faces. -/
theorem plaquettesAtLink_card_le_six {B : Box 4} (l : PrimalLinks B) :
    (Finset.univ.filter fun p : PrimalPlaquettes B =>
      l ∈ plaquetteBoundaryLinks p).card ≤ 6 := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp l.2
  let otherAxes : Finset (Fin 4) := Finset.univ.erase a
  let cover : Finset (PrimalPlaquettes B) :=
    otherAxes.biUnion (plaquettesAtLinkByAxis l)
  have hcover :
      (Finset.univ.filter fun p : PrimalPlaquettes B =>
        l ∈ plaquetteBoundaryLinks p) ⊆ cover := by
    intro p hp
    rcases boundaryLink_has_face p l (Finset.mem_filter.mp hp).2 with
      ⟨i, hi, hside⟩
    have hia : i ≠ a := by
      have haMem : a ∈ cellAxes l.1 := by rw [ha]; simp
      rcases hside with ⟨e, hpe, hface⟩ | ⟨e, hpe, hface⟩
      · rw [hface, cellAxes_upperFace] at haMem
        exact (Finset.mem_erase.mp haMem).1.symm
      · rw [hface, cellAxes_lowerFace] at haMem
        exact (Finset.mem_erase.mp haMem).1.symm
    have hiOther : i ∈ otherAxes := by
      simp [otherAxes, hia]
    refine Finset.mem_biUnion.mpr ⟨i, hiOther, ?_⟩
    rcases hside with ⟨e, hpe, hface⟩ | ⟨e, hpe, hface⟩
    · exact Finset.mem_union.mpr (Or.inr <|
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, hpe, hface⟩⟩)
    · exact Finset.mem_union.mpr (Or.inl <|
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, hpe, hface⟩⟩)
  have hcoverCard : cover.card ≤
      ∑ i ∈ otherAxes, (plaquettesAtLinkByAxis l i).card := by
    dsimp [cover]
    exact Finset.card_biUnion_le
  have hsum :
      (∑ i ∈ otherAxes, (plaquettesAtLinkByAxis l i).card) ≤
        ∑ _i ∈ otherAxes, 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact plaquettesAtLinkByAxis_card_le_two l i
  have hotherCard : otherAxes.card = 3 := by
    dsimp [otherAxes]
    rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
    simp
  have hsum' : (∑ _i ∈ otherAxes, 2) = 6 := by
    rw [Finset.sum_const, nsmul_eq_mul, hotherCard]
    norm_num
  calc
    (Finset.univ.filter fun p : PrimalPlaquettes B =>
      l ∈ plaquetteBoundaryLinks p).card ≤ cover.card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ otherAxes, (plaquettesAtLinkByAxis l i).card := hcoverCard
    _ ≤ ∑ _i ∈ otherAxes, 2 := hsum
    _ = 6 := hsum'

/-- The graph adjacency relation for the support of a dual integer field. -/
@[expose] def plaquettesShareBoundaryLink {B : Box 4}
    (p q : PrimalPlaquettes B) : Prop :=
  p ≠ q ∧ ∃ l, l ∈ plaquetteBoundaryLinks p ∧ l ∈ plaquetteBoundaryLinks q

/-- The finite simple graph used to define connected dual polymers. -/
@[expose] def plaquetteLinkGraph {B : Box 4} : SimpleGraph (PrimalPlaquettes B) where
  Adj := plaquettesShareBoundaryLink
  symm := by
    constructor
    intro p q h
    rcases h.2 with ⟨l, hpl, hql⟩
    exact ⟨h.1.symm, l, hql, hpl⟩
  loopless := by
    constructor
    intro p h
    exact h.1 rfl

noncomputable instance plaquetteLinkGraphDecidableAdj {B : Box 4} :
    DecidableRel (plaquetteLinkGraph (B := B)).Adj := Classical.decRel _

noncomputable instance plaquetteLinkGraphLocallyFinite {B : Box 4} :
    (plaquetteLinkGraph (B := B)).LocallyFinite := fun _ => Fintype.ofFinite _


/-- The chain carried by a selected plaquette set. -/
@[expose] noncomputable def plaquetteFieldChainOnSet {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) (s : Finset (PrimalPlaquettes B)) : Chain 4 B :=
  ∑ p ∈ s, Finsupp.single p.1 (m p)

private theorem exists_nonzero_of_finset_sum_ne_zero {α : Type*}
    (s : Finset α) (f : α → ℤ) (h : (∑ x ∈ s, f x) ≠ 0) :
    ∃ x ∈ s, f x ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  apply Finset.sum_eq_zero
  intro x hx
  exact hn x hx

theorem plaquetteFieldChainOnSet_boundary_coeff {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) (s : Finset (PrimalPlaquettes B))
    (l : PrimalLinks B) :
    (boundary (plaquetteFieldChainOnSet m s)) l.1 =
      ∑ p ∈ s, m p * (boundary (Finsupp.single p.1 (1 : ℤ))) l.1 := by
  classical
  unfold plaquetteFieldChainOnSet
  rw [map_sum]
  rw [finsupp_finset_sum_apply]
  apply Finset.sum_congr rfl
  intro p hp
  have hs : Finsupp.single p.1 (m p) = (m p) • basisChain p.1 := by
    ext c
    by_cases hc : c = p.1 <;> simp [basisChain, hc]
  calc
    (boundary (Finsupp.single p.1 (m p))) l.1 =
        (boundary ((m p) • basisChain p.1)) l.1 := by rw [hs]
    _ = m p * (boundary (Finsupp.single p.1 (1 : ℤ))) l.1 := by
        rw [map_smul]
        simp [basisChain, Finsupp.smul_apply]

/-- Boundary supports of nonadjacent plaquette families are disjoint. -/
theorem plaquetteFieldChainOnSet_boundary_support_disjoint {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (s t : Finset (PrimalPlaquettes B))
    (hdisj : Disjoint s t)
    (hsep : ∀ p ∈ s, ∀ q ∈ t,
      ¬ (plaquetteLinkGraph (B := B)).Adj p q) :
    Disjoint
      (Finset.univ.filter fun l : PrimalLinks B =>
        (boundary (plaquetteFieldChainOnSet m s)) l.1 ≠ 0)
      (Finset.univ.filter fun l : PrimalLinks B =>
        (boundary (plaquetteFieldChainOnSet m t)) l.1 ≠ 0) := by
  classical
  rw [Finset.disjoint_left]
  intro l hlS hlT
  have hS := (Finset.mem_filter.mp hlS).2
  have hT := (Finset.mem_filter.mp hlT).2
  rw [plaquetteFieldChainOnSet_boundary_coeff m s l] at hS
  rw [plaquetteFieldChainOnSet_boundary_coeff m t l] at hT
  obtain ⟨p, hpS, hpcoeff⟩ := exists_nonzero_of_finset_sum_ne_zero
    (s := s) (fun p => m p * (boundary (Finsupp.single p.1 (1 : ℤ))) l.1) hS
  obtain ⟨q, hqT, hqcoeff⟩ := exists_nonzero_of_finset_sum_ne_zero
    (s := t) (fun q => m q * (boundary (Finsupp.single q.1 (1 : ℤ))) l.1) hT
  have hmp : m p ≠ 0 := fun hzero => by simp [hzero] at hpcoeff
  have hmq : m q ≠ 0 := fun hzero => by simp [hzero] at hqcoeff
  have hbp : (boundary (Finsupp.single p.1 (1 : ℤ))) l.1 ≠ 0 :=
    fun hz => by simp [hz] at hpcoeff
  have hbq : (boundary (Finsupp.single q.1 (1 : ℤ))) l.1 ≠ 0 :=
    fun hz => by simp [hz] at hqcoeff
  have hpq : p ≠ q := by
    intro heq
    have hnot : p ∉ t := (Finset.disjoint_left.mp hdisj) hpS
    exact hnot (heq ▸ hqT)
  apply hsep p hpS q hqT
  exact ⟨hpq, l,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbp⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbq⟩⟩

/-- Finite incidence count: four boundary links, with at most six plaquettes
through each link, give degree at most `4 * (6 - 1) = 20`.  The two local
incidence bounds are kept explicit so the geometric calculation can be
reviewed independently of this finite union estimate. -/
theorem plaquetteLinkGraph_degree_le_twenty_of_incidence_bounds {B : Box 4}
    (hfour : ∀ p : PrimalPlaquettes B,
      (plaquetteBoundaryLinks p).card ≤ 4)
    (hsix : ∀ l : PrimalLinks B,
      (Finset.univ.filter fun p : PrimalPlaquettes B =>
        l ∈ plaquetteBoundaryLinks p).card ≤ 6)
    (p : PrimalPlaquettes B) :
    (plaquetteLinkGraph (B := B)).degree p ≤ 20 := by
  classical
  let incident (l : PrimalLinks B) : Finset (PrimalPlaquettes B) :=
    Finset.univ.filter fun q => l ∈ plaquetteBoundaryLinks q
  let covers : Finset (PrimalPlaquettes B) :=
    (plaquetteBoundaryLinks p).biUnion fun l => (incident l).erase p
  have hsub : (plaquetteLinkGraph (B := B)).neighborFinset p ⊆ covers := by
    intro q hq
    have hAdj : (plaquetteLinkGraph (B := B)).Adj p q :=
      (plaquetteLinkGraph (B := B)).mem_neighborFinset p q |>.mp hq
    rcases hAdj.2 with ⟨l, hpl, hql⟩
    refine Finset.mem_biUnion.mpr ⟨l, hpl, ?_⟩
    have hqi : q ∈ incident l := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hql⟩
    exact Finset.mem_erase.mpr ⟨hAdj.1.symm, hqi⟩
  have hcardCover : covers.card ≤
      ∑ l ∈ plaquetteBoundaryLinks p, ((incident l).erase p).card := by
    dsimp [covers]
    exact Finset.card_biUnion_le
  have hsum :
      (∑ l ∈ plaquetteBoundaryLinks p, ((incident l).erase p).card) ≤
        ∑ _l ∈ plaquetteBoundaryLinks p, 5 := by
    apply Finset.sum_le_sum
    intro l hl
    have hpm : p ∈ incident l :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
    have hlocal : (incident l).card ≤ 6 := by
      simpa [incident] using hsix l
    rw [Finset.card_erase_of_mem hpm]
    omega
  have hsum' :
      (∑ _l ∈ plaquetteBoundaryLinks p, 5) ≤ 4 * 5 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact Nat.mul_le_mul_right 5 (hfour p)
  calc
    (plaquetteLinkGraph (B := B)).degree p =
        ((plaquetteLinkGraph (B := B)).neighborFinset p).card := by
          rfl
    _ ≤ covers.card := Finset.card_le_card hsub
    _ ≤ ∑ l ∈ plaquetteBoundaryLinks p, ((incident l).erase p).card := hcardCover
    _ ≤ ∑ _l ∈ plaquetteBoundaryLinks p, 5 := hsum
    _ ≤ 4 * 5 := hsum'
    _ = 20 := by norm_num

/-- The explicit four-edge by six-plaquettes incidence count gives degree 20. -/
theorem plaquetteLinkGraph_degree_le_twenty {B : Box 4}
    (p : PrimalPlaquettes B) :
    (plaquetteLinkGraph (B := B)).degree p ≤ 20 := by
  apply plaquetteLinkGraph_degree_le_twenty_of_incidence_bounds
    plaquetteBoundaryLinks_card_le_four plaquettesAtLink_card_le_six p

/-- A rooted connected plaquette support of size `k` has at most `400^k`
possibilities, using the explicit cubical degree bound. -/
theorem card_linkConnectedPlaquetteSupports_le {B : Box 4}
    (p : PrimalPlaquettes B) (k : ℕ) (hk : 1 ≤ k) :
    (FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p k).card ≤
      400 ^ k := by
  exact card_areaAnimals_le (G := plaquetteLinkGraph)
    (fun q => plaquetteLinkGraph_degree_le_twenty q) p k hk

end FroehlichSpencer.FS82.Wilson

end
