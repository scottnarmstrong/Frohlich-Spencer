/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Connected vertex sets for KP Claim 4.2

This is Kharash–Peled Claim 4.2.

This module records the finite-set connectivity interface and elementary path cases used by its
covering argument.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u

variable {V : Type u} [DecidableEq V] (G : SimpleGraph V)

/-- A finite set is connected in `G` when its induced subgraph is connected. -/
def IsConnectedVertexSet (s : Finset V) : Prop := (G.induce (s : Set V)).Connected

/-- An allowed KP Claim 4.2 covering set: it has two or three vertices and is connected in the
induced subgraph. -/
def IsC42Set (s : Finset V) : Prop :=
  (s.card = 2 ∨ s.card = 3) ∧ IsConnectedVertexSet G s

/-- A list of allowed sets covers a specified vertex set. Every listed set is required to stay
inside that vertex set. -/
def IsC42Cover (U : Set V) (C : List (Finset V)) : Prop :=
  (∀ s ∈ C, IsC42Set G s ∧ (s : Set V) ⊆ U) ∧ ∀ v ∈ U, ∃ s ∈ C, v ∈ s

/-- Connectivity of a finite induced vertex set is preserved when its vertices are embedded into
the ambient graph. -/
theorem IsConnectedVertexSet.image_subtype {S : Set V} [DecidablePred (· ∈ S)]
    (t : Finset S) (ht : IsConnectedVertexSet (G.induce S) t) :
    IsConnectedVertexSet G (t.image Subtype.val) := by
  classical
  let H := G.induce S
  let e : (H.induce (t : Set S)) →g
      G.induce ((t.image Subtype.val : Finset V) : Set V) := {
    toFun := fun x => ⟨x.val.val, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩
    map_rel' := by
      intro x y hxy
      simpa [H, SimpleGraph.induce_adj] using hxy
  }
  have he : Function.Surjective e := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases Finset.mem_image.mp hy with ⟨x, hxt, rfl⟩
    refine ⟨⟨x, hxt⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact ht.map e he

/-- A covering family on an induced subgraph transports to the ambient vertex set. -/
theorem IsC42Cover.image_subtype {S : Set V} [DecidablePred (· ∈ S)]
    {U : Set S} (C : List (Finset S))
    (hC : IsC42Cover (G.induce S) U C) :
    IsC42Cover G (Subtype.val '' U) (C.map fun s => s.image Subtype.val) := by
  classical
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases List.mem_map.mp hs with ⟨t, ht, rfl⟩
    rcases hC.1 t ht with ⟨⟨hcard, hconn⟩, _⟩
    refine ⟨?_, ?_⟩
    · have hcardImage : (t.image Subtype.val).card = t.card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      refine ⟨?_, IsConnectedVertexSet.image_subtype G t hconn⟩
      rcases hcard with h2 | h3
      · exact Or.inl (hcardImage.trans h2)
      · exact Or.inr (hcardImage.trans h3)
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      have hyU : (y : S) ∈ U := (hC.1 t ht).2 (by simpa using hy)
      exact ⟨y, hyU, rfl⟩
  · intro v hv
    change v ∈ Subtype.val '' U at hv
    rcases hv with ⟨w, hwU, rfl⟩
    obtain ⟨t, ht, hvt⟩ := hC.2 w hwU
    refine ⟨t.image Subtype.val, List.mem_map.mpr ⟨t, ht, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨w, hvt, rfl⟩

/-- An adjacent pair is connected in the ambient graph. -/
theorem isConnectedVertexSet_pair {u v : V} (huv : G.Adj u v) :
    IsConnectedVertexSet G {u, v} := by
  simp only [IsConnectedVertexSet]
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨u, by simp⟩, ?_⟩
  intro b
  rcases b with ⟨b, hb⟩
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hbu | hbv
  · subst b
    exact SimpleGraph.Reachable.rfl
  · subst b
    exact (show (G.induce ({u, v} : Finset V)).Adj ⟨u, by simp⟩ ⟨v, by simp⟩ by
      simpa using huv).reachable

/-- A path of two edges gives a connected triple, allowing the endpoint sets used in Claim 4.2. -/
theorem isConnectedVertexSet_triple_of_adj {u v w : V} (huv : G.Adj u v)
    (hvw : G.Adj v w) : IsConnectedVertexSet G {u, v, w} := by
  simp only [IsConnectedVertexSet]
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨u, by simp⟩, ?_⟩
  intro b
  rcases b with ⟨b, hb⟩
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hb
  have huv' : (G.induce ({u, v, w} : Finset V)).Reachable ⟨u, by simp⟩ ⟨v, by simp⟩ :=
    (show (G.induce ({u, v, w} : Finset V)).Adj ⟨u, by simp⟩ ⟨v, by simp⟩ by
      simpa using huv).reachable
  have hvw' : (G.induce ({u, v, w} : Finset V)).Reachable ⟨v, by simp⟩ ⟨w, by simp⟩ :=
    (show (G.induce ({u, v, w} : Finset V)).Adj ⟨v, by simp⟩ ⟨w, by simp⟩ by
      simpa using hvw).reachable
  have huw' := huv'.trans hvw'
  rcases hb with hbu | hb
  · subst b
    exact SimpleGraph.Reachable.rfl
  · rcases hb with hbv | hbw
    · subst b
      exact huv'
    · subst b
      exact huw'

omit [DecidableEq V] in
/-- Connectedness of an induced finite vertex set is monotone under graph inclusion. -/
theorem isConnectedVertexSet_mono {H : SimpleGraph V} (hGH : G ≤ H)
    (s : Finset V) (hconn : IsConnectedVertexSet G s) : IsConnectedVertexSet H s := by
  have hInd : G.induce (s : Set V) ≤ H.induce (s : Set V) := by
    intro x y hxy
    exact hGH hxy
  exact SimpleGraph.Connected.mono hInd hconn

omit [DecidableEq V] in
/-- A cover remains a cover when its ambient graph is enlarged. -/
theorem isC42Cover_mono {H : SimpleGraph V} (hGH : G ≤ H) {U : Set V}
    {C : List (Finset V)} (hC : IsC42Cover G U C) : IsC42Cover H U C := by
  refine ⟨?_, hC.2⟩
  intro s hs
  rcases hC.1 s hs with ⟨⟨hcard, hconn⟩, hsub⟩
  exact ⟨⟨hcard, isConnectedVertexSet_mono G hGH s hconn⟩, hsub⟩

/-- The first vertex of a longest simple path in a finite tree is a leaf. -/
theorem degree_eq_one_of_maximal_isPath_start [Fintype V] [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    (hnil : ¬ p.Nil) (hTree : G.IsTree) : G.degree u = 1 := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  refine ⟨p.snd, p.adj_snd hnil, ?_⟩
  intro w hadj
  apply hTree.isAcyclic.eq_snd_of_adj_start hp hadj
  by_contra hnot
  have hlong : (SimpleGraph.Walk.cons hadj.symm p).IsPath := hp.cons hnot
  have hle := hmax w v (SimpleGraph.Walk.cons hadj.symm p) hlong
  simp only [SimpleGraph.Walk.length_cons] at hle
  omega

/-- The last vertex of a longest simple path in a finite tree is a leaf. -/
theorem degree_eq_one_of_maximal_isPath_end [Fintype V] [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    (hnil : ¬ p.Nil) (hTree : G.IsTree) : G.degree v = 1 := by
  apply degree_eq_one_of_maximal_isPath_start G p.reverse hp.reverse ?_ (by simpa using hnil) hTree
  intro a b q hq
  have hle := hmax b a q.reverse hq.reverse
  simpa using hle

omit [DecidableEq V] in
/-- A longest path in a finite tree contains the terminal triple used in the corrected form of
KP Claim 4.2: the first vertex is a leaf, and either its neighbor has degree two or the third
vertex is a leaf. -/
theorem exists_leaf_terminal_triple_of_maximal_path [Fintype V] [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    (hnil : ¬ p.Nil) (hTree : G.IsTree) (hLong : 3 ≤ p.length) :
    ∃ a b c, a ≠ c ∧ G.degree a = 1 ∧ G.Adj a b ∧ G.Adj b c ∧
      (G.degree b = 2 ∨ G.degree c = 1) := by
  classical
  let b := p.snd
  let c₀ := p.tail.snd
  have htail : ¬ p.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, SimpleGraph.Walk.length_tail]
    omega
  have hab : G.Adj u b := by
    dsimp [b]
    exact p.adj_snd hnil
  have hbc₀ : G.Adj b c₀ := by
    dsimp [b, c₀]
    exact p.tail.adj_snd htail
  have hac₀ : u ≠ c₀ := by
    intro heq
    have hget : p.getVert 0 = p.getVert 2 := by
      simpa [c₀, SimpleGraph.Walk.snd, SimpleGraph.Walk.getVert_tail] using heq
    have hidx0 : (0 : ℕ) ≤ p.length := Nat.zero_le _
    have hidx2 : 2 ≤ p.length := by omega
    have hinj := hp.getVert_injOn hidx0 hidx2 hget
    omega
  by_cases hdeg : G.degree b = 2
  · exact ⟨u, b, c₀, hac₀, degree_eq_one_of_maximal_isPath_start G p hp hmax hnil hTree,
      hab, hbc₀, Or.inl hdeg⟩
  · have htwoMem : u ∈ G.neighborFinset b := by
      simpa [SimpleGraph.mem_neighborFinset] using hab.symm
    have hthreeMem : c₀ ∈ G.neighborFinset b := by
      simpa [SimpleGraph.mem_neighborFinset] using hbc₀
    have hsubset : ({u, c₀} : Finset V) ⊆ G.neighborFinset b := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact htwoMem
      · exact hthreeMem
    have hdegree_ge : 2 ≤ G.degree b := by
      have hcard := Finset.card_le_card hsubset
      rw [Finset.card_pair hac₀, SimpleGraph.card_neighborFinset_eq_degree] at hcard
      exact hcard
    have hdegree_gt : 2 < G.degree b := by omega
    have hcard : ({u, c₀} : Finset V).card < (G.neighborFinset b).card := by
      rw [Finset.card_pair hac₀, SimpleGraph.card_neighborFinset_eq_degree]
      exact hdegree_gt
    obtain ⟨c, hcMem, hcNot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hcAdj : G.Adj b c := by
      simpa [SimpleGraph.mem_neighborFinset] using hcMem
    have hcu : c ≠ u := by
      intro h
      subst c
      exact hcNot (Finset.mem_insert_self _ _)
    have hcc₀ : c ≠ c₀ := by
      intro h
      subst c
      exact hcNot (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hcNotTail : c ∉ p.tail.support := by
      intro hcTail
      have hEq := hTree.isAcyclic.eq_snd_of_adj_start hp.tail hcAdj hcTail
      exact hcc₀ hEq
    have hLeaf : G.degree c = 1 := by
      rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
      refine ⟨b, hcAdj.symm, ?_⟩
      intro w hcw
      by_contra hwb
      have hwNotTail : w ∉ p.tail.support := by
        intro hwTail
        let r := p.tail.takeUntil w hwTail
        have hr : r.IsPath := hp.tail.takeUntil hwTail
        let q : G.Walk b w := SimpleGraph.Walk.cons hcAdj
          (SimpleGraph.Walk.cons hcw SimpleGraph.Walk.nil)
        have hq : q.IsPath := by
          have hInner : (SimpleGraph.Walk.cons hcw SimpleGraph.Walk.nil).IsPath :=
            SimpleGraph.Walk.IsPath.nil.cons (by simpa using hcw.ne) (h := hcw)
          have houterStartNot : b ∉ (SimpleGraph.Walk.cons hcw SimpleGraph.Walk.nil).support := by
            simpa [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
              List.mem_singleton] using
              (show b ≠ c ∧ b ≠ w from ⟨hcAdj.ne, Ne.symm hwb⟩)
          exact hInner.cons houterStartNot (h := hcAdj)
        have hPathEq :=
          (hTree.isAcyclic.subsingleton_path b w).elim ⟨r, hr⟩ ⟨q, hq⟩
        have hEq : r = q := congrArg Subtype.val hPathEq
        have hcInR : c ∈ r.support := by
          rw [hEq]
          simp [q]
        exact hcNotTail (p.tail.support_takeUntil_subset_support hwTail hcInR)
      let inner := SimpleGraph.Walk.cons hcAdj.symm p.tail
      have hinner : inner.IsPath := hp.tail.cons hcNotTail
      have hwNotInner : w ∉ inner.support := by
        simpa [inner, SimpleGraph.Walk.support_cons] using
          (show w ≠ c ∧ w ∉ p.tail.support from ⟨Ne.symm hcw.ne, hwNotTail⟩)
      let longer := SimpleGraph.Walk.cons hcw.symm (SimpleGraph.Walk.cons hcAdj.symm p.tail)
      have hlonger : longer.IsPath := by
        dsimp [longer]
        exact hinner.cons hwNotInner
      have hle := hmax w v longer hlonger
      have hlen : longer.length = p.length + 1 := by
        simp [longer, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_tail]
        omega
      omega
    exact ⟨u, b, c, Ne.symm hcu, degree_eq_one_of_maximal_isPath_start G p hp hmax hnil hTree,
      hab, hcAdj, Or.inr hLeaf⟩

omit [DecidableEq V] in
/-- Every finite tree with at least four vertices has the terminal triple needed for the
two-vertex deletion induction. -/
theorem exists_leaf_chain_of_isTree_of_four_le_card [Fintype V] [DecidableRel G.Adj]
    (hTree : G.IsTree) (hlarge : 4 ≤ Fintype.card V) :
    ∃ a b c, a ≠ c ∧ G.degree a = 1 ∧ G.Adj a b ∧ G.Adj b c ∧
      (G.degree b = 2 ∨ G.degree c = 1) := by
  classical
  obtain ⟨a₀, b₀, hab₀⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  obtain ⟨q, hq⟩ := hTree.connected.exists_isPath a₀ b₀
  have hqpos : 0 < q.length := (q.not_nil_iff_lt_length).mp (q.not_nil_of_ne hab₀)
  obtain ⟨u, v, p, hp, hmax⟩ :=
    @SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length V G
      (Fintype.card_pos_iff.mp (by omega)) inferInstance
  have hpnil : ¬ p.Nil := by
    intro hpNil
    have hpzero := (SimpleGraph.Walk.length_eq_zero_iff).mpr hpNil
    have hle := hmax a₀ b₀ q hq
    omega
  have huDegree := degree_eq_one_of_maximal_isPath_start G p hp hmax hpnil hTree
  have hlong : 2 ≤ p.length := by
    by_contra h
    have hpLe : p.length ≤ 1 := by omega
    have hcover : ∀ x : V, x = u ∨ x = p.snd := by
      intro x
      obtain ⟨r, hr⟩ := hTree.connected.exists_isPath u x
      have hrLe := hmax u x r hr
      by_cases hrzero : r.length = 0
      · exact Or.inl ((SimpleGraph.Walk.length_eq_zero_iff.mp hrzero).eq.symm)
      · have hrone : r.length = 1 := by omega
        have hux : G.Adj u x := SimpleGraph.Walk.adj_of_length_eq_one hrone
        obtain ⟨y, huy, hyuniq⟩ :=
          (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp huDegree
        have hpUnique := hyuniq p.snd (p.adj_snd hpnil)
        exact Or.inr ((hyuniq x hux).trans hpUnique.symm)
    have hsubset : (Finset.univ : Finset V) ⊆ {u, p.snd} := by
      intro x hx
      simpa using hcover x
    have hcard := Finset.card_le_card hsubset
    have hpairs : ({u, p.snd} : Finset V).card ≤ 2 := by
      calc
        _ ≤ 1 + ({p.snd} : Finset V).card := Finset.card_insert_le _ _
        _ = 2 := by simp
    rw [Finset.card_univ] at hcard
    omega
  by_cases hlen2 : p.length = 2
  · have hEndDegree := degree_eq_one_of_maximal_isPath_end G p hp hmax hpnil hTree
    have hAdj₁ : G.Adj u p.snd := p.adj_snd hpnil
    have hAdj₂ : G.Adj p.snd v := by
      simpa [SimpleGraph.Walk.penultimate, hlen2, SimpleGraph.Walk.snd] using
        p.adj_penultimate hpnil
    have huNeV : u ≠ v := by
      intro huv
      have hget : p.getVert 0 = p.getVert p.length := by
        simpa [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length] using huv
      have hidx := hp.getVert_injOn (Nat.zero_le _) (le_rfl : p.length ≤ p.length) hget
      omega
    exact ⟨u, p.snd, v, huNeV, huDegree, hAdj₁, hAdj₂, Or.inr hEndDegree⟩
  · have hLong : 3 ≤ p.length := by omega
    exact exists_leaf_terminal_triple_of_maximal_path G p hp hmax hpnil hTree hLong

omit [DecidableEq V] in
/-- The universal induced vertex set is connected whenever the ambient graph is. -/
theorem isConnectedVertexSet_univ_of_connected [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) : IsConnectedVertexSet G Finset.univ := by
  classical
  simp only [IsConnectedVertexSet]
  let e : G →g G.induce (↑(Finset.univ : Finset V) : Set V) := {
    toFun := fun x => ⟨x, by simp⟩
    map_rel' := by
      intro x y hxy
      simpa [SimpleGraph.induce_adj] using hxy
  }
  have he : Function.Surjective e := by
    intro y
    refine ⟨y.1, ?_⟩
    apply Subtype.ext
    rfl
  exact SimpleGraph.Connected.map (G := G)
    (H := G.induce (↑(Finset.univ : Finset V) : Set V)) e he hconn

/-- Deleting one neighbor of a degree-two vertex leaves it degree one in the induced graph. -/
theorem degree_induce_compl_singleton_eq_one_of_adj_of_degree_eq_two
    [Fintype V] [DecidableRel G.Adj] {a b : V} (hab : G.Adj a b)
    (hdeg : G.degree b = 2) :
    (G.induce ({a}ᶜ : Set V)).degree ⟨b, by simpa using Ne.symm hab.ne⟩ = 1 := by
  classical
  let bs : ({a}ᶜ : Set V) := ⟨b, by simpa using Ne.symm hab.ne⟩
  have ha : a ∈ G.neighborFinset b := by
    simpa [SimpleGraph.mem_neighborFinset] using hab.symm
  have hcard : G.neighborFinset b ∩ ({a}ᶜ : Set V).toFinset =
      (G.neighborFinset b).erase a := by
    ext x
    simp [Finset.mem_inter, Finset.mem_erase, and_comm]
  have hone : (G.neighborFinset b ∩ ({a}ᶜ : Set V).toFinset).card = 1 := by
    rw [hcard, Finset.card_erase_of_mem ha,
      SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  have hm := SimpleGraph.map_neighborFinset_induce (G := G)
    (s := ({a}ᶜ : Set V)) bs
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    ((G.induce ({a}ᶜ : Set V)).neighborFinset bs).card =
        (((G.induce ({a}ᶜ : Set V)).neighborFinset bs).map
          (Function.Embedding.subtype (· ∈ ({a}ᶜ : Set V)))).card := by simp
    _ = (G.neighborFinset b ∩ ({a}ᶜ : Set V).toFinset).card := by rw [hm]
    _ = 1 := hone

/-- Removing a vertex not adjacent to a leaf preserves its degree in the induced graph. -/
theorem degree_induce_compl_singleton_eq_one_of_leaf_of_not_adj
    [Fintype V] [DecidableRel G.Adj] {a c : V} (hne : c ≠ a)
    (hdeg : G.degree c = 1) (hca : ¬ G.Adj c a) :
    (G.induce ({a}ᶜ : Set V)).degree ⟨c, hne⟩ = 1 := by
  classical
  have hsubset : G.neighborSet c ⊆ ({a}ᶜ : Set V) := by
    intro x hx
    change x ≠ a
    intro hxa
    subst x
    exact hca (by simpa [SimpleGraph.mem_neighborSet] using hx)
  rw [SimpleGraph.degree_induce_of_neighborSet_subset hsubset]
  exact hdeg

/-- A finite tree on at least two vertices has the KP Claim 4.2 cover. -/
theorem exists_tree_c42_cover :
    ∀ n : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (T : SimpleGraph W) [DecidableRel T.Adj],
      Fintype.card W = n → T.IsTree → 2 ≤ n →
        ∃ C : List (Finset W), C.length = n / 2 ∧ C.Nodup ∧
        IsC42Cover T Set.univ C := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W instF instD T instAdj hcard htree hn
    classical
    by_cases hsmall : n = 2 ∨ n = 3
    · refine ⟨[Finset.univ], ?_, List.nodup_singleton _, ?_⟩
      · simp
        omega
      · refine ⟨?_, ?_⟩
        · intro s hs
          simp only [List.mem_singleton] at hs
          subst s
          constructor
          · refine ⟨?_, ?_⟩
            · rcases hsmall with h2 | h3
              · left
                simp [hcard, h2]
              · right
                simp [hcard, h3]
            · exact isConnectedVertexSet_univ_of_connected T htree.connected
          · exact Set.subset_univ _
        · intro v hv
          exact ⟨Finset.univ, by simp, Finset.mem_univ _⟩
    · have hlarge : 4 ≤ Fintype.card W := by omega
      obtain ⟨a, b, c, hac, haDeg, hab, hbc, hcase⟩ :=
        exists_leaf_chain_of_isTree_of_four_le_card T htree hlarge
      have habNe : a ≠ b := hab.ne
      have hbcNe : b ≠ c := hbc.ne
      have hcardTriple : ({a, b, c} : Finset W).card = 3 := by
        simp [hac, habNe, hbcNe]
      have hconnTriple : IsConnectedVertexSet T ({a, b, c} : Finset W) :=
        isConnectedVertexSet_triple_of_adj T hab hbc
      let S₁ : Set W := ({a}ᶜ : Set W)
      let W₁ := S₁
      let H : SimpleGraph W₁ := T.induce S₁
      have hHconn : H.Connected := by
        simpa [H, W₁, S₁] using
          htree.connected.induce_compl_singleton_of_degree_eq_one (v := a) haDeg
      have hHacyc : H.IsAcyclic := by
        simpa [H, W₁, S₁] using htree.isAcyclic.induce S₁
      let d : W := if T.degree b = 2 then b else c
      have hdNeA : d ≠ a := by
        by_cases hdeg : T.degree b = 2
        · simpa [d, hdeg] using Ne.symm habNe
        · simpa [d, hdeg] using Ne.symm hac
      let d₁ : W₁ := ⟨d, hdNeA⟩
      have hdDegH : H.degree d₁ = 1 := by
        by_cases hdeg : T.degree b = 2
        · have hh := degree_induce_compl_singleton_eq_one_of_adj_of_degree_eq_two
            (G := T) hab hdeg
          have hd1eq : d₁ = (⟨b, Ne.symm habNe⟩ : W₁) := by
            apply Subtype.ext
            change d = b
            simp [d, hdeg]
          rw [hd1eq]
          simpa [H, W₁, S₁] using hh
        · have hcDeg : T.degree c = 1 := by
            rcases hcase with hb | hc
            · exact (hdeg hb).elim
            · exact hc
          have hca : ¬ T.Adj c a := by
            obtain ⟨x, hcx, hxuniq⟩ :=
              (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hcDeg
            intro hca
            have hax : a = x := hxuniq a hca
            have hbx : b = x := hxuniq b hbc.symm
            exact habNe (hax.trans hbx.symm)
          have hh := degree_induce_compl_singleton_eq_one_of_leaf_of_not_adj
            (G := T) (Ne.symm hac) hcDeg hca
          have hd1eq : d₁ = (⟨c, Ne.symm hac⟩ : W₁) := by
            apply Subtype.ext
            change d = c
            simp [d, hdeg]
          rw [hd1eq]
          simpa [H, W₁, S₁] using hh
      let S₂ : Set W₁ := ({d₁}ᶜ : Set W₁)
      let W₂ := S₂
      let R : SimpleGraph W₂ := H.induce S₂
      have hRconn : R.Connected := by
        simpa [R, W₂, S₂] using
          hHconn.induce_compl_singleton_of_degree_eq_one (v := d₁) hdDegH
      have hRacyc : R.IsAcyclic := by
        simpa [R, W₂, S₂] using hHacyc.induce S₂
      have hRtree : R.IsTree := ⟨hRconn, hRacyc⟩
      have hcard₁ : Fintype.card W₁ = Fintype.card W - 1 := by
        change Fintype.card {x : W // x ≠ a} = _
        rw [Fintype.card_subtype_compl (p := fun x : W => x = a)]
        simp
      have hcard₂ : Fintype.card W₂ = n - 2 := by
        calc
          Fintype.card W₂ = Fintype.card W₁ - 1 := by
            change Fintype.card {x : W₁ // x ≠ d₁} = _
            rw [Fintype.card_subtype_compl (p := fun x : W₁ => x = d₁)]
            simp
          _ = n - 2 := by rw [hcard₁, hcard]; omega
      have hn₂ : 2 ≤ n - 2 := by omega
      obtain ⟨C, hlen, hnodup, hcover⟩ :=
        ih (n - 2) (by omega) (W := W₂) R hcard₂ hRtree hn₂
      have hcover₁ : IsC42Cover H
          ((Subtype.val : (↑W₂) → (↑W₁)) '' (Set.univ : Set (↑W₂)))
          (C.map fun s => s.image Subtype.val) := by
        simpa [R, W₂, S₂] using
          IsC42Cover.image_subtype H (S := S₂) (U := Set.univ) C hcover
      have hcover₂ : IsC42Cover T
          ((Subtype.val : (↑W₁) → W) ''
            ((Subtype.val : (↑W₂) → (↑W₁)) '' (Set.univ : Set (↑W₂))))
          ((C.map fun s => s.image Subtype.val).map fun s => s.image Subtype.val) := by
        exact IsC42Cover.image_subtype T (S := S₁)
          (C.map fun s => s.image Subtype.val) hcover₁
      let f₂ : Finset (↑W₂) → Finset (↑W₁) := fun s => s.image Subtype.val
      let f₁ : Finset (↑W₁) → Finset W := fun s => s.image Subtype.val
      have hf₂ : Function.Injective f₂ := by
        intro s t h
        exact (Finset.image_inj Subtype.val_injective).mp h
      have hf₁ : Function.Injective f₁ := by
        intro s t h
        exact (Finset.image_inj Subtype.val_injective).mp h
      let C₂ := (C.map f₂).map f₁
      have hnodup₂ : C₂.Nodup := by
        have hnd := (hnodup.map hf₂).map hf₁
        simpa [C₂, f₁, f₂] using hnd
      have haNotMem : ∀ s ∈ C₂, a ∉ s := by
        intro s hs haS
        have hs' : s ∈ ((C.map fun s => s.image Subtype.val).map
            fun s => s.image Subtype.val) := by simpa [C₂, f₁, f₂] using hs
        have haU : a ∈ ((Subtype.val : (↑W₁) → W) ''
            ((Subtype.val : (↑W₂) → (↑W₁)) '' (Set.univ : Set (↑W₂)))) :=
          (hcover₂.1 s hs').2 (by simpa using haS)
        rcases haU with ⟨w, hw, hwa⟩
        exact w.property hwa
      let C₃ := ({a, b, c} : Finset W) :: C₂
      have hnodup₃ : C₃.Nodup := by
        simp only [C₃, List.nodup_cons]
        constructor
        · intro hs
          exact haNotMem _ hs (by simp)
        · exact hnodup₂
      have hlen₂ : C₂.length = (n - 2) / 2 := by
        simp [C₂, hlen]
      refine ⟨C₃, ?_, hnodup₃, ?_⟩
      · simp [C₃, hlen₂]
        omega
      · refine ⟨?_, ?_⟩
        · intro s hs
          simp only [C₃, List.mem_cons] at hs
          rcases hs with hs | hs
          · subst s
            refine ⟨⟨Or.inr ?_, hconnTriple⟩, Set.subset_univ _⟩
            exact hcardTriple
          · rcases hcover₂.1 s hs with ⟨hallowed, hsubset⟩
            exact ⟨hallowed, Set.subset_univ _⟩
        · intro v hv
          by_cases hva : v = a
          · subst v
            exact ⟨{a, b, c}, by simp [C₃], by simp⟩
          · by_cases hvb : v = b
            · subst v
              exact ⟨{a, b, c}, by simp [C₃], by simp⟩
            · by_cases hvc : v = c
              · subst v
                exact ⟨{a, b, c}, by simp [C₃], by simp⟩
              · have hvNotD : v ≠ d := by
                  by_cases hdeg : T.degree b = 2
                  · simpa [d, hdeg] using hvb
                  · simpa [d, hdeg] using hvc
                have hvU : v ∈
                    ((Subtype.val : (↑W₁) → W) ''
                      ((Subtype.val : (↑W₂) → (↑W₁)) '' (Set.univ : Set (↑W₂)))) := by
                  refine ⟨⟨v, hva⟩, ?_, rfl⟩
                  refine ⟨⟨⟨v, hva⟩, ?_⟩, Set.mem_univ _, rfl⟩
                  intro heq
                  exact hvNotD (congrArg Subtype.val heq)
                obtain ⟨s, hs, hvs⟩ := hcover₂.2 v hvU
                refine ⟨s, ?_, hvs⟩
                simp only [C₃, List.mem_cons]
                right
                simpa [C₂] using hs

/-- Splitting a natural number into pairs and a possible odd remainder. -/
theorem nat_eq_twice_div_two_add_odd (n : ℕ) :
    n = 2 * (n / 2) + if Odd n then 1 else 0 := by
  by_cases h : Odd n
  · rcases h with ⟨k, hk⟩
    simp [show Odd n from ⟨k, hk⟩]
    omega
  · have he : Even n := (Nat.even_or_odd n).resolve_right h
    rcases he with ⟨k, hk⟩
    simp [h]
    omega

/-- The connected component supports partition the finite vertex set. -/
theorem sum_connectedComponent_ncard [Fintype V] [DecidableRel G.Adj] :
    ∑ c : G.ConnectedComponent, c.supp.ncard = Fintype.card V := by
  classical
  have hdisj : ∀ c ∈ (Finset.univ : Finset G.ConnectedComponent),
      ∀ d ∈ (Finset.univ : Finset G.ConnectedComponent), c ≠ d →
        Disjoint c.supp.toFinset d.supp.toFinset := by
    intro c hc d hd hcd
    apply Set.disjoint_toFinset.mpr
    exact (SimpleGraph.pairwise_disjoint_supp_connectedComponent G) hcd
  have hUnion : (Finset.univ : Finset G.ConnectedComponent).biUnion
      (fun c => c.supp.toFinset) = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_toFinset]
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨G.connectedComponentMk v,
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  calc
    _ = ∑ c ∈ (Finset.univ : Finset G.ConnectedComponent),
        (c.supp.toFinset).card := by simp_rw [Set.ncard_eq_toFinset_card']
    _ = ((Finset.univ : Finset G.ConnectedComponent).biUnion
        (fun c => c.supp.toFinset)).card := (Finset.card_biUnion hdisj).symm
    _ = Fintype.card V := by simp [hUnion]

omit [DecidableEq V] in
/-- Distinct connected-component supports are disjoint. -/
theorem connectedComponent_support_disjoint [DecidableRel G.Adj]
    (c d : G.ConnectedComponent) (hcd : c ≠ d) :
    Disjoint c.supp d.supp := by
  exact (SimpleGraph.pairwise_disjoint_supp_connectedComponent G) hcd

/-- The finite-set representation of an unordered pair is injective. -/
theorem sym2_toFinset_injective :
    Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e f h
  apply Sym2.ext
  intro x
  simpa only [Sym2.mem_toFinset] using
    Iff.of_eq (congrArg (fun s : Finset V => x ∈ s) h)

/-- An odd-sized finite tree cover leaves an edge pair unused. -/
theorem exists_tree_c42_cover_unused_edge [Fintype V] [DecidableRel G.Adj]
    (hTree : G.IsTree) (hodd : Odd (Fintype.card V))
    (hsize : 2 ≤ Fintype.card V) :
    ∃ C : List (Finset V), C.length = Fintype.card V / 2 ∧ C.Nodup ∧
      IsC42Cover G Set.univ C ∧
      ∃ e ∈ G.edgeFinset, e.toFinset ∉ C.toFinset := by
  classical
  obtain ⟨C, hlen, hnodup, hcover⟩ :=
    exists_tree_c42_cover (Fintype.card V) G rfl hTree hsize
  let E := G.edgeFinset.image Sym2.toFinset
  have hEdges : E.card + 1 = Fintype.card V := by
    dsimp [E]
    rw [Finset.card_image_of_injective _ sym2_toFinset_injective]
    exact hTree.card_edgeFinset
  have hlt : C.toFinset.card < E.card := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
    rcases hodd with ⟨k, hk⟩
    omega
  obtain ⟨s, hsE, hsNot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hsE
  exact ⟨C, hlen, hnodup, hcover, e, he, hsNot⟩

/-- Each connected component of a finite graph without isolated vertices has a tree cover. -/
theorem exists_component_c42_cover [Fintype V] [DecidableRel G.Adj]
    (hNoIsolates : ∀ v : V, ∃ w : V, G.Adj v w)
    (c : G.ConnectedComponent) [Fintype c] :
    ∃ C : List (Finset c), C.length = c.supp.ncard / 2 ∧ C.Nodup ∧
      IsC42Cover c.toSimpleGraph Set.univ C := by
  classical
  obtain ⟨v, hv⟩ := c.nonempty_supp
  obtain ⟨w, hvw⟩ := hNoIsolates v
  have hw : w ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    calc
      G.connectedComponentMk w = G.connectedComponentMk v :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvw).symm
      _ = c := hv
  let v' : c := ⟨v, hv⟩
  let w' : c := ⟨w, hw⟩
  have hne : v' ≠ w' := by
    intro h
    exact hvw.ne (congrArg Subtype.val h)
  have hcard : 2 ≤ Fintype.card c := by
    calc
      2 = ({v', w'} : Finset c).card := (Finset.card_pair hne).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card c := Finset.card_univ
  have hcCard : Fintype.card c = c.supp.ncard := by
    change Fintype.card c.supp = c.supp.ncard
    exact Set.fintypeCard_eq_ncard c.supp
  obtain ⟨T, hTle, hTtree⟩ := c.connected_toSimpleGraph.exists_isTree_le
  obtain ⟨C, hlen, hnodup, hcover⟩ :=
    exists_tree_c42_cover (Fintype.card c) T rfl hTtree hcard
  refine ⟨C, ?_, hnodup, isC42Cover_mono (G := T) (H := c.toSimpleGraph) hTle hcover⟩
  simpa [hcCard] using hlen

/-- Odd components provide an additional connected pair outside the tree cover. -/
theorem exists_component_c42_cover_unused_pair [Fintype V] [DecidableRel G.Adj]
    (hNoIsolates : ∀ v : V, ∃ w : V, G.Adj v w)
    (c : G.ConnectedComponent) [Fintype c] (hodd : Odd c.supp.ncard) :
    ∃ C : List (Finset c), C.length = c.supp.ncard / 2 ∧ C.Nodup ∧
      IsC42Cover c.toSimpleGraph Set.univ C ∧
      ∃ s : Finset c, s.card = 2 ∧ IsConnectedVertexSet c.toSimpleGraph s ∧
        s ∉ C.toFinset := by
  classical
  obtain ⟨v, hv⟩ := c.nonempty_supp
  obtain ⟨w, hvw⟩ := hNoIsolates v
  have hw : w ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    calc
      G.connectedComponentMk w = G.connectedComponentMk v :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvw).symm
      _ = c := hv
  let v' : c := ⟨v, hv⟩
  let w' : c := ⟨w, hw⟩
  have hne : v' ≠ w' := by
    intro h
    exact hvw.ne (congrArg Subtype.val h)
  have hcard : 2 ≤ Fintype.card c := by
    calc
      2 = ({v', w'} : Finset c).card := (Finset.card_pair hne).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card c := Finset.card_univ
  have hcCard : Fintype.card c = c.supp.ncard := by
    change Fintype.card c.supp = c.supp.ncard
    exact Set.fintypeCard_eq_ncard c.supp
  obtain ⟨T, hTle, hTtree⟩ := c.connected_toSimpleGraph.exists_isTree_le
  have hodd' : Odd (Fintype.card c) := by simpa [hcCard] using hodd
  obtain ⟨C, hlen, hnodup, hcover, e, he, hunused⟩ :=
    exists_tree_c42_cover_unused_edge (G := T) hTtree hodd' hcard
  have heedge : e ∈ T.edgeSet := SimpleGraph.mem_edgeFinset.mp he
  have hadj : T.Adj e.out.1 e.out.2 := by
    rw [← e.out_eq] at heedge
    exact (SimpleGraph.mem_edgeSet (G := T) (v := e.out.1) (w := e.out.2)).mp heedge
  have hpairSet : e.toFinset = {e.out.1, e.out.2} := by
    calc
      e.toFinset = (s(e.out.1, e.out.2)).toFinset :=
        congrArg Sym2.toFinset e.out_eq.symm
      _ = {e.out.1, e.out.2} := Sym2.toFinset_mk_eq
  have hpaircard : e.toFinset.card = 2 := by
    rw [Sym2.card_toFinset_of_not_isDiag e (T.not_isDiag_of_mem_edgeSet heedge)]
  have hpairconn : IsConnectedVertexSet T e.toFinset := by
    rw [hpairSet]
    exact isConnectedVertexSet_pair T hadj
  have hcover' : IsC42Cover c.toSimpleGraph Set.univ C :=
    isC42Cover_mono (G := T) (H := c.toSimpleGraph) hTle hcover
  refine ⟨C, ?_, hnodup, hcover', e.toFinset, hpaircard,
    isConnectedVertexSet_mono (G := T) hTle e.toFinset hpairconn, hunused⟩
  simpa [hcCard] using hlen

/-- A component's tree cover maps to a cover of its support in the original graph. -/
theorem exists_component_c42_cover_in_ambient [Fintype V] [DecidableRel G.Adj]
    (hNoIsolates : ∀ v : V, ∃ w : V, G.Adj v w)
    (c : G.ConnectedComponent) [Fintype c] :
    ∃ C : List (Finset V), C.length = c.supp.ncard / 2 ∧ C.Nodup ∧
      IsC42Cover G c.supp C := by
  classical
  obtain ⟨C, hlen, hnodup, hcover⟩ := exists_component_c42_cover G hNoIsolates c
  change IsC42Cover (G.induce c.supp) Set.univ C at hcover
  have hmap : IsC42Cover G ((Subtype.val : c → V) '' (Set.univ : Set c))
      (C.map fun s => s.image Subtype.val) :=
    IsC42Cover.image_subtype G (S := c.supp) (U := Set.univ) C hcover
  have hset : ((Subtype.val : c → V) '' (Set.univ : Set c)) = c.supp := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact x.property
    · intro hv
      exact ⟨⟨v, hv⟩, Set.mem_univ _, rfl⟩
  have hnodupMap : (C.map fun s => s.image Subtype.val).Nodup := by
    apply hnodup.map
    intro s t h
    exact (Finset.image_inj Subtype.val_injective).mp h
  refine ⟨C.map fun s => s.image Subtype.val, ?_, hnodupMap, ?_⟩
  · simpa using hlen
  · rw [← hset]
    exact hmap

/-- A component cover can be chosen with an additional unused pair when the component is odd. -/
theorem exists_component_c42_cover_with_optional_pair [Fintype V] [DecidableRel G.Adj]
    (hNoIsolates : ∀ v : V, ∃ w : V, G.Adj v w)
    (c : G.ConnectedComponent) [Fintype c] :
    ∃ C : List (Finset V), C.length = c.supp.ncard / 2 ∧ C.Nodup ∧
      IsC42Cover G c.supp C ∧
      (Odd c.supp.ncard → ∃ s : Finset V, s.card = 2 ∧
        IsConnectedVertexSet G s ∧ (s : Set V) ⊆ c.supp ∧ s ∉ C.toFinset) := by
  classical
  by_cases hodd : Odd c.supp.ncard
  · obtain ⟨C, hlen, hnodup, hcover, s, hcard, hconn, hsNot⟩ :=
      exists_component_c42_cover_unused_pair G hNoIsolates c hodd
    let C' := C.map fun t => t.image Subtype.val
    let s' := s.image Subtype.val
    have hcover' : IsC42Cover G c.supp C' := by
      have hmap : IsC42Cover G ((Subtype.val : c → V) '' (Set.univ : Set c)) C' :=
        IsC42Cover.image_subtype G (S := c.supp) (U := Set.univ) C hcover
      have hset : ((Subtype.val : c → V) '' (Set.univ : Set c)) = c.supp := by
        ext v
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact x.property
        · intro hv
          exact ⟨⟨v, hv⟩, Set.mem_univ _, rfl⟩
      rw [← hset]
      exact hmap
    have hnodup' : C'.Nodup := by
      apply hnodup.map
      intro t u h
      exact (Finset.image_inj Subtype.val_injective).mp h
    have hnot' : s' ∉ C'.toFinset := by
      intro hs'
      have hsmem : s' ∈ C' := List.mem_toFinset.mp hs'
      rcases List.mem_map.mp hsmem with ⟨t, ht, hEq⟩
      have hts : t = s := (Finset.image_inj Subtype.val_injective).mp hEq
      subst t
      exact hsNot (List.mem_toFinset.mpr ht)
    have hconn' : IsConnectedVertexSet (G.induce c.supp) s := by
      change IsConnectedVertexSet c.toSimpleGraph s
      exact hconn
    refine ⟨C', ?_, hnodup', hcover', ?_⟩
    · simp [C', hlen]
    · intro _
      refine ⟨s', ?_, IsConnectedVertexSet.image_subtype G s hconn', ?_, hnot'⟩
      · rw [Finset.card_image_of_injective _ Subtype.val_injective, hcard]
      · intro v hv
        rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
        exact w.property
  · obtain ⟨C, hlen, hnodup, hcover⟩ :=
      exists_component_c42_cover_in_ambient G hNoIsolates c
    exact ⟨C, hlen, hnodup, hcover, fun h => (hodd h).elim⟩

/-- The componentwise pair counts and odd components give the global floor identity. -/
theorem card_eq_twice_component_halves_add_odd [Fintype V] [DecidableRel G.Adj] :
    Fintype.card V =
      2 * (∑ c : G.ConnectedComponent, c.supp.ncard / 2) +
        (Finset.univ.filter
          (fun c : G.ConnectedComponent => Odd c.supp.ncard)).card := by
  classical
  let O := Finset.univ.filter
    (fun c : G.ConnectedComponent => Odd c.supp.ncard)
  have hO : (∑ c : G.ConnectedComponent,
      if Odd c.supp.ncard then 1 else 0) = O.card := by
    simp [O]
  calc
    Fintype.card V = ∑ c : G.ConnectedComponent, c.supp.ncard :=
      (sum_connectedComponent_ncard G).symm
    _ = ∑ c : G.ConnectedComponent,
        (2 * (c.supp.ncard / 2) + if Odd c.supp.ncard then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact nat_eq_twice_div_two_add_odd c.supp.ncard
    _ = 2 * (∑ c : G.ConnectedComponent, c.supp.ncard / 2) + O.card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, hO]

/-- The number of missing component pairs is half the number of odd components. -/
theorem card_div_two_eq_component_halves_add_odd_div_two
    [Fintype V] [DecidableRel G.Adj] :
    Fintype.card V / 2 =
      (∑ c : G.ConnectedComponent, c.supp.ncard / 2) +
        (Finset.univ.filter
          (fun c : G.ConnectedComponent => Odd c.supp.ncard)).card / 2 := by
  have h := card_eq_twice_component_halves_add_odd G
  omega

/-- KP Claim 4.2: every finite nonempty graph without isolated vertices has the stated cover. -/
theorem claim_4_2 [Fintype V] [Nonempty V] [DecidableRel G.Adj]
    (hNoIsolates : ∀ v : V, ∃ w : V, G.Adj v w) :
    ∃ C : List (Finset V), C.length = Fintype.card V / 2 ∧ C.Nodup ∧
      IsC42Cover G Set.univ C := by
  classical
  let Cover : ∀ c : G.ConnectedComponent, List (Finset V) := fun c =>
    Classical.choose (exists_component_c42_cover_with_optional_pair G hNoIsolates c)
  have hCover : ∀ c : G.ConnectedComponent,
      (Cover c).length = c.supp.ncard / 2 ∧ (Cover c).Nodup ∧
      IsC42Cover G c.supp (Cover c) ∧
        (Odd c.supp.ncard → ∃ s : Finset V, s.card = 2 ∧
          IsConnectedVertexSet G s ∧ (s : Set V) ⊆ c.supp ∧
            s ∉ (Cover c).toFinset) := by
    intro c
    exact Classical.choose_spec
      (exists_component_c42_cover_with_optional_pair G hNoIsolates c)
  let Fam : G.ConnectedComponent → Finset (Finset V) := fun c => (Cover c).toFinset
  let Base : Finset (Finset V) := Finset.univ.biUnion Fam
  have hFamDisjoint : ∀ c ∈ (Finset.univ : Finset G.ConnectedComponent),
      ∀ d ∈ Finset.univ, c ≠ d → Disjoint (Fam c) (Fam d) := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro s hsC hsD
    have hsC' : s ∈ Cover c := List.mem_toFinset.mp hsC
    have hsD' : s ∈ Cover d := List.mem_toFinset.mp hsD
    have hallowedC := ((hCover c).2.2.1).1 s hsC'
    have hallowedD := ((hCover d).2.2.1).1 s hsD'
    have hpos : 0 < s.card := by
      rcases hallowedC.1.1 with h2 | h3 <;> omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have hvsC : v ∈ c.supp := hallowedC.2 hv
    have hvsD : v ∈ d.supp := hallowedD.2 hv
    have hdisj := connectedComponent_support_disjoint G c d hcd
    exact (Set.disjoint_left.mp hdisj) hvsC hvsD
  have hBaseCard : Base.card = ∑ c : G.ConnectedComponent, c.supp.ncard / 2 := by
    calc
      Base.card = ∑ c ∈ (Finset.univ : Finset G.ConnectedComponent), (Fam c).card := by
        simpa [Base, Fam] using (Finset.card_biUnion hFamDisjoint)
      _ = ∑ c : G.ConnectedComponent, c.supp.ncard / 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [Fam, List.toFinset_card_of_nodup (hCover c).2.1, (hCover c).1]
  have hBaseCovers : ∀ v : V, ∃ s ∈ Base, v ∈ s := by
    intro v
    let c := G.connectedComponentMk v
    have hv : v ∈ c.supp := by
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    obtain ⟨s, hs, hvs⟩ := (hCover c).2.2.1.2 v hv
    refine ⟨s, ?_, hvs⟩
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, ?_⟩
    exact List.mem_toFinset.mpr hs
  let O : Finset G.ConnectedComponent := Finset.univ.filter
    (fun c => Odd c.supp.ncard)
  obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq (Nat.div_le_self O.card 2)
  let Extra : G.ConnectedComponent → Finset V := fun c =>
    if hc : Odd c.supp.ncard then Classical.choose ((hCover c).2.2.2 hc) else ∅
  have hExtraSpec (c : G.ConnectedComponent) (hc : Odd c.supp.ncard) :
      (Extra c).card = 2 ∧ IsConnectedVertexSet G (Extra c) ∧
        ((Extra c : Finset V) : Set V) ⊆ c.supp ∧ (Extra c) ∉ Fam c := by
    simpa only [Extra, dite_eq_left hc, Fam] using
      Classical.choose_spec ((hCover c).2.2.2 hc)
  let Extras : Finset (Finset V) := K.image Extra
  have hExtraInj : Set.InjOn Extra (K : Set G.ConnectedComponent) := by
    intro c hc d hd hEq
    by_contra hcd
    have hcOdd : Odd c.supp.ncard := (Finset.mem_filter.mp (hKsub hc)).2
    have hdOdd : Odd d.supp.ncard := (Finset.mem_filter.mp (hKsub hd)).2
    have hcSpec := hExtraSpec c hcOdd
    have hdSpec := hExtraSpec d hdOdd
    have hpos : 0 < (Extra c).card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have hvd : v ∈ Extra d := by simpa [hEq] using hv
    have hvC : v ∈ c.supp := hcSpec.2.2.1 hv
    have hvD : v ∈ d.supp := hdSpec.2.2.1 hvd
    have hdisj := connectedComponent_support_disjoint G c d hcd
    exact (Set.disjoint_left.mp hdisj) hvC hvD
  have hExtrasCard : Extras.card = K.card := by
    dsimp [Extras]
    exact Finset.card_image_of_injOn hExtraInj
  have hBaseExtrasDisjoint : Disjoint Base Extras := by
    apply Finset.disjoint_left.mpr
    intro s hsBase hsExtra
    rcases Finset.mem_biUnion.mp hsBase with ⟨d, hd, hsD⟩
    rcases Finset.mem_image.mp hsExtra with ⟨c, hc, hcs⟩
    have hcOdd : Odd c.supp.ncard := (Finset.mem_filter.mp (hKsub hc)).2
    have hcSpec := hExtraSpec c hcOdd
    have hpos : 0 < s.card := by rw [← hcs, hcSpec.1]; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have hvC : v ∈ c.supp := by
      apply hcSpec.2.2.1
      simpa [hcs] using hv
    have hvD : v ∈ d.supp :=
      (((hCover d).2.2.1).1 s (List.mem_toFinset.mp hsD)).2 hv
    have hcd : c = d := by
      by_contra hneq
      have hdisj := connectedComponent_support_disjoint G c d hneq
      exact (Set.disjoint_left.mp hdisj) hvC hvD
    have hsC : s ∈ Fam c := hcd.symm ▸ hsD
    have hExtraFam : Extra c ∈ Fam c := by simpa [hcs] using hsC
    exact hcSpec.2.2.2 hExtraFam
  let Final : Finset (Finset V) := Base ∪ Extras
  have hFinalCard : Final.card = Fintype.card V / 2 := by
    rw [Finset.card_union_of_disjoint hBaseExtrasDisjoint, hBaseCard, hExtrasCard,
      hKcard, card_div_two_eq_component_halves_add_odd_div_two G]
  have hFinalCover : IsC42Cover G Set.univ Final.toList := by
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs' : s ∈ Final := Finset.mem_toList.mp hs
      rcases Finset.mem_union.mp hs' with hsBase | hsExtra
      · rcases Finset.mem_biUnion.mp hsBase with ⟨c, hc, hsC⟩
        have hsC' : s ∈ Cover c := List.mem_toFinset.mp hsC
        exact ⟨(((hCover c).2.2.1).1 s hsC').1, Set.subset_univ _⟩
      · rcases Finset.mem_image.mp hsExtra with ⟨c, hc, hcs⟩
        have hcOdd : Odd c.supp.ncard := (Finset.mem_filter.mp (hKsub hc)).2
        have hsC := hExtraSpec c hcOdd
        refine ⟨⟨Or.inl ?_, ?_⟩, Set.subset_univ _⟩
        · simpa [hcs] using hsC.1
        · simpa [hcs] using hsC.2.1
    · intro v hv
      obtain ⟨s, hs, hvs⟩ := hBaseCovers v
      refine ⟨s, Finset.mem_toList.mpr ?_, hvs⟩
      exact Finset.mem_union.mpr (Or.inl hs)
  refine ⟨Final.toList, ?_, Finset.nodup_toList _, hFinalCover⟩
  simpa [Finset.length_toList] using hFinalCard

end FroehlichSpencer.BKT

end
