/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.SourceLatticeChain
public import FroehlichSpencer.FS82.Cubical.IntegerPrism

/-! Coordinate paths for the ShortPhase exterior shell. -/

public section

namespace FroehlichSpencer.FS82.Currents.ShortPhase

open Cubical
open Classical

noncomputable section

@[expose] def vertexCell {B : Box 4} (v : Anchor 4 B) : Cell 4 B :=
  fun i => Sum.inl (v i)

@[expose] def pathStage {B : Box 4} (p q : Anchor 4 B) (k : ℕ) :
    Anchor 4 B := fun j => if j.val < k then q j else p j

@[expose] def cubePath {B : Box 4} (p q : Anchor 4 B) : Chain 4 B :=
  ∑ i : Fin 4, signedPathEdges (vertexCell (pathStage p q i.val)) i
    (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
      (Nat.le_of_lt_succ (q i).isLt)

@[expose] def natGap (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

theorem vertexCell_update {B : Box 4} (p : Anchor 4 B) (i : Fin 4)
    (v : Fin (B i + 1)) :
    vertexUpdate (vertexCell p) i v = vertexCell (Function.update p i v) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [vertexCell, vertexUpdate]
  · simp [vertexCell, vertexUpdate, Function.update_of_ne h]

theorem pathStage_succ {B : Box 4} (p q : Anchor 4 B) (i : Fin 4) :
    Function.update (pathStage p q i.val) i (q i) =
      pathStage p q (i.val + 1) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [pathStage]
  · have hval : j.val ≠ i.val := by
      intro h
      apply hji
      exact Fin.ext h
    have hlt : j.val < i.val + 1 ↔ j.val < i.val := by omega
    change (Function.update
      (fun k : Fin 4 => if k.val < i.val then q k else p k) i (q i)) j =
      if j.val < i.val + 1 then q j else p j
    rw [Function.update_of_ne hji]
    simp only [hlt]

theorem axisBoundary_cubePathPiece {B : Box 4} (p q : Anchor 4 B)
    (i : Fin 4) :
    boundary (signedPathEdges (vertexCell (pathStage p q i.val)) i
      (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
      (Nat.le_of_lt_succ (q i).isLt)) =
      basisChain (vertexCell (pathStage p q (i.val + 1))) -
        basisChain (vertexCell (pathStage p q i.val)) := by
  let c := vertexCell (pathStage p q i.val)
  have hself : axisBoundary (B := B) i
      (signedPathEdges c i (p i).val (q i).val
        (Nat.le_of_lt_succ (p i).isLt) (Nat.le_of_lt_succ (q i).isLt)) =
      basisChain (vertexCell (pathStage p q (i.val + 1))) -
        basisChain c := by
    rw [axisBoundary_signedPathEdges, vertexCell_update, vertexCell_update]
    dsimp [c]
    rw [pathStage_succ]
    have hp : Function.update (pathStage p q i.val) i (p i) =
        pathStage p q i.val := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [pathStage]
      · simp [Function.update_of_ne hji]
    rw [hp]
    change ((-1 : ℤ) ^ cellRankBefore (vertexCell (pathStage p q i.val)) i) •
        (basisChain (vertexCell (pathStage p q (i.val + 1))) -
          basisChain (vertexCell (pathStage p q i.val))) = _
    rw [show cellRankBefore (vertexCell (pathStage p q i.val)) i = 0 by
      simp [cellRankBefore, vertexCell, coordIsEdge]]
    norm_num
  change (∑ j : Fin 4, axisBoundary (B := B) j
      (signedPathEdges (vertexCell (pathStage p q i.val)) i
        (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
        (Nat.le_of_lt_succ (q i).isLt))) = _
  rw [Finset.sum_eq_single i]
  · exact hself
  · intro j hj hji
    have hcj : (vertexCell (pathStage p q i.val)) j =
        Sum.inl (pathStage p q i.val j) := rfl
    exact axisBoundary_signedPathEdges_vertex_other
      (c := vertexCell (pathStage p q i.val)) (i := i) (j := j)
      (hij := Ne.symm hji) (w := pathStage p q i.val j) (hcj := hcj)
      (a := (p i).val) (b := (q i).val)
      (ha := Nat.le_of_lt_succ (p i).isLt)
      (hb := Nat.le_of_lt_succ (q i).isLt)
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem cubePath_boundary {B : Box 4} (p q : Anchor 4 B) :
    boundary (cubePath p q) = basisChain (vertexCell q) -
      basisChain (vertexCell p) := by
  unfold cubePath
  rw [map_sum]
  calc
    (∑ i : Fin 4, boundary (signedPathEdges (vertexCell (pathStage p q i.val)) i
        (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
        (Nat.le_of_lt_succ (q i).isLt))) =
      ∑ i : Fin 4, (basisChain (vertexCell (pathStage p q (i.val + 1))) -
        basisChain (vertexCell (pathStage p q i.val))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact axisBoundary_cubePathPiece p q i
    _ = basisChain (vertexCell q) - basisChain (vertexCell p) := by
      let f : ℕ → Chain 4 B := fun k => basisChain (vertexCell (pathStage p q k))
      have htelescope :
          (∑ i ∈ Finset.range 4, (f (i + 1) - f i)) = f 4 - f 0 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num
      let g : ℕ → Chain 4 B := fun n => f (n + 1) - f n
      have hsumFin :
          (∑ i : Fin 4, g i.val) = f 4 - f 0 := by
        exact (Fin.sum_univ_eq_sum_range g 4).trans htelescope
      rw [hsumFin]
      have hstart : pathStage p q 0 = p := by
        funext i
        simp [pathStage]
      have hend : pathStage p q 4 = q := by
        funext i
        simp [pathStage]
      dsimp [f]
      rw [hend, hstart]

theorem homogeneousSupport_finset_sum {B : Box 4} {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Chain 4 B) (k : ℕ)
    (hf : ∀ i ∈ s, homogeneousSupport (f i) k) :
    homogeneousSupport (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [homogeneousSupport]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply homogeneousSupport_add
      · exact hf i (Finset.mem_insert_self i s)
      · apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)

theorem signedPathEdges_homogeneousSupport_one {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) (a b : ℕ)
    (ha : a ≤ B i) (hb : b ≤ B i)
    (hc : cellDegree c = 0) (hvertex : ¬ coordIsEdge (c i)) :
    homogeneousSupport (signedPathEdges c i a b ha hb) 1 := by
  unfold signedPathEdges
  split_ifs with hab
  · simpa [hc] using homogeneousSupport_pathEdges c i a b hb hvertex
  · simpa [hc] using homogeneousSupport_smul (-1)
      (homogeneousSupport_pathEdges c i b a ha hvertex)

theorem cubePath_homogeneousSupport_one {B : Box 4}
    (p q : Anchor 4 B) : homogeneousSupport (cubePath p q) 1 := by
  unfold cubePath
  apply homogeneousSupport_finset_sum (Finset.univ : Finset (Fin 4))
  intro i hi
  exact signedPathEdges_homogeneousSupport_one
    (vertexCell (pathStage p q i.val)) i (p i).val (q i).val
    (Nat.le_of_lt_succ (p i).isLt) (Nat.le_of_lt_succ (q i).isLt)
    (by simp [cellDegree, cellAxes, vertexCell, coordIsEdge])
    (by simp [vertexCell, coordIsEdge])

theorem chainL1_eq_sum_univ {B : Box 4} (q : Chain 4 B) :
    chainL1 q = ∑ c : Cell 4 B, (q c).natAbs := by
  classical
  unfold chainL1
  exact Finset.sum_subset (Finset.subset_univ q.support) (by
    intro c hc hnot
    have hzero : q c = 0 := by
      by_contra hn
      exact hnot (Finsupp.mem_support_iff.mpr hn)
    simp [hzero])

theorem chainL1_add_le {B : Box 4} (q r : Chain 4 B) :
    chainL1 (q + r) ≤ chainL1 q + chainL1 r := by
  rw [chainL1_eq_sum_univ, chainL1_eq_sum_univ, chainL1_eq_sum_univ]
  calc
    (∑ c : Cell 4 B, ((q + r) c).natAbs) ≤
        ∑ c : Cell 4 B, ((q c).natAbs + (r c).natAbs) := by
          apply Finset.sum_le_sum
          intro c hc
          exact Int.natAbs_add_le (q c) (r c)
    _ = (∑ c : Cell 4 B, (q c).natAbs) +
        (∑ c : Cell 4 B, (r c).natAbs) := by rw [Finset.sum_add_distrib]

theorem chainL1_finset_sum_le {B : Box 4} {ι : Type*}
    (s : Finset ι) (f : ι → Chain 4 B) :
    chainL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, chainL1 (f i) := by
  classical
  rw [chainL1_eq_sum_univ]
  calc
    (∑ c : Cell 4 B, ((∑ i ∈ s, f i) c).natAbs) ≤
        ∑ c : Cell 4 B, ∑ i ∈ s, (f i c).natAbs := by
          apply Finset.sum_le_sum
          intro c hc
          rw [finsupp_finset_sum_apply]
          exact Int.natAbs_sum_le _ _
    _ = ∑ i ∈ s, chainL1 (f i) := by
          simp_rw [chainL1_eq_sum_univ]
          rw [Finset.sum_comm]

theorem chainL1_basis {B : Box 4} (c : Cell 4 B) :
    chainL1 (basisChain c) = 1 := by
  simp [chainL1, basisChain]

theorem chainL1_neg_eq {B : Box 4} (q : Chain 4 B) :
    chainL1 (-q) = chainL1 q := by
  rw [chainL1_eq_sum_univ, chainL1_eq_sum_univ]
  simp

theorem chainL1_pathEdges_le {B : Box 4} (c : Cell 4 B) (i : Fin 4)
    (l r : ℕ) (hr : r ≤ B i) :
    chainL1 (pathEdges c i l r hr) ≤ r - l := by
  unfold pathEdges
  calc
    chainL1 (∑ t : {t : ℕ // t ∈ Finset.Ico l r},
        basisChain (edgeCell c i ⟨t.val, by
          have ht := Finset.mem_Ico.mp t.property
          exact lt_of_lt_of_le ht.2 hr⟩)) ≤
      ∑ t : {t : ℕ // t ∈ Finset.Ico l r},
        chainL1 (basisChain (edgeCell c i ⟨t.val, by
          have ht := Finset.mem_Ico.mp t.property
          exact lt_of_lt_of_le ht.2 hr⟩)) := by
            simpa using chainL1_finset_sum_le
              (Finset.univ : Finset {t : ℕ // t ∈ Finset.Ico l r})
              (fun t => basisChain (edgeCell c i ⟨t.val, by
                have ht := Finset.mem_Ico.mp t.property
                exact lt_of_lt_of_le ht.2 hr⟩))
    _ = r - l := by simp [chainL1_basis, Nat.card_Ico]

theorem chainL1_signedPathEdges_le {B : Box 4} (c : Cell 4 B) (i : Fin 4)
    (a b : ℕ) (ha : a ≤ B i) (hb : b ≤ B i) :
    chainL1 (signedPathEdges c i a b ha hb) ≤ natGap a b := by
  by_cases hab : a ≤ b
  · simp [signedPathEdges, natGap, hab]
    exact chainL1_pathEdges_le c i a b hb
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    simp [signedPathEdges, natGap, hab, chainL1_neg_eq]
    exact chainL1_pathEdges_le c i b a ha

theorem chainL1_cubePath_le {B : Box 4} (p q : Anchor 4 B) :
    chainL1 (cubePath p q) ≤ ∑ i : Fin 4, natGap (p i).val (q i).val := by
  unfold cubePath
  calc
    chainL1 (∑ i : Fin 4, signedPathEdges (vertexCell (pathStage p q i.val)) i
        (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
        (Nat.le_of_lt_succ (q i).isLt)) ≤
      ∑ i : Fin 4, chainL1 (signedPathEdges (vertexCell (pathStage p q i.val)) i
        (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
        (Nat.le_of_lt_succ (q i).isLt)) := by
          simpa using chainL1_finset_sum_le
            (Finset.univ : Finset (Fin 4))
            (fun i => signedPathEdges (vertexCell (pathStage p q i.val)) i
              (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
              (Nat.le_of_lt_succ (q i).isLt))
    _ ≤ ∑ i : Fin 4, natGap (p i).val (q i).val := by
          apply Finset.sum_le_sum
          intro i hi
          exact chainL1_signedPathEdges_le _ _ _ _ _ _

theorem support_finset_sum_subset {B : Box 4} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Chain 4 B) :
    (∑ i ∈ s, f i).support ⊆ s.biUnion fun i => (f i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      intro x hx
      have hx' := Finsupp.support_add hx
      rcases Finset.mem_union.mp hx' with hleft | hright
      · exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_insert_self _ _, hleft⟩
      · have hright' : x ∈ s.biUnion fun i => (f i).support := ih hright
        rcases Finset.mem_biUnion.mp hright' with ⟨i, hi, hxi⟩
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_insert_of_mem hi, hxi⟩

theorem pathEdges_fixed_coord {B : Box 4} (c : Cell 4 B) (i j : Fin 4)
    (hij : i ≠ j) (v : Fin (B j + 1)) (hc : c j = Sum.inl v)
    (l r : ℕ) (hr : r ≤ B i) :
    ∀ x ∈ (pathEdges c i l r hr).support, x j = Sum.inl v := by
  intro x hx
  have hsubset : x ∈
      (Finset.univ : Finset {t : ℕ // t ∈ Finset.Ico l r}).biUnion
        (fun t => (basisChain (edgeCell c i ⟨t.val, by
          have ht := Finset.mem_Ico.mp t.property
          exact lt_of_lt_of_le ht.2 hr⟩)).support) := by
    simpa only [pathEdges] using
      (support_finset_sum_subset
        (s := (Finset.univ : Finset {t : ℕ // t ∈ Finset.Ico l r}))
        (f := fun t => basisChain (edgeCell c i ⟨t.val, by
          have ht := Finset.mem_Ico.mp t.property
          exact lt_of_lt_of_le ht.2 hr⟩)) hx)
  rcases Finset.mem_biUnion.mp hsubset with ⟨t, ht, hterm⟩
  have heq : x = edgeCell c i ⟨t.val, by
      have ht' := Finset.mem_Ico.mp t.property
      exact lt_of_lt_of_le ht'.2 hr⟩ := by
    simpa [basisChain] using hterm
  rw [heq]
  simp [edgeCell, Function.update_of_ne (Ne.symm hij), hc]

theorem signedPathEdges_fixed_coord {B : Box 4} (c : Cell 4 B)
    (i j : Fin 4) (hij : i ≠ j) (v : Fin (B j + 1))
    (hc : c j = Sum.inl v) (a b : ℕ) (ha : a ≤ B i) (hb : b ≤ B i) :
    ∀ x ∈ (signedPathEdges c i a b ha hb).support, x j = Sum.inl v := by
  by_cases hab : a ≤ b
  · simpa [signedPathEdges, hab] using
      pathEdges_fixed_coord c i j hij v hc a b hb
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    simpa [signedPathEdges, hab] using
      pathEdges_fixed_coord c i j hij v hc b a ha

@[expose] def sourceUpperBoundaryAnchorValue {B : Box 4} (k : Fin 4) :
    Fin ((bumpedBox B) k + 1) :=
  ⟨B k + 1, by dsimp [bumpedBox]; omega⟩

@[expose] def sourceExteriorAnchorCoord {B : Box 4}
    (v : Anchor 4 (bumpedBox B)) (k : Fin 4) : Prop :=
  v k = 0 ∨ v k = sourceUpperBoundaryAnchorValue k

@[expose] def sourceExteriorCellCoord {B : Box 4}
    (c : Cell 4 (bumpedBox B)) (k : Fin 4) : Prop :=
  c k = Sum.inl 0 ∨ c k = Sum.inl (sourceUpperBoundaryAnchorValue k)

theorem cubePath_fixed_exterior_coord {B : Box 4}
    (p q : Anchor 4 (bumpedBox B))
    (k : Fin 4) (hpq : p k = q k) :
    ∀ c ∈ (cubePath p q).support, c k = Sum.inl (p k) := by
  intro c hc
  have hsubset : c ∈ (Finset.univ : Finset (Fin 4)).biUnion (fun i =>
      (signedPathEdges (vertexCell (pathStage p q i.val)) i
        (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
        (Nat.le_of_lt_succ (q i).isLt)).support) := by
    simpa only [cubePath] using
      (support_finset_sum_subset
        (s := (Finset.univ : Finset (Fin 4)))
        (f := fun i => signedPathEdges (vertexCell (pathStage p q i.val)) i
          (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
          (Nat.le_of_lt_succ (q i).isLt)) hc)
  rcases Finset.mem_biUnion.mp hsubset with ⟨i, hi, hci⟩
  by_cases hki : k = i
  · subst i
    have heq : (p k).val = (q k).val := congrArg Fin.val hpq
    have hzero : signedPathEdges (vertexCell (pathStage p q k.val)) k
        (p k).val (q k).val (Nat.le_of_lt_succ (p k).isLt)
        (Nat.le_of_lt_succ (q k).isLt) = 0 := by
      simp [heq, signedPathEdges, pathEdges_eq_Ico]
    simp [hzero] at hci
  · have hkpath : (pathStage p q i.val) k = p k := by
      simp [pathStage, hpq]
    have hcbase : (vertexCell (pathStage p q i.val)) k = Sum.inl (p k) := by
      simp [vertexCell, hkpath]
    exact signedPathEdges_fixed_coord
      (vertexCell (pathStage p q i.val)) i k (Ne.symm hki) (p k) hcbase
      (p i).val (q i).val (Nat.le_of_lt_succ (p i).isLt)
      (Nat.le_of_lt_succ (q i).isLt) c hci

theorem axisBoundaryBasis_one_support_degree_zero {B : Box 4}
    (c : Cell 4 B) (hc : cellDegree c = 1) (i : Fin 4)
    {x : Cell 4 B} (hx : x ∈ (axisBoundaryBasis c i).support) :
    cellDegree x = 0 := by
  cases hci : c i with
  | inl v => simp [axisBoundaryBasis, hci] at hx
  | inr e =>
    have haxes : cellAxes c = {i} := by
      have hcard : (cellAxes c).card = 1 := by simpa [cellDegree] using hc
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
      have hi : i ∈ cellAxes c := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ i, ?_⟩
        rw [hci]
        rfl
      have : i = j := by simpa [hj] using hi
      simpa [this] using hj
    have hup : cellDegree (upperFace c i e) = 0 := by
      simp [cellDegree, cellAxes_upperFace, haxes]
    have hlo : cellDegree (lowerFace c i e) = 0 := by
      simp [cellDegree, cellAxes_lowerFace, haxes]
    have hx' : x ∈ (basisChain (upperFace c i e) -
        basisChain (lowerFace c i e)).support := by
      have hxsmul : x ∈ (((-1 : ℤ) ^ cellRankBefore c i) •
          (basisChain (upperFace c i e) - basisChain (lowerFace c i e))).support := by
        simpa [axisBoundaryBasis, hci] using hx
      exact (Finsupp.support_smul (b := (-1 : ℤ) ^ cellRankBefore c i)
        (g := basisChain (upperFace c i e) - basisChain (lowerFace c i e))) hxsmul
    have hxunion : x ∈ (basisChain (upperFace c i e)).support ∪
        (basisChain (lowerFace c i e)).support := Finsupp.support_sub hx'
    rcases Finset.mem_union.mp hxunion with hu | hl
    · have hxe : x = upperFace c i e := by simpa [basisChain] using hu
      rw [hxe, hup]
    · have hxe : x = lowerFace c i e := by simpa [basisChain] using hl
      rw [hxe, hlo]

theorem boundary_eq_linearCombination {B : Box 4} (q : Chain 4 B) :
    boundary q = Finsupp.linearCombination ℤ boundaryBasis q := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp [map_add, hq, hr]
  | single c z =>
      have hs : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases h : x = c <;> simp [basisChain, h]
      rw [hs, map_smul, boundary_basis]
      simp [basisChain, Finsupp.linearCombination_single]

theorem boundaryBasis_one_support_degree_zero {B : Box 4}
    (c : Cell 4 B) (hc : cellDegree c = 1) {x : Cell 4 B}
    (hx : x ∈ (boundaryBasis c).support) : cellDegree x = 0 := by
  have hsubset : x ∈ (Finset.univ : Finset (Fin 4)).biUnion
      (fun i => (axisBoundaryBasis c i).support) := by
    simpa only [boundaryBasis] using
      (support_finset_sum_subset (s := (Finset.univ : Finset (Fin 4)))
        (f := fun i => axisBoundaryBasis c i) hx)
  rcases Finset.mem_biUnion.mp hsubset with ⟨i, hi, hxi⟩
  exact axisBoundaryBasis_one_support_degree_zero c hc i hxi

theorem boundary_one_homogeneous_zero {B : Box 4} (q : Chain 4 B)
    (hq : homogeneousSupport q 1) :
    homogeneousSupport (boundary q) 0 := by
  intro x hx
  rw [boundary_eq_linearCombination] at hx
  rw [Finsupp.linearCombination_apply] at hx
  have hsum := Finsupp.support_sum hx
  rcases Finset.mem_biUnion.mp hsum with ⟨c, hc, hcx⟩
  have hcx' : x ∈ (boundaryBasis c).support := by
    rw [Finsupp.mem_support_iff] at hcx ⊢
    intro hzero
    apply hcx
    simp [hzero]
  have hcdegree := hq c hc
  exact boundaryBasis_one_support_degree_zero c hcdegree hcx'

theorem sourceCurrentLatticeChain_homogeneousSupport {B : Box 4}
    (q : IntegerCurrent B) :
    homogeneousSupport (sourceCurrentLatticeChain q) 1 := by
  exact sourceCurrentChain_homogeneousSupport (sourceCurrentOrientationTwist q)

theorem zeroCell_isLeft {B : Box 4} {c : Cell 4 B}
    (hc : cellDegree c = 0) (i : Fin 4) : (c i).isLeft = true := by
  cases hci : c i with
  | inl v => rfl
  | inr e =>
      have haxes : cellAxes c = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [cellDegree] using hc
      have hi : i ∉ cellAxes c := by simp [haxes]
      have hm : i ∈ cellAxes c := by
        rw [cellAxes, Finset.mem_filter]
        refine ⟨Finset.mem_univ i, ?_⟩
        change (c i).isRight = true
        rw [hci]
        rfl
      exact (hi hm).elim

@[expose] def zeroCellAnchor {B : Box 4} (c : Cell 4 B) (hc : cellDegree c = 0) :
    Anchor 4 B := fun i => (c i).getLeft (zeroCell_isLeft hc i)

theorem vertexCell_zeroCellAnchor {B : Box 4} {c : Cell 4 B}
    (hc : cellDegree c = 0) : vertexCell (zeroCellAnchor c hc) = c := by
  funext i
  change Sum.inl ((c i).getLeft (zeroCell_isLeft hc i)) = c i
  have heq : c i = Sum.inl ((c i).getLeft (zeroCell_isLeft hc i)) :=
    (Sum.getLeft_eq_iff
      (a := (c i).getLeft (zeroCell_isLeft hc i))
      (zeroCell_isLeft hc i)).mp rfl
  exact heq.symm

@[expose] def sourceZeroCellOfInteriorAnchor {B : Box 4}
    (v : Anchor 4 (bumpedBox B))
    (hv : ∀ i, 0 < (v i).val ∧ (v i).val ≤ B i) :
    Gaussian.SourceDualZeroCells B :=
  ⟨(fun i => Sum.inl ⟨(v i).val - 1, by
      have hpos := (hv i).1
      have hbound := (hv i).2
      have hlt := (v i).isLt
      dsimp [bumpedBox] at hlt
      omega⟩), by
    simp [Cubical.dualCellDegree, Cubical.dualCellAxes]⟩

theorem lambdaCellToBumpedBox_sourceZeroCellOfInteriorAnchor {B : Box 4}
    (v : Anchor 4 (bumpedBox B))
    (hv : ∀ i, 0 < (v i).val ∧ (v i).val ≤ B i) :
    lambdaCellToBumpedBox (sourceZeroCellOfInteriorAnchor v hv).1 =
      vertexCell v := by
  funext i
  change Sum.inl ⟨((v i).val - 1) + 1, by
      have hpos := (hv i).1
      have hbound := (hv i).2
      have h := (v i).isLt
      dsimp [bumpedBox] at h
      omega⟩ = Sum.inl (v i)
  congr 1
  apply Fin.ext
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (hv i).1)

theorem sourceCurrentBoundary_shell {B : Box 4} (q : IntegerCurrent B)
    (hco : currentDivergence q = 0) :
    ∀ c ∈ (boundary (sourceCurrentLatticeChain q)).support,
      ∃ i, sourceExteriorCellCoord c i := by
  have hhom := boundary_one_homogeneous_zero
    (sourceCurrentLatticeChain q) (sourceCurrentLatticeChain_homogeneousSupport q)
  have hboundary :=
    (currentDivergence_eq_zero_iff_latticeBoundary_eq_zero q).mp hco
  intro c hc
  have hcdeg : cellDegree c = 0 := hhom c hc
  let v := zeroCellAnchor c hcdeg
  by_contra hno
  have hinterior : ∀ i, 0 < (v i).val ∧ (v i).val ≤ B i := by
    intro i
    have hne : (v i).val ≠ 0 := by
      intro hzero
      apply hno
      refine ⟨i, Or.inl ?_⟩
      have hv0 : v i = 0 := Fin.ext hzero
      rw [← vertexCell_zeroCellAnchor hcdeg]
      simp [v, vertexCell, hv0]
    have hnotTop : (v i).val ≠ B i + 1 := by
      intro htop
      apply hno
      refine ⟨i, Or.inr ?_⟩
      have hvtop : v i = sourceUpperBoundaryAnchorValue i := by
        apply Fin.ext
        exact htop
      rw [← vertexCell_zeroCellAnchor hcdeg]
      simp [v, vertexCell, hvtop, sourceUpperBoundaryAnchorValue]
    constructor
    · omega
    · have hlt := (v i).isLt
      dsimp [bumpedBox] at hlt
      omega
  let w := sourceZeroCellOfInteriorAnchor v hinterior
  have hcell : lambdaCellToBumpedBox w.1 = c := by
    rw [lambdaCellToBumpedBox_sourceZeroCellOfInteriorAnchor]
    exact vertexCell_zeroCellAnchor hcdeg
  have hzero := hboundary w
  rw [hcell] at hzero
  have hnonzero : (boundary (sourceCurrentLatticeChain q)) c ≠ 0 :=
    Finsupp.mem_support_iff.mp hc
  exact hnonzero hzero

@[expose] def sourceBoundaryChain {B : Box 4} (q : IntegerCurrent B) :
    Chain 4 (bumpedBox B) := boundary (sourceCurrentLatticeChain q)

@[expose] def sourceBoundaryAnchor {B : Box 4} (q : IntegerCurrent B)
    (c : Cell 4 (bumpedBox B)) : Anchor 4 (bumpedBox B) :=
  if hc : c ∈ (sourceBoundaryChain q).support then
    zeroCellAnchor c (boundary_one_homogeneous_zero
      (sourceCurrentLatticeChain q) (sourceCurrentLatticeChain_homogeneousSupport q)
      c hc)
  else fun _ => 0

theorem sourceBoundaryAnchor_cell {B : Box 4} (q : IntegerCurrent B)
    {c : Cell 4 (bumpedBox B)} (hc : c ∈ (sourceBoundaryChain q).support) :
    vertexCell (sourceBoundaryAnchor q c) = c := by
  simp only [sourceBoundaryAnchor, dite_eq_left hc]
  exact vertexCell_zeroCellAnchor
    (boundary_one_homogeneous_zero (sourceCurrentLatticeChain q)
      (sourceCurrentLatticeChain_homogeneousSupport q) c hc)

theorem sourceBoundaryAnchor_exterior {B : Box 4} (q : IntegerCurrent B)
    (hco : currentDivergence q = 0)
    {c : Cell 4 (bumpedBox B)} (hc : c ∈ (sourceBoundaryChain q).support) :
    ∃ i, sourceExteriorAnchorCoord (sourceBoundaryAnchor q c) i := by
  obtain ⟨i, hi⟩ := sourceCurrentBoundary_shell q hco c hc
  refine ⟨i, ?_⟩
  have hcell := sourceBoundaryAnchor_cell q hc
  have hcoord := congrFun hcell i
  rcases hi with hlo | htop
  · have heq : Sum.inl (sourceBoundaryAnchor q c i) = Sum.inl 0 := hcoord.trans hlo
    exact Or.inl (Sum.inl.inj heq)
  · have heq : Sum.inl (sourceBoundaryAnchor q c i) =
        Sum.inl (sourceUpperBoundaryAnchorValue i) := hcoord.trans htop
    exact Or.inr (Sum.inl.inj heq)

@[expose] def sourceLinkUpperAnchor {B : Box 4} (e : Link B) :
    Anchor 4 (bumpedBox B) := Function.update (base e) (axis e)
      ⟨(base e (axis e)).val + 1, by
        exact Nat.succ_lt_succ (base_axis_lt e)⟩

@[expose] def sourceVertexStep {B : Box 4} (q : IntegerCurrent B)
    (p r : Anchor 4 (bumpedBox B)) : Prop :=
  ∃ e ∈ q.support,
    (p = base e ∧ r = sourceLinkUpperAnchor e) ∨
    (p = sourceLinkUpperAnchor e ∧ r = base e)

inductive SourceVertexPath {B : Box 4} (q : IntegerCurrent B) :
    Anchor 4 (bumpedBox B) → Anchor 4 (bumpedBox B) → ℕ → Prop where
  | refl (p) : SourceVertexPath q p p 0
  | cons {a b c n} : sourceVertexStep q a b →
      SourceVertexPath q b c n → SourceVertexPath q a c (n + 1)

@[expose] def SourceCurrentConnected {B : Box 4} (q : IntegerCurrent B) : Prop :=
  ∀ c ∈ (sourceBoundaryChain q).support,
      ∀ d ∈ (sourceBoundaryChain q).support,
      ∃ n, n ≤ q.support.card ∧
        SourceVertexPath q (sourceBoundaryAnchor q c) (sourceBoundaryAnchor q d) n

theorem sourceVertexStep_coordinate_bound {B : Box 4}
    (q : IntegerCurrent B) {p r : Anchor 4 (bumpedBox B)}
    (hstep : sourceVertexStep q p r) (i : Fin 4) :
    Int.natAbs ((p i).val - (r i).val) ≤ 1 := by
  rcases hstep with ⟨e, he, hcd | hdc⟩
  · rcases hcd with ⟨rfl, rfl⟩
    by_cases hi : axis e = i
    · subst i
      simp [sourceLinkUpperAnchor]
    · have hne : i ≠ axis e := Ne.symm hi
      simp [sourceLinkUpperAnchor, Function.update_of_ne hne]
  · rcases hdc with ⟨rfl, rfl⟩
    by_cases hi : axis e = i
    · subst i
      simp [sourceLinkUpperAnchor]
    · have hne : i ≠ axis e := Ne.symm hi
      simp [sourceLinkUpperAnchor, Function.update_of_ne hne]

theorem sourceVertexPath_coordinate_bound {B : Box 4}
    (q : IntegerCurrent B) {p r : Anchor 4 (bumpedBox B)} {n : ℕ}
    (hpath : SourceVertexPath q p r n) (i : Fin 4) :
    Int.natAbs ((p i).val - (r i).val) ≤ n := by
  induction hpath with
  | refl p => simp
  | @cons a b c n hstep htail ih =>
      have hfirst := sourceVertexStep_coordinate_bound q hstep i
      have htri : Int.natAbs ((a i).val - (c i).val) ≤
          Int.natAbs ((a i).val - (b i).val) +
            Int.natAbs ((b i).val - (c i).val) := by
        have heq : ((a i).val : ℤ) - (c i).val =
            (((a i).val : ℤ) - (b i).val) +
              (((b i).val : ℤ) - (c i).val) := by ring
        rw [heq]
        exact Int.natAbs_add_le _ _
      omega

@[expose] def sourceBoundaryDiameter {B : Box 4} (q : IntegerCurrent B)
    (D : ℕ) : Prop :=
  ∀ c ∈ (sourceBoundaryChain q).support,
    ∀ d ∈ (sourceBoundaryChain q).support, ∀ i,
      Int.natAbs ((sourceBoundaryAnchor q c i).val -
        (sourceBoundaryAnchor q d i).val) ≤ D

@[expose] def sourceBoundaryNoOpposingFaces {B : Box 4}
    (q : IntegerCurrent B) : Prop :=
  ∀ c ∈ (sourceBoundaryChain q).support,
    ∀ d ∈ (sourceBoundaryChain q).support, ∀ i,
      ¬ (sourceBoundaryAnchor q c i = 0 ∧
        sourceBoundaryAnchor q d i = sourceUpperBoundaryAnchorValue i) ∧
      ¬ (sourceBoundaryAnchor q c i = sourceUpperBoundaryAnchorValue i ∧
        sourceBoundaryAnchor q d i = 0)

theorem sourceCurrentConnected_boundaryDiameter {B : Box 4}
    (q : IntegerCurrent B) (hconn : SourceCurrentConnected q) :
    sourceBoundaryDiameter q q.support.card := by
  intro c hc d hd i
  obtain ⟨n, hn, hpath⟩ := hconn c hc d hd
  have hbound := sourceVertexPath_coordinate_bound q hpath i
  exact le_trans hbound (by exact_mod_cast hn)

theorem sourceCurrentConnected_noOpposingFaces {B : Box 4}
    (q : IntegerCurrent B) (hconn : SourceCurrentConnected q)
    (hshort : ∀ i, q.support.card < B i) :
    sourceBoundaryNoOpposingFaces q := by
  intro c hc d hd i
  have hdiam := sourceCurrentConnected_boundaryDiameter q hconn
  constructor
  · intro hfaces
    rcases hfaces with ⟨hlo, htop⟩
    have hlarge : Int.natAbs ((sourceBoundaryAnchor q c i).val -
        (sourceBoundaryAnchor q d i).val) = B i + 1 := by
      rw [hlo, htop]
      change Int.natAbs ((0 : ℤ) - ((B i + 1 : ℕ) : ℤ)) = B i + 1
      rw [show (0 : ℤ) - ((B i + 1 : ℕ) : ℤ) =
        -((B i + 1 : ℕ) : ℤ) by omega]
      rw [Int.natAbs_neg, Int.natAbs_natCast]
    have hsmall := hdiam c hc d hd i
    have hs := hshort i
    omega
  · intro hfaces
    rcases hfaces with ⟨htop, hlo⟩
    have hlarge : Int.natAbs ((sourceBoundaryAnchor q d i).val -
        (sourceBoundaryAnchor q c i).val) = B i + 1 := by
      rw [hlo, htop]
      change Int.natAbs (((B i + 1 : ℕ) : ℤ) - (0 : ℤ)) = B i + 1
      rw [show ((B i + 1 : ℕ) : ℤ) - (0 : ℤ) =
        ((B i + 1 : ℕ) : ℤ) by omega]
      rw [Int.natAbs_natCast]
    have hsmall := hdiam d hd c hc i
    have hs := hshort i
    omega

theorem sourceExteriorAnchors_agree_on_shared_axis {B : Box 4}
    (q : IntegerCurrent B) (hno : sourceBoundaryNoOpposingFaces q)
    {c d : Cell 4 (bumpedBox B)} (hc : c ∈ (sourceBoundaryChain q).support)
    (hd : d ∈ (sourceBoundaryChain q).support)
    {i j : Fin 4}
    (hi : sourceExteriorAnchorCoord (sourceBoundaryAnchor q c) i)
    (hj : sourceExteriorAnchorCoord (sourceBoundaryAnchor q d) j)
    (hij : i = j) : sourceBoundaryAnchor q c i = sourceBoundaryAnchor q d i := by
  subst j
  rcases hi with hci | hci <;> rcases hj with hdj | hdj
  · exact hci.trans hdj.symm
  · exact False.elim ((hno c hc d hd i).1 ⟨hci, hdj⟩)
  · exact False.elim ((hno c hc d hd i).2 ⟨hci, hdj⟩)
  · exact hci.trans hdj.symm

@[expose] def sourceShellHub {B : Box 4} (p q : Anchor 4 (bumpedBox B))
    (i j : Fin 4) : Anchor 4 (bumpedBox B) := fun k =>
  if k = i then p k else if k = j then q k else p k

@[expose] def sourceShellRoute {B : Box 4} (p q : Anchor 4 (bumpedBox B))
    (i j : Fin 4) : Chain 4 (bumpedBox B) :=
  cubePath p (sourceShellHub p q i j) -
    cubePath q (sourceShellHub p q i j)

theorem sourceShellRoute_homogeneousSupport_one {B : Box 4}
    (p q : Anchor 4 (bumpedBox B)) (i j : Fin 4) :
    homogeneousSupport (sourceShellRoute p q i j) 1 := by
  unfold sourceShellRoute
  rw [sub_eq_add_neg]
  apply homogeneousSupport_add (cubePath_homogeneousSupport_one p _)
  simpa using homogeneousSupport_smul (-1) (cubePath_homogeneousSupport_one q _)

theorem sourceShellHub_eq_p_on_i {B : Box 4}
    (p q : Anchor 4 (bumpedBox B)) (i j : Fin 4) :
    sourceShellHub p q i j i = p i := by
  simp [sourceShellHub]

theorem sourceShellHub_eq_q_on_j {B : Box 4}
    (p q : Anchor 4 (bumpedBox B)) (i j : Fin 4)
    (hij : i = j → p i = q i) :
    sourceShellHub p q i j j = q j := by
  by_cases h : i = j
  · subst j
    simpa [sourceShellHub] using hij rfl
  · simp [sourceShellHub, h, eq_comm]

theorem sourceShellRoute_boundary {B : Box 4}
    (p q : Anchor 4 (bumpedBox B)) (i j : Fin 4) :
    boundary (sourceShellRoute p q i j) =
      basisChain (vertexCell q) - basisChain (vertexCell p) := by
  simp only [sourceShellRoute, map_sub, cubePath_boundary]
  abel

theorem cubePath_shell_of_exterior_coord {B : Box 4}
    (p q : Anchor 4 (bumpedBox B)) (i : Fin 4)
    (hp : sourceExteriorAnchorCoord p i)
    (hpq : p i = q i) :
    ∀ c ∈ (cubePath p q).support, sourceExteriorCellCoord c i := by
  intro c hc
  have hcoord := cubePath_fixed_exterior_coord p q i hpq c hc
  rcases hp with hzero | htop
  · exact Or.inl (by simpa [hzero] using hcoord)
  · exact Or.inr (by simpa [htop] using hcoord)

theorem sourceShellRoute_support_shell {B : Box 4}
    (p q : Anchor 4 (bumpedBox B)) (i j : Fin 4)
    (hpi : sourceExteriorAnchorCoord p i)
    (hqj : sourceExteriorAnchorCoord q j)
    (hij : i = j → p i = q i) :
    ∀ c ∈ (sourceShellRoute p q i j).support,
      ∃ k, sourceExteriorCellCoord c k := by
  intro c hc
  have hsub : c ∈ (cubePath p (sourceShellHub p q i j)).support ∪
      (cubePath q (sourceShellHub p q i j)).support :=
    Finsupp.support_sub hc
  rcases Finset.mem_union.mp hsub with hleft | hright
  · exact ⟨i, cubePath_shell_of_exterior_coord p _ i hpi
        (sourceShellHub_eq_p_on_i p q i j).symm c hleft⟩
  · exact ⟨j, cubePath_shell_of_exterior_coord q _ j hqj
      (sourceShellHub_eq_q_on_j p q i j hij).symm c hright⟩

theorem supportedInRect_sum {B : Box 4} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Chain 4 B) (lo hi : Fin 4 → ℕ)
    (hf : ∀ i ∈ s, supportedInRect (f i) lo hi) :
    supportedInRect (∑ i ∈ s, f i) lo hi := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [supportedInRect]
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      apply supportedInRect_add
      · exact hf i (Finset.mem_insert_self _ _)
      · apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)

theorem cubePath_supportedInRect {B : Box 4}
    (p q : Anchor 4 B) (lo hi : Fin 4 → ℕ)
    (hp : ∀ i, lo i ≤ (p i).val ∧ (p i).val ≤ hi i)
    (hq : ∀ i, lo i ≤ (q i).val ∧ (q i).val ≤ hi i) :
    supportedInRect (cubePath p q) lo hi := by
  unfold cubePath
  apply supportedInRect_sum (Finset.univ : Finset (Fin 4))
  intro i hii
  apply supportedInRect_signedPathEdges
    (vertexCell (pathStage p q i.val)) i (p i).val (q i).val
    (Nat.le_of_lt_succ (p i).isLt) (Nat.le_of_lt_succ (q i).isLt) lo hi
  · apply (supportedInRect_basis_iff _ lo hi).2
    intro j
    simp only [vertexCell, cellCoordLower, cellCoordUpper, coordBase,
      coordIsEdge]
    by_cases hji : j.val < i.val
    · simpa [pathStage, hji] using hq j
    · simpa [pathStage, hji] using hp j
  · exact hp i
  · exact hq i

theorem supportedInRect_sub {B : Box 4} {q r : Chain 4 B}
    {lo hi : Fin 4 → ℕ} (hq : supportedInRect q lo hi)
    (hr : supportedInRect r lo hi) :
    supportedInRect (q - r) lo hi := by
  have hneg : supportedInRect (-r) lo hi := by
    intro c hc k
    have hc' : c ∈ r.support := by
      rw [Finsupp.mem_support_iff] at hc ⊢
      intro hz
      apply hc
      simp [hz]
    exact hr c hc' k
  simpa [sub_eq_add_neg] using supportedInRect_add hq hneg

theorem supportedInRect_neg {B : Box 4} {q : Chain 4 B}
    {lo hi : Fin 4 → ℕ} (hq : supportedInRect q lo hi) :
    supportedInRect (-q) lo hi := by
  intro c hc k
  have hc' : c ∈ q.support := by
    rw [Finsupp.mem_support_iff] at hc ⊢
    intro hz
    apply hc
    simp [hz]
  exact hq c hc' k

theorem axisBoundaryBasis_supportedInRect {B : Box 4} (c : Cell 4 B)
    (i : Fin 4) (lo hi : Fin 4 → ℕ)
    (hc : supportedInRect (basisChain c) lo hi) :
    supportedInRect (axisBoundaryBasis c i) lo hi := by
  cases hci : c i with
  | inl v => simp [axisBoundaryBasis, hci, supportedInRect]
  | inr e =>
      have hbounds := (supportedInRect_basis_iff c lo hi).mp hc
      have hu : supportedInRect (basisChain (upperFace c i e)) lo hi := by
        apply (supportedInRect_basis_iff _ lo hi).2
        intro j
        by_cases hji : j = i
        · subst j
          rcases hbounds i with ⟨hlo, hhi⟩
          have hlow : cellCoordLower c i = e.val := by
            simp [cellCoordLower, coordBase, hci]
          have hupp : cellCoordUpper c i = e.val + 1 := by
            simp [cellCoordUpper, coordBase, coordIsEdge, hci]
          rw [hlow] at hlo
          rw [hupp] at hhi
          simp [upperFace, vertexUpdate, cellCoordLower, cellCoordUpper,
            coordBase, coordIsEdge]
          omega
        · simpa [upperFace, vertexUpdate, Function.update_of_ne hji,
            cellCoordLower, cellCoordUpper] using hbounds j
      have hl : supportedInRect (basisChain (lowerFace c i e)) lo hi := by
        apply (supportedInRect_basis_iff _ lo hi).2
        intro j
        by_cases hji : j = i
        · subst j
          rcases hbounds i with ⟨hlo, hhi⟩
          have hlow : cellCoordLower c i = e.val := by
            simp [cellCoordLower, coordBase, hci]
          have hupp : cellCoordUpper c i = e.val + 1 := by
            simp [cellCoordUpper, coordBase, coordIsEdge, hci]
          rw [hlow] at hlo
          rw [hupp] at hhi
          simp [lowerFace, vertexUpdate, cellCoordLower, cellCoordUpper,
            coordBase, coordIsEdge]
          omega
        · simpa [lowerFace, vertexUpdate, Function.update_of_ne hji,
            cellCoordLower, cellCoordUpper] using hbounds j
      rw [axisBoundaryBasis, hci]
      exact supportedInRect_smul _ (supportedInRect_sub hu hl)

theorem boundaryBasis_supportedInRect {B : Box 4} (c : Cell 4 B)
    (lo hi : Fin 4 → ℕ) (hc : supportedInRect (basisChain c) lo hi) :
    supportedInRect (boundaryBasis c) lo hi := by
  unfold boundaryBasis
  apply supportedInRect_sum (Finset.univ : Finset (Fin 4))
  intro i hmem
  exact axisBoundaryBasis_supportedInRect c i lo hi hc

theorem boundary_supportedInRect {B : Box 4} (q : Chain 4 B)
    (lo hi : Fin 4 → ℕ) (hq : supportedInRect q lo hi) :
    supportedInRect (boundary q) lo hi := by
  rw [boundary_eq_linearCombination]
  apply supportedInRect_linearCombination boundaryBasis lo hi
  · intro c hc
    exact boundaryBasis_supportedInRect c lo hi hc
  · exact hq

theorem sourceShellRoute_supportedInRect {B : Box 4}
    (p q : Anchor 4 (bumpedBox B)) (i j : Fin 4) (lo hi : Fin 4 → ℕ)
    (hp : ∀ k, lo k ≤ (p k).val ∧ (p k).val ≤ hi k)
    (hq : ∀ k, lo k ≤ (q k).val ∧ (q k).val ≤ hi k) :
    supportedInRect (sourceShellRoute p q i j) lo hi := by
  unfold sourceShellRoute
  apply supportedInRect_sub
  · apply cubePath_supportedInRect
    · exact hp
    · intro k
      by_cases hki : k = i
      · subst k
        simpa [sourceShellHub] using hp i
      · by_cases hkj : k = j
        · subst k
          simpa [sourceShellHub, hki] using hq j
        · simpa [sourceShellHub, hki, hkj] using hp k
  · apply cubePath_supportedInRect
    · exact hq
    · intro k
      by_cases hki : k = i
      · subst k
        simpa [sourceShellHub] using hp i
      · by_cases hkj : k = j
        · subst k
          simpa [sourceShellHub, hki] using hq j
        · simpa [sourceShellHub, hki, hkj] using hp k

theorem sourceCurrentLatticeChain_supportedInRect {B : Box 4}
    (q : IntegerCurrent B) (lo : Fin 4 → ℕ) (D : ℕ)
    (hq : supportInSourceCube q.support lo D) :
    supportedInRect (sourceCurrentLatticeChain q) lo (fun k => lo k + D) := by
  apply sourceCurrentChain_supportedInRect
  intro k e he
  have hsupp : (sourceCurrentOrientationTwist q).support = q.support :=
    sourceCurrentOrientationTwist_support q
  rw [hsupp] at he
  exact hq k e he

theorem sourceBoundaryAnchor_in_rect {B : Box 4} (q : IntegerCurrent B)
    (lo : Fin 4 → ℕ) (D : ℕ)
    (hq : supportInSourceCube q.support lo D)
    {c : Cell 4 (bumpedBox B)} (hc : c ∈ (sourceBoundaryChain q).support) :
    ∀ k, lo k ≤ (sourceBoundaryAnchor q c k).val ∧
      (sourceBoundaryAnchor q c k).val ≤ lo k + D := by
  have hchain := sourceCurrentLatticeChain_supportedInRect q lo D hq
  have hboundary := boundary_supportedInRect
    (sourceCurrentLatticeChain q) lo (fun k => lo k + D) hchain
  have hvertex := sourceBoundaryAnchor_cell q hc
  have hdegree := boundary_one_homogeneous_zero
    (sourceCurrentLatticeChain q) (sourceCurrentLatticeChain_homogeneousSupport q)
    c hc
  intro k
  have hcoord := congrFun hvertex k
  cases hck : c k with
  | inl v =>
      have hv : (sourceBoundaryAnchor q c k).val = v.val := by
        have heq : Sum.inl (sourceBoundaryAnchor q c k) =
            (Sum.inl v : Coord (bumpedBox B) k) := by
          simpa [vertexCell, hck] using hcoord
        exact congrArg Fin.val (Sum.inl.inj heq)
      have hrect := hboundary c hc k
      simpa [cellCoordLower, cellCoordUpper, coordBase, coordIsEdge,
        hck, hv] using hrect
  | inr e =>
      have hzero := zeroCell_isLeft hdegree k
      simp [hck] at hzero

theorem natGap_le_of_abs_sub_le {a b D : ℕ}
    (h : Int.natAbs ((a : ℤ) - b) ≤ D) : natGap a b ≤ D := by
  unfold natGap
  split_ifs with hab
  · have habs : Int.natAbs ((a : ℤ) - b) = b - a := by
      rw [show (a : ℤ) - b = -((b : ℤ) - a) by omega]
      rw [Int.natAbs_neg]
      have hsub : (b : ℤ) - a = (↑(b - a) : ℤ) := by omega
      rw [hsub]
      simp
    rw [habs] at h
    exact h
  · have habs : Int.natAbs ((a : ℤ) - b) = a - b := by
      have hsub : (a : ℤ) - b = (↑(a - b) : ℤ) := by omega
      rw [hsub]
      simp
    rw [habs] at h
    exact h

theorem chainL1_sub_le {B : Box 4} (q r : Chain 4 B) :
    chainL1 (q - r) ≤ chainL1 q + chainL1 r := by
  simpa [sub_eq_add_neg, chainL1_neg_eq] using chainL1_add_le q (-r)

theorem chainL1_cubePath_le_of_coordinate_bounds {B : Box 4}
    (p q : Anchor 4 B) (D : ℕ)
    (hbound : ∀ i, Int.natAbs ((p i).val - (q i).val) ≤ D) :
    chainL1 (cubePath p q) ≤ 4 * D := by
  calc
    chainL1 (cubePath p q) ≤
        ∑ i : Fin 4, natGap (p i).val (q i).val := chainL1_cubePath_le p q
    _ ≤ ∑ _i : Fin 4, D := by
      apply Finset.sum_le_sum
      intro i hi
      exact natGap_le_of_abs_sub_le (hbound i)
    _ = 4 * D := by norm_num

theorem chainL1_sourceShellRoute_le {B : Box 4}
    (p q : Anchor 4 (bumpedBox B)) (i j : Fin 4) (D : ℕ)
    (hbound : ∀ k, Int.natAbs ((p k).val - (q k).val) ≤ D)
    (hij : i = j → p i = q i) :
    chainL1 (sourceShellRoute p q i j) ≤ 8 * D := by
  unfold sourceShellRoute
  have hphub : ∀ k, Int.natAbs
      ((p k).val - (sourceShellHub p q i j k).val) ≤ D := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [sourceShellHub]
    · by_cases hkj : k = j
      · subst k
        by_cases hsame : i = j
        · subst j
          have hval : p i = q i := hij rfl
          simp [sourceShellHub, hval]
        · have hdiff : Int.natAbs ((p j).val - (q j).val) ≤ D := hbound j
          have hji : j ≠ i := by simpa using hki
          simpa [sourceShellHub, hji, hsame] using hdiff
      · simp [sourceShellHub, hki, hkj]
  have hqhub : ∀ k, Int.natAbs
      ((q k).val - (sourceShellHub p q i j k).val) ≤ D := by
    intro k
    by_cases hki : k = i
    · subst k
      by_cases hsame : i = j
      · subst j
        have hval : p i = q i := hij rfl
        simp [sourceShellHub, hval]
      · have hdiff : Int.natAbs ((q i).val - (p i).val) ≤ D := by
          have := hbound i
          have hnat : Int.natAbs ((q i).val - (p i).val) =
              Int.natAbs ((p i).val - (q i).val) := by
            omega
          simpa [hnat] using this
        simpa [sourceShellHub, hsame] using hdiff
    · by_cases hkj : k = j
      · subst k
        simp [sourceShellHub, hki]
      · have hdiff : Int.natAbs ((q k).val - (p k).val) ≤ D := by
          have := hbound k
          have hnat : Int.natAbs ((q k).val - (p k).val) =
              Int.natAbs ((p k).val - (q k).val) := by omega
          simpa [hnat] using this
        simpa [sourceShellHub, hki, hkj] using hdiff
  have hp := chainL1_cubePath_le_of_coordinate_bounds p
    (sourceShellHub p q i j) D hphub
  have hq := chainL1_cubePath_le_of_coordinate_bounds q
    (sourceShellHub p q i j) D hqhub
  exact le_trans (chainL1_sub_le _ _) (by omega)


theorem source_boundary_route_exists_rect {B : Box 4} (q : IntegerCurrent B)
    (hco : currentDivergence q = 0)
    (hno : sourceBoundaryNoOpposingFaces q) (D : ℕ)
    (hdiam : sourceBoundaryDiameter q D) (lo : Fin 4 → ℕ)
    (hcube : supportInSourceCube q.support lo (2 * D))
    {c₀ c : Cell 4 (bumpedBox B)}
    (hc₀ : c₀ ∈ (sourceBoundaryChain q).support)
    (hc : c ∈ (sourceBoundaryChain q).support) :
    ∃ r : Chain 4 (bumpedBox B),
      boundary r = basisChain c - basisChain c₀ ∧
      (∀ e ∈ r.support, ∃ i, sourceExteriorCellCoord e i) ∧
      homogeneousSupport r 1 ∧ chainL1 r ≤ 8 * D ∧
      supportedInRect r lo (fun k => lo k + 2 * D) := by
  let p := sourceBoundaryAnchor q c₀
  let v := sourceBoundaryAnchor q c
  have hpExterior : ∃ i, sourceExteriorAnchorCoord p i :=
    sourceBoundaryAnchor_exterior q hco hc₀
  have hvExterior : ∃ j, sourceExteriorAnchorCoord v j :=
    sourceBoundaryAnchor_exterior q hco hc
  obtain ⟨i, hi⟩ := hpExterior
  obtain ⟨j, hj⟩ := hvExterior
  have hsame : i = j → p i = v i := by
    intro hij
    exact sourceExteriorAnchors_agree_on_shared_axis q hno hc₀ hc hi hj hij
  have hpRect := sourceBoundaryAnchor_in_rect q lo (2 * D) hcube hc₀
  have hvRect := sourceBoundaryAnchor_in_rect q lo (2 * D) hcube hc
  refine ⟨sourceShellRoute p v i j, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sourceShellRoute_boundary]
    rw [← sourceBoundaryAnchor_cell q hc₀, ← sourceBoundaryAnchor_cell q hc]
  · exact sourceShellRoute_support_shell p v i j hi hj hsame
  · exact sourceShellRoute_homogeneousSupport_one p v i j
  · apply chainL1_sourceShellRoute_le p v i j D ?_ hsame
    intro k
    exact hdiam c₀ hc₀ c hc k
  · exact sourceShellRoute_supportedInRect p v i j lo (fun k => lo k + 2 * D)
      hpRect hvRect

noncomputable def sourceChosenBoundaryRouteRect {B : Box 4}
    (q : IntegerCurrent B) (hco : currentDivergence q = 0)
    (hno : sourceBoundaryNoOpposingFaces q) (D : ℕ)
    (hdiam : sourceBoundaryDiameter q D) (lo : Fin 4 → ℕ)
    (hcube : supportInSourceCube q.support lo (2 * D))
    (c₀ : Cell 4 (bumpedBox B))
    (hc₀ : c₀ ∈ (sourceBoundaryChain q).support)
    (c : Cell 4 (bumpedBox B)) : Chain 4 (bumpedBox B) :=
  if hc : c ∈ (sourceBoundaryChain q).support then
    Classical.choose (source_boundary_route_exists_rect q hco hno D hdiam lo hcube hc₀ hc)
  else 0

theorem sourceChosenBoundaryRouteRect_spec {B : Box 4}
    (q : IntegerCurrent B) (hco : currentDivergence q = 0)
    (hno : sourceBoundaryNoOpposingFaces q) (D : ℕ)
    (hdiam : sourceBoundaryDiameter q D) (lo : Fin 4 → ℕ)
    (hcube : supportInSourceCube q.support lo (2 * D))
    (c₀ : Cell 4 (bumpedBox B))
    (hc₀ : c₀ ∈ (sourceBoundaryChain q).support)
    {c : Cell 4 (bumpedBox B)}
    (hc : c ∈ (sourceBoundaryChain q).support) :
    boundary (sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c) =
        basisChain c - basisChain c₀ ∧
      (∀ e ∈ (sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c).support,
        ∃ i, sourceExteriorCellCoord e i) ∧
      homogeneousSupport (sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c) 1 ∧
      chainL1 (sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c) ≤ 8 * D ∧
      supportedInRect
        (sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c)
        lo (fun k => lo k + 2 * D) := by
  simp only [sourceChosenBoundaryRouteRect, dite_eq_left hc]
  exact Classical.choose_spec
    (source_boundary_route_exists_rect q hco hno D hdiam lo hcube hc₀ hc)

theorem chainL1_smul_eq {B : Box 4} (z : ℤ) (q : Chain 4 B) :
    chainL1 (z • q) = z.natAbs * chainL1 q := by
  rw [chainL1_eq_sum_univ, chainL1_eq_sum_univ]
  simp only [Finsupp.smul_apply, smul_eq_mul, Int.natAbs_mul]
  rw [Finset.mul_sum]

@[expose] def chainTotal {B : Box 4} (q : Chain 4 B) : ℤ :=
  ∑ c : Cell 4 B, q c

theorem chainTotal_basis {B : Box 4} (c : Cell 4 B) :
    chainTotal (basisChain c) = 1 := by
  classical
  simp [chainTotal, basisChain]

theorem chainTotal_add {B : Box 4} (q r : Chain 4 B) :
    chainTotal (q + r) = chainTotal q + chainTotal r := by
  simp [chainTotal, Finset.sum_add_distrib]

theorem chainTotal_neg {B : Box 4} (q : Chain 4 B) :
    chainTotal (-q) = -chainTotal q := by
  simp [chainTotal]

theorem chainTotal_sub {B : Box 4} (q r : Chain 4 B) :
    chainTotal (q - r) = chainTotal q - chainTotal r := by
  rw [sub_eq_add_neg, chainTotal_add, chainTotal_neg]
  rfl

theorem chainTotal_smul {B : Box 4} (z : ℤ) (q : Chain 4 B) :
    chainTotal (z • q) = z * chainTotal q := by
  simp [chainTotal, Finset.mul_sum]

theorem chainTotal_sum {B : Box 4} {ι : Type*} (s : Finset ι)
    (f : ι → Chain 4 B) :
    chainTotal (∑ i ∈ s, f i) = ∑ i ∈ s, chainTotal (f i) := by
  classical
  unfold chainTotal
  simp_rw [finsupp_finset_sum_apply]
  rw [Finset.sum_comm]

theorem chainTotal_axisBoundaryBasis {B : Box 4} (c : Cell 4 B)
    (i : Fin 4) : chainTotal (axisBoundaryBasis c i) = 0 := by
  cases hci : c i with
  | inl v => simp [axisBoundaryBasis, hci, chainTotal]
  | inr e =>
      simp only [axisBoundaryBasis, hci, chainTotal_smul]
      rw [chainTotal_sub, chainTotal_basis, chainTotal_basis]
      ring

theorem chainTotal_boundaryBasis {B : Box 4} (c : Cell 4 B) :
    chainTotal (boundaryBasis c) = 0 := by
  change chainTotal (∑ i : Fin 4, axisBoundaryBasis c i) = 0
  rw [chainTotal_sum (Finset.univ) (axisBoundaryBasis c)]
  exact Finset.sum_eq_zero fun i hi => chainTotal_axisBoundaryBasis c i

theorem chainTotal_boundary_zero {B : Box 4}
    (q : Chain 4 B) : chainTotal (boundary q) = 0 := by
  induction q using Finsupp.induction_linear with
  | zero => simp [chainTotal]
  | add q r ihq ihr => rw [map_add, chainTotal_add, ihq, ihr]; simp
  | single c z =>
      have hs : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases h : x = c <;> simp [basisChain, h]
      rw [hs, map_smul, chainTotal_smul, boundary_basis,
        chainTotal_boundaryBasis]
      simp

theorem chain_eq_support_basis {B : Box 4} (q : Chain 4 B) :
    (∑ c ∈ q.support, q c • basisChain c) = q := by
  classical
  ext x
  rw [finsupp_finset_sum_apply]
  by_cases hx : q x = 0
  · rw [hx]
    apply Finset.sum_eq_zero
    intro c hc
    have hcx : c ≠ x := by
      intro hcx
      subst x
      exact (Finsupp.mem_support_iff.mp hc) hx
    simp [basisChain, hcx]
  · have hxmem : x ∈ q.support := Finsupp.mem_support_iff.mpr hx
    rw [Finset.sum_eq_single x]
    · simp [basisChain]
    · intro c hc hcx
      simp [basisChain, hcx.symm]
    · intro hnot
      exact (hnot hxmem).elim

theorem chainL1_axisBoundaryBasis_le_two {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) : chainL1 (axisBoundaryBasis c i) ≤ 2 := by
  cases hci : c i with
  | inl v => simp [axisBoundaryBasis, hci, chainL1]
  | inr e =>
      rw [axisBoundaryBasis, hci, chainL1_smul_eq]
      have hsign : ((-1 : ℤ) ^ cellRankBefore c i).natAbs = 1 := by
        simp
      calc
        ((-1 : ℤ) ^ cellRankBefore c i).natAbs *
            chainL1 (basisChain (upperFace c i e) - basisChain (lowerFace c i e)) =
            chainL1 (basisChain (upperFace c i e) - basisChain (lowerFace c i e)) := by
              rw [hsign]
              simp
        _ ≤ chainL1 (basisChain (upperFace c i e)) +
            chainL1 (basisChain (lowerFace c i e)) := chainL1_sub_le _ _
        _ = 2 := by simp [chainL1_basis]

theorem chainL1_boundaryBasis_le_two_one {B : Box 4}
    (c : Cell 4 B) (hc : cellDegree c = 1) : chainL1 (boundaryBasis c) ≤ 2 := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (show (cellAxes c).card = 1 by
    simpa [cellDegree] using hc)
  have hsum := chainL1_finset_sum_le
    (s := (Finset.univ : Finset (Fin 4))) (f := axisBoundaryBasis c)
  have hdecomp : boundaryBasis c = ∑ j : Fin 4, axisBoundaryBasis c j := by
    rfl
  rw [hdecomp]
  calc
    chainL1 (∑ j : Fin 4, axisBoundaryBasis c j) ≤
        ∑ j : Fin 4, chainL1 (axisBoundaryBasis c j) := by
          simpa using hsum
    _ = chainL1 (axisBoundaryBasis c i) := by
          rw [Finset.sum_eq_single i]
          · intro j hj hji
            have hnot : j ∉ cellAxes c := by rw [hi]; simp [hji]
            have hpoint : ∃ v : Fin (B j + 1), c j = Sum.inl v := by
              cases hcj : c j with
              | inl v => exact ⟨v, rfl⟩
              | inr e =>
                  have hmem : j ∈ cellAxes c := by
                    apply Finset.mem_filter.mpr
                    exact ⟨Finset.mem_univ j, by rw [hcj]; rfl⟩
                  exact (hnot hmem).elim
            obtain ⟨v, hcj⟩ := hpoint
            simp [axisBoundaryBasis, hcj, chainL1]
          · intro hnot
            exact (hnot (Finset.mem_univ i)).elim
    _ ≤ 2 := chainL1_axisBoundaryBasis_le_two c i

theorem chainL1_boundary_le_two_of_homogeneousOne {B : Box 4}
    (q : Chain 4 B) (hq : homogeneousSupport q 1) :
    chainL1 (boundary q) ≤ 2 * chainL1 q := by
  classical
  have hb : boundary q =
      ∑ c ∈ q.support, q c • boundaryBasis c := by
    calc
      boundary q = boundary (∑ c ∈ q.support, q c • basisChain c) := by
        rw [chain_eq_support_basis]
      _ = ∑ c ∈ q.support, q c • boundaryBasis c := by
        rw [map_sum]
        simp_rw [map_smul, boundary_basis]
  calc
    chainL1 (boundary q) ≤
      ∑ c ∈ q.support, chainL1 (q c • boundaryBasis c) := by
        rw [hb]
        exact chainL1_finset_sum_le _ _
    _ = ∑ c ∈ q.support, (q c).natAbs * chainL1 (boundaryBasis c) := by
        simp_rw [chainL1_smul_eq]
    _ ≤ ∑ c ∈ q.support, (q c).natAbs * 2 := by
        apply Finset.sum_le_sum
        intro c hc
        apply Nat.mul_le_mul_left
        exact chainL1_boundaryBasis_le_two_one c (hq c hc)
    _ = 2 * chainL1 q := by
        change (∑ c ∈ q.support, (q c).natAbs * 2) =
          2 * (∑ c ∈ q.support, (q c).natAbs)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        exact Nat.mul_comm _ _

theorem chainTotal_eq_support_sum {B : Box 4} (q : Chain 4 B) :
    chainTotal q = ∑ c ∈ q.support, q c := by
  classical
  unfold chainTotal
  symm
  apply Finset.sum_subset (Finset.subset_univ q.support)
  intro c hc hnot
  have hzero : q c = 0 := by
    by_contra hn
    exact hnot (Finsupp.mem_support_iff.mpr hn)
  simp [hzero]


theorem sourceExteriorClosure_exists_rect {B : Box 4} (q : IntegerCurrent B)
    (hco : currentDivergence q = 0)
    (hno : sourceBoundaryNoOpposingFaces q) (D : ℕ)
    (hdiam : sourceBoundaryDiameter q D) (lo : Fin 4 → ℕ)
    (hcube : supportInSourceCube q.support lo (2 * D)) :
    ∃ ε : Chain 4 (bumpedBox B),
      boundary ε = -sourceBoundaryChain q ∧
      (∀ c ∈ ε.support, ∃ i, sourceExteriorCellCoord c i) ∧
      homogeneousSupport ε 1 ∧
      chainL1 ε ≤ (8 * D) * chainL1 (sourceBoundaryChain q) ∧
      supportedInRect ε lo (fun k => lo k + 2 * D) := by
  classical
  let b := sourceBoundaryChain q
  have htotal : ∑ c ∈ b.support, b c = 0 := by
    calc
      (∑ c ∈ b.support, b c) = chainTotal b :=
        (chainTotal_eq_support_sum b).symm
      _ = 0 := by
        dsimp [b, sourceBoundaryChain]
        exact chainTotal_boundary_zero (sourceCurrentLatticeChain q)
  by_cases hnonempty : b.support.Nonempty
  · let c₀ := Classical.choose hnonempty
    have hc₀ : c₀ ∈ b.support := Classical.choose_spec hnonempty
    let route := sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀
    let ε := -(∑ c ∈ b.support, b c • route c)
    refine ⟨ε, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [ε, route]
      rw [map_neg, map_sum]
      have hroutes : ∀ c ∈ b.support,
          boundary (sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c) =
            basisChain c - basisChain c₀ := by
        intro c hc
        exact (sourceChosenBoundaryRouteRect_spec q hco hno D hdiam lo hcube
          c₀ hc₀ hc).1
      have hrouteSum :
          (∑ c ∈ b.support, boundary
            (b c • sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c)) = b := by
        calc
          (∑ c ∈ b.support, boundary
              (b c • sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c)) =
              ∑ c ∈ b.support, b c • (basisChain c - basisChain c₀) := by
                apply Finset.sum_congr rfl
                intro c hc
                rw [map_smul, hroutes c hc]
          _ = (∑ c ∈ b.support, b c • basisChain c) -
              (∑ c ∈ b.support, b c • basisChain c₀) := by
                rw [← Finset.sum_sub_distrib]
                congr 1
                funext c
                rw [smul_sub]
          _ = b - (∑ c ∈ b.support, b c) • basisChain c₀ := by
                rw [chain_eq_support_basis, ← Finset.sum_smul]
          _ = b := by rw [htotal]; simp
      rw [hrouteSum]
    · intro c hc
      have hsum := support_finset_sum_subset
        (s := b.support)
        (f := fun c => b c • sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c)
      have hneg : c ∈ (∑ c ∈ b.support,
          b c • sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c).support := by
        simpa [ε, route] using hc
      have hmem := hsum hneg
      rcases Finset.mem_biUnion.mp hmem with ⟨v, hv, hvc⟩
      have hrouteSupport : c ∈
          (sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ v).support := by
        rw [Finsupp.mem_support_iff] at hvc ⊢
        intro hzero
        apply hvc
        simp [hzero]
      rcases (sourceChosenBoundaryRouteRect_spec q hco hno D hdiam lo hcube
          c₀ hc₀ hv).2.1 c hrouteSupport with ⟨i, hi⟩
      exact ⟨i, hi⟩
    · have hsumhom : homogeneousSupport
          (∑ c ∈ b.support,
            b c • sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c) 1 := by
        apply homogeneousSupport_finset_sum b.support
          (fun c => b c • sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c) 1
        intro c hc
        exact homogeneousSupport_smul (b c)
          ((sourceChosenBoundaryRouteRect_spec q hco hno D hdiam lo hcube
            c₀ hc₀ hc).2.2.1)
      simpa [ε] using homogeneousSupport_smul (-1) hsumhom
    · dsimp [ε, route]
      rw [chainL1_neg_eq]
      calc
        chainL1 (∑ c ∈ b.support,
            b c • sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c) ≤
          ∑ c ∈ b.support, chainL1
            (b c • sourceChosenBoundaryRouteRect q hco hno D hdiam lo hcube c₀ hc₀ c) :=
              chainL1_finset_sum_le _ _
        _ ≤ ∑ c ∈ b.support, (b c).natAbs * (8 * D) := by
              apply Finset.sum_le_sum
              intro c hc
              rw [chainL1_smul_eq]
              exact Nat.mul_le_mul_left _
                ((sourceChosenBoundaryRouteRect_spec q hco hno D hdiam lo hcube
                  c₀ hc₀ hc).2.2.2.1)
        _ = (8 * D) * chainL1 b := by
              calc
                (∑ c ∈ b.support, (b c).natAbs * (8 * D)) =
                    (8 * D) * ∑ c ∈ b.support, (b c).natAbs := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro c hc
                      exact Nat.mul_comm _ _
                _ = (8 * D) * chainL1 b := by simp [chainL1]
    · apply supportedInRect_neg
      apply supportedInRect_sum
      intro c hc
      exact supportedInRect_smul (b c)
        ((sourceChosenBoundaryRouteRect_spec q hco hno D hdiam lo hcube
          c₀ hc₀ hc).2.2.2.2)
  · have hb : b = 0 := by
      ext c
      by_contra hne
      exact hnonempty ⟨c, Finsupp.mem_support_iff.mpr hne⟩
    refine ⟨0, ?_, ?_, ?_, ?_, ?_⟩
    · change boundary (0 : Chain 4 (bumpedBox B)) = -b
      simp [hb]
    · simp
    · simp [homogeneousSupport]
    · simp [chainL1]
    · simp [supportedInRect]


theorem shortCurrentShellClosure_exists_rect {B : Box 4}
    (q : IntegerCurrent B) (hco : currentDivergence q = 0)
    (hconn : SourceCurrentConnected q) (m : ℕ)
    (hmin : ∀ i, m ≤ B i) (hshort : q.support.card < m)
    (lo : Fin 4 → ℕ)
    (hcube : supportInSourceCube q.support lo (2 * q.support.card)) :
    ∃ ε : Chain 4 (bumpedBox B),
      boundary (sourceCurrentLatticeChain q + ε) = 0 ∧
      (∀ c ∈ ε.support, ∃ i, sourceExteriorCellCoord c i) ∧
      homogeneousSupport ε 1 ∧
      chainL1 ε ≤ 24 * q.support.card * chainL1 (sourceCurrentLatticeChain q) ∧
      chainL1 (sourceCurrentLatticeChain q + ε) ≤
        (1 + 24 * q.support.card) * chainL1 (sourceCurrentLatticeChain q) ∧
      supportedInRect ε lo (fun k => lo k + 2 * q.support.card) := by
  have hshortSide : ∀ i, q.support.card < B i := by
    intro i
    exact lt_of_lt_of_le hshort (hmin i)
  have hdiam := sourceCurrentConnected_boundaryDiameter q hconn
  have hno := sourceCurrentConnected_noOpposingFaces q hconn hshortSide
  obtain ⟨ε, hcycle, hexterior, hεhom, hε, hεrect⟩ :=
    sourceExteriorClosure_exists_rect q hco hno q.support.card hdiam lo hcube
  have hrhoHom := sourceCurrentLatticeChain_homogeneousSupport q
  have hboundaryL1 := chainL1_boundary_le_two_of_homogeneousOne
    (sourceCurrentLatticeChain q) hrhoHom
  have hε24 : chainL1 ε ≤
      24 * q.support.card * chainL1 (sourceCurrentLatticeChain q) := by
    calc
      chainL1 ε ≤ (8 * q.support.card) *
          chainL1 (sourceBoundaryChain q) := hε
      _ ≤ (8 * q.support.card) *
          (2 * chainL1 (sourceCurrentLatticeChain q)) :=
            Nat.mul_le_mul_left _ hboundaryL1
      _ = 16 * q.support.card * chainL1 (sourceCurrentLatticeChain q) := by ring
      _ ≤ 24 * q.support.card * chainL1 (sourceCurrentLatticeChain q) := by
            apply Nat.mul_le_mul_right
            omega
  refine ⟨ε, ?_, hexterior, hεhom, hε24, ?_, hεrect⟩
  · rw [map_add, hcycle]
    simp [sourceBoundaryChain]
  · calc
      chainL1 (sourceCurrentLatticeChain q + ε) ≤
          chainL1 (sourceCurrentLatticeChain q) + chainL1 ε :=
            chainL1_add_le _ _
      _ ≤ chainL1 (sourceCurrentLatticeChain q) +
          24 * q.support.card * chainL1 (sourceCurrentLatticeChain q) :=
            Nat.add_le_add_left hε24 _
      _ = (1 + 24 * q.support.card) *
          chainL1 (sourceCurrentLatticeChain q) := by ring

theorem fillingOperator_boundary_of_positiveCycle {B : Box 4}
    (anchor : Anchor 4 (bumpedBox B)) (q : Chain 4 (bumpedBox B))
    (hcycle : boundary q = 0) (hpositive : positiveDegreeSupport q) :
    boundary (fillingOperator anchor q) = q := by
  have hprism := fillingOperator_prism_identity anchor
  have hq := congrArg
    (fun T : Chain 4 (bumpedBox B) →ₗ[ℤ] Chain 4 (bumpedBox B) => T q)
    hprism
  change boundary (fillingOperator anchor q) +
      fillingOperator anchor (boundary q) =
        q - finalProjection anchor q at hq
  have hproj : finalProjection anchor q = 0 :=
    orderedPrismProjection_kills_positiveSupport anchor q hpositive
  rw [hcycle, map_zero, hproj, sub_zero, add_zero] at hq
  exact hq


theorem sourceShortFilling_support_subset_omega {B : Box 4}
    (anchor : Anchor 4 (bumpedBox B)) (q : Chain 4 (bumpedBox B))
    (lo : Fin 4 → ℕ) (D : ℕ)
    (hanchor : ∀ k, lo k ≤ (anchor k).val ∧ (anchor k).val ≤ lo k + D)
    (hqrect : supportedInRect q lo (fun k => lo k + D))
    (hqhom : homogeneousSupport q 1) :
    ∀ c ∈ (fillingOperator anchor q).support,
      ∃ p ∈ sourceOmega (B := B) lo D, p.1 = c := by
  intro c hc
  have hrect := fillingOperator_supportedInRect anchor q lo
    (fun k => lo k + D) hanchor hqrect
  have hhom := fillingOperator_homogeneousSupport anchor q 1 hqhom
  have hdeg : cellDegree c = 2 := by
    have h := hhom c hc
    norm_num at h ⊢
    exact h
  have hinside := hrect c hc
  refine ⟨⟨c, hdeg⟩, ?_, rfl⟩
  simp only [sourceOmega, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hinside

theorem sourceChain_support_card_le_omega {B : Box 4}
    (q : Chain 4 (bumpedBox B)) (lo : Fin 4 → ℕ) (D K : ℕ)
    (hsupport : ∀ c ∈ q.support,
      ∃ p ∈ sourceOmega (B := B) lo D, p.1 = c)
    (hcoef : coefficientwiseBound q K) :
    q.support.card ≤ (sourceOmega (B := B) lo D).card ∧
      chainL1 q ≤ (sourceOmega (B := B) lo D).card * K := by
  have hcard : q.support.card ≤ (sourceOmega (B := B) lo D).card := by
    let SupportCell := {c : Cell 4 (bumpedBox B) // c ∈ q.support}
    let OmegaCell := {p : SourcePlaquette B // p ∈ sourceOmega (B := B) lo D}
    let f : SupportCell → OmegaCell := fun c =>
      ⟨Classical.choose (hsupport c.1 c.2),
        (Classical.choose_spec (hsupport c.1 c.2)).1⟩
    have hspec (c : SupportCell) : (f c).1.1 = c.1 :=
      (Classical.choose_spec (hsupport c.1 c.2)).2
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      calc
        a.1 = (f a).1.1 := (hspec a).symm
        _ = (f b).1.1 := congrArg (fun z : OmegaCell => z.1.1) hab
        _ = b.1 := hspec b
    have hfin : Fintype.card SupportCell ≤ Fintype.card OmegaCell :=
      Fintype.card_le_of_injective f hinj
    have hdom : Fintype.card SupportCell = q.support.card :=
      Fintype.card_coe q.support
    have hcod : Fintype.card OmegaCell = (sourceOmega (B := B) lo D).card :=
      Fintype.card_coe (sourceOmega (B := B) lo D)
    omega
  refine ⟨hcard, ?_⟩
  calc
    chainL1 q = ∑ c ∈ q.support, (q c).natAbs := rfl
    _ ≤ ∑ _c ∈ q.support, K := by
      apply Finset.sum_le_sum
      intro c hc
      exact hcoef c
    _ = q.support.card * K := by simp
    _ ≤ (sourceOmega (B := B) lo D).card * K := Nat.mul_le_mul_right K hcard

@[expose] def chainPairing {B : Box 4} (α : Cell 4 B → ℝ)
    (q : Chain 4 B) : ℝ :=
  ∑ c : Cell 4 B, α c * (q c : ℝ)

theorem chainPairing_add {B : Box 4} (α : Cell 4 B → ℝ)
    (q r : Chain 4 B) :
    chainPairing α (q + r) = chainPairing α q + chainPairing α r := by
  simp only [chainPairing, Finsupp.add_apply, Int.cast_add, mul_add]
  rw [Finset.sum_add_distrib]

theorem chainPairing_smul {B : Box 4} (α : Cell 4 B → ℝ)
    (z : ℤ) (q : Chain 4 B) :
    chainPairing α (z • q) = (z : ℝ) * chainPairing α q := by
  simp [chainPairing, Finsupp.smul_apply, Int.cast_mul, Finset.mul_sum,
    mul_left_comm]

theorem chainPairing_sum {B : Box 4} {ι : Type*} (α : Cell 4 B → ℝ)
    (s : Finset ι) (f : ι → Chain 4 B) :
    chainPairing α (∑ i ∈ s, f i) = ∑ i ∈ s, chainPairing α (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chainPairing]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, chainPairing_add, ih, Finset.sum_insert hi]

theorem chainPairing_eq_support_sum {B : Box 4} (α : Cell 4 B → ℝ)
    (q : Chain 4 B) :
    chainPairing α q = ∑ c ∈ q.support, α c * (q c : ℝ) := by
  classical
  unfold chainPairing
  symm
  apply Finset.sum_subset (Finset.subset_univ q.support)
  intro c hc hnot
  have hzero : q c = 0 := by
    by_contra hn
    exact hnot (Finsupp.mem_support_iff.mpr hn)
  simp [hzero]

theorem chainPairing_abs_le_card_mul_coefficientBound {B : Box 4}
    (α : Cell 4 B → ℝ) (q : Chain 4 B) (M : ℝ) (K : ℕ)
    (hM : 0 ≤ M)
    (hα : ∀ c ∈ q.support, |α c| ≤ M)
    (hcoef : coefficientwiseBound q K) :
    |chainPairing α q| ≤ (q.support.card : ℝ) * M * K := by
  rw [chainPairing_eq_support_sum]
  calc
    |∑ c ∈ q.support, α c * (q c : ℝ)| ≤
        ∑ c ∈ q.support, |α c * (q c : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ q.support, M * (K : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      calc
        |α c * (q c : ℝ)| = |α c| * |(q c : ℝ)| := abs_mul _ _
        _ = |α c| * ((q c).natAbs : ℝ) := by
          have hcast : ((q c).natAbs : ℝ) = |(q c : ℝ)| := by
            rw [Nat.cast_natAbs, Int.cast_abs]
          rw [hcast.symm]
        _ ≤ M * ((q c).natAbs : ℝ) :=
          mul_le_mul_of_nonneg_right (hα c hc) (by positivity)
        _ ≤ M * (K : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hcoef c) hM
    _ = (q.support.card : ℝ) * M * K := by simp [mul_assoc]

@[expose] def chainCoboundary {B : Box 4} (α : Cell 4 (bumpedBox B) → ℝ)
    (p : Cell 4 (bumpedBox B)) : ℝ :=
  chainPairing α (boundaryBasis p)

theorem chainPairing_boundary_stokes {B : Box 4}
    (α : Cell 4 (bumpedBox B) → ℝ) (μ : Chain 4 (bumpedBox B)) :
    chainPairing (chainCoboundary α) μ =
      chainPairing α (boundary μ) := by
  have hboundary : boundary μ =
      ∑ p ∈ μ.support, μ p • boundaryBasis p := by
    calc
      boundary μ = boundary (∑ p ∈ μ.support, μ p • basisChain p) := by
        rw [chain_eq_support_basis]
      _ = ∑ p ∈ μ.support, μ p • boundaryBasis p := by
        rw [map_sum]
        simp_rw [map_smul, boundary_basis]
  calc
    chainPairing (chainCoboundary α) μ =
        ∑ p ∈ μ.support, chainCoboundary α p * (μ p : ℝ) :=
          chainPairing_eq_support_sum _ _
    _ = ∑ p ∈ μ.support, (μ p : ℝ) *
        chainPairing α (boundaryBasis p) := by
          apply Finset.sum_congr rfl
          intro p hp
          unfold chainCoboundary
          ring
    _ = chainPairing α
        (∑ p ∈ μ.support, μ p • boundaryBasis p) := by
          rw [chainPairing_sum]
          simp_rw [chainPairing_smul]
    _ = chainPairing α (boundary μ) := by rw [hboundary]

theorem chainPairing_zero_of_vanishes {B : Box 4}
    (α : Cell 4 B → ℝ) (q : Chain 4 B)
    (hα : ∀ c ∈ q.support, α c = 0) : chainPairing α q = 0 := by
  rw [chainPairing_eq_support_sum]
  apply Finset.sum_eq_zero
  intro c hc
  simp [hα c hc]

theorem sourceRelativeStokes_identity {B : Box 4}
    (q : IntegerCurrent B) (ε μ : Chain 4 (bumpedBox B))
    (α : Cell 4 (bumpedBox B) → ℝ)
    (hboundary : boundary μ = sourceCurrentLatticeChain q + ε)
    (hε : ∀ c ∈ ε.support, ∃ i, sourceExteriorCellCoord c i)
    (hα : ∀ c, (∃ i, sourceExteriorCellCoord c i) → α c = 0) :
    chainPairing (chainCoboundary α) μ =
      chainPairing α (sourceCurrentLatticeChain q) := by
  rw [chainPairing_boundary_stokes, hboundary, chainPairing_add]
  have hzero : chainPairing α ε = 0 :=
    chainPairing_zero_of_vanishes α ε (by
      intro c hc
      exact hα c (hε c hc))
  rw [hzero, add_zero]

theorem sourceOmega_card_le_10000L4 {B : Box 4}
    (lo : Fin 4 → ℕ) (L : ℕ) (hL : 1 ≤ L) :
    (sourceOmega (B := B) lo (2 * L)).card ≤ 10000 * L^4 := by
  have hcard := sourceOmega_card_le_cubeCode (B := B) lo (2 * L)
  have hbase : 2 * L + 1 ≤ 3 * L := by omega
  have hpow : (2 * L + 1)^4 ≤ (3 * L)^4 := Nat.pow_le_pow_left hbase 4
  calc
    (sourceOmega (B := B) lo (2 * L)).card ≤ 16 * (2 * L + 1)^4 := hcard
    _ ≤ 16 * (3 * L)^4 := Nat.mul_le_mul_left 16 hpow
    _ = 1296 * L^4 := by ring
    _ ≤ 10000 * L^4 := Nat.mul_le_mul_right (L^4) (by omega)

theorem short_current_phase_bound {B : Box 4} (q : IntegerCurrent B)
    (hco : currentDivergence q = 0) (hconn : SourceCurrentConnected q)
    (m : ℕ) (hmin : ∀ i, m ≤ B i)
    (hL : 1 ≤ q.support.card) (hshort : q.support.card < m)
    (lo : Fin 4 → ℕ) (hlo : ∀ i, lo i ≤ B i + 1)
    (hcube : supportInSourceCube q.support lo (2 * q.support.card))
    (α : Cell 4 (bumpedBox B) → ℝ)
    (hzeroShell : ∀ c, (∃ i, sourceExteriorCellCoord c i) → α c = 0) :
    ∃ ε μ : Chain 4 (bumpedBox B),
      boundary (sourceCurrentLatticeChain q + ε) = 0 ∧
      (∀ c ∈ ε.support, ∃ i, sourceExteriorCellCoord c i) ∧
      homogeneousSupport ε 1 ∧
      chainL1 ε ≤ 24 * q.support.card * chainL1 (sourceCurrentLatticeChain q) ∧
      chainL1 (sourceCurrentLatticeChain q + ε) ≤
        25 * q.support.card * chainL1 (sourceCurrentLatticeChain q) ∧
      supportedInRect ε lo (fun k => lo k + 2 * q.support.card) ∧
      boundary μ = sourceCurrentLatticeChain q + ε ∧
      (∀ c ∈ μ.support,
        ∃ p ∈ sourceOmega (B := B) lo (2 * q.support.card), p.1 = c) ∧
      coefficientwiseBound μ
        (chainL1 (sourceCurrentLatticeChain q + ε)) ∧
      chainPairing (chainCoboundary α) μ =
        chainPairing α (sourceCurrentLatticeChain q) ∧
      |(2 * Real.pi) * chainPairing α (sourceCurrentLatticeChain q)| ≤
        (50 * Real.pi * 10000) *
          sourceOmegaMax lo (2 * q.support.card)
            (fun p => chainCoboundary α p.1) *
          (q.support.card : ℝ)^5 *
          (chainL1 (sourceCurrentLatticeChain q) : ℝ) := by
  obtain ⟨ε, hcycle, hεshell, hεhom, hεmass, hξmass, hεrect⟩ :=
    shortCurrentShellClosure_exists_rect q hco hconn m hmin hshort lo hcube
  let ξ := sourceCurrentLatticeChain q + ε
  let anchor : Anchor 4 (bumpedBox B) := fun i =>
    ⟨lo i, by have hl := hlo i; dsimp [bumpedBox]; omega⟩
  let μ := fillingOperator anchor ξ
  have hxiHom : homogeneousSupport ξ 1 := by
    dsimp [ξ]
    exact homogeneousSupport_add (sourceCurrentLatticeChain_homogeneousSupport q) hεhom
  have hxiRect : supportedInRect ξ lo (fun k => lo k + 2 * q.support.card) := by
    dsimp [ξ]
    apply supportedInRect_add
    · exact sourceCurrentLatticeChain_supportedInRect q lo (2 * q.support.card) hcube
    · exact hεrect
  have hanchor : ∀ k, lo k ≤ (anchor k).val ∧
      (anchor k).val ≤ lo k + 2 * q.support.card := by
    intro k
    constructor <;> dsimp [anchor] <;> omega
  have hfillBoundary : boundary μ = ξ := by
    dsimp [μ, ξ]
    apply fillingOperator_boundary_of_positiveCycle anchor _ hcycle
    intro c hc
    have h := hxiHom c hc
    omega
  have hfillOmega := sourceShortFilling_support_subset_omega
    anchor ξ lo (2 * q.support.card) hanchor hxiRect hxiHom
  have hfillCoef : coefficientwiseBound μ (chainL1 ξ) := by
    dsimp [μ, ξ]
    exact fillingOperator_coefficientwise_le_l1 anchor _
  have ⟨hfillCard, _hfillMass⟩ := sourceChain_support_card_le_omega
    μ lo (2 * q.support.card) (chainL1 ξ) hfillOmega hfillCoef
  let curvature : SourcePlaquette B → ℝ := fun p => chainCoboundary α p.1
  let M := sourceOmegaMax lo (2 * q.support.card) curvature
  have hM : 0 ≤ M := by
    dsimp [M, curvature]
    exact sourceOmegaMax_nonneg lo (2 * q.support.card) _
  have hfield : ∀ c ∈ μ.support, |chainCoboundary α c| ≤ M := by
    intro c hc
    obtain ⟨p, hp, hpc⟩ := hfillOmega c hc
    rw [← hpc]
    exact sourceOmegaMax_bound lo (2 * q.support.card) curvature hp
  have hpair := chainPairing_abs_le_card_mul_coefficientBound
    (chainCoboundary α) μ M (chainL1 ξ) hM hfield hfillCoef
  have hcardOmega := sourceOmega_card_le_10000L4 (B := B) lo q.support.card hL
  have hcardReal : (μ.support.card : ℝ) ≤
      (sourceOmega (B := B) lo (2 * q.support.card)).card := by
    exact_mod_cast hfillCard
  have hmass25 : chainL1 ξ ≤
      25 * q.support.card * chainL1 (sourceCurrentLatticeChain q) := by
    calc
      chainL1 ξ ≤ (1 + 24 * q.support.card) *
          chainL1 (sourceCurrentLatticeChain q) := by simpa [ξ] using hξmass
      _ ≤ 25 * q.support.card * chainL1 (sourceCurrentLatticeChain q) := by
            apply Nat.mul_le_mul_right
            omega
  have hmassReal : (chainL1 ξ : ℝ) ≤
      25 * (q.support.card : ℝ) *
        (chainL1 (sourceCurrentLatticeChain q) : ℝ) := by
    exact_mod_cast hmass25
  have hcardOmegaReal :
      ((sourceOmega (B := B) lo (2 * q.support.card)).card : ℝ) ≤
        10000 * (q.support.card : ℝ)^4 := by
    exact_mod_cast hcardOmega
  have hpairBound : |chainPairing (chainCoboundary α) μ| ≤
      10000 * (q.support.card : ℝ)^4 * M *
        (25 * (q.support.card : ℝ) *
          (chainL1 (sourceCurrentLatticeChain q) : ℝ)) := by
    calc
      |chainPairing (chainCoboundary α) μ| ≤
          (μ.support.card : ℝ) * M * (chainL1 ξ : ℝ) := hpair
      _ ≤ ((sourceOmega (B := B) lo (2 * q.support.card)).card : ℝ) *
          M * (chainL1 ξ : ℝ) := by
            gcongr
      _ ≤ (10000 * (q.support.card : ℝ)^4) * M *
          (25 * (q.support.card : ℝ) *
            (chainL1 (sourceCurrentLatticeChain q) : ℝ)) := by
            gcongr
  have hrelative := sourceRelativeStokes_identity q ε μ α hfillBoundary hεshell
    hzeroShell
  refine ⟨ε, μ, hcycle, hεshell, hεhom, hεmass, ?_, hεrect,
    hfillBoundary, hfillOmega, hfillCoef, hrelative, ?_⟩
  · simpa [ξ] using hmass25
  · calc
      |(2 * Real.pi) * chainPairing α (sourceCurrentLatticeChain q)| =
          |(2 * Real.pi) * chainPairing (chainCoboundary α) μ| := by
            rw [← hrelative]
      _ = (2 * Real.pi) * |chainPairing (chainCoboundary α) μ| := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (2 * Real.pi) *
          (10000 * (q.support.card : ℝ)^4 * M *
            (25 * (q.support.card : ℝ) *
              (chainL1 (sourceCurrentLatticeChain q) : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hpairBound (by positivity)
      _ = (50 * Real.pi * 10000) * M *
          (q.support.card : ℝ)^5 *
          (chainL1 (sourceCurrentLatticeChain q) : ℝ) := by ring

end
end FroehlichSpencer.FS82.Currents.ShortPhase
end
