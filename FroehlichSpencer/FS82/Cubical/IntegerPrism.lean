/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.Incidence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Integer prism filling

The ordered coordinate-prism filling, its prefix-sum characterization, support control, and coefficient bound.
-/

public section

namespace FroehlichSpencer.FS82.Cubical

noncomputable section
open Classical

private theorem homogeneousSupport_projection {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (i : Fin d) (q : Chain d B) (k : ℕ)
    (hq : homogeneousSupport q k) :
    homogeneousSupport (projection anchor i q) k := by
  change homogeneousSupport
    (Finsupp.linearCombination ℤ (projectionBasis anchor · i) q) k
  exact homogeneousSupport_linearCombination_same cellDegree cellDegree
    (projectionBasis anchor · i)
    (fun c => homogeneousSupport_projectionBasis anchor c i) q k hq


@[expose] def orderedPrismFilling {d : ℕ} {B : Box d} (anchor : Anchor d B) :
    List (Fin d) → Chain d B →ₗ[ℤ] Chain d B
  | [] => 0
  | i :: is => homotopy anchor i + projection anchor i * orderedPrismFilling anchor is

@[expose] def orderedPrismProjection {d : ℕ} {B : Box d} (anchor : Anchor d B) :
    List (Fin d) → Chain d B →ₗ[ℤ] Chain d B
  | [] => LinearMap.id
  | i :: is => projection anchor i * orderedPrismProjection anchor is


@[expose] def fillingOperator {d : ℕ} {B : Box d} (anchor : Anchor d B) :
    Chain d B →ₗ[ℤ] Chain d B := orderedPrismFilling anchor (List.finRange d)

private theorem linearCombination_support_witness {α β : Type*} [DecidableEq α]
    [DecidableEq β] (f : α → β →₀ ℤ) (q : α →₀ ℤ) (x : β)
    (hx : x ∈ (Finsupp.linearCombination ℤ f q).support) :
    ∃ a ∈ q.support, x ∈ (f a).support := by
  rw [Finsupp.linearCombination_apply] at hx
  have hsum := Finsupp.support_sum hx
  rcases Finset.mem_biUnion.mp hsum with ⟨a, ha, hxa⟩
  refine ⟨a, ha, ?_⟩
  rw [Finsupp.mem_support_iff] at hxa ⊢
  intro hzero
  apply hxa
  simp [hzero]

private theorem pathEdges_support_off_axis {d : ℕ} {B : Box d}
    (c : Cell d B) (i j : Fin d) (hji : j ≠ i)
    (l r : ℕ) (hr : r ≤ B i) (x : Cell d B)
    (hx : x ∈ (pathEdges c i l r hr).support) : x j = c j := by
  classical
  let I := {t : ℕ // t ∈ Finset.Ico l r}
  let edgeAt : I → Cell d B := fun t => edgeCell c i ⟨t.val, by
    have ht := Finset.mem_Ico.mp t.property
    exact lt_of_lt_of_le ht.2 hr⟩
  have hEval : (∑ t : I, basisChain (edgeAt t)) x =
      ∑ t : I, basisChain (edgeAt t) x := by
    exact finsupp_finset_sum_apply (Finset.univ : Finset I) (fun t => basisChain (edgeAt t)) x
  have hxval : (pathEdges c i l r hr) x ≠ 0 := Finsupp.mem_support_iff.mp hx
  have hsum_ne : (∑ t : I, basisChain (edgeAt t) x) ≠ 0 := by
    change (∑ t : I, basisChain (edgeAt t)) x ≠ 0 at hxval
    rw [hEval] at hxval
    exact hxval
  change (∑ t ∈ (Finset.univ : Finset I), basisChain (edgeAt t) x) ≠ 0 at hsum_ne
  obtain ⟨t, ht, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hcell : x = edgeAt t := by
    have hterm' : (basisChain (edgeAt t)) x ≠ 0 := hterm
    by_contra hne
    apply hterm'
    simp [basisChain, hne]
  rw [hcell]
  simp [edgeAt, edgeCell, Function.update_of_ne hji]

private theorem anchorPathBasis_support_off_axis {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (c : Cell d B) (i j : Fin d) (hji : j ≠ i)
    (x : Cell d B) (hx : x ∈ (anchorPathBasis anchor c i).support) :
    x j = c j := by
  cases hci : c i with
  | inr e => simp [anchorPathBasis, hci] at hx
  | inl v =>
      by_cases hav : (anchor i).val ≤ v.val
      · have hx' : x ∈ (pathEdges c i (anchor i).val v.val
            (Nat.le_of_lt_succ v.isLt)).support := by
          rw [Finsupp.mem_support_iff] at hx ⊢
          simpa [anchorPathBasis, hci, hav, Finsupp.smul_apply] using hx
        exact pathEdges_support_off_axis c i j hji _ _ _ x hx'
      · have hx' : x ∈ (pathEdges c i v.val (anchor i).val
            (Nat.le_of_lt_succ (anchor i).isLt)).support := by
          rw [Finsupp.mem_support_iff] at hx ⊢
          simpa [anchorPathBasis, hci, hav, Finsupp.smul_apply] using hx
        exact pathEdges_support_off_axis c i j hji _ _ _ x hx'

private theorem projection_support_off_axis {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) (i j : Fin d) (hji : j ≠ i)
    (x : Cell d B) (hx : x ∈ (projection anchor i q).support) :
    ∃ y ∈ q.support, x j = y j := by
  have h := linearCombination_support_witness (projectionBasis anchor · i) q x
    (by simpa [projection, extendBasisMap] using hx)
  obtain ⟨y, hy, hxy⟩ := h
  cases hyi : y i with
  | inr e => simp [projectionBasis, hyi] at hxy
  | inl v =>
      have hxeq : x = Function.update y i (Sum.inl (anchor i)) := by
        rw [Finsupp.mem_support_iff] at hxy
        have hsingle : (Finsupp.single (Function.update y i (Sum.inl (anchor i)))
            (1 : ℤ)) x ≠ 0 := by
          simpa [projectionBasis, hyi, basisChain] using hxy
        by_contra hne
        apply hsingle
        simp [hne]
      refine ⟨y, hy, ?_⟩
      rw [hxeq]
      simp [Function.update_of_ne hji]

private theorem orderedPrismFilling_support_off_list {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (is : List (Fin d)) (c : Cell d B)
    (x : Cell d B) (hx : x ∈ (orderedPrismFilling anchor is (basisChain c)).support) :
    ∀ j, j ∉ is → x j = c j := by
  induction is generalizing x with
  | nil => simp [orderedPrismFilling] at hx
  | cons i is ih =>
      intro j hj
      simp only [List.mem_cons, not_or] at hj
      change x ∈ (homotopy anchor i (basisChain c) +
        projection anchor i (orderedPrismFilling anchor is (basisChain c))).support at hx
      have hx' : x ∈ (homotopy anchor i (basisChain c)).support ∪
          (projection anchor i (orderedPrismFilling anchor is (basisChain c))).support :=
        Finsupp.support_add hx
      rcases Finset.mem_union.mp hx' with hx' | hx'
      · have hxH : x ∈ (anchorPathBasis anchor c i).support := by
          simpa [homotopy, extendBasisMap, basisChain] using hx'
        exact anchorPathBasis_support_off_axis anchor c i j hj.1 x hxH
      · obtain ⟨y, hy, hxy⟩ := projection_support_off_axis anchor
          (orderedPrismFilling anchor is (basisChain c)) i j hj.1 x hx'
        exact hxy.trans (ih y hy j hj.2)

private theorem projection_apply_fixed_vertex {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) (i : Fin d) (v : Fin (B i + 1))
    (hcoord : ∀ y ∈ q.support, y i = Sum.inl v) (x : Cell d B) :
    projection anchor i q x =
      if x i = Sum.inl (anchor i) then q (Function.update x i (Sum.inl v)) else 0 := by
  classical
  have hEval : (projection anchor i q) x =
      ∑ y ∈ q.support, q y * projectionBasis anchor y i x := by
    simp [projection, extendBasisMap, Finsupp.linearCombination_apply,
      Finsupp.sum]
  rw [hEval]
  by_cases hxa : x i = Sum.inl (anchor i)
  · let y0 : Cell d B := Function.update x i (Sum.inl v)
    have hupdate0 : Function.update y0 i (Sum.inl (anchor i)) = x := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [y0, hxa]
      · simp [y0, Function.update_of_ne hki]
    have hunique (y : Cell d B) (hy : y ∈ q.support) (hne : y ≠ y0) :
        x ≠ Function.update y i (Sum.inl (anchor i)) := by
      intro hxy
      apply hne
      funext k
      by_cases hki : k = i
      · subst k
        simp [y0, hcoord y hy]
      · have hk : x k = y k := by
          simpa [Function.update_of_ne hki] using congrFun hxy k
        simp [y0, Function.update_of_ne hki, hk]
    have hsum : (∑ y ∈ q.support,
        q y * (if x = Function.update y i (Sum.inl (anchor i)) then 1 else 0)) = q y0 := by
      rw [Finset.sum_eq_single y0]
      · simp [hupdate0]
      · intro y hy hne
        simp [hunique y hy hne]
      · intro hnot
        have hzero : q y0 = 0 := Finsupp.notMem_support_iff.mp hnot
        simp [hzero]
    have hrewrite : ∀ y ∈ q.support,
        projectionBasis anchor y i x =
          if x = Function.update y i (Sum.inl (anchor i)) then 1 else 0 := by
      intro y hy
      simp [projectionBasis, hcoord y hy, basisChain, Finsupp.single_apply, eq_comm]
    calc
      (∑ y ∈ q.support, q y * projectionBasis anchor y i x) =
          ∑ y ∈ q.support,
            q y * (if x = Function.update y i (Sum.inl (anchor i)) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hrewrite y hy]
      _ = q y0 := hsum
      _ = if x i = Sum.inl (anchor i) then
            q (Function.update x i (Sum.inl v)) else 0 := by
        simp [hxa, y0]
  · simp only [ite_eq_right hxa]
    apply Finset.sum_eq_zero
    intro y hy
    have hneq : x ≠ Function.update y i (Sum.inl (anchor i)) := by
      intro heq
      apply hxa
      simpa using congrFun heq i
    simp [projectionBasis, hcoord y hy, basisChain, hneq]

private theorem projection_coefficientwiseBound_fixed_vertex {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) (i : Fin d) (v : Fin (B i + 1))
    (hcoord : ∀ y ∈ q.support, y i = Sum.inl v)
    (hq : coefficientwiseBound q 1) :
    coefficientwiseBound (projection anchor i q) 1 := by
  intro x
  rw [projection_apply_fixed_vertex anchor q i v hcoord x]
  by_cases h : x i = Sum.inl (anchor i)
  · simp [h]
    exact hq (Function.update x i (Sum.inl v))
  · simp [h]

private theorem projection_eq_zero_fixed_edge {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) (i : Fin d) (e : Fin (B i))
    (hcoord : ∀ y ∈ q.support, y i = Sum.inr e) : projection anchor i q = 0 := by
  classical
  ext x
  have hEval : (projection anchor i q) x =
      ∑ y ∈ q.support, q y * projectionBasis anchor y i x := by
    simp [projection, extendBasisMap, Finsupp.linearCombination_apply,
      Finsupp.sum]
  rw [hEval]
  apply Finset.sum_eq_zero
  intro y hy
  simp [projectionBasis, hcoord y hy]

private theorem projection_support_at_anchor {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) (i : Fin d) (x : Cell d B)
    (hx : x ∈ (projection anchor i q).support) :
    x i = Sum.inl (anchor i) := by
  obtain ⟨y, hy, hxy⟩ := linearCombination_support_witness
    (projectionBasis anchor · i) q x (by simpa [projection, extendBasisMap] using hx)
  cases hyi : y i with
  | inr e => simp [projectionBasis, hyi] at hxy
  | inl v =>
      have hxeq : x = Function.update y i (Sum.inl (anchor i)) := by
        rw [Finsupp.mem_support_iff] at hxy
        have hsingle : (Finsupp.single (Function.update y i (Sum.inl (anchor i)))
            (1 : ℤ)) x ≠ 0 := by
          simpa [projectionBasis, hyi, basisChain] using hxy
        by_contra hne
        apply hsingle
        simp [hne]
      rw [hxeq]
      simp

private theorem pathEdges_support_axis {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (l r : ℕ) (hr : r ≤ B i)
    (x : Cell d B) (hx : x ∈ (pathEdges c i l r hr).support) :
    coordIsEdge (x i) := by
  classical
  let I := {t : ℕ // t ∈ Finset.Ico l r}
  let edgeAt : I → Cell d B := fun t => edgeCell c i ⟨t.val, by
    have ht := Finset.mem_Ico.mp t.property
    exact lt_of_lt_of_le ht.2 hr⟩
  have hEval : (∑ t : I, basisChain (edgeAt t)) x =
      ∑ t : I, basisChain (edgeAt t) x := by
    exact finsupp_finset_sum_apply (Finset.univ : Finset I) (fun t => basisChain (edgeAt t)) x
  have hxval : (pathEdges c i l r hr) x ≠ 0 := Finsupp.mem_support_iff.mp hx
  have hsum_ne : (∑ t : I, basisChain (edgeAt t) x) ≠ 0 := by
    change (∑ t : I, basisChain (edgeAt t)) x ≠ 0 at hxval
    rw [hEval] at hxval
    exact hxval
  change (∑ t ∈ (Finset.univ : Finset I), basisChain (edgeAt t) x) ≠ 0 at hsum_ne
  obtain ⟨t, ht, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hcell : x = edgeAt t := by
    by_contra hne
    apply hterm
    simp [basisChain, hne]
  rw [hcell]
  simp [edgeAt, edgeCell, coordIsEdge]

private theorem anchorPathBasis_support_axis {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (c : Cell d B) (i : Fin d) (x : Cell d B)
    (hx : x ∈ (anchorPathBasis anchor c i).support) : coordIsEdge (x i) := by
  cases hci : c i with
  | inr e => simp [anchorPathBasis, hci] at hx
  | inl v =>
      by_cases hav : (anchor i).val ≤ v.val
      · have hx' : x ∈ (pathEdges c i (anchor i).val v.val
            (Nat.le_of_lt_succ v.isLt)).support := by
          rw [Finsupp.mem_support_iff] at hx ⊢
          simpa [anchorPathBasis, hci, hav, Finsupp.smul_apply] using hx
        exact pathEdges_support_axis c i _ _ _ x hx'
      · have hx' : x ∈ (pathEdges c i v.val (anchor i).val
            (Nat.le_of_lt_succ (anchor i).isLt)).support := by
          rw [Finsupp.mem_support_iff] at hx ⊢
          simpa [anchorPathBasis, hci, hav, Finsupp.smul_apply] using hx
        exact pathEdges_support_axis c i _ _ _ x hx'

private theorem orderedPrismFilling_basis_coefficientwiseBound {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (is : List (Fin d)) (hnd : is.Nodup) (c : Cell d B) :
    coefficientwiseBound (orderedPrismFilling anchor is (basisChain c)) 1 := by
  induction is generalizing c with
  | nil => simp [orderedPrismFilling, coefficientwiseBound]
  | cons i is ih =>
      simp only [List.nodup_cons] at hnd
      have htail : coefficientwiseBound (orderedPrismFilling anchor is (basisChain c)) 1 :=
        ih hnd.2 c
      have hcoord : ∀ y ∈ (orderedPrismFilling anchor is (basisChain c)).support,
          y i = c i := by
        intro y hy
        exact orderedPrismFilling_support_off_list anchor is c y hy i hnd.1
      cases hci : c i with
      | inr e =>
          have hproj := projection_eq_zero_fixed_edge anchor
            (orderedPrismFilling anchor is (basisChain c)) i e (by
              intro y hy
              simpa [hci] using hcoord y hy)
          intro x
          change (homotopy anchor i (basisChain c) x +
            projection anchor i (orderedPrismFilling anchor is (basisChain c)) x).natAbs ≤ 1
          rw [hproj]
          simp [homotopy, extendBasisMap, basisChain, anchorPathBasis, hci]
      | inl v =>
          have hprojBound := projection_coefficientwiseBound_fixed_vertex anchor
            (orderedPrismFilling anchor is (basisChain c)) i v (by
              intro y hy
              simpa [hci] using hcoord y hy) htail
          intro x
          change (homotopy anchor i (basisChain c) x +
            projection anchor i (orderedPrismFilling anchor is (basisChain c)) x).natAbs ≤ 1
          by_cases hzero : anchorPathBasis anchor c i x = 0
          · simpa [homotopy, extendBasisMap, basisChain, hzero] using hprojBound x
          · have hHsupport : x ∈ (anchorPathBasis anchor c i).support :=
              Finsupp.mem_support_iff.mpr hzero
            have hPzero :
                projection anchor i (orderedPrismFilling anchor is (basisChain c)) x = 0 := by
              by_contra hP
              have hPsupport : x ∈
                  (projection anchor i (orderedPrismFilling anchor is (basisChain c))).support :=
                Finsupp.mem_support_iff.mpr hP
              have hHedge := anchorPathBasis_support_axis anchor c i x hHsupport
              have hPvertex := projection_support_at_anchor anchor
                (orderedPrismFilling anchor is (basisChain c)) i x hPsupport
              simp [coordIsEdge, hPvertex] at hHedge
            rw [hPzero]
            simpa [homotopy, extendBasisMap, basisChain] using
              anchorPathBasis_coefficientwiseBound anchor c i x

/-- Reduction of the filling coefficient estimate to the geometric generator
claim that each basis input contributes at most one unit to any output cell. -/
theorem fillingOperator_coefficientwise_le_l1_of_basis_bound
    {d : ℕ} {B : Box d} (anchor : Anchor d B) (q : Chain d B)
    (hbasis : ∀ c x, (fillingOperator anchor (basisChain c) x).natAbs ≤ 1) :
    coefficientwiseBound (fillingOperator anchor q) (chainL1 q) := by
  have hrepr (T : Chain d B →ₗ[ℤ] Chain d B) (u : Chain d B) :
      T u = Finsupp.linearCombination ℤ (fun c : Cell d B => T (basisChain c)) u := by
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp [map_add, hu, hv]
    | single c z =>
        have hsingle : Finsupp.single c z = z • basisChain c := by
          ext x
          by_cases hx : x = c <;> simp [basisChain, hx]
        rw [hsingle, map_smul]
        simp [Finsupp.linearCombination_apply, basisChain]
  rw [hrepr (fillingOperator anchor) q]
  exact linearCombination_coefficientwise_le_l1
    (fun c => fillingOperator anchor (basisChain c)) q hbasis

theorem fillingOperator_basis_coefficient_bound {d : ℕ} {B : Box d}
    (anchor : Anchor d B) :
    ∀ c x, (fillingOperator anchor (basisChain c) x).natAbs ≤ 1 := by
  intro c x
  exact (orderedPrismFilling_basis_coefficientwiseBound anchor
    (List.finRange d) (List.nodup_finRange d) c) x

/-- The sharp coefficientwise `ℓ∞ ≤ ℓ¹` estimate for the prism filling. -/
theorem fillingOperator_coefficientwise_le_l1 {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) :
    coefficientwiseBound (fillingOperator anchor q) (chainL1 q) :=
  fillingOperator_coefficientwise_le_l1_of_basis_bound anchor q
    (fillingOperator_basis_coefficient_bound anchor)


@[expose] def finalProjection {d : ℕ} {B : Box d} (anchor : Anchor d B) :
    Chain d B →ₗ[ℤ] Chain d B := orderedPrismProjection anchor (List.finRange d)

/-- Projection product over the coordinates of a list preceding a given index. -/
@[expose] def listPrefixProjection {d : ℕ} {B : Box d} (anchor : Anchor d B)
    (l : List (Fin d)) (i : Fin d) : Chain d B →ₗ[ℤ] Chain d B :=
  (l.filter (fun j => j < i)).foldl
    (fun acc j => acc * projection anchor j) LinearMap.id

/-- The sum expansion of a list-ordered coordinate prism. -/
@[expose] def listPrismExpansion {d : ℕ} {B : Box d} (anchor : Anchor d B)
    (l : List (Fin d)) : Chain d B →ₗ[ℤ] Chain d B :=
  (l.map fun i => listPrefixProjection anchor l i * homotopy anchor i).sum


@[simp] theorem boundary_basis {d : ℕ} {B : Box d} (c : Cell d B) :
    boundary (basisChain c) = boundaryBasis c := by
  simp [boundary, axisBoundary, axisBoundaryBasis, basisChain, boundaryBasis,
    Finsupp.linearCombination_single]

@[simp] theorem axisBoundary_basis {d : ℕ} {B : Box d} (i : Fin d) (c : Cell d B) :
    axisBoundary i (basisChain c) = axisBoundaryBasis c i := by
  simp [axisBoundary, basisChain]

theorem axisBoundary_pathEdges_other {d : ℕ} {B : Box d} (c : Cell d B)
    (i j : Fin d) (hij : i ≠ j) (e : Fin (B j)) (hcj : c j = Sum.inr e)
    (l r : ℕ) (hr : r ≤ B i) :
    axisBoundary (B := B) j (pathEdges c i l r hr) =
      ((-1 : ℤ) ^ axisRank (insert i (cellAxes c)) j) •
        (pathEdges (upperFace c j e) i l r hr -
          pathEdges (lowerFace c j e) i l r hr) := by
  unfold pathEdges
  rw [map_sum]
  rw [smul_sub, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have htB : t.val < B i := by
    have ht' := Finset.mem_Ico.mp t.property
    omega
  let ti : Fin (B i) := ⟨t.val, htB⟩
  have hcoord : (edgeCell c i ti) j = Sum.inr e := by
    simp [edgeCell, Function.update_of_ne (Ne.symm hij), hcj]
  have hrank : cellRankBefore (edgeCell c i ti) j =
      axisRank (insert i (cellAxes c)) j := by
    rw [cellRankBefore_eq_axisRank, cellAxes_edgeCell_eq_insert]
  have hupper := upperFace_edgeCell_commute c i j hij ti e
  have hlower := lowerFace_edgeCell_commute c i j hij ti e
  rw [axisBoundary_basis]
  change axisBoundaryBasis (edgeCell c i ti) j =
      (((-1 : ℤ) ^ axisRank (insert i (cellAxes c)) j) •
          basisChain (edgeCell (upperFace c j e) i ti) -
        ((-1 : ℤ) ^ axisRank (insert i (cellAxes c)) j) •
          basisChain (edgeCell (lowerFace c j e) i ti))
  simp only [axisBoundaryBasis, hcoord, hrank]
  rw [hupper, hlower]
  rw [smul_sub]

theorem axisBoundary_pathEdges_vertex_other {d : ℕ} {B : Box d} (c : Cell d B)
    (i j : Fin d) (hij : i ≠ j) (w : Fin (B j + 1))
    (hcj : c j = Sum.inl w) (l r : ℕ) (hr : r ≤ B i) :
    axisBoundary (B := B) j (pathEdges c i l r hr) = 0 := by
  unfold pathEdges
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro t ht
  have htB : t.val < B i := by
    have ht' := Finset.mem_Ico.mp t.property
    omega
  let ti : Fin (B i) := ⟨t.val, htB⟩
  have hcoord : (edgeCell c i ti) j = Sum.inl w := by
    simp [edgeCell, Function.update_of_ne (Ne.symm hij), hcj]
  rw [axisBoundary_basis]
  change axisBoundaryBasis (edgeCell c i ti) j = 0
  simp [axisBoundaryBasis, hcoord]

theorem axisBoundary_signedPathEdges_other {d : ℕ} {B : Box d}
    (c : Cell d B) (i j : Fin d) (hij : i ≠ j)
    (e : Fin (B j)) (hcj : c j = Sum.inr e)
    (a b : ℕ) (ha : a ≤ B i) (hb : b ≤ B i) :
    axisBoundary (B := B) j (signedPathEdges c i a b ha hb) =
      ((-1 : ℤ) ^ axisRank (insert i (cellAxes c)) j) •
        (signedPathEdges (upperFace c j e) i a b ha hb -
          signedPathEdges (lowerFace c j e) i a b ha hb) := by
  by_cases hab : a ≤ b
  · simpa [signedPathEdges, hab] using
      (axisBoundary_pathEdges_other c i j hij e hcj a b hb)
  · have _hba : b ≤ a := Nat.le_of_not_ge hab
    unfold signedPathEdges
    rw [dite_eq_right hab, map_neg]
    rw [axisBoundary_pathEdges_other c i j hij e hcj b a ha]
    simp [hab, smul_sub]
    abel

theorem axisBoundary_signedPathEdges_vertex_other {d : ℕ} {B : Box d}
    (c : Cell d B) (i j : Fin d) (hij : i ≠ j)
    (w : Fin (B j + 1)) (hcj : c j = Sum.inl w)
    (a b : ℕ) (ha : a ≤ B i) (hb : b ≤ B i) :
    axisBoundary (B := B) j (signedPathEdges c i a b ha hb) = 0 := by
  by_cases hab : a ≤ b
  · simpa [signedPathEdges, hab] using
      (axisBoundary_pathEdges_vertex_other c i j hij w hcj a b hb)
  · simpa [signedPathEdges, hab] using
      (axisBoundary_pathEdges_vertex_other c i j hij w hcj b a ha)

@[simp] theorem homotopy_basis {d : ℕ} {B : Box d} (anchor : Anchor d B)
    (i : Fin d) (c : Cell d B) :
    homotopy anchor i (basisChain c) = anchorPathBasis anchor c i := by
  simp [homotopy, extendBasisMap, basisChain]

@[simp] theorem projection_basis {d : ℕ} {B : Box d} (anchor : Anchor d B)
    (i : Fin d) (c : Cell d B) :
    projection anchor i (basisChain c) = projectionBasis anchor c i := by
  simp [projection, extendBasisMap, basisChain]

theorem projection_idempotent {d : ℕ} {B : Box d} (anchor : Anchor d B) (i : Fin d) :
    projection anchor i * projection anchor i = projection anchor i := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ =>
      rw [map_add, map_add]
      rw [h₁, h₂]
  | single c z =>
      change projection anchor i (projection anchor i (Finsupp.single c z)) =
        projection anchor i (Finsupp.single c z)
      cases h : c i <;> simp [projection, extendBasisMap, projectionBasis, basisChain, h]

theorem projection_commute {d : ℕ} {B : Box d} (anchor : Anchor d B)
    (i j : Fin d) (hij : i ≠ j) :
    projection anchor i * projection anchor j = projection anchor j * projection anchor i := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂]
  | single c z =>
      change projection anchor i (projection anchor j (Finsupp.single c z)) =
        projection anchor j (projection anchor i (Finsupp.single c z))
      have hij' : Function.update c j (Sum.inl (anchor j)) i = c i :=
        Function.update_of_ne hij _ _
      have hji' : Function.update c i (Sum.inl (anchor i)) j = c j :=
        Function.update_of_ne (Ne.symm hij) _ _
      cases hi : c i <;> cases hj : c j <;>
        simp [projection, extendBasisMap, projectionBasis, basisChain, hi, hj, hij', hji',
          Function.update_comm hij]

theorem chain_interval_telescopes {d : ℕ} {B : Box d}
    (v : ℕ → Chain d B) (l r : ℕ) (hlr : l ≤ r) :
    (∑ t ∈ Finset.Ico l r, (v (t + 1) - v t)) = v r - v l := by
  induction r generalizing l with
  | zero =>
      have hl : l = 0 := Nat.eq_zero_of_le_zero hlr
      subst l
      simp
  | succ r ih =>
      by_cases h : l ≤ r
      · rw [Finset.sum_Ico_succ_top h]
        rw [ih l h]
        abel
      · have hl : l = r + 1 := by omega
        subst l
        simp

theorem axisBoundary_pathEdges_forward {d : ℕ} {B : Box d} (c : Cell d B)
    (i : Fin d) (l r : ℕ) (hlr : l ≤ r) (hr : r ≤ B i) :
    axisBoundary (B := B) i (pathEdges c i l r hr) =
      ((-1 : ℤ) ^ cellRankBefore c i) •
        (basisChain (vertexUpdate c i ⟨r, Nat.lt_succ_of_le hr⟩) -
          basisChain (vertexUpdate c i ⟨l, Nat.lt_succ_of_le (le_trans hlr hr)⟩)) := by
  rw [pathEdges_eq_Ico]
  let v : ℕ → Chain d B := vertexChainZeroExtension c i
  calc
    axisBoundary i (∑ t ∈ Finset.Ico l r, pathEdgeTerm c i t) =
        ∑ t ∈ Finset.Ico l r,
          ((-1 : ℤ) ^ cellRankBefore c i) • (v (t + 1) - v t) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_Ico.mp ht
      have htb : t < B i := lt_of_lt_of_le ht'.2 hr
      have ht1 : t + 1 ≤ B i := Nat.succ_le_of_lt htb
      have hs : cellRankBefore (edgeCell c i ⟨t, htb⟩) i =
          cellRankBefore c i := cellRankBefore_edgeCell_self c i ⟨t, htb⟩
      simp only [pathEdgeTerm, dite_eq_left htb, axisBoundary_basis,
        axisBoundaryBasis, edgeCell, Function.update_self]
      have hs' : cellRankBefore (Function.update c i (Sum.inr ⟨t, htb⟩)) i =
          cellRankBefore c i := by simpa [edgeCell] using hs
      rw [hs']
      simp [upperFace, lowerFace, vertexUpdate,
        v, vertexChainZeroExtension, ht1, Nat.le_of_lt htb]
    _ = ((-1 : ℤ) ^ cellRankBefore c i) • (v r - v l) := by
      rw [← Finset.smul_sum]
      rw [chain_interval_telescopes v l r hlr]
    _ = ((-1 : ℤ) ^ cellRankBefore c i) •
        (basisChain (vertexUpdate c i ⟨r, Nat.lt_succ_of_le hr⟩) -
          basisChain (vertexUpdate c i ⟨l, Nat.lt_succ_of_le (le_trans hlr hr)⟩)) := by
      have hlB : l ≤ B i := le_trans hlr hr
      simp only [v, vertexChainZeroExtension, dite_eq_left hr, dite_eq_left hlB]

theorem axisBoundary_signedPathEdges {d : ℕ} {B : Box d} (c : Cell d B)
    (i : Fin d) (a b : ℕ) (ha : a ≤ B i) (hb : b ≤ B i) :
    axisBoundary (B := B) i (signedPathEdges c i a b ha hb) =
      ((-1 : ℤ) ^ cellRankBefore c i) •
        (basisChain (vertexUpdate c i ⟨b, Nat.lt_succ_of_le hb⟩) -
          basisChain (vertexUpdate c i ⟨a, Nat.lt_succ_of_le ha⟩)) := by
  by_cases hab : a ≤ b
  · unfold signedPathEdges
    rw [dite_eq_left hab]
    exact axisBoundary_pathEdges_forward c i a b hab hb
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    unfold signedPathEdges
    rw [dite_eq_right hab, map_neg]
    rw [axisBoundary_pathEdges_forward c i b a hba ha]
    simp only [smul_sub]
    abel

theorem anchorPathBasis_eq_signedPath {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (c : Cell d B) (i : Fin d) (v : Fin (B i + 1))
    (hci : c i = Sum.inl v) :
    anchorPathBasis anchor c i =
      ((-1 : ℤ) ^ cellRankBefore c i) •
        signedPathEdges c i (anchor i).val v.val
          (Nat.le_of_lt_succ (anchor i).isLt) (Nat.le_of_lt_succ v.isLt) := by
  unfold anchorPathBasis
  rw [hci]
  simp [signedPathEdges]

private theorem supportedInRect_anchorPathBasis {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (c : Cell d B) (i : Fin d) (lo hi : Fin d → ℕ)
    (hc : supportedInRect (basisChain c) lo hi)
    (hanchor : ∀ j, lo j ≤ (anchor j).val ∧ (anchor j).val ≤ hi j) :
    supportedInRect (anchorPathBasis anchor c i) lo hi := by
  cases hci : c i with
  | inr e => simp [anchorPathBasis, hci, supportedInRect]
  | inl v =>
      have hv : lo i ≤ v.val ∧ v.val ≤ hi i := by
        have h := (supportedInRect_basis_iff c lo hi).mp hc i
        simpa [cellCoordLower, cellCoordUpper, coordBase, coordIsEdge, hci] using h
      rw [anchorPathBasis_eq_signedPath anchor c i v hci]
      exact supportedInRect_smul ((-1 : ℤ) ^ cellRankBefore c i)
        (supportedInRect_signedPathEdges c i (anchor i).val v.val
          (Nat.le_of_lt_succ (anchor i).isLt) (Nat.le_of_lt_succ v.isLt)
          lo hi hc (hanchor i) hv)

theorem supportedInRect_projectionBasis {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (c : Cell d B) (i : Fin d) (lo hi : Fin d → ℕ)
    (hc : supportedInRect (basisChain c) lo hi)
    (hanchor : ∀ j, lo j ≤ (anchor j).val ∧ (anchor j).val ≤ hi j) :
    supportedInRect (projectionBasis anchor c i) lo hi := by
  classical
  cases hci : c i with
  | inr e => simp [projectionBasis, hci, supportedInRect]
  | inl v =>
      have hc' := (supportedInRect_basis_iff c lo hi).mp hc
      have hupdate : ∀ j,
          lo j ≤ cellCoordLower (vertexUpdate c i (anchor i)) j ∧
            cellCoordUpper (vertexUpdate c i (anchor i)) j ≤ hi j := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa [vertexUpdate, cellCoordLower, cellCoordUpper, coordBase, coordIsEdge]
            using hanchor i
        · change lo j ≤ cellCoordLower
              (Function.update c i (Sum.inl (anchor i))) j ∧
            cellCoordUpper (Function.update c i (Sum.inl (anchor i))) j ≤ hi j
          rw [cellCoordLower, cellCoordUpper, coordBase, Function.update_of_ne hji]
          exact hc' j
      have hbas : supportedInRect
          (basisChain (vertexUpdate c i (anchor i))) lo hi :=
        (supportedInRect_basis_iff _ lo hi).2 hupdate
      simpa [projectionBasis, vertexUpdate, hci] using hbas

theorem supportedInRect_homotopy {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (i : Fin d) (q : Chain d B) (lo hi : Fin d → ℕ)
    (hq : supportedInRect q lo hi)
    (hanchor : ∀ j, lo j ≤ (anchor j).val ∧ (anchor j).val ≤ hi j) :
    supportedInRect (homotopy anchor i q) lo hi := by
  change supportedInRect
    (Finsupp.linearCombination ℤ (anchorPathBasis anchor · i) q) lo hi
  exact supportedInRect_linearCombination (anchorPathBasis anchor · i) lo hi
    (fun c hc => supportedInRect_anchorPathBasis anchor c i lo hi hc hanchor) q hq

theorem supportedInRect_projection {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (i : Fin d) (q : Chain d B) (lo hi : Fin d → ℕ)
    (hq : supportedInRect q lo hi)
    (hanchor : ∀ j, lo j ≤ (anchor j).val ∧ (anchor j).val ≤ hi j) :
    supportedInRect (projection anchor i q) lo hi := by
  change supportedInRect
    (Finsupp.linearCombination ℤ (projectionBasis anchor · i) q) lo hi
  exact supportedInRect_linearCombination (projectionBasis anchor · i) lo hi
    (fun c hc => supportedInRect_projectionBasis anchor c i lo hi hc hanchor) q hq

private theorem homogeneousSupport_anchorPathBasis {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (c : Cell d B) (i : Fin d) :
    homogeneousSupport (anchorPathBasis anchor c i) (cellDegree c + 1) := by
  cases hci : c i with
  | inr e => simp [anchorPathBasis, hci, homogeneousSupport]
  | inl v =>
      rw [anchorPathBasis_eq_signedPath anchor c i v hci]
      unfold signedPathEdges
      split_ifs with hab
      · exact homogeneousSupport_smul _
          (homogeneousSupport_pathEdges c i (anchor i).val v.val
            (Nat.le_of_lt_succ v.isLt) (by simp [coordIsEdge, hci]))
      · simpa using homogeneousSupport_smul (-1)
          (homogeneousSupport_smul ((-1 : ℤ) ^ cellRankBefore c i)
            (homogeneousSupport_pathEdges c i v.val (anchor i).val
              (Nat.le_of_lt_succ (anchor i).isLt) (by simp [coordIsEdge, hci])))

private theorem homogeneousSupport_homotopy {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (i : Fin d) (q : Chain d B) (k : ℕ)
    (hq : homogeneousSupport q k) :
    homogeneousSupport (homotopy anchor i q) (k + 1) := by
  change homogeneousSupport
    (Finsupp.linearCombination ℤ (anchorPathBasis anchor · i) q) (k + 1)
  exact homogeneousSupport_linearCombination_raise cellDegree cellDegree
    (anchorPathBasis anchor · i)
    (fun c => homogeneousSupport_anchorPathBasis anchor c i) q k hq

private theorem homogeneousSupport_orderedPrismFilling {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (l : List (Fin d)) :
    ∀ q k, homogeneousSupport q k →
      homogeneousSupport (orderedPrismFilling anchor l q) (k + 1) := by
  induction l with
  | nil =>
      intro q k hq
      simp [orderedPrismFilling, homogeneousSupport]
  | cons i is ih =>
      intro q k hq
      change homogeneousSupport
        (homotopy anchor i q +
          projection anchor i (orderedPrismFilling anchor is q)) (k + 1)
      apply homogeneousSupport_add
      · exact homogeneousSupport_homotopy anchor i q k hq
      · exact homogeneousSupport_projection anchor i (orderedPrismFilling anchor is q)
          (k + 1) (ih q k hq)

theorem fillingOperator_homogeneousSupport {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) (k : ℕ)
    (hq : homogeneousSupport q k) :
    homogeneousSupport (fillingOperator anchor q) (k + 1) := by
  exact homogeneousSupport_orderedPrismFilling anchor (List.finRange d) q k hq
end
end FroehlichSpencer.FS82.Cubical

end
