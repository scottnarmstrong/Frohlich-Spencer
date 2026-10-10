/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.IntegerPrism
import Mathlib.Tactic

/-!
# Integer cubical exactness

The boundary-square-zero and prism identities, including positive-degree cycle filling with degree and support control.
-/

public section

namespace FroehlichSpencer.FS82.Cubical

noncomputable section
open Classical

private theorem orderedPrismFilling_supportedInRect {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (l : List (Fin d)) (q : Chain d B)
    (lo hi : Fin d → ℕ)
    (hanchor : ∀ j, lo j ≤ (anchor j).val ∧ (anchor j).val ≤ hi j)
    (hq : supportedInRect q lo hi) :
    supportedInRect (orderedPrismFilling anchor l q) lo hi := by
  induction l generalizing q lo hi hanchor hq with
  | nil => simp [orderedPrismFilling, supportedInRect]
  | cons i is ih =>
      change supportedInRect
        (homotopy anchor i q +
          projection anchor i (orderedPrismFilling anchor is q)) lo hi
      apply supportedInRect_add
      · exact supportedInRect_homotopy anchor i q lo hi hq hanchor
      · exact supportedInRect_projection anchor i (orderedPrismFilling anchor is q)
          lo hi (ih q lo hi hanchor hq) hanchor

theorem fillingOperator_supportedInRect {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) (lo hi : Fin d → ℕ)
    (hanchor : ∀ j, lo j ≤ (anchor j).val ∧ (anchor j).val ≤ hi j)
    (hq : supportedInRect q lo hi) :
    supportedInRect (fillingOperator anchor q) lo hi := by
  exact orderedPrismFilling_supportedInRect anchor (List.finRange d) q lo hi hanchor hq

theorem cellRankBefore_vertexUpdate_self {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (v : Fin (B i + 1)) :
    cellRankBefore (vertexUpdate c i v) i = cellRankBefore c i := by
  unfold cellRankBefore
  congr 1
  ext j
  by_cases hji : j < i
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [vertexUpdate, coordIsEdge, Function.update_of_ne (ne_of_lt hji)]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [vertexUpdate, coordIsEdge, hji]

theorem cellRankBefore_vertexUpdate_same {d : ℕ} {B : Box d}
    (c : Cell d B) (i j : Fin d) (v w : Fin (B i + 1))
    (hci : c i = Sum.inl v) :
    cellRankBefore (vertexUpdate c i w) j = cellRankBefore c j := by
  unfold cellRankBefore
  congr 1
  ext k
  by_cases hkj : k < j
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hki : k = i
    · subst k
      simp [vertexUpdate, coordIsEdge, hci]
    · simp [vertexUpdate, coordIsEdge, Function.update_of_ne hki]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [hkj]

theorem axisRank_insert_of_notMem {d : ℕ} (I : Finset (Fin d))
    (i j : Fin d) (hi : i ∉ I) :
    axisRank (insert i I) j = if i < j then axisRank I j + 1 else axisRank I j := by
  change ((Finset.filter (fun k : Fin d => k < j) (insert i I)).card) =
    if i < j then (Finset.filter (fun k : Fin d => k < j) I).card + 1
    else (Finset.filter (fun k : Fin d => k < j) I).card
  by_cases hij : i < j
  · have hfilter : Finset.filter (fun k : Fin d => k < j) (insert i I) =
        insert i (Finset.filter (fun k : Fin d => k < j) I) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_insert]
      by_cases hki : k = i
      · subst k
        simp [hij, hi]
      · simp [hki]
    rw [hfilter]
    have hnot : i ∉ Finset.filter (fun k : Fin d => k < j) I := by
      simp [hi]
    simp [hij, hnot]
  · have hfilter : Finset.filter (fun k : Fin d => k < j) (insert i I) =
        Finset.filter (fun k : Fin d => k < j) I := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_insert]
      by_cases hki : k = i
      · subst k
        simp [hij]
      · simp [hki]
    rw [hfilter]
    simp [hij]

theorem anchorPrism_sign_identity {d : ℕ} {B : Box d} (c : Cell d B)
    (i j : Fin d) (hij : i ≠ j) (v : Fin (B i + 1)) (e : Fin (B j))
    (hci : c i = Sum.inl v) (hcj : c j = Sum.inr e) :
    (-1 : ℤ) ^ cellRankBefore c i *
        (-1 : ℤ) ^ axisRank (insert i (cellAxes c)) j =
      - ((-1 : ℤ) ^ cellRankBefore c j *
        (-1 : ℤ) ^ cellRankBefore (upperFace c j e) i) := by
  have hiA : i ∉ cellAxes c := by
    simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coordIsEdge, hci]
  have hjA : j ∈ cellAxes c := by
    simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coordIsEdge, hcj]
  have hiRank : cellRankBefore c i = axisRank (cellAxes c) i :=
    cellRankBefore_eq_axisRank c i
  have hjRank : cellRankBefore c j = axisRank (cellAxes c) j :=
    cellRankBefore_eq_axisRank c j
  have hfRank : cellRankBefore (upperFace c j e) i =
      axisRank ((cellAxes c).erase j) i :=
    cellRankBefore_upperFace_eq_axisRank c j i e
  by_cases hij' : i < j
  · have hInsJ : axisRank (insert i (cellAxes c)) j =
        axisRank (cellAxes c) j + 1 := by
      rw [axisRank_insert_of_notMem (cellAxes c) i j hiA]
      simp [hij']
    have hEraseJ : axisRank ((cellAxes c).erase j) i =
        axisRank (cellAxes c) i := by
      change (((cellAxes c).erase j).filter (fun k : Fin d => k < i)).card =
        ((cellAxes c).filter (fun k => k < i)).card
      rw [Finset.filter_erase]
      have hnot : j ∉ Finset.filter (fun k => k < i) (cellAxes c) := by
        simp [Finset.mem_filter, not_lt_of_gt hij']
      simp [hnot]
    rw [hiRank, hjRank, hfRank, hInsJ, hEraseJ, pow_succ]
    ring
  · have hji : j < i := by omega
    have hInsJ : axisRank (insert i (cellAxes c)) j =
        axisRank (cellAxes c) j := by
      rw [axisRank_insert_of_notMem (cellAxes c) i j hiA]
      simp [not_lt_of_gt hji]
    have hEraseJ : axisRank ((cellAxes c).erase j) i + 1 =
        axisRank (cellAxes c) i := Contraction.axisRank_erase hji hjA
    have hExp : axisRank (cellAxes c) i =
        axisRank ((cellAxes c).erase j) i + 1 := by omega
    rw [hiRank, hjRank, hfRank, hInsJ, hExp, pow_succ]
    ring

theorem vertexUpdate_eq_self_of_coord {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (v : Fin (B i + 1))
    (hci : c i = Sum.inl v) : vertexUpdate c i v = c := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [vertexUpdate, hci]
  · simp [vertexUpdate, Function.update_of_ne hji]

theorem negOne_pow_square (n : ℕ) :
    ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := by
  rw [← pow_add]
  have hn : n + n = 2 * n := by omega
  rw [hn, pow_mul]
  norm_num

theorem pathEdges_vertexUpdate_irrelevant {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (v : Fin (B i + 1))
    (l r : ℕ) (hr : r ≤ B i) :
    pathEdges (vertexUpdate c i v) i l r hr = pathEdges c i l r hr := by
  unfold pathEdges
  apply Finset.sum_congr rfl
  intro t ht
  simp [basisChain, edgeCell, vertexUpdate]

theorem signedPathEdges_vertexUpdate_irrelevant {d : ℕ} {B : Box d}
    (c : Cell d B) (i : Fin d) (v : Fin (B i + 1))
    (a b : ℕ) (ha : a ≤ B i) (hb : b ≤ B i) :
    signedPathEdges (vertexUpdate c i v) i a b ha hb = signedPathEdges c i a b ha hb := by
  unfold signedPathEdges
  split_ifs
  · exact pathEdges_vertexUpdate_irrelevant c i v a b hb
  · exact congrArg Neg.neg (pathEdges_vertexUpdate_irrelevant c i v b a ha)

theorem axisHomotopy_prism {d : ℕ} {B : Box d} (anchor : Anchor d B) (i : Fin d) :
    axisBoundary (B := B) i * homotopy anchor i + homotopy anchor i * axisBoundary i =
      LinearMap.id - projection anchor i := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂, sub_add]
  | single c z =>
      have hsingle : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases hx : x = c <;> simp [basisChain, hx]
      rw [hsingle, map_smul, map_smul]
      change z • (axisBoundary (B := B) i (homotopy anchor i (basisChain c)) +
          homotopy anchor i (axisBoundary (B := B) i (basisChain c))) =
        z • (basisChain c - projection anchor i (basisChain c))
      congr 1
      rw [homotopy_basis, axisBoundary_basis, projection_basis]
      cases hci : c i with
      | inl v =>
          have hpath := anchorPathBasis_eq_signedPath anchor c i v hci
          rw [hpath, map_smul, axisBoundary_signedPathEdges]
          simp [axisBoundaryBasis, hci, projectionBasis, smul_smul,
            vertexUpdate_eq_self_of_coord, negOne_pow_square]
          rfl
      | inr e =>
          have hv : (upperFace c i e) i = Sum.inl
              ⟨e.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt e.isLt)⟩ := by
            simp [upperFace, vertexUpdate]
          have hl : (lowerFace c i e) i = Sum.inl
              ⟨e.val, Nat.lt_succ_of_le e.isLt.le⟩ := by
            simp [lowerFace, vertexUpdate]
          have hru : cellRankBefore (upperFace c i e) i = cellRankBefore c i := by
            rw [upperFace]
            exact cellRankBefore_vertexUpdate_self c i _
          have hrl : cellRankBefore (lowerFace c i e) i = cellRankBefore c i := by
            rw [lowerFace]
            exact cellRankBefore_vertexUpdate_self c i _
          simp only [anchorPathBasis, hci]
          rw [axisBoundaryBasis, hci]
          rw [map_smul, map_sub]
          rw [homotopy_basis, homotopy_basis]
          rw [anchorPathBasis_eq_signedPath anchor (upperFace c i e) i _ hv,
            anchorPathBasis_eq_signedPath anchor (lowerFace c i e) i _ hl,
            hru, hrl]
          have huPath : signedPathEdges (upperFace c i e) i (anchor i).val (e.val + 1)
              (Nat.le_of_lt_succ (anchor i).isLt) (Nat.succ_le_of_lt e.isLt) =
              signedPathEdges c i (anchor i).val (e.val + 1)
                (Nat.le_of_lt_succ (anchor i).isLt) (Nat.succ_le_of_lt e.isLt) := by
            simpa only [upperFace] using
              (signedPathEdges_vertexUpdate_irrelevant c i
                ⟨e.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt e.isLt)⟩
                (anchor i).val (e.val + 1) (Nat.le_of_lt_succ (anchor i).isLt)
                (Nat.succ_le_of_lt e.isLt))
          have hlPath : signedPathEdges (lowerFace c i e) i (anchor i).val e.val
              (Nat.le_of_lt_succ (anchor i).isLt) e.isLt.le =
              signedPathEdges c i (anchor i).val e.val
                (Nat.le_of_lt_succ (anchor i).isLt) e.isLt.le := by
            simpa only [lowerFace] using
              (signedPathEdges_vertexUpdate_irrelevant c i
                ⟨e.val, Nat.lt_succ_of_le e.isLt.le⟩
                (anchor i).val e.val (Nat.le_of_lt_succ (anchor i).isLt) e.isLt.le)
          rw [huPath, hlPath]
          simp [hci, projectionBasis, smul_sub, smul_smul,
            negOne_pow_square]
          rw [signedPathEdges_succ c i (anchor i).val e.val
            (Nat.le_of_lt_succ (anchor i).isLt) e.isLt]
          have hedge : edgeCell c i e = c := by
            funext j
            by_cases hji : j = i
            · subst j
              simp [edgeCell, hci]
            · simp [edgeCell, Function.update_of_ne hji]
          simpa [edgeCell] using congrArg basisChain hedge

theorem axisBoundary_homotopy_anticommute {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (i j : Fin d) (hij : i ≠ j) :
    axisBoundary (B := B) j * homotopy anchor i =
      -(homotopy anchor i * axisBoundary (B := B) j) := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single c z =>
      have hsingle : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases hx : x = c <;> simp [basisChain, hx]
      rw [hsingle, map_smul, map_smul]
      change z • axisBoundary (B := B) j (homotopy anchor i (basisChain c)) =
        z • (-(homotopy anchor i (axisBoundary (B := B) j (basisChain c))))
      congr 1
      rw [homotopy_basis, axisBoundary_basis]
      cases hci : c i with
      | inr ei =>
          cases hcj : c j with
          | inl w => simp [anchorPathBasis, axisBoundaryBasis, hci, hcj]
          | inr ej =>
              simp [anchorPathBasis, axisBoundaryBasis, hci, hcj,
                upperFace, lowerFace, vertexUpdate,
                Function.update_of_ne hij]
      | inl v =>
          have ha : (anchor i).val ≤ B i := Nat.le_of_lt_succ (anchor i).isLt
          have hb : v.val ≤ B i := Nat.le_of_lt_succ v.isLt
          cases hcj : c j with
          | inl w =>
              rw [anchorPathBasis_eq_signedPath anchor c i v hci, map_smul,
                axisBoundary_signedPathEdges_vertex_other c i j hij w hcj
                  (anchor i).val v.val ha hb]
              simp [axisBoundaryBasis, hcj]
          | inr ej =>
              have huv : (upperFace c j ej) i = Sum.inl v := by
                simp [upperFace, vertexUpdate,
                  Function.update_of_ne hij, hci]
              have hlv : (lowerFace c j ej) i = Sum.inl v := by
                simp [lowerFace, vertexUpdate,
                  Function.update_of_ne hij, hci]
              have hru : cellRankBefore (upperFace c j ej) i =
                  cellRankBefore (lowerFace c j ej) i := by
                rw [cellRankBefore_upperFace_eq_axisRank,
                  cellRankBefore_lowerFace_eq_axisRank]
              have hsign := anchorPrism_sign_identity c i j hij v ej hci hcj
              rw [anchorPathBasis_eq_signedPath anchor c i v hci, map_smul,
                axisBoundary_signedPathEdges_other c i j hij ej hcj
                  (anchor i).val v.val ha hb]
              rw [axisBoundaryBasis, hcj, map_smul, map_sub,
                homotopy_basis, homotopy_basis]
              rw [anchorPathBasis_eq_signedPath anchor (upperFace c j ej) i v huv,
                anchorPathBasis_eq_signedPath anchor (lowerFace c j ej) i v hlv,
                hru]
              let sI : ℤ := (-1 : ℤ) ^ cellRankBefore c i
              let sS : ℤ := (-1 : ℤ) ^ axisRank (insert i (cellAxes c)) j
              let sJ : ℤ := (-1 : ℤ) ^ cellRankBefore c j
              let sF : ℤ := (-1 : ℤ) ^ cellRankBefore (lowerFace c j ej) i
              let U : Chain d B :=
                signedPathEdges (upperFace c j ej) i (anchor i).val v.val ha hb
              let L : Chain d B :=
                signedPathEdges (lowerFace c j ej) i (anchor i).val v.val ha hb
              change sI • (sS • (U - L)) = -(sJ • (sF • U - sF • L))
              have hsign' : sI * sS = -(sJ * sF) := by
                simpa [sI, sS, sJ, sF, hru] using hsign
              have hdist : (sJ * sF) • (U - L) =
                  sJ • (sF • U - sF • L) := by
                simp only [smul_sub, ← smul_smul]
              calc
                sI • (sS • (U - L)) = (sI * sS) • (U - L) := by
                  rw [smul_smul]
                _ = (-(sJ * sF)) • (U - L) := by rw [hsign']
                _ = -((sJ * sF) • (U - L)) := by rw [neg_smul]
                _ = -(sJ • (sF • U - sF • L)) := by rw [hdist]

theorem fullBoundaryHomotopy_prism {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (i : Fin d) :
    boundary (B := B) * homotopy anchor i + homotopy anchor i * boundary =
      LinearMap.id - projection anchor i := by
  have hterms :
      ∑ j : Fin d,
        (axisBoundary (B := B) j * homotopy anchor i +
          homotopy anchor i * axisBoundary (B := B) j) =
        LinearMap.id - projection anchor i := by
    rw [Finset.sum_eq_single i]
    · exact axisHomotopy_prism anchor i
    · intro j hj hji
      rw [axisBoundary_homotopy_anticommute anchor i j (Ne.symm hji)]
      simp
    · simp
  change (∑ j : Fin d, axisBoundary (B := B) j) * homotopy anchor i +
      homotopy anchor i * (∑ j : Fin d, axisBoundary (B := B) j) = _
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact hterms

theorem projection_axisBoundary_commute {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (i j : Fin d) :
    projection anchor i * axisBoundary (B := B) j =
      axisBoundary (B := B) j * projection anchor i := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single c z =>
      have hsingle : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases hx : x = c <;> simp [basisChain, hx]
      rw [hsingle, map_smul, map_smul]
      change z • projection anchor i (axisBoundary (B := B) j (basisChain c)) =
        z • axisBoundary (B := B) j (projection anchor i (basisChain c))
      congr 1
      rw [axisBoundary_basis, projection_basis]
      by_cases hij : i = j
      · subst j
        cases hci : c i with
        | inl v => simp [axisBoundaryBasis, projectionBasis, hci]
        | inr e =>
            simp [axisBoundaryBasis, projectionBasis, hci,
              upperFace, lowerFace, vertexUpdate]
      · cases hci : c i with
        | inr ei =>
            cases hcj : c j with
            | inl w => simp [axisBoundaryBasis, projectionBasis, hci, hcj]
            | inr ej =>
                simp [axisBoundaryBasis, projectionBasis, hci, hcj,
                  upperFace, lowerFace, vertexUpdate, Function.update_of_ne hij]
        | inl v =>
            have hrank : cellRankBefore (vertexUpdate c i (anchor i)) j =
                cellRankBefore c j :=
              cellRankBefore_vertexUpdate_same c i j v (anchor i) hci
            cases hcj : c j with
            | inl w =>
                have hnewj :
                    Function.update c i (Sum.inl (anchor i)) j = Sum.inl w := by
                  rw [Function.update_of_ne (Ne.symm hij), hcj]
                simp only [axisBoundaryBasis, hcj]
                simp only [projectionBasis, hci]
                rw [axisBoundary_basis]
                simp only [axisBoundaryBasis, hnewj]
                simp
            | inr ej =>
                have hnewj :
                    Function.update c i (Sum.inl (anchor i)) j = Sum.inr ej := by
                  rw [Function.update_of_ne (Ne.symm hij), hcj]
                have huv : (upperFace c j ej) i = Sum.inl v := by
                  simp [upperFace, vertexUpdate, Function.update_of_ne hij, hci]
                have hlv : (lowerFace c j ej) i = Sum.inl v := by
                  simp [lowerFace, vertexUpdate, Function.update_of_ne hij, hci]
                have hupper : upperFace (vertexUpdate c i (anchor i)) j ej =
                    vertexUpdate (upperFace c j ej) i (anchor i) := by
                  unfold upperFace
                  exact vertexUpdate_commute c hij (anchor i) _
                have hlower : lowerFace (vertexUpdate c i (anchor i)) j ej =
                    vertexUpdate (lowerFace c j ej) i (anchor i) := by
                  unfold lowerFace
                  exact vertexUpdate_commute c hij (anchor i) _
                simp only [axisBoundaryBasis, hcj, map_smul, map_sub]
                rw [projection_basis, projection_basis]
                simp only [projectionBasis, huv, hlv, projectionBasis, hci]
                rw [axisBoundary_basis]
                simp only [axisBoundaryBasis, hnewj]
                have hrank' :
                    cellRankBefore (Function.update c i (Sum.inl (anchor i))) j =
                      cellRankBefore c j := hrank
                rw [hrank']
                have hupper' :
                    upperFace (Function.update c i (Sum.inl (anchor i))) j ej =
                      Function.update (upperFace c j ej) i (Sum.inl (anchor i)) := by
                  simpa only [vertexUpdate] using hupper
                have hlower' :
                    lowerFace (Function.update c i (Sum.inl (anchor i))) j ej =
                      Function.update (lowerFace c j ej) i (Sum.inl (anchor i)) := by
                  simpa only [vertexUpdate] using hlower
                rw [hupper', hlower']

theorem projection_boundary_commute {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (i : Fin d) :
    projection anchor i * boundary (B := B) =
      boundary (B := B) * projection anchor i := by
  change projection anchor i * (∑ j : Fin d, axisBoundary (B := B) j) =
    (∑ j : Fin d, axisBoundary (B := B) j) * projection anchor i
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact projection_axisBoundary_commute anchor i j

theorem orderedPrism_identity {d : ℕ} {B : Box d} (anchor : Anchor d B)
    (is : List (Fin d)) :
    boundary (B := B) * orderedPrismFilling anchor is +
        orderedPrismFilling anchor is * boundary =
      LinearMap.id - orderedPrismProjection anchor is := by
  induction is with
  | nil => simp [orderedPrismFilling, orderedPrismProjection]
  | cons i is ih =>
      simp only [orderedPrismFilling, orderedPrismProjection]
      let P := projection anchor i
      let H := homotopy anchor i
      let F := orderedPrismFilling anchor is
      let Q := orderedPrismProjection anchor is
      have hP : boundary (B := B) * P = P * boundary :=
        (projection_boundary_commute anchor i).symm
      have hH : boundary (B := B) * H + H * boundary = LinearMap.id - P :=
        fullBoundaryHomotopy_prism anchor i
      have hExpand :
          boundary * (H + P * F) + (H + P * F) * boundary =
            (boundary * H + H * boundary) + P * (boundary * F + F * boundary) := by
        calc
          boundary * (H + P * F) + (H + P * F) * boundary =
              (boundary * H + H * boundary) +
                (boundary * P * F + P * F * boundary) := by noncomm_ring
          _ = (boundary * H + H * boundary) +
                (P * boundary * F + P * F * boundary) := by rw [hP]
          _ = (boundary * H + H * boundary) +
                P * (boundary * F + F * boundary) := by noncomm_ring
      rw [hExpand, hH, ih]
      have hPid : P * LinearMap.id = P := by
        simpa only [Module.End.one_eq_id] using (mul_one P)
      rw [mul_sub, hPid]
      abel

theorem projection_orderedPrismProjection_commute {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (is : List (Fin d)) (hnd : is.Nodup)
    (i : Fin d) (hi : i ∉ is) :
    projection anchor i * orderedPrismProjection anchor is =
      orderedPrismProjection anchor is * projection anchor i := by
  induction is with
  | nil =>
      apply LinearMap.ext
      intro x
      rfl
  | cons j is ih =>
      simp only [List.nodup_cons] at hnd
      simp only [List.mem_cons, not_or] at hi
      change projection anchor i *
          (projection anchor j * orderedPrismProjection anchor is) =
        (projection anchor j * orderedPrismProjection anchor is) * projection anchor i
      calc
        projection anchor i * (projection anchor j * orderedPrismProjection anchor is) =
            (projection anchor i * projection anchor j) * orderedPrismProjection anchor is := by
              rw [mul_assoc]
        _ = (projection anchor j * projection anchor i) * orderedPrismProjection anchor is := by
              rw [projection_commute anchor i j hi.1]
        _ = projection anchor j * (projection anchor i * orderedPrismProjection anchor is) := by
              rw [mul_assoc]
        _ = projection anchor j * (orderedPrismProjection anchor is * projection anchor i) := by
              rw [ih hnd.2 hi.2]
        _ = (projection anchor j * orderedPrismProjection anchor is) * projection anchor i := by
              rw [mul_assoc]

theorem orderedPrismProjection_kills_axis {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (is : List (Fin d)) (hnd : is.Nodup)
    (i : Fin d) (hi : i ∈ is) (c : Cell d B) (haxis : i ∈ cellAxes c) :
    orderedPrismProjection anchor is (basisChain c) = 0 := by
  induction is generalizing i c with
  | nil => simp at hi
  | cons j is ih =>
      simp only [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hi with hji | hiTail
      · subst j
        have hcomm : projection anchor i * orderedPrismProjection anchor is =
            orderedPrismProjection anchor is * projection anchor i :=
          projection_orderedPrismProjection_commute anchor is hnd.2 i hnd.1
        calc
          orderedPrismProjection anchor (i :: is) (basisChain c) =
              orderedPrismProjection anchor is (projection anchor i (basisChain c)) := by
                change (projection anchor i * orderedPrismProjection anchor is) (basisChain c) = _
                rw [hcomm]
                rfl
          _ = 0 := by
            have hzero : projection anchor i (basisChain c) = 0 := by
              cases hci : c i with
              | inl v =>
                  have hiMem : coordIsEdge (c i) := by simpa [cellAxes] using haxis
                  rw [hci] at hiMem
                  simp [coordIsEdge] at hiMem
              | inr e => simp [projection_basis, projectionBasis, hci]
            rw [hzero]
            simp
      · have hne : j ≠ i := by
          intro hEq
          subst j
          exact hnd.1 hiTail
        have htail : orderedPrismProjection anchor is (basisChain c) = 0 :=
          ih hnd.2 i hiTail c haxis
        change projection anchor j (orderedPrismProjection anchor is (basisChain c)) = 0
        rw [htail]
        simp

theorem orderedPrismProjection_kills_positiveCell {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (c : Cell d B) (hpos : 0 < cellDegree c) :
    orderedPrismProjection anchor (List.finRange d) (basisChain c) = 0 := by
  have hnonempty : (cellAxes c).Nonempty := Finset.card_pos.mp hpos
  obtain ⟨i, hi⟩ := hnonempty
  have hiList : i ∈ List.finRange d := by simp
  exact orderedPrismProjection_kills_axis anchor (List.finRange d)
    (List.nodup_finRange d) i hiList c hi

theorem orderedPrismProjection_kills_positiveSupport {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) (hq : positiveDegreeSupport q) :
    orderedPrismProjection anchor (List.finRange d) q = 0 := by
  classical
  rw [← Finsupp.sum_single q]
  unfold Finsupp.sum
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro c hc
  have hsingle : Finsupp.single c (q c) = q c • basisChain c := by
    ext x
    by_cases hx : x = c <;> simp [basisChain, hx]
  rw [hsingle, map_smul, orderedPrismProjection_kills_positiveCell anchor c (hq c hc)]
  simp

theorem exists_boundary_eq_of_cycle_positive {d : ℕ} {B : Box d}
    (anchor : Anchor d B) (q : Chain d B) (hq : positiveDegreeSupport q)
    (hcycle : boundary (B := B) q = 0) :
    ∃ m : Chain d B, boundary m = q := by
  refine ⟨orderedPrismFilling anchor (List.finRange d) q, ?_⟩
  have hprism := congrArg (fun T : Chain d B →ₗ[ℤ] Chain d B => T q)
    (orderedPrism_identity anchor (List.finRange d))
  change boundary (orderedPrismFilling anchor (List.finRange d) q) +
      orderedPrismFilling anchor (List.finRange d) (boundary q) =
    q - orderedPrismProjection anchor (List.finRange d) q at hprism
  have hproj := orderedPrismProjection_kills_positiveSupport anchor q hq
  rw [hcycle, map_zero, hproj, sub_zero, add_zero] at hprism
  exact hprism

theorem axisBoundary_anticommute {d : ℕ} {B : Box d} (i j : Fin d) (hij : i ≠ j) :
    axisBoundary (B := B) i * axisBoundary (B := B) j =
      -(axisBoundary (B := B) j * axisBoundary (B := B) i) := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single c z =>
      have hsingle : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases hx : x = c <;> simp [basisChain, hx]
      rw [hsingle, map_smul, map_smul]
      change z • axisBoundary i (axisBoundary j (basisChain c)) =
        z • (-axisBoundary j (axisBoundary i (basisChain c)))
      rw [axisBoundary_basis, axisBoundary_basis]
      cases hci : c i with
      | inl vi =>
          cases hcj : c j <;>
            simp [axisBoundary, axisBoundaryBasis, hci, hcj, basisChain, hij]
      | inr ei =>
          cases hcj : c j with
          | inl vj =>
              simp [axisBoundary, axisBoundaryBasis, hci, hcj, basisChain, Ne.symm hij]
          | inr ej =>
              have hiAxis : i ∈ cellAxes c := by
                simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [hci]
                simp [coordIsEdge]
              have hjAxis : j ∈ cellAxes c := by
                simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [hcj]
                simp [coordIsEdge]
              have hsign :
                  (-1 : ℤ) ^ cellRankBefore c j *
                    (-1 : ℤ) ^ cellRankBefore (lowerFace c j ej) i =
                  - ((-1 : ℤ) ^ cellRankBefore c i *
                    (-1 : ℤ) ^ cellRankBefore (lowerFace c i ei) j) := by
                by_cases hlt : i < j
                · have h := cellSignSwap c hlt hiAxis hjAxis ei ej
                  nlinarith [h]
                · have hji : j < i := by omega
                  exact cellSignSwap c hji hjAxis hiAxis ej ei
              have hUU : upperFace (upperFace c j ej) i ei =
                  upperFace (upperFace c i ei) j ej := by
                change vertexUpdate (vertexUpdate c j _) i _ =
                  vertexUpdate (vertexUpdate c i _) j _
                exact vertexUpdate_commute c (Ne.symm hij) _ _
              have hLU : lowerFace (upperFace c j ej) i ei =
                  upperFace (lowerFace c i ei) j ej := by
                change vertexUpdate (vertexUpdate c j _) i _ =
                  vertexUpdate (vertexUpdate c i _) j _
                exact vertexUpdate_commute c (Ne.symm hij) _ _
              have hUL : upperFace (lowerFace c j ej) i ei =
                  lowerFace (upperFace c i ei) j ej := by
                change vertexUpdate (vertexUpdate c j _) i _ =
                  vertexUpdate (vertexUpdate c i _) j _
                exact vertexUpdate_commute c (Ne.symm hij) _ _
              have hLL : lowerFace (lowerFace c j ej) i ei =
                  lowerFace (lowerFace c i ei) j ej := by
                change vertexUpdate (vertexUpdate c j _) i _ =
                  vertexUpdate (vertexUpdate c i _) j _
                exact vertexUpdate_commute c (Ne.symm hij) _ _
              have hcoeff : z * ((-1 : ℤ) ^ cellRankBefore c j *
                    (-1 : ℤ) ^ axisRank ((cellAxes c).erase j) i) =
                  -(z * ((-1 : ℤ) ^ cellRankBefore c i *
                    (-1 : ℤ) ^ axisRank ((cellAxes c).erase i) j)) := by
                have h := congrArg (fun x : ℤ => z * x) hsign
                simpa using h
              simp [axisBoundary, axisBoundaryBasis, hci, hcj, basisChain,
                hUU, hLU, hUL, hLL, hij, Ne.symm hij,
                smul_sub]
              rw [hcoeff]
              simp only [Finsupp.single_neg]
              abel

theorem axisBoundary_square_zero {d : ℕ} {B : Box d} (i : Fin d) :
    axisBoundary (B := B) i * axisBoundary (B := B) i = 0 := by
  apply LinearMap.ext
  intro q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single c z =>
      have hsingle : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases hx : x = c <;> simp [basisChain, hx]
      rw [hsingle, map_smul]
      cases hci : c i with
      | inl vi =>
          simp [axisBoundary, axisBoundaryBasis, hci, basisChain]
      | inr ei =>
          simp [axisBoundary, axisBoundaryBasis, hci, basisChain,
            lowerFace, upperFace, vertexUpdate]

theorem two_smul_linearMap_injective {d : ℕ} {B : Box d}
    (T : Chain d B →ₗ[ℤ] Chain d B) (hT : (2 : ℤ) • T = 0) : T = 0 := by
  apply LinearMap.ext
  intro q
  ext c
  have hc : (2 : ℤ) * T q c = 0 := by
    have h := congrArg (fun S : Chain d B →ₗ[ℤ] Chain d B => S q c) hT
    simpa using h
  rcases mul_eq_zero.mp hc with htwo | hval
  · norm_num at htwo
  · exact hval

theorem boundary_square_zero {d : ℕ} {B : Box d} :
    boundary (B := B) * boundary (B := B) = 0 := by
  change (∑ i : Fin d, axisBoundary (B := B) i) *
      (∑ j : Fin d, axisBoundary (B := B) j) = 0
  let X : Chain d B →ₗ[ℤ] Chain d B :=
    ∑ i : Fin d, ∑ j : Fin d,
      axisBoundary (B := B) i * axisBoundary (B := B) j
  have hexpand :
      (∑ i : Fin d, axisBoundary (B := B) i) *
      (∑ j : Fin d, axisBoundary (B := B) j) = X := by
    rw [Finset.sum_mul]
    simp only [X, Finset.mul_sum]
  have hanti (i j : Fin d) :
      axisBoundary (B := B) i * axisBoundary (B := B) j =
        -(axisBoundary (B := B) j * axisBoundary (B := B) i) := by
    by_cases hij : i = j
    · subst j
      rw [axisBoundary_square_zero]
      simp
    · exact axisBoundary_anticommute i j hij
  have hneg : X = -(∑ i : Fin d, ∑ j : Fin d,
      axisBoundary (B := B) j * axisBoundary (B := B) i) := by
    change (∑ i : Fin d, ∑ j : Fin d,
      axisBoundary (B := B) i * axisBoundary (B := B) j) =
      -(∑ i : Fin d, ∑ j : Fin d,
        axisBoundary (B := B) j * axisBoundary (B := B) i)
    rw [← Finset.sum_neg_distrib]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact hanti i j
  have hswap : (∑ i : Fin d, ∑ j : Fin d,
      axisBoundary (B := B) j * axisBoundary (B := B) i) = X := by
    simpa only [X] using
      (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun i j : Fin d =>
          axisBoundary (B := B) j * axisBoundary (B := B) i))
  have hX : X = -X := by
    calc
      X = -(∑ i : Fin d, ∑ j : Fin d,
          axisBoundary (B := B) j * axisBoundary (B := B) i) := hneg
      _ = -X := by rw [hswap]
  have hadd : X + X = 0 := by
    calc
      X + X = -X + X := congrArg (fun t => t + X) hX
      _ = 0 := neg_add_cancel X
  have htwo : (2 : ℤ) • X = 0 := by simpa [two_smul] using hadd
  rw [hexpand]
  exact two_smul_linearMap_injective X htwo

theorem fillingOperator_prism_identity {d : ℕ} {B : Box d}
    (anchor : Anchor d B) :
    boundary (B := B) * fillingOperator anchor + fillingOperator anchor * boundary =
      LinearMap.id - finalProjection anchor := by
  simpa [fillingOperator, finalProjection] using
    orderedPrism_identity anchor (List.finRange d)
end
end FroehlichSpencer.FS82.Cubical

end
