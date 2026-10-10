/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.FourierParseval


open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Fourier
open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable


@[expose] public section

namespace FroehlichSpencer.FS82.Infinite.FourierVariational


theorem char_lowerFace (c : LatticeCell 4) (i : Fin 4) (t : ℤ)
    (hc : c i = Sum.inr t) (k : Torus4) :
    latticeCharacter (latticeCellPoint (latticeLowerFace c i t)) k =
      latticeCharacter (latticeCellPoint c) k := by
  fin_cases i
  · have hci : c 0 = Sum.inr t := by simpa using hc
    simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate, latticeLowerFace, hci]
  · have hci : c 1 = Sum.inr t := by simpa using hc
    simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate, latticeLowerFace, hci]
  · have hci : c 2 = Sum.inr t := by simpa using hc
    simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate, latticeLowerFace, hci]
  · have hci : c 3 = Sum.inr t := by simpa using hc
    simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate, latticeLowerFace, hci]

theorem char_upperFace (c : LatticeCell 4) (i : Fin 4) (t : ℤ)
    (hc : c i = Sum.inr t) (k : Torus4) :
    latticeCharacter (latticeCellPoint (latticeUpperFace c i t)) k =
      fourier (-1) (torus4Coord k i) * latticeCharacter (latticeCellPoint c) k := by
  fin_cases i
  all_goals
    first
    | (have hci : c 0 = Sum.inr t := by simpa using hc
       simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate, latticeUpperFace, hci, torus4Coord]; ring)
    | (have hci : c 1 = Sum.inr t := by simpa using hc
       simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate, latticeUpperFace, hci, torus4Coord]; ring)
    | (have hci : c 2 = Sum.inr t := by simpa using hc
       simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate, latticeUpperFace, hci, torus4Coord]; ring)
    | (have hci : c 3 = Sum.inr t := by simpa using hc
       simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate, latticeUpperFace, hci, torus4Coord]; ring)

theorem latticeBoundaryBasis_link (c : LatticeCell 4) (i : Fin 4)
    (haxis : latticeLinkAxisCell c i) :
    latticeBoundaryBasis c =
      latticeBasis (latticeUpperFace c i (Sum.elim id id (c i))) -
        latticeBasis (latticeLowerFace c i (Sum.elim id id (c i))) := by
  have hiEdge : latticeIsEdge (c i) := haxis.1
  cases hci : c i with
  | inl v => simp [latticeIsEdge, hci] at hiEdge
  | inr t =>
      have hrank : latticeRankBefore c i = 0 := by
        unfold latticeRankBefore
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact haxis.2 j (ne_of_lt hj.1) hj.2
      unfold latticeBoundaryBasis
      rw [Finset.sum_eq_single i]
      · simp [hci, hrank, latticeBasis]
      · intro j hj hji
        cases hcj : c j with
        | inl v => simp
        | inr e =>
            have hnot := haxis.2 j hji
            simp [latticeIsEdge, hcj] at hnot
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim

theorem boundaryFourier_link (c : LatticeCell 4) (i : Fin 4)
    (haxis : latticeLinkAxisCell c i) (k : Torus4) :
    latticeChainFourierFunctional ∅ k
        (globalBoundary (Finsupp.single c (1 : ℝ))) =
      (fourier (-1) (torus4Coord k i) - 1) *
        latticeCharacter (latticeCellPoint c) k := by
  have hci : c i = Sum.inr (Sum.elim id id (c i)) := by
    cases h : c i with
    | inl v =>
        have hEdge := haxis.1
        simp [latticeIsEdge, h] at hEdge
    | inr t => rfl
  rw [globalBoundary, realLatticeBoundary_basis, latticeBoundaryBasis_link c i haxis]
  have hupper : Fourier.latticeCellAxes
      (latticeUpperFace c i (Sum.elim id id (c i))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hj' : latticeIsEdge (latticeUpperFace c i (Sum.elim id id (c i)) j) := by
      simpa [Fourier.latticeCellAxes] using hj
    by_cases hji : j = i
    · subst j
      simp [latticeIsEdge, latticeUpperFace] at hj'
    · have hnot := haxis.2 j hji
      exact hnot (by simpa [latticeIsEdge, latticeUpperFace, hji] using hj')
  have hlower : Fourier.latticeCellAxes
      (latticeLowerFace c i (Sum.elim id id (c i))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hj' : latticeIsEdge (latticeLowerFace c i (Sum.elim id id (c i)) j) := by
      simpa [Fourier.latticeCellAxes] using hj
    by_cases hji : j = i
    · subst j
      simp [latticeIsEdge, latticeLowerFace] at hj'
    · have hnot := haxis.2 j hji
      exact hnot (by simpa [latticeIsEdge, latticeLowerFace, hji] using hj')
  have hcast : castLatticeChain
      (latticeBasis (latticeUpperFace c i (Sum.elim id id (c i))) -
        latticeBasis (latticeLowerFace c i (Sum.elim id id (c i)))) =
      Finsupp.single (latticeUpperFace c i (Sum.elim id id (c i))) (1 : ℝ) -
        Finsupp.single (latticeLowerFace c i (Sum.elim id id (c i))) 1 := by
    ext d
    simp [castLatticeChain_apply, latticeBasis, Finsupp.single_apply, Int.cast_sub]
  rw [hcast, map_sub]
  have hup : latticeChainFourierFunctional ∅ k
      (Finsupp.single (latticeUpperFace c i (Sum.elim id id (c i))) (1 : ℝ)) =
      latticeCharacter (latticeCellPoint (latticeUpperFace c i (Sum.elim id id (c i)))) k := by
    simp [latticeChainFourierFunctional, hupper]
  have hlo : latticeChainFourierFunctional ∅ k
      (Finsupp.single (latticeLowerFace c i (Sum.elim id id (c i))) (1 : ℝ)) =
      latticeCharacter (latticeCellPoint (latticeLowerFace c i (Sum.elim id id (c i)))) k := by
    simp [latticeChainFourierFunctional, hlower]
  rw [hup, hlo, char_upperFace c i (Sum.elim id id (c i)) hci k,
    char_lowerFace c i (Sum.elim id id (c i)) hci k]
  ring

private theorem sum_linkAxis_function (c : LatticeCell 4) (f : Fin 4 → ℂ)
    (hc : latticeCellDegree c = 1) :
    ∑ i : Fin 4, (if latticeLinkAxisCell c i then f i else 0) =
      f (Classical.choose (existsUnique_latticeLinkAxis_of_degree_one c hc)) := by
  classical
  obtain ⟨i, hi, huniq⟩ := existsUnique_latticeLinkAxis_of_degree_one c hc
  have hchosen : Classical.choose (existsUnique_latticeLinkAxis_of_degree_one c hc) = i := by
    exact huniq _ (Classical.choose_spec (existsUnique_latticeLinkAxis_of_degree_one c hc)).1
  have hfilter : Finset.univ.filter (fun j : Fin 4 => latticeLinkAxisCell c j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨huniq j, fun hj => by simpa [hj] using hi⟩
  calc
    ∑ j : Fin 4, (if latticeLinkAxisCell c j then f j else 0) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin 4 => latticeLinkAxisCell c j), f j := by
      rw [← Finset.sum_filter]
    _ = f i := by rw [hfilter]; simp
    _ = f (Classical.choose (existsUnique_latticeLinkAxis_of_degree_one c hc)) := by
      rw [hchosen]

private theorem linearMap_apply_sum_support
    {α : Type*} [DecidableEq α] (L : (α →₀ ℝ) →ₗ[ℝ] ℂ)
    (q : α →₀ ℝ) :
    L q = ∑ c ∈ q.support, (q c : ℂ) * L (Finsupp.single c 1) := by
  classical
  have hrepr : q = ∑ c ∈ q.support, Finsupp.single c (q c) := by
    simpa only [Finsupp.sum] using (Finsupp.sum_single q).symm
  calc
    L q = L (∑ c ∈ q.support, Finsupp.single c (q c)) := congrArg L hrepr
    _ = ∑ c ∈ q.support, L (Finsupp.single c (q c)) := by
      exact map_sum L (fun c => Finsupp.single c (q c)) q.support
    _ = ∑ c ∈ q.support, (q c : ℂ) * L (Finsupp.single c 1) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hsingle : Finsupp.single c (q c) = q c • Finsupp.single c (1 : ℝ) := by
        ext d
        by_cases h : d = c <;> simp [h]
      rw [hsingle, map_smul]
      simp

theorem boundaryFourier_linkField (μ : GlobalLinkField) (k : Torus4) :
    latticeChainFourierFunctional ∅ k
        (globalBoundary (μ : RealLatticeChain 4)) =
      ∑ i : Fin 4, (fourier (-1) (torus4Coord k i) - 1) *
        globalLinkFourierComponent μ i k := by
  classical
  let L : RealLatticeChain 4 →ₗ[ℝ] ℂ :=
    (latticeChainFourierFunctional ∅ k).comp globalBoundary
  have hL : L (μ : RealLatticeChain 4) =
      ∑ c ∈ μ.1.support, (μ.1 c : ℂ) *
        L (Finsupp.single c (1 : ℝ)) := linearMap_apply_sum_support L μ.1
  change L (μ : RealLatticeChain 4) = _
  rw [hL]
  calc
    _ = ∑ c ∈ μ.1.support, ∑ i : Fin 4,
          (if latticeLinkAxisCell c i then
            (fourier (-1) (torus4Coord k i) - 1) *
              ((μ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k)
            else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hdegree := μ.2 c hc
      have haxis := existsUnique_latticeLinkAxis_of_degree_one c hdegree
      let i₀ := Classical.choose haxis
      have hi₀ : latticeLinkAxisCell c i₀ := Classical.choose_spec haxis |>.1
      have hchosen : Classical.choose haxis = i₀ := rfl
      have hboundary : L (Finsupp.single c (1 : ℝ)) =
          (fourier (-1) (torus4Coord k i₀) - 1) *
            latticeCharacter (latticeCellPoint c) k := by
        change latticeChainFourierFunctional ∅ k
          (globalBoundary (Finsupp.single c (1 : ℝ))) = _
        exact boundaryFourier_link c i₀ hi₀ k
      have hsum := sum_linkAxis_function c
        (fun i => (fourier (-1) (torus4Coord k i) - 1) *
          ((μ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k)) hdegree
      have hsum' : ∑ i : Fin 4,
          (if latticeLinkAxisCell c i then
            (fourier (-1) (torus4Coord k i) - 1) *
              ((μ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k)
            else 0) = (μ.1 c : ℂ) * L (Finsupp.single c 1) := by
        rw [hsum, show Classical.choose haxis = i₀ by rfl, hboundary]
        ring
      exact hsum'.symm
    _ = ∑ i : Fin 4, ∑ c ∈ globalLinkAxisSupport μ i,
          (fourier (-1) (torus4Coord k i) - 1) *
            ((μ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k) := by
      simp_rw [globalLinkAxisSupport, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 4, (fourier (-1) (torus4Coord k i) - 1) *
          globalLinkFourierComponent μ i k := by
      apply Finset.sum_congr rfl
      intro i hi
      have hcomponent : globalLinkFourierComponent μ i k =
          ∑ c ∈ globalLinkAxisSupport μ i,
            (μ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k := rfl
      rw [← Finset.mul_sum, ← hcomponent]

/-- A globally co-closed link field has no Fourier component in the gradient
direction at any frequency. -/
theorem chainFourierFunctional_single (axes : Finset (Fin 4))
    (c : LatticeCell 4) (r : ℝ) (k : Torus4) :
    latticeChainFourierFunctional axes k (Finsupp.single c r) =
      if Fourier.latticeCellAxes c = axes then
        (r : ℂ) * latticeCharacter (latticeCellPoint c) k else 0 := by
  classical
  simp [latticeChainFourierFunctional, Finsupp.linearCombination_single]

noncomputable def fourierLatticeCoboundaryTerm (c : LatticeCell 4) (i : Fin 4) :
    RealLatticeChain 4 :=
  match c i with
  | Sum.inl t =>
      ((-1 : ℝ) ^ latticeRankBefore c i) •
        (Finsupp.single (latticeEdgeCell c i (t - 1)) 1 -
          Finsupp.single (latticeEdgeCell c i t) 1)
  | Sum.inr _ => 0

private theorem sourceRealLatticeCoboundary_single_eq_sum_fourier (c : LatticeCell 4) :
    sourceRealLatticeCoboundary (Finsupp.single c (1 : ℝ)) =
      ∑ i : Fin 4, fourierLatticeCoboundaryTerm c i := by
  rw [sourceRealLatticeCoboundary_single]
  simp only [one_smul]
  ext x
  simp only [castLatticeChain, Finsupp.mapRange_apply,
    latticeCoboundaryBasis, Finset.sum_apply']
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i <;>
    simp [fourierLatticeCoboundaryTerm, hci, latticeBasis, Finsupp.single_apply,
      Int.cast_pow, Int.cast_sub]

theorem char_edgeCell_vertex (c : LatticeCell 4) (i : Fin 4) (t : ℤ)
    (hc : c i = Sum.inl t) (k : Torus4) :
    latticeCharacter (latticeCellPoint (latticeEdgeCell c i (t - 1))) k =
      fourier 1 (torus4Coord k i) * latticeCharacter (latticeCellPoint c) k := by
  fin_cases i
  · have hci : c 0 = Sum.inl t := by simpa using hc
    change latticeCharacter (latticeCellPoint (latticeEdgeCell c (0 : Fin 4) (t - 1))) k =
      fourier 1 k.1 * latticeCharacter (latticeCellPoint c) k
    simp only [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate,
      latticeEdgeCell, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0),
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0),
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0), hci, Sum.elim]
    simp only [id_eq]
    rw [show -(t - 1) = 1 + (-t) by omega, fourier_add]
    ring
  · have hci : c 1 = Sum.inl t := by simpa using hc
    change latticeCharacter (latticeCellPoint (latticeEdgeCell c (1 : Fin 4) (t - 1))) k =
      fourier 1 k.2.1 * latticeCharacter (latticeCellPoint c) k
    simp only [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate,
      latticeEdgeCell, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1), hci, Sum.elim]
    simp only [id_eq]
    rw [show -(t - 1) = 1 + (-t) by omega, fourier_add]
    ring
  · have hci : c 2 = Sum.inl t := by simpa using hc
    change latticeCharacter (latticeCellPoint (latticeEdgeCell c (2 : Fin 4) (t - 1))) k =
      fourier 1 k.2.2.1 * latticeCharacter (latticeCellPoint c) k
    simp only [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate,
      latticeEdgeCell, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2), hci, Sum.elim]
    simp only [id_eq]
    rw [show -(t - 1) = 1 + (-t) by omega, fourier_add]
    ring
  · have hci : c 3 = Sum.inl t := by simpa using hc
    change latticeCharacter (latticeCellPoint (latticeEdgeCell c (3 : Fin 4) (t - 1))) k =
      fourier 1 k.2.2.2 * latticeCharacter (latticeCellPoint c) k
    simp only [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate,
      latticeEdgeCell, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3),
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3),
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3), hci, Sum.elim]
    simp only [id_eq]
    rw [show -(t - 1) = 1 + (-t) by omega, fourier_add]
    ring


theorem edgeCellAxes_link (c : LatticeCell 4) (i j : Fin 4) (t : ℤ)
    (haxis : latticeLinkAxisCell c i) :
    Fourier.latticeCellAxes (latticeEdgeCell c j t) = {i, j} := by
  classical
  ext l
  simp only [Fourier.latticeCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  by_cases hlj : l = j
  · subst l
    simp [latticeEdgeCell, latticeIsEdge]
  · by_cases hli : l = i
    · subst l
      constructor
      · intro _
        simp
      · intro _
        have hcell : latticeEdgeCell c j (t) i = c i := by
          simp [latticeEdgeCell, Function.update_of_ne hlj]
        rw [hcell]
        exact haxis.1
    · have hcell : latticeEdgeCell c j (t) l = c l := by
        simp [latticeEdgeCell, Function.update_of_ne hlj]
      rw [hcell]
      constructor
      · intro he
        exact False.elim (haxis.2 l hli he)
      · intro hmem
        simp only [Finset.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact (hli hmem).elim
        · exact (hlj hmem).elim


theorem char_edgeCell_vertex_at (c : LatticeCell 4) (i : Fin 4) (t : ℤ)
    (hc : c i = Sum.inl t) (k : Torus4) :
    latticeCharacter (latticeCellPoint (latticeEdgeCell c i t)) k =
      latticeCharacter (latticeCellPoint c) k := by
  fin_cases i
  · have hci : c 0 = Sum.inl t := by simpa using hc
    simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate,
      latticeEdgeCell, hci, Sum.elim]
  · have hci : c 1 = Sum.inl t := by simpa using hc
    simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate,
      latticeEdgeCell, hci, Sum.elim]
  · have hci : c 2 = Sum.inl t := by simpa using hc
    simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate,
      latticeEdgeCell, hci, Sum.elim]
  · have hci : c 3 = Sum.inl t := by simpa using hc
    simp [latticeCharacter, latticeCellPoint, latticeCellBaseCoordinate,
      latticeEdgeCell, hci, Sum.elim]

theorem latticeRankBefore_link_lt (c : LatticeCell 4) (i j : Fin 4)
    (haxis : latticeLinkAxisCell c i) (hij : i < j) :
    latticeRankBefore c j = 1 := by
  classical
  unfold latticeRankBefore
  have hfilter : Finset.univ.filter (fun l : Fin 4 => l < j ∧ latticeIsEdge (c l)) = {i} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hlj, hle⟩
      by_cases hli : l = i
      · exact hli
      · exact (haxis.2 l hli hle).elim
    · intro hli
      subst l
      exact ⟨hij, haxis.1⟩
  rw [hfilter]
  simp


theorem fourierLatticeCoboundaryTerm_pair_eval (c : LatticeCell 4) (i j : Fin 4)
    (haxis : latticeLinkAxisCell c i) (hij : i < j)
    (t : ℤ) (hcj : c j = Sum.inl t) (k : Torus4) :
    latticeChainFourierFunctional {i, j} k (fourierLatticeCoboundaryTerm c j) =
      -((fourier 1 (torus4Coord k j) - 1) *
        latticeCharacter (latticeCellPoint c) k) := by
  have hji : j ≠ i := ne_of_gt hij
  have hrank := latticeRankBefore_link_lt c i j haxis hij
  rw [fourierLatticeCoboundaryTerm, hcj, hrank]
  rw [map_smul, map_sub]
  have haxesL : Fourier.latticeCellAxes (latticeEdgeCell c j (t - 1)) = {i, j} :=
    edgeCellAxes_link c i j (t - 1) haxis
  have haxesU : Fourier.latticeCellAxes (latticeEdgeCell c j t) = {i, j} :=
    edgeCellAxes_link c i j t haxis
  simp only [chainFourierFunctional_single, haxesL, haxesU]
  rw [char_edgeCell_vertex c j t hcj k, char_edgeCell_vertex_at c j t hcj k]
  norm_num
  ring

theorem coboundary_link_basis_pair_first (c : LatticeCell 4) (i j : Fin 4)
    (haxis : latticeLinkAxisCell c i) (hij : i < j) (k : Torus4) :
    latticeChainFourierFunctional {i, j} k
        (globalCoboundary (Finsupp.single c (1 : ℝ))) =
      -((fourier 1 (torus4Coord k j) - 1) *
        latticeCharacter (latticeCellPoint c) k) := by
  classical
  have hji : j ≠ i := ne_of_gt hij
  have hterm (l : Fin 4) : latticeChainFourierFunctional {i, j} k
      (fourierLatticeCoboundaryTerm c l) =
      if l = j then -((fourier 1 (torus4Coord k j) - 1) *
        latticeCharacter (latticeCellPoint c) k) else 0 := by
    by_cases hlj : l = j
    · subst l
      have hcj : c j = Sum.inl (Sum.elim id id (c j)) := by
        cases h : c j with
        | inl v => rfl
        | inr t =>
          have hnot : ¬ latticeIsEdge (c j) := haxis.2 j hji
          exact (hnot (by simp [latticeIsEdge, h])).elim
      simpa using fourierLatticeCoboundaryTerm_pair_eval c i j haxis hij _ hcj k
    · by_cases hli : l = i
      · subst l
        cases hc : c i with
        | inl v =>
            have hbad := haxis.1
            simp [latticeIsEdge, hc] at hbad
        | inr t => simp [fourierLatticeCoboundaryTerm, hc, hlj]
      · cases hc : c l with
        | inr t => simp [fourierLatticeCoboundaryTerm, hc, hlj]
        | inl v =>
          have haxesL : Fourier.latticeCellAxes (latticeEdgeCell c l (v - 1)) = {i, l} :=
            edgeCellAxes_link c i l (v - 1) haxis
          have haxesU : Fourier.latticeCellAxes (latticeEdgeCell c l v) = {i, l} :=
            edgeCellAxes_link c i l v haxis
          have hne : ({i, l} : Finset (Fin 4)) ≠ {i, j} := by
            intro heq
            have hm : l ∈ ({i, l} : Finset (Fin 4)) := by simp
            rw [heq] at hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with hmem | hmem
            · exact hli hmem
            · exact hlj hmem
          rw [fourierLatticeCoboundaryTerm, hc, map_smul, map_sub]
          simp [chainFourierFunctional_single, haxesL, haxesU, hne, hlj]
  unfold globalCoboundary
  rw [sourceRealLatticeCoboundary_single_eq_sum_fourier, map_sum]
  rw [Finset.sum_congr rfl (fun l hl => hterm l)]
  simp


theorem latticeRankBefore_link_gt (c : LatticeCell 4) (i j : Fin 4)
    (haxis : latticeLinkAxisCell c j) (hij : i < j) :
    latticeRankBefore c i = 0 := by
  classical
  unfold latticeRankBefore
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  rcases hl with ⟨hsmall, hedge⟩
  have hlj : l ≠ j := by
    intro heq
    subst l
    omega
  exact haxis.2 l hlj hedge

theorem fourierLatticeCoboundaryTerm_pair_eval_lower (c : LatticeCell 4) (i j : Fin 4)
    (haxis : latticeLinkAxisCell c j) (hij : i < j)
    (t : ℤ) (hci : c i = Sum.inl t) (k : Torus4) :
    latticeChainFourierFunctional {i, j} k (fourierLatticeCoboundaryTerm c i) =
      (fourier 1 (torus4Coord k i) - 1) *
        latticeCharacter (latticeCellPoint c) k := by
  have hji : i ≠ j := ne_of_lt hij
  have hrank := latticeRankBefore_link_gt c i j haxis hij
  rw [fourierLatticeCoboundaryTerm, hci, hrank]
  rw [map_smul, map_sub]
  have haxesL : Fourier.latticeCellAxes (latticeEdgeCell c i (t - 1)) = {i, j} := by
    have hx := edgeCellAxes_link c j i (t - 1) haxis
    simpa [Finset.pair_comm] using hx
  have haxesU : Fourier.latticeCellAxes (latticeEdgeCell c i t) = {i, j} := by
    have hx := edgeCellAxes_link c j i t haxis
    simpa [Finset.pair_comm] using hx
  simp only [chainFourierFunctional_single, haxesL, haxesU]
  rw [char_edgeCell_vertex c i t hci k, char_edgeCell_vertex_at c i t hci k]
  norm_num
  ring

theorem coboundary_link_basis_pair_second (c : LatticeCell 4) (i j : Fin 4)
    (haxis : latticeLinkAxisCell c j) (hij : i < j) (k : Torus4) :
    latticeChainFourierFunctional {i, j} k
        (globalCoboundary (Finsupp.single c (1 : ℝ))) =
      (fourier 1 (torus4Coord k i) - 1) *
        latticeCharacter (latticeCellPoint c) k := by
  classical
  have hji : i ≠ j := ne_of_lt hij
  have hterm (l : Fin 4) : latticeChainFourierFunctional {i, j} k
      (fourierLatticeCoboundaryTerm c l) =
      if l = i then (fourier 1 (torus4Coord k i) - 1) *
        latticeCharacter (latticeCellPoint c) k else 0 := by
    by_cases hli : l = i
    · subst l
      have hci : c i = Sum.inl (Sum.elim id id (c i)) := by
        cases h : c i with
        | inl v => rfl
        | inr t =>
          have hnot : ¬ latticeIsEdge (c i) := haxis.2 i hji
          exact (hnot (by simp [latticeIsEdge, h])).elim
      simpa using fourierLatticeCoboundaryTerm_pair_eval_lower c i j haxis hij _ hci k
    · by_cases hlj : l = j
      · subst l
        cases hc : c j with
        | inl v =>
            have hbad := haxis.1
            simp [latticeIsEdge, hc] at hbad
        | inr t => simp [fourierLatticeCoboundaryTerm, hc, hli]
      · cases hc : c l with
        | inr t => simp [fourierLatticeCoboundaryTerm, hc, hli]
        | inl v =>
          have haxesL : Fourier.latticeCellAxes (latticeEdgeCell c l (v - 1)) = {j, l} :=
            edgeCellAxes_link c j l (v - 1) haxis
          have haxesU : Fourier.latticeCellAxes (latticeEdgeCell c l v) = {j, l} :=
            edgeCellAxes_link c j l v haxis
          have hne : ({j, l} : Finset (Fin 4)) ≠ {i, j} := by
            intro heq
            have hm : l ∈ ({j, l} : Finset (Fin 4)) := by simp
            rw [heq] at hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with hmem | hmem
            · exact hli hmem
            · exact hlj hmem
          rw [fourierLatticeCoboundaryTerm, hc, map_smul, map_sub]
          simp [chainFourierFunctional_single, haxesL, haxesU, hne, hli]
  unfold globalCoboundary
  rw [sourceRealLatticeCoboundary_single_eq_sum_fourier, map_sum]
  rw [Finset.sum_congr rfl (fun l hl => hterm l)]
  simp


theorem fourierLatticeCoboundaryTerm_pair_zero_of_linkAxis_other
    (c : LatticeCell 4) (a i j l : Fin 4)
    (haxis : latticeLinkAxisCell c a) (hai : a ≠ i) (haj : a ≠ j)
    (k : Torus4) :
    latticeChainFourierFunctional {i, j} k (fourierLatticeCoboundaryTerm c l) = 0 := by
  by_cases hla : l = a
  · subst l
    cases hc : c a with
    | inl v =>
        have hbad := haxis.1
        simp [latticeIsEdge, hc] at hbad
    | inr t => simp [fourierLatticeCoboundaryTerm, hc]
  · cases hc : c l with
    | inr t => simp [fourierLatticeCoboundaryTerm, hc]
    | inl v =>
      have haxesL : Fourier.latticeCellAxes (latticeEdgeCell c l (v - 1)) = {a, l} :=
        edgeCellAxes_link c a l (v - 1) haxis
      have haxesU : Fourier.latticeCellAxes (latticeEdgeCell c l v) = {a, l} :=
        edgeCellAxes_link c a l v haxis
      have hne : ({a, l} : Finset (Fin 4)) ≠ {i, j} := by
        intro heq
        have hm : a ∈ ({a, l} : Finset (Fin 4)) := by simp
        rw [heq] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with hmem | hmem
        · exact hai hmem
        · exact haj hmem
      rw [fourierLatticeCoboundaryTerm, hc, map_smul, map_sub]
      simp [chainFourierFunctional_single, haxesL, haxesU, hne]

theorem coboundary_link_basis_pair_other (c : LatticeCell 4) (i j a : Fin 4)
    (haxis : latticeLinkAxisCell c a) (hai : a ≠ i) (haj : a ≠ j)
    (k : Torus4) :
    latticeChainFourierFunctional {i, j} k
        (globalCoboundary (Finsupp.single c (1 : ℝ))) = 0 := by
  classical
  unfold globalCoboundary
  rw [sourceRealLatticeCoboundary_single_eq_sum_fourier, map_sum]
  rw [Finset.sum_congr rfl (fun l hl =>
    fourierLatticeCoboundaryTerm_pair_zero_of_linkAxis_other c a i j l haxis hai haj k)]
  simp

theorem latticeLinkAxis_singleton (c : LatticeCell 4) (a : Fin 4)
    (haxis : latticeLinkAxisCell c a) : Fourier.latticeCellAxes c = {a} := by
  classical
  ext l
  simp only [Fourier.latticeCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro he
    by_contra hla
    exact haxis.2 l hla he
  · rintro rfl
    exact haxis.1

theorem coboundary_link_basis_pair_decompose (c : LatticeCell 4) (i j : Fin 4)
    (hdegree : latticeCellDegree c = 1) (hij : i < j) (k : Torus4) :
    latticeChainFourierFunctional {i, j} k
        (globalCoboundary (Finsupp.single c (1 : ℝ))) =
      (if latticeLinkAxisCell c i then
        -((fourier 1 (torus4Coord k j) - 1) *
          latticeCharacter (latticeCellPoint c) k)
       else if latticeLinkAxisCell c j then
        (fourier 1 (torus4Coord k i) - 1) *
          latticeCharacter (latticeCellPoint c) k
       else 0) := by
  obtain ⟨a, ha, huniq⟩ := existsUnique_latticeLinkAxis_of_degree_one c hdegree
  by_cases hai : a = i
  · subst a
    have haxis : latticeLinkAxisCell c i := ha
    simp only [haxis]
    exact coboundary_link_basis_pair_first c i j haxis hij k
  · by_cases haj : a = j
    · subst a
      have haxis : latticeLinkAxisCell c j := ha
      have hnotI : ¬ latticeLinkAxisCell c i := by
        intro h
        have heq : i = j := huniq i h
        omega
      simp only [hnotI, haxis]
      exact coboundary_link_basis_pair_second c i j haxis hij k
    · have haxisI : ¬ latticeLinkAxisCell c i := by
        intro h
        exact hai (huniq i h).symm
      have haxisJ : ¬ latticeLinkAxisCell c j := by
        intro h
        exact haj (huniq j h).symm
      simp only [haxisI, haxisJ]
      exact coboundary_link_basis_pair_other c i j a ha hai haj k

theorem coboundaryFourierComponent_pair (φ : GlobalLinkField) (i j : Fin 4)
    (hij : i < j) (k : Torus4) :
    latticeChainFourierComponent
      (globalCoboundary (φ : RealLatticeChain 4)) {i, j} k =
      -((fourier 1 (torus4Coord k j) - 1) * globalLinkFourierComponent φ i k) +
        ((fourier 1 (torus4Coord k i) - 1) * globalLinkFourierComponent φ j k) := by
  classical
  rw [latticeChainFourierComponent_eq_functional]
  let L : RealLatticeChain 4 →ₗ[ℝ] ℂ :=
    (latticeChainFourierFunctional {i, j} k).comp globalCoboundary
  have hleft : L (φ : RealLatticeChain 4) =
      ∑ c ∈ φ.1.support, (φ.1 c : ℂ) * L (Finsupp.single c 1) :=
    linearMap_apply_sum_support L φ.1
  change L (φ : RealLatticeChain 4) = _
  rw [hleft]
  have hpoint (c : LatticeCell 4) (hc : c ∈ φ.1.support) :
      (φ.1 c : ℂ) * L (Finsupp.single c 1) =
        (if latticeLinkAxisCell c i then
          -((fourier 1 (torus4Coord k j) - 1) *
            ((φ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k)) else 0) +
        (if latticeLinkAxisCell c j then
          (fourier 1 (torus4Coord k i) - 1) *
            ((φ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k) else 0) := by
    have hdeg := φ.2 c hc
    have hbasis := coboundary_link_basis_pair_decompose c i j hdeg hij k
    rw [show L (Finsupp.single c 1) =
      latticeChainFourierFunctional {i, j} k (globalCoboundary (Finsupp.single c 1)) by rfl,
      hbasis]
    by_cases hci : latticeLinkAxisCell c i
    · have hcj : ¬ latticeLinkAxisCell c j := by
        intro hcj
        have hdeg := φ.2 c hc
        obtain ⟨a, ha, huniq⟩ := existsUnique_latticeLinkAxis_of_degree_one c hdeg
        have hia : i = a := huniq i hci
        have hja : j = a := huniq j hcj
        omega
      simp [hci, hcj]
      ring
    · by_cases hcj : latticeLinkAxisCell c j <;> (simp [hci, hcj] <;> ring)
  calc
    _ = ∑ c ∈ φ.1.support,
          ((if latticeLinkAxisCell c i then
              -((fourier 1 (torus4Coord k j) - 1) *
                ((φ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k)) else 0) +
           (if latticeLinkAxisCell c j then
              (fourier 1 (torus4Coord k i) - 1) *
                ((φ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k) else 0)) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hpoint c hc
    _ = (∑ c ∈ φ.1.support,
          if latticeLinkAxisCell c i then
            -((fourier 1 (torus4Coord k j) - 1) *
              ((φ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k)) else 0) +
        ∑ c ∈ φ.1.support,
          if latticeLinkAxisCell c j then
            (fourier 1 (torus4Coord k i) - 1) *
              ((φ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k) else 0 := by
      rw [Finset.sum_add_distrib]
    _ = -((fourier 1 (torus4Coord k j) - 1) * globalLinkFourierComponent φ i k) +
        ((fourier 1 (torus4Coord k i) - 1) * globalLinkFourierComponent φ j k) := by
      let s := φ.1.support
      let fi (c : LatticeCell 4) := (φ.1 c : ℂ) * latticeCharacter (latticeCellPoint c) k
      have hcomp (a : Fin 4) : globalLinkFourierComponent φ a k =
          ∑ c ∈ s, if latticeLinkAxisCell c a then fi c else 0 := by
        unfold globalLinkFourierComponent globalLinkAxisSupport fi
        rw [Finset.sum_filter]
      have hfactor (a : Fin 4) (A : ℂ) :
          (∑ c ∈ s, if latticeLinkAxisCell c a then A * fi c else 0) =
            A * (∑ c ∈ s, if latticeLinkAxisCell c a then fi c else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        by_cases ha : latticeLinkAxisCell c a <;> simp [ha]
      rw [hcomp i, hcomp j]
      have htermI :
          (∑ c ∈ s, if latticeLinkAxisCell c i then
              -((fourier 1 (torus4Coord k j) - 1) * fi c) else 0) =
            -(fourier 1 (torus4Coord k j) - 1) *
              (∑ c ∈ s, if latticeLinkAxisCell c i then fi c else 0) := by
        calc
          _ = ∑ c ∈ s, if latticeLinkAxisCell c i then
                (-(fourier 1 (torus4Coord k j) - 1)) * fi c else 0 := by
            apply Finset.sum_congr rfl
            intro c hc
            by_cases ha : latticeLinkAxisCell c i
            · simp [ha]
              ring
            · simp [ha]
          _ = _ := hfactor i (-(fourier 1 (torus4Coord k j) - 1))
      have htermJ :
          (∑ c ∈ s, if latticeLinkAxisCell c j then
              (fourier 1 (torus4Coord k i) - 1) * fi c else 0) =
            (fourier 1 (torus4Coord k i) - 1) *
              (∑ c ∈ s, if latticeLinkAxisCell c j then fi c else 0) :=
        hfactor j (fourier 1 (torus4Coord k i) - 1)
      rw [htermI, htermJ]
      ring


theorem globallyCoClosed_fourier_orthogonal (μ : GlobalLinkField)
    (hμ : globallyCoClosed μ) (k : Torus4) :
    ∑ i : Fin 4, (fourier (-1) (torus4Coord k i) - 1) *
        globalLinkFourierComponent μ i k = 0 := by
  rw [← boundaryFourier_linkField]
  rw [hμ]
  simp

def fourierPairCurlEnergy (a u : Fin 4 → ℂ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    if i < j then Complex.normSq (a j * u i - a i * u j) else 0

def fourierHodgeInner (a u : Fin 4 → ℂ) : ℂ := ∑ i : Fin 4, conj (a i) * u i

def fourierHodgePair (u m : Fin 4 → ℂ) : ℂ := ∑ i : Fin 4, u i * conj (m i)

def fourierHodgeNormSq (u : Fin 4 → ℂ) : ℝ := ∑ i : Fin 4, Complex.normSq (u i)

def fourierHodgeResidual (a u : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun i => (↑(fourierHodgeNormSq a) : ℂ) * u i - a i * fourierHodgeInner a u

theorem fourierPairCurlEnergy_identity (a u : Fin 4 → ℂ) :
    fourierPairCurlEnergy a u = fourierHodgeNormSq a * fourierHodgeNormSq u - Complex.normSq (fourierHodgeInner a u) := by
  unfold fourierPairCurlEnergy fourierHodgeNormSq fourierHodgeInner
  simp only [Fin.sum_univ_succ]
  simp
  simp only [Complex.normSq_apply, Complex.conj_re, Complex.conj_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im]
  ring_nf

theorem hodgeResidual_pair (a m u : Fin 4 → ℂ)
    (horth : fourierHodgeInner a m = 0) :
    fourierHodgePair (fourierHodgeResidual a u) m = (↑(fourierHodgeNormSq a) : ℂ) * fourierHodgePair u m := by
  let lam := fourierHodgeNormSq a
  let g := fourierHodgeInner a u
  have horth' : ∑ i : Fin 4, a i * conj (m i) = 0 := by
    simpa [fourierHodgeInner, map_sum, map_mul, Complex.conj_conj, mul_comm] using
      congrArg conj horth
  unfold fourierHodgeResidual
  change (∑ i : Fin 4, ((↑lam : ℂ) * u i - a i * g) * conj (m i)) =
    (↑lam : ℂ) * fourierHodgePair u m
  calc
    (∑ i : Fin 4, ((↑lam : ℂ) * u i - a i * g) * conj (m i)) =
        ∑ i : Fin 4, ((↑lam : ℂ) * (u i * conj (m i)) -
          (a i * conj (m i)) * g) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (↑lam : ℂ) * (∑ i : Fin 4, u i * conj (m i)) -
        (∑ i : Fin 4, a i * conj (m i)) * g := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    _ = (↑lam : ℂ) * fourierHodgePair u m := by simp [horth', fourierHodgePair]

theorem hodgeResidual_norm (a u : Fin 4 → ℂ) :
    fourierHodgeNormSq (fourierHodgeResidual a u) = fourierHodgeNormSq a * fourierPairCurlEnergy a u := by
  let lam := fourierHodgeNormSq a
  let g := fourierHodgeInner a u
  have hcomplex :
      ∑ i : Fin 4, (↑lam : ℂ) * u i * conj (a i * g) =
        (↑lam : ℂ) * (g * conj g) := by
    calc
      _ = ∑ i : Fin 4, (↑lam : ℂ) * ((conj (a i) * u i) * conj g) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_mul]
        ring
      _ = (↑lam : ℂ) * ∑ i : Fin 4, ((conj (a i) * u i) * conj g) := by
        rw [Finset.mul_sum]
      _ = (↑lam : ℂ) * ((∑ i : Fin 4, conj (a i) * u i) * conj g) := by
        rw [Finset.sum_mul]
      _ = (↑lam : ℂ) * (g * conj g) := by rfl
  have hcross : ∑ i : Fin 4,
      Complex.re ((↑lam : ℂ) * u i * conj (a i * g)) = lam * Complex.normSq g := by
    calc
      _ = Complex.re (∑ i : Fin 4, (↑lam : ℂ) * u i * conj (a i * g)) := by
        rw [Complex.re_sum]
      _ = lam * Complex.normSq g := by
        rw [hcomplex]
        simp [Complex.mul_conj]
  have hsumexpand :
      (∑ i : Fin 4, (Complex.normSq ((↑lam : ℂ) * u i) +
        Complex.normSq (a i * g) -
        2 * Complex.re ((↑lam : ℂ) * u i * conj (a i * g)))) =
      (∑ i : Fin 4, Complex.normSq ((↑lam : ℂ) * u i)) +
        (∑ i : Fin 4, Complex.normSq (a i * g)) -
        2 * (∑ i : Fin 4, Complex.re ((↑lam : ℂ) * u i * conj (a i * g))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  calc
    fourierHodgeNormSq (fourierHodgeResidual a u) =
        ∑ i : Fin 4, (Complex.normSq ((↑lam : ℂ) * u i) +
          Complex.normSq (a i * g) -
          2 * Complex.re ((↑lam : ℂ) * u i * conj (a i * g))) := by
      unfold fourierHodgeNormSq fourierHodgeResidual
      apply Finset.sum_congr rfl
      intro i hi
      rw [Complex.normSq_sub]
    _ = lam ^ 2 * fourierHodgeNormSq u + lam * Complex.normSq g - 2 * (lam * Complex.normSq g) := by
      rw [hsumexpand]
      simp_rw [Complex.normSq_mul, Complex.normSq_ofReal]
      rw [← Finset.mul_sum, ← Finset.sum_mul, hcross]
      simp [lam, fourierHodgeNormSq, mul_comm, mul_assoc, pow_two]
    _ = lam * fourierPairCurlEnergy a u := by
      rw [fourierPairCurlEnergy_identity]
      simp [lam, fourierHodgeNormSq, g]
      ring

theorem fourierPairCurlEnergy_upper (a m u : Fin 4 → ℂ)
    (horth : fourierHodgeInner a m = 0) (hpos : 0 < fourierHodgeNormSq a) :
    2 * (fourierHodgePair u m).re - fourierPairCurlEnergy a u ≤
      fourierHodgeNormSq m / fourierHodgeNormSq a := by
  let w := fourierHodgeResidual a u
  have hp := hodgeResidual_pair a m u horth
  have hn := hodgeResidual_norm a u
  have hsquare : 0 ≤ fourierHodgeNormSq (fun i => w i - m i) := by
    unfold fourierHodgeNormSq
    apply Finset.sum_nonneg
    intro i hi
    exact Complex.normSq_nonneg _
  have hcomplete :
      2 * (fourierHodgePair w m).re - fourierHodgeNormSq w ≤ fourierHodgeNormSq m := by
    have hexpand : fourierHodgeNormSq (fun i => w i - m i) =
        fourierHodgeNormSq w + fourierHodgeNormSq m - 2 * (fourierHodgePair w m).re := by
      unfold fourierHodgeNormSq fourierHodgePair
      simp_rw [Complex.normSq_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Complex.re_sum]
    rw [hexpand] at hsquare
    linarith
  have hpairRe : (fourierHodgePair w m).re =
      fourierHodgeNormSq a * (fourierHodgePair u m).re := by
    rw [hp]
    simp
  have hineq : fourierHodgeNormSq a *
      (2 * (fourierHodgePair u m).re - fourierPairCurlEnergy a u) ≤ fourierHodgeNormSq m := by
    calc
      _ = 2 * (fourierHodgePair w m).re - fourierHodgeNormSq w := by rw [hpairRe, hn]; ring
      _ ≤ fourierHodgeNormSq m := hcomplete
  apply (le_div_iff₀ hpos).2
  simpa [mul_comm] using hineq


noncomputable def fourierFourierCurlEnergy (φ : GlobalLinkField) (k : Torus4) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    if i < j then Complex.normSq
      (latticeChainFourierComponent
        (globalCoboundary (φ : RealLatticeChain 4)) {i, j} k) else 0

/-- The pointwise finite-dimensional Hodge estimate at every nonzero
frequency. The zero frequency is omitted from the inequality; it is a Haar
null point in the integral representation. -/
theorem globallyCoClosed_fourier_pointwise_bound
    (μ φ : GlobalLinkField) (hμ : globallyCoClosed μ) (k : Torus4)
    (hpos : 0 < fourierLaplacianSymbol k) :
    2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)).re -
      fourierFourierCurlEnergy φ k ≤ fourierGreenDensity μ k := by
  let a : Fin 4 → ℂ := fun i => fourier 1 (torus4Coord k i) - 1
  let u : Fin 4 → ℂ := fun i => globalLinkFourierComponent φ i k
  let m : Fin 4 → ℂ := fun i => globalLinkFourierComponent μ i k
  have hsymbol : fourierHodgeNormSq a = fourierLaplacianSymbol k := by
    unfold fourierHodgeNormSq fourierLaplacianSymbol a
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.normSq_eq_norm_sq]
    have hneg : fourier 1 (torus4Coord k i) - 1 =
        -((1 : ℂ) - fourier 1 (torus4Coord k i)) := by ring
    rw [hneg, norm_neg]
  have horth : fourierHodgeInner a m = 0 := by
    have hcoord (i : Fin 4) :
        conj (fourier 1 (torus4Coord k i) - 1) =
          fourier (-1) (torus4Coord k i) - 1 := by
      calc
        conj (fourier 1 (torus4Coord k i) - 1) =
            conj (fourier 1 (torus4Coord k i)) - 1 := by rw [map_sub, map_one]
        _ = fourier (-1) (torus4Coord k i) - 1 := by
          rw [← fourier_neg]
    have hterm (i : Fin 4) : conj (a i) =
        fourier (-1) (torus4Coord k i) - 1 := by
      dsimp [a]
      exact hcoord i
    unfold fourierHodgeInner
    calc
      (∑ i : Fin 4, conj (a i) * m i) =
          ∑ i : Fin 4, (fourier (-1) (torus4Coord k i) - 1) *
            globalLinkFourierComponent μ i k := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hterm i]
      _ = 0 := globallyCoClosed_fourier_orthogonal μ hμ k
  have hpositive : 0 < fourierHodgeNormSq a := by rw [hsymbol]; exact hpos
  have hcurl : fourierFourierCurlEnergy φ k = fourierPairCurlEnergy a u := by
    unfold fourierFourierCurlEnergy fourierPairCurlEnergy
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij]
      rw [coboundaryFourierComponent_pair φ i j hij k]
      have hneg : -((fourier 1 (torus4Coord k j) - 1) *
            globalLinkFourierComponent φ i k) +
          ((fourier 1 (torus4Coord k i) - 1) *
            globalLinkFourierComponent φ j k) =
          -(a j * u i - a i * u j) := by
        dsimp [a, u]
        ring
      rw [hneg, Complex.normSq_neg]
    · simp [hij]
  have hgreen : fourierHodgeNormSq m / fourierHodgeNormSq a =
      fourierGreenDensity μ k := by
    rw [hsymbol]
    unfold fourierGreenDensity
    rw [← Finset.sum_div]
    apply congrArg (fun x : ℝ => x / fourierLaplacianSymbol k)
    unfold fourierHodgeNormSq
    apply Finset.sum_congr rfl
    intro i hi
    exact Complex.normSq_eq_norm_sq _
  have hbound := fourierPairCurlEnergy_upper a m u horth hpositive
  have hpair : (∑ i : Fin 4, globalLinkFourierComponent φ i k *
      conj (globalLinkFourierComponent μ i k)).re = (fourierHodgePair u m).re := by
    rfl
  rw [hcurl, ← hgreen]
  rw [hpair]
  exact hbound

/-- A coboundary of a link field has no Fourier component on any cell-axis
set other than a two-element plaquette-axis set. -/
theorem coboundaryFourierComponent_zero_of_axes_card_ne_two
    (φ : GlobalLinkField) (axes : Finset (Fin 4)) (k : Torus4)
    (hcard : axes.card ≠ 2) :
    latticeChainFourierComponent
      (globalCoboundary (φ : RealLatticeChain 4)) axes k = 0 := by
  classical
  rw [latticeChainFourierComponent_eq_functional]
  let L : RealLatticeChain 4 →ₗ[ℝ] ℂ :=
    (latticeChainFourierFunctional axes k).comp globalCoboundary
  change L (φ : RealLatticeChain 4) = 0
  rw [linearMap_apply_sum_support L φ.1]
  apply Finset.sum_eq_zero
  intro c hc
  have hdegree := φ.2 c hc
  obtain ⟨a, haxis, _⟩ := existsUnique_latticeLinkAxis_of_degree_one c hdegree
  have hsingle : L (Finsupp.single c (1 : ℝ)) = 0 := by
    change latticeChainFourierFunctional axes k
      (globalCoboundary (Finsupp.single c (1 : ℝ))) = 0
    unfold globalCoboundary
    rw [sourceRealLatticeCoboundary_single_eq_sum_fourier, map_sum]
    apply Finset.sum_eq_zero
    intro l hl
    cases hcl : c l with
    | inr t => simp [fourierLatticeCoboundaryTerm, hcl]
    | inl t =>
        have hli : l ≠ a := by
          intro h
          subst l
          have := haxis.1
          simp [latticeIsEdge, hcl] at this
        have haxesL : Fourier.latticeCellAxes
            (latticeEdgeCell c l (t - 1)) = {a, l} :=
          edgeCellAxes_link c a l (t - 1) haxis
        have haxesU : Fourier.latticeCellAxes
            (latticeEdgeCell c l t) = {a, l} :=
          edgeCellAxes_link c a l t haxis
        have hpairCard : ({a, l} : Finset (Fin 4)).card = 2 :=
          Finset.card_pair hli.symm
        have hpairNe : ({a, l} : Finset (Fin 4)) ≠ axes := by
          intro heq
          apply hcard
          exact (congrArg Finset.card heq).symm.trans hpairCard
        rw [fourierLatticeCoboundaryTerm, hcl, map_smul, map_sub]
        simp [chainFourierFunctional_single, haxesL, haxesU, hpairNe]
  have hLsingle : L (Finsupp.single c (1 : ℝ)) = 0 := hsingle
  have hscalar : (φ.1 c : ℂ) * L (Finsupp.single c (1 : ℝ)) = 0 := by
    rw [hLsingle]
    simp
  simpa using hscalar


end FroehlichSpencer.FS82.Infinite.FourierVariational
