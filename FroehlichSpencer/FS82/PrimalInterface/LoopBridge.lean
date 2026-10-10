/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Surface.RectangularLoop
public import FroehlichSpencer.FS82.Surface.CentredCube
public import FroehlichSpencer.FS82.PrimalInterface.LatticeBridge
public import FroehlichSpencer.FS82.Wilson.PerimeterRoot

/-!
# the literal rectangular loop and the internal sheet of the centred cube

Hence the loop is the zero extension of the boundary of the internal sheet:
it lies in the cube, on links, and its coefficients are those of the internal boundary.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.PrimalInterface

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite

/-! ### The sheet in the lattice -/

/-- The lattice plaquette `[j, j+1] × [k, k+1] × {0} × {0}`. -/
def rectCell (j k : ℤ) : LatticeCell 4 := ![Sum.inr j, Sum.inr k, Sum.inl 0, Sum.inl 0]

theorem rectCell_injective {j k j' k' : ℤ} (h : rectCell j k = rectCell j' k') :
    j = j' ∧ k = k' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  exact ⟨by simpa [rectCell] using h0, by simpa [rectCell] using h1⟩

/-- The sheet of the `L × T` rectangle as a lattice chain. -/
noncomputable def rectangleSheet (L T : ℕ) : LatticeChain 4 :=
  ∑ j ∈ Finset.range L, ∑ k ∈ Finset.range T, latticeBasis (rectCell j k)

theorem rectangleSheet_apply_of (L T : ℕ) {y : LatticeCell 4}
    (h : ∃ j : ℕ, j < L ∧ ∃ k : ℕ, k < T ∧ rectCell j k = y) : rectangleSheet L T y = 1 := by
  classical
  obtain ⟨j₀, hj₀, k₀, hk₀, rfl⟩ := h
  unfold rectangleSheet latticeBasis
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single j₀]
  · rw [Finsupp.finsetSum_apply, Finset.sum_eq_single k₀]
    · exact Finsupp.single_eq_same
    · intro k _ hk
      have hne : rectCell (j₀ : ℤ) (k : ℤ) ≠ rectCell (j₀ : ℤ) (k₀ : ℤ) := fun h =>
        hk (by exact_mod_cast (rectCell_injective h).2)
      simp [hne]
    · intro h
      exact absurd (Finset.mem_range.mpr hk₀) h
  · intro j _ hj
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hne : rectCell (j : ℤ) (k : ℤ) ≠ rectCell (j₀ : ℤ) (k₀ : ℤ) := fun h =>
      hj (by exact_mod_cast (rectCell_injective h).1)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_range.mpr hj₀) h

theorem rectangleSheet_apply_of_not (L T : ℕ) {y : LatticeCell 4}
    (h : ¬∃ j : ℕ, j < L ∧ ∃ k : ℕ, k < T ∧ rectCell j k = y) : rectangleSheet L T y = 0 := by
  classical
  unfold rectangleSheet latticeBasis
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hne : rectCell (j : ℤ) (k : ℤ) ≠ y := fun h' =>
    h ⟨j, Finset.mem_range.mp hj, k, Finset.mem_range.mp hk, h'⟩
  simp [hne]

/-! ### The boundary of the sheet is the four-sided loop -/

theorem latticeBoundaryBasis_rectCell (j k : ℤ) :
    latticeBoundaryBasis (rectCell j k) =
      (latticeBasis ![Sum.inl (j + 1), Sum.inr k, Sum.inl 0, Sum.inl 0] -
          latticeBasis ![Sum.inl j, Sum.inr k, Sum.inl 0, Sum.inl 0]) -
        (latticeBasis ![Sum.inr j, Sum.inl (k + 1), Sum.inl 0, Sum.inl 0] -
          latticeBasis ![Sum.inr j, Sum.inl k, Sum.inl 0, Sum.inl 0]) := by
  classical
  have hr0 : latticeRankBefore (rectCell j k) 0 = 0 := by
    simp [latticeRankBefore]
  have hr1 : latticeRankBefore (rectCell j k) 1 = 1 := by
    unfold latticeRankBefore
    have hset : (Finset.univ.filter fun i : Fin 4 => i < 1 ∧ latticeIsEdge (rectCell j k i)) =
        {0} := by
      ext i
      fin_cases i <;> simp [latticeIsEdge, rectCell]
    rw [hset]
    rfl
  have hU0 : latticeUpperFace (rectCell j k) 0 j =
      ![Sum.inl (j + 1), Sum.inr k, Sum.inl 0, Sum.inl 0] := by
    funext i
    fin_cases i <;> rfl
  have hL0 : latticeLowerFace (rectCell j k) 0 j =
      ![Sum.inl j, Sum.inr k, Sum.inl 0, Sum.inl 0] := by
    funext i
    fin_cases i <;> rfl
  have hU1 : latticeUpperFace (rectCell j k) 1 k =
      ![Sum.inr j, Sum.inl (k + 1), Sum.inl 0, Sum.inl 0] := by
    funext i
    fin_cases i <;> rfl
  have hL1 : latticeLowerFace (rectCell j k) 1 k =
      ![Sum.inr j, Sum.inl k, Sum.inl 0, Sum.inl 0] := by
    funext i
    fin_cases i <;> rfl
  have h : latticeBoundaryBasis (rectCell j k) =
      ((-1 : ℤ) ^ latticeRankBefore (rectCell j k) 0) •
          (latticeBasis (latticeUpperFace (rectCell j k) 0 j) -
            latticeBasis (latticeLowerFace (rectCell j k) 0 j)) +
        ((-1 : ℤ) ^ latticeRankBefore (rectCell j k) 1) •
          (latticeBasis (latticeUpperFace (rectCell j k) 1 k) -
            latticeBasis (latticeLowerFace (rectCell j k) 1 k)) + 0 + 0 := by
    unfold latticeBoundaryBasis
    rw [Fin.sum_univ_four]
    rfl
  rw [h, hr0, hr1, hU0, hL0, hU1, hL1]
  simp only [pow_zero, one_smul, pow_one, neg_smul, add_zero]
  rw [sub_eq_add_neg _ (_ - _)]

theorem latticeBoundary_rectangleSheet (L T : ℕ) :
    latticeBoundary (rectangleSheet L T) = Surface.rectangularLoop L T := by
  have hA : ∀ k : ℕ, ∑ j ∈ Finset.range L,
      (latticeBasis ![Sum.inl ((j : ℤ) + 1), Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0] -
        latticeBasis ![Sum.inl (j : ℤ), Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0]) =
      latticeBasis ![Sum.inl (L : ℤ), Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0] -
        latticeBasis ![Sum.inl 0, Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0] := by
    intro k
    have h := Finset.sum_range_sub
      (fun j : ℕ => latticeBasis (d := 4) ![Sum.inl (j : ℤ), Sum.inr (k : ℤ), Sum.inl 0, Sum.inl 0]) L
    simpa using h
  have hB : ∀ j : ℕ, ∑ k ∈ Finset.range T,
      (latticeBasis ![Sum.inr (j : ℤ), Sum.inl ((k : ℤ) + 1), Sum.inl 0, Sum.inl 0] -
        latticeBasis ![Sum.inr (j : ℤ), Sum.inl (k : ℤ), Sum.inl 0, Sum.inl 0]) =
      latticeBasis ![Sum.inr (j : ℤ), Sum.inl (T : ℤ), Sum.inl 0, Sum.inl 0] -
        latticeBasis ![Sum.inr (j : ℤ), Sum.inl 0, Sum.inl 0, Sum.inl 0] := by
    intro j
    have h := Finset.sum_range_sub
      (fun k : ℕ => latticeBasis (d := 4) ![Sum.inr (j : ℤ), Sum.inl (k : ℤ), Sum.inl 0, Sum.inl 0]) T
    simpa using h
  unfold rectangleSheet
  simp only [map_sum, latticeBoundary_basis, latticeBoundaryBasis_rectCell]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_sub_distrib _ _, Finset.sum_sub_distrib,
    Finset.sum_comm, Finset.sum_congr rfl fun k _ => hA k, Finset.sum_congr rfl fun j _ => hB j]
  unfold Surface.rectangularLoop latticeBasis
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp only [neg_sub]
  exact add_comm _ _

/-! ### The internal sheet -/

variable {L T N : ℕ}

/-- The cells of the internal sheet, in the coordinates of the primal box. -/
def SheetPrimalCell (L T N : ℕ) (c : Cell 4 (cube N)) : Prop :=
  (∃ e, c 0 = Sum.inr e ∧ N ≤ e.val ∧ e.val < N + L) ∧
  (∃ e, c 1 = Sum.inr e ∧ N ≤ e.val ∧ e.val < N + T) ∧
  (∃ v, c 2 = Sum.inl v ∧ v.val = N) ∧ (∃ v, c 3 = Sum.inl v ∧ v.val = N)

theorem star_inl_iff {B : Box 4} (c : Cell 4 B) (i : Fin 4) (p : ℕ → Prop) :
    (∃ v, primalDualCellEquiv c i = Sum.inl v ∧ p v.val) ↔ ∃ e, c i = Sum.inr e ∧ p e.val := by
  cases h : c i with
  | inl v => simp [primalDualCellEquiv, h]
  | inr e =>
      constructor
      · rintro ⟨v, hv, hp⟩
        have hv' : (Sum.inl ⟨e.val, e.isLt⟩ : DualCoord B i) = Sum.inl v := by
          simpa [primalDualCellEquiv, h] using hv
        cases Sum.inl.inj hv'
        exact ⟨e, rfl, hp⟩
      · rintro ⟨e', he', hp⟩
        cases Sum.inr.inj he'
        exact ⟨⟨e.val, e.isLt⟩, by simp [primalDualCellEquiv, h], hp⟩

theorem star_inr_iff {B : Box 4} (c : Cell 4 B) (i : Fin 4) (p : ℕ → Prop) :
    (∃ e, primalDualCellEquiv c i = Sum.inr e ∧ p e.val) ↔ ∃ v, c i = Sum.inl v ∧ p v.val := by
  cases h : c i with
  | inr e => simp [primalDualCellEquiv, h]
  | inl v =>
      constructor
      · rintro ⟨e, he, hp⟩
        have he' : (Sum.inr ⟨v.val, v.isLt⟩ : DualCoord B i) = Sum.inr e := by
          simpa [primalDualCellEquiv, h] using he
        cases Sum.inr.inj he'
        exact ⟨v, rfl, hp⟩
      · rintro ⟨v', hv', hp⟩
        cases Sum.inl.inj hv'
        exact ⟨⟨v.val, v.isLt⟩, by simp [primalDualCellEquiv, h], hp⟩

theorem cubeSheetCell_star_iff (c : Cell 4 (cube N))
    (h : dualCellDegree (primalDualCellEquiv c) = 2) :
    Wilson.cubeSheetCell (L := L) (T := T) (N := N) ⟨primalDualCellEquiv c, h⟩ ↔
      SheetPrimalCell L T N c :=
  and_congr (star_inl_iff c 0 fun n => N ≤ n ∧ n < N + L)
    (and_congr (star_inl_iff c 1 fun n => N ≤ n ∧ n < N + T)
      (and_congr (star_inr_iff c 2 fun n => n = N) (star_inr_iff c 3 fun n => n = N)))

theorem star_degree_of_sheetPrimalCell {c : Cell 4 (cube N)} (h : SheetPrimalCell L T N c) :
    dualCellDegree (primalDualCellEquiv c) = 2 := by
  obtain ⟨⟨e0, h0, -⟩, ⟨e1, h1, -⟩, ⟨v2, h2, -⟩, ⟨v3, h3, -⟩⟩ := h
  have e0' : primalDualCellEquiv c 0 = Sum.inl ⟨e0.val, e0.isLt⟩ := by
    simp [primalDualCellEquiv, h0]
  have e1' : primalDualCellEquiv c 1 = Sum.inl ⟨e1.val, e1.isLt⟩ := by
    simp [primalDualCellEquiv, h1]
  have e2' : primalDualCellEquiv c 2 = Sum.inr ⟨v2.val, v2.isLt⟩ := by
    simp [primalDualCellEquiv, h2]
  have e3' : primalDualCellEquiv c 3 = Sum.inr ⟨v3.val, v3.isLt⟩ := by
    simp [primalDualCellEquiv, h3]
  unfold dualCellDegree
  rw [show dualCellAxes (primalDualCellEquiv c) = {2, 3} from by
    ext i
    simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    match i with
    | 0 => simp [e0']
    | 1 => simp [e1']
    | 2 => simp [e2']
    | 3 => simp [e3']]
  rfl

theorem cubePrimalSheet_apply (c : Cell 4 (cube N)) :
    Wilson.cubePrimalSheet L T N c =
      Wilson.sourceIntegerDualTwoChain (Wilson.sourceIntegerCubeSheet L T N)
        (primalDualCellEquiv c) := by
  simp [Wilson.cubePrimalSheet, Gaussian.integerStarMapInverse, Finsupp.equivMapDomain_apply]

theorem cubePrimalSheet_apply_of {c : Cell 4 (cube N)} (h : SheetPrimalCell L T N c) :
    Wilson.cubePrimalSheet L T N c = 1 := by
  classical
  have hdeg := star_degree_of_sheetPrimalCell h
  rw [cubePrimalSheet_apply]
  change Finsupp.embDomain Gaussian.sourceDualTwoEmbedding (Wilson.sourceIntegerCubeSheet L T N)
    (Gaussian.sourceDualTwoEmbedding ⟨primalDualCellEquiv c, hdeg⟩) = 1
  rw [Finsupp.embDomain_apply_self]
  simp [Wilson.sourceIntegerCubeSheet, (cubeSheetCell_star_iff c hdeg).mpr h]

theorem cubePrimalSheet_apply_of_not {c : Cell 4 (cube N)} (h : ¬SheetPrimalCell L T N c) :
    Wilson.cubePrimalSheet L T N c = 0 := by
  classical
  rw [cubePrimalSheet_apply]
  by_cases hdeg : dualCellDegree (primalDualCellEquiv c) = 2
  · change Finsupp.embDomain Gaussian.sourceDualTwoEmbedding (Wilson.sourceIntegerCubeSheet L T N)
      (Gaussian.sourceDualTwoEmbedding ⟨primalDualCellEquiv c, hdeg⟩) = 0
    rw [Finsupp.embDomain_apply_self]
    simp [Wilson.sourceIntegerCubeSheet, mt (cubeSheetCell_star_iff c hdeg).mp h]
  · apply Finsupp.embDomain_of_notMem_range
    rintro ⟨f, hf⟩
    exact hdeg (hf ▸ f.2)

/-- The cell of the cube at the lattice plaquette `[j, j+1] × [k, k+1] × {0}²`. -/
def cubeRectCell (N j k : ℕ) (hj : j < N) (hk : k < N) : Cell 4 (cube N) :=
  (![Sum.inr ⟨N + j, by omega⟩, Sum.inr ⟨N + k, by omega⟩, Sum.inl ⟨N, by omega⟩,
      Sum.inl ⟨N, by omega⟩] : Fin 4 → Sum (Fin (2 * N + 1)) (Fin (2 * N)))

theorem cubeRectCell_zero (N j k : ℕ) (hj : j < N) (hk : k < N) :
    cubeRectCell N j k hj hk 0 = Sum.inr ⟨N + j, show N + j < 2 * N by omega⟩ := rfl

theorem cubeRectCell_one (N j k : ℕ) (hj : j < N) (hk : k < N) :
    cubeRectCell N j k hj hk 1 = Sum.inr ⟨N + k, show N + k < 2 * N by omega⟩ := rfl

theorem cubeRectCell_two (N j k : ℕ) (hj : j < N) (hk : k < N) :
    cubeRectCell N j k hj hk 2 = Sum.inl ⟨N, show N < 2 * N + 1 by omega⟩ := rfl

theorem cubeRectCell_three (N j k : ℕ) (hj : j < N) (hk : k < N) :
    cubeRectCell N j k hj hk 3 = Sum.inl ⟨N, show N < 2 * N + 1 by omega⟩ := rfl

theorem boxCellEmbedding_cubeRectCell (N j k : ℕ) (hj : j < N) (hk : k < N) :
    boxCellEmbedding (cubeOrigin N) (cubeRectCell N j k hj hk) = rectCell j k := by
  funext i
  fin_cases i <;> simp [boxCellEmbedding, embedCoord, cubeOrigin, cubeRectCell, rectCell]

theorem sheetPrimalCell_cubeRectCell {j k : ℕ} (hj : j < L) (hk : k < T) (hL : L ≤ N)
    (hT : T ≤ N) :
    SheetPrimalCell L T N (cubeRectCell N j k (lt_of_lt_of_le hj hL) (lt_of_lt_of_le hk hT)) :=
  ⟨⟨_, cubeRectCell_zero N j k _ _, Nat.le_add_right N j, Nat.add_lt_add_left hj N⟩,
    ⟨_, cubeRectCell_one N j k _ _, Nat.le_add_right N k, Nat.add_lt_add_left hk N⟩,
    ⟨_, cubeRectCell_two N j k _ _, rfl⟩, ⟨_, cubeRectCell_three N j k _ _, rfl⟩⟩

theorem sheetPrimalCell_iff (hL : L ≤ N) (hT : T ≤ N) (c : Cell 4 (cube N)) :
    SheetPrimalCell L T N c ↔
      ∃ j : ℕ, j < L ∧ ∃ k : ℕ, k < T ∧ rectCell j k = boxCellEmbedding (cubeOrigin N) c := by
  constructor
  · rintro ⟨⟨e0, h0, hN0, hL0⟩, ⟨e1, h1, hN1, hT1⟩, ⟨v2, h2, hv2⟩, ⟨v3, h3, hv3⟩⟩
    have hj : e0.val - N < L := by omega
    have hk : e1.val - N < T := by omega
    refine ⟨e0.val - N, hj, e1.val - N, hk, ?_⟩
    have hc : c = cubeRectCell N (e0.val - N) (e1.val - N) (lt_of_lt_of_le hj hL)
        (lt_of_lt_of_le hk hT) := by
      funext i
      match i with
      | 0 =>
          rw [h0, cubeRectCell_zero]
          exact congrArg Sum.inr (Fin.ext (show e0.val = N + (e0.val - N) by omega))
      | 1 =>
          rw [h1, cubeRectCell_one]
          exact congrArg Sum.inr (Fin.ext (show e1.val = N + (e1.val - N) by omega))
      | 2 =>
          rw [h2, cubeRectCell_two]
          exact congrArg Sum.inl (Fin.ext hv2)
      | 3 =>
          rw [h3, cubeRectCell_three]
          exact congrArg Sum.inl (Fin.ext hv3)
    rw [hc, boxCellEmbedding_cubeRectCell]
  · rintro ⟨j, hj, k, hk, h⟩
    have hc : c = cubeRectCell N j k (lt_of_lt_of_le hj hL) (lt_of_lt_of_le hk hT) := by
      apply (boxCellEmbedding (B := cube N) (cubeOrigin N)).injective
      rw [← h, boxCellEmbedding_cubeRectCell]
    rw [hc]
    exact sheetPrimalCell_cubeRectCell hj hk hL hT

/-- For `L, T ≤ N` the internal sheet of the cube is the lattice sheet. -/
theorem zeroExtension_cubePrimalSheet (hL : L ≤ N) (hT : T ≤ N) :
    zeroExtension (cubeOrigin N) (Wilson.cubePrimalSheet L T N) = rectangleSheet L T := by
  classical
  ext y
  by_cases hy : y ∈ Set.range (boxCellEmbedding (B := cube N) (cubeOrigin N))
  · obtain ⟨c, rfl⟩ := hy
    rw [zeroExtension_apply_embedding]
    by_cases hP : SheetPrimalCell L T N c
    · rw [cubePrimalSheet_apply_of hP,
        rectangleSheet_apply_of L T ((sheetPrimalCell_iff hL hT c).mp hP)]
    · rw [cubePrimalSheet_apply_of_not hP,
        rectangleSheet_apply_of_not L T (mt (sheetPrimalCell_iff hL hT c).mpr hP)]
  · rw [zeroExtension_vanishes_outside _ _ _ hy, rectangleSheet_apply_of_not]
    rintro ⟨j, hj, k, hk, rfl⟩
    exact hy ⟨cubeRectCell N j k (lt_of_lt_of_le hj hL) (lt_of_lt_of_le hk hT),
      boxCellEmbedding_cubeRectCell N j k _ _⟩

/-- **The loop is the zero extension of the boundary of the internal sheet.** -/
theorem rectangularLoop_eq_zeroExtension (hL : L ≤ N) (hT : T ≤ N) :
    Surface.rectangularLoop L T =
      zeroExtension (cubeOrigin N) (boundary (Wilson.cubePrimalSheet L T N)) := by
  rw [zeroExtension_boundary, zeroExtension_cubePrimalSheet hL hT, latticeBoundary_rectangleSheet]

theorem rectangularLoop_apply_embedding (hL : L ≤ N) (hT : T ≤ N) (c : Cell 4 (cube N)) :
    Surface.rectangularLoop L T (boxCellEmbedding (cubeOrigin N) c) =
      boundary (Wilson.cubePrimalSheet L T N) c := by
  rw [rectangularLoop_eq_zeroExtension hL hT, zeroExtension_apply_embedding]

/-- Boundary lowers the homogeneous cubical degree by one (as `XY.xyIntegerBoundary_homogeneousSupport`). -/
theorem boundary_homogeneousSupport {B : Box 4} (q : Chain 4 B) (k : ℕ) (hk : 0 < k)
    (hq : homogeneousSupport q k) : homogeneousSupport (boundary q) (k - 1) := by
  have hqR : realHomogeneousSupport (castIntegerChain q) k := by
    intro c hc
    exact hq c (Finsupp.support_mapRange hc)
  have hbdR := Gaussian.realBoundary_homogeneousSupport (castIntegerChain q) k hk hqR
  have hcast : castIntegerChain (boundary q) = realBoundary (castIntegerChain q) := by
    simpa [realBoundary] using (realifyLinearMap_cast boundary q).symm
  intro c hc
  have hcR : c ∈ (realBoundary (castIntegerChain q)).support := by
    rw [← hcast]
    rw [Finsupp.mem_support_iff] at hc ⊢
    intro hz
    apply hc
    have hzero : ((boundary q c : ℤ) : ℝ) = 0 := by
      simpa [castIntegerChain, Finsupp.mapRange_apply] using hz
    exact_mod_cast hzero
  exact hbdR c hcR

/-- **Gate.** For `L, T ≤ N` every cell of the loop is a link of the centred cube. -/
theorem rectangularLoop_subset_centredCube (L T N : ℕ) (hN : 0 < N) (hL : L ≤ N) (hT : T ≤ N)
    (c : Surface.LatticeCell) (hc : c ∈ (Surface.rectangularLoop L T).support) :
    ∃ ℓ : Surface.PrimalLinks (Surface.centredCube N hN),
      Surface.primalCellEmbedding (Surface.centredCube N hN) ℓ.1 = c := by
  rw [rectangularLoop_eq_zeroExtension hL hT, zeroExtension_support] at hc
  obtain ⟨c', hc', rfl⟩ := Finset.mem_map.mp hc
  have hdeg : cellDegree c' = 1 :=
    boundary_homogeneousSupport (Wilson.cubePrimalSheet L T N) 2 (by norm_num)
      (Wilson.cubePrimalSheet_homogeneousSupport L T N) c' hc'
  exact ⟨⟨c', (primalCellDegree_eq (Surface.centredCube N hN) c').trans hdeg⟩,
    primalCellEmbedding_eq (Surface.centredCube N hN) c'⟩

end FroehlichSpencer.FS82.PrimalInterface

end
