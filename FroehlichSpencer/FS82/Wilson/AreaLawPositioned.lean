/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawFinite
public import FroehlichSpencer.FS82.Wilson.PerimeterRoot

/-!
# Positioned finite-volume Wilson rectangles

The low-coupling cluster estimate is extended to a coordinate rectangle whose
lower corner is specified in the cell indices of the box. The centered-cube
family used by the perimeter theorem is the specialization at index `N` on
all four axes.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Infinite
open Classical

/-- The vertex at the requested lower corner of a positioned rectangle. -/
@[expose] def positionedRectangleBaseCell {B : Box 4}
    (o : Fin 4 → ℕ) (ho : ∀ i, o i ≤ B i) : Cell 4 B := fun i =>
  Sum.inl ⟨o i, Nat.lt_succ_of_le (ho i)⟩

/-- A `0–1` plaquette based at offset `(i,j)` from the requested lower corner. -/
@[expose] def positionedRectanglePlaquette {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) : Cell 4 B :=
  edgeCell
    (edgeCell (positionedRectangleBaseCell o ho) 0
      ⟨o 0 + i.val, by have := Nat.le_add_right (o 0) L; omega⟩)
    1 ⟨o 1 + j.val, by have := Nat.le_add_right (o 1) T; omega⟩

/-- The oriented sheet of the positioned rectangle. -/
@[expose] noncomputable def positionedRectangleSheet {B : Box 4}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k) (L T : ℕ)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) : Chain 4 B :=
  ∑ x : Fin L × Fin T,
    basisChain (positionedRectanglePlaquette o ho hL hT x.1 x.2)

/-- The loop bounding the positioned sheet. -/
@[expose] noncomputable def positionedRectangleLoop {B : Box 4}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k) (L T : ℕ)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) : Chain 4 B :=
  boundary (positionedRectangleSheet o ho L T hL hT)

theorem positionedRectanglePlaquette_axes {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) :
    cellAxes (positionedRectanglePlaquette o ho hL hT i j) = {0, 1} := by
  classical
  apply Finset.ext
  intro k
  simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  fin_cases k <;>
    simp [positionedRectanglePlaquette, positionedRectangleBaseCell,
      edgeCell, coordIsEdge]

@[simp] theorem positionedRectanglePlaquette_apply0 {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) :
    positionedRectanglePlaquette o ho hL hT i j 0 =
      Sum.inr ⟨o 0 + i.val, by have hi := i.isLt; omega⟩ := by
  simp [positionedRectanglePlaquette, edgeCell]

@[simp] theorem positionedRectanglePlaquette_apply1 {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) :
    positionedRectanglePlaquette o ho hL hT i j 1 =
      Sum.inr ⟨o 1 + j.val, by have hj := j.isLt; omega⟩ := by
  simp [positionedRectanglePlaquette, edgeCell]


theorem positionedRectanglePlaquette_injective {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) :
    Function.Injective (fun x : Fin L × Fin T =>
      positionedRectanglePlaquette o ho hL hT x.1 x.2) := by
  intro x y hxy
  change positionedRectanglePlaquette o ho hL hT x.1 x.2 =
    positionedRectanglePlaquette o ho hL hT y.1 y.2 at hxy
  apply Prod.ext
  · apply Fin.ext
    have h := congrFun hxy (0 : Fin 4)
    have hx : o 0 + x.1.val < B 0 := by have := x.1.isLt; omega
    have hy : o 0 + y.1.val < B 0 := by have := y.1.isLt; omega
    change Sum.inr (⟨o 0 + x.1.val, hx⟩ : Fin (B 0)) =
      Sum.inr (⟨o 0 + y.1.val, hy⟩ : Fin (B 0)) at h
    have hv := congrArg Fin.val (Sum.inr.inj h)
    exact Nat.add_left_cancel hv
  · apply Fin.ext
    have h := congrFun hxy (1 : Fin 4)
    have hx : o 1 + x.2.val < B 1 := by have := x.2.isLt; omega
    have hy : o 1 + y.2.val < B 1 := by have := y.2.isLt; omega
    change Sum.inr (⟨o 1 + x.2.val, hx⟩ : Fin (B 1)) =
      Sum.inr (⟨o 1 + y.2.val, hy⟩ : Fin (B 1)) at h
    have hv := congrArg Fin.val (Sum.inr.inj h)
    exact Nat.add_left_cancel hv

/-! ### The centered-cube specialization -/

def centeredRectangleOrigin (N : ℕ) : Fin 4 → ℕ := fun _ => N

theorem centeredRectangleOrigin_le (N : ℕ) :
    ∀ i, centeredRectangleOrigin N i ≤ (cube N) i := by
  intro i
  simp [centeredRectangleOrigin, cube]
  omega

theorem centeredRectangleFits {L T N : ℕ}
    (hN : max L T ≤ N) :
    centeredRectangleOrigin N 0 + L ≤ (cube N) 0 ∧
      centeredRectangleOrigin N 1 + T ≤ (cube N) 1 := by
  have hL : L ≤ N := le_trans (Nat.le_max_left _ _) hN
  have hT : T ≤ N := le_trans (Nat.le_max_right _ _) hN
  simp [centeredRectangleOrigin, cube]
  omega

theorem positionedRectangleSheet_homogeneousSupport {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) :
    homogeneousSupport (positionedRectangleSheet o ho L T hL hT) 2 := by
  classical
  intro c hc
  change c ∈ (∑ x : Fin L × Fin T,
    basisChain (positionedRectanglePlaquette o ho hL hT x.1 x.2)).support at hc
  have hsum := Finsupp.support_finsetSum hc
  rcases Finset.mem_biUnion.mp hsum with ⟨x, hx, hterm⟩
  have hne : basisChain (positionedRectanglePlaquette o ho hL hT x.1 x.2) c ≠ 0 :=
    Finsupp.mem_support_iff.mp hterm
  have hcell : c = positionedRectanglePlaquette o ho hL hT x.1 x.2 := by
    by_contra hnot
    simp [basisChain, hnot] at hne
  rw [hcell, cellDegree, positionedRectanglePlaquette_axes o ho hL hT x.1 x.2]
  simp

theorem areaTestPotential_pairing_positionedRectangleLoop {B : Box 4}
    {L T : ℕ} (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) :
    integerCellPairing areaTestPotential
      (positionedRectangleLoop o ho L T hL hT) = (L * T : ℕ) := by
  classical
  rw [positionedRectangleLoop, positionedRectangleSheet]
  rw [integerCellPairing_boundary_sum]
  have hterm (x : Fin L × Fin T) :
      integerCellPairing areaTestPotential
        (boundary (basisChain (positionedRectanglePlaquette o ho hL hT x.1 x.2))) = 1 := by
    let p : PrimalPlaquettes B := ⟨positionedRectanglePlaquette o ho hL hT x.1 x.2, by
      rw [cellDegree, positionedRectanglePlaquette_axes]
      simp⟩
    change areaTestPlaquetteCurl p = 1
    rw [areaTestPlaquetteCurl_eq_axes, positionedRectanglePlaquette_axes]
    simp
  simp_rw [hterm]
  simp

theorem areaTestPotential_pairing_boundary_eq_positionedSource
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    integerCellPairing areaTestPotential
      (boundary (plaquetteModeChain m)) =
    integerCellPairing areaTestPotential
      (boundary (positionedRectangleSheet o ho L T hL hT)) := by
  apply integerCellPairing_eq_of_degreeOne_coeff_eq
  · intro c hc
    simp [areaTestPotential, hc]
  · intro c hc
    let l : PrimalLinks B := ⟨c, hc⟩
    have hl := congrFun hsource l
    simpa [plaquetteModeDivergence, primalSheetLoopFrequency] using hl

theorem areaTestPotential_modeL1_lower_bound_positioned
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    (L * T : ℤ) ≤ ∑ p : PrimalPlaquettes B, |m p| := by
  classical
  have hpair := areaTestPotential_pairing_boundary_eq_positionedSource
    o ho hL hT m hsource
  rw [integerCellPairing_boundary_plaquetteModeChain] at hpair
  have hArea : integerCellPairing areaTestPotential
      (boundary (positionedRectangleSheet o ho L T hL hT)) = (L * T : ℕ) :=
    areaTestPotential_pairing_positionedRectangleLoop o ho hL hT
  change integerCellPairing areaTestPotential
    (positionedRectangleLoop o ho L T hL hT) = _ at hArea
  change _ = integerCellPairing areaTestPotential
      (positionedRectangleLoop o ho L T hL hT) at hpair
  rw [hArea] at hpair
  have hpair' :
      ∑ p : PrimalPlaquettes B, m p * areaTestPlaquetteCurl p = (L * T : ℕ) := by
    simpa [areaTestPlaquetteCurl] using hpair
  have harea_nonneg : 0 ≤ (L * T : ℤ) := by positivity
  calc
    (L * T : ℤ) =
        |∑ p : PrimalPlaquettes B, m p * areaTestPlaquetteCurl p| := by
      rw [hpair']
      simp [abs_of_nonneg harea_nonneg]
    _ ≤ ∑ p : PrimalPlaquettes B, |m p * areaTestPlaquetteCurl p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : PrimalPlaquettes B, |m p| := by
      apply Finset.sum_le_sum
      intro p hp
      rw [areaTestPlaquetteCurl_eq_axes]
      split_ifs <;> simp

theorem areaTestPotential_modeRealL1_lower_bound_positioned
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    (L * T : ℝ) ≤ ∑ p : PrimalPlaquettes B, |(m p : ℝ)| := by
  have hInt := areaTestPotential_modeL1_lower_bound_positioned
    o ho hL hT m hsource
  exact_mod_cast hInt

theorem areaLocalPotential_pairing_positionedRectangleLoop
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) :
    integerCellPairing
        (areaLocalPotential
          ⟨o 0 + i.val, by have := i.isLt; omega⟩
          ⟨o 1 + j.val, by have := j.isLt; omega⟩)
        (positionedRectangleLoop o ho L T hL hT) = 1 := by
  classical
  let a : Fin (B 0) := ⟨o 0 + i.val, by have := i.isLt; omega⟩
  let b : Fin (B 1) := ⟨o 1 + j.val, by have := j.isLt; omega⟩
  rw [positionedRectangleLoop, positionedRectangleSheet,
    integerCellPairing_boundary_sum]
  have hterm (x : Fin L × Fin T) :
      integerCellPairing (areaLocalPotential a b)
        (boundary (basisChain (positionedRectanglePlaquette o ho hL hT x.1 x.2))) =
        if x = (i, j) then 1 else 0 := by
    let p : PrimalPlaquettes B := ⟨positionedRectanglePlaquette o ho hL hT x.1 x.2, by
      rw [cellDegree, positionedRectanglePlaquette_axes]
      simp⟩
    rw [areaLocalPotential_curl p a b]
    have hxcoord : coordBase (p.1 0) = a.val ↔ x.1 = i := by
      constructor
      · intro h
        apply Fin.ext
        have hv : o 0 + x.1.val = o 0 + i.val := by
          simpa [p, a, positionedRectanglePlaquette_apply0, coordBase] using h
        omega
      · intro h
        simp [p, a, positionedRectanglePlaquette_apply0, coordBase, h]
    have hycoord : coordBase (p.1 1) = b.val ↔ x.2 = j := by
      constructor
      · intro h
        apply Fin.ext
        have hv : o 1 + x.2.val = o 1 + j.val := by
          simpa [p, b, positionedRectanglePlaquette_apply1, coordBase] using h
        omega
      · intro h
        simp [p, b, positionedRectanglePlaquette_apply1, coordBase, h]
    have haxes := positionedRectanglePlaquette_axes o ho hL hT x.1 x.2
    rw [haxes]
    simp [hxcoord, hycoord, Prod.ext_iff]
  change (∑ x : Fin L × Fin T,
    integerCellPairing (areaLocalPotential a b)
      (boundary (basisChain (positionedRectanglePlaquette o ho hL hT x.1 x.2)))) = 1
  calc
    _ = ∑ x : Fin L × Fin T, (if x = (i, j) then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hterm x
    _ = 1 := by simp

private theorem positioned_exists_nonzero_sum_term {α : Type*}
    (s : Finset α) (f : α → ℤ) (h : (∑ x ∈ s, f x) ≠ 0) :
    ∃ x ∈ s, f x ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  apply Finset.sum_eq_zero
  intro x hx
  exact hn x hx

theorem plaquetteFieldSupport_card_lower_bound_positioned
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    L * T ≤ (plaquetteFieldSupport m).card := by
  classical
  let index := Fin L × Fin T
  let localTest (x : index) : Cell 4 B → ℤ :=
    areaLocalPotential
      ⟨o 0 + x.1.val, by have := x.1.isLt; omega⟩
      ⟨o 1 + x.2.val, by have := x.2.isLt; omega⟩
  have hpair (x : index) :
      integerCellPairing (localTest x) (boundary (plaquetteModeChain m)) = 1 := by
    have heq := integerCellPairing_eq_of_degreeOne_coeff_eq
      (localTest x) (boundary (plaquetteModeChain m))
      (boundary (positionedRectangleSheet o ho L T hL hT))
      (by intro c hc; simp [localTest, areaLocalPotential, hc])
      (by
        intro c hc
        let l : PrimalLinks B := ⟨c, hc⟩
        have hl := congrFun hsource l
        simpa [plaquetteModeDivergence, primalSheetLoopFrequency] using hl)
    calc
      _ = integerCellPairing (localTest x)
          (boundary (positionedRectangleSheet o ho L T hL hT)) := heq
      _ = 1 := by
          rw [← positionedRectangleLoop]
          exact areaLocalPotential_pairing_positionedRectangleLoop o ho hL hT x.1 x.2
  have hsum (x : index) :
      (∑ p : PrimalPlaquettes B,
        m p * integerCellPairing (localTest x) (boundary (basisChain p.1))) = 1 := by
    rw [← integerCellPairing_boundary_plaquetteModeChain]
    exact hpair x
  let witness (x : index) :
      ∃ p : PrimalPlaquettes B, p ∈ plaquetteFieldSupport m ∧
        integerCellPairing (localTest x) (boundary (basisChain p.1)) = 1 := by
    have hne : (∑ p : PrimalPlaquettes B,
        m p * integerCellPairing (localTest x) (boundary (basisChain p.1))) ≠ 0 := by
      rw [hsum]
      norm_num
    obtain ⟨p, hp, hterm⟩ := positioned_exists_nonzero_sum_term
      (Finset.univ : Finset (PrimalPlaquettes B))
      (fun p => m p * integerCellPairing (localTest x) (boundary (basisChain p.1))) hne
    have hm : m p ≠ 0 := by
      intro hz
      simp [hz] at hterm
    have hcurl : integerCellPairing (localTest x)
        (boundary (basisChain p.1)) = 1 := by
      have hzero_or_one : integerCellPairing (localTest x)
          (boundary (basisChain p.1)) = 0 ∨
        integerCellPairing (localTest x) (boundary (basisChain p.1)) = 1 := by
        have hc := areaLocalPotential_curl p
          ⟨o 0 + x.1.val, by have := x.1.isLt; omega⟩
          ⟨o 1 + x.2.val, by have := x.2.isLt; omega⟩
        dsimp [localTest] at hc
        rw [hc]
        split_ifs <;> simp
      rcases hzero_or_one with hz | hone
      · exact False.elim (hterm (by rw [hz]; simp))
      · exact hone
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, hcurl⟩
  let pick (x : index) : PrimalPlaquettes B := Classical.choose (witness x)
  have hpick (x : index) :
      pick x ∈ plaquetteFieldSupport m ∧
        integerCellPairing (localTest x)
          (boundary (basisChain (pick x).1)) = 1 := Classical.choose_spec (witness x)
  have hinj : Function.Injective pick := by
    intro x y hxy
    have hcoords (z : index) :
        (0 : Fin 4) ∈ cellAxes (pick z).1 ∧
        (1 : Fin 4) ∈ cellAxes (pick z).1 ∧
        coordBase ((pick z).1 0) = o 0 + z.1.val ∧
        coordBase ((pick z).1 1) = o 1 + z.2.val := by
      have hc := hpick z |>.2
      rw [areaLocalPotential_curl] at hc
      split_ifs at hc with h
      · simpa [localTest] using h
      · simp at hc
    have hx := hcoords x
    have hy := hcoords y
    have h0 : x.1.val = y.1.val := Nat.add_left_cancel (by rw [← hx.2.2.1, ← hy.2.2.1, hxy])
    have h1 : x.2.val = y.2.val := Nat.add_left_cancel (by rw [← hx.2.2.2, ← hy.2.2.2, hxy])
    apply Prod.ext <;> apply Fin.ext <;> assumption
  have hcount :
      (Finset.univ : Finset index).card ≤ (plaquetteFieldSupport m).card :=
    Finset.card_le_card_of_injOn pick
      (by intro x hx; exact hpick x |>.1)
      (by intro x hx y hy hxy; exact hinj hxy)
  simpa [index, Fintype.card_prod] using hcount

theorem sourceIntegerDualTwoChain_apply {B : SourceBox}
    (q : SourceIntegerDualTwoField B) (c : DualCell 4 B)
    (hc : dualCellDegree c = 2) :
    sourceIntegerDualTwoChain q c = q ⟨c, hc⟩ := by
  unfold sourceIntegerDualTwoChain
  rw [Finsupp.embDomain_apply]
  have hx : ∃ a : SourceDualTwoCells B, sourceDualTwoEmbedding a = c :=
    ⟨⟨c, hc⟩, rfl⟩
  rw [dite_eq_left hx]
  have hchoose : hx.choose = (⟨c, hc⟩ : SourceDualTwoCells B) := by
    have hsecond : c = sourceDualTwoEmbedding (⟨c, hc⟩ : SourceDualTwoCells B) := rfl
    exact sourceDualTwoEmbedding.injective (hx.choose_spec.trans hsecond)
  rw [hchoose]

theorem cubePrimalSheet_apply_of_degreeTwo {L T N : ℕ}
    (c : Cell 4 (cube N)) (hc : cellDegree c = 2) :
    cubePrimalSheet L T N c =
      sourceIntegerCubeSheet L T N ⟨primalDualCellEquiv c, by
        have h := star_complementary_degree c
        omega⟩ := by
  have hdual : dualCellDegree (primalDualCellEquiv c) = 2 := by
    have h := star_complementary_degree c
    omega
  change Finsupp.equivMapDomain primalDualCellEquiv.symm
      (sourceIntegerDualTwoChain (sourceIntegerCubeSheet L T N)) c = _
  rw [Finsupp.equivMapDomain_apply]
  simpa using sourceIntegerDualTwoChain_apply
    (sourceIntegerCubeSheet L T N) (primalDualCellEquiv c) hdual

theorem cubeSheetCell_centeredPositionedPlaquette
    {L T N : ℕ} (hN : max L T ≤ N) (i : Fin L) (j : Fin T) :
    cubeSheetCell (L := L) (T := T) (N := N)
      ⟨primalDualCellEquiv
        (positionedRectanglePlaquette (centeredRectangleOrigin N)
          (centeredRectangleOrigin_le N) (centeredRectangleFits hN).1
          (centeredRectangleFits hN).2 i j), by
            have hpaxes := positionedRectanglePlaquette_axes
              (centeredRectangleOrigin N) (centeredRectangleOrigin_le N)
              (centeredRectangleFits hN).1 (centeredRectangleFits hN).2 i j
            have hpdegree : cellDegree
                (positionedRectanglePlaquette (centeredRectangleOrigin N)
                  (centeredRectangleOrigin_le N) (centeredRectangleFits hN).1
                  (centeredRectangleFits hN).2 i j) = 2 := by
              rw [cellDegree, hpaxes]
              simp
            have h := star_complementary_degree
              (positionedRectanglePlaquette (centeredRectangleOrigin N)
                (centeredRectangleOrigin_le N) (centeredRectangleFits hN).1
                (centeredRectangleFits hN).2 i j)
            omega⟩ := by
  have hL : L ≤ N := le_trans (Nat.le_max_left _ _) hN
  have hT : T ≤ N := le_trans (Nat.le_max_right _ _) hN
  have hi := i.isLt
  have hj := j.isLt
  let p := positionedRectanglePlaquette (centeredRectangleOrigin N)
    (centeredRectangleOrigin_le N) (centeredRectangleFits hN).1
    (centeredRectangleFits hN).2 i j
  have hdegree : cellDegree p = 2 := by
    rw [cellDegree, positionedRectanglePlaquette_axes]
    simp
  have hdual : dualCellDegree (primalDualCellEquiv p) = 2 := by
    have h := star_complementary_degree p
    omega
  change cubeSheetCell (L := L) (T := T) (N := N)
    (⟨primalDualCellEquiv p, hdual⟩ : SourceDualTwoCells (cube N))
  simp only [cubeSheetCell]
  have h0 : primalDualCellEquiv p 0 =
      Sum.inl (⟨N + i.val, by simp [cube]; omega⟩ : Fin (cube N 0)) := by
    dsimp [p, centeredRectangleOrigin, positionedRectanglePlaquette,
      positionedRectangleBaseCell, edgeCell]
    rfl
  have h1 : primalDualCellEquiv p 1 =
      Sum.inl (⟨N + j.val, by simp [cube]; omega⟩ : Fin (cube N 1)) := by
    dsimp [p, centeredRectangleOrigin, positionedRectanglePlaquette,
      positionedRectangleBaseCell, edgeCell]
    rfl
  have h2 : primalDualCellEquiv p 2 =
      (Sum.inr (⟨N, by simp [cube]; omega⟩ : Fin (cube N 2 + 1)) :
        DualCoord (cube N) 2) := by
    dsimp [p, centeredRectangleOrigin, positionedRectanglePlaquette,
      positionedRectangleBaseCell, edgeCell]
    rfl
  have h3 : primalDualCellEquiv p 3 =
      (Sum.inr (⟨N, by simp [cube]; omega⟩ : Fin (cube N 3 + 1)) :
        DualCoord (cube N) 3) := by
    dsimp [p, centeredRectangleOrigin, positionedRectanglePlaquette,
      positionedRectangleBaseCell, edgeCell]
    rfl
  rw [h0, h1, h2, h3]
  refine ⟨?_, ?_⟩
  · refine ⟨(⟨N + i.val, ?_⟩ : Fin (cube N 0)), ?_⟩
    · change N + i.val < 2 * N
      omega
    constructor
    · rfl
    constructor
    · change N ≤ N + i.val
      omega
    · change N + i.val < N + L
      omega
  · refine ⟨?_, ?_⟩
    · refine ⟨(⟨N + j.val, ?_⟩ : Fin (cube N 1)), ?_⟩
      · change N + j.val < 2 * N
        omega
      constructor
      · rfl
      constructor
      · change N ≤ N + j.val
        omega
      · change N + j.val < N + T
        omega
    · refine ⟨?_, ?_⟩
      · refine ⟨(⟨N, ?_⟩ : Fin (cube N 2 + 1)), ?_⟩
        · change N < 2 * N + 1
          omega
        constructor
        · rfl
        · rfl
      · refine ⟨(⟨N, ?_⟩ : Fin (cube N 3 + 1)), ?_⟩
        · change N < 2 * N + 1
          omega
        constructor
        · rfl
        change (⟨N, by change N < 2 * N + 1; omega⟩ : Fin (cube N 3 + 1)).val = N
        rfl

theorem cubeSheetCell_centered_iff_positionedPlaquette
    {L T N : ℕ} (hN : max L T ≤ N)
    (c : Cell 4 (cube N)) (hc : cellDegree c = 2) :
    cubeSheetCell (L := L) (T := T) (N := N)
        ⟨primalDualCellEquiv c, by
          have h := star_complementary_degree c
          omega⟩ ↔
      ∃ i : Fin L, ∃ j : Fin T,
        c = positionedRectanglePlaquette (centeredRectangleOrigin N)
          (centeredRectangleOrigin_le N) (centeredRectangleFits hN).1
          (centeredRectangleFits hN).2 i j := by
  let f : SourceDualTwoCells (cube N) := ⟨primalDualCellEquiv c, by
    have h := star_complementary_degree c
    omega⟩
  constructor
  · intro hf
    rcases hf with ⟨⟨v0, h0, h0lo, h0hi⟩,
      ⟨⟨v1, h1, h1lo, h1hi⟩, ⟨e2, h2, h2val⟩, ⟨e3, h3, h3val⟩⟩⟩
    have hL : L ≤ N := le_trans (Nat.le_max_left _ _) hN
    have hT : T ≤ N := le_trans (Nat.le_max_right _ _) hN
    have hc0 : ∃ e : Fin (cube N 0), c 0 = Sum.inr e ∧ e.val = v0.val := by
      cases hcoord : c 0 with
      | inl v =>
          have hbad : f.1 0 = Sum.inr (⟨v.val, v.isLt⟩ : Fin (cube N 0 + 1)) := by
            simp [f, primalDualCellEquiv, hcoord]
          rw [h0] at hbad
          cases hbad
      | inr e =>
          refine ⟨e, rfl, ?_⟩
          have heq : (⟨e.val, e.isLt⟩ : Fin (cube N 0)) = v0 := by
            simpa [f, primalDualCellEquiv, hcoord] using h0
          exact congrArg Fin.val heq
    have hc1 : ∃ e : Fin (cube N 1), c 1 = Sum.inr e ∧ e.val = v1.val := by
      cases hcoord : c 1 with
      | inl v =>
          have hbad : f.1 1 = Sum.inr (⟨v.val, v.isLt⟩ : Fin (cube N 1 + 1)) := by
            simp [f, primalDualCellEquiv, hcoord]
          rw [h1] at hbad
          cases hbad
      | inr e =>
          refine ⟨e, rfl, ?_⟩
          have heq : (⟨e.val, e.isLt⟩ : Fin (cube N 1)) = v1 := by
            simpa [f, primalDualCellEquiv, hcoord] using h1
          exact congrArg Fin.val heq
    obtain ⟨e0, hc0, he0⟩ := hc0
    obtain ⟨e1, hc1, he1⟩ := hc1
    have he0range : N ≤ e0.val ∧ e0.val < N + L := by simpa [he0] using And.intro h0lo h0hi
    have he1range : N ≤ e1.val ∧ e1.val < N + T := by simpa [he1] using And.intro h1lo h1hi
    let i : Fin L := ⟨e0.val - N, by omega⟩
    let j : Fin T := ⟨e1.val - N, by omega⟩
    have hi : N + i.val = e0.val := by dsimp [i]; omega
    have hj : N + j.val = e1.val := by dsimp [j]; omega
    have hc2 : c 2 = Sum.inl (⟨N, by simp [cube]; omega⟩ : Fin (cube N 2 + 1)) := by
      cases hcoord : c 2 with
      | inl v =>
          have heq : (⟨v.val, v.isLt⟩ : Fin (cube N 2 + 1)) = e2 := by
            simpa [f, primalDualCellEquiv, hcoord] using h2
          apply congrArg Sum.inl
          apply Fin.ext
          simpa [h2val] using congrArg Fin.val heq
      | inr e =>
          simp [primalDualCellEquiv, hcoord] at h2
    have hc3 : c 3 = Sum.inl (⟨N, by simp [cube]; omega⟩ : Fin (cube N 3 + 1)) := by
      cases hcoord : c 3 with
      | inl v =>
          have heq : (⟨v.val, v.isLt⟩ : Fin (cube N 3 + 1)) = e3 := by
            simpa [f, primalDualCellEquiv, hcoord] using h3
          apply congrArg Sum.inl
          apply Fin.ext
          simpa [h3val] using congrArg Fin.val heq
      | inr e =>
          simp [primalDualCellEquiv, hcoord] at h3
    refine ⟨i, j, ?_⟩
    funext k
    fin_cases k
    · simp [positionedRectanglePlaquette, centeredRectangleOrigin,
        edgeCell, hc0, hi]
    · simp [positionedRectanglePlaquette, centeredRectangleOrigin,
        edgeCell, hc1, hj]
    · simp [positionedRectanglePlaquette, positionedRectangleBaseCell,
        centeredRectangleOrigin, edgeCell, hc2]
    · simp [positionedRectanglePlaquette, positionedRectangleBaseCell,
        centeredRectangleOrigin, edgeCell, hc3]
  · rintro ⟨i, j, rfl⟩
    exact cubeSheetCell_centeredPositionedPlaquette hN i j

theorem positionedRectangleSheet_apply {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (c : Cell 4 B) :
    positionedRectangleSheet o ho L T hL hT c =
      if ∃ i : Fin L, ∃ j : Fin T,
          positionedRectanglePlaquette o ho hL hT i j = c then 1 else 0 := by
  classical
  by_cases hex : ∃ i : Fin L, ∃ j : Fin T,
      positionedRectanglePlaquette o ho hL hT i j = c
  · obtain ⟨i, j, hxc⟩ := hex
    let x : Fin L × Fin T := (i, j)
    have hunique (y : Fin L × Fin T)
        (hy : positionedRectanglePlaquette o ho hL hT y.1 y.2 = c) : y = x := by
      apply positionedRectanglePlaquette_injective o ho hL hT
      exact hy.trans hxc.symm
    unfold positionedRectangleSheet
    rw [finsupp_finset_sum_apply]
    rw [Finset.sum_eq_single x]
    · have hex' : ∃ a : Fin L, ∃ b : Fin T,
          positionedRectanglePlaquette o ho hL hT a b = c := ⟨i, j, hxc⟩
      simp [basisChain, x, hxc, hex']
    · intro y hy hne
      have hneq : positionedRectanglePlaquette o ho hL hT y.1 y.2 ≠ c := by
        intro h
        exact hne (hunique y h)
      simp [basisChain, hneq]
    · intro hnot
      exact (hnot (Finset.mem_univ x)).elim
  · unfold positionedRectangleSheet
    rw [finsupp_finset_sum_apply]
    rw [Finset.sum_eq_zero]
    · simp [hex]
    · intro x hx
      have hneq : positionedRectanglePlaquette o ho hL hT x.1 x.2 ≠ c := by
        intro h
        exact hex ⟨x.1, x.2, h⟩
      simp [basisChain, hneq]

theorem positionedRectangleSheet_eq_cubePrimalSheet
    {L T N : ℕ} (hN : max L T ≤ N) :
    positionedRectangleSheet (centeredRectangleOrigin N)
      (centeredRectangleOrigin_le N) L T
      (centeredRectangleFits hN).1 (centeredRectangleFits hN).2 =
      cubePrimalSheet L T N := by
  classical
  let o := centeredRectangleOrigin N
  let ho := centeredRectangleOrigin_le N
  let hfits := centeredRectangleFits hN
  ext c
  by_cases hc : cellDegree c = 2
  · rw [cubePrimalSheet_apply_of_degreeTwo c hc]
    have hiff := cubeSheetCell_centered_iff_positionedPlaquette hN c hc
    simp only [sourceIntegerCubeSheet, Finsupp.equivFunOnFinite_symm_apply_apply]
    rw [positionedRectangleSheet_apply]
    have hiff' : cubeSheetCell (L := L) (T := T) (N := N)
        ⟨primalDualCellEquiv c, by
          have h := star_complementary_degree c
          omega⟩ ↔
        ∃ i : Fin L, ∃ j : Fin T,
          positionedRectanglePlaquette (centeredRectangleOrigin N)
            (centeredRectangleOrigin_le N) (centeredRectangleFits hN).1
            (centeredRectangleFits hN).2 i j = c := by
      constructor
      · intro h
        obtain ⟨i, j, heq⟩ := hiff.mp h
        exact ⟨i, j, heq.symm⟩
      · rintro ⟨i, j, heq⟩
        exact hiff.mpr ⟨i, j, heq.symm⟩
    simp [hiff']
  · have hcube : cubePrimalSheet L T N c = 0 := by
      by_contra hne
      exact hc (cubePrimalSheet_homogeneousSupport L T N c
        (Finsupp.mem_support_iff.mpr hne))
    have hpos : positionedRectangleSheet o ho L T hfits.1 hfits.2 c = 0 := by
      by_contra hne
      exact hc (positionedRectangleSheet_homogeneousSupport o ho hfits.1 hfits.2 c
        (Finsupp.mem_support_iff.mpr hne))
    rw [hpos, hcube]

theorem centeredPositionedRectangleLoop_eq_cubePrimalSheet_boundary
    {L T N : ℕ} (hN : max L T + 1 ≤ N) :
    positionedRectangleLoop (centeredRectangleOrigin N)
      (centeredRectangleOrigin_le N) L T
      (centeredRectangleFits (L := L) (T := T) (N := N) (by omega)).1
      (centeredRectangleFits (L := L) (T := T) (N := N) (by omega)).2 =
      boundary (cubePrimalSheet L T N) := by
  have hcenter : max L T ≤ N := by omega
  change positionedRectangleLoop (centeredRectangleOrigin N)
      (centeredRectangleOrigin_le N) L T
      (centeredRectangleFits hcenter).1 (centeredRectangleFits hcenter).2 = _
  rw [positionedRectangleLoop,
    positionedRectangleSheet_eq_cubePrimalSheet hcenter]


/-! ### Positioned boundary geometry -/

@[expose] def positionedHorizontalLink {B : Box 4}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (x : Fin (B 0)) (y : Fin (B 1 + 1)) : Cell 4 B :=
  edgeCell (vertexUpdate (positionedRectangleBaseCell o ho) 1 y) 0 x

@[expose] def positionedVerticalLink {B : Box 4}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (x : Fin (B 0 + 1)) (y : Fin (B 1)) : Cell 4 B :=
  edgeCell (vertexUpdate (positionedRectangleBaseCell o ho) 0 x) 1 y

@[expose] def positionedRectangleBottomLink {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) (i : Fin L) : Cell 4 B :=
  positionedHorizontalLink o ho ⟨o 0 + i.val, by have := i.isLt; omega⟩
    ⟨o 1, Nat.lt_succ_of_le (by omega)⟩

@[expose] def positionedRectangleTopLink {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) (i : Fin L) : Cell 4 B :=
  positionedHorizontalLink o ho ⟨o 0 + i.val, by have := i.isLt; omega⟩
    ⟨o 1 + T, Nat.lt_succ_of_le (by omega)⟩

@[expose] def positionedRectangleLeftLink {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) (j : Fin T) : Cell 4 B :=
  positionedVerticalLink o ho ⟨o 0, Nat.lt_succ_of_le (by omega)⟩
    ⟨o 1 + j.val, by have := j.isLt; omega⟩

@[expose] def positionedRectangleRightLink {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) (j : Fin T) : Cell 4 B :=
  positionedVerticalLink o ho ⟨o 0 + L, Nat.lt_succ_of_le (by omega)⟩
    ⟨o 1 + j.val, by have := j.isLt; omega⟩

@[expose] noncomputable def positionedRectanglePerimeter {B : Box 4}
    {L T : ℕ} (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) : Finset (Cell 4 B) :=
  Finset.univ.image (positionedRectangleBottomLink o ho hL hT) ∪
    (Finset.univ.image (positionedRectangleTopLink o ho hL hT) ∪
      (Finset.univ.image (positionedRectangleLeftLink o ho hL hT) ∪
        Finset.univ.image (positionedRectangleRightLink o ho hL hT)))

@[simp] theorem positionedHorizontalLink_axes {B : Box 4}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (x : Fin (B 0)) (y : Fin (B 1 + 1)) :
    cellAxes (positionedHorizontalLink o ho x y) = {0} := by
  classical
  unfold positionedHorizontalLink
  rw [cellAxes_edgeCell_eq_insert]
  have hv : cellAxes (vertexUpdate (positionedRectangleBaseCell o ho) 1 y) = ∅ := by
    ext k
    simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases k <;> simp [coordIsEdge, vertexUpdate, positionedRectangleBaseCell]
  rw [hv]
  simp

@[simp] theorem positionedVerticalLink_axes {B : Box 4}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (x : Fin (B 0 + 1)) (y : Fin (B 1)) :
    cellAxes (positionedVerticalLink o ho x y) = {1} := by
  classical
  unfold positionedVerticalLink
  rw [cellAxes_edgeCell_eq_insert]
  have hv : cellAxes (vertexUpdate (positionedRectangleBaseCell o ho) 0 x) = ∅ := by
    ext k
    simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases k <;> simp [coordIsEdge, vertexUpdate, positionedRectangleBaseCell]
  rw [hv]
  simp

@[simp] theorem positionedHorizontalLink_apply0 {B : Box 4} {o : Fin 4 → ℕ}
    {ho : ∀ k, o k ≤ B k} {x : Fin (B 0)} {y : Fin (B 1 + 1)} :
    positionedHorizontalLink o ho x y 0 = Sum.inr x := by
  simp [positionedHorizontalLink, edgeCell, vertexUpdate]

@[simp] theorem positionedHorizontalLink_apply1 {B : Box 4} {o : Fin 4 → ℕ}
    {ho : ∀ k, o k ≤ B k} {x : Fin (B 0)} {y : Fin (B 1 + 1)} :
    positionedHorizontalLink o ho x y 1 = Sum.inl y := by
  simp [positionedHorizontalLink, edgeCell, vertexUpdate]

@[simp] theorem positionedVerticalLink_apply0 {B : Box 4} {o : Fin 4 → ℕ}
    {ho : ∀ k, o k ≤ B k} {x : Fin (B 0 + 1)} {y : Fin (B 1)} :
    positionedVerticalLink o ho x y 0 = Sum.inl x := by
  simp [positionedVerticalLink, edgeCell, vertexUpdate]

@[simp] theorem positionedVerticalLink_apply1 {B : Box 4} {o : Fin 4 → ℕ}
    {ho : ∀ k, o k ≤ B k} {x : Fin (B 0 + 1)} {y : Fin (B 1)} :
    positionedVerticalLink o ho x y 1 = Sum.inr y := by
  simp [positionedVerticalLink, edgeCell, vertexUpdate]


private theorem positionedPlaquette_boundary_explicit {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) :
    boundary (basisChain (positionedRectanglePlaquette o ho hL hT i j)) =
      basisChain (positionedHorizontalLink o ho
        ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨o 1 + j.val, by have := j.isLt; omega⟩) +
      basisChain (positionedVerticalLink o ho
        ⟨o 0 + i.val + 1, by have := i.isLt; omega⟩
        ⟨o 1 + j.val, by have := j.isLt; omega⟩) -
      basisChain (positionedHorizontalLink o ho
        ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨o 1 + j.val + 1, by have := j.isLt; omega⟩) -
      basisChain (positionedVerticalLink o ho
        ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨o 1 + j.val, by have := j.isLt; omega⟩) := by
  classical
  let p := positionedRectanglePlaquette o ho hL hT i j
  have hset0 : (Finset.univ.filter fun k : Fin 4 =>
      k < 0 ∧ coordIsEdge (p k)) = ∅ := by ext k; simp
  have hset1 : (Finset.univ.filter fun k : Fin 4 =>
      k < 1 ∧ coordIsEdge (p k)) = {0} := by
    ext k
    fin_cases k <;> simp [p, positionedRectanglePlaquette, edgeCell,
      positionedRectangleBaseCell, coordIsEdge]
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
  have hright : upperFace p 0 ⟨o 0 + i.val, by have := i.isLt; omega⟩ =
      positionedVerticalLink o ho ⟨o 0 + i.val + 1, by have := i.isLt; omega⟩
        ⟨o 1 + j.val, by have := j.isLt; omega⟩ := by
    funext k
    fin_cases k <;> simp [p, positionedRectanglePlaquette, positionedVerticalLink,
      upperFace, edgeCell, vertexUpdate, positionedRectangleBaseCell]
  have hleft : lowerFace p 0 ⟨o 0 + i.val, by have := i.isLt; omega⟩ =
      positionedVerticalLink o ho ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨o 1 + j.val, by have := j.isLt; omega⟩ := by
    funext k
    fin_cases k <;> simp [p, positionedRectanglePlaquette, positionedVerticalLink,
      lowerFace, edgeCell, vertexUpdate, positionedRectangleBaseCell]
  have htop : upperFace p 1 ⟨o 1 + j.val, by have := j.isLt; omega⟩ =
      positionedHorizontalLink o ho ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨o 1 + j.val + 1, by have := j.isLt; omega⟩ := by
    funext k
    fin_cases k <;> simp [p, positionedRectanglePlaquette, positionedHorizontalLink,
      upperFace, edgeCell, vertexUpdate, positionedRectangleBaseCell]
  have hbottom : lowerFace p 1 ⟨o 1 + j.val, by have := j.isLt; omega⟩ =
      positionedHorizontalLink o ho ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨o 1 + j.val, by have := j.isLt; omega⟩ := by
    funext k
    fin_cases k <;> simp [p, positionedRectanglePlaquette, positionedHorizontalLink,
      lowerFace, edgeCell, vertexUpdate, positionedRectangleBaseCell]
  have hp0 : p 0 = Sum.inr ⟨o 0 + i.val, by have := i.isLt; omega⟩ := by
    simp [p, positionedRectanglePlaquette, edgeCell]
  have hp1 : p 1 = Sum.inr ⟨o 1 + j.val, by have := j.isLt; omega⟩ := by
    simp [p, positionedRectanglePlaquette, edgeCell]
  have hp2 : p 2 = Sum.inl ⟨o 2, Nat.lt_succ_of_le (ho 2)⟩ := by
    simp [p, positionedRectanglePlaquette, edgeCell, positionedRectangleBaseCell]
  have hp3 : p 3 = Sum.inl ⟨o 3, Nat.lt_succ_of_le (ho 3)⟩ := by
    simp [p, positionedRectanglePlaquette, edgeCell, positionedRectangleBaseCell]
  have hp1' : p (Fin.succ 0) = Sum.inr ⟨o 1 + j.val,
      Nat.lt_of_lt_of_le (by omega : o 1 + j.val < o 1 + T) hT⟩ := by
    simp [p, positionedRectanglePlaquette, edgeCell]
  have hp2' : p (Fin.succ 0).succ = Sum.inl ⟨o 2, Nat.lt_succ_of_le (ho 2)⟩ := by
    simp [p, positionedRectanglePlaquette, edgeCell, positionedRectangleBaseCell]
  have hp3' : p (Fin.succ 0).succ.succ = Sum.inl ⟨o 3, Nat.lt_succ_of_le (ho 3)⟩ := by
    simp [p, positionedRectanglePlaquette, edgeCell, positionedRectangleBaseCell]
  have hjcoord : o 1 + j.val < B 1 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT
  have htop' : upperFace p (Fin.succ 0) ⟨o 1 + j.val, by simpa using hjcoord⟩ =
      positionedHorizontalLink o ho ⟨o 0 + i.val,
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val + 1, Nat.lt_succ_of_le (by
          calc
            o 1 + j.val + 1 = o 1 + (j.val + 1) := by omega
            _ ≤ o 1 + T := Nat.add_le_add_left (Nat.succ_le_of_lt j.isLt) _
            _ ≤ B 1 := hT)⟩ := by simpa using htop
  have hbottom' : lowerFace p (Fin.succ 0) ⟨o 1 + j.val, by simpa using hjcoord⟩ =
      positionedHorizontalLink o ho ⟨o 0 + i.val,
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_succ_of_le
          (Nat.le_trans (Nat.add_le_add_left (Nat.le_of_lt j.isLt) (o 1)) hT)⟩ := by
            simpa using hbottom
  simp only [hp0, hp1', hp2', hp3', hright, hleft, htop', hbottom']
  simp only [Fin.sum_univ_zero]
  abel_nf

private theorem positionedFinSum_sub_succ_eq_endpoints {G : Type*} [AddCommGroup G]
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

private theorem positionedFinSum_succ_sub_eq_endpoints {G : Type*} [AddCommGroup G]
    (n : ℕ) (f : ℕ → G) :
    (∑ i : Fin n, (f (i.val + 1) - f i.val)) = f n - f 0 := by
  have h := positionedFinSum_sub_succ_eq_endpoints n f
  calc
    (∑ i : Fin n, (f (i.val + 1) - f i.val)) =
        ∑ i : Fin n, -(f i.val - f (i.val + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          abel
    _ = - ∑ i : Fin n, (f i.val - f (i.val + 1)) := by
          rw [Finset.sum_neg_distrib]
    _ = f n - f 0 := by rw [h]; abel

theorem positionedRectangleLoop_eq_perimeterRows {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) :
    positionedRectangleLoop o ho L T hL hT =
      (∑ i : Fin L, basisChain (positionedRectangleBottomLink o ho hL hT i)) -
      (∑ i : Fin L, basisChain (positionedRectangleTopLink o ho hL hT i)) +
      (∑ j : Fin T, basisChain (positionedRectangleRightLink o ho hL hT j)) -
      (∑ j : Fin T, basisChain (positionedRectangleLeftLink o ho hL hT j)) := by
  classical
  let H (i : Fin L) (j : ℕ) : Chain 4 B :=
    if hj : j ≤ B 1 then
      basisChain (positionedHorizontalLink o ho
        ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨j, Nat.lt_succ_of_le hj⟩)
    else 0
  let V (i : ℕ) (j : Fin T) : Chain 4 B :=
    if hi : i ≤ B 0 then
      basisChain (positionedVerticalLink o ho
        ⟨i, Nat.lt_succ_of_le hi⟩
        ⟨o 1 + j.val,
          Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
    else 0
  have hhorizontal (i : Fin L) :
      (∑ j : Fin T, (H i (o 1 + j.val) - H i (o 1 + j.val + 1))) =
        H i (o 1) - H i (o 1 + T) := by
    have h := positionedFinSum_sub_succ_eq_endpoints T (fun j => H i (o 1 + j))
    simpa [Nat.add_assoc] using h
  have hvertical (j : Fin T) :
      (∑ i : Fin L, (V (o 0 + i.val + 1) j - V (o 0 + i.val) j)) =
        V (o 0 + L) j - V (o 0) j := by
    have h := positionedFinSum_succ_sub_eq_endpoints L (fun i => V (o 0 + i) j)
    simpa [Nat.add_assoc] using h
  unfold positionedRectangleLoop positionedRectangleSheet
  rw [map_sum, Fintype.sum_prod_type]
  simp_rw [positionedPlaquette_boundary_explicit]
  have hHbottom (i : Fin L) (j : Fin T) :
      basisChain (positionedHorizontalLink o ho
        ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨o 1 + j.val, by have := j.isLt; omega⟩) = H i (o 1 + j.val) := by
    have hj : o 1 + j.val ≤ B 1 := by have := j.isLt; omega
    simp [H, hj]
  have hHtop (i : Fin L) (j : Fin T) :
      basisChain (positionedHorizontalLink o ho
        ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨o 1 + j.val + 1, by have := j.isLt; omega⟩) = H i (o 1 + j.val + 1) := by
    have hj : o 1 + (j.val + 1) ≤ B 1 := by have := j.isLt; omega
    simp [H, hj, Nat.add_assoc]
  have hVleft (i : Fin L) (j : Fin T) :
      basisChain (positionedVerticalLink o ho
        ⟨o 0 + i.val, by have := i.isLt; omega⟩
        ⟨o 1 + j.val, by have := j.isLt; omega⟩) = V (o 0 + i.val) j := by
    have hi : o 0 + i.val ≤ B 0 := by have := i.isLt; omega
    simp [V, hi]
  have hVright (i : Fin L) (j : Fin T) :
      basisChain (positionedVerticalLink o ho
        ⟨o 0 + i.val + 1, by have := i.isLt; omega⟩
        ⟨o 1 + j.val, by have := j.isLt; omega⟩) = V (o 0 + i.val + 1) j := by
    have hi : o 0 + (i.val + 1) ≤ B 0 := by have := i.isLt; omega
    simp [V, hi, Nat.add_assoc]
  simp_rw [hHbottom, hHtop, hVleft, hVright]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hHdiff :
      (∑ i : Fin L, ∑ j : Fin T, H i (o 1 + j.val)) -
        (∑ i : Fin L, ∑ j : Fin T, H i (o 1 + j.val + 1)) =
        (∑ i : Fin L, H i (o 1)) - (∑ i : Fin L, H i (o 1 + T)) := by
    calc
      _ = ∑ i : Fin L, ∑ j : Fin T,
            (H i (o 1 + j.val) - H i (o 1 + j.val + 1)) := by
              rw [← Finset.sum_sub_distrib]
              apply Fintype.sum_congr
              intro i
              rw [← Finset.sum_sub_distrib]
      _ = ∑ i : Fin L, (H i (o 1) - H i (o 1 + T)) := by
              apply Fintype.sum_congr
              intro i
              exact hhorizontal i
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hVdiff :
      (∑ i : Fin L, ∑ j : Fin T, V (o 0 + i.val + 1) j) -
        (∑ i : Fin L, ∑ j : Fin T, V (o 0 + i.val) j) =
        (∑ j : Fin T, V (o 0 + L) j) - (∑ j : Fin T, V (o 0) j) := by
    have hrightSum :
        (∑ i : Fin L, ∑ j : Fin T, V (o 0 + i.val + 1) j) =
          ∑ j : Fin T, ∑ i : Fin L, V (o 0 + i.val + 1) j := by
      rw [Finset.sum_comm]
    have hleftSum :
        (∑ i : Fin L, ∑ j : Fin T, V (o 0 + i.val) j) =
          ∑ j : Fin T, ∑ i : Fin L, V (o 0 + i.val) j := by
      rw [Finset.sum_comm]
    calc
      _ = ∑ j : Fin T, ∑ i : Fin L,
            (V (o 0 + i.val + 1) j - V (o 0 + i.val) j) := by
              rw [hrightSum, hleftSum, ← Finset.sum_sub_distrib]
              apply Fintype.sum_congr
              intro j
              rw [← Finset.sum_sub_distrib]
      _ = ∑ j : Fin T, (V (o 0 + L) j - V (o 0) j) := by
              apply Fintype.sum_congr
              intro j
              exact hvertical j
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hH0 : (∑ i : Fin L, H i (o 1)) =
      ∑ i : Fin L, basisChain (positionedRectangleBottomLink o ho hL hT i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [H, positionedRectangleBottomLink, ho]
  have hHT : (∑ i : Fin L, H i (o 1 + T)) =
      ∑ i : Fin L, basisChain (positionedRectangleTopLink o ho hL hT i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [H, positionedRectangleTopLink, hT]
  have hVR : (∑ j : Fin T, V (o 0 + L) j) =
      ∑ j : Fin T, basisChain (positionedRectangleRightLink o ho hL hT j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [V, positionedRectangleRightLink, hL]
  have hVL : (∑ j : Fin T, V (o 0) j) =
      ∑ j : Fin T, basisChain (positionedRectangleLeftLink o ho hL hT j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [V, positionedRectangleLeftLink, ho]
  calc
    _ = ((∑ i : Fin L, ∑ j : Fin T, H i (o 1 + j.val)) -
        (∑ i : Fin L, ∑ j : Fin T, H i (o 1 + j.val + 1))) +
        ((∑ i : Fin L, ∑ j : Fin T, V (o 0 + i.val + 1) j) -
        (∑ i : Fin L, ∑ j : Fin T, V (o 0 + i.val) j)) := by abel
    _ = ((∑ i : Fin L, H i (o 1)) - (∑ i : Fin L, H i (o 1 + T))) +
        ((∑ j : Fin T, V (o 0 + L) j) - (∑ j : Fin T, V (o 0) j)) := by
          rw [hHdiff, hVdiff]
    _ = _ := by rw [hH0, hHT, hVR, hVL]; abel

private theorem positioned_row_support_subset_image {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (_hT : o 1 + T ≤ B 1)
    (y : Fin (B 1 + 1)) :
    (∑ i : Fin L, basisChain (positionedHorizontalLink o ho
      ⟨o 0 + i.val, by have := i.isLt; omega⟩ y)).support ⊆
      Finset.univ.image (fun i : Fin L => positionedHorizontalLink o ho
        ⟨o 0 + i.val, by have := i.isLt; omega⟩ y) := by
  classical
  intro c hc
  have hsum := Finsupp.support_finsetSum hc
  rcases Finset.mem_biUnion.mp hsum with ⟨i, hi, hterm⟩
  have hsingle : c = positionedHorizontalLink o ho
      ⟨o 0 + i.val, by have := i.isLt; omega⟩ y := by
    have hne : basisChain (positionedHorizontalLink o ho
        ⟨o 0 + i.val, by have := i.isLt; omega⟩ y) c ≠ 0 :=
      Finsupp.mem_support_iff.mp hterm
    by_contra h
    simp [basisChain, h] at hne
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hsingle.symm⟩

private theorem positioned_col_support_subset_image {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (_hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (x : Fin (B 0 + 1)) :
    (∑ j : Fin T, basisChain (positionedVerticalLink o ho x
      ⟨o 1 + j.val, by have := j.isLt; omega⟩)).support ⊆
      Finset.univ.image (fun j : Fin T => positionedVerticalLink o ho x
        ⟨o 1 + j.val, by have := j.isLt; omega⟩) := by
  classical
  intro c hc
  have hsum := Finsupp.support_finsetSum hc
  rcases Finset.mem_biUnion.mp hsum with ⟨j, hj, hterm⟩
  have hsingle : c = positionedVerticalLink o ho x
      ⟨o 1 + j.val, by have := j.isLt; omega⟩ := by
    have hne : basisChain (positionedVerticalLink o ho x
        ⟨o 1 + j.val, by have := j.isLt; omega⟩) c ≠ 0 :=
      Finsupp.mem_support_iff.mp hterm
    by_contra h
    simp [basisChain, h] at hne
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hsingle.symm⟩

theorem positionedRectangleLoop_support_subset_perimeter {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) :
    (positionedRectangleLoop o ho L T hL hT).support ⊆
      positionedRectanglePerimeter o ho hL hT := by
  classical
  rw [positionedRectangleLoop_eq_perimeterRows]
  let bot := ∑ i : Fin L, basisChain (positionedRectangleBottomLink o ho hL hT i)
  let top := ∑ i : Fin L, basisChain (positionedRectangleTopLink o ho hL hT i)
  let right := ∑ j : Fin T, basisChain (positionedRectangleRightLink o ho hL hT j)
  let left := ∑ j : Fin T, basisChain (positionedRectangleLeftLink o ho hL hT j)
  intro c hc
  change c ∈ (bot - top + right - left).support at hc
  have hsupport : (bot - top + right - left).support ⊆
      (bot.support ∪ top.support) ∪ (right.support ∪ left.support) := by
    calc
      (bot - top + right - left).support = ((bot - top) + (right - left)).support := by
        congr 1
        abel
      _ ⊆ (bot - top).support ∪ (right - left).support := Finsupp.support_add
      _ ⊆ (bot.support ∪ top.support) ∪ (right.support ∪ left.support) := by
        exact Finset.union_subset_union Finsupp.support_sub Finsupp.support_sub
  rcases Finset.mem_union.mp (hsupport hc) with hrows | hcols
  · rcases Finset.mem_union.mp hrows with hbot | htop
    · exact Finset.mem_union_left _ (positioned_row_support_subset_image o ho hL hT _ hbot)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (positioned_row_support_subset_image o ho hL hT _ htop))
  · rcases Finset.mem_union.mp hcols with hright | hleft
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (positioned_col_support_subset_image o ho hL hT _ hright)))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_left _ (positioned_col_support_subset_image o ho hL hT _ hleft)))

theorem positionedRectanglePerimeter_mem_cases {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (c : Cell 4 B) (hc : c ∈ positionedRectanglePerimeter o ho hL hT) :
    (∃ i : Fin L, c = positionedRectangleBottomLink o ho hL hT i) ∨
    (∃ i : Fin L, c = positionedRectangleTopLink o ho hL hT i) ∨
    (∃ j : Fin T, c = positionedRectangleLeftLink o ho hL hT j) ∨
    (∃ j : Fin T, c = positionedRectangleRightLink o ho hL hT j) := by
  classical
  simp only [positionedRectanglePerimeter, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hc
  rcases hc with ⟨i, h⟩ | ⟨i, h⟩ | ⟨j, h⟩ | ⟨j, h⟩
  · exact Or.inl ⟨i, h.symm⟩
  · exact Or.inr (Or.inl ⟨i, h.symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨j, h.symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, h.symm⟩))

private theorem positionedHorizontal_ne_vertical {B : Box 4}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (x : Fin (B 0)) (y : Fin (B 1 + 1))
    (u : Fin (B 0 + 1)) (v : Fin (B 1)) :
    positionedHorizontalLink o ho x y ≠ positionedVerticalLink o ho u v := by
  intro h
  have haxes := congrArg cellAxes h
  simp [positionedHorizontalLink_axes, positionedVerticalLink_axes] at haxes


-- The side-case simp sets are shared across branches; a few branch-local entries
-- are intentionally unused by each individual simplification.
set_option linter.unusedSimpArgs false

private theorem positionedHorizontalPotentialBottom_shape {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (_hLpos : 0 < L) (hTpos : 0 < T)
    (i : Fin L) (j : Fin T) (c : Cell 4 B)
    (hc : c ∈ positionedRectanglePerimeter o ho hL hT) :
    areaLawHorizontalPotentialBottom
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c =
      if c = positionedRectangleBottomLink o ho hL hT i then 1 else 0 := by
  rcases positionedRectanglePerimeter_mem_cases o ho hL hT c hc with hb | ht | hl | hr
  · obtain ⟨k, rfl⟩ := hb
    by_cases hk : k = i
    · subst k
      have hval : areaLawHorizontalPotentialBottom
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
          (positionedRectangleBottomLink o ho hL hT i) = 1 := by
        simp [areaLawHorizontalPotentialBottom, positionedRectangleBottomLink,
          cellDegree, positionedHorizontalLink_axes,
          coordBase, Nat.le_add_right]
      simpa using hval
    · have hcoord : o 0 + k.val ≠ o 0 + i.val := by
        intro heq
        exact hk (Fin.ext (Nat.add_left_cancel heq))
      have hne : positionedRectangleBottomLink o ho hL hT k ≠
          positionedRectangleBottomLink o ho hL hT i := by
        intro heq
        apply hcoord
        have h := congrArg (fun z => coordBase (z 0)) heq
        simpa [positionedRectangleBottomLink, coordBase] using h
      have hindex : k.val ≠ i.val := by
        intro hki
        exact hk (Fin.ext hki)
      have hval : areaLawHorizontalPotentialBottom
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
          (positionedRectangleBottomLink o ho hL hT k) = 0 := by
        simp [areaLawHorizontalPotentialBottom, positionedRectangleBottomLink,
          cellDegree, positionedHorizontalLink_axes,
          coordBase, hcoord, hindex, Nat.le_add_right]
      rw [hval]
      simp [hne, hindex]
  · obtain ⟨k, rfl⟩ := ht
    have hcut : ¬ o 1 + T ≤ o 1 + j.val := by omega
    have hne : positionedRectangleTopLink o ho hL hT k ≠
        positionedRectangleBottomLink o ho hL hT i := by
      intro heq
      have h := congrArg (fun z => coordBase (z 1)) heq
      simp [positionedRectangleTopLink, positionedRectangleBottomLink,
        coordBase] at h
      omega
    have hval : areaLawHorizontalPotentialBottom
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleTopLink o ho hL hT k) = 0 := by
      simp [areaLawHorizontalPotentialBottom, positionedRectangleTopLink, cellDegree,
        positionedHorizontalLink_axes, coordBase, hcut]
    rw [hval]
    simp [hne]
  · obtain ⟨k, rfl⟩ := hl
    have hne : positionedRectangleLeftLink o ho hL hT k ≠
        positionedRectangleBottomLink o ho hL hT i := by
      intro h
      exact positionedHorizontal_ne_vertical o ho _ _ _ _ h.symm
    have hval : areaLawHorizontalPotentialBottom
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleLeftLink o ho hL hT k) = 0 := by
      simp [areaLawHorizontalPotentialBottom, positionedRectangleLeftLink,
        cellDegree, positionedVerticalLink_axes]
    rw [hval]
    simp [hne]
  · obtain ⟨k, rfl⟩ := hr
    have hne : positionedRectangleRightLink o ho hL hT k ≠
        positionedRectangleBottomLink o ho hL hT i := by
      intro h
      exact positionedHorizontal_ne_vertical o ho _ _ _ _ h.symm
    have hval : areaLawHorizontalPotentialBottom
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleRightLink o ho hL hT k) = 0 := by
      simp [areaLawHorizontalPotentialBottom, positionedRectangleRightLink,
        cellDegree, positionedVerticalLink_axes]
    rw [hval]
    simp [hne]

private theorem positionedHorizontalPotentialTop_shape {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (_hLpos : 0 < L) (hTpos : 0 < T)
    (i : Fin L) (j : Fin T) (c : Cell 4 B)
    (hc : c ∈ positionedRectanglePerimeter o ho hL hT) :
    areaLawHorizontalPotentialTop
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c =
      if c = positionedRectangleTopLink o ho hL hT i then -1 else 0 := by
  rcases positionedRectanglePerimeter_mem_cases o ho hL hT c hc with hb | ht | hl | hr
  · obtain ⟨k, rfl⟩ := hb
    have hne : positionedRectangleBottomLink o ho hL hT k ≠
        positionedRectangleTopLink o ho hL hT i := by
      intro heq
      have h := congrArg (fun z => coordBase (z 1)) heq
      simp [positionedRectangleBottomLink, positionedRectangleTopLink,
        coordBase] at h
      omega
    have hval : areaLawHorizontalPotentialTop
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleBottomLink o ho hL hT k) = 0 := by
      simp [areaLawHorizontalPotentialTop, positionedRectangleBottomLink, cellDegree,
        positionedHorizontalLink_axes, coordBase]
    rw [hval]
    simp [hne]
  · obtain ⟨k, rfl⟩ := ht
    by_cases hk : k = i
    · subst k
      have hcut : o 1 + j.val < o 1 + T := Nat.add_lt_add_left j.isLt (o 1)
      have hval : areaLawHorizontalPotentialTop
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
          (positionedRectangleTopLink o ho hL hT i) = -1 := by
        simp [areaLawHorizontalPotentialTop, positionedRectangleTopLink, cellDegree,
          positionedHorizontalLink_axes, coordBase, hcut]
      simpa using hval
    · have hcoord : o 0 + k.val ≠ o 0 + i.val := by
        intro heq
        exact hk (Fin.ext (Nat.add_left_cancel heq))
      have hne : positionedRectangleTopLink o ho hL hT k ≠
          positionedRectangleTopLink o ho hL hT i := by
        intro heq
        apply hcoord
        have h := congrArg (fun z => coordBase (z 0)) heq
        simpa [positionedRectangleTopLink, coordBase] using h
      have hindex : k.val ≠ i.val := by
        intro hki
        exact hk (Fin.ext hki)
      have hval : areaLawHorizontalPotentialTop
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
          (positionedRectangleTopLink o ho hL hT k) = 0 := by
        simp [areaLawHorizontalPotentialTop, positionedRectangleTopLink, cellDegree,
          positionedHorizontalLink_axes, coordBase, hcoord, hindex]
      rw [hval]
      simp [hne]
  · obtain ⟨k, rfl⟩ := hl
    have hne : positionedRectangleLeftLink o ho hL hT k ≠
        positionedRectangleTopLink o ho hL hT i := by
      intro h
      exact positionedHorizontal_ne_vertical o ho _ _ _ _ h.symm
    have hval : areaLawHorizontalPotentialTop
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleLeftLink o ho hL hT k) = 0 := by
      simp [areaLawHorizontalPotentialTop, positionedRectangleLeftLink,
        cellDegree, positionedVerticalLink_axes]
    rw [hval]
    simp [hne]
  · obtain ⟨k, rfl⟩ := hr
    have hne : positionedRectangleRightLink o ho hL hT k ≠
        positionedRectangleTopLink o ho hL hT i := by
      intro h
      exact positionedHorizontal_ne_vertical o ho _ _ _ _ h.symm
    have hval : areaLawHorizontalPotentialTop
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleRightLink o ho hL hT k) = 0 := by
      simp [areaLawHorizontalPotentialTop, positionedRectangleRightLink,
        cellDegree, positionedVerticalLink_axes]
    rw [hval]
    simp [hne]
private theorem positionedVerticalPotentialLeft_shape {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) (c : Cell 4 B)
    (hc : c ∈ positionedRectanglePerimeter o ho hL hT) :
    areaLawVerticalPotentialLeft
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c =
      if c = positionedRectangleLeftLink o ho hL hT j then -1 else 0 := by
  rcases positionedRectanglePerimeter_mem_cases o ho hL hT c hc with hb | ht | hl | hr
  · obtain ⟨k, rfl⟩ := hb
    have hne : positionedRectangleBottomLink o ho hL hT k ≠
        positionedRectangleLeftLink o ho hL hT j := by
      intro h
      exact positionedHorizontal_ne_vertical o ho _ _ _ _ h
    have hval : areaLawVerticalPotentialLeft
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleBottomLink o ho hL hT k) = 0 := by
      simp [areaLawVerticalPotentialLeft, positionedRectangleBottomLink,
        cellDegree, positionedHorizontalLink_axes]
    rw [hval]
    simp [hne]
  · obtain ⟨k, rfl⟩ := ht
    have hne : positionedRectangleTopLink o ho hL hT k ≠
        positionedRectangleLeftLink o ho hL hT j := by
      intro h
      exact positionedHorizontal_ne_vertical o ho _ _ _ _ h
    have hval : areaLawVerticalPotentialLeft
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleTopLink o ho hL hT k) = 0 := by
      simp [areaLawVerticalPotentialLeft, positionedRectangleTopLink,
        cellDegree, positionedHorizontalLink_axes]
    rw [hval]
    simp [hne]
  · obtain ⟨k, rfl⟩ := hl
    by_cases hk : k = j
    · subst k
      have hval : areaLawVerticalPotentialLeft
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
          (positionedRectangleLeftLink o ho hL hT j) = -1 := by
        simp [areaLawVerticalPotentialLeft, positionedRectangleLeftLink, cellDegree,
          positionedVerticalLink_axes, coordBase]
      simpa using hval
    · have hcoord : o 1 + k.val ≠ o 1 + j.val := by
        intro heq
        exact hk (Fin.ext (Nat.add_left_cancel heq))
      have hne : positionedRectangleLeftLink o ho hL hT k ≠
          positionedRectangleLeftLink o ho hL hT j := by
        intro heq
        apply hcoord
        have h := congrArg (fun z => coordBase (z 1)) heq
        simpa [positionedRectangleLeftLink, coordBase] using h
      have hindex : k.val ≠ j.val := by
        intro hkj
        exact hk (Fin.ext hkj)
      have hval : areaLawVerticalPotentialLeft
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
          (positionedRectangleLeftLink o ho hL hT k) = 0 := by
        simp [areaLawVerticalPotentialLeft, positionedRectangleLeftLink, cellDegree,
          positionedVerticalLink_axes, coordBase, hindex]
      rw [hval]
      simp [hne, hindex]
  · obtain ⟨k, rfl⟩ := hr
    have hcut : ¬ o 0 + L ≤ o 0 + i.val := by omega
    have hne : positionedRectangleRightLink o ho hL hT k ≠
        positionedRectangleLeftLink o ho hL hT j := by
      intro heq
      have h := congrArg (fun z => coordBase (z 0)) heq
      simp [positionedRectangleRightLink, positionedRectangleLeftLink,
        coordBase] at h
      omega
    have hval : areaLawVerticalPotentialLeft
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleRightLink o ho hL hT k) = 0 := by
      simp [areaLawVerticalPotentialLeft, positionedRectangleRightLink, cellDegree,
        positionedVerticalLink_axes, coordBase, hcut]
    rw [hval]
    simp [hne]

private theorem positionedLocalPotential_shape {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) (c : Cell 4 B)
    (hc : c ∈ positionedRectanglePerimeter o ho hL hT) :
    areaLocalPotential
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c =
      if c = positionedRectangleRightLink o ho hL hT j then 1 else 0 := by
  rcases positionedRectanglePerimeter_mem_cases o ho hL hT c hc with hb | ht | hl | hr
  · obtain ⟨k, rfl⟩ := hb
    have hne : positionedRectangleBottomLink o ho hL hT k ≠
        positionedRectangleRightLink o ho hL hT j := by
      intro h
      exact positionedHorizontal_ne_vertical o ho _ _ _ _ h
    have hval : areaLocalPotential
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleBottomLink o ho hL hT k) = 0 := by
      simp [areaLocalPotential, positionedRectangleBottomLink,
        cellDegree, positionedHorizontalLink_axes]
    rw [hval]
    simp [hne]
  · obtain ⟨k, rfl⟩ := ht
    have hne : positionedRectangleTopLink o ho hL hT k ≠
        positionedRectangleRightLink o ho hL hT j := by
      intro h
      exact positionedHorizontal_ne_vertical o ho _ _ _ _ h
    have hval : areaLocalPotential
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleTopLink o ho hL hT k) = 0 := by
      simp [areaLocalPotential, positionedRectangleTopLink,
        cellDegree, positionedHorizontalLink_axes]
    rw [hval]
    simp [hne]
  · obtain ⟨k, rfl⟩ := hl
    have hcut : ¬ o 0 + i.val < o 0 := by omega
    have hne : positionedRectangleLeftLink o ho hL hT k ≠
        positionedRectangleRightLink o ho hL hT j := by
      intro h
      have hcoord := congrArg (fun z => coordBase (z 0)) h
      simp [positionedRectangleLeftLink, positionedRectangleRightLink,
        coordBase] at hcoord
      omega
    have hval : areaLocalPotential
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
        (positionedRectangleLeftLink o ho hL hT k) = 0 := by
      simp [areaLocalPotential, positionedRectangleLeftLink, cellDegree,
        positionedVerticalLink_axes, coordBase, hcut]
    rw [hval]
    simp [hne]
  · obtain ⟨k, rfl⟩ := hr
    by_cases hk : k = j
    · subst k
      have hcut : o 0 + i.val < o 0 + L := Nat.add_lt_add_left i.isLt (o 0)
      have hval : areaLocalPotential
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
          (positionedRectangleRightLink o ho hL hT j) = 1 := by
        simp [areaLocalPotential, positionedRectangleRightLink, cellDegree,
          positionedVerticalLink_axes, coordBase, hcut]
      simpa using hval
    · have hcoord : o 1 + k.val ≠ o 1 + j.val := by
        intro heq
        exact hk (Fin.ext (Nat.add_left_cancel heq))
      have hne : positionedRectangleRightLink o ho hL hT k ≠
          positionedRectangleRightLink o ho hL hT j := by
        intro heq
        apply hcoord
        have h := congrArg (fun z => coordBase (z 1)) heq
        simpa [positionedRectangleRightLink, coordBase] using h
      have hindex : k.val ≠ j.val := by
        intro hkj
        exact hk (Fin.ext hkj)
      have hval : areaLocalPotential
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
          (positionedRectangleRightLink o ho hL hT k) = 0 := by
        simp [areaLocalPotential, positionedRectangleRightLink, cellDegree,
          positionedVerticalLink_axes, coordBase, hindex]
      rw [hval]
      simp [hne, hindex]

set_option linter.unusedSimpArgs true

private theorem positioned_integerCellPairing_eq_single {B : Box 4}
    (f : Cell 4 B → ℤ) (q : Chain 4 B) (e : Cell 4 B) (v : ℤ)
    (hshape : ∀ c ∈ q.support,
      (c = e → f c = v) ∧ (c ≠ e → f c = 0)) :
    integerCellPairing f q = q e * v := by
  classical
  unfold integerCellPairing
  calc
    (∑ c : Cell 4 B, q c * f c) =
        ∑ c : Cell 4 B, if c = e then q c * v else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          by_cases hmem : c ∈ q.support
          · by_cases he : c = e
            · subst c
              simp [hshape e hmem]
            · simp [he, hshape c hmem]
          · have hzero : q c = 0 := Finsupp.notMem_support_iff.mp hmem
            simp [hzero]
    _ = q e * v := by simp

private theorem positionedIntegerPairing_bottom_eq_link {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T) (i : Fin L) (j : Fin T)
    (q : Chain 4 B)
    (hq : q.support ⊆ positionedRectanglePerimeter o ho hL hT) :
    integerCellPairing
      (areaLawHorizontalPotentialBottom
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩) q =
      q (positionedRectangleBottomLink o ho hL hT i) := by
  have hshape : ∀ c ∈ q.support,
      (c = positionedRectangleBottomLink o ho hL hT i →
        areaLawHorizontalPotentialBottom
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c = 1) ∧
      (c ≠ positionedRectangleBottomLink o ho hL hT i →
        areaLawHorizontalPotentialBottom
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c = 0) := by
    intro c hc
    have hs := positionedHorizontalPotentialBottom_shape o ho hL hT hLpos hTpos i j c (hq hc)
    constructor <;> intro he <;> rw [hs] <;> simp [he]
  simpa using positioned_integerCellPairing_eq_single _ q
    (positionedRectangleBottomLink o ho hL hT i) 1 hshape

private theorem positionedIntegerPairing_top_eq_link {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T) (i : Fin L) (j : Fin T)
    (q : Chain 4 B)
    (hq : q.support ⊆ positionedRectanglePerimeter o ho hL hT) :
    integerCellPairing
      (areaLawHorizontalPotentialTop
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩) q =
      q (positionedRectangleTopLink o ho hL hT i) * (-1) := by
  have hshape : ∀ c ∈ q.support,
      (c = positionedRectangleTopLink o ho hL hT i →
        areaLawHorizontalPotentialTop
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c = -1) ∧
      (c ≠ positionedRectangleTopLink o ho hL hT i →
        areaLawHorizontalPotentialTop
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c = 0) := by
    intro c hc
    have hs := positionedHorizontalPotentialTop_shape o ho hL hT hLpos hTpos i j c (hq hc)
    constructor <;> intro he <;> rw [hs] <;> simp [he]
  exact positioned_integerCellPairing_eq_single _ q
    (positionedRectangleTopLink o ho hL hT i) (-1) hshape

private theorem positionedIntegerPairing_left_eq_link {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) (q : Chain 4 B)
    (hq : q.support ⊆ positionedRectanglePerimeter o ho hL hT) :
    integerCellPairing
      (areaLawVerticalPotentialLeft
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩) q =
      q (positionedRectangleLeftLink o ho hL hT j) * (-1) := by
  have hshape : ∀ c ∈ q.support,
      (c = positionedRectangleLeftLink o ho hL hT j →
        areaLawVerticalPotentialLeft
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c = -1) ∧
      (c ≠ positionedRectangleLeftLink o ho hL hT j →
        areaLawVerticalPotentialLeft
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c = 0) := by
    intro c hc
    have hs := positionedVerticalPotentialLeft_shape o ho hL hT i j c (hq hc)
    constructor <;> intro he <;> rw [hs] <;> simp [he]
  exact positioned_integerCellPairing_eq_single _ q
    (positionedRectangleLeftLink o ho hL hT j) (-1) hshape

private theorem positionedIntegerPairing_right_eq_link {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (i : Fin L) (j : Fin T) (q : Chain 4 B)
    (hq : q.support ⊆ positionedRectanglePerimeter o ho hL hT) :
    integerCellPairing
      (areaLocalPotential
        ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
        ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩) q =
      q (positionedRectangleRightLink o ho hL hT j) := by
  have hshape : ∀ c ∈ q.support,
      (c = positionedRectangleRightLink o ho hL hT j →
        areaLocalPotential
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c = 1) ∧
      (c ≠ positionedRectangleRightLink o ho hL hT j →
        areaLocalPotential
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩ c = 0) := by
    intro c hc
    have hs := positionedLocalPotential_shape o ho hL hT i j c (hq hc)
    constructor <;> intro he <;> rw [hs] <;> simp [he]
  simpa using positioned_integerCellPairing_eq_single _ q
    (positionedRectangleRightLink o ho hL hT j) 1 hshape

theorem positionedBoundaryPotential_mode_pairings {B : Box 4}
    (a : Fin (B 0)) (b : Fin (B 1)) (m : PrimalPlaquettes B → ℤ) :
    integerCellPairing (areaLawHorizontalPotentialBottom a b)
        (boundary (plaquetteModeChain m)) =
      integerCellPairing (areaLocalPotential a b)
        (boundary (plaquetteModeChain m)) ∧
    integerCellPairing (areaLawHorizontalPotentialTop a b)
        (boundary (plaquetteModeChain m)) =
      integerCellPairing (areaLocalPotential a b)
        (boundary (plaquetteModeChain m)) ∧
    integerCellPairing (areaLawVerticalPotentialLeft a b)
        (boundary (plaquetteModeChain m)) =
      integerCellPairing (areaLocalPotential a b)
        (boundary (plaquetteModeChain m)) := by
  have hhom := plaquetteModeChain_homogeneousSupport m
  refine ⟨?_, ?_, ?_⟩
  · exact integerCellPairing_boundary_eq_of_same_plaquette_curl _ _ _ hhom
      (by intro p; rw [areaLawHorizontalPotentialBottom_curl, areaLocalPotential_curl])
  · exact integerCellPairing_boundary_eq_of_same_plaquette_curl _ _ _ hhom
      (by intro p; rw [areaLawHorizontalPotentialTop_curl, areaLocalPotential_curl])
  · exact integerCellPairing_boundary_eq_of_same_plaquette_curl _ _ _ hhom
      (by intro p; rw [areaLawVerticalPotentialLeft_curl, areaLocalPotential_curl])

private theorem positionedComponentRemainder_boundary_support_disjoint {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    Disjoint
      (Finset.univ.filter fun l : PrimalLinks B =>
        (boundary (plaquetteModeChain (plaquetteModeComponentField m c))) l.1 ≠ 0)
      (Finset.univ.filter fun l : PrimalLinks B =>
        (boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c))) l.1 ≠ 0) := by
  have hdisj : Disjoint (plaquetteModeComponentSupport m c)
      (plaquetteModeComponentRemainderSupport m c) := by
    change Disjoint (plaquetteModeComponentSupport m c)
      (plaquetteFieldSupport m \ plaquetteModeComponentSupport m c)
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hq).2 hp
  have hsep : ∀ p ∈ plaquetteModeComponentSupport m c,
      ∀ q ∈ plaquetteModeComponentRemainderSupport m c,
        ¬ (plaquetteLinkGraph (B := B)).Adj p q := by
    intro p hp q hq hadj
    have hqm : m q ≠ 0 := by
      have hq' := Finset.mem_sdiff.mp hq
      exact (Finset.mem_filter.mp hq'.1).2
    let d := (nonzeroPlaquetteGraph m).connectedComponentMk ⟨q, hqm⟩
    have hqC : q ∉ plaquetteModeComponentSupport m c :=
      (Finset.mem_sdiff.mp hq).2
    have hcd : c ≠ d := by
      intro h
      apply hqC
      rw [mem_plaquetteModeComponentSupport_iff_componentMk m q hqm c]
      exact h.symm
    exact plaquetteModeComponentSupport_nonadjacent m hcd hp
      ((mem_plaquetteModeComponentSupport_iff_componentMk m q hqm d).2 rfl)
      hadj
  have hset := plaquetteFieldChainOnSet_boundary_support_disjoint
    m (plaquetteModeComponentSupport m c)
    (plaquetteModeComponentRemainderSupport m c) hdisj hsep
  simpa [plaquetteModeComponentField_chain_eq_set,
    plaquetteModeComponentRemainder_chain_eq_set] using hset

theorem positionedComponentBoundary_support_subset_source
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    (boundary (plaquetteModeChain (plaquetteModeComponentField m c))).support ⊆
      (positionedRectangleLoop o ho L T hL hT).support := by
  classical
  let q := boundary (plaquetteModeChain (plaquetteModeComponentField m c))
  let r := boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c))
  have hsourceChain := (plaquetteModeDivergence_eq_boundary m
    (positionedRectangleSheet o ho L T hL hT)
    (positionedRectangleSheet_homogeneousSupport o ho hL hT)).mp hsource
  have hsum : q + r = positionedRectangleLoop o ho L T hL hT := by
    dsimp [q, r, positionedRectangleLoop]
    calc
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) +
          boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
          boundary (plaquetteModeChain (plaquetteModeComponentField m c) +
            plaquetteModeChain (plaquetteModeComponentRemainder m c)) := by
              symm
              exact map_add boundary _ _
      _ = boundary (plaquetteModeChain m) := by
            rw [← plaquetteModeChain_eq_component_add_remainder]
      _ = boundary (positionedRectangleSheet o ho L T hL hT) := hsourceChain
  intro l hl
  have hdeg : cellDegree l = 1 :=
    integerBoundary_homogeneousSupport
      (plaquetteModeChain (plaquetteModeComponentField m c)) 2 (by omega)
      (plaquetteModeChain_homogeneousSupport _)
      l (by simpa [q] using hl)
  let e : PrimalLinks B := ⟨l, hdeg⟩
  have hq : q l ≠ 0 := by simpa [q] using Finsupp.mem_support_iff.mp hl
  have hqmem : e ∈ Finset.univ.filter fun z : PrimalLinks B => q z.1 ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e] using hq⟩
  have hdisj := positionedComponentRemainder_boundary_support_disjoint m c
  have hrnot : e ∉ Finset.univ.filter fun z : PrimalLinks B => r z.1 ≠ 0 := by
    intro hrmem
    exact (Finset.disjoint_left.mp hdisj) hqmem hrmem
  have hrzero : r l = 0 := by
    by_contra hr
    apply hrnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e] using hr⟩
  have hcoeff := congrArg (fun z : Chain 4 B => z l) hsum
  have hloop : (positionedRectangleLoop o ho L T hL hT) l ≠ 0 := by
    rw [← hcoeff]
    simp [q, r, hq, hrzero]
  exact Finsupp.mem_support_iff.mpr hloop

private theorem positionedComponentBoundary_side_relations {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent)
    (i : Fin L) (j : Fin T)
    (hq : (boundary (plaquetteModeChain (plaquetteModeComponentField m c))).support ⊆
      positionedRectanglePerimeter o ho hL hT) :
    (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (positionedRectangleBottomLink o ho hL hT i) =
      (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (positionedRectangleRightLink o ho hL hT j) ∧
    (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (positionedRectangleTopLink o ho hL hT i) * (-1) =
      (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (positionedRectangleRightLink o ho hL hT j) ∧
    (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (positionedRectangleLeftLink o ho hL hT j) * (-1) =
      (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (positionedRectangleRightLink o ho hL hT j) := by
  let q := boundary (plaquetteModeChain (plaquetteModeComponentField m c))
  let a : Fin (B 0) := ⟨o 0 + i.val,
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
  let b : Fin (B 1) := ⟨o 1 + j.val,
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩
  have hpairs := positionedBoundaryPotential_mode_pairings a b
    (plaquetteModeComponentField m c)
  have hbottom := hpairs.1
  have htop := hpairs.2.1
  have hleft := hpairs.2.2
  rw [positionedIntegerPairing_bottom_eq_link o ho hL hT hLpos hTpos i j q hq] at hbottom
  rw [positionedIntegerPairing_right_eq_link o ho hL hT i j q hq] at hbottom
  rw [positionedIntegerPairing_top_eq_link o ho hL hT hLpos hTpos i j q hq] at htop
  rw [positionedIntegerPairing_right_eq_link o ho hL hT i j q hq] at htop
  rw [positionedIntegerPairing_left_eq_link o ho hL hT i j q hq] at hleft
  rw [positionedIntegerPairing_right_eq_link o ho hL hT i j q hq] at hleft
  exact ⟨by simpa [q] using hbottom, by simpa [q] using htop,
    by simpa [q] using hleft⟩

private theorem positionedRectangleLoop_side_coefficients {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T) :
    (∀ i : Fin L,
      (positionedRectangleLoop o ho L T hL hT)
        (positionedRectangleBottomLink o ho hL hT i) = 1) ∧
    (∀ i : Fin L,
      (positionedRectangleLoop o ho L T hL hT)
        (positionedRectangleTopLink o ho hL hT i) = -1) ∧
    (∀ j : Fin T,
      (positionedRectangleLoop o ho L T hL hT)
        (positionedRectangleLeftLink o ho hL hT j) = -1) ∧
    (∀ j : Fin T,
      (positionedRectangleLoop o ho L T hL hT)
        (positionedRectangleRightLink o ho hL hT j) = 1) := by
  have hperim := positionedRectangleLoop_support_subset_perimeter o ho hL hT
  have hhom := positionedRectangleSheet_homogeneousSupport o ho hL hT
  have hcurlBottom (i : Fin L) (j : Fin T) (p : PrimalPlaquettes B) :
      integerCellPairing
          (areaLawHorizontalPotentialBottom
            ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
            ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
          (boundary (basisChain p.1)) =
        integerCellPairing
          (areaLocalPotential
            ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
            ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
          (boundary (basisChain p.1)) := by
    rw [areaLawHorizontalPotentialBottom_curl, areaLocalPotential_curl]
  have hcurlTop (i : Fin L) (j : Fin T) (p : PrimalPlaquettes B) :
      integerCellPairing
          (areaLawHorizontalPotentialTop
            ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
            ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
          (boundary (basisChain p.1)) =
        integerCellPairing
          (areaLocalPotential
            ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
            ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
          (boundary (basisChain p.1)) := by
    rw [areaLawHorizontalPotentialTop_curl, areaLocalPotential_curl]
  have hcurlLeft (i : Fin L) (j : Fin T) (p : PrimalPlaquettes B) :
      integerCellPairing
          (areaLawVerticalPotentialLeft
            ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
            ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
          (boundary (basisChain p.1)) =
        integerCellPairing
          (areaLocalPotential
            ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
            ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
          (boundary (basisChain p.1)) := by
    rw [areaLawVerticalPotentialLeft_curl, areaLocalPotential_curl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    let j : Fin T := ⟨0, hTpos⟩
    have hpair := integerCellPairing_boundary_eq_of_same_plaquette_curl
      _ _ (positionedRectangleSheet o ho L T hL hT) hhom (hcurlBottom i j)
    have heq : integerCellPairing
        (areaLawHorizontalPotentialBottom
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
        (positionedRectangleLoop o ho L T hL hT) = 1 := by
      change integerCellPairing _ (boundary (positionedRectangleSheet o ho L T hL hT)) = 1
      calc
        _ = integerCellPairing
            (areaLocalPotential
              ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
              ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
            (boundary (positionedRectangleSheet o ho L T hL hT)) := hpair
        _ = 1 := areaLocalPotential_pairing_positionedRectangleLoop o ho hL hT i j
    rw [positionedIntegerPairing_bottom_eq_link o ho hL hT hLpos hTpos i j
      (positionedRectangleLoop o ho L T hL hT) hperim] at heq
    exact heq
  · intro i
    let j : Fin T := ⟨0, hTpos⟩
    have hpair := integerCellPairing_boundary_eq_of_same_plaquette_curl
      _ _ (positionedRectangleSheet o ho L T hL hT) hhom (hcurlTop i j)
    have heq : integerCellPairing
        (areaLawHorizontalPotentialTop
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
        (positionedRectangleLoop o ho L T hL hT) = 1 := by
      change integerCellPairing _ (boundary (positionedRectangleSheet o ho L T hL hT)) = 1
      calc
        _ = integerCellPairing
            (areaLocalPotential
              ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
              ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
            (boundary (positionedRectangleSheet o ho L T hL hT)) := hpair
        _ = 1 := areaLocalPotential_pairing_positionedRectangleLoop o ho hL hT i j
    rw [positionedIntegerPairing_top_eq_link o ho hL hT hLpos hTpos i j
      (positionedRectangleLoop o ho L T hL hT) hperim] at heq
    nlinarith
  · intro j
    let i : Fin L := ⟨0, hLpos⟩
    have hpair := integerCellPairing_boundary_eq_of_same_plaquette_curl
      _ _ (positionedRectangleSheet o ho L T hL hT) hhom (hcurlLeft i j)
    have heq : integerCellPairing
        (areaLawVerticalPotentialLeft
          ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
          ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
        (positionedRectangleLoop o ho L T hL hT) = 1 := by
      change integerCellPairing _ (boundary (positionedRectangleSheet o ho L T hL hT)) = 1
      calc
        _ = integerCellPairing
            (areaLocalPotential
              ⟨o 0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt (o 0)) hL⟩
              ⟨o 1 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (o 1)) hT⟩)
            (boundary (positionedRectangleSheet o ho L T hL hT)) := hpair
        _ = 1 := areaLocalPotential_pairing_positionedRectangleLoop o ho hL hT i j
    rw [positionedIntegerPairing_left_eq_link o ho hL hT i j
      (positionedRectangleLoop o ho L T hL hT) hperim] at heq
    nlinarith
  · intro j
    exact (positionedIntegerPairing_right_eq_link o ho hL hT
      (⟨0, hLpos⟩ : Fin L) j (positionedRectangleLoop o ho L T hL hT) hperim).symm.trans
      (areaLocalPotential_pairing_positionedRectangleLoop o ho hL hT ⟨0, hLpos⟩ j)

private theorem positionedComponentBoundary_sum_eq_source {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    boundary (plaquetteModeChain (plaquetteModeComponentField m c)) +
        boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
      positionedRectangleLoop o ho L T hL hT := by
  have hsourceChain := (plaquetteModeDivergence_eq_boundary m
    (positionedRectangleSheet o ho L T hL hT)
    (positionedRectangleSheet_homogeneousSupport o ho hL hT)).mp hsource
  calc
    boundary (plaquetteModeChain (plaquetteModeComponentField m c)) +
        boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
        boundary (plaquetteModeChain (plaquetteModeComponentField m c) +
          plaquetteModeChain (plaquetteModeComponentRemainder m c)) := by
            symm
            exact map_add boundary _ _
    _ = boundary (plaquetteModeChain m) := by
          rw [← plaquetteModeChain_eq_component_add_remainder]
    _ = boundary (positionedRectangleSheet o ho L T hL hT) := hsourceChain
    _ = positionedRectangleLoop o ho L T hL hT := rfl

private theorem positionedPlaquetteModeComponentBoundary_eq_zero_or_loop
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    boundary (plaquetteModeChain (plaquetteModeComponentField m c)) = 0 ∨
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) =
        positionedRectangleLoop o ho L T hL hT := by
  classical
  let q := boundary (plaquetteModeChain (plaquetteModeComponentField m c))
  let r := boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c))
  have hqSource := positionedComponentBoundary_support_subset_source
    o ho hL hT m c hsource
  have hqPerim : q.support ⊆ positionedRectanglePerimeter o ho hL hT := by
    intro x hx
    exact positionedRectangleLoop_support_subset_perimeter o ho hL hT (hqSource hx)
  have hSide (i : Fin L) (j : Fin T) :
      q (positionedRectangleBottomLink o ho hL hT i) =
          q (positionedRectangleRightLink o ho hL hT j) ∧
      q (positionedRectangleTopLink o ho hL hT i) * (-1) =
          q (positionedRectangleRightLink o ho hL hT j) ∧
      q (positionedRectangleLeftLink o ho hL hT j) * (-1) =
          q (positionedRectangleRightLink o ho hL hT j) := by
    simpa [q] using positionedComponentBoundary_side_relations
      o ho hL hT hLpos hTpos m c i j hqPerim
  have hloopSide := positionedRectangleLoop_side_coefficients
    o ho hL hT hLpos hTpos
  by_cases hqzero : q = 0
  · exact Or.inl (by simpa [q] using hqzero)
  · have hqhom : homogeneousSupport q 1 := by
      dsimp [q]
      exact integerBoundary_homogeneousSupport
        (plaquetteModeChain (plaquetteModeComponentField m c)) 2 (by omega)
        (plaquetteModeChain_homogeneousSupport _)
    have hqNonempty : q.support.Nonempty := Finsupp.support_nonempty_iff.mpr hqzero
    obtain ⟨x, hx⟩ := hqNonempty
    have hxdeg : cellDegree x = 1 := hqhom x hx
    let e : PrimalLinks B := ⟨x, hxdeg⟩
    have hxe : q e.1 ≠ 0 := by
      simpa [e] using Finsupp.mem_support_iff.mp hx
    have hxperim : e.1 ∈ positionedRectanglePerimeter o ho hL hT := by
      exact positionedRectangleLoop_support_subset_perimeter o ho hL hT
        (hqSource (by simpa [q, e] using hx))
    let i0 : Fin L := ⟨0, hLpos⟩
    let j0 : Fin T := ⟨0, hTpos⟩
    have hexistsRight : ∃ j : Fin T,
        q (positionedRectangleRightLink o ho hL hT j) ≠ 0 := by
      obtain hbottom | htop | hleft | hright :=
        positionedRectanglePerimeter_mem_cases o ho hL hT e.1 hxperim
      · obtain ⟨i, hxi⟩ := hbottom
        have hval : q (positionedRectangleBottomLink o ho hL hT i) ≠ 0 := by
          rw [← hxi]
          exact hxe
        refine ⟨j0, ?_⟩
        rw [← (hSide i j0).1]
        exact hval
      · obtain ⟨i, hxi⟩ := htop
        have hval : q (positionedRectangleTopLink o ho hL hT i) ≠ 0 := by
          rw [← hxi]
          exact hxe
        refine ⟨j0, ?_⟩
        intro hz
        apply hval
        have hzero : q (positionedRectangleTopLink o ho hL hT i) * (-1) = 0 :=
          (hSide i j0).2.1.trans hz
        exact (mul_eq_zero.mp hzero).resolve_right (by norm_num)
      · obtain ⟨j, hxj⟩ := hleft
        have hval : q (positionedRectangleLeftLink o ho hL hT j) ≠ 0 := by
          rw [← hxj]
          exact hxe
        refine ⟨j, ?_⟩
        intro hz
        apply hval
        have hzero : q (positionedRectangleLeftLink o ho hL hT j) * (-1) = 0 :=
          (hSide i0 j).2.2.trans hz
        exact (mul_eq_zero.mp hzero).resolve_right (by norm_num)
      · obtain ⟨j, hxj⟩ := hright
        refine ⟨j, ?_⟩
        rw [← hxj]
        exact hxe
    obtain ⟨jstar, hjStar⟩ := hexistsRight
    have hsum := positionedComponentBoundary_sum_eq_source o ho hL hT m c hsource
    let side : Cell 4 B := positionedRectangleRightLink o ho hL hT jstar
    let link : PrimalLinks B := ⟨side, by
      simp [side, positionedRectangleRightLink, cellDegree, positionedVerticalLink_axes]⟩
    have hqmem : link ∈ Finset.univ.filter fun z : PrimalLinks B => q z.1 ≠ 0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [link, side] using hjStar⟩
    have hdisj := positionedComponentRemainder_boundary_support_disjoint m c
    have hrnot : link ∉ Finset.univ.filter fun z : PrimalLinks B => r z.1 ≠ 0 := by
      intro hr
      exact (Finset.disjoint_left.mp hdisj) hqmem hr
    have hrzero : r side = 0 := by
      by_contra hne
      apply hrnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [link, side] using hne⟩
    have hcoeff := congrArg (fun z : Chain 4 B => z side) hsum
    have hright0 : q side = 1 := by
      have hloop := hloopSide.2.2.2 jstar
      have hcoeff' : q side = (positionedRectangleLoop o ho L T hL hT) side := by
        change q side + r side = (positionedRectangleLoop o ho L T hL hT) side at hcoeff
        simpa [hrzero] using hcoeff
      calc
        q side = (positionedRectangleLoop o ho L T hL hT) side := hcoeff'
        _ = 1 := by simpa [side] using hloop
    have hrightAll (j : Fin T) :
        q (positionedRectangleRightLink o ho hL hT j) = 1 := by
      calc
        q (positionedRectangleRightLink o ho hL hT j) =
            q (positionedRectangleBottomLink o ho hL hT i0) := (hSide i0 j).1.symm
        _ = q (positionedRectangleRightLink o ho hL hT jstar) := (hSide i0 jstar).1
        _ = 1 := by simpa [side] using hright0
    have hbottomAll (i : Fin L) :
        q (positionedRectangleBottomLink o ho hL hT i) = 1 := by
      calc
        _ = q (positionedRectangleRightLink o ho hL hT j0) := (hSide i j0).1
        _ = 1 := hrightAll j0
    have htopAll (i : Fin L) :
        q (positionedRectangleTopLink o ho hL hT i) = -1 := by
      have h := (hSide i j0).2.1
      rw [hrightAll j0] at h
      nlinarith
    have hleftAll (j : Fin T) :
        q (positionedRectangleLeftLink o ho hL hT j) = -1 := by
      have h := (hSide i0 j).2.2
      rw [hrightAll j] at h
      nlinarith
    have hqSupportPerim : q.support ⊆ positionedRectanglePerimeter o ho hL hT := hqPerim
    have hloopSupportPerim := positionedRectangleLoop_support_subset_perimeter o ho hL hT
    have hloopHom : homogeneousSupport (positionedRectangleLoop o ho L T hL hT) 1 := by
      rw [positionedRectangleLoop]
      exact integerBoundary_homogeneousSupport (positionedRectangleSheet o ho L T hL hT)
        2 (by omega) (positionedRectangleSheet_homogeneousSupport o ho hL hT)
    have hqeq : q = positionedRectangleLoop o ho L T hL hT := by
      ext x
      by_cases hdeg : cellDegree x = 1
      · by_cases hperim : x ∈ positionedRectanglePerimeter o ho hL hT
        · obtain hbottom | htop | hleft | hright :=
            positionedRectanglePerimeter_mem_cases o ho hL hT x hperim
          · obtain ⟨i, rfl⟩ := hbottom
            exact (hbottomAll i).trans (hloopSide.1 i).symm
          · obtain ⟨i, rfl⟩ := htop
            exact (htopAll i).trans (hloopSide.2.1 i).symm
          · obtain ⟨j, rfl⟩ := hleft
            exact (hleftAll j).trans (hloopSide.2.2.1 j).symm
          · obtain ⟨j, rfl⟩ := hright
            exact (hrightAll j).trans (hloopSide.2.2.2 j).symm
        · have hqzero' : q x = 0 := by
            by_contra hne
            apply hperim
            exact hqSupportPerim (Finsupp.mem_support_iff.mpr hne)
          have hloopzero : (positionedRectangleLoop o ho L T hL hT) x = 0 := by
            by_contra hne
            apply hperim
            exact hloopSupportPerim (Finsupp.mem_support_iff.mpr hne)
          simp [hqzero', hloopzero]
      · have hqzero' : q x = 0 := by
          by_contra hne
          exact hdeg (hqhom x (Finsupp.mem_support_iff.mpr hne))
        have hloopzero : (positionedRectangleLoop o ho L T hL hT) x = 0 := by
          by_contra hne
          exact hdeg (hloopHom x (Finsupp.mem_support_iff.mpr hne))
        simp [hqzero', hloopzero]
    exact Or.inr (by simpa [q] using hqeq)

private theorem exists_positionedPlaquetteModeComponent_with_source_boundary
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    ∃ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) =
        positionedRectangleLoop o ho L T hL hT := by
  classical
  by_contra hnone
  push Not at hnone
  have hcomponentZero (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) = 0 := by
    rcases positionedPlaquetteModeComponentBoundary_eq_zero_or_loop
      o ho hL hT hLpos hTpos m c hsource with hz | hs
    · exact hz
    · exact (hnone c hs).elim
  have htotal :
      (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
        boundary (plaquetteModeChain (plaquetteModeComponentField m c))) =
          positionedRectangleLoop o ho L T hL hT := by
    calc
      _ = boundary (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
          plaquetteModeChain (plaquetteModeComponentField m c)) := by rw [map_sum]
      _ = boundary (plaquetteModeChain m) := by rw [plaquetteModeChain_component_sum_eq]
      _ = boundary (positionedRectangleSheet o ho L T hL hT) :=
            (plaquetteModeDivergence_eq_boundary m
              (positionedRectangleSheet o ho L T hL hT)
              (positionedRectangleSheet_homogeneousSupport o ho hL hT)).mp hsource
      _ = positionedRectangleLoop o ho L T hL hT := rfl
  have hsumzero :
      (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
        boundary (plaquetteModeChain (plaquetteModeComponentField m c))) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    exact hcomponentZero c
  have hloopzero : positionedRectangleLoop o ho L T hL hT = 0 := by
    rw [← htotal, hsumzero]
  have hpair := areaTestPotential_pairing_positionedRectangleLoop o ho hL hT
  rw [hloopzero] at hpair
  have harea : (0 : ℤ) < (L * T : ℤ) := by
    exact_mod_cast Nat.mul_pos hLpos hTpos
  have hcast : (L * T : ℤ) = 0 := by simpa using hpair.symm
  exact (ne_of_gt harea) hcast

private theorem positioned_exists_nonzero_sum {α : Type*}
    (s : Finset α) (f : α → ℤ) (h : (∑ x ∈ s, f x) ≠ 0) :
    ∃ x ∈ s, f x ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  apply Finset.sum_eq_zero
  intro x hx
  exact hn x hx

/-! ### Positioned source components and roots -/

noncomputable def positionedRectangleSourceComponent {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    (nonzeroPlaquetteGraph m).ConnectedComponent :=
  Classical.choose (exists_positionedPlaquetteModeComponent_with_source_boundary
    o ho hL hT hLpos hTpos m hsource)

theorem positionedRectangleSourceComponent_boundary {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    boundary (plaquetteModeChain (plaquetteModeComponentField m
      (positionedRectangleSourceComponent o ho hL hT hLpos hTpos m hsource))) =
        positionedRectangleLoop o ho L T hL hT :=
  Classical.choose_spec (exists_positionedPlaquetteModeComponent_with_source_boundary
    o ho hL hT hLpos hTpos m hsource)

theorem positionedRectangleSourceComponent_remainder_divergence_zero
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    plaquetteModeDivergence (plaquetteModeComponentRemainder m
      (positionedRectangleSourceComponent o ho hL hT hLpos hTpos m hsource)) = 0 := by
  let c := positionedRectangleSourceComponent o ho hL hT hLpos hTpos m hsource
  have htotal : boundary (plaquetteModeChain m) =
      positionedRectangleLoop o ho L T hL hT :=
    (plaquetteModeDivergence_eq_boundary m
      (positionedRectangleSheet o ho L T hL hT)
      (positionedRectangleSheet_homogeneousSupport o ho hL hT)).mp hsource
  have hsum :
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) +
        boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
          boundary (plaquetteModeChain m) := by
    rw [← map_add, ← plaquetteModeChain_eq_component_add_remainder]
  have hrem : boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) = 0 := by
    rw [positionedRectangleSourceComponent_boundary o ho hL hT hLpos hTpos m hsource] at hsum
    rw [htotal] at hsum
    have hcancel :
        positionedRectangleLoop o ho L T hL hT +
            boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
          positionedRectangleLoop o ho L T hL hT + 0 := by
      simpa using hsum
    exact add_left_cancel hcancel
  have hdiv := (plaquetteModeDivergence_eq_boundary
    (plaquetteModeComponentRemainder m c) 0 (by intro x hx; simp at hx)).2 (by
      simpa [map_zero] using hrem)
  have hfreqzero : primalSheetLoopFrequency (0 : Chain 4 B) = 0 := by
    funext l
    simp [primalSheetLoopFrequency]
  have hdiv' : plaquetteModeDivergence (plaquetteModeComponentRemainder m c) =
      primalSheetLoopFrequency (0 : Chain 4 B) := by simpa using hdiv
  exact hdiv'.trans hfreqzero

@[expose] noncomputable def positionedRectangleBoundaryLinks {B : Box 4}
    {L T : ℕ} (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) : Finset (PrimalLinks B) :=
  Finset.univ.filter fun l => positionedRectangleLoop o ho L T hL hT l.1 ≠ 0

@[expose] noncomputable def positionedRectangleSourceRootPlaquettes {B : Box 4}
    {L T : ℕ} (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) : Finset (PrimalPlaquettes B) :=
  (positionedRectangleBoundaryLinks o ho hL hT).biUnion fun l =>
    Finset.univ.filter fun p : PrimalPlaquettes B => l ∈ plaquetteBoundaryLinks p

private theorem positionedRectangleBoundaryLinks_subset_faces {B : Box 4}
    {L T : ℕ} (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) :
    positionedRectangleBoundaryLinks o ho hL hT ⊆
      (Finset.univ : Finset (Fin L × Fin T)).biUnion fun x =>
        plaquetteBoundaryLinks
          (⟨positionedRectanglePlaquette o ho hL hT x.1 x.2, by
            rw [cellDegree, positionedRectanglePlaquette_axes]
            simp⟩ : PrimalPlaquettes B) := by
  classical
  intro l hl
  have hcoef :
      positionedRectangleLoop o ho L T hL hT l.1 =
        ∑ x : Fin L × Fin T,
          (boundary (basisChain (positionedRectanglePlaquette o ho hL hT x.1 x.2))) l.1 := by
    rw [positionedRectangleLoop, positionedRectangleSheet, map_sum,
      finsupp_finset_sum_apply]
  have hsum : (∑ x : Fin L × Fin T,
      (boundary (basisChain (positionedRectanglePlaquette o ho hL hT x.1 x.2))) l.1) ≠ 0 := by
    rw [← hcoef]
    exact (Finset.mem_filter.mp hl).2
  obtain ⟨x, hx, hxne⟩ := positioned_exists_nonzero_sum
    (Finset.univ : Finset (Fin L × Fin T))
    (fun x => (boundary (basisChain
      (positionedRectanglePlaquette o ho hL hT x.1 x.2))) l.1) hsum
  refine Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, ?_⟩
  let p : PrimalPlaquettes B := ⟨positionedRectanglePlaquette o ho hL hT x.1 x.2, by
    rw [cellDegree, positionedRectanglePlaquette_axes]
    simp⟩
  have hface : (boundary (Finsupp.single p.1 (1 : ℤ))) l.1 ≠ 0 := by
    simpa [p, basisChain] using hxne
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hface⟩

theorem positionedRectangleSourceRootPlaquettes_card_le {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) :
    (positionedRectangleSourceRootPlaquettes o ho hL hT).card ≤ 24 * (L * T) := by
  classical
  let faces : Finset (PrimalPlaquettes B) := Finset.univ.image fun x : Fin L × Fin T =>
    (⟨positionedRectanglePlaquette o ho hL hT x.1 x.2, by
      rw [cellDegree, positionedRectanglePlaquette_axes]
      simp⟩ : PrimalPlaquettes B)
  let faceLinks : Finset (PrimalLinks B) := faces.biUnion plaquetteBoundaryLinks
  have hcover : positionedRectangleBoundaryLinks o ho hL hT ⊆ faceLinks := by
    intro l hl
    rcases Finset.mem_biUnion.mp
      (positionedRectangleBoundaryLinks_subset_faces o ho hL hT hl) with ⟨x, hx, hlink⟩
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, hlink⟩
  have hfacesCard : faces.card ≤ L * T := by
    dsimp [faces]
    calc
      _ ≤ (Finset.univ : Finset (Fin L × Fin T)).card := Finset.card_image_le
      _ = L * T := by simp
  have hlinks : (positionedRectangleBoundaryLinks o ho hL hT).card ≤ 4 * (L * T) := by
    have hfaceLinks : faceLinks.card ≤ ∑ p ∈ faces, (plaquetteBoundaryLinks p).card :=
      Finset.card_biUnion_le
    have hsum : (∑ p ∈ faces, (plaquetteBoundaryLinks p).card) ≤ ∑ _p ∈ faces, 4 := by
      apply Finset.sum_le_sum
      intro p hp
      exact plaquetteBoundaryLinks_card_le_four p
    have hsum' : (∑ _p ∈ faces, 4) ≤ 4 * (L * T) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right 4 hfacesCard
    exact (Finset.card_le_card hcover).trans (hfaceLinks.trans (hsum.trans hsum'))
  have hrootCover :
      (positionedRectangleSourceRootPlaquettes o ho hL hT).card ≤
        ∑ l ∈ positionedRectangleBoundaryLinks o ho hL hT,
          (Finset.univ.filter fun p : PrimalPlaquettes B =>
            l ∈ plaquetteBoundaryLinks p).card := by
    dsimp [positionedRectangleSourceRootPlaquettes]
    exact Finset.card_biUnion_le
  have hsum :
      (∑ l ∈ positionedRectangleBoundaryLinks o ho hL hT,
        (Finset.univ.filter fun p : PrimalPlaquettes B =>
          l ∈ plaquetteBoundaryLinks p).card) ≤
        ∑ _l ∈ positionedRectangleBoundaryLinks o ho hL hT, 6 := by
    apply Finset.sum_le_sum
    intro l hl
    exact plaquettesAtLink_card_le_six l
  have hsum' :
      (∑ _l ∈ positionedRectangleBoundaryLinks o ho hL hT, 6) ≤ 24 * (L * T) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc
      (positionedRectangleBoundaryLinks o ho hL hT).card * 6 ≤ (4 * (L * T)) * 6 :=
        Nat.mul_le_mul_right 6 hlinks
      _ = 24 * (L * T) := by ring
  exact hrootCover.trans (hsum.trans hsum')

theorem card_positionedRectangleSourceAnimalSupports_le {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1) (k : ℕ) (hk : 1 ≤ k) :
    ((positionedRectangleSourceRootPlaquettes o ho hL hT).biUnion fun p =>
      FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p k).card ≤
        24 * (L * T) * 400 ^ k := by
  classical
  calc
    _ ≤ ∑ p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT,
        (FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT, 400 ^ k := by
      apply Finset.sum_le_sum
      intro p hp
      exact card_linkConnectedPlaquetteSupports_le p k hk
    _ = (positionedRectangleSourceRootPlaquettes o ho hL hT).card * 400 ^ k := by
      simp [Finset.sum_const]
    _ ≤ 24 * (L * T) * 400 ^ k :=
      Nat.mul_le_mul_right (400 ^ k) (positionedRectangleSourceRootPlaquettes_card_le o ho hL hT)

theorem positionedRectangleSourceComponent_support_has_rootedAnimal {B : Box 4}
    {L T : ℕ} (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    ∃ p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT,
      plaquetteModeComponentSupport m
        (positionedRectangleSourceComponent o ho hL hT hLpos hTpos m hsource) ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
            (plaquetteModeComponentSupport m
              (positionedRectangleSourceComponent o ho hL hT hLpos hTpos m hsource)).card := by
  classical
  let c := positionedRectangleSourceComponent o ho hL hT hLpos hTpos m hsource
  let f := plaquetteModeComponentField m c
  have hq : boundary (plaquetteModeChain f) = positionedRectangleLoop o ho L T hL hT :=
    positionedRectangleSourceComponent_boundary o ho hL hT hLpos hTpos m hsource
  have hloopNe : positionedRectangleLoop o ho L T hL hT ≠ 0 := by
    intro hz
    have hpair := areaTestPotential_pairing_positionedRectangleLoop o ho hL hT
    rw [hz] at hpair
    have harea : (0 : ℤ) < (L * T : ℤ) := by exact_mod_cast Nat.mul_pos hLpos hTpos
    have hcast : (L * T : ℤ) = 0 := by simpa using hpair.symm
    exact (ne_of_gt harea) hcast
  obtain ⟨l, hl⟩ := Finsupp.support_nonempty_iff.mpr hloopNe
  have hloopCoeff : positionedRectangleLoop o ho L T hL hT l ≠ 0 :=
    Finsupp.mem_support_iff.mp hl
  have hqCoeff : (boundary (plaquetteModeChain f)) l ≠ 0 := by simpa [hq] using hloopCoeff
  have hdeg : cellDegree l = 1 :=
    integerBoundary_homogeneousSupport (plaquetteModeChain f) 2 (by omega)
      (plaquetteModeChain_homogeneousSupport f) l (Finsupp.mem_support_iff.mpr hqCoeff)
  let link : PrimalLinks B := ⟨l, hdeg⟩
  have hlinkSource : link ∈ positionedRectangleBoundaryLinks o ho hL hT := by
    simp only [positionedRectangleBoundaryLinks, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change positionedRectangleLoop o ho L T hL hT l ≠ 0
    exact hloopCoeff
  have hchainEq : plaquetteModeChain f =
      plaquetteFieldChainOnSet m (plaquetteModeComponentSupport m c) := by
    simpa [f] using plaquetteModeComponentField_chain_eq_set m c
  have hcoeff :
      (boundary (plaquetteFieldChainOnSet m (plaquetteModeComponentSupport m c))) link.1 ≠ 0 := by
    rw [← hchainEq]
    simpa [link] using hqCoeff
  rw [plaquetteFieldChainOnSet_boundary_coeff] at hcoeff
  obtain ⟨p, hp, hpterm⟩ := positioned_exists_nonzero_sum
    (plaquetteModeComponentSupport m c)
    (fun p => m p * (boundary (Finsupp.single p.1 (1 : ℤ))) link.1) hcoeff
  have hpBoundary : (boundary (Finsupp.single p.1 (1 : ℤ))) link.1 ≠ 0 := by
    intro hz
    simp [hz] at hpterm
  have hroot : p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT := by
    rw [positionedRectangleSourceRootPlaquettes]
    refine Finset.mem_biUnion.mpr ⟨link, hlinkSource, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, plaquetteBoundaryLinks]
    exact hpBoundary
  exact ⟨p, hroot, by simpa [c] using plaquetteModeComponentSupport_mem_animals m c hp⟩

private theorem positionedComponent_remainder_support_disjoint {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    Disjoint (plaquetteFieldSupport (plaquetteModeComponentField m c))
      (plaquetteFieldSupport (plaquetteModeComponentRemainder m c)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hpcomp hprem
  have hcompval : plaquetteModeComponentField m c p ≠ 0 :=
    (Finset.mem_filter.mp hpcomp).2
  have hremval : plaquetteModeComponentRemainder m c p ≠ 0 :=
    (Finset.mem_filter.mp hprem).2
  have hcomp : p ∈ plaquetteModeComponentSupport m c := by
    by_contra hnot
    simp [plaquetteModeComponentField, hnot] at hcompval
  have hnot : p ∉ plaquetteModeComponentSupport m c := by
    intro hmem
    simp [plaquetteModeComponentRemainder, hmem] at hremval
  exact hnot hcomp

theorem dualWilsonPartition_le_positionedRectangleSourceClusters_mul_vacuum
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T) (β : ℝ) (hβ : 0 < β) :
    dualWilsonPartition (B := B) β (positionedRectangleSheet o ho L T hL hT) ≤
      (∑' c : {a : PrimalPlaquettes B → ℤ //
        plaquetteModeDivergence a =
          primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT) ∧
        ∃ p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT,
          plaquetteFieldSupport a ∈
            FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
              (plaquetteFieldSupport a).card}, dualGaussianProduct β c.1) *
        dualWilsonPartition (B := B) β (0 : Chain 4 B) := by
  let S := positionedRectangleSheet o ho L T hL hT
  let Roots := positionedRectangleSourceRootPlaquettes o ho hL hT
  let C : (PrimalPlaquettes B → ℤ) → Prop := fun a =>
    ∃ p ∈ Roots, plaquetteFieldSupport a ∈
      FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
        (plaquetteFieldSupport a).card
  let X := {m : PrimalPlaquettes B → ℤ //
    plaquetteModeDivergence m = primalSheetLoopFrequency S}
  let pick (x : X) : (nonzeroPlaquetteGraph x.1).ConnectedComponent :=
    positionedRectangleSourceComponent o ho hL hT hLpos hTpos x.1 (by simpa [X, S] using x.2)
  let comp (x : X) : PrimalPlaquettes B → ℤ := plaquetteModeComponentField x.1 (pick x)
  let rem (x : X) : PrimalPlaquettes B → ℤ := plaquetteModeComponentRemainder x.1 (pick x)
  let P := {a : PrimalPlaquettes B → ℤ //
    plaquetteModeDivergence a = primalSheetLoopFrequency S ∧ C a}
  let split : X → P × (PrimalPlaquettes B → ℤ) := fun x =>
    (⟨comp x, ⟨by
      apply (plaquetteModeDivergence_eq_boundary (comp x) S
        (positionedRectangleSheet_homogeneousSupport o ho hL hT)).2
      simpa [comp, pick, X, S, positionedRectangleLoop] using
        positionedRectangleSourceComponent_boundary o ho hL hT hLpos hTpos x.1 x.2,
      by
        obtain ⟨p, hp, ha⟩ := positionedRectangleSourceComponent_support_has_rootedAnimal
          o ho hL hT hLpos hTpos x.1 x.2
        exact ⟨p, by simpa [Roots] using hp, by
          simpa [comp, pick, X, plaquetteModeComponentField_support] using ha⟩⟩⟩,
      rem x)
  have hinj : Function.Injective split := by
    intro x y hxy
    apply Subtype.ext
    have hcomp : comp x = comp y := congrArg (fun z : P × _ => z.1.1) hxy
    have hrem : rem x = rem y := congrArg Prod.snd hxy
    have hxadd : comp x + rem x = x.1 := by
      simpa [comp, rem, pick] using plaquetteModeComponentField_add_remainder x.1 (pick x)
    have hyadd : comp y + rem y = y.1 := by
      simpa [comp, rem, pick] using plaquetteModeComponentField_add_remainder y.1 (pick y)
    calc
      x.1 = comp x + rem x := hxadd.symm
      _ = comp y + rem y := by rw [hcomp, hrem]
      _ = y.1 := hyadd
  have hfactor (x : X) :
      dualGaussianProduct β x.1 =
        dualGaussianProduct β (split x).1.1 *
          dualWilsonTerm β (0 : Chain 4 B) (split x).2 := by
    have hadd : comp x + rem x = x.1 := by
      simpa [comp, rem, pick] using plaquetteModeComponentField_add_remainder x.1 (pick x)
    have hdivrem : plaquetteModeDivergence (rem x) = 0 := by
      simpa [rem, pick, X, S] using
        positionedRectangleSourceComponent_remainder_divergence_zero
          o ho hL hT hLpos hTpos x.1 x.2
    have hfreqzero : primalSheetLoopFrequency (0 : Chain 4 B) = 0 := by
      funext l
      simp [primalSheetLoopFrequency]
    have hterm0 : plaquetteModeDivergence (rem x) =
        primalSheetLoopFrequency (0 : Chain 4 B) := by rw [hdivrem, hfreqzero]
    have hprod := dualGaussianProduct_mul_of_disjoint_support β (comp x) (rem x) (by
      simpa [comp, rem, pick] using positionedComponent_remainder_support_disjoint x.1 (pick x))
    rw [← hadd]
    simpa [split, dualWilsonTerm, hterm0] using hprod
  have hmain := dualWilsonPartition_le_sourceCluster_mul_vacuum
    β hβ S C split hinj hfactor
  simpa [S, Roots, C, P] using hmain

private theorem positionedGaussianSupportSubset_tsum_le {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (supports : Finset (Finset (PrimalPlaquettes B))) :
    (∑' m : {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m ∈ supports},
      dualGaussianProduct β m.1) ≤
        ∑ S ∈ supports, nonzeroGaussianActivity β ^ S.card := by
  classical
  let A := {S : Finset (PrimalPlaquettes B) // S ∈ supports}
  let Fiber (s : A) := {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m = s.1}
  let Y := Σ s : A, Fiber s
  let w : Y → ℝ := fun y => dualGaussianProduct β y.2.1
  let e : {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m ∈ supports} → Y :=
    fun m => ⟨⟨plaquetteFieldSupport m.1, m.2⟩, ⟨m.1, rfl⟩⟩
  have hinj : Function.Injective e := by
    intro m n h
    apply Subtype.ext
    exact congrArg (fun y : Y => y.2.1) h
  have hwNonneg (y : Y) : 0 ≤ w y := dualGaussianProduct_nonneg β y.2.1
  have hfiber (s : A) : Summable (fun m : Fiber s => w ⟨s, m⟩) := by
    have hgauss := dualGaussianProduct_summable (B := B) β hβ
    exact hgauss.comp_injective (by intro m n h; exact Subtype.ext h)
  have houter : Summable (fun s : A => ∑' m : Fiber s, w ⟨s, m⟩) :=
    Summable.of_finite
  have hY : Summable w := (summable_sigma_of_nonneg hwNonneg).2 ⟨hfiber, houter⟩
  have hsubsum :
      (∑' m : {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m ∈ supports},
        dualGaussianProduct β m.1) ≤ ∑' y : Y, w y := by
    have hfun :
        (fun m : {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m ∈ supports} =>
          dualGaussianProduct β m.1) = w ∘ e := by funext m; rfl
    rw [hfun]
    exact tsum_comp_le_tsum_of_inj hY hwNonneg hinj
  have hdecomp : (∑' y : Y, w y) = ∑' s : A, ∑' m : Fiber s, w ⟨s, m⟩ := hY.tsum_sigma
  calc
    _ ≤ ∑' y : Y, w y := hsubsum
    _ = ∑ S ∈ supports, nonzeroGaussianActivity β ^ S.card := by
      calc
        _ = ∑' s : A, ∑' m : Fiber s, w ⟨s, m⟩ := hdecomp
        _ = ∑ s : A, ∑' m : Fiber s, w ⟨s, m⟩ := by
          let inst : Fintype A := Fintype.ofFinite A
          rw [tsum_fintype]
          refine Finset.sum_congr ?_ ?_
          · ext s; simp
          · intro s hs; rfl
        _ = ∑ s : A, nonzeroGaussianActivity β ^ s.1.card := by
          apply Finset.sum_congr rfl
          intro s hs
          have hfiberValue :
              (∑' m : Fiber s, w ⟨s, m⟩) = nonzeroGaussianActivity β ^ s.1.card := by
            simpa [w, Fiber] using dualGaussianProduct_exactSupport_tsum β hβ s.1
          exact hfiberValue
        _ = ∑ S ∈ supports, nonzeroGaussianActivity β ^ S.card := by
          simpa [A] using Finset.sum_coe_sort supports
            (fun S : Finset (PrimalPlaquettes B) => nonzeroGaussianActivity β ^ S.card)

private theorem positionedGeometricTail_sum_le {A N : ℕ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ k ∈ Finset.range (N + 1), if A ≤ k then r ^ k else 0) ≤
      areaActivityTail r A := by
  classical
  let f : ℕ → ℝ := fun k => if A ≤ k then r ^ k else 0
  have hgeom : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun k => by
      by_cases hk : A ≤ k
      · simpa [f, hk] using pow_nonneg hr0 k
      · simp [f, hk]) (fun k => by
      by_cases hk : A ≤ k
      · simp [f, hk]
      · simpa [f, hk] using pow_nonneg hr0 k) hgeom
  have htailEq : (∑' k : ℕ, f k) = areaActivityTail r A := by
    let e : ℕ ≃ {k : ℕ // A ≤ k} := {
      toFun := fun n => ⟨A + n, by omega⟩
      invFun := fun k => k.1 - A
      left_inv := by intro n; simp
      right_inv := by intro k; apply Subtype.ext; exact Nat.add_sub_of_le k.2 }
    calc
      (∑' k : ℕ, f k) = ∑' k : {k : ℕ // A ≤ k}, r ^ k.1 := by
        calc
          _ = ∑' k : ℕ, ({k : ℕ | A ≤ k}.indicator (fun k => r ^ k)) k := by
            apply tsum_congr
            intro k
            by_cases hk : A ≤ k <;> simp [Set.indicator, hk, f]
          _ = _ := (tsum_subtype {k : ℕ | A ≤ k} (fun k => r ^ k)).symm
      _ = ∑' n : ℕ, r ^ (A + n) := by
        symm
        exact e.tsum_eq (fun k : {k : ℕ // A ≤ k} => r ^ k.1)
      _ = areaActivityTail r A := rfl
  calc
    (∑ k ∈ Finset.range (N + 1), f k) ≤ ∑' k : ℕ, f k :=
      hf.sum_le_tsum (Finset.range (N + 1)) (fun k hk => by
        dsimp [f]
        split_ifs <;> positivity)
    _ = areaActivityTail r A := htailEq

theorem positionedRectangleConnectedSourceActivity_le_tail {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hA : 1 ≤ L * T) (β : ℝ) (hβ : 0 < β) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ Real.exp (-7))
    (hrEq : r = 400 * nonzeroGaussianActivity β) :
    (∑' m : {m : PrimalPlaquettes B → ℤ //
      (∃ p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT,
        plaquetteFieldSupport m ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
            (plaquetteFieldSupport m).card) ∧
      L * T ≤ (plaquetteFieldSupport m).card}, dualGaussianProduct β m.1) ≤
        24 * ((L * T : ℕ) : ℝ) * areaActivityTail r (L * T) := by
  classical
  let roots := positionedRectangleSourceRootPlaquettes o ho hL hT
  let supports : Finset (Finset (PrimalPlaquettes B)) := Finset.univ.filter fun S =>
    (L * T) ≤ S.card ∧ ∃ p ∈ roots,
      S ∈ FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p S.card
  have hallowed (m : {m : PrimalPlaquettes B → ℤ //
      (∃ p ∈ roots, plaquetteFieldSupport m ∈
        FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
          (plaquetteFieldSupport m).card) ∧ L * T ≤ (plaquetteFieldSupport m).card}) :
      plaquetteFieldSupport m.1 ∈ supports := by
    simp only [supports, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨m.2.2, m.2.1⟩
  have hsumSupport := positionedGaussianSupportSubset_tsum_le β hβ supports
  have hsumCluster :
      (∑' m : {m : PrimalPlaquettes B → ℤ //
        (∃ p ∈ roots, plaquetteFieldSupport m ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
            (plaquetteFieldSupport m).card) ∧
        L * T ≤ (plaquetteFieldSupport m).card}, dualGaussianProduct β m.1) ≤
      ∑' m : {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m ∈ supports},
        dualGaussianProduct β m.1 := by
    have hsummable := dualGaussianProduct_summable (B := B) β hβ
    let target : Type := {m : PrimalPlaquettes B → ℤ // plaquetteFieldSupport m ∈ supports}
    let forget : target → (PrimalPlaquettes B → ℤ) := fun m => m.1
    have hforget : Function.Injective forget := by intro m n h; exact Subtype.ext h
    have hsummableTarget : Summable (fun m : target => dualGaussianProduct β m.1) := by
      change Summable (dualGaussianProduct β ∘ forget)
      exact hsummable.comp_injective hforget
    let i : {m : PrimalPlaquettes B → ℤ //
        (∃ p ∈ roots, plaquetteFieldSupport m ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
            (plaquetteFieldSupport m).card) ∧ L * T ≤ (plaquetteFieldSupport m).card} → target :=
      fun m => ⟨m.1, hallowed m⟩
    have hi : Function.Injective i := by
      intro m n h
      apply Subtype.ext
      exact congrArg (fun z : target => z.1) h
    have hfun :
        (fun m : {m : PrimalPlaquettes B → ℤ //
          (∃ p ∈ roots, plaquetteFieldSupport m ∈
            FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
              (plaquetteFieldSupport m).card) ∧ L * T ≤ (plaquetteFieldSupport m).card} =>
          dualGaussianProduct β m.1) = (fun m => dualGaussianProduct β m.1) ∘ i := by
      funext m; rfl
    rw [hfun]
    exact tsum_comp_le_tsum_of_inj hsummableTarget
      (fun m : target => dualGaussianProduct_nonneg β m.1) hi
  have hmax (S : Finset (PrimalPlaquettes B)) : S.card ≤ Fintype.card (PrimalPlaquettes B) :=
    Finset.card_le_card (Finset.subset_univ S)
  let K := Finset.range (Fintype.card (PrimalPlaquettes B) + 1)
  let f : Finset (PrimalPlaquettes B) → ℝ := fun S => nonzeroGaussianActivity β ^ S.card
  have hsumFib := Finset.sum_fiberwise_of_maps_to (s := supports) (t := K)
    (g := fun S => S.card) (f := f) (by intro S hS; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hmax S)))
  have hsumBounds :
      (∑ k ∈ K, ∑ S ∈ supports with S.card = k, f S) ≤
        ∑ k ∈ K, if L * T ≤ k then 24 * ((L * T : ℕ) : ℝ) * r ^ k else 0 := by
    apply Finset.sum_le_sum
    intro k hk
    by_cases hkA : L * T ≤ k
    · have hlevelSubset : supports.filter (fun S => S.card = k) ⊆
          roots.biUnion fun p =>
            FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p k := by
        intro S hS
        have hS' := Finset.mem_filter.mp hS
        have hmem := Finset.mem_filter.mp hS'.1
        obtain ⟨p, hp, hanimal⟩ := hmem.2.2
        refine Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩
        simpa [hS'.2] using hanimal
      have hcount : (supports.filter (fun S => S.card = k)).card ≤
          24 * (L * T) * 400 ^ k := by
        exact (Finset.card_le_card hlevelSubset).trans
          (card_positionedRectangleSourceAnimalSupports_le o ho hL hT k (by omega))
      have hconst : (∑ S ∈ supports with S.card = k, f S) =
          ((supports.filter (fun S => S.card = k)).card : ℝ) *
            nonzeroGaussianActivity β ^ k := by
        calc
          _ = ∑ S ∈ supports.filter (fun S => S.card = k),
                nonzeroGaussianActivity β ^ k := by
              apply Finset.sum_congr rfl
              intro S hS
              have hs := (Finset.mem_filter.mp hS).2
              simp [f, hs]
          _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
      rw [hconst]
      have hcountR : ((supports.filter (fun S => S.card = k)).card : ℝ) ≤
          24 * (L * T : ℕ) * (400 : ℝ) ^ k := by exact_mod_cast hcount
      have htau : 0 ≤ nonzeroGaussianActivity β := by
        unfold nonzeroGaussianActivity
        exact tsum_nonneg fun z => by split_ifs <;> positivity
      have hpow : 0 ≤ nonzeroGaussianActivity β ^ k := pow_nonneg htau _
      simp only [ite_eq_left hkA]
      calc
        _ ≤ (24 * (L * T : ℕ) * (400 : ℝ) ^ k) * nonzeroGaussianActivity β ^ k :=
          mul_le_mul_of_nonneg_right hcountR hpow
        _ = 24 * ((L * T : ℕ) : ℝ) * r ^ k := by rw [hrEq, mul_pow]; ring
    · have hempty : supports.filter (fun S => S.card = k) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (by
          intro S hS
          simp only [supports, Finset.mem_filter, Finset.mem_univ, true_and] at hS
          intro heq
          exact hkA (by omega))
      have hzero : (∑ S ∈ supports with S.card = k, f S) = 0 := by simp [hempty]
      rw [hzero]
      simp only [ite_eq_right hkA]
      norm_num
  have htauGeometric :
      (∑ S ∈ supports, f S) ≤
        24 * ((L * T : ℕ) : ℝ) * areaActivityTail r (L * T) := by
    rw [← hsumFib]
    calc
      _ ≤ ∑ k ∈ K, if L * T ≤ k then 24 * ((L * T : ℕ) : ℝ) * r ^ k else 0 := hsumBounds
      _ = 24 * ((L * T : ℕ) : ℝ) *
            (∑ k ∈ K, if L * T ≤ k then r ^ k else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> ring
      _ ≤ 24 * ((L * T : ℕ) : ℝ) * areaActivityTail r (L * T) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact positionedGeometricTail_sum_le hr0
          (lt_of_le_of_lt hr1 (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)))
  exact hsumCluster.trans (hsumSupport.trans htauGeometric)

theorem dualGaussianProduct_source_small_beta_bound_positioned {B : Box 4}
    {L T : ℕ} (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 1 / 80)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT)) :
    dualGaussianProduct β m ≤
      Real.exp (-10 * (L * T : ℝ)) * dualGaussianProduct (4 * β / 3) m := by
  have hmass := areaTestPotential_modeRealL1_lower_bound_positioned
    o ho hL hT m hsource
  have hbound := dualGaussianProduct_le_residual_of_l1 β hβ m
  have hcoef : (10 : ℝ) ≤ 1 / (8 * β) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * β)).2
    nlinarith [hsmall]
  have harea : 0 ≤ (L * T : ℝ) := by positivity
  have hmul : 10 * (L * T : ℝ) ≤ (L * T : ℝ) / (8 * β) := by
    calc
      10 * (L * T : ℝ) ≤ (1 / (8 * β)) * (L * T : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef harea
      _ = (L * T : ℝ) / (8 * β) := by ring
  have hexp : Real.exp (-((L * T : ℝ) / (8 * β))) ≤ Real.exp (-10 * (L * T : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    dualGaussianProduct β m ≤
        Real.exp (-((∑ p : PrimalPlaquettes B, |(m p : ℝ)|) / (8 * β))) *
          dualGaussianProduct (4 * β / 3) m :=
      dualGaussianProduct_le_residual_of_l1 β hβ m
    _ ≤ Real.exp (-((L * T : ℝ) / (8 * β))) *
          dualGaussianProduct (4 * β / 3) m := by
      apply mul_le_mul_of_nonneg_right _ (dualGaussianProduct_nonneg (4 * β / 3) m)
      exact Real.exp_le_exp.mpr (by
        have hdiv := div_le_div_of_nonneg_right hmass (by positivity : 0 ≤ 8 * β)
        linarith)
    _ ≤ Real.exp (-10 * (L * T : ℝ)) * dualGaussianProduct (4 * β / 3) m :=
      mul_le_mul_of_nonneg_right hexp (dualGaussianProduct_nonneg (4 * β / 3) m)

private theorem positionedRectangleSourceCluster_residual_le_tail {B : Box 4}
    {L T : ℕ} (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 1 / 80) :
    (∑' c : {m : PrimalPlaquettes B → ℤ //
      plaquetteModeDivergence m =
        primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT) ∧
      ∃ p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT,
        plaquetteFieldSupport m ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
            (plaquetteFieldSupport m).card}, dualGaussianProduct β c.1) ≤
      Real.exp (-10 * (L * T : ℝ)) *
        (24 * ((L * T : ℕ) : ℝ) *
          areaActivityTail (400 * nonzeroGaussianActivity (4 * β / 3)) (L * T)) := by
  classical
  let Source : Type := {m : PrimalPlaquettes B → ℤ //
    plaquetteModeDivergence m =
      primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT) ∧
    ∃ p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT,
      plaquetteFieldSupport m ∈
        FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
          (plaquetteFieldSupport m).card}
  let Allowed : Type := {m : PrimalPlaquettes B → ℤ //
    (∃ p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT,
      plaquetteFieldSupport m ∈
        FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
          (plaquetteFieldSupport m).card) ∧
    L * T ≤ (plaquetteFieldSupport m).card}
  let residualβ : ℝ := 4 * β / 3
  let r : ℝ := 400 * nonzeroGaussianActivity residualβ
  let extract : ℝ := Real.exp (-10 * (L * T : ℝ))
  have hβr : 0 < residualβ := by dsimp [residualβ]; positivity
  have hr0 : 0 ≤ r := by
    dsimp [r]
    unfold nonzeroGaussianActivity
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg fun z => by split_ifs <;> positivity
  have hrsmall : r ≤ Real.exp (-7) := by
    dsimp [r, residualβ]
    exact smallBeta_residualActivity_bound β hβ hsmall
  have hfull := dualGaussianProduct_summable (B := B) residualβ hβr
  let forgetSource : Source → (PrimalPlaquettes B → ℤ) := fun m => m.1
  have hforgetSource : Function.Injective forgetSource := by
    intro m n h
    exact Subtype.ext h
  have hsourceResidualSummable : Summable (fun m : Source =>
      dualGaussianProduct residualβ m.1) := by
    change Summable (dualGaussianProduct residualβ ∘ forgetSource)
    exact hfull.comp_injective hforgetSource
  have hsourceOriginalSummable : Summable (fun m : Source =>
      dualGaussianProduct β m.1) := by
    have h := dualGaussianProduct_summable (B := B) β hβ
    change Summable (dualGaussianProduct β ∘ forgetSource)
    exact h.comp_injective hforgetSource
  have hsourcePoint (m : Source) :
      dualGaussianProduct β m.1 ≤ extract * dualGaussianProduct residualβ m.1 := by
    dsimp [extract, residualβ]
    exact dualGaussianProduct_source_small_beta_bound_positioned
      o ho hL hT β hβ hsmall m.1 m.2.1
  have hsourceSum :
      (∑' m : Source, dualGaussianProduct β m.1) ≤
        extract * (∑' m : Source, dualGaussianProduct residualβ m.1) := by
    calc
      _ ≤ ∑' m : Source, extract * dualGaussianProduct residualβ m.1 :=
        hsourceOriginalSummable.tsum_le_tsum hsourcePoint
          (hsourceResidualSummable.mul_left extract)
      _ = extract * (∑' m : Source, dualGaussianProduct residualβ m.1) := tsum_mul_left
  have harea (m : Source) : L * T ≤ (plaquetteFieldSupport m.1).card :=
    plaquetteFieldSupport_card_lower_bound_positioned o ho hL hT m.1 m.2.1
  let incl : Source → Allowed := fun m => ⟨m.1, ⟨m.2.2, harea m⟩⟩
  have hinj : Function.Injective incl := by
    intro m n h
    apply Subtype.ext
    exact congrArg (fun x : Allowed => x.1) h
  have hfullAllowed : Summable (fun m : Allowed => dualGaussianProduct residualβ m.1) := by
    let forgetAllowed : Allowed → (PrimalPlaquettes B → ℤ) := fun m => m.1
    have hforgetAllowed : Function.Injective forgetAllowed := by
      intro m n h
      exact Subtype.ext h
    change Summable (dualGaussianProduct residualβ ∘ forgetAllowed)
    exact hfull.comp_injective hforgetAllowed
  have hsourceResidualLeAllowed :
      (∑' m : Source, dualGaussianProduct residualβ m.1) ≤
        ∑' m : Allowed, dualGaussianProduct residualβ m.1 := by
    have hfun : (fun m : Source => dualGaussianProduct residualβ m.1) =
        (fun m : Allowed => dualGaussianProduct residualβ m.1) ∘ incl := by
      funext m
      rfl
    rw [hfun]
    exact tsum_comp_le_tsum_of_inj hfullAllowed
      (fun m : Allowed => dualGaussianProduct_nonneg residualβ m.1) hinj
  have hA : 1 ≤ L * T := by
    have hpos : 0 < L * T := Nat.mul_pos hLpos hTpos
    omega
  have hrEq : r = 400 * nonzeroGaussianActivity residualβ := by rfl
  have hcluster := positionedRectangleConnectedSourceActivity_le_tail
    o ho hL hT hA residualβ hβr r hr0 hrsmall hrEq
  have hAcast : ((L * T : ℕ) : ℝ) = (L : ℝ) * (T : ℝ) := by norm_cast
  calc
    (∑' m : Source, dualGaussianProduct β m.1) ≤
        extract * (∑' m : Source, dualGaussianProduct residualβ m.1) := hsourceSum
    _ ≤ extract * (∑' m : Allowed, dualGaussianProduct residualβ m.1) :=
      mul_le_mul_of_nonneg_left hsourceResidualLeAllowed (Real.exp_pos _).le
    _ ≤ extract *
        (24 * ((L * T : ℕ) : ℝ) * areaActivityTail r (L * T)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact hcluster
    _ = extract * (24 * (L * T : ℝ) * areaActivityTail r (L * T)) := by rw [hAcast]
    _ = Real.exp (-10 * (L * T : ℝ)) *
        (24 * ((L * T : ℕ) : ℝ) *
          areaActivityTail (400 * nonzeroGaussianActivity (4 * β / 3)) (L * T)) := by
      simp [extract, r, residualβ, hAcast]

theorem primalWilsonExpectation_positionedRectangle_smallBeta_areaLaw
    {B : Box 4} {L T : ℕ}
    (o : Fin 4 → ℕ) (ho : ∀ k, o k ≤ B k)
    (hL : o 0 + L ≤ B 0) (hT : o 1 + T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 1 / 80) :
    0 ≤ (primalWilsonExpectation β (positionedRectangleSheet o ho L T hL hT)).re ∧
      (primalWilsonExpectation β (positionedRectangleSheet o ho L T hL hT)).re ≤
        Real.exp (-(L * T : ℝ) / 2) := by
  classical
  let A : ℕ := L * T
  let residualβ : ℝ := 4 * β / 3
  let r : ℝ := 400 * nonzeroGaussianActivity residualβ
  let extract : ℝ := Real.exp (-10 * (A : ℝ))
  have hA : 1 ≤ A := by
    dsimp [A]
    have hpos : 0 < L * T := Nat.mul_pos hLpos hTpos
    omega
  have hβr : 0 < residualβ := by dsimp [residualβ]; positivity
  have hr0 : 0 ≤ r := by
    dsimp [r]
    unfold nonzeroGaussianActivity
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg fun z => by split_ifs <;> positivity
  have hrsmall : r ≤ Real.exp (-7) := by
    dsimp [r, residualβ]
    exact smallBeta_residualActivity_bound β hβ hsmall
  have hpartition := dualWilsonPartition_le_positionedRectangleSourceClusters_mul_vacuum
    o ho hL hT hLpos hTpos β hβ
  have hvac : 0 < dualWilsonPartition (B := B) β (0 : Chain 4 B) :=
    dualWilsonPartition_zero_pos β hβ
  have hratio :
      dualWilsonPartition (B := B) β (positionedRectangleSheet o ho L T hL hT) /
          dualWilsonPartition (B := B) β (0 : Chain 4 B) ≤
        ∑' c : {m : PrimalPlaquettes B → ℤ //
          plaquetteModeDivergence m =
            primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT) ∧
          ∃ p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT,
            plaquetteFieldSupport m ∈
              FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
                (plaquetteFieldSupport m).card}, dualGaussianProduct β c.1 := by
    apply (div_le_iff₀ hvac).2
    exact hpartition
  have hclusterTail := positionedRectangleSourceCluster_residual_le_tail
    o ho hL hT hLpos hTpos β hβ hsmall
  have hactivityTail := areaActivityTail_bound A hA r hr0 hrsmall
  have hclusterBound :
      (∑' c : {m : PrimalPlaquettes B → ℤ //
        plaquetteModeDivergence m =
          primalSheetLoopFrequency (positionedRectangleSheet o ho L T hL hT) ∧
        ∃ p ∈ positionedRectangleSourceRootPlaquettes o ho hL hT,
          plaquetteFieldSupport m ∈
            FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
              (plaquetteFieldSupport m).card}, dualGaussianProduct β c.1) ≤
        Real.exp (-(A : ℝ) / 2) := by
    have htailCast : areaActivityTail r (L * T) = areaActivityTail r A := rfl
    have hcoefCast : ((L * T : ℕ) : ℝ) = (A : ℝ) := rfl
    have hcluster := hclusterTail
    rw [htailCast, hcoefCast] at hcluster
    have hextract : Real.exp (-10 * (L * T : ℝ)) = extract := by
      dsimp [extract, A]
      congr 1
      push_cast
      ring
    have hExtractLe : extract ≤ 1 := by
      dsimp [extract]
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hApos : 0 ≤ (A : ℝ) := by positivity
      linarith
    calc
      _ ≤ extract * (24 * (A : ℝ) * areaActivityTail r A) := by
        calc
          _ ≤ Real.exp (-10 * (L * T : ℝ)) *
              (24 * (A : ℝ) * areaActivityTail r A) := by
            simpa [htailCast, hcoefCast] using hcluster
          _ = extract * (24 * (A : ℝ) * areaActivityTail r A) := by rw [hextract]
      _ ≤ extract * Real.exp (-(A : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hactivityTail (Real.exp_pos _).le
      _ ≤ Real.exp (-(A : ℝ) / 2) := by
        calc
          _ ≤ 1 * Real.exp (-(A : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hExtractLe (Real.exp_pos _).le
          _ = _ := by ring
  have hreal :
      (primalWilsonExpectation β (positionedRectangleSheet o ho L T hL hT)).re =
        dualWilsonPartition (B := B) β (positionedRectangleSheet o ho L T hL hT) /
          dualWilsonPartition (B := B) β (0 : Chain 4 B) := by
    rw [primalWilsonExpectation_eq_dualPartition_ratio β hβ]
    rw [← Complex.ofReal_div]
    simp only [Complex.ofReal_re]
  refine ⟨primalWilsonExpectation_re_nonneg β hβ _, ?_⟩
  rw [hreal]
  have hratioBound := hratio.trans hclusterBound
  simpa [A] using hratioBound

theorem cubePrimalSheet_smallBeta_areaLaw {L T N : ℕ}
    (hN : max L T + 1 ≤ N) (hLpos : 0 < L) (hTpos : 0 < T)
    (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 1 / 80) :
    0 ≤ (primalWilsonExpectation β (cubePrimalSheet L T N)).re ∧
      (primalWilsonExpectation β (cubePrimalSheet L T N)).re ≤
        Real.exp (-(L * T : ℝ) / 2) := by
  have hfits := centeredRectangleFits (L := L) (T := T) (N := N) (by omega)
  have hN0 : N ≤ (cube N) 0 := by simp [cube]; omega
  have hN1 : N ≤ (cube N) 1 := by simp [cube]; omega
  have hL : centeredRectangleOrigin N 0 + L ≤ (cube N) 0 := by
    simpa [centeredRectangleOrigin] using hfits.1
  have hT : centeredRectangleOrigin N 1 + T ≤ (cube N) 1 := by
    simpa [centeredRectangleOrigin] using hfits.2
  have hmain := primalWilsonExpectation_positionedRectangle_smallBeta_areaLaw
    (centeredRectangleOrigin N) (centeredRectangleOrigin_le N) hL hT hLpos hTpos β hβ hsmall
  simpa only [positionedRectangleSheet_eq_cubePrimalSheet
    (L := L) (T := T) (N := N) (by omega)] using hmain

theorem fs82_wilson_transition_cube :
    ∃ β₀ β₁ c : ℝ, β₀ < β₁ ∧ 0 < c ∧
      (∀ {L T N : ℕ}, 1 ≤ L → 1 ≤ T → max L T + 1 ≤ N →
        ∀ β : ℝ, 0 < β → β ≤ β₀ →
          0 ≤ (primalWilsonExpectation β (cubePrimalSheet L T N)).re ∧
          (primalWilsonExpectation β (cubePrimalSheet L T N)).re ≤
            Real.exp (-c * (L * T : ℝ))) ∧
      (∀ β : ℝ, β₁ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
        ∀ L T N : ℕ, 1 ≤ L → 1 ≤ T → max L T + 1 ≤ N →
          Real.exp (-(d * ((L : ℝ) + T))) ≤
            (primalWilsonExpectation β (cubePrimalSheet L T N)).re) := by
  refine ⟨1 / 80, wilsonBetaThreshold, 1 / 2, ?_, by norm_num, ?_, ?_⟩
  · unfold wilsonBetaThreshold
    have hrate : 0 ≤ FroehlichSpencer.FS82.Root.MomentComparisonAssembly.rootRate :=
      FroehlichSpencer.FS82.Root.MomentComparisonAssembly.rootRate_nonneg
    nlinarith
  · intro L T N hL hT hN β hβ hsmall
    have hmain := cubePrimalSheet_smallBeta_areaLaw hN (by omega) (by omega) β hβ hsmall
    refine ⟨hmain.1, ?_⟩
    have hexp : -(1 / 2 : ℝ) * (L * T : ℝ) = -(L * T : ℝ) / 2 := by ring
    rw [hexp]
    exact hmain.2
  · intro β hβ
    refine ⟨wilsonPerimeterConstant β, wilsonPerimeterConstant_nonneg hβ, ?_⟩
    intro L T N hL hT hN
    obtain ⟨w, hw, hbound⟩ := fs82_wilson_perimeter_cube hβ hL hT hN
    rw [hw]
    exact by simpa using hbound

end FroehlichSpencer.FS82.Wilson

end
