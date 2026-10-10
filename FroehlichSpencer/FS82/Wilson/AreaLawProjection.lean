/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawLocalPotential
public import FroehlichSpencer.FS82.Wilson.AreaLawSource

/-!
# Projection to the coordinate plane

The two transverse coordinate projections commute with boundary and collapse
all parallel fibers to the 0--1 plane.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

/-- The zero-coordinate statement used to project onto the 0--1 plane. -/
@[expose] def areaPlaneAnchor {B : Box 4} (i : Fin 4) : Fin (B i + 1) :=
  ⟨0, Nat.zero_lt_succ (B i)⟩

/-- Project a cubical chain to the 0--1 plane through the origin. -/
@[expose] noncomputable def areaPlaneProjection {B : Box 4} :
    Chain 4 B →ₗ[ℤ] Chain 4 B :=
  projection areaPlaneAnchor 2 * projection areaPlaneAnchor 3

theorem areaPlaneProjection_boundary_commute {B : Box 4} :
    areaPlaneProjection * boundary (B := B) =
      boundary (B := B) * areaPlaneProjection := by
  unfold areaPlaneProjection
  calc
    (projection areaPlaneAnchor 2 * projection areaPlaneAnchor 3) *
        boundary (B := B) =
      projection areaPlaneAnchor 2 *
        (projection areaPlaneAnchor 3 * boundary (B := B)) := by rw [mul_assoc]
    _ = projection areaPlaneAnchor 2 *
        (boundary (B := B) * projection areaPlaneAnchor 3) := by
          rw [projection_boundary_commute]
    _ = (projection areaPlaneAnchor 2 * boundary (B := B)) *
        projection areaPlaneAnchor 3 := by rw [mul_assoc]
    _ = (boundary (B := B) * projection areaPlaneAnchor 2) *
        projection areaPlaneAnchor 3 := by rw [projection_boundary_commute]
    _ = boundary (B := B) *
        (projection areaPlaneAnchor 2 * projection areaPlaneAnchor 3) := by
          rw [mul_assoc]

private theorem linearCombination_support_witness
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β →₀ ℤ) (q : α →₀ ℤ) {x : β}
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

private theorem projectionBasis_support_coord {B : Box 4}
    (i j : Fin 4) (hij : i ≠ j) (c : Cell 4 B)
    (x : Cell 4 B) (hx : x ∈ (projectionBasis areaPlaneAnchor c i).support) :
    x i = Sum.inl (areaPlaneAnchor i) ∧ x j = c j := by
  cases hci : c i with
  | inl v =>
      have hx' : x = Function.update c i (Sum.inl (areaPlaneAnchor i)) := by
        have hxval := Finsupp.mem_support_iff.mp hx
        change (projectionBasis areaPlaneAnchor c i) x ≠ 0 at hxval
        simpa [projectionBasis, hci, basisChain, Finsupp.single_apply,
          eq_comm] using hxval
      constructor
      · rw [hx']
        simp
      · rw [hx']
        simp [Function.update_of_ne (Ne.symm hij)]
  | inr e =>
      have hxval := Finsupp.mem_support_iff.mp hx
      change (projectionBasis areaPlaneAnchor c i) x ≠ 0 at hxval
      simp [projectionBasis, hci] at hxval

private theorem projection_support_coord {B : Box 4}
    (i j : Fin 4) (hij : i ≠ j) (q : Chain 4 B)
    (x : Cell 4 B) (hx : x ∈ (projection areaPlaneAnchor i q).support) :
    x i = Sum.inl (areaPlaneAnchor i) ∧
      ∃ c ∈ q.support, x j = c j := by
  change x ∈
    (Finsupp.linearCombination ℤ (projectionBasis areaPlaneAnchor · i) q).support
      at hx
  obtain ⟨c, hc, hx'⟩ := linearCombination_support_witness
    (projectionBasis areaPlaneAnchor · i) q hx
  obtain ⟨hxi, hxj⟩ := projectionBasis_support_coord i j hij c x hx'
  exact ⟨hxi, c, hc, hxj⟩

theorem areaPlaneProjection_support_transverse_coords {B : Box 4}
    (q : Chain 4 B) (c : Cell 4 B)
    (hc : c ∈ (areaPlaneProjection q).support) :
    c 2 = Sum.inl (areaPlaneAnchor 2) ∧
      c 3 = Sum.inl (areaPlaneAnchor 3) := by
  have hproj2 : areaPlaneProjection q =
      projection areaPlaneAnchor 2 (projection areaPlaneAnchor 3 q) := rfl
  rw [hproj2] at hc
  obtain ⟨h2, c₃, hc₃, hcoord₃⟩ :=
    projection_support_coord 2 3 (by decide) (projection areaPlaneAnchor 3 q) c hc
  have h3 := (projection_support_coord 3 2 (by decide) q c₃ hc₃).1
  exact ⟨h2, by simpa [h3] using hcoord₃⟩

theorem areaPlaneProjection_preserves_degree_two {B : Box 4}
    (q : Chain 4 B) (hq : homogeneousSupport q 2) :
    homogeneousSupport (areaPlaneProjection q) 2 := by
  have hproject (i : Fin 4) (r : Chain 4 B)
      (hr : homogeneousSupport r 2) :
      homogeneousSupport (projection areaPlaneAnchor i r) 2 := by
    change homogeneousSupport
      (Finsupp.linearCombination ℤ (projectionBasis areaPlaneAnchor · i) r) 2
    exact homogeneousSupport_linearCombination_same cellDegree cellDegree
      (projectionBasis areaPlaneAnchor · i)
      (fun c => homogeneousSupport_projectionBasis areaPlaneAnchor c i) r 2 hr
  unfold areaPlaneProjection
  exact hproject 2 _ (hproject 3 _ hq)

theorem areaPlaneProjection_preserves_homogeneousSupport {B : Box 4}
    (q : Chain 4 B) (k : ℕ) (hq : homogeneousSupport q k) :
    homogeneousSupport (areaPlaneProjection q) k := by
  have hproject (i : Fin 4) (r : Chain 4 B)
      (hr : homogeneousSupport r k) :
      homogeneousSupport (projection areaPlaneAnchor i r) k := by
    change homogeneousSupport
      (Finsupp.linearCombination ℤ (projectionBasis areaPlaneAnchor · i) r) k
    exact homogeneousSupport_linearCombination_same cellDegree cellDegree
      (projectionBasis areaPlaneAnchor · i)
      (fun c => homogeneousSupport_projectionBasis areaPlaneAnchor c i) r k hr
  unfold areaPlaneProjection
  exact hproject 2 _ (hproject 3 _ hq)

theorem areaPlaneProjection_basis_fixed {B : Box 4} (c : Cell 4 B)
    (h2 : c 2 = Sum.inl (areaPlaneAnchor 2))
    (h3 : c 3 = Sum.inl (areaPlaneAnchor 3)) :
    areaPlaneProjection (basisChain c) = basisChain c := by
  change projection areaPlaneAnchor 2
      (projection areaPlaneAnchor 3 (basisChain c)) = basisChain c
  rw [projection_basis]
  have hu3 : Function.update c 3 (Sum.inl (areaPlaneAnchor 3)) = c := by
    funext j
    by_cases hj : j = 3
    · subst j
      simpa using h3.symm
    · simp [Function.update_of_ne hj]
  have hproj3 : projectionBasis areaPlaneAnchor c 3 = basisChain c := by
    simp [projectionBasis, h3, hu3]
  rw [hproj3, projection_basis]
  have hu2 : Function.update c 2 (Sum.inl (areaPlaneAnchor 2)) = c := by
    funext j
    by_cases hj : j = 2
    · subst j
      simpa using h2.symm
    · simp [Function.update_of_ne hj]
  have hproj2 : projectionBasis areaPlaneAnchor c 2 = basisChain c := by
    simp [projectionBasis, h2, hu2]
  exact hproj2

theorem plaquetteModeChain_homogeneousSupport {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) :
    homogeneousSupport (plaquetteModeChain m) 2 := by
  classical
  intro c hc
  change c ∈ (∑ p : PrimalPlaquettes B,
    Finsupp.single p.1 (m p)).support at hc
  have hsum := Finsupp.support_finsetSum hc
  rcases Finset.mem_biUnion.mp hsum with ⟨p, hp, hterm⟩
  have hnonzero : (Finsupp.single p.1 (m p)) c ≠ 0 :=
    Finsupp.mem_support_iff.mp hterm
  have hcell : c = p.1 := by
    by_contra hne
    simp [hne] at hnonzero
  rw [hcell]
  exact p.2

theorem areaPlaneProjection_mode_support_witness {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) (c : Cell 4 B)
    (hc : c ∈ (areaPlaneProjection (plaquetteModeChain m)).support) :
    ∃ p : PrimalPlaquettes B, m p ≠ 0 ∧
      c ∈ (areaPlaneProjection (basisChain p.1)).support := by
  classical
  change c ∈ (areaPlaneProjection
      (∑ p : PrimalPlaquettes B, Finsupp.single p.1 (m p))).support at hc
  rw [map_sum] at hc
  have hsum := Finsupp.support_finsetSum hc
  rcases Finset.mem_biUnion.mp hsum with ⟨p, hp, hterm⟩
  have hsingle : Finsupp.single p.1 (m p) = (m p) • basisChain p.1 := by
    ext x
    by_cases h : x = p.1 <;> simp [basisChain, h]
  have hterm' :
      c ∈ ((m p) • areaPlaneProjection (basisChain p.1)).support := by
    simpa [hsingle, map_smul] using hterm
  have hnonzero :
      ((m p) • areaPlaneProjection (basisChain p.1)) c ≠ 0 :=
    Finsupp.mem_support_iff.mp hterm'
  by_cases hm : m p = 0
  · simp [hm] at hnonzero
  · refine ⟨p, hm, ?_⟩
    rw [Finsupp.mem_support_iff]
    intro hzero
    apply hnonzero
    simp [Finsupp.smul_apply, hzero]

theorem areaLocalPotential_rectangle_face_curl {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (a : Fin L) (b : Fin T) (i : Fin L) (j : Fin T) :
    integerCellPairing (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b))
      (boundary (basisChain (wilsonRectanglePlaquette hL hT i j))) =
        if i = a ∧ j = b then 1 else 0 := by
  have haxes := wilsonRectanglePlaquette_axes hL hT i j
  have hdegree : cellDegree (wilsonRectanglePlaquette hL hT i j) = 2 := by
    rw [cellDegree, haxes]
    simp
  have hcoord0 :
      coordBase (wilsonRectanglePlaquette hL hT i j 0) =
        (Fin.castLE hL i).val := by
    simp [wilsonRectanglePlaquette, edgeCell, coordBase]
  have hcoord1 :
      coordBase (wilsonRectanglePlaquette hL hT i j 1) =
        (Fin.castLE hT j).val := by
    simp [wilsonRectanglePlaquette, edgeCell, coordBase]
  let p : PrimalPlaquettes B :=
    ⟨wilsonRectanglePlaquette hL hT i j, hdegree⟩
  have hp := areaLocalPotential_curl p (Fin.castLE hL a) (Fin.castLE hT b)
  simpa [p, haxes, hcoord0, hcoord1, Fin.ext_iff] using hp

theorem areaLocalPotential_rectangle_loop_pairing {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (a : Fin L) (b : Fin T) :
    integerCellPairing (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b))
      (wilsonRectangleLoop L T hL hT) = 1 := by
  classical
  rw [wilsonRectangleLoop, wilsonRectangleSheet]
  rw [integerCellPairing_boundary_sum]
  simp_rw [areaLocalPotential_rectangle_face_curl hL hT a b]
  rw [Finset.sum_eq_single (a, b)]
  · simp
  · intro x hx hne
    by_cases hxa : x.1 = a
    · have hxb : x.2 ≠ b := by
        intro hxb
        exact hne (Prod.ext hxa hxb)
      simp [hxa, hxb]
    · simp [hxa]
  · simp

theorem integerCellPairing_boundary_chain {B : Box 4}
    (f : Cell 4 B → ℤ) (q : Chain 4 B) :
    integerCellPairing f (boundary q) =
      ∑ c : Cell 4 B, q c * integerCellPairing f (boundary (basisChain c)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [integerCellPairing]
  | add q r hq hr =>
      rw [map_add, integerCellPairing_add, hq, hr, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      simp [Finsupp.add_apply, add_mul]
  | single c z =>
      have hsingle : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases h : x = c <;> simp [basisChain, h]
      rw [hsingle, map_smul, integerCellPairing_smul]
      simp [integerCellPairing, basisChain, Finsupp.single_apply]

@[expose] noncomputable def areaPlaneAdjointPotential {B : Box 4}
    (a : Fin (B 0)) (b : Fin (B 1)) (c : Cell 4 B) : ℤ :=
  integerCellPairing (areaLocalPotential a b)
    (areaPlaneProjection (basisChain c))

theorem integerCellPairing_areaPlaneProjection_eq_adjoint {B : Box 4}
    (a : Fin (B 0)) (b : Fin (B 1)) (q : Chain 4 B) :
    integerCellPairing (areaLocalPotential a b) (areaPlaneProjection q) =
      integerCellPairing (areaPlaneAdjointPotential a b) q := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [areaPlaneAdjointPotential, integerCellPairing]
  | add q r hq hr =>
      rw [map_add, integerCellPairing_add, integerCellPairing_add, hq, hr]
  | single c z =>
      have hsingle : Finsupp.single c z = z • basisChain c := by
        ext x
        by_cases h : x = c <;> simp [basisChain, h]
      rw [hsingle, map_smul, integerCellPairing_smul, integerCellPairing_smul]
      simp [areaPlaneAdjointPotential]

theorem integerCellPairing_zero_of_support_zero {B : Box 4}
    (f : Cell 4 B → ℤ) (q : Chain 4 B)
    (hf : ∀ c ∈ q.support, f c = 0) :
    integerCellPairing f q = 0 := by
  classical
  unfold integerCellPairing
  apply Finset.sum_eq_zero
  intro c hc
  by_cases hmem : c ∈ q.support
  · rw [hf c hmem]
    simp
  · have hzero : q c = 0 := Finsupp.notMem_support_iff.mp hmem
    simp [hzero]

theorem areaPlaneAdjointPotential_zero_of_degree_ne_one {B : Box 4}
    (a : Fin (B 0)) (b : Fin (B 1)) (c : Cell 4 B)
    (hc : cellDegree c ≠ 1) :
    areaPlaneAdjointPotential a b c = 0 := by
  unfold areaPlaneAdjointPotential
  apply integerCellPairing_zero_of_support_zero
  intro d hd
  have hdegree := areaPlaneProjection_preserves_homogeneousSupport
    (basisChain c) (cellDegree c) (homogeneousSupport_basis c) d hd
  simp [areaLocalPotential, hdegree, hc]

theorem areaPlaneProjection_rectSheet_identity {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) :
    areaPlaneProjection (wilsonRectangleSheet L T hL hT) =
      wilsonRectangleSheet L T hL hT := by
  classical
  unfold areaPlaneProjection wilsonRectangleSheet
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact areaPlaneProjection_basis_fixed _ (by
    simp [wilsonRectanglePlaquette, edgeCell, wilsonRectangleBaseCell,
      areaPlaneAnchor]) (by
    simp [wilsonRectanglePlaquette, edgeCell, wilsonRectangleBaseCell,
      areaPlaneAnchor])

theorem areaPlaneProjectedMode_boundary_pairing_eq_one {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT))
    (a : Fin L) (b : Fin T) :
    integerCellPairing
      (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b))
      (boundary (areaPlaneProjection (plaquetteModeChain m))) = 1 := by
  let aB : Fin (B 0) := Fin.castLE hL a
  let bB : Fin (B 1) := Fin.castLE hT b
  have hsourcePair :
      integerCellPairing (areaPlaneAdjointPotential aB bB)
        (boundary (plaquetteModeChain m)) =
      integerCellPairing (areaPlaneAdjointPotential aB bB)
        (boundary (wilsonRectangleSheet L T hL hT)) := by
    apply integerCellPairing_eq_of_degreeOne_coeff_eq
    · intro c hc
      exact areaPlaneAdjointPotential_zero_of_degree_ne_one aB bB c hc
    · intro c hc
      let l : PrimalLinks B := ⟨c, hc⟩
      have h := congrFun hsource l
      simpa [plaquetteModeDivergence, primalSheetLoopFrequency, l] using h
  have hcommMode := congrArg
    (fun f : Chain 4 B →ₗ[ℤ] Chain 4 B => f (plaquetteModeChain m))
    (areaPlaneProjection_boundary_commute (B := B))
  have hcommSheet := congrArg
    (fun f : Chain 4 B →ₗ[ℤ] Chain 4 B => f (wilsonRectangleSheet L T hL hT))
    (areaPlaneProjection_boundary_commute (B := B))
  have hcommMode' :
      areaPlaneProjection (boundary (plaquetteModeChain m)) =
        boundary (areaPlaneProjection (plaquetteModeChain m)) := by
    exact hcommMode
  have hcommSheet' :
      areaPlaneProjection (boundary (wilsonRectangleSheet L T hL hT)) =
        boundary (areaPlaneProjection (wilsonRectangleSheet L T hL hT)) := by
    exact hcommSheet
  calc
    integerCellPairing (areaLocalPotential aB bB)
        (boundary (areaPlaneProjection (plaquetteModeChain m))) =
      integerCellPairing (areaLocalPotential aB bB)
        (areaPlaneProjection (boundary (plaquetteModeChain m))) := by
          rw [← hcommMode']
    _ = integerCellPairing (areaPlaneAdjointPotential aB bB)
        (boundary (plaquetteModeChain m)) :=
          integerCellPairing_areaPlaneProjection_eq_adjoint aB bB _
    _ = integerCellPairing (areaPlaneAdjointPotential aB bB)
        (boundary (wilsonRectangleSheet L T hL hT)) := hsourcePair
    _ = integerCellPairing (areaLocalPotential aB bB)
        (areaPlaneProjection (boundary (wilsonRectangleSheet L T hL hT))) :=
          (integerCellPairing_areaPlaneProjection_eq_adjoint aB bB _).symm
    _ = integerCellPairing (areaLocalPotential aB bB)
        (boundary (areaPlaneProjection (wilsonRectangleSheet L T hL hT))) := by
          rw [hcommSheet']
    _ = integerCellPairing (areaLocalPotential aB bB)
        (boundary (wilsonRectangleSheet L T hL hT)) := by
          rw [areaPlaneProjection_rectSheet_identity]
    _ = 1 := by
          simpa [aB, bB, wilsonRectangleLoop] using
            areaLocalPotential_rectangle_loop_pairing hL hT a b

theorem areaPlaneProjectedCell_eq_rectangleFace {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (a : Fin L) (b : Fin T)
    (c : Cell 4 B)
    (haxes : cellAxes c = {0, 1})
    (h2 : c 2 = Sum.inl (areaPlaneAnchor 2))
    (h3 : c 3 = Sum.inl (areaPlaneAnchor 3))
    (h0 : coordBase (c 0) = (Fin.castLE hL a).val)
    (h1 : coordBase (c 1) = (Fin.castLE hT b).val) :
    c = wilsonRectanglePlaquette hL hT a b := by
  classical
  funext i
  fin_cases i
  · have hmem : (0 : Fin 4) ∈ cellAxes c := by rw [haxes]; simp
    cases hc0 : c 0 with
    | inl v =>
        have hr : coordIsEdge (c 0) := (Finset.mem_filter.mp hmem).2
        simp [coordIsEdge, hc0] at hr
    | inr e =>
        have he : e.val = (Fin.castLE hL a).val := by simpa [hc0, coordBase] using h0
        have heq : e = Fin.castLE hL a := Fin.ext he
        simp [hc0, heq, wilsonRectanglePlaquette, edgeCell]
  · have hmem : (1 : Fin 4) ∈ cellAxes c := by rw [haxes]; simp
    cases hc1 : c 1 with
    | inl v =>
        have hr : coordIsEdge (c 1) := (Finset.mem_filter.mp hmem).2
        simp [coordIsEdge, hc1] at hr
    | inr e =>
        have he : e.val = (Fin.castLE hT b).val := by simpa [hc1, coordBase] using h1
        have heq : e = Fin.castLE hT b := Fin.ext he
        simp [hc1, heq, wilsonRectanglePlaquette, edgeCell]
  · simpa [areaPlaneAnchor, wilsonRectanglePlaquette, edgeCell,
      wilsonRectangleBaseCell] using h2
  · simpa [areaPlaneAnchor, wilsonRectanglePlaquette, edgeCell,
      wilsonRectangleBaseCell] using h3

theorem areaPlaneProjection_support_axes {B : Box 4}
    (q : Chain 4 B) (hq : homogeneousSupport q 2)
    (c : Cell 4 B) (hc : c ∈ (areaPlaneProjection q).support) :
    cellAxes c = {0, 1} := by
  classical
  have hdeg : cellDegree c = 2 :=
    areaPlaneProjection_preserves_degree_two q hq c hc
  obtain ⟨hc2, hc3⟩ := areaPlaneProjection_support_transverse_coords q c hc
  have h2not : (2 : Fin 4) ∉ cellAxes c := by
    intro hmem
    have hed : coordIsEdge (c 2) := (Finset.mem_filter.mp hmem).2
    simp [coordIsEdge, hc2] at hed
  have h3not : (3 : Fin 4) ∉ cellAxes c := by
    intro hmem
    have hed : coordIsEdge (c 3) := (Finset.mem_filter.mp hmem).2
    simp [coordIsEdge, hc3] at hed
  have hsubset : cellAxes c ⊆ ({0, 1} : Finset (Fin 4)) := by
    intro i hi
    have hnot2 : i ≠ 2 := by
      intro heq
      subst i
      exact h2not hi
    have hnot3 : i ≠ 3 := by
      intro heq
      subst i
      exact h3not hi
    fin_cases i <;> simp_all [cellAxes, coordIsEdge]
  have hcard : (cellAxes c).card = 2 := by
    exact hdeg
  have hpaircard : ({0, 1} : Finset (Fin 4)).card = 2 := by simp
  exact Finset.eq_of_subset_of_card_le hsubset (by
    rw [hpaircard, hcard])

theorem areaPlaneProjectedMode_target_coefficient {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT))
    (a : Fin L) (b : Fin T) :
    areaPlaneProjection (plaquetteModeChain m)
        (wilsonRectanglePlaquette hL hT a b) = 1 := by
  classical
  let q : Chain 4 B := areaPlaneProjection (plaquetteModeChain m)
  let aB : Fin (B 0) := Fin.castLE hL a
  let bB : Fin (B 1) := Fin.castLE hT b
  let target : Cell 4 B := wilsonRectanglePlaquette hL hT a b
  have hpair := areaPlaneProjectedMode_boundary_pairing_eq_one hL hT m hsource a b
  rw [integerCellPairing_boundary_chain] at hpair
  have htargetcurl :
      integerCellPairing (areaLocalPotential aB bB)
        (boundary (basisChain target)) = 1 := by
    simpa [target, aB, bB] using
      areaLocalPotential_rectangle_face_curl hL hT a b a b
  have htargetcurl' :
      integerCellPairing (areaLocalPotential aB bB)
        (boundaryBasis target) = 1 := by
    simpa [boundary_basis] using htargetcurl
  have hsum :
      (∑ c : Cell 4 B, q c *
        integerCellPairing (areaLocalPotential aB bB)
          (boundary (basisChain c))) = q target := by
    rw [Finset.sum_eq_single target]
    · simp [htargetcurl']
    · intro c hc hne
      by_cases hqc : q c = 0
      · simp [hqc]
      · have hcsupp : c ∈ q.support := Finsupp.mem_support_iff.mpr hqc
        have haxes := areaPlaneProjection_support_axes
          (plaquetteModeChain m) (plaquetteModeChain_homogeneousSupport m)
          c (by simpa [q] using hcsupp)
        obtain ⟨hc2, hc3⟩ :=
          areaPlaneProjection_support_transverse_coords
            (plaquetteModeChain m) c (by simpa [q] using hcsupp)
        have hdegree : cellDegree c = 2 :=
          areaPlaneProjection_preserves_degree_two
            (plaquetteModeChain m) (plaquetteModeChain_homogeneousSupport m)
            c (by simpa [q] using hcsupp)
        let p : PrimalPlaquettes B := ⟨c, hdegree⟩
        have hnot :
            ¬((0 : Fin 4) ∈ cellAxes c ∧ (1 : Fin 4) ∈ cellAxes c ∧
              coordBase (c 0) = aB.val ∧ coordBase (c 1) = bB.val) := by
          intro hcond
          have hceq := areaPlaneProjectedCell_eq_rectangleFace hL hT a b c
            haxes hc2 hc3 hcond.2.2.1 hcond.2.2.2
          exact hne (by simpa [target] using hceq)
        have hcurl :
            integerCellPairing (areaLocalPotential aB bB)
              (boundary (basisChain c)) = 0 := by
          rw [areaLocalPotential_curl p aB bB]
          simp [p, hnot]
        have hcurl' :
            integerCellPairing (areaLocalPotential aB bB) (boundaryBasis c) = 0 := by
          simpa [boundary_basis] using hcurl
        simp [hcurl']
    · simp
  change q target = 1
  rw [← hsum]
  simpa [q, aB, bB] using hpair

theorem areaPlaneProjection_basis_support_card_le {B : Box 4}
    (c : Cell 4 B) :
    (areaPlaneProjection (basisChain c)).support.card ≤ 1 := by
  change (projection areaPlaneAnchor 2
      (projection areaPlaneAnchor 3 (basisChain c))).support.card ≤ 1
  rw [projection_basis]
  cases hc3 : c 3 with
  | inr e =>
      simp [projectionBasis, hc3]
  | inl v =>
      simp only [projectionBasis, hc3]
      rw [projection_basis]
      cases hc2 : c 2 with
      | inr e =>
          simp [projectionBasis, hc2]
      | inl w =>
          simp [projectionBasis, hc2, basisChain]

theorem plaquetteFieldSupport_card_lower_bound {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    L * T ≤ (plaquetteFieldSupport m).card := by
  classical
  let witness (x : Fin L × Fin T) :
      ∃ p : PrimalPlaquettes B,
        p ∈ plaquetteFieldSupport m ∧
        wilsonRectanglePlaquette hL hT x.1 x.2 ∈
          (areaPlaneProjection (basisChain p.1)).support := by
    have hcoeff := areaPlaneProjectedMode_target_coefficient hL hT m hsource x.1 x.2
    have htarget :
        wilsonRectanglePlaquette hL hT x.1 x.2 ∈
          (areaPlaneProjection (plaquetteModeChain m)).support :=
      Finsupp.mem_support_iff.mpr (by simp [hcoeff])
    obtain ⟨p, hmp, hpsupp⟩ :=
      areaPlaneProjection_mode_support_witness m _ htarget
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmp⟩, hpsupp⟩
  let pick (x : Fin L × Fin T) : PrimalPlaquettes B :=
    Classical.choose (witness x)
  have hpick (x : Fin L × Fin T) :
      pick x ∈ plaquetteFieldSupport m ∧
        wilsonRectanglePlaquette hL hT x.1 x.2 ∈
          (areaPlaneProjection (basisChain (pick x).1)).support :=
    Classical.choose_spec (witness x)
  have hinj : Function.Injective pick := by
    intro x y hxy
    have htarget :
        wilsonRectanglePlaquette hL hT x.1 x.2 =
          wilsonRectanglePlaquette hL hT y.1 y.2 := by
      have hcard := areaPlaneProjection_basis_support_card_le (pick x).1
      have hboth : ∀ c ∈
          (areaPlaneProjection (basisChain (pick x).1)).support,
          ∀ d ∈ (areaPlaneProjection (basisChain (pick x).1)).support, c = d :=
        Finset.card_le_one.mp hcard
      exact hboth _ (hpick x).2 _ (by simpa [hxy] using (hpick y).2)
    have hxy' := (wilsonRectanglePlaquette_injective hL hT) htarget
    exact hxy'
  have hcount :
      (Finset.univ : Finset (Fin L × Fin T)).card ≤
        (plaquetteFieldSupport m).card :=
    Finset.card_le_card_of_injOn pick
      (by
        intro x hx
        exact (hpick x).1)
      (by
        intro x hx y hy hxy
        exact hinj hxy)
  simpa [Fintype.card_prod] using hcount


end FroehlichSpencer.FS82.Wilson

end
