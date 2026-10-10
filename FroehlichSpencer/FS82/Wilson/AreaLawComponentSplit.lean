/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawComponentBoundary
public import FroehlichSpencer.FS82.Wilson.AreaLawRootCount

/-!
# Positive source-component decomposition

Connected support components split a source mode into one source-bearing
component and a boundaryless remainder. This module makes the split explicit
for rectangular Wilson loops.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

private theorem plaquetteModeChain_eq_fieldChainOnSet_of_restrict
    {B : Box 4} (m f : PrimalPlaquettes B → ℤ)
    (s : Finset (PrimalPlaquettes B))
    (hf : ∀ p, f p = if p ∈ s then m p else 0) :
    plaquetteModeChain f = plaquetteFieldChainOnSet m s := by
  classical
  ext x
  by_cases hx : cellDegree x = 2
  · let p : PrimalPlaquettes B := ⟨x, hx⟩
    change (plaquetteModeChain f) p.1 =
      (plaquetteFieldChainOnSet m s) p.1
    rw [plaquetteModeChain_apply]
    rw [hf]
    unfold plaquetteFieldChainOnSet
    rw [finsupp_finset_sum_apply]
    by_cases hps : p ∈ s
    · rw [ite_eq_left hps]
      symm
      rw [Finset.sum_eq_single p]
      · simp
      · intro q hq hqp
        have hcell : q.1 ≠ p.1 := by
          intro heq
          exact hqp (Subtype.ext heq)
        simp [hcell]
      · intro hnot
        exact (hnot hps).elim
    · rw [ite_eq_right hps]
      symm
      apply Finset.sum_eq_zero
      intro q hq
      have hcell : q.1 ≠ p.1 := by
        intro heq
        apply hps
        exact (Subtype.ext heq) ▸ hq
      simp [hcell]
  · have hleft : plaquetteModeChain f x = 0 := by
      by_contra hne
      exact hx ((plaquetteModeChain_homogeneousSupport f) x
        (Finsupp.mem_support_iff.mpr hne))
    have hright : plaquetteFieldChainOnSet m s x = 0 := by
      unfold plaquetteFieldChainOnSet
      rw [finsupp_finset_sum_apply]
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hpx : p.1 = x
      · subst x
        exact (hx p.2).elim
      · simp [hpx]
    rw [hleft, hright]

theorem plaquetteModeComponentField_chain_eq_set {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    plaquetteModeChain (plaquetteModeComponentField m c) =
      plaquetteFieldChainOnSet m (plaquetteModeComponentSupport m c) := by
  apply plaquetteModeChain_eq_fieldChainOnSet_of_restrict
  intro p
  simp [plaquetteModeComponentField]

@[expose] noncomputable def plaquetteModeComponentRemainderSupport {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    Finset (PrimalPlaquettes B) :=
  plaquetteFieldSupport m \ plaquetteModeComponentSupport m c

theorem plaquetteModeComponentRemainder_chain_eq_set {B : Box 4}
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
    plaquetteModeChain (plaquetteModeComponentRemainder m c) =
      plaquetteFieldChainOnSet m (plaquetteModeComponentRemainderSupport m c) := by
  apply plaquetteModeChain_eq_fieldChainOnSet_of_restrict
  intro p
  by_cases hC : p ∈ plaquetteModeComponentSupport m c
  · simp [plaquetteModeComponentRemainderSupport, hC,
      plaquetteModeComponentRemainder]
  · by_cases hm : m p = 0
    · simp [plaquetteModeComponentRemainderSupport, hC, hm,
        plaquetteFieldSupport, plaquetteModeComponentRemainder]
    · have hmem : p ∈ plaquetteFieldSupport m := by
        simp [plaquetteFieldSupport, hm]
      simp [plaquetteModeComponentRemainderSupport, hC, hmem,
        plaquetteModeComponentRemainder]

theorem wilsonRectangleSheet_homogeneousSupport {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) :
    homogeneousSupport (wilsonRectangleSheet L T hL hT) 2 := by
  classical
  intro c hc
  change c ∈ (∑ x : Fin L × Fin T,
    basisChain (wilsonRectanglePlaquette hL hT x.1 x.2)).support at hc
  have hsum := Finsupp.support_finsetSum hc
  rcases Finset.mem_biUnion.mp hsum with ⟨x, hx, hterm⟩
  have hne : basisChain (wilsonRectanglePlaquette hL hT x.1 x.2) c ≠ 0 :=
    Finsupp.mem_support_iff.mp hterm
  have hcell : c = wilsonRectanglePlaquette hL hT x.1 x.2 := by
    by_contra hnot
    simp [basisChain, hnot] at hne
  rw [hcell, cellDegree, wilsonRectanglePlaquette_axes hL hT x.1 x.2]
  simp

private theorem componentRemainder_boundary_support_disjoint {B : Box 4}
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

/-- The boundary of a selected support component is supported on the source
loop whenever the whole mode has that loop boundary. -/
theorem plaquetteModeComponentBoundary_support_subset_source
    {B : Box 4} {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    (boundary (plaquetteModeChain (plaquetteModeComponentField m c))).support ⊆
      (wilsonRectangleLoop L T hL hT).support := by
  classical
  let q := boundary (plaquetteModeChain (plaquetteModeComponentField m c))
  let r := boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c))
  have hsourceChain := (plaquetteModeDivergence_eq_boundary m
    (wilsonRectangleSheet L T hL hT)
    (wilsonRectangleSheet_homogeneousSupport hL hT)).mp hsource
  have hsum : q + r = wilsonRectangleLoop L T hL hT := by
    dsimp [q, r, wilsonRectangleLoop]
    calc
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) +
          boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
          boundary (plaquetteModeChain (plaquetteModeComponentField m c) +
            plaquetteModeChain (plaquetteModeComponentRemainder m c)) := by
              symm
              exact map_add boundary _ _
      _ = boundary (plaquetteModeChain m) := by
            rw [← plaquetteModeChain_eq_component_add_remainder]
      _ = boundary (wilsonRectangleSheet L T hL hT) := hsourceChain
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
  have hdisj := componentRemainder_boundary_support_disjoint m c
  have hrnot : e ∉ Finset.univ.filter fun z : PrimalLinks B => r z.1 ≠ 0 := by
    intro hrmem
    exact (Finset.disjoint_left.mp hdisj) hqmem hrmem
  have hrzero : r l = 0 := by
    by_contra hr
    apply hrnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e] using hr⟩
  have hcoeff := congrArg (fun z : Chain 4 B => z l) hsum
  have hloop : (wilsonRectangleLoop L T hL hT) l ≠ 0 := by
    rw [← hcoeff]
    simp [q, r, hq, hrzero]
  exact Finsupp.mem_support_iff.mpr hloop

private theorem areaLawComponentBoundary_side_relations {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent)
    (a : Fin L) (b : Fin T)
    (hperim : (boundary (plaquetteModeChain
      (plaquetteModeComponentField m c))).support ⊆
      areaLawRectanglePerimeterCells L T hL hT) :
    (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (areaLawRectangleBottomLink hL a) =
      (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (areaLawRectangleRightLink hL hT b) ∧
    (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (areaLawRectangleTopLink hL hT a) * (-1) =
      (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (areaLawRectangleRightLink hL hT b) ∧
    (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (areaLawRectangleLeftLink hT b) * (-1) =
      (boundary (plaquetteModeChain (plaquetteModeComponentField m c)))
        (areaLawRectangleRightLink hL hT b) := by
  have hpairs := areaLawBoundaryPotential_mode_pairings hL hT a b
    (plaquetteModeComponentField m c)
  have hbottom := hpairs.1
  have htop := hpairs.2.1
  have hleft := hpairs.2.2
  rw [integerCellPairing_horizontalBottom_eq_link hL hT a b _ hperim,
    integerCellPairing_verticalRight_eq_link hL hT a b _ hperim] at hbottom
  rw [integerCellPairing_horizontalTop_eq_link hL hT a b _ hperim,
    integerCellPairing_verticalRight_eq_link hL hT a b _ hperim] at htop
  rw [integerCellPairing_verticalLeft_eq_link hL hT a b _ hperim,
    integerCellPairing_verticalRight_eq_link hL hT a b _ hperim] at hleft
  exact ⟨hbottom, htop, hleft⟩

private theorem wilsonRectangleLoop_side_coefficients {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T) :
    (∀ a : Fin L, (wilsonRectangleLoop L T hL hT)
        (areaLawRectangleBottomLink hL a) = 1) ∧
    (∀ a : Fin L, (wilsonRectangleLoop L T hL hT)
        (areaLawRectangleTopLink hL hT a) = -1) ∧
    (∀ b : Fin T, (wilsonRectangleLoop L T hL hT)
        (areaLawRectangleLeftLink hT b) = -1) ∧
    (∀ b : Fin T, (wilsonRectangleLoop L T hL hT)
        (areaLawRectangleRightLink hL hT b) = 1) := by
  have hperim := wilsonRectangleLoop_support_subset_perimeter hL hT
  have hhom := wilsonRectangleSheet_homogeneousSupport hL hT
  have hcurl (a : Fin L) (b : Fin T) :
      ∀ p : PrimalPlaquettes B,
        integerCellPairing
            (areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b))
            (boundary (basisChain p.1)) =
          integerCellPairing (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b))
            (boundary (basisChain p.1)) := by
    intro p
    rw [areaLawHorizontalPotentialBottom_curl, areaLocalPotential_curl]
  have hTopCurl (a : Fin L) (b : Fin T) :
      ∀ p : PrimalPlaquettes B,
        integerCellPairing
            (areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b))
            (boundary (basisChain p.1)) =
          integerCellPairing (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b))
            (boundary (basisChain p.1)) := by
    intro p
    rw [areaLawHorizontalPotentialTop_curl, areaLocalPotential_curl]
  have hLeftCurl (a : Fin L) (b : Fin T) :
      ∀ p : PrimalPlaquettes B,
        integerCellPairing
            (areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b))
            (boundary (basisChain p.1)) =
          integerCellPairing (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b))
            (boundary (basisChain p.1)) := by
    intro p
    rw [areaLawVerticalPotentialLeft_curl, areaLocalPotential_curl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    let b : Fin T := ⟨0, hTpos⟩
    have hpair := integerCellPairing_boundary_eq_of_same_plaquette_curl
      _ _ (wilsonRectangleSheet L T hL hT) hhom (hcurl a b)
    have heq : integerCellPairing
        (areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b))
        (wilsonRectangleLoop L T hL hT) = 1 := by
      change integerCellPairing
        (areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b))
        (boundary (wilsonRectangleSheet L T hL hT)) = 1
      calc
        integerCellPairing
            (areaLawHorizontalPotentialBottom (Fin.castLE hL a) (Fin.castLE hT b))
            (boundary (wilsonRectangleSheet L T hL hT)) =
            integerCellPairing (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b))
              (boundary (wilsonRectangleSheet L T hL hT)) := hpair
        _ = 1 := areaLocalPotential_rectangle_loop_pairing hL hT a b
    rw [integerCellPairing_horizontalBottom_eq_link hL hT a b _ hperim] at heq
    exact heq
  · intro a
    let b : Fin T := ⟨0, hTpos⟩
    have hpair := integerCellPairing_boundary_eq_of_same_plaquette_curl
      _ _ (wilsonRectangleSheet L T hL hT) hhom (hTopCurl a b)
    have heq : integerCellPairing
        (areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b))
        (wilsonRectangleLoop L T hL hT) = 1 := by
      change integerCellPairing
        (areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b))
        (boundary (wilsonRectangleSheet L T hL hT)) = 1
      calc
        integerCellPairing
            (areaLawHorizontalPotentialTop (Fin.castLE hL a) (Fin.castLE hT b))
            (boundary (wilsonRectangleSheet L T hL hT)) =
            integerCellPairing (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b))
              (boundary (wilsonRectangleSheet L T hL hT)) := hpair
        _ = 1 := areaLocalPotential_rectangle_loop_pairing hL hT a b
    rw [integerCellPairing_horizontalTop_eq_link hL hT a b _ hperim] at heq
    nlinarith
  · intro b
    let a : Fin L := ⟨0, hLpos⟩
    have hpair := integerCellPairing_boundary_eq_of_same_plaquette_curl
      _ _ (wilsonRectangleSheet L T hL hT) hhom (hLeftCurl a b)
    have heq : integerCellPairing
        (areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b))
        (wilsonRectangleLoop L T hL hT) = 1 := by
      change integerCellPairing
        (areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b))
        (boundary (wilsonRectangleSheet L T hL hT)) = 1
      calc
        integerCellPairing
            (areaLawVerticalPotentialLeft (Fin.castLE hL a) (Fin.castLE hT b))
            (boundary (wilsonRectangleSheet L T hL hT)) =
            integerCellPairing (areaLocalPotential (Fin.castLE hL a) (Fin.castLE hT b))
              (boundary (wilsonRectangleSheet L T hL hT)) := hpair
        _ = 1 := areaLocalPotential_rectangle_loop_pairing hL hT a b
    rw [integerCellPairing_verticalLeft_eq_link hL hT a b _ hperim] at heq
    nlinarith
  · intro b
    have hpair := areaLocalPotential_rectangle_loop_pairing hL hT
      (⟨0, hLpos⟩ : Fin L) b
    rw [integerCellPairing_verticalRight_eq_link hL hT
      (⟨0, hLpos⟩ : Fin L) b _ hperim] at hpair
    exact hpair

private theorem plaquetteModeComponent_boundary_sum_eq_source {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    boundary (plaquetteModeChain (plaquetteModeComponentField m c)) +
        boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
      wilsonRectangleLoop L T hL hT := by
  have hsourceChain := (plaquetteModeDivergence_eq_boundary m
    (wilsonRectangleSheet L T hL hT)
    (wilsonRectangleSheet_homogeneousSupport hL hT)).mp hsource
  calc
    boundary (plaquetteModeChain (plaquetteModeComponentField m c)) +
        boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c)) =
        boundary (plaquetteModeChain (plaquetteModeComponentField m c) +
          plaquetteModeChain (plaquetteModeComponentRemainder m c)) := by
            symm
            exact map_add boundary _ _
    _ = boundary (plaquetteModeChain m) := by
          rw [← plaquetteModeChain_eq_component_add_remainder]
    _ = boundary (wilsonRectangleSheet L T hL hT) := hsourceChain
    _ = wilsonRectangleLoop L T hL hT := rfl

/-- A nonzero support component carrying any part of the source loop carries
the whole loop. The four coordinate curl tests propagate one nonzero side
coefficient to all four sides; disjoint component boundaries then fix its
coefficient to the source value. -/
theorem plaquetteModeComponentBoundary_eq_zero_or_loop {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (c : (nonzeroPlaquetteGraph m).ConnectedComponent)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    boundary (plaquetteModeChain (plaquetteModeComponentField m c)) = 0 ∨
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) =
        wilsonRectangleLoop L T hL hT := by
  classical
  let q := boundary (plaquetteModeChain (plaquetteModeComponentField m c))
  let r := boundary (plaquetteModeChain (plaquetteModeComponentRemainder m c))
  have hqSource := plaquetteModeComponentBoundary_support_subset_source
    hL hT m c hsource
  have hqPerim : q.support ⊆ areaLawRectanglePerimeterCells L T hL hT := by
    intro x hx
    exact wilsonRectangleLoop_support_subset_perimeter hL hT (hqSource hx)
  have hSide (a : Fin L) (b : Fin T) :
      q (areaLawRectangleBottomLink hL a) =
          q (areaLawRectangleRightLink hL hT b) ∧
      q (areaLawRectangleTopLink hL hT a) * (-1) =
          q (areaLawRectangleRightLink hL hT b) ∧
      q (areaLawRectangleLeftLink hT b) * (-1) =
          q (areaLawRectangleRightLink hL hT b) := by
    simpa [q] using areaLawComponentBoundary_side_relations hL hT m c a b hqPerim
  have hloopSide := wilsonRectangleLoop_side_coefficients hL hT hLpos hTpos
  by_cases hqzero : q = 0
  · exact Or.inl (by simpa [q] using hqzero)
  · have hqhom : homogeneousSupport q 1 := by
      dsimp [q]
      exact integerBoundary_homogeneousSupport
        (plaquetteModeChain (plaquetteModeComponentField m c)) 2 (by omega)
        (plaquetteModeChain_homogeneousSupport _)
    have hqNonempty : q.support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr hqzero
    obtain ⟨x, hx⟩ := hqNonempty
    have hxdeg : cellDegree x = 1 := hqhom x hx
    let e : PrimalLinks B := ⟨x, hxdeg⟩
    have hxe : q e.1 ≠ 0 := by
      simpa [e] using Finsupp.mem_support_iff.mp hx
    have hxperim : e.1 ∈ areaLawRectanglePerimeterCells L T hL hT := by
      apply wilsonRectangleLoop_support_subset_perimeter hL hT
      exact hqSource (by simpa [q, e] using hx)
    let a0 : Fin L := ⟨0, hLpos⟩
    let b0 : Fin T := ⟨0, hTpos⟩
    have hexistsRight : ∃ b : Fin T,
        q (areaLawRectangleRightLink hL hT b) ≠ 0 := by
      obtain hbottom | hrest | hleft | hright :=
        areaLawRectanglePerimeter_mem_cases hL hT e.1 hxperim
      · obtain ⟨a, hxa⟩ := hbottom
        have hval : q (areaLawRectangleBottomLink hL a) ≠ 0 := by
          rw [← hxa]
          exact hxe
        refine ⟨b0, ?_⟩
        rw [← (hSide a b0).1]
        exact hval
      · obtain ⟨a, hxa⟩ := hrest
        have hval : q (areaLawRectangleTopLink hL hT a) ≠ 0 := by
          rw [← hxa]
          exact hxe
        refine ⟨b0, ?_⟩
        intro hz
        apply hval
        have hzero : q (areaLawRectangleTopLink hL hT a) * (-1) = 0 :=
          (hSide a b0).2.1.trans hz
        exact (mul_eq_zero.mp hzero).resolve_right (by norm_num)
      · obtain ⟨b, hxb⟩ := hleft
        have hval : q (areaLawRectangleLeftLink hT b) ≠ 0 := by
          rw [← hxb]
          exact hxe
        refine ⟨b, ?_⟩
        intro hz
        apply hval
        have hzero : q (areaLawRectangleLeftLink hT b) * (-1) = 0 :=
          (hSide a0 b).2.2.trans hz
        exact (mul_eq_zero.mp hzero).resolve_right (by norm_num)
      · obtain ⟨b, hxb⟩ := hright
        refine ⟨b, ?_⟩
        rw [← hxb]
        exact hxe
    obtain ⟨bstar, hbStar⟩ := hexistsRight
    have hsum := plaquetteModeComponent_boundary_sum_eq_source
      hL hT m c hsource
    let side : Cell 4 B := areaLawRectangleRightLink hL hT bstar
    have hsideDeg : cellDegree side = 1 := by
      simp [side, cellDegree, areaLawRectangleRightLink,
        areaLawRectangleVerticalLink_axes]
    let link : PrimalLinks B := ⟨side, hsideDeg⟩
    have hqmem : link ∈ Finset.univ.filter fun z : PrimalLinks B => q z.1 ≠ 0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [link, side] using hbStar⟩
    have hdisj := componentRemainder_boundary_support_disjoint m c
    have hrnot : link ∉ Finset.univ.filter fun z : PrimalLinks B => r z.1 ≠ 0 := by
      intro hr
      have hdisj' : Disjoint
          (Finset.univ.filter fun z : PrimalLinks B => q z.1 ≠ 0)
          (Finset.univ.filter fun z : PrimalLinks B => r z.1 ≠ 0) := by
        simpa [q, r] using hdisj
      exact (Finset.disjoint_left.mp hdisj') hqmem hr
    have hrzero : r side = 0 := by
      by_contra hne
      apply hrnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [link, side] using hne⟩
    have hcoeff := congrArg (fun z : Chain 4 B => z side) hsum
    have hright0 : q side = 1 := by
      have hloop := hloopSide.2.2.2 bstar
      have hcoeff' : q side = (wilsonRectangleLoop L T hL hT) side := by
        change q side + r side = (wilsonRectangleLoop L T hL hT) side at hcoeff
        simpa [hrzero] using hcoeff
      calc
        q side = (wilsonRectangleLoop L T hL hT) side := hcoeff'
        _ = 1 := by simpa [side] using hloop
    have hrightAll (b : Fin T) :
        q (areaLawRectangleRightLink hL hT b) = 1 := by
      calc
        q (areaLawRectangleRightLink hL hT b) = q (areaLawRectangleBottomLink hL a0) :=
          (hSide a0 b).1.symm
        _ = q (areaLawRectangleRightLink hL hT bstar) := (hSide a0 bstar).1
        _ = 1 := by simpa [side] using hright0
    have hbottomAll (a : Fin L) :
        q (areaLawRectangleBottomLink hL a) = 1 := by
      calc
        _ = q (areaLawRectangleRightLink hL hT b0) := (hSide a b0).1
        _ = 1 := hrightAll b0
    have htopAll (a : Fin L) :
        q (areaLawRectangleTopLink hL hT a) = -1 := by
      have h := (hSide a b0).2.1
      rw [hrightAll b0] at h
      nlinarith
    have hleftAll (b : Fin T) :
        q (areaLawRectangleLeftLink hT b) = -1 := by
      have h := (hSide a0 b).2.2
      rw [hrightAll b] at h
      nlinarith
    have hqSupportPerim : q.support ⊆ areaLawRectanglePerimeterCells L T hL hT := hqPerim
    have hloopSupportPerim := wilsonRectangleLoop_support_subset_perimeter hL hT
    have hqhom : homogeneousSupport q 1 := by
      dsimp [q]
      exact integerBoundary_homogeneousSupport
        (plaquetteModeChain (plaquetteModeComponentField m c)) 2 (by omega)
        (plaquetteModeChain_homogeneousSupport _)
    have hloopHom : homogeneousSupport (wilsonRectangleLoop L T hL hT) 1 := by
      rw [wilsonRectangleLoop]
      exact integerBoundary_homogeneousSupport (wilsonRectangleSheet L T hL hT)
        2 (by omega) (wilsonRectangleSheet_homogeneousSupport hL hT)
    have hqeq : q = wilsonRectangleLoop L T hL hT := by
      ext x
      by_cases hdeg : cellDegree x = 1
      · by_cases hperim : x ∈ areaLawRectanglePerimeterCells L T hL hT
        · obtain hbottom | hrest | hleft | hright :=
            areaLawRectanglePerimeter_mem_cases hL hT x hperim
          · obtain ⟨a, rfl⟩ := hbottom
            exact (hbottomAll a).trans (hloopSide.1 a).symm
          · obtain ⟨a, rfl⟩ := hrest
            exact (htopAll a).trans (hloopSide.2.1 a).symm
          · obtain ⟨b, rfl⟩ := hleft
            exact (hleftAll b).trans (hloopSide.2.2.1 b).symm
          · obtain ⟨b, rfl⟩ := hright
            exact (hrightAll b).trans (hloopSide.2.2.2 b).symm
        · have hqzero' : q x = 0 := by
            by_contra hne
            apply hperim
            exact hqSupportPerim (Finsupp.mem_support_iff.mpr hne)
          have hloopzero : (wilsonRectangleLoop L T hL hT) x = 0 := by
            by_contra hne
            apply hperim
            exact hloopSupportPerim (Finsupp.mem_support_iff.mpr hne)
          simp [hqzero', hloopzero]
      · have hqzero' : q x = 0 := by
          by_contra hne
          exact hdeg (hqhom x (Finsupp.mem_support_iff.mpr hne))
        have hloopzero : (wilsonRectangleLoop L T hL hT) x = 0 := by
          by_contra hne
          exact hdeg (hloopHom x (Finsupp.mem_support_iff.mpr hne))
        simp [hqzero', hloopzero]
    exact Or.inr (by simpa [q] using hqeq)

/-- Some nonzero-support component is the unique source-bearing component of
a mode with rectangular boundary. -/
theorem exists_plaquetteModeComponent_with_source_boundary {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (m : PrimalPlaquettes B → ℤ)
    (hsource : plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT)) :
    ∃ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) =
        wilsonRectangleLoop L T hL hT := by
  classical
  by_contra hnone
  push Not at hnone
  have hcomponentZero (c : (nonzeroPlaquetteGraph m).ConnectedComponent) :
      boundary (plaquetteModeChain (plaquetteModeComponentField m c)) = 0 := by
    rcases plaquetteModeComponentBoundary_eq_zero_or_loop
      hL hT hLpos hTpos m c hsource with hz | hs
    · exact hz
    · exact (hnone c hs).elim
  have htotal :
      (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
        boundary (plaquetteModeChain (plaquetteModeComponentField m c))) =
          wilsonRectangleLoop L T hL hT := by
    calc
      _ = boundary (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
          plaquetteModeChain (plaquetteModeComponentField m c)) := by rw [map_sum]
      _ = boundary (plaquetteModeChain m) := by
            rw [plaquetteModeChain_component_sum_eq]
      _ = boundary (wilsonRectangleSheet L T hL hT) :=
            (plaquetteModeDivergence_eq_boundary m
              (wilsonRectangleSheet L T hL hT)
              (wilsonRectangleSheet_homogeneousSupport hL hT)).mp hsource
      _ = wilsonRectangleLoop L T hL hT := rfl
  have hsumzero :
      (∑ c : (nonzeroPlaquetteGraph m).ConnectedComponent,
        boundary (plaquetteModeChain (plaquetteModeComponentField m c))) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    exact hcomponentZero c
  have hloopzero : wilsonRectangleLoop L T hL hT = 0 := by
    rw [← htotal, hsumzero]
  have hpair := areaTestPotential_pairing_wilsonRectangleLoop hL hT
  rw [hloopzero] at hpair
  have harea : (0 : ℤ) < (L * T : ℤ) := by
    exact_mod_cast Nat.mul_pos hLpos hTpos
  have hcast : (L * T : ℤ) = 0 := by simpa using hpair.symm
  exact (ne_of_gt harea) hcast

end FroehlichSpencer.FS82.Wilson

end
