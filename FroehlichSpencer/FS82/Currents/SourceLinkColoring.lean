/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex

/-!
# The direction and base-point parity coloring of source links

A source link is colored by its unique coordinate direction and the parity of
its lattice base point. The geometric plaquette-independence lemma is proved
below from the cubical incidence representation.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Currents.SourceLinkColoring

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

variable {B : SourceBox}

/-- The unique oriented coordinate direction of a source link. -/
noncomputable def linkDirection (e : SourceDualOneCells B) : Fin 4 :=
  Classical.choose (Finset.card_eq_one.mp e.2)

theorem linkAxes_eq_singleton (e : SourceDualOneCells B) :
    dualCellAxes e.1 = {linkDirection e} :=
  Classical.choose_spec (Finset.card_eq_one.mp e.2)

theorem linkDirection_mem_axes (e : SourceDualOneCells B) :
    linkDirection e ∈ dualCellAxes e.1 := by
  rw [linkAxes_eq_singleton]
  simp

theorem linkAxis_eq_direction (e : SourceDualOneCells B) {i : Fin 4}
    (hi : i ∈ dualCellAxes e.1) : i = linkDirection e := by
  rw [linkAxes_eq_singleton] at hi
  simpa using hi

/-- The integer lattice base-point coordinate of a source link. -/
def linkBaseCoordinate (e : SourceDualOneCells B) (i : Fin 4) : ℕ :=
  match e.1 i with
  | Sum.inl v => v.val + 1
  | Sum.inr v => v.val

/-- The parity of the sum of the four base-point coordinates. -/
def linkBaseParity (e : SourceDualOneCells B) : Fin 2 :=
  ⟨(∑ i : Fin 4, linkBaseCoordinate e i) % 2, Nat.mod_lt _ (by omega)⟩

/-- The eight-class direction and base-point parity coloring. -/
noncomputable def linkColor (e : SourceDualOneCells B) : Fin 8 :=
  ⟨2 * (linkDirection e).val + (linkBaseParity e).val, by
    have hd := (linkDirection e).isLt
    have hp := (linkBaseParity e).isLt
    omega⟩


/-- A source plaquette is incident to a link when it is one of the two cubical
faces in a transverse coordinate of that link. -/
def linkIncidentPlaquette (e : SourceDualOneCells B) (p : SourceDualTwoCells B) : Prop :=
  ∃ (i : Fin 4) (v : Fin (B i)), e.1 i = Sum.inl v ∧
    (p.1 = dualUpperFace e.1 i v ∨ p.1 = dualLowerFace e.1 i v)

theorem linkCoord_isRight_iff (e : SourceDualOneCells B) (i : Fin 4) :
    (e.1 i).isRight = true ↔ i = linkDirection e := by
  constructor
  · intro h
    apply linkAxis_eq_direction e
    simp [dualCellAxes, h]
  · rintro rfl
    have h := linkDirection_mem_axes e
    simpa [dualCellAxes] using h

theorem linkCoord_isLeft_of_ne_direction (e : SourceDualOneCells B)
    {i : Fin 4} (hi : i ≠ linkDirection e) :
    ∃ v : Fin (B i), e.1 i = Sum.inl v := by
  cases h : e.1 i with
  | inl v => exact ⟨v, rfl⟩
  | inr v =>
      have hr : (e.1 i).isRight = true := by simp [h]
      have := (linkCoord_isRight_iff e i).mp hr
      exact (hi this).elim

theorem upperFace_axes_eq (e : SourceDualOneCells B) (i : Fin 4)
    (v : Fin (B i)) :
    dualCellAxes (dualUpperFace e.1 i v) = {linkDirection e, i} := by
  ext k
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases hki : k = i
  · subst k
    simp [dualUpperFace]
  · have hcoord : dualUpperFace e.1 i v k = e.1 k := by
      simp [dualUpperFace, hki]
    rw [hcoord, linkCoord_isRight_iff]
    simp [hki]

theorem lowerFace_axes_eq (e : SourceDualOneCells B) (i : Fin 4)
    (v : Fin (B i)) :
    dualCellAxes (dualLowerFace e.1 i v) = {linkDirection e, i} := by
  ext k
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases hki : k = i
  · subst k
    simp [dualLowerFace]
  · have hcoord : dualLowerFace e.1 i v k = e.1 k := by
      simp [dualLowerFace, hki]
    rw [hcoord, linkCoord_isRight_iff]
    simp [hki]


/-- Transverse coordinate directions of a source link. -/
abbrev TransverseAxes (e : SourceDualOneCells B) :=
  {i : Fin 4 // i ≠ linkDirection e}

/-- The source link has a vertex coordinate in every transverse direction. -/
noncomputable def transverseVertex (e : SourceDualOneCells B)
    (i : TransverseAxes e) : Fin (B i.1) :=
  Classical.choose (linkCoord_isLeft_of_ne_direction e (i := i.1) i.2)

theorem transverseVertex_spec (e : SourceDualOneCells B)
    (i : TransverseAxes e) :
    e.1 i.1 = Sum.inl (transverseVertex e i) :=
  Classical.choose_spec (linkCoord_isLeft_of_ne_direction e (i := i.1) i.2)

/-- The axes `{i,j}` have cardinality two when the directions differ. -/
private theorem sourceAxesPair_card {i j : Fin 4} (hij : i ≠ j) :
    ({i, j} : Finset (Fin 4)).card = 2 := by
  have hnot : i ∉ ({j} : Finset (Fin 4)) := by
    intro hm
    exact hij (Finset.mem_singleton.mp hm)
  change (insert i ({j} : Finset (Fin 4))).card = 2
  rw [Finset.card_insert_of_notMem hnot]
  simp

/-- One upper adjacent plaquette in a fixed transverse direction. -/
noncomputable def incidentUpperFace (e : SourceDualOneCells B)
    (i : TransverseAxes e) : SourceDualTwoCells B :=
  ⟨dualUpperFace e.1 i.1 (transverseVertex e i), by
    rw [dualCellDegree, upperFace_axes_eq]
    exact sourceAxesPair_card i.property.symm⟩

/-- One lower adjacent plaquette in a fixed transverse direction. -/
noncomputable def incidentLowerFace (e : SourceDualOneCells B)
    (i : TransverseAxes e) : SourceDualTwoCells B :=
  ⟨dualLowerFace e.1 i.1 (transverseVertex e i), by
    rw [dualCellDegree, lowerFace_axes_eq]
    exact sourceAxesPair_card i.property.symm⟩

/-- One of the at most two plaquettes adjacent to a link in a fixed transverse
direction. -/
noncomputable def incidentCandidateFace (e : SourceDualOneCells B)
    (i : TransverseAxes e) (upper : Bool) : SourceDualTwoCells B :=
  if upper then incidentUpperFace e i else incidentLowerFace e i

@[simp] theorem incidentCandidateFace_true_val (e : SourceDualOneCells B)
    (i : TransverseAxes e) :
    (incidentCandidateFace e i true).1 =
      dualUpperFace e.1 i.1 (transverseVertex e i) := rfl

@[simp] theorem incidentCandidateFace_false_val (e : SourceDualOneCells B)
    (i : TransverseAxes e) :
    (incidentCandidateFace e i false).1 =
      dualLowerFace e.1 i.1 (transverseVertex e i) := rfl

/-- The finite set of all candidate incident plaquettes. -/
noncomputable def incidentCandidateFaces (e : SourceDualOneCells B) :
    Finset (SourceDualTwoCells B) :=
  Finset.univ.image fun q : TransverseAxes e × Bool =>
    incidentCandidateFace e q.1 q.2

/-- The plaquettes appearing in the link's curl column. -/
noncomputable def incidentPlaquettes (e : SourceDualOneCells B) :
    Finset (SourceDualTwoCells B) :=
  by
    classical
    exact Finset.univ.filter fun p => linkIncidentPlaquette e p

/-- Number of contained source plaquettes incident to a link. -/
noncomputable def incidentPlaquetteCount (e : SourceDualOneCells B) : ℕ :=
  (incidentPlaquettes e).card

theorem incidentPlaquettes_subset_candidates (e : SourceDualOneCells B) :
    incidentPlaquettes e ⊆ incidentCandidateFaces e := by
  classical
  intro p hp
  have hinc := (Finset.mem_filter.mp hp).2
  rcases hinc with ⟨i, v, hcoord, hup | hlo⟩
  · have hne : i ≠ linkDirection e := by
      intro hi
      subst i
      have hr := (linkCoord_isRight_iff e (linkDirection e)).2 rfl
      rw [hcoord] at hr
      simp at hr
    let ti : TransverseAxes e := ⟨i, hne⟩
    have hv : transverseVertex e ti = v := by
      apply Sum.inl.inj
      rw [← transverseVertex_spec e ti, hcoord]
    have hface : p = incidentCandidateFace e ti true := by
      apply Subtype.ext
      change p.1 = (incidentCandidateFace e ti true).1
      rw [incidentCandidateFace_true_val]
      rw [hup, hv]
    apply Finset.mem_image.mpr
    exact ⟨(ti, true), Finset.mem_univ _, hface.symm⟩
  · have hne : i ≠ linkDirection e := by
      intro hi
      subst i
      have hr := (linkCoord_isRight_iff e (linkDirection e)).2 rfl
      rw [hcoord] at hr
      simp at hr
    let ti : TransverseAxes e := ⟨i, hne⟩
    have hv : transverseVertex e ti = v := by
      apply Sum.inl.inj
      rw [← transverseVertex_spec e ti, hcoord]
    have hface : p = incidentCandidateFace e ti false := by
      apply Subtype.ext
      change p.1 = (incidentCandidateFace e ti false).1
      rw [incidentCandidateFace_false_val]
      rw [hlo, hv]
    apply Finset.mem_image.mpr
    exact ⟨(ti, false), Finset.mem_univ _, hface.symm⟩

theorem transverseAxes_card (e : SourceDualOneCells B) :
    Fintype.card (TransverseAxes e) = 3 := by
  classical
  simp [TransverseAxes, Fintype.card_subtype_compl]

theorem incidentPlaquetteCount_le_six (e : SourceDualOneCells B) :
    (incidentPlaquettes e).card ≤ 6 := by
  calc
    (incidentPlaquettes e).card ≤ (incidentCandidateFaces e).card :=
      Finset.card_le_card (incidentPlaquettes_subset_candidates e)
    _ ≤ Fintype.card (TransverseAxes e × Bool) := Finset.card_image_le
    _ = 6 := by rw [Fintype.card_prod, transverseAxes_card]; decide

theorem incidentPlaquetteCount_pos (e : SourceDualOneCells B) :
    0 < (incidentPlaquettes e).card := by
  classical
  have hnonempty : Nonempty (TransverseAxes e) := by
    apply Fintype.card_pos_iff.mp
    rw [transverseAxes_card]
    norm_num
  obtain ⟨i⟩ := hnonempty
  let p := incidentCandidateFace e i true
  have hp : p ∈ incidentPlaquettes e := by
    change p ∈ Finset.univ.filter (fun q => linkIncidentPlaquette e q)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    refine ⟨i.1, transverseVertex e i, transverseVertex_spec e i, ?_⟩
    left
    change p.1 = (incidentCandidateFace e i true).1
    rw [incidentCandidateFace_true_val]
  exact Finset.card_pos.mpr ⟨p, hp⟩

theorem incidentPlaquetteCount_bounds (e : SourceDualOneCells B) :
    1 ≤ incidentPlaquetteCount e ∧ incidentPlaquetteCount e ≤ 6 := by
  exact ⟨Nat.succ_le_of_lt (incidentPlaquetteCount_pos e),
    incidentPlaquetteCount_le_six e⟩


theorem linkColor_injective_pair {e f : SourceDualOneCells B}
    (h : linkColor e = linkColor f) :
    linkDirection e = linkDirection f ∧ linkBaseParity e = linkBaseParity f := by
  have hval := congrArg Fin.val h
  simp only [linkColor] at hval
  have hdir : (linkDirection e).val = (linkDirection f).val := by
    have he := (linkDirection e).isLt
    have hf := (linkDirection f).isLt
    have hpe := (linkBaseParity e).isLt
    have hpf := (linkBaseParity f).isLt
    omega
  have hpar : (linkBaseParity e).val = (linkBaseParity f).val := by omega
  exact ⟨Fin.ext hdir, Fin.ext hpar⟩


private theorem sourceLinks_eq_of_coordinates_except
    {e f : SourceDualOneCells B} (i : Fin 4)
    (hi : e.1 i = f.1 i)
    (hrest : ∀ k, k ≠ i → e.1 k = f.1 k) : e = f := by
  apply Subtype.ext
  funext k
  by_cases hk : k = i
  · subst k
    exact hi
  · exact hrest k hk

/-- Sharing one cubical plaquette with the same link direction forces the
base-point parities to differ unless the links are equal. -/
private theorem sameDirection_sharedFace_parity_ne
    {e f : SourceDualOneCells B} {i : Fin 4} {v w : Fin (B i)}
    (hne : e ≠ f)
    (hiv : e.1 i = Sum.inl v) (hfw : f.1 i = Sum.inl w)
    (hface : (dualUpperFace e.1 i v = dualUpperFace f.1 i w ∨
        dualUpperFace e.1 i v = dualLowerFace f.1 i w) ∨
      (dualLowerFace e.1 i v = dualUpperFace f.1 i w ∨
        dualLowerFace e.1 i v = dualLowerFace f.1 i w)) :
    linkBaseParity e ≠ linkBaseParity f := by
  have hrest : ∀ k, k ≠ i → e.1 k = f.1 k := by
    intro k hk
    rcases hface with hface | hface
    · rcases hface with hface | hface
      · have h := congrFun hface k
        simpa [dualUpperFace, hk] using h
      · have h := congrFun hface k
        simpa [dualUpperFace, dualLowerFace, hk] using h
    · rcases hface with hface | hface
      · have h := congrFun hface k
        simpa [dualLowerFace, dualUpperFace, hk] using h
      · have h := congrFun hface k
        simpa [dualLowerFace, hk] using h
  have hstep : linkBaseCoordinate e i + 1 = linkBaseCoordinate f i ∨
      linkBaseCoordinate f i + 1 = linkBaseCoordinate e i := by
    rcases hface with hface | hface
    · rcases hface with hface | hface
      · have hvw : v = w := by
          apply Fin.ext
          have h := congrArg (fun c : DualCoord B i => match c with
            | Sum.inl x => 0
            | Sum.inr x => x.val) (congrFun hface i)
          simp [dualUpperFace] at h
          omega
        have hcoord : e.1 i = f.1 i := by rw [hiv, hfw, hvw]
        exact (hne (sourceLinks_eq_of_coordinates_except i hcoord hrest)).elim
      · have hvw : v.val + 1 = w.val := by
          have h := congrFun hface i
          simp [dualUpperFace, dualLowerFace] at h
          exact h
        left
        simp [linkBaseCoordinate, hiv, hfw]
        omega
    · rcases hface with hface | hface
      · have hvw : w.val + 1 = v.val := by
          have h := congrFun hface i
          simp [dualLowerFace, dualUpperFace] at h
          exact h.symm
        right
        simp [linkBaseCoordinate, hiv, hfw]
        omega
      · have hvw : v = w := by
          apply Fin.ext
          have h := congrArg (fun c : DualCoord B i => match c with
            | Sum.inl x => 0
            | Sum.inr x => x.val) (congrFun hface i)
          simp [dualLowerFace] at h
          omega
        have hcoord : e.1 i = f.1 i := by rw [hiv, hfw, hvw]
        exact (hne (sourceLinks_eq_of_coordinates_except i hcoord hrest)).elim
  have hsumRest : (∑ k ∈ Finset.univ.erase i, linkBaseCoordinate e k) =
      ∑ k ∈ Finset.univ.erase i, linkBaseCoordinate f k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    simp only [linkBaseCoordinate]
    rw [hrest k hki]
  have hsumE : (∑ k : Fin 4, linkBaseCoordinate e k) =
      linkBaseCoordinate e i +
        ∑ k ∈ Finset.univ.erase i, linkBaseCoordinate e k :=
    (Finset.add_sum_erase Finset.univ (linkBaseCoordinate e) (Finset.mem_univ i)).symm
  have hsumF : (∑ k : Fin 4, linkBaseCoordinate f k) =
      linkBaseCoordinate f i +
        ∑ k ∈ Finset.univ.erase i, linkBaseCoordinate f k :=
    (Finset.add_sum_erase Finset.univ (linkBaseCoordinate f) (Finset.mem_univ i)).symm
  have htot : (∑ k : Fin 4, linkBaseCoordinate e k) + 1 =
      ∑ k : Fin 4, linkBaseCoordinate f k ∨
      (∑ k : Fin 4, linkBaseCoordinate f k) + 1 =
      ∑ k : Fin 4, linkBaseCoordinate e k := by
    rcases hstep with hstep | hstep
    · left
      rw [hsumE, hsumF, hsumRest]
      omega
    · right
      rw [hsumE, hsumF, hsumRest]
      omega
  intro hpar
  have hparval := congrArg Fin.val hpar
  simp only [linkBaseParity] at hparval
  rcases htot with htot | htot <;> omega

/-- Two distinct links of one source plaquette have different eight-class colors. -/
theorem linkColor_ne_of_sharedPlaquette {e f : SourceDualOneCells B}
    (hne : e ≠ f)
    (hshare : ∃ p : SourceDualTwoCells B,
      linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p) :
    linkColor e ≠ linkColor f := by
  intro hcolor
  obtain ⟨hdir, hpar⟩ := linkColor_injective_pair hcolor
  rcases hshare with ⟨p, he, hf⟩
  rcases he with ⟨i, v, hiv, hfaceE⟩
  rcases hf with ⟨j, w, hjw, hfaceF⟩
  have haxesE : dualCellAxes p.1 = {linkDirection e, i} := by
    rcases hfaceE with hup | hlo
    · rw [hup]
      exact upperFace_axes_eq e i v
    · rw [hlo]
      exact lowerFace_axes_eq e i v
  have haxesF : dualCellAxes p.1 = {linkDirection f, j} := by
    rcases hfaceF with hup | hlo
    · rw [hup]
      exact upperFace_axes_eq f j w
    · rw [hlo]
      exact lowerFace_axes_eq f j w
  have hiNe : i ≠ linkDirection e := by
    intro heq
    subst i
    have hright := (linkCoord_isRight_iff e (linkDirection e)).mpr rfl
    simp [hiv] at hright
  have hjNe : j ≠ linkDirection f := by
    intro heq
    subst j
    have hright := (linkCoord_isRight_iff f (linkDirection f)).mpr rfl
    simp [hjw] at hright
  have himem : i ∈ dualCellAxes p.1 := by
    rw [haxesE]
    simp
  have himem' : i = linkDirection f ∨ i = j := by
    rw [haxesF] at himem
    simpa using himem
  have hij : i = j := by
    rcases himem' with h | h
    · exact (hiNe (h.trans hdir.symm)).elim
    · exact h
  subst j
  have hface : (dualUpperFace e.1 i v = dualUpperFace f.1 i w ∨
        dualUpperFace e.1 i v = dualLowerFace f.1 i w) ∨
      (dualLowerFace e.1 i v = dualUpperFace f.1 i w ∨
        dualLowerFace e.1 i v = dualLowerFace f.1 i w) := by
    rcases hfaceE with hupE | hloE <;> rcases hfaceF with hupF | hloF
    · exact Or.inl (Or.inl (hupE.symm.trans hupF))
    · exact Or.inl (Or.inr (hupE.symm.trans hloF))
    · exact Or.inr (Or.inl (hloE.symm.trans hupF))
    · exact Or.inr (Or.inr (hloE.symm.trans hloF))
  exact sameDirection_sharedFace_parity_ne hne hiv hjw hface hpar

end FroehlichSpencer.FS82.Currents.SourceLinkColoring

end
