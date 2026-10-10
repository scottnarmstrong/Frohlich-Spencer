/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.DualComplex3
public import FroehlichSpencer.FS82.XY.Expansion3
public import FroehlichSpencer.FS82.Currents.Current
public import FroehlichSpencer.FS82.Gaussian.RenormalizedFamily

/-!
# The direction and base-point parity coloring of dual links

A dual link is colored by its unique coordinate direction and the parity of
its lattice base point. The geometric plaquette-independence lemma is proved
below from the cubical incidence representation.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY.Renormalization3

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.XY.Expansion3
open Classical

variable {C P : Type*} [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]


variable {B : Dual3Box}

/-- The oriented plaquette-link coefficient in the grounded dual complex's three-dimensional
dual chart, evaluated on a coordinate unit link. -/
noncomputable def dual3ChartIncidence (p : Dual3Plaquettes B)
    (e : Dual3Links B) : ℝ :=
  dual3D₁ (EuclideanSpace.single e 1) p

theorem dual3ChartIncidence_eq_dualExteriorDifference
    (p : Dual3Plaquettes B) (e : Dual3Links B) :
    dual3ChartIncidence p e =
      dualExteriorDifference (Finsupp.single (dual3LinksEmbedding e) (1 : ℝ))
        (dual3PlaquettesEmbedding p) := by
  have hs : dual3LinksToChain (EuclideanSpace.single e 1) =
      Finsupp.single (dual3LinksEmbedding e) (1 : ℝ) := by
    ext c
    simp [dual3LinksToChain, dual3EmbedSubtype, euclideanToFinsupp]
  have h := congrArg (fun q : DualRealChain 3 B => q (dual3PlaquettesEmbedding p))
    (dual3D₁_embed_eq_derivative (EuclideanSpace.single e 1))
  rw [hs] at h
  simpa [dual3ChartIncidence, dual3PlaquettesToChain, LinearMap.comp_apply,
    Finsupp.single_apply] using h

theorem dual3ChartIncidence_eq_coordinateStencil
    (p : Dual3Plaquettes B) (e : Dual3Links B) :
    dual3ChartIncidence p e =
      dualExteriorDifferenceStencilBasis (dual3LinksEmbedding e)
        (dual3PlaquettesEmbedding p) := by
  rw [dual3ChartIncidence_eq_dualExteriorDifference,
    dualExteriorDifference_eq_coordinateStencil,
    dualExteriorDifferenceStencil, Finsupp.linearCombination_single]
  simp


/-- The unique oriented coordinate direction of a dual link. -/
noncomputable def linkDirection (e : Dual3Links B) : Fin 3 :=
  Classical.choose (Finset.card_eq_one.mp e.2)

theorem linkAxes_eq_singleton (e : Dual3Links B) :
    dualCellAxes e.1 = {linkDirection e} :=
  Classical.choose_spec (Finset.card_eq_one.mp e.2)

theorem linkDirection_mem_axes (e : Dual3Links B) :
    linkDirection e ∈ dualCellAxes e.1 := by
  rw [linkAxes_eq_singleton]
  simp

theorem linkAxis_eq_direction (e : Dual3Links B) {i : Fin 3}
    (hi : i ∈ dualCellAxes e.1) : i = linkDirection e := by
  rw [linkAxes_eq_singleton] at hi
  simpa using hi

/-- The integer lattice base-point coordinate of a dual link. -/
def linkBaseCoordinate (e : Dual3Links B) (i : Fin 3) : ℕ :=
  match e.1 i with
  | Sum.inl v => v.val + 1
  | Sum.inr v => v.val

/-- The parity of the sum of the three base-point coordinates. -/
def linkBaseParity (e : Dual3Links B) : Fin 2 :=
  ⟨(∑ i : Fin 3, linkBaseCoordinate e i) % 2, Nat.mod_lt _ (by omega)⟩

/-- The six-class direction and base-point parity coloring. -/
noncomputable def linkColor (e : Dual3Links B) : Fin 6 :=
  ⟨2 * (linkDirection e).val + (linkBaseParity e).val, by
    have hd := (linkDirection e).isLt
    have hp := (linkBaseParity e).isLt
    omega⟩


/-- A dual plaquette is incident to a link when it is one of the two cubical
faces in a transverse coordinate of that link. -/
def linkIncidentPlaquette (e : Dual3Links B) (p : Dual3Plaquettes B) : Prop :=
  ∃ (i : Fin 3) (v : Fin (B i)), e.1 i = Sum.inl v ∧
    (p.1 = dualUpperFace e.1 i v ∨ p.1 = dualLowerFace e.1 i v)

theorem linkCoord_isRight_iff (e : Dual3Links B) (i : Fin 3) :
    (e.1 i).isRight = true ↔ i = linkDirection e := by
  constructor
  · intro h
    apply linkAxis_eq_direction e
    simp [dualCellAxes, h]
  · rintro rfl
    have h := linkDirection_mem_axes e
    simpa [dualCellAxes] using h

theorem linkCoord_isLeft_of_ne_direction (e : Dual3Links B)
    {i : Fin 3} (hi : i ≠ linkDirection e) :
    ∃ v : Fin (B i), e.1 i = Sum.inl v := by
  cases h : e.1 i with
  | inl v => exact ⟨v, rfl⟩
  | inr v =>
      have hr : (e.1 i).isRight = true := by simp [h]
      have := (linkCoord_isRight_iff e i).mp hr
      exact (hi this).elim

theorem upperFace_axes_eq (e : Dual3Links B) (i : Fin 3)
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

theorem lowerFace_axes_eq (e : Dual3Links B) (i : Fin 3)
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


theorem dual3ChartIncidence_sum_faces
    (p : Dual3Plaquettes B) (e : Dual3Links B) :
    dual3ChartIncidence p e =
      ∑ i : Fin 3, match e.1 i with
        | Sum.inl v =>
            (-1 : ℝ) ^ dualVertexRankBefore e.1 i *
              ((if p.1 = dualUpperFace e.1 i v then 1 else 0) -
                (if p.1 = dualLowerFace e.1 i v then 1 else 0))
        | Sum.inr _ => 0 := by
  rw [dual3ChartIncidence_eq_coordinateStencil]
  unfold dualExteriorDifferenceStencilBasis
  rw [← Finsupp.lapply_apply (M := ℝ) (R := ℝ)
    (a := dual3PlaquettesEmbedding p)]
  rw [map_sum (Finsupp.lapply (R := ℝ) (dual3PlaquettesEmbedding p))]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : e.1 i <;> simp [dual3LinksEmbedding, dual3PlaquettesEmbedding,
    h, Finsupp.single_apply, smul_eq_mul, eq_comm]

theorem dual3ChartIncidence_zero_of_not_incident
    (p : Dual3Plaquettes B) (e : Dual3Links B)
    (h : ¬ linkIncidentPlaquette e p) :
    dual3ChartIncidence p e = 0 := by
  rw [dual3ChartIncidence_sum_faces]
  apply Finset.sum_eq_zero
  intro i hi
  cases hcoord : e.1 i with
  | inr k => simp
  | inl v =>
      by_cases hu : p.1 = dualUpperFace e.1 i v
      · exact (h ⟨i, v, hcoord, Or.inl hu⟩).elim
      · by_cases hl : p.1 = dualLowerFace e.1 i v
        · exact (h ⟨i, v, hcoord, Or.inr hl⟩).elim
        · simp [hu, hl]

theorem dual3ChartIncidence_eq_sign_of_incident
    (p : Dual3Plaquettes B) (e : Dual3Links B)
    (h : linkIncidentPlaquette e p) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ dual3ChartIncidence p e = σ := by
  classical
  rcases h with ⟨i, v, hcoord, hu | hl⟩
  · let σ : ℝ := (-1 : ℝ) ^ dualVertexRankBefore e.1 i
    have haxes : dualCellAxes p.1 = {linkDirection e, i} := by
      rw [hu]
      exact upperFace_axes_eq e i v
    have hupperlower : dualUpperFace e.1 i v ≠ dualLowerFace e.1 i v := by
      intro heq
      have heq' := congrFun heq i
      simp [dualUpperFace, dualLowerFace] at heq'
    have hsum : dual3ChartIncidence p e = σ := by
      rw [dual3ChartIncidence_sum_faces]
      rw [Finset.sum_eq_single i]
      · rw [hcoord, hu]
        simp [σ, hupperlower]
      · intro j hj hji
        cases hjcoord : e.1 j with
        | inr k => simp
        | inl w =>
            have hjdir : j ≠ linkDirection e := by
              intro hjdir
              subst j
              have hright := (linkCoord_isRight_iff e (linkDirection e)).2 rfl
              rw [hjcoord] at hright
              simp at hright
            by_cases hju : p.1 = dualUpperFace e.1 j w
            · have hjmem : j ∈ dualCellAxes p.1 := by
                rw [hju, upperFace_axes_eq]
                simp
              rw [haxes] at hjmem
              have hji' : j = linkDirection e ∨ j = i := by
                simpa using hjmem
              rcases hji' with hdir | hii
              · exact (hjdir hdir).elim
              · exact (hji hii).elim
            · by_cases hjl : p.1 = dualLowerFace e.1 j w
              · have hjmem : j ∈ dualCellAxes p.1 := by
                  rw [hjl, lowerFace_axes_eq]
                  simp
                rw [haxes] at hjmem
                have hji' : j = linkDirection e ∨ j = i := by
                  simpa using hjmem
                rcases hji' with hdir | hii
                · exact (hjdir hdir).elim
                · exact (hji hii).elim
              · simp [hju, hjl]
      · simp
    have hσ : σ = 1 ∨ σ = -1 := by
      dsimp [σ]
      induction dualVertexRankBefore e.1 i with
      | zero => left; norm_num
      | succ n ih =>
          rcases ih with hσ | hσ
          · right; rw [pow_succ, hσ]; norm_num
          · left; rw [pow_succ, hσ]; norm_num
    exact ⟨σ, hσ, hsum⟩
  · let σ : ℝ := -((-1 : ℝ) ^ dualVertexRankBefore e.1 i)
    have haxes : dualCellAxes p.1 = {linkDirection e, i} := by
      rw [hl]
      exact lowerFace_axes_eq e i v
    have hupperlower : dualUpperFace e.1 i v ≠ dualLowerFace e.1 i v := by
      intro heq
      have heq' := congrFun heq i
      simp [dualUpperFace, dualLowerFace] at heq'
    have hsum : dual3ChartIncidence p e = σ := by
      rw [dual3ChartIncidence_sum_faces]
      rw [Finset.sum_eq_single i]
      · rw [hcoord, hl]
        simp [σ, Ne.symm hupperlower]
      · intro j hj hji
        cases hjcoord : e.1 j with
        | inr k => simp
        | inl w =>
            have hjdir : j ≠ linkDirection e := by
              intro hjdir
              subst j
              have hright := (linkCoord_isRight_iff e (linkDirection e)).2 rfl
              rw [hjcoord] at hright
              simp at hright
            by_cases hju : p.1 = dualUpperFace e.1 j w
            · have hjmem : j ∈ dualCellAxes p.1 := by
                rw [hju, upperFace_axes_eq]
                simp
              rw [haxes] at hjmem
              have hji' : j = linkDirection e ∨ j = i := by
                simpa using hjmem
              rcases hji' with hdir | hii
              · exact (hjdir hdir).elim
              · exact (hji hii).elim
            · by_cases hjl : p.1 = dualLowerFace e.1 j w
              · have hjmem : j ∈ dualCellAxes p.1 := by
                  rw [hjl, lowerFace_axes_eq]
                  simp
                rw [haxes] at hjmem
                have hji' : j = linkDirection e ∨ j = i := by
                  simpa using hjmem
                rcases hji' with hdir | hii
                · exact (hjdir hdir).elim
                · exact (hji hii).elim
              · simp [hju, hjl]
      · simp
    have hσ : (-1 : ℝ) ^ dualVertexRankBefore e.1 i = 1 ∨
        (-1 : ℝ) ^ dualVertexRankBefore e.1 i = -1 := by
      induction dualVertexRankBefore e.1 i with
      | zero => left; norm_num
      | succ n ih =>
          rcases ih with hσ | hσ
          · right; rw [pow_succ, hσ]; norm_num
          · left; rw [pow_succ, hσ]; norm_num
    rcases hσ with hσ | hσ
    · refine ⟨σ, Or.inr ?_, hsum⟩
      simp [σ, hσ]
    · refine ⟨σ, Or.inl ?_, hsum⟩
      simp [σ, hσ]

/-- Transverse coordinate directions of a dual link. -/
abbrev TransverseAxes (e : Dual3Links B) :=
  {i : Fin 3 // i ≠ linkDirection e}

/-- The dual link has a vertex coordinate in every transverse direction. -/
noncomputable def transverseVertex (e : Dual3Links B)
    (i : TransverseAxes e) : Fin (B i.1) :=
  Classical.choose (linkCoord_isLeft_of_ne_direction e (i := i.1) i.2)

theorem transverseVertex_spec (e : Dual3Links B)
    (i : TransverseAxes e) :
    e.1 i.1 = Sum.inl (transverseVertex e i) :=
  Classical.choose_spec (linkCoord_isLeft_of_ne_direction e (i := i.1) i.2)

/-- The axes `{i,j}` have cardinality two when the directions differ. -/
private theorem dualAxesPair_card {i j : Fin 3} (hij : i ≠ j) :
    ({i, j} : Finset (Fin 3)).card = 2 := by
  have hnot : i ∉ ({j} : Finset (Fin 3)) := by
    intro hm
    exact hij (Finset.mem_singleton.mp hm)
  change (insert i ({j} : Finset (Fin 3))).card = 2
  rw [Finset.card_insert_of_notMem hnot]
  simp

/-- One upper adjacent plaquette in a fixed transverse direction. -/
noncomputable def incidentUpperFace (e : Dual3Links B)
    (i : TransverseAxes e) : Dual3Plaquettes B :=
  ⟨dualUpperFace e.1 i.1 (transverseVertex e i), by
    rw [dualCellDegree, upperFace_axes_eq]
    exact dualAxesPair_card i.property.symm⟩

/-- One lower adjacent plaquette in a fixed transverse direction. -/
noncomputable def incidentLowerFace (e : Dual3Links B)
    (i : TransverseAxes e) : Dual3Plaquettes B :=
  ⟨dualLowerFace e.1 i.1 (transverseVertex e i), by
    rw [dualCellDegree, lowerFace_axes_eq]
    exact dualAxesPair_card i.property.symm⟩

/-- One of the at most two plaquettes adjacent to a link in a fixed transverse
direction. -/
noncomputable def incidentCandidateFace (e : Dual3Links B)
    (i : TransverseAxes e) (upper : Bool) : Dual3Plaquettes B :=
  if upper then incidentUpperFace e i else incidentLowerFace e i

@[simp] theorem incidentCandidateFace_true_val (e : Dual3Links B)
    (i : TransverseAxes e) :
    (incidentCandidateFace e i true).1 =
      dualUpperFace e.1 i.1 (transverseVertex e i) := rfl

@[simp] theorem incidentCandidateFace_false_val (e : Dual3Links B)
    (i : TransverseAxes e) :
    (incidentCandidateFace e i false).1 =
      dualLowerFace e.1 i.1 (transverseVertex e i) := rfl

/-- The finite set of all candidate incident plaquettes. -/
noncomputable def incidentCandidateFaces (e : Dual3Links B) :
    Finset (Dual3Plaquettes B) :=
  Finset.univ.image fun q : TransverseAxes e × Bool =>
    incidentCandidateFace e q.1 q.2

/-- The plaquettes appearing in the link's curl column. -/
noncomputable def incidentPlaquettes (e : Dual3Links B) :
    Finset (Dual3Plaquettes B) :=
  by
    classical
    exact Finset.univ.filter fun p => linkIncidentPlaquette e p

/-- Number of contained dual plaquettes incident to a link. -/
noncomputable def incidentPlaquetteCount (e : Dual3Links B) : ℕ :=
  (incidentPlaquettes e).card


theorem dual3ChartIncidence_sq_eq_incidenceIndicator
    (p : Dual3Plaquettes B) (e : Dual3Links B) :
    (dual3ChartIncidence p e) ^ 2 =
      if linkIncidentPlaquette e p then 1 else 0 := by
  classical
  by_cases h : linkIncidentPlaquette e p
  · obtain ⟨σ, hσ, hval⟩ := dual3ChartIncidence_eq_sign_of_incident p e h
    rw [hval]
    rcases hσ with hσ | hσ
    · simp [h, hσ]
    · simp [h, hσ]
  · rw [dual3ChartIncidence_zero_of_not_incident p e h]
    simp [h]

theorem linkMass_dual3ChartIncidence_eq_incidentPlaquetteCount
    (e : Dual3Links B) :
    linkMass dual3ChartIncidence e = (incidentPlaquetteCount e : ℝ) := by
  classical
  calc
    linkMass dual3ChartIncidence e =
        ∑ p : Dual3Plaquettes B, if linkIncidentPlaquette e p then 1 else 0 := by
      unfold linkMass
      apply Finset.sum_congr rfl
      intro p hp
      rw [dual3ChartIncidence_sq_eq_incidenceIndicator]
    _ = (incidentPlaquetteCount e : ℝ) := by
      simp [incidentPlaquetteCount, incidentPlaquettes, Finset.sum_boole]

theorem incidentPlaquettes_subset_candidates (e : Dual3Links B) :
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

theorem transverseAxes_card (e : Dual3Links B) :
    Fintype.card (TransverseAxes e) = 2 := by
  classical
  simp [TransverseAxes, Fintype.card_subtype_compl]

theorem incidentPlaquetteCount_le_four (e : Dual3Links B) :
    (incidentPlaquettes e).card ≤ 4 := by
  calc
    (incidentPlaquettes e).card ≤ (incidentCandidateFaces e).card :=
      Finset.card_le_card (incidentPlaquettes_subset_candidates e)
    _ ≤ Fintype.card (TransverseAxes e × Bool) := Finset.card_image_le
    _ = 4 := by rw [Fintype.card_prod, transverseAxes_card]; decide

theorem incidentPlaquetteCount_pos (e : Dual3Links B) :
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


theorem linkColor_injective_pair {e f : Dual3Links B}
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


private theorem dualLinks_eq_of_coordinates_except
    {e f : Dual3Links B} (i : Fin 3)
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
    {e f : Dual3Links B} {i : Fin 3} {v w : Fin (B i)}
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
        exact (hne (dualLinks_eq_of_coordinates_except i hcoord hrest)).elim
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
        exact (hne (dualLinks_eq_of_coordinates_except i hcoord hrest)).elim
  have hsumRest : (∑ k ∈ Finset.univ.erase i, linkBaseCoordinate e k) =
      ∑ k ∈ Finset.univ.erase i, linkBaseCoordinate f k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    simp only [linkBaseCoordinate]
    rw [hrest k hki]
  have hsumE : (∑ k : Fin 3, linkBaseCoordinate e k) =
      linkBaseCoordinate e i +
        ∑ k ∈ Finset.univ.erase i, linkBaseCoordinate e k :=
    (Finset.add_sum_erase Finset.univ (linkBaseCoordinate e) (Finset.mem_univ i)).symm
  have hsumF : (∑ k : Fin 3, linkBaseCoordinate f k) =
      linkBaseCoordinate f i +
        ∑ k ∈ Finset.univ.erase i, linkBaseCoordinate f k :=
    (Finset.add_sum_erase Finset.univ (linkBaseCoordinate f) (Finset.mem_univ i)).symm
  have htot : (∑ k : Fin 3, linkBaseCoordinate e k) + 1 =
      ∑ k : Fin 3, linkBaseCoordinate f k ∨
      (∑ k : Fin 3, linkBaseCoordinate f k) + 1 =
      ∑ k : Fin 3, linkBaseCoordinate e k := by
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

/-- Two distinct links of one dual plaquette have different six-class colors. -/
theorem linkColor_ne_of_sharedPlaquette {e f : Dual3Links B}
    (hne : e ≠ f)
    (hshare : ∃ p : Dual3Plaquettes B,
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

/-! ## Six-class mass capture -/

/-- The members of a finite support in one of the six parity-direction colors. -/
noncomputable def colorClass (S : Finset (Dual3Links B)) (c : Fin 6) : Finset (Dual3Links B) :=
  S.filter fun e => linkColor e = c

/-- Squared mass carried by one color class. -/
noncomputable def classMass (S : Finset (Dual3Links B)) (ρ : Dual3Links B → ℝ)
    (c : Fin 6) : ℝ :=
  ∑ e ∈ colorClass S c, ρ e ^ 2

theorem classMass_sum (S : Finset (Dual3Links B)) (ρ : Dual3Links B → ℝ) :
    (∑ c : Fin 6, classMass S ρ c) = ∑ e ∈ S, ρ e ^ 2 := by
  simp only [classMass, colorClass]
  exact Finset.sum_fiberwise S linkColor (fun e => ρ e ^ 2)

/-- A heaviest color captures at least one sixth of the total squared current mass. -/
theorem exists_colorClass_large (S : Finset (Dual3Links B))
    (ρ : Dual3Links B → ℝ) :
    ∃ c : Fin 6, (∑ e ∈ S, ρ e ^ 2) / 6 ≤ classMass S ρ c := by
  classical
  let mass : Fin 6 → ℝ := classMass S ρ
  obtain ⟨c, _, hmax⟩ := Finset.exists_max_image Finset.univ mass Finset.univ_nonempty
  have hsum : (∑ c : Fin 6, mass c) = ∑ e ∈ S, ρ e ^ 2 := by
    exact classMass_sum S ρ
  have hbound : (∑ e ∈ S, ρ e ^ 2) ≤ 6 * mass c := by
    calc
      (∑ e ∈ S, ρ e ^ 2) = ∑ d : Fin 6, mass d := hsum.symm
      _ ≤ ∑ _d : Fin 6, mass c :=
        Finset.sum_le_sum fun d _ => hmax d (Finset.mem_univ d)
      _ = 6 * mass c := by simp [Fintype.card_fin]
  refine ⟨c, ?_⟩
  change (∑ e ∈ S, ρ e ^ 2) / 6 ≤ mass c
  linarith


/-- The nonzero support of one real finite current in the 3D dual-link chart. -/
noncomputable def familyCurrentSupport {I : Type*}
    (ρ : I → Dual3Links B → ℝ) (i : I) : Finset (Dual3Links B) :=
  Finset.univ.filter fun e => ρ i e ≠ 0

theorem familyCurrentSupport_intCast {I : Type*}
    (q : I → Dual3Links B → ℤ) (i : I) :
    familyCurrentSupport (fun j e => (q j e : ℝ)) i = currentSupport (q i) := by
  ext e
  simp [familyCurrentSupport, currentSupport]

/-- Choose, independently for each current, a direction-parity class carrying
at least one sixth of its squared mass. -/
noncomputable def selectedFamilyColor {I : Type*}
    (ρ : I → Dual3Links B → ℝ) (i : I) : Fin 6 :=
  Classical.choose (exists_colorClass_large (familyCurrentSupport ρ i) (ρ i))

/-- The links of current `i` selected for conditional Gaussian integration. -/
noncomputable def selectedFamilyBlock {I : Type*}
    (ρ : I → Dual3Links B → ℝ) (i : I) : Finset (Dual3Links B) :=
  colorClass (familyCurrentSupport ρ i) (selectedFamilyColor ρ i)

/-- The union of selected links in a finite current family. -/
noncomputable def selectedFamilyDomain {I : Type*} [Fintype I]
    (ρ : I → Dual3Links B → ℝ) : Finset (Dual3Links B) :=
  Finset.univ.biUnion (selectedFamilyBlock ρ)

theorem selectedFamilyBlock_subset_support {I : Type*}
    (ρ : I → Dual3Links B → ℝ) (i : I) :
    selectedFamilyBlock ρ i ⊆ familyCurrentSupport ρ i := by
  intro e he
  exact (Finset.mem_filter.mp he).1

theorem selectedFamilyBlock_mass_captures {I : Type*}
    (ρ : I → Dual3Links B → ℝ) (i : I) :
    (∑ e ∈ familyCurrentSupport ρ i, (ρ i e) ^ 2) / 6 ≤
      classMass (familyCurrentSupport ρ i) (ρ i) (selectedFamilyColor ρ i) := by
  exact Classical.choose_spec
    (exists_colorClass_large (familyCurrentSupport ρ i) (ρ i))

theorem selectedFamilyBlock_no_sharedPlaquette {I : Type*}
    (ρ : I → Dual3Links B → ℝ) (i : I) :
    ∀ e ∈ selectedFamilyBlock ρ i, ∀ f ∈ selectedFamilyBlock ρ i,
      e ≠ f → ¬ ∃ p : Dual3Plaquettes B,
        linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p := by
  intro e he f hf hne hshare
  have hce : linkColor e = selectedFamilyColor ρ i :=
    (Finset.mem_filter.mp he).2
  have hcf : linkColor f = selectedFamilyColor ρ i :=
    (Finset.mem_filter.mp hf).2
  have hneq := linkColor_ne_of_sharedPlaquette hne hshare
  exact hneq (hce.trans hcf.symm)

/-- If different source currents are separated by the expansion's local
relation, their selected link sets are disjoint and have no cross activity. -/
theorem selectedFamily_blocks_disjoint_and_crossZero
    {I : Type*} [DecidableEq I]
    (ρ : I → Dual3Links B → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ e ∈ familyCurrentSupport ρ i,
      ∀ f ∈ familyCurrentSupport ρ j, ¬ currentNear e f) :
    (∀ i j, i ≠ j → Disjoint (selectedFamilyBlock ρ i)
      (selectedFamilyBlock ρ j)) ∧
    (∀ i j e, i ≠ j → e ∈ selectedFamilyBlock ρ i → ρ j e = 0) := by
  constructor
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    have hsi := selectedFamilyBlock_subset_support ρ i hei
    have hsj := selectedFamilyBlock_subset_support ρ j hej
    have hrefl : currentNear e e := by
      left
      intro k
      exact ⟨by omega, by omega⟩
    exact (hsep i j hij e hsi e hsj hrefl).elim
  · intro i j e hij hei
    by_contra hne
    have heleft : e ∈ familyCurrentSupport ρ i :=
      selectedFamilyBlock_subset_support ρ i hei
    have heright : e ∈ familyCurrentSupport ρ j := by
      simp [familyCurrentSupport, hne]
    have hrefl : currentNear e e := by
      left
      intro k
      exact ⟨by omega, by omega⟩
    exact (hsep i j hij e heleft e heright hrefl).elim

theorem selectedFamilyDomain_spec {I : Type*} [Fintype I]
    (ρ : I → Dual3Links B → ℝ) (e : Dual3Links B) :
    e ∈ selectedFamilyDomain ρ ↔ ∃ i, e ∈ selectedFamilyBlock ρ i := by
  simp [selectedFamilyDomain]

theorem selectedFamily_chartBlocks_independent
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → Dual3Links B → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ e ∈ familyCurrentSupport ρ i,
      ∀ f ∈ familyCurrentSupport ρ j, ¬ currentNear e f) :
    ∀ p, ∀ e₁ ∈ selectedFamilyDomain ρ, ∀ e₂ ∈ selectedFamilyDomain ρ,
      e₁ ≠ e₂ → dual3ChartIncidence p e₁ = 0 ∨
        dual3ChartIncidence p e₂ = 0 := by
  intro p e₁ he₁ e₂ he₂ hne
  rcases (selectedFamilyDomain_spec ρ e₁).mp he₁ with ⟨i, hi⟩
  rcases (selectedFamilyDomain_spec ρ e₂).mp he₂ with ⟨j, hj⟩
  have hinc (e : Dual3Links B) (hcoeff : dual3ChartIncidence p e ≠ 0) :
      linkIncidentPlaquette e p := by
    by_contra hnot
    exact hcoeff (dual3ChartIncidence_zero_of_not_incident p e hnot)
  by_cases hij : i = j
  · subst j
    have hno := selectedFamilyBlock_no_sharedPlaquette ρ i e₁ hi e₂ hj hne
    by_cases hc₁ : dual3ChartIncidence p e₁ = 0
    · exact Or.inl hc₁
    · by_cases hc₂ : dual3ChartIncidence p e₂ = 0
      · exact Or.inr hc₂
      · exact (hno ⟨p, hinc e₁ hc₁, hinc e₂ hc₂⟩).elim
  · have hs₁ := selectedFamilyBlock_subset_support ρ i hi
    have hs₂ := selectedFamilyBlock_subset_support ρ j hj
    have hnotNear := hsep i j hij e₁ hs₁ e₂ hs₂
    by_cases hc₁ : dual3ChartIncidence p e₁ = 0
    · exact Or.inl hc₁
    · by_cases hc₂ : dual3ChartIncidence p e₂ = 0
      · exact Or.inr hc₂
      · have hshare :
          ∃ p' : Dual3Plaquettes B,
            dual3LinkIncidentPlaquette e₁ p' ∧ dual3LinkIncidentPlaquette e₂ p' := by
          exact ⟨p,
            by simpa [linkIncidentPlaquette, dual3LinkIncidentPlaquette] using hinc e₁ hc₁,
            by simpa [linkIncidentPlaquette, dual3LinkIncidentPlaquette] using hinc e₂ hc₂⟩
        exact (hnotNear (Or.inr hshare)).elim


/-! ## One-link attenuation -/

/-- Selection of six colors and at most four plaquettes per link give the
explicit D=3 Gaussian attenuation constant `1/48`. -/
theorem selectedLinkEnergy_at_least_one48
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Finset ι) (β : ℝ) (ρ : ι → ℝ) (n : ι → ℕ)
    (hβ : 0 ≤ β)
    (hnpos : ∀ b ∈ T, 0 < n b) (hnle : ∀ b ∈ T, n b ≤ 4)
    (hcapture : (∑ b ∈ S, ρ b ^ 2) / 6 ≤ ∑ b ∈ T, ρ b ^ 2) :
    Real.exp (-((β / 2) * ∑ b ∈ T, ρ b ^ 2 / (n b : ℝ))) ≤
      Real.exp (-((β / 48) * ∑ b ∈ S, ρ b ^ 2)) := by
  apply Real.exp_le_exp.mpr
  have hlocal : ∀ b ∈ T, ρ b ^ 2 / 4 ≤ ρ b ^ 2 / (n b : ℝ) := by
    intro b hb
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
      (by exact_mod_cast (hnpos b hb))]
    have hn := hnle b hb
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (sq_nonneg (ρ b))
  have hsum := Finset.sum_le_sum hlocal
  have hscaled : (∑ b ∈ T, ρ b ^ 2) / 4 ≤
      ∑ b ∈ T, ρ b ^ 2 / (n b : ℝ) := by
    simpa [Finset.sum_div] using hsum
  have htarget : (∑ b ∈ S, ρ b ^ 2) / 24 ≤
      ∑ b ∈ T, ρ b ^ 2 / (n b : ℝ) := by
    have hscaledCapture : (∑ b ∈ S, ρ b ^ 2) / 24 ≤
        (∑ b ∈ T, ρ b ^ 2) / 4 := by linarith
    linarith
  have hmul := mul_le_mul_of_nonneg_left htarget
    (div_nonneg hβ (by norm_num : (0 : ℝ) ≤ 2))
  have hscaledTarget : (β / 48) * (∑ b ∈ S, ρ b ^ 2) ≤
      (β / 2) * ∑ b ∈ T, ρ b ^ 2 / (n b : ℝ) := by
    nlinarith [hmul]
  linarith


end FroehlichSpencer.FS82.XY.Renormalization3

end
