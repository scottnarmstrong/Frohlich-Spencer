/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.SourceCurlCoefficients
public import FroehlichSpencer.FS82.Currents.SourceLinkColoring

@[expose] public section

namespace FroehlichSpencer.FS82.Gaussian.SourceTreeChart

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Gaussian

variable {B : SourceBox}

open Classical

theorem sourceCurlCoefficient_eq_stencil_eval
    (p : SourceDualTwoCells B) (e : SourceDualOneCells B) :
    sourceCurlCoefficient p e =
      dualExteriorDifferenceStencilBasis
        (sourceDualOneEmbedding e) (sourceDualTwoEmbedding p) := by
  exact sourceCurlCoefficient_eq_coordinateStencil p e

theorem sourceCurlCoefficient_sum_faces
    (p : SourceDualTwoCells B) (e : SourceDualOneCells B) :
    sourceCurlCoefficient p e =
      ∑ i : Fin 4, match e.1 i with
        | Sum.inl v =>
            (-1 : ℝ) ^ dualVertexRankBefore e.1 i *
              ((if p.1 = dualUpperFace e.1 i v then 1 else 0) -
                (if p.1 = dualLowerFace e.1 i v then 1 else 0))
        | Sum.inr _ => 0 := by
  rw [sourceCurlCoefficient_eq_stencil_eval]
  unfold dualExteriorDifferenceStencilBasis
  rw [← Finsupp.lapply_apply (M := ℝ) (R := ℝ)
    (a := sourceDualTwoEmbedding p)]
  rw [map_sum (Finsupp.lapply (R := ℝ) (sourceDualTwoEmbedding p))]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : e.1 i <;> simp [sourceDualOneEmbedding, sourceDualTwoEmbedding,
    h, Finsupp.single_apply, smul_eq_mul, eq_comm]

theorem sourceCurlCoefficient_eq_zero_of_not_incident
    (p : SourceDualTwoCells B) (e : SourceDualOneCells B)
    (h : ¬ linkIncidentPlaquette e p) :
    sourceCurlCoefficient p e = 0 := by
  rw [sourceCurlCoefficient_sum_faces]
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

theorem sourceCurlCoefficient_eq_sign_of_incident
    (p : SourceDualTwoCells B) (e : SourceDualOneCells B)
    (h : linkIncidentPlaquette e p) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ sourceCurlCoefficient p e = σ := by
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
    have hsum : sourceCurlCoefficient p e = σ := by
      rw [sourceCurlCoefficient_sum_faces]
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
          rcases ih with h | h
          · right; rw [pow_succ, h]; norm_num
          · left; rw [pow_succ, h]; norm_num
    exact ⟨σ, hσ, hsum⟩
  · let σ : ℝ := -((-1 : ℝ) ^ dualVertexRankBefore e.1 i)
    have haxes : dualCellAxes p.1 = {linkDirection e, i} := by
      rw [hl]
      exact lowerFace_axes_eq e i v
    have hupperlower : dualUpperFace e.1 i v ≠ dualLowerFace e.1 i v := by
      intro heq
      have heq' := congrFun heq i
      simp [dualUpperFace, dualLowerFace] at heq'
    have hsum : sourceCurlCoefficient p e = σ := by
      rw [sourceCurlCoefficient_sum_faces]
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
          rcases ih with h | h
          · right; rw [pow_succ, h]; norm_num
          · left; rw [pow_succ, h]; norm_num
    rcases hσ with hσ | hσ
    · refine ⟨σ, Or.inr ?_, hsum⟩
      simp [σ, hσ]
    · refine ⟨σ, Or.inl ?_, hsum⟩
      simp [σ, hσ]

theorem sourceCurlCoefficient_trichotomy
    (p : SourceDualTwoCells B) (e : SourceDualOneCells B) :
    sourceCurlCoefficient p e = 0 ∨ sourceCurlCoefficient p e = 1 ∨
      sourceCurlCoefficient p e = -1 := by
  by_cases h : linkIncidentPlaquette e p
  · obtain ⟨σ, hσ, hval⟩ := sourceCurlCoefficient_eq_sign_of_incident p e h
    rw [hval]
    rcases hσ with hσ | hσ
    · exact Or.inr (Or.inl hσ)
    · exact Or.inr (Or.inr hσ)
  · exact Or.inl (sourceCurlCoefficient_eq_zero_of_not_incident p e h)

theorem sourceCurlCoefficient_sq_eq_incidenceIndicator
    (p : SourceDualTwoCells B) (e : SourceDualOneCells B) :
    (sourceCurlCoefficient p e) ^ 2 =
      if linkIncidentPlaquette e p then 1 else 0 := by
  classical
  by_cases h : linkIncidentPlaquette e p
  · obtain ⟨σ, hσ, hval⟩ := sourceCurlCoefficient_eq_sign_of_incident p e h
    rw [hval]
    rcases hσ with hσ | hσ
    · simp [h, hσ]
    · simp [h, hσ]
  · rw [sourceCurlCoefficient_eq_zero_of_not_incident p e h]
    simp [h]

theorem sourceCurlCoefficient_sq_sum_eq_incidentPlaquetteCount
    (e : SourceDualOneCells B) :
    ∑ p : SourceDualTwoCells B, (sourceCurlCoefficient p e) ^ 2 =
      (incidentPlaquetteCount e : ℝ) := by
  classical
  calc
    ∑ p : SourceDualTwoCells B, (sourceCurlCoefficient p e) ^ 2 =
        ∑ p : SourceDualTwoCells B,
          if linkIncidentPlaquette e p then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            simp only [sourceCurlCoefficient_sq_eq_incidenceIndicator]
    _ = (incidentPlaquetteCount e : ℝ) := by
      simp [incidentPlaquetteCount, incidentPlaquettes, Finset.sum_boole]


end FroehlichSpencer.FS82.Gaussian.SourceTreeChart

end
