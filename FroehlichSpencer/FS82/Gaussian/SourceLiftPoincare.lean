/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.PoincareSlice
import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

open scoped BigOperators InnerProductSpace
namespace FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Cubical

variable {B : SourceBox}

@[expose] noncomputable def sourceOneLift
    (η : EuclideanSpace ℝ (SourceDualOneCells B)) :
    EuclideanSpace ℝ (DualCell 4 B) :=
  finsuppToEuclidean (sourceDualOneToChain η)

theorem sourceOneLift_apply_of_degree
    (η : EuclideanSpace ℝ (SourceDualOneCells B))
    (q : DualCell 4 B) (hq : dualCellDegree q = 1) :
    sourceOneLift η q = η ⟨q, hq⟩ := by
  change embedDualSubtype sourceDualOneEmbedding (euclideanToFinsupp η)
      (sourceDualOneEmbedding ⟨q, hq⟩) = η ⟨q, hq⟩
  rw [embedDualSubtype_apply_at_image]
  simp [euclideanToFinsupp_apply]

theorem sourceOneLift_apply_of_ne_degree
    (η : EuclideanSpace ℝ (SourceDualOneCells B))
    (q : DualCell 4 B) (hq : dualCellDegree q ≠ 1) :
    sourceOneLift η q = 0 := by
  have hsupp := embedDualSubtype_homogeneous sourceDualOneEmbedding 1
    (by intro e; exact e.2) (euclideanToFinsupp η)
  have hval : sourceDualOneToChain η q = 0 := by
    by_contra h
    have hmem : q ∈ (sourceDualOneToChain η).support :=
      Finsupp.mem_support_iff.mpr h
    exact hq (hsupp q hmem)
  simp [sourceOneLift, hval]

theorem sourceOneLift_inner
    (η ζ : EuclideanSpace ℝ (SourceDualOneCells B)) :
    inner ℝ (sourceOneLift η) (sourceOneLift ζ) = inner ℝ η ζ := by
  classical
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  let f : DualCell 4 B → ℝ := fun q => sourceOneLift ζ q * sourceOneLift η q
  let Comp := {q : DualCell 4 B // dualCellDegree q ≠ 1}
  let e : DualCell 4 B ≃ Sum (SourceDualOneCells B) Comp :=
    { toFun := fun q => if h : dualCellDegree q = 1 then Sum.inl ⟨q, h⟩
        else Sum.inr ⟨q, h⟩
      invFun := fun s => Sum.elim Subtype.val Subtype.val s
      left_inv := by
        intro q
        by_cases h : dualCellDegree q = 1 <;> simp [h]
      right_inv := by
        intro s
        cases s with
        | inl q => simp [q.2]
        | inr q => simp [q.2] }
  have htotal :
      (∑ q : DualCell 4 B, f q) =
        (∑ q : SourceDualOneCells B, f q.1) +
          ∑ q : Comp, f q.1 := by
    calc
      (∑ q : DualCell 4 B, f q) =
          ∑ s : Sum (SourceDualOneCells B) Comp,
            Sum.elim (fun q => f q.1) (fun q => f q.1) s := by
              apply Fintype.sum_equiv e
              intro q
              by_cases h : dualCellDegree q = 1 <;> simp [e, h]
      _ = _ := by simp [Fintype.sum_sum_type]
  have hcomp : (∑ q : Comp, f q.1) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp [f, sourceOneLift_apply_of_ne_degree, q.2]
  have hpos :
      (∑ q : SourceDualOneCells B, f q.1) =
        ∑ q : SourceDualOneCells B, ζ q * η q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hη := sourceOneLift_apply_of_degree η q.1 q.2
    have hζ := sourceOneLift_apply_of_degree ζ q.1 q.2
    simp [f, hη, hζ, mul_comm]
  calc
    (∑ q : DualCell 4 B, f q) =
        (∑ q : SourceDualOneCells B, f q.1) + ∑ q : Comp, f q.1 := htotal
    _ = ∑ q : SourceDualOneCells B, f q.1 := by rw [hcomp]; ring
    _ = ∑ q : SourceDualOneCells B, ζ q * η q := hpos

theorem sumAxisEuclidean_eq_fullExterior
    (x : EuclideanSpace ℝ (DualCell 4 B)) :
    sumAxisEuclidean x =
      finsuppToEuclidean (dualExteriorDifference (euclideanToFinsupp x)) := by
  have h := congrArg
    (fun L : DualRealChain 4 B →ₗ[ℝ] DualRealChain 4 B =>
      L (euclideanToFinsupp x))
    (dualExteriorDifferenceStencil_eq_sum_axis (B := B))
  have h' := congrArg (finsuppToEuclidean (α := DualCell 4 B)) h
  simpa [sumAxisEuclidean, axisEuclidean, LinearMap.comp_apply,
    dualExteriorDifference_eq_coordinateStencil,
    euclideanToFinsupp_finsuppToEuclidean] using h'.symm

@[expose] noncomputable def sourceTwoLift
    (η : EuclideanSpace ℝ (SourceDualTwoCells B)) :
    EuclideanSpace ℝ (DualCell 4 B) :=
  finsuppToEuclidean (sourceDualTwoToChain η)

theorem sourceTwoLift_apply_of_degree
    (η : EuclideanSpace ℝ (SourceDualTwoCells B))
    (q : DualCell 4 B) (hq : dualCellDegree q = 2) :
    sourceTwoLift η q = η ⟨q, hq⟩ := by
  change embedDualSubtype sourceDualTwoEmbedding (euclideanToFinsupp η)
      (sourceDualTwoEmbedding ⟨q, hq⟩) = η ⟨q, hq⟩
  rw [embedDualSubtype_apply_at_image]
  simp [euclideanToFinsupp_apply]

theorem sourceTwoLift_apply_of_ne_degree
    (η : EuclideanSpace ℝ (SourceDualTwoCells B))
    (q : DualCell 4 B) (hq : dualCellDegree q ≠ 2) :
    sourceTwoLift η q = 0 := by
  have hsupp := embedDualSubtype_homogeneous sourceDualTwoEmbedding 2
    (by intro e; exact e.2) (euclideanToFinsupp η)
  have hval : sourceDualTwoToChain η q = 0 := by
    by_contra h
    have hmem : q ∈ (sourceDualTwoToChain η).support :=
      Finsupp.mem_support_iff.mpr h
    exact hq (hsupp q hmem)
  simp [sourceTwoLift, hval]

theorem sourceTwoLift_inner
    (η ζ : EuclideanSpace ℝ (SourceDualTwoCells B)) :
    inner ℝ (sourceTwoLift η) (sourceTwoLift ζ) = inner ℝ η ζ := by
  classical
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  let f : DualCell 4 B → ℝ := fun q => sourceTwoLift ζ q * sourceTwoLift η q
  let Comp := {q : DualCell 4 B // dualCellDegree q ≠ 2}
  let e : DualCell 4 B ≃ Sum (SourceDualTwoCells B) Comp :=
    { toFun := fun q => if h : dualCellDegree q = 2 then Sum.inl ⟨q, h⟩
        else Sum.inr ⟨q, h⟩
      invFun := fun s => Sum.elim Subtype.val Subtype.val s
      left_inv := by
        intro q
        by_cases h : dualCellDegree q = 2 <;> simp [h]
      right_inv := by
        intro s
        cases s with
        | inl q => simp [q.2]
        | inr q => simp [q.2] }
  have htotal :
      (∑ q : DualCell 4 B, f q) =
        (∑ q : SourceDualTwoCells B, f q.1) +
          ∑ q : Comp, f q.1 := by
    calc
      (∑ q : DualCell 4 B, f q) =
          ∑ s : Sum (SourceDualTwoCells B) Comp,
            Sum.elim (fun q => f q.1) (fun q => f q.1) s := by
              apply Fintype.sum_equiv e
              intro q
              by_cases h : dualCellDegree q = 2 <;> simp [e, h]
      _ = _ := by simp [Fintype.sum_sum_type]
  have hcomp : (∑ q : Comp, f q.1) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp [f, sourceTwoLift_apply_of_ne_degree, q.2]
  have hpos :
      (∑ q : SourceDualTwoCells B, f q.1) =
        ∑ q : SourceDualTwoCells B, ζ q * η q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hη := sourceTwoLift_apply_of_degree η q.1 q.2
    have hζ := sourceTwoLift_apply_of_degree ζ q.1 q.2
    simp [f, hη, hζ, mul_comm]
  calc
    (∑ q : DualCell 4 B, f q) =
        (∑ q : SourceDualTwoCells B, f q.1) + ∑ q : Comp, f q.1 := htotal
    _ = ∑ q : SourceDualTwoCells B, f q.1 := by rw [hcomp]; ring
    _ = ∑ q : SourceDualTwoCells B, ζ q * η q := hpos

theorem sourceOneLift_sumAxis_eq_d1
    (η : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sumAxisEuclidean (sourceOneLift η) = sourceTwoLift (sourceDualD₁ η) := by
  rw [sumAxisEuclidean_eq_fullExterior]
  simp only [sourceOneLift, sourceTwoLift,
    euclideanToFinsupp_finsuppToEuclidean]
  rw [← sourceDualD₁_embed_eq_derivative]

theorem sourceOneLift_homogeneous_support
    (η : EuclideanSpace ℝ (SourceDualOneCells B)) :
    ∀ q : DualCell 4 B, dualCellDegree q ≠ 1 → sourceOneLift η q = 0 := by
  intro q hq
  exact sourceOneLift_apply_of_ne_degree η q hq

theorem inner_lift_of_homogeneous_support
    (η : EuclideanSpace ℝ (SourceDualOneCells B))
    (y : EuclideanSpace ℝ (DualCell 4 B)) (k : ℕ)
    (hη : ∀ q : DualCell 4 B, dualCellDegree q ≠ 1 → sourceOneLift η q = 0)
    (hy : ∀ q : DualCell 4 B, dualCellDegree q ≠ k → y q = 0)
    (hk : k ≠ 1) : inner ℝ (sourceOneLift η) y = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hdeg : dualCellDegree q = 1
  · have hky : dualCellDegree q ≠ k := by omega
    simp [hy q hky]
  · simp [hη q hdeg]

theorem sumAxisAdjoint_sourceOneLift_eq_zero
    (η : EuclideanSpace ℝ (SourceDualOneCells B))
    (hco : sourceDualD₀.adjoint η = 0) :
    sumAxisAdjointEuclidean (sourceOneLift η) = 0 := by
  classical
  apply PiLp.ext
  intro q
  let bq := EuclideanSpace.single q (1 : ℝ)
  have hbqF : euclideanToFinsupp bq = Finsupp.single q (1 : ℝ) := by
    ext c
    simp [bq, euclideanToFinsupp_apply, EuclideanSpace.single,
      Finsupp.single_apply, eq_comm]
  have hcoord : (sumAxisAdjointEuclidean (sourceOneLift η)) q =
      inner ℝ (sumAxisEuclidean bq) (sourceOneLift η) := by
    have h := sumAxis_adjoint_inner bq (sourceOneLift η)
    rw [EuclideanSpace.inner_single_left] at h
    simpa [bq] using h.symm
  rw [hcoord]
  by_cases hdeg : dualCellDegree q = 0
  · let q₀ : SourceDualZeroCells B := ⟨q, hdeg⟩
    have hderiv : sumAxisEuclidean bq =
        sourceOneLift (sourceDualD₀ (EuclideanSpace.single q₀ (1 : ℝ))) := by
      rw [sumAxisEuclidean_eq_fullExterior]
      have hsource : sourceDualZeroToChain (EuclideanSpace.single q₀ (1 : ℝ)) =
          euclideanToFinsupp bq := by
        have hzeroF : euclideanToFinsupp
            (EuclideanSpace.single q₀ (1 : ℝ)) = Finsupp.single q₀ (1 : ℝ) := by
          ext c
          simp [q₀, euclideanToFinsupp_apply, EuclideanSpace.single,
            Finsupp.single_apply, eq_comm]
        calc
          sourceDualZeroToChain (EuclideanSpace.single q₀ (1 : ℝ)) =
              embedDualSubtype sourceDualZeroEmbedding (Finsupp.single q₀ (1 : ℝ)) := by
                change embedDualSubtype sourceDualZeroEmbedding
                  (euclideanToFinsupp (EuclideanSpace.single q₀ (1 : ℝ))) = _
                rw [hzeroF]
          _ = Finsupp.single q (1 : ℝ) := by
                rw [embedDualSubtype_apply_single]
                rfl
          _ = euclideanToFinsupp bq := hbqF.symm
      rw [← hsource, ← sourceDualD₀_embed_eq_derivative]
      rfl
    rw [hderiv, sourceOneLift_inner]
    have hadj := LinearMap.adjoint_inner_right
      sourceDualD₀ (EuclideanSpace.single q₀ (1 : ℝ)) η
    rw [hco] at hadj
    simp at hadj
    exact hadj.symm
  · by_cases hdeg4 : dualCellDegree q = 4
    · have hcard : (dualCellAxes q).card = 4 := by
        simpa [dualCellDegree] using hdeg4
      have haxes : dualCellAxes q = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro i
        by_contra hi
        have hne : dualCellAxes q ≠ Finset.univ := by
          intro h
          apply hi
          rw [h]
          simp
        have hlt := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.subset_univ _, hne⟩)
        have hlt' : (dualCellAxes q).card < 4 := by simpa using hlt
        omega
      have hright : ∀ i : Fin 4, ∃ e : Fin (B i + 1), q i = Sum.inr e := by
        intro i
        cases h : q i with
        | inl v =>
            have hi : i ∈ dualCellAxes q := by
              rw [haxes]
              simp
            simp [dualCellAxes, h] at hi
        | inr e => exact ⟨e, rfl⟩
      have hD0 : dualExteriorDifference (Finsupp.single q (1 : ℝ)) = 0 := by
        rw [dualExteriorDifference_basis_eq_coordinateStencil]
        unfold Cubical.dualExteriorDifferenceStencilBasis
        apply Finset.sum_eq_zero
        intro i hi
        obtain ⟨e, he⟩ := hright i
        simp [he]
      have hbqF : euclideanToFinsupp bq = Finsupp.single q (1 : ℝ) := by
        ext c
        simp [bq, euclideanToFinsupp_apply, EuclideanSpace.single,
          Finsupp.single_apply, eq_comm]
      have hcurlzero : sumAxisEuclidean bq = 0 := by
        rw [sumAxisEuclidean_eq_fullExterior, hbqF, hD0]
        simp
      rw [hcurlzero]
      simp
    · have hdegree_le : dualCellDegree q ≤ 4 := by
        unfold dualCellDegree
        exact Finset.card_le_card (Finset.subset_univ _)
      have hfull : dualCellDegree q < 4 := by omega
      have hsingle :
        dualRealHomogeneousSupport
          (dualExteriorDifference (Finsupp.single q (1 : ℝ)))
          (dualCellDegree q + 1) := by
        exact dualExteriorDifference_homogeneousSupport _ (dualCellDegree q)
          hfull (by
            intro c hc
            have hcq : c = q := by
              simpa [Finsupp.mem_support_iff] using hc
            simp [hcq])
      have hy : ∀ c : DualCell 4 B,
        dualCellDegree c ≠ dualCellDegree q + 1 →
          (sumAxisEuclidean bq) c = 0 := by
        have hsum : sumAxisEuclidean bq =
            finsuppToEuclidean
              (dualExteriorDifference (Finsupp.single q (1 : ℝ))) := by
          rw [sumAxisEuclidean_eq_fullExterior, hbqF]
        intro c hc
        rw [hsum]
        simp only [finsuppToEuclidean_apply]
        by_contra hn
        have hs := hsingle c (Finsupp.mem_support_iff.mpr hn)
        exact hc hs
      have hperp := inner_lift_of_homogeneous_support η
        (sumAxisEuclidean bq) (dualCellDegree q + 1)
        (sourceOneLift_homogeneous_support η) hy (by omega)
      simpa [real_inner_comm] using hperp

end FroehlichSpencer.FS82.Gaussian
end
