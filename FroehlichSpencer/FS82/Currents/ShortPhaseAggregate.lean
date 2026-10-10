/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.SourceLatticeChain
public import FroehlichSpencer.FS82.Currents.ShortCurrentShell
public import FroehlichSpencer.FS82.Gaussian.LatticeOperator
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex
public import FroehlichSpencer.FS82.Cubical.UnitBox

/-!
This module proves the signed C2 incidence identity needed to apply the
ShortPhase short-current phase estimate to the Gaussian source Hodge field.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Currents.ShortPhaseAggregate

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents.ShortPhase

noncomputable section

variable {B : Box 4}

def bumpedCellEmbedding (c : Cell 4 (bumpedBox B)) : LatticeCell 4 :=
  boxCellEmbedding (fun _ : Fin 4 => 0) c

def sourcePrimalOneForm (τ : EuclideanSpace ℝ (SourceDualOneCells B)) :
    Cell 4 (bumpedBox B) → ℝ := fun c =>
  Cubical.lambdaStarRealZeroExtension (B := B) originZero
    (euclideanToFinsupp τ) (bumpedCellEmbedding c)

theorem bumpedCellEmbedding_lambdaCellToBumpedBox (e : Link B) :
    bumpedCellEmbedding (lambdaCellToBumpedBox e.1) =
      Cubical.lambdaStarEmbedding (B := B) originZero e := by
  funext i
  cases h : e.1 i <;>
    simp [bumpedCellEmbedding, Cubical.boxCellEmbedding, Cubical.embedCoord,
      lambdaCellToBumpedBox, Cubical.lambdaStarEmbedding,
      Cubical.dualCellEmbedding, Cubical.dualEmbedCoord, Cubical.originZero, h]

theorem sourcePrimalOneForm_link (τ : EuclideanSpace ℝ (SourceDualOneCells B))
    (e : Link B) :
    sourcePrimalOneForm τ (lambdaCellToBumpedBox e.1) = τ e := by
  rw [sourcePrimalOneForm, bumpedCellEmbedding_lambdaCellToBumpedBox]
  rw [Cubical.lambdaStarRealZeroExtension_eq_embDomain]
  simp [Finsupp.embDomain_apply, euclideanToFinsupp_apply]

private theorem boxCellEmbedding_upperFace (c : Cell 4 (bumpedBox B))
    (i : Fin 4) (e : Fin ((bumpedBox B) i)) :
    boxCellEmbedding originZero (upperFace c i e) =
      latticeUpperFace (boxCellEmbedding originZero c) i (e.val : ℤ) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [boxCellEmbedding, embedCoord, upperFace, vertexUpdate,
      latticeUpperFace, originZero]
  · simp [boxCellEmbedding, embedCoord, upperFace, vertexUpdate,
      latticeUpperFace, originZero, hji]

private theorem boxCellEmbedding_lowerFace (c : Cell 4 (bumpedBox B))
    (i : Fin 4) (e : Fin ((bumpedBox B) i)) :
    boxCellEmbedding originZero (lowerFace c i e) =
      latticeLowerFace (boxCellEmbedding originZero c) i (e.val : ℤ) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [boxCellEmbedding, embedCoord, lowerFace, vertexUpdate,
      latticeLowerFace, originZero]
  · simp [boxCellEmbedding, embedCoord, lowerFace, vertexUpdate,
      latticeLowerFace, originZero, hji]

private theorem zeroExtension_basis (c : Cell 4 (bumpedBox B)) :
    Cubical.zeroExtension originZero (basisChain c) =
      latticeBasis (boxCellEmbedding originZero c) := by
  simp [Cubical.zeroExtension, basisChain, latticeBasis,
    Finsupp.linearCombination_single]

private theorem cellRankBefore_boxCellEmbedding (c : Cell 4 (bumpedBox B))
    (i : Fin 4) :
    latticeRankBefore (boxCellEmbedding originZero c) i =
      cellRankBefore c i := by
  unfold latticeRankBefore cellRankBefore
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : c j <;>
    simp [boxCellEmbedding, embedCoord, latticeIsEdge, coordIsEdge,
      originZero, h]

private theorem zeroExtension_boundaryBasis (c : Cell 4 (bumpedBox B)) :
    Cubical.zeroExtension originZero (boundaryBasis c) =
      latticeBoundaryBasis (boxCellEmbedding originZero c) := by
  classical
  rw [boundaryBasis, latticeBoundaryBasis]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i with
  | inl v => simp [hci, Cubical.zeroExtension, boxCellEmbedding, embedCoord,
      originZero]
  | inr e =>
      rw [map_smul, map_sub, zeroExtension_basis, zeroExtension_basis,
        cellRankBefore_boxCellEmbedding,
        boxCellEmbedding_upperFace, boxCellEmbedding_lowerFace]
      simp [hci, boxCellEmbedding, embedCoord, originZero]

private theorem zeroExtension_apply_at_image (q : Chain 4 (bumpedBox B))
    (c : Cell 4 (bumpedBox B)) :
    Cubical.zeroExtension originZero q (boxCellEmbedding originZero c) = q c := by
  rw [Cubical.zeroExtension_eq_embDomain]
  simp [Finsupp.embDomain_apply]

private theorem boundaryBasis_apply_matches_lattice
    (c f : Cell 4 (bumpedBox B)) :
    (boundaryBasis c f : ℤ) =
      latticeBoundaryBasis (boxCellEmbedding originZero c)
        (boxCellEmbedding originZero f) := by
  have h := congrArg (fun q : LatticeChain 4 => q (boxCellEmbedding originZero f))
    (zeroExtension_boundaryBasis c)
  rw [zeroExtension_apply_at_image] at h
  exact h

theorem chainCoboundary_sourcePrimalOneForm_signed (τ : EuclideanSpace ℝ (SourceDualOneCells B))
    (f : SourceDualTwoCells B) :
    chainCoboundary (sourcePrimalOneForm τ) (lambdaCellToBumpedBox f.1) =
      dualCellOrientationSign f.1 *
        ((latticeExactOneComplex (B := B) originZero).d₁ τ f) := by
  let E : LatticeCell 4 := dualCellEmbedding originZero f.1
  have hEmbed : bumpedCellEmbedding (lambdaCellToBumpedBox f.1) = E := by
    funext i
    cases h : f.1 i <;>
      simp [E, bumpedCellEmbedding, Cubical.boxCellEmbedding, Cubical.embedCoord,
        lambdaCellToBumpedBox, Cubical.dualCellEmbedding,
        Cubical.dualEmbedCoord, originZero, h]
  have hcurl : sourceRealLatticeCoboundary
      (Cubical.lambdaStarRealZeroExtension (B := B) originZero
        (sourceDualTMap (euclideanToFinsupp (sourceDualTLinear τ)))) E =
        sourceRealLatticeCoboundary
          (Cubical.lambdaStarRealZeroExtension (B := B) originZero
            (euclideanToFinsupp τ)) E := by
    have hT : sourceDualTMap (euclideanToFinsupp (sourceDualTLinear τ)) =
        euclideanToFinsupp τ := by
      apply Finsupp.ext
      intro e
      simp only [sourceDualTMap_apply, euclideanToFinsupp_apply,
        sourceDualTLinear_apply]
      calc
        dualCellOrientationSign e.1 *
            (dualCellOrientationSign e.1 * τ e) =
          dualCellOrientationSign e.1 ^ 2 * τ e := by ring
        _ = τ e := by rw [dualCellOrientationSign_sq]; norm_num
    rw [hT]
  have hcoeff := sourceDualD₁_physical_coefficient originZero
    (sourceDualTLinear τ) f
  change sourceDualD₁ (sourceDualTLinear τ) f = _ at hcoeff
  have hfinite : chainCoboundary (sourcePrimalOneForm τ)
      (lambdaCellToBumpedBox f.1) =
      sourceRealLatticeCoboundary
        (Cubical.lambdaStarRealZeroExtension (B := B) originZero
          (euclideanToFinsupp τ)) E := by
    change chainPairing (sourcePrimalOneForm τ)
        (boundaryBasis (lambdaCellToBumpedBox f.1)) = _
    let q := euclideanToFinsupp τ
    have hq : q = ∑ e : Link B, Finsupp.single e (τ e) := by
      calc
        q = ∑ e : Link B, Finsupp.single e (q e) :=
          (Finsupp.univ_sum_single q).symm
        _ = ∑ e : Link B, Finsupp.single e (τ e) := by
          apply Finset.sum_congr rfl
          intro e he
          simp [q, euclideanToFinsupp_apply]
    have heq (e : Link B) (c : Cell 4 (bumpedBox B)) :
        bumpedCellEmbedding (lambdaCellToBumpedBox e.1) = bumpedCellEmbedding c ↔
          lambdaCellToBumpedBox e.1 = c := by
      change boxCellEmbedding originZero (lambdaCellToBumpedBox e.1) =
          boxCellEmbedding originZero c ↔ _
      exact (boxCellEmbedding originZero).injective.eq_iff
    have hform (c : Cell 4 (bumpedBox B)) :
        sourcePrimalOneForm τ c =
          ∑ e : Link B,
            (if c = lambdaCellToBumpedBox e.1 then τ e else 0) := by
      change Cubical.lambdaStarRealZeroExtension originZero
          (euclideanToFinsupp τ) (boxCellEmbedding originZero c) = _
      rw [show euclideanToFinsupp τ =
          ∑ e : Link B, Finsupp.single e (τ e) by simpa [q] using hq]
      rw [map_sum]
      rw [Finset.sum_apply']
      apply Finset.sum_congr rfl
      intro e he
      rw [show Cubical.lambdaStarRealZeroExtension originZero
          (Finsupp.single e (τ e)) =
            Finsupp.single (Cubical.lambdaStarEmbedding originZero e) (τ e) by
          simp [Cubical.lambdaStarRealZeroExtension,
            Finsupp.linearCombination_single]]
      rw [show Cubical.lambdaStarEmbedding originZero e =
          bumpedCellEmbedding (lambdaCellToBumpedBox e.1) by
          exact (bumpedCellEmbedding_lambdaCellToBumpedBox e).symm]
      have heqc := heq e c
      rw [show boxCellEmbedding originZero c = bumpedCellEmbedding c by rfl]
      simp only [Finsupp.single_apply]
      simp [heqc, eq_comm]
    have hL : chainPairing (sourcePrimalOneForm τ) (boundaryBasis
        (lambdaCellToBumpedBox f.1)) =
        ∑ e : Link B, τ e *
          ((boundaryBasis (lambdaCellToBumpedBox f.1)
            (lambdaCellToBumpedBox e.1) : ℤ) : ℝ) := by
      unfold chainPairing
      simp_rw [hform]
      calc
        (∑ c : Cell 4 (bumpedBox B),
            (∑ e : Link B,
              (if c = lambdaCellToBumpedBox e.1 then τ e else 0)) *
                (boundaryBasis (lambdaCellToBumpedBox f.1) c : ℝ)) =
          ∑ c : Cell 4 (bumpedBox B), ∑ e : Link B,
            (if c = lambdaCellToBumpedBox e.1 then τ e else 0) *
              (boundaryBasis (lambdaCellToBumpedBox f.1) c : ℝ) := by
                congr 1
                funext c
                rw [Finset.sum_mul]
        _ = ∑ e : Link B, ∑ c : Cell 4 (bumpedBox B),
            (if c = lambdaCellToBumpedBox e.1 then τ e else 0) *
              (boundaryBasis (lambdaCellToBumpedBox f.1) c : ℝ) := by
                rw [Finset.sum_comm]
        _ = ∑ e : Link B, τ e *
            (boundaryBasis (lambdaCellToBumpedBox f.1)
              (lambdaCellToBumpedBox e.1) : ℝ) := by
                apply Finset.sum_congr rfl
                intro e he
                rw [Finset.sum_eq_single (lambdaCellToBumpedBox e.1)]
                · simp
                · intro c hc hne
                  simp [hne]
                · intro hnot
                  exact (hnot (Finset.mem_univ _)).elim
    have hR : sourceRealLatticeCoboundary
        (Cubical.lambdaStarRealZeroExtension originZero q) E =
        ∑ e : Link B, τ e *
          (latticeCoboundaryBasis
            (Cubical.lambdaStarEmbedding originZero e) E : ℝ) := by
      rw [show q = ∑ e : Link B, Finsupp.single e (τ e) by exact hq]
      simp_rw [map_sum]
      rw [Finset.sum_apply']
      apply Finset.sum_congr rfl
      intro e he
      rw [show Cubical.lambdaStarRealZeroExtension originZero
          (Finsupp.single e (τ e)) =
            Finsupp.single (Cubical.lambdaStarEmbedding originZero e) (τ e) by
          simp [Cubical.lambdaStarRealZeroExtension,
            Finsupp.linearCombination_single],
        sourceRealLatticeCoboundary_single]
      simp [Finsupp.smul_apply, Cubical.castLatticeChain,
        Finsupp.mapRange_apply, latticeCoboundaryBasis]
    have hterms : ∀ e : Link B,
        τ e * ((boundaryBasis (lambdaCellToBumpedBox f.1)
            (lambdaCellToBumpedBox e.1) : ℤ) : ℝ) =
          τ e * (latticeCoboundaryBasis
            (Cubical.lambdaStarEmbedding originZero e) E : ℝ) := by
      intro e
      have hcell := boundaryBasis_apply_matches_lattice
        (lambdaCellToBumpedBox f.1) (lambdaCellToBumpedBox e.1)
      have hcell' : (boundaryBasis (lambdaCellToBumpedBox f.1)
          (lambdaCellToBumpedBox e.1) : ℝ) =
          latticeBoundaryBasis E (Cubical.lambdaStarEmbedding originZero e) := by
        have hp : boxCellEmbedding originZero
            (lambdaCellToBumpedBox f.1) = E := by
          exact hEmbed
        have he' : boxCellEmbedding originZero
            (lambdaCellToBumpedBox e.1) = Cubical.lambdaStarEmbedding originZero e := by
          exact bumpedCellEmbedding_lambdaCellToBumpedBox e
        rw [hp, he'] at hcell
        exact_mod_cast hcell
      have htranspose := latticeCoboundaryBasis_transpose
        (Cubical.lambdaStarEmbedding originZero e) E
      rw [htranspose]
      exact congrArg (fun x : ℝ => τ e * x) hcell'
    rw [hL, hR]
    apply Finset.sum_congr rfl
    intro e he
    exact hterms e
  rw [hfinite]
  change sourceRealLatticeCoboundary
      (Cubical.lambdaStarRealZeroExtension (B := B) originZero
        (euclideanToFinsupp τ)) E =
    dualCellOrientationSign f.1 * sourceDualD₁ (sourceDualTLinear τ) f
  rw [hcurl] at hcoeff
  have hsignInt : dualCellOrientationSign f.1 ^ 2 = (1 : ℤ) := by
    unfold dualCellOrientationSign axisSetOrientationSign
    rw [pow_two, ← mul_pow]
    norm_num
  have hsign : (dualCellOrientationSign f.1 : ℝ)^2 = 1 := by
    exact_mod_cast hsignInt
  calc
    sourceRealLatticeCoboundary
        (Cubical.lambdaStarRealZeroExtension (B := B) originZero
          (euclideanToFinsupp τ)) E =
      ((dualCellOrientationSign f.1 : ℝ) ^ 2) *
        sourceRealLatticeCoboundary
          (Cubical.lambdaStarRealZeroExtension (B := B) originZero
            (euclideanToFinsupp τ)) E := by
      rw [hsign]
      ring
    _ = dualCellOrientationSign f.1 *
        (dualCellOrientationSign f.1 *
          sourceRealLatticeCoboundary
            (Cubical.lambdaStarRealZeroExtension (B := B) originZero
              (euclideanToFinsupp τ)) E) := by ring
    _ = dualCellOrientationSign f.1 * sourceDualD₁ (sourceDualTLinear τ) f := by
      rw [← hcoeff]


end
end FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
