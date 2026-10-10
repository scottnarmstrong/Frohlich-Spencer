/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.SourceFilling
public import FroehlichSpencer.FS82.Gaussian.LatticeBridgeHigher
public import FroehlichSpencer.FS82.Gaussian.LatticeOperator

/-!
# C2-twisted source-current lattice chain

Every star-oriented source-link coefficient is multiplied by the C2 sign before
it is embedded in the coordinate-oriented primal lattice.
-/

public section

namespace FroehlichSpencer.FS82.Currents

open Cubical
open FroehlichSpencer.FS82.Gaussian
noncomputable section
open Classical

@[expose] def sourceCurrentOrientationSign {B : Box 4} (e : Link B) : ℤ :=
  sourceDualT e

@[expose] def sourceCurrentOrientationTwist {B : Box 4}
    (q : IntegerCurrent B) : IntegerCurrent B :=
  Finsupp.linearCombination ℤ
    (fun e : Link B => Finsupp.single e (sourceCurrentOrientationSign e)) q

theorem sourceCurrentOrientationTwist_apply {B : Box 4}
    (q : IntegerCurrent B) (e : Link B) :
    sourceCurrentOrientationTwist q e = sourceCurrentOrientationSign e * q e := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [sourceCurrentOrientationTwist]
  | add q r hq hr =>
      change (Finsupp.linearCombination ℤ
          (fun e : Link B => Finsupp.single e (sourceCurrentOrientationSign e))
          (q + r)) e = _
      have hq' : (Finsupp.linearCombination ℤ
          (fun a : Link B => Finsupp.single a (sourceCurrentOrientationSign a)) q) e =
          sourceCurrentOrientationSign e * q e := hq
      have hr' : (Finsupp.linearCombination ℤ
          (fun a : Link B => Finsupp.single a (sourceCurrentOrientationSign a)) r) e =
          sourceCurrentOrientationSign e * r e := hr
      rw [map_add, Finsupp.add_apply, hq', hr']
      simp only [Finsupp.add_apply]
      ring
  | single a z =>
      by_cases h : a = e
      · subst a
        simp [sourceCurrentOrientationTwist, Finsupp.linearCombination_single,
          mul_comm]
      · simp [sourceCurrentOrientationTwist,
          Finsupp.linearCombination_single, h]

theorem sourceCurrentOrientationSign_sq {B : Box 4} (e : Link B) :
    sourceCurrentOrientationSign e ^ 2 = 1 := by
  change sourceDualT e ^ 2 = 1
  rcases sourceDualT_is_pm_one e with hs | hs <;> simp [hs]

private theorem sourceCurrentOrientationSign_ne_zero {B : Box 4}
    (e : Link B) : sourceCurrentOrientationSign e ≠ 0 := by
  intro hzero
  have hs := sourceCurrentOrientationSign_sq e
  rw [hzero] at hs
  norm_num at hs


theorem sourceCurrentOrientationTwist_support {B : Box 4}
    (q : IntegerCurrent B) :
    (sourceCurrentOrientationTwist q).support = q.support := by
  ext e
  simp only [Finsupp.mem_support_iff, sourceCurrentOrientationTwist_apply]
  constructor
  · intro h
    by_contra hq
    apply h
    simp [hq]
  · exact mul_ne_zero (sourceCurrentOrientationSign_ne_zero e)

@[expose] def sourceCurrentLatticeChain {B : Box 4} (q : IntegerCurrent B) :
    Chain 4 (bumpedBox B) :=
  sourceCurrentChain (sourceCurrentOrientationTwist q)

@[simp] theorem sourceCurrentLatticeChain_apply {B : Box 4}
    (q : IntegerCurrent B) (e : Link B) :
    sourceCurrentLatticeChain q (lambdaCellToBumpedBox e.1) =
      sourceCurrentOrientationSign e * q e := by
  rw [sourceCurrentLatticeChain, sourceCurrentChain_apply,
    sourceCurrentOrientationTwist_apply]


private theorem sourcePhysicalExtension_sourceDualOneToChain_apply
    {B : Box 4} (origin : Fin 4 → ℤ)
    (x : EuclideanSpace ℝ (SourceDualOneCells B)) (e : SourceDualOneCells B) :
    sourcePhysicalDualZeroExtension origin (sourceDualOneToChain x)
      (dualCellEmbedding origin e.1) = x e := by
  rw [sourceDualOneToChain, LinearMap.comp_apply,
    sourcePhysicalDualZeroExtension_embedDualSubtype]
  change (Finsupp.linearCombination ℝ
      (fun a : SourceDualOneCells B => Finsupp.single
        ((Function.Embedding.trans sourceDualOneEmbedding
          (dualCellEmbedding origin)) a) 1)
      (euclideanToFinsupp x))
      ((Function.Embedding.trans sourceDualOneEmbedding
        (dualCellEmbedding origin)) e) = x e
  have hh := linearCombination_single_embedding_hits
    (Function.Embedding.trans sourceDualOneEmbedding (dualCellEmbedding origin))
    (euclideanToFinsupp x) e
  simpa [euclideanToFinsupp_apply, Function.Embedding.trans_apply] using hh

private theorem dualOrientationSign_zeroCell {B : Box 4}
    (v : SourceDualZeroCells B) : dualCellOrientationSign v.1 = 1 := by
  have haxes : dualCellAxes v.1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [dualCellDegree] using v.2
  simp [dualCellOrientationSign, axisSetOrientationSign, haxes]

theorem sourceDualD₀_basis_physicalCoefficient {B : Box 4}
    (v : SourceDualZeroCells B) (e : SourceDualOneCells B) :
    sourceDualD₀ (EuclideanSpace.single v (1 : ℝ)) e =
      dualCellOrientationSign e.1 *
        (latticeCoboundaryBasis
          (dualCellEmbedding (fun _ : Fin 4 => 0) v.1)
          (dualCellEmbedding (fun _ : Fin 4 => 0) e.1) : ℝ) := by
  let origin : Fin 4 → ℤ := fun _ => 0
  have hbridge := sourceDualD₀_physical_bridge origin
    (EuclideanSpace.single v (1 : ℝ))
  have hcoeff := congrArg
    (fun q : RealLatticeChain 4 => q (dualCellEmbedding origin e.1)) hbridge
  rw [sourcePhysicalExtension_sourceDualOneToChain_apply] at hcoeff
  have hvertex : dualOrientationSignTwist (sourceDualZeroToChain
      (EuclideanSpace.single v (1 : ℝ))) = Finsupp.single v.1 (1 : ℝ) := by
    classical
    rw [sourceDualZeroToChain, LinearMap.comp_apply]
    rw [show euclideanToFinsupp (EuclideanSpace.single v (1 : ℝ)) =
        Finsupp.single v 1 by
      ext w
      simp [euclideanToFinsupp_apply, Finsupp.single_apply, eq_comm]]
    rw [embedDualSubtype_apply_single]
    rw [dualOrientationSignTwist]
    simp only [Finsupp.linearCombination_single]
    have hzero : dualCellOrientationSign (sourceDualZeroEmbedding v) = 1 := by
      change dualCellOrientationSign v.1 = 1
      exact dualOrientationSign_zeroCell v
    rw [hzero]
    simp [sourceDualZeroEmbedding]
  have hsign : latticeCellOrientationSign (dualCellEmbedding origin e.1) =
      dualCellOrientationSign e.1 := latticeCellOrientationSign_physical origin e.1
  rw [latticeOrientationSignTwist_apply, hsign, hvertex,
    sourcePhysicalDualZeroExtension_single,
    sourceRealLatticeCoboundary_single] at hcoeff
  simp [castLatticeChain] at hcoeff
  simpa [origin] using hcoeff

private def zeroOrigin : Fin 4 → ℤ := fun _ => 0

private theorem cellRankBefore_boxCellEmbedding_zero {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) :
    latticeRankBefore (boxCellEmbedding zeroOrigin c) i =
    cellRankBefore c i := by
  unfold latticeRankBefore cellRankBefore
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : c j <;>
    simp [boxCellEmbedding, embedCoord, latticeIsEdge, coordIsEdge,
      zeroOrigin, h]

private theorem boxCellEmbedding_upperFace_zero {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) (e : Fin (B i)) :
    boxCellEmbedding zeroOrigin (upperFace c i e) =
      latticeUpperFace (boxCellEmbedding zeroOrigin c) i (e.val : ℤ) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [boxCellEmbedding, embedCoord, upperFace, vertexUpdate,
      latticeUpperFace, zeroOrigin]
  · simp [boxCellEmbedding, embedCoord, upperFace, vertexUpdate,
      latticeUpperFace, zeroOrigin, hji]

private theorem boxCellEmbedding_lowerFace_zero {B : Box 4}
    (c : Cell 4 B) (i : Fin 4) (e : Fin (B i)) :
    boxCellEmbedding zeroOrigin (lowerFace c i e) =
      latticeLowerFace (boxCellEmbedding zeroOrigin c) i (e.val : ℤ) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [boxCellEmbedding, embedCoord, lowerFace, vertexUpdate,
      latticeLowerFace, zeroOrigin]
  · simp [boxCellEmbedding, embedCoord, lowerFace, vertexUpdate,
      latticeLowerFace, zeroOrigin, hji]

private theorem zeroExtension_basis {B : Box 4} (c : Cell 4 B) :
    zeroExtension (B := B) zeroOrigin (basisChain c) =
      latticeBasis (boxCellEmbedding zeroOrigin c) := by
  simp [zeroExtension, basisChain, latticeBasis,
    Finsupp.linearCombination_single]

private theorem zeroExtension_boundaryBasis_eq_lattice {B : Box 4}
    (c : Cell 4 B) :
    zeroExtension (B := B) zeroOrigin (boundaryBasis c) =
      latticeBoundaryBasis (boxCellEmbedding zeroOrigin c) := by
  classical
  rw [boundaryBasis, latticeBoundaryBasis]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i with
  | inl v => simp [hci, zeroExtension, boxCellEmbedding, embedCoord,
      zeroOrigin]
  | inr e =>
      rw [map_smul, map_sub, zeroExtension_basis, zeroExtension_basis,
        cellRankBefore_boxCellEmbedding_zero,
        boxCellEmbedding_upperFace_zero, boxCellEmbedding_lowerFace_zero]
      simp [hci, boxCellEmbedding, embedCoord, zeroOrigin]

private theorem zeroExtension_apply_at_image {B : Box 4}
    (q : Chain 4 B) (c : Cell 4 B) :
    zeroExtension (B := B) zeroOrigin q (boxCellEmbedding zeroOrigin c) = q c := by
  rw [zeroExtension_eq_embDomain]
  simp [Finsupp.embDomain_apply]

private theorem boundaryBasis_apply_matches_lattice {B : Box 4}
    (c f : Cell 4 B) :
    (boundaryBasis c f : ℤ) =
      latticeBoundaryBasis (boxCellEmbedding zeroOrigin c)
        (boxCellEmbedding zeroOrigin f) := by
  have h := congrArg
    (fun q : LatticeChain 4 => q (boxCellEmbedding zeroOrigin f))
    (zeroExtension_boundaryBasis_eq_lattice c)
  rw [zeroExtension_apply_at_image] at h
  exact h

private theorem bumped_source_cell_embedding {B : Box 4}
    (c : DualCell 4 B) :
    boxCellEmbedding zeroOrigin (lambdaCellToBumpedBox c) =
      dualCellEmbedding zeroOrigin c := by
  funext i
  cases h : c i <;>
    simp [boxCellEmbedding, embedCoord, lambdaCellToBumpedBox,
      dualCellEmbedding, dualEmbedCoord, zeroOrigin, h]

private theorem sourceDualD₀_basis_matches_finite_boundary
    {B : Box 4} (v : SourceDualZeroCells B) (e : Link B) :
    Cubical.dualExteriorDifference (Finsupp.single v.1 (1 : ℝ)) e.1 =
      (sourceCurrentOrientationSign e : ℝ) *
        (boundaryBasis (lambdaCellToBumpedBox e.1)
          (lambdaCellToBumpedBox v.1) : ℝ) := by
  have hD0 := sourceDualD₀_basis_physicalCoefficient v e
  have hEval : sourceDualD₀ (EuclideanSpace.single v (1 : ℝ)) e =
      Cubical.dualExteriorDifference (Finsupp.single v.1 (1 : ℝ)) e.1 := by
    have hleft :
        sourceDualOneToChain (sourceDualD₀ (EuclideanSpace.single v (1 : ℝ))) e.1 =
          sourceDualD₀ (EuclideanSpace.single v (1 : ℝ)) e := by
      change embedDualSubtype sourceDualOneEmbedding
          (euclideanToFinsupp (sourceDualD₀ (EuclideanSpace.single v (1 : ℝ))))
          (sourceDualOneEmbedding e) = _
      rw [embedDualSubtype_apply_at_image]
      simp [euclideanToFinsupp_apply]
    have hzero : sourceDualZeroToChain (EuclideanSpace.single v (1 : ℝ)) =
        Finsupp.single v.1 (1 : ℝ) := by
      simp [sourceDualZeroToChain, LinearMap.comp_apply,
        euclideanToFinsupp_single, embedDualSubtype_apply_single,
        sourceDualZeroEmbedding]
    have h := congrArg (fun z : DualRealChain 4 B => z e.1)
      (sourceDualD₀_embed_eq_derivative (EuclideanSpace.single v (1 : ℝ)))
    rw [hleft, hzero] at h
    exact h
  rw [hEval] at hD0
  have hV := bumped_source_cell_embedding v.1
  have hE := bumped_source_cell_embedding e.1
  have hV' := hV
  have hE' := hE
  change boxCellEmbedding (fun _ : Fin 4 => 0) (lambdaCellToBumpedBox v.1) =
      dualCellEmbedding (fun _ : Fin 4 => 0) v.1 at hV'
  change boxCellEmbedding (fun _ : Fin 4 => 0) (lambdaCellToBumpedBox e.1) =
      dualCellEmbedding (fun _ : Fin 4 => 0) e.1 at hE'
  rw [← hV', ← hE', latticeCoboundaryBasis_transpose] at hD0
  have hboundary := boundaryBasis_apply_matches_lattice
    (lambdaCellToBumpedBox e.1) (lambdaCellToBumpedBox v.1)
  change (boundaryBasis (lambdaCellToBumpedBox e.1)
      (lambdaCellToBumpedBox v.1) : ℤ) =
    latticeBoundaryBasis
      (boxCellEmbedding (fun _ : Fin 4 => 0) (lambdaCellToBumpedBox e.1))
      (boxCellEmbedding (fun _ : Fin 4 => 0) (lambdaCellToBumpedBox v.1)) at hboundary
  have hboundary' :
      (boundaryBasis (lambdaCellToBumpedBox e.1)
        (lambdaCellToBumpedBox v.1) : ℝ) =
      latticeBoundaryBasis
        (boxCellEmbedding (fun _ : Fin 4 => 0) (lambdaCellToBumpedBox e.1))
        (boxCellEmbedding (fun _ : Fin 4 => 0) (lambdaCellToBumpedBox v.1)) := by
    exact_mod_cast hboundary
  rw [← hboundary'] at hD0
  have hsign := sourceDualT_cast_eq_orientationSign e
  rw [← hsign] at hD0
  simpa [sourceCurrentOrientationSign] using hD0

private theorem sourceCurrentChain_single {B : Box 4}
    (e : Link B) (n : ℤ) :
    sourceCurrentChain (Finsupp.single e n) =
      n • basisChain (lambdaCellToBumpedBox e.1) := by
  rw [sourceCurrentChain, Finsupp.embDomain_single]
  change Finsupp.single (lambdaCellToBumpedBox e.1) n =
    n • Finsupp.single (lambdaCellToBumpedBox e.1) 1
  simp

theorem sourceCurrentLatticeChain_add {B : Box 4}
    (q r : IntegerCurrent B) :
    sourceCurrentLatticeChain (q + r) =
      sourceCurrentLatticeChain q + sourceCurrentLatticeChain r := by
  unfold sourceCurrentLatticeChain
  have ht : sourceCurrentOrientationTwist (q + r) =
      sourceCurrentOrientationTwist q + sourceCurrentOrientationTwist r := by
    ext e
    simp only [sourceCurrentOrientationTwist_apply, Finsupp.add_apply]
    ring
  rw [ht, sourceCurrentChain_add]

theorem sourceCurrentLatticeChain_single {B : Box 4}
    (e : Link B) (n : ℤ) :
    sourceCurrentLatticeChain (Finsupp.single e n) =
      (sourceCurrentOrientationSign e * n) •
        basisChain (lambdaCellToBumpedBox e.1) := by
  unfold sourceCurrentLatticeChain
  have htwist : sourceCurrentOrientationTwist (Finsupp.single e n) =
      Finsupp.single e (sourceCurrentOrientationSign e * n) := by
    ext f
    by_cases h : f = e <;>
      simp [sourceCurrentOrientationTwist_apply, h]
  rw [htwist, sourceCurrentChain_single]

private theorem sourceCurrentLatticeChainDivergence_single
    {B : Box 4} (e : Link B) (n : ℤ) (v : SourceDualZeroCells B) :
    ((boundary (sourceCurrentLatticeChain (Finsupp.single e n))
        (lambdaCellToBumpedBox v.1) : ℤ) : ℝ) =
      currentDivergence (Finsupp.single e n) v := by
  rw [sourceCurrentLatticeChain_single, map_smul, boundary_basis]
  rw [currentDivergence_single]
  rw [sourceDualD₀_basis_matches_finite_boundary]
  simp [Finsupp.smul_apply, Int.cast_mul, mul_assoc, mul_comm]

theorem sourceCurrentLatticeChainDivergence_matches
    {B : Box 4} (q : IntegerCurrent B) (v : SourceDualZeroCells B) :
    ((boundary (sourceCurrentLatticeChain q)
        (lambdaCellToBumpedBox v.1) : ℤ) : ℝ) =
      currentDivergence q v := by
  induction q using Finsupp.induction_linear with
  | zero => simp [sourceCurrentLatticeChain, sourceCurrentOrientationTwist,
      sourceCurrentChain, currentDivergence, sourceDualDivergenceOperator,
      realCurrent]
  | add q r hq hr =>
      rw [sourceCurrentLatticeChain_add, map_add, Finsupp.add_apply,
        Int.cast_add, hq, hr, currentDivergence_add]
  | single e n => exact sourceCurrentLatticeChainDivergence_single e n v

theorem currentDivergence_eq_zero_iff_latticeBoundary_eq_zero
    {B : Box 4} (q : IntegerCurrent B) :
    currentDivergence q = 0 ↔
      ∀ v : SourceDualZeroCells B,
        boundary (sourceCurrentLatticeChain q)
          (lambdaCellToBumpedBox v.1) = 0 := by
  constructor
  · intro hdiv v
    have hreal :
        ((boundary (sourceCurrentLatticeChain q)
            (lambdaCellToBumpedBox v.1) : ℤ) : ℝ) = 0 := by
      calc
        _ = currentDivergence q v :=
          sourceCurrentLatticeChainDivergence_matches q v
        _ = 0 := congrFun hdiv v
    exact Int.cast_eq_zero.mp hreal
  · intro hboundary
    funext v
    have hreal :
        ((boundary (sourceCurrentLatticeChain q)
            (lambdaCellToBumpedBox v.1) : ℤ) : ℝ) = 0 := by
      rw [hboundary v]
      simp
    calc
      currentDivergence q v =
          ((boundary (sourceCurrentLatticeChain q)
            (lambdaCellToBumpedBox v.1) : ℤ) : ℝ) :=
        (sourceCurrentLatticeChainDivergence_matches q v).symm
      _ = 0 := hreal


end
end FroehlichSpencer.FS82.Currents
