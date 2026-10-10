/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Surface.WilsonLoopExpectation
public import FroehlichSpencer.FS82.Wilson.PrimalMeasure
public import FroehlichSpencer.FS82.Cubical.IntegerPrism

/-!
# the literal primal cells and the internal cubical box

The literal primal cells of a rectangle `R` are the cells of the internal box `R.side`
(definitionally), with the same degree and the same embedding into the lattice cells at the
origin `R.origin`.

The internal finite boundary is the lattice boundary of the embedded chain.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.PrimalInterface

open FroehlichSpencer.FS82.Cubical

theorem primalCellDegree_eq (R : Surface.RectBox4) (c : Surface.PrimalCell R) :
    Surface.primalCellDegree R c = cellDegree (B := R.side) c := by
  unfold Surface.primalCellDegree cellDegree cellAxes coordIsEdge
  congr

theorem primalCellEmbedding_eq (R : Surface.RectBox4) (c : Surface.PrimalCell R) :
    Surface.primalCellEmbedding R c = boxCellEmbedding (B := R.side) R.origin c := by
  funext i
  simp only [Surface.primalCellEmbedding, boxCellEmbedding, embedCoord,
    Function.Embedding.coeFn_mk]
  cases c i <;> rfl

/-- The literal links are the internal links. -/
def linkEquiv (R : Surface.RectBox4) :
    Surface.PrimalLinks R ≃ Wilson.PrimalLinks R.side :=
  Equiv.subtypeEquivRight fun c => by rw [primalCellDegree_eq]

/-- The literal plaquettes are the internal plaquettes. -/
def plaquetteEquiv (R : Surface.RectBox4) :
    Surface.PrimalPlaquettes R ≃ Wilson.PrimalPlaquettes R.side :=
  Equiv.subtypeEquivRight fun c => by rw [primalCellDegree_eq]


variable {B : Box 4} (origin : Fin 4 → ℤ)

theorem boxCellEmbedding_upperFace (c : Cell 4 B) (i : Fin 4) (e : Fin (B i)) :
    boxCellEmbedding origin (upperFace c i e) =
      latticeUpperFace (boxCellEmbedding origin c) i (origin i + (e.val : ℤ)) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [boxCellEmbedding, embedCoord, upperFace, vertexUpdate, latticeUpperFace, add_assoc]
  · simp [boxCellEmbedding, embedCoord, upperFace, vertexUpdate, latticeUpperFace, hji]

theorem boxCellEmbedding_lowerFace (c : Cell 4 B) (i : Fin 4) (e : Fin (B i)) :
    boxCellEmbedding origin (lowerFace c i e) =
      latticeLowerFace (boxCellEmbedding origin c) i (origin i + (e.val : ℤ)) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [boxCellEmbedding, embedCoord, lowerFace, vertexUpdate, latticeLowerFace]
  · simp [boxCellEmbedding, embedCoord, lowerFace, vertexUpdate, latticeLowerFace, hji]

theorem zeroExtension_basisChain (c : Cell 4 B) :
    zeroExtension origin (basisChain c) = latticeBasis (boxCellEmbedding origin c) := by
  simp [zeroExtension, basisChain, latticeBasis, Finsupp.linearCombination_single]

theorem latticeRankBefore_boxCellEmbedding (c : Cell 4 B) (i : Fin 4) :
    latticeRankBefore (boxCellEmbedding origin c) i = cellRankBefore c i := by
  unfold latticeRankBefore cellRankBefore
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : c j <;> simp [boxCellEmbedding, embedCoord, latticeIsEdge, coordIsEdge, h]

theorem zeroExtension_boundaryBasis (c : Cell 4 B) :
    zeroExtension origin (boundaryBasis c) = latticeBoundaryBasis (boxCellEmbedding origin c) := by
  classical
  rw [boundaryBasis, latticeBoundaryBasis, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases hci : c i with
  | inl v => simp [hci, boxCellEmbedding, embedCoord]
  | inr e =>
      rw [map_smul, map_sub, zeroExtension_basisChain, zeroExtension_basisChain,
        latticeRankBefore_boxCellEmbedding, boxCellEmbedding_upperFace, boxCellEmbedding_lowerFace]
      simp [hci, boxCellEmbedding, embedCoord]

theorem zeroExtension_apply_embedding (q : Chain 4 B) (c : Cell 4 B) :
    zeroExtension origin q (boxCellEmbedding origin c) = q c := by
  rw [zeroExtension_eq_embDomain]
  simp [Finsupp.embDomain_apply]

/-- The finite boundary is the lattice boundary of the zero extension. -/
theorem zeroExtension_boundary (q : Chain 4 B) :
    zeroExtension origin (boundary q) = latticeBoundary (zeroExtension origin q) := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add, hq, hr]
  | single c z =>
      have hs : Finsupp.single c z = z • basisChain c := by
        simp [basisChain]
      simp only [hs, map_smul, boundary_basis, zeroExtension_boundaryBasis,
        zeroExtension_basisChain, latticeBoundary_basis]

/-- The literal boundary coefficient of a pair of box cells is the internal one. -/
theorem literal_boundaryBasis_apply (R : Surface.RectBox4) (p c : Surface.PrimalCell R) :
    Surface.latticeBoundaryBasis (Surface.primalCellEmbedding R p)
        (Surface.primalCellEmbedding R c) =
      boundaryBasis (B := R.side) p c := by
  rw [primalCellEmbedding_eq, primalCellEmbedding_eq]
  have h := congrArg (fun q : LatticeChain 4 => q (boxCellEmbedding (B := R.side) R.origin c))
    (zeroExtension_boundaryBasis (B := R.side) R.origin p)
  simp only [zeroExtension_apply_embedding] at h
  exact h.symm

/-- A circle chain pairing with the cochain of a link configuration is a sum over the links. -/
theorem circleChainPairing_primalCircleCochain (q : Chain 4 B)
    (z : Wilson.PrimalAngleConfig B) :
    Wilson.circleChainPairing q (Wilson.primalCircleCochain z) =
      ∑ j : Wilson.PrimalLinks B, q j.1 • z j := by
  classical
  unfold Wilson.circleChainPairing
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_fintype q (fun c a => a • Wilson.primalCircleCochain z c)
      (fun c => zero_smul ℤ _)]
  rw [← Finset.sum_filter_of_ne (p := fun c : Cell 4 B => cellDegree c = 1)]
  · rw [Finset.sum_subtype (p := fun c : Cell 4 B => cellDegree c = 1)
      (Finset.univ.filter fun c : Cell 4 B => cellDegree c = 1)
      (fun c => by simp) (fun c => q c • Wilson.primalCircleCochain z c)]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Wilson.primalCircleCochain
    rw [dite_eq_left j.2]
  · intro c _ hne
    by_contra hdeg
    apply hne
    unfold Wilson.primalCircleCochain
    rw [dite_eq_right hdeg, smul_zero]

end FroehlichSpencer.FS82.PrimalInterface

end
