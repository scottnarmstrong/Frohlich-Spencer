/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.SourceConstructor

/-!
# Centered C1 cube carriers

The exhaustion uses side parameter `N`, dual box side `2N`, and physical
origin `(-N,…,-N)`. Both point and interval coordinates shift by one when
passing from cube `N` to cube `N+1`, exactly preserving C1 physical cells.
-/

public section

namespace FroehlichSpencer.FS82.Infinite

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor

/-- The centered source box with `2N` primal intervals per coordinate. -/
@[expose] def cube (N : ℕ) : Box 4 := fun _ => 2 * N

/-- C1 origin for the centered cube. -/
@[expose] def cubeOrigin (N : ℕ) : Fin 4 → ℤ := fun _ => -(N : ℤ)

/-- Embed one dual coordinate into the next centered box by shifting its
index by one, for either a point or an interval. -/
@[expose] def cubeShiftCoord (N : ℕ) (i : Fin 4) :
    DualCoord (cube N) i → DualCoord (cube (N + 1)) i
  | Sum.inl v => Sum.inl ⟨v.val + 1, by simp [cube]; omega⟩
  | Sum.inr e => Sum.inr ⟨e.val + 1, by simp [cube]; omega⟩

/-- Cellwise carrier embedding for successive centered boxes. -/
@[expose] def cubeShiftCell (N : ℕ) (c : DualCell 4 (cube N)) :
    DualCell 4 (cube (N + 1)) := fun i => cubeShiftCoord N i (c i)


theorem cubeShiftCell_degree (N : ℕ) (c : DualCell 4 (cube N)) :
    dualCellDegree (cubeShiftCell N c) = dualCellDegree c := by
  classical
  apply congrArg Finset.card
  ext i
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : c i <;> simp [cubeShiftCell, cubeShiftCoord, h]

theorem cubeShiftCell_C1 (N : ℕ) (c : DualCell 4 (cube N)) :
    dualCellEmbedding (cubeOrigin (N + 1)) (cubeShiftCell N c) =
      dualCellEmbedding (cubeOrigin N) c := by
  funext i
  cases h : c i <;>
    simp [dualCellEmbedding, dualEmbedCoord, cubeOrigin,
      cubeShiftCell, cubeShiftCoord, h] <;> omega

/-- Nested link carriers under the centered C1 embedding. -/
@[expose] def cubeShiftLinks (N : ℕ) :
    LambdaStarLinks (cube N) → LambdaStarLinks (cube (N + 1)) :=
  fun e => ⟨cubeShiftCell N e.1, by
    rw [cubeShiftCell_degree]
    exact e.2⟩

theorem cubeShiftLinks_C1 (N : ℕ) (e : LambdaStarLinks (cube N)) :
    lambdaStarEmbedding (cubeOrigin (N + 1)) (cubeShiftLinks N e) =
      lambdaStarEmbedding (cubeOrigin N) e := by
  change dualCellEmbedding (cubeOrigin (N + 1))
      (cubeShiftCell N e.1) = dualCellEmbedding (cubeOrigin N) e.1
  exact cubeShiftCell_C1 N e.1


/-- C1 carrier embedding for dual plaquettes of a centered cube. -/
@[expose] def cubePlaquetteEmbedding (N : ℕ) :
    {c : DualCell 4 (cube N) // dualCellDegree c = 2} ↪ LatticeCell 4 where
  toFun f := dualCellEmbedding (cubeOrigin N) f.1
  inj' := by
    intro a b h
    exact Subtype.ext ((dualCellEmbedding (cubeOrigin N)).injective h)


theorem cube_links_nested (N : ℕ) :
    Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) ⊆
      Set.range (lambdaStarEmbedding (B := cube (N + 1)) (cubeOrigin (N + 1))) := by
  rintro x ⟨e, rfl⟩
  exact ⟨cubeShiftLinks N e, cubeShiftLinks_C1 N e⟩

/-- Restrict a physical lattice field to the centered finite dual link carrier.
The C1 embedding already identifies the source-star coordinates with physical
link orientations, so no second C2 sign transport is applied here. -/
@[expose] noncomputable def cubeLinkRestriction (N : ℕ)
    (μ : RealLatticeChain 4) :
    EuclideanSpace ℝ (SourceDualOneCells (cube N)) :=
  finsuppToEuclidean
    (lambdaStarRealCompression (B := cube N) (cubeOrigin N) μ)

/-- The finite co-closed carrier used by the source root on cube `N`. -/
noncomputable abbrev cubeSourceW (N : ℕ) :=
  Gaussian.coClosed (sourceLatticeComplex (B := cube N))

end FroehlichSpencer.FS82.Infinite

end
