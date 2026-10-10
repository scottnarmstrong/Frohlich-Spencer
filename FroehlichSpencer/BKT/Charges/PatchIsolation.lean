/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.CoverReplacement

/-! # Distance criteria for isolated support patches

These lemmas turn the diameter-versus-separation estimate in  into the
locality condition used by the minimum-cover replacement theorem. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- A point-pair distance bounds the minimum distance between the two sets. -/
theorem squareDistance_le_latticeDistance_of_mem
    (boundary : SquareBoundary) (L : ℕ)
    (s t : Finset (Fin L × Fin L)) (x : Fin L × Fin L) (y : Fin L × Fin L)
    (hx : x ∈ s) (hy : y ∈ t) :
    squareDistance boundary L s t ≤ latticeDistance boundary L x y := by
  classical
  have hprod : (s.product t).Nonempty :=
    ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  have himage : latticeDistance boundary L x y ∈
      (s.product t).image (fun p => latticeDistance boundary L p.1 p.2) :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  unfold squareDistance
  rw [dite_eq_left hprod]
  exact Finset.min'_le _ _ himage

/-- A point-pair distance is bounded by the diameter of a set containing both
points. -/
theorem latticeDistance_le_squareDiameter_of_mem
    (boundary : SquareBoundary) (L : ℕ)
    (s : Finset (Fin L × Fin L)) (x y : Fin L × Fin L)
    (hx : x ∈ s) (hy : y ∈ s) :
    latticeDistance boundary L x y ≤ squareDiameter boundary L s := by
  classical
  have hprod : (s.product s).Nonempty :=
    ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  have himage : latticeDistance boundary L x y ∈
      (s.product s).image (fun p => latticeDistance boundary L p.1 p.2) :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  unfold squareDiameter
  rw [dite_eq_left hprod]
  exact Finset.le_max' _ _ himage

/-- Real coercions of the preceding min-distance and diameter estimates. -/
theorem squareDistance_le_latticeDistance_real_of_mem
    (boundary : SquareBoundary) (L : ℕ)
    (s t : Finset (Fin L × Fin L)) (x : Fin L × Fin L) (y : Fin L × Fin L)
    (hx : x ∈ s) (hy : y ∈ t) :
    (squareDistance boundary L s t : ℝ) ≤ latticeDistance boundary L x y := by
  exact_mod_cast squareDistance_le_latticeDistance_of_mem boundary L s t x y hx hy

theorem latticeDistance_le_squareDiameter_real_of_mem
    (boundary : SquareBoundary) (L : ℕ)
    (s : Finset (Fin L × Fin L)) (x y : Fin L × Fin L)
    (hx : x ∈ s) (hy : y ∈ s) :
    latticeDistance boundary L x y ≤ (squareDiameter boundary L s : ℝ) := by
  exact_mod_cast latticeDistance_le_squareDiameter_of_mem boundary L s x y hx hy

/-- Real-valued form matching the scale threshold in KP (2.4). -/
theorem squareLocalToPatch_of_real_separation_diameter
    (boundary : SquareBoundary) (L : ℕ)
    (support source patch : Finset (Fin L × Fin L))
    (C : Finset (Finset (Fin L × Fin L))) (R : ℝ)
    (hpatchEq : patch = source ∩ support)
    (hseparation : R ≤ (squareDistance boundary L source (support \ source) : ℝ))
    (hdiameter : ∀ t ∈ C, (squareDiameter boundary L t : ℝ) < R) :
    ∀ t ∈ C, SquareMeetsPatch patch t →
      SquareLocalToPatch support patch t := by
  intro t ht hmeet x hxt hxSupport
  by_contra hxPatch
  rcases hmeet with ⟨y, hyPatch, hyT⟩
  have hyInter : y ∈ source ∩ support :=
    Eq.mp (congrArg (fun u : Finset (Fin L × Fin L) => y ∈ u) hpatchEq) hyPatch
  have hySource : y ∈ source := (Finset.mem_inter.mp hyInter).1
  have hxNotSource : x ∉ source := by
    intro hxSource
    apply hxPatch
    have hxInter : x ∈ source ∩ support := Finset.mem_inter.mpr ⟨hxSource, hxSupport⟩
    exact Eq.mp (congrArg (fun u : Finset (Fin L × Fin L) => x ∈ u)
      hpatchEq.symm) hxInter
  have hxOutside : x ∈ support \ source := Finset.mem_sdiff.mpr ⟨hxSupport, hxNotSource⟩
  have hdistLower : R ≤ latticeDistance boundary L y x :=
    hseparation.trans (squareDistance_le_latticeDistance_real_of_mem boundary L source
      (support \ source) y x hySource hxOutside)
  have hdistUpper : latticeDistance boundary L y x < R :=
    lt_of_le_of_lt (latticeDistance_le_squareDiameter_real_of_mem boundary L t y x hyT hxt)
      (hdiameter t ht)
  exact (not_lt_of_ge hdistLower) hdistUpper

/-- Pointwise form used when the source separation is known from its selected
minimum cover. -/
theorem squareLocalToPatch_of_pointwise_separation_diameter
    (boundary : SquareBoundary) (L : ℕ)
    (support source patch : Finset (Fin L × Fin L))
    (C : Finset (Finset (Fin L × Fin L))) (R : ℝ)
    (hpatchEq : patch = source ∩ support)
    (hseparation : ∀ x ∈ source, ∀ y ∈ support \ source,
      R ≤ latticeDistance boundary L x y)
    (hdiameter : ∀ t ∈ C, (squareDiameter boundary L t : ℝ) < R) :
    ∀ t ∈ C, SquareMeetsPatch patch t →
      SquareLocalToPatch support patch t := by
  intro t ht hmeet x hxt hxSupport
  by_contra hxPatch
  rcases hmeet with ⟨y, hyPatch, hyT⟩
  have hyInter : y ∈ source ∩ support :=
    Eq.mp (congrArg (fun u : Finset (Fin L × Fin L) => y ∈ u) hpatchEq) hyPatch
  have hySource : y ∈ source := (Finset.mem_inter.mp hyInter).1
  have hxNotSource : x ∉ source := by
    intro hxSource
    apply hxPatch
    have hxInter : x ∈ source ∩ support := Finset.mem_inter.mpr ⟨hxSource, hxSupport⟩
    exact Eq.mp (congrArg (fun u : Finset (Fin L × Fin L) => x ∈ u)
      hpatchEq.symm) hxInter
  have hxOutside : x ∈ support \ source := Finset.mem_sdiff.mpr ⟨hxSupport, hxNotSource⟩
  have hdistLower := hseparation y hySource x hxOutside
  have hdistUpper : latticeDistance boundary L y x < R :=
    lt_of_le_of_lt (latticeDistance_le_squareDiameter_real_of_mem boundary L t y x hyT hxt)
      (hdiameter t ht)
  exact (not_lt_of_ge hdistLower) hdistUpper

/-- The explicit ancestor intersects the support exactly in the source
patch, once the source is separated and the target parent has diameter below
that separation. -/
theorem ancestorParent_inter_support_eq_source_inter
    (boundary : SquareBoundary) (L : ℕ) (k : PositiveSquareScale)
    (j : ParentOffset) (hL : 0 < L)
    (source support : Finset (Fin L × Fin L))
    (hsource : source ∈ kpSquares boundary L k.val)
    (hsourceSide : squareSide k.val ≤ L) (R : ℝ)
    (hpatchNonempty : (source ∩ support).Nonempty)
    (hseparation : ∀ x ∈ source, ∀ y ∈ support \ source,
      R ≤ latticeDistance boundary L x y)
    (hparentDiameter : (squareDiameter boundary L
      (ancestorParent boundary L k j hL source) : ℝ) < R) :
    ancestorParent boundary L k j hL source ∩ support = source ∩ support := by
  let patch := source ∩ support
  have hsourceParent : source ⊆ ancestorParent boundary L k j hL source :=
    square_subset_ancestorParent boundary L k j hL source hsource hsourceSide
  have hmeet : SquareMeetsPatch patch (ancestorParent boundary L k j hL source) := by
    rcases hpatchNonempty with ⟨x, hx⟩
    exact ⟨x, hx, hsourceParent (Finset.mem_inter.mp hx).1⟩
  have hlocal := squareLocalToPatch_of_pointwise_separation_diameter boundary L support source patch
    {ancestorParent boundary L k j hL source} R rfl hseparation
    (by
      intro t ht
      have ht' := Finset.mem_singleton.mp ht
      subst t
      exact hparentDiameter)
    (ancestorParent boundary L k j hL source) (by simp) hmeet
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hxParent := (Finset.mem_inter.mp hx).1
    have hxSupport := (Finset.mem_inter.mp hx).2
    have hxPatch := hlocal x hxParent hxSupport
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxPatch).1, hxSupport⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxSource, hxSupport⟩
    exact Finset.mem_inter.mpr ⟨hsourceParent hxSource, hxSupport⟩

end FroehlichSpencer.BKT

end
