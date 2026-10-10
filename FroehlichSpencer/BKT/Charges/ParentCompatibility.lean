/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.SeparatedPatch

/-! # Overlap compatibility at an intermediate parent scale

This is the cross-scale overlap step of  It uses the already selected
intermediate parent in the larger-scale minimum cover; uniqueness of the
cover square meeting the smaller patch then identifies the larger separated
square with that parent. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The offset from a lower source scale to a larger source scale, when the
gap is one through three. -/
def parentGapOffset (k l : PositiveSquareScale) (hkl : k.val < l.val)
    (hgap : l.val - k.val ≤ 3) : ParentOffset :=
  ⟨l.val - k.val, by constructor <;> omega⟩

/-- If two separated patches overlap, the smaller patch lies in the larger
separated square. If the larger-scale minimum cover already contains the
explicit intermediate parent, that square is exactly the parent. This is the
inductive compatibility step used before comparing their parents at a common
later target scale. -/
theorem overlapping_separated_patch_eq_parent
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L)
    (k l : PositiveSquareScale) (hkl : k.val < l.val)
    (hgap : l.val - k.val ≤ 3) (hL : 0 < L)
    (Ck : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val ρ C})
    (Cl : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L l.val ρ C})
    (s t : Finset (Fin L × Fin L))
    (hs : s ∈ separatedSquares boundary L ρ k Ck)
    (ht : t ∈ separatedSquares boundary L ρ l Cl)
    (hoverlap : ((s ∩ chargeSupport ρ) ∩ (t ∩ chargeSupport ρ)).Nonempty)
    (hsourceSide : squareSide k.val ≤ L)
    (hparentDiameter : (squareDiameter boundary L
      (ancestorParent boundary L k (parentGapOffset k l hkl hgap) hL s) : ℝ) <
        squareSeparationThreshold k)
    (hsourceDiameter : (squareDiameter boundary L s : ℝ) <
      squareSeparationThreshold l)
    (hlargerCoverDiameter : ∀ u ∈ Cl.val,
      (squareDiameter boundary L u : ℝ) < squareSeparationThreshold k)
    (hintermediateInCover :
      ancestorParent boundary L k (parentGapOffset k l hkl hgap) hL s ∈ Cl.val) :
    s ∩ chargeSupport ρ = t ∩ chargeSupport ρ ∧
      t = ancestorParent boundary L k (parentGapOffset k l hkl hgap) hL s := by
  classical
  let patch := s ∩ chargeSupport ρ
  let parent := ancestorParent boundary L k (parentGapOffset k l hkl hgap) hL s
  obtain ⟨x, hxCommon⟩ := hoverlap
  change x ∈ patch ∩ (t ∩ chargeSupport ρ) at hxCommon
  rcases Finset.mem_inter.mp hxCommon with ⟨hxPatchCommon, hxTargetPatch⟩
  have hxPatch : x ∈ patch := by
    exact hxPatchCommon
  have hxT : x ∈ t := (Finset.mem_inter.mp hxTargetPatch).1
  have hpatchToT : patch ⊆ t := by
    intro y hy
    by_contra hyT
    have hySupport : y ∈ chargeSupport ρ := (Finset.mem_inter.mp hy).2
    obtain ⟨u, hu, hyu⟩ := Cl.property.1.2 y hySupport
    have htu : u ≠ t := by
      intro hEq
      subst u
      exact hyT hyu
    have htsep : squareSeparationThreshold l ≤
        (squareDistance boundary L t u : ℝ) := by
      have ht' : t ∈ Cl.val ∧ 1 < Cl.val.card ∧
          ∀ v ∈ Cl.val, v ≠ t →
            (2 * (chargeCoverScale : ℝ)) * (2 : ℝ) ^
              (chargeCoverExponent * (l.val + 1 : ℕ)) ≤
                (squareDistance boundary L t v : ℝ) := by
        simpa [separatedSquares] using ht
      simpa [squareSeparationThreshold] using ht'.2.2 u hu htu
    have hdistLower : squareSeparationThreshold l ≤
        latticeDistance boundary L x y :=
      htsep.trans (squareDistance_le_latticeDistance_real_of_mem boundary L t u
        x y hxT hyu)
    have hdistUpper : latticeDistance boundary L x y < squareSeparationThreshold l :=
      lt_of_le_of_lt (latticeDistance_le_squareDiameter_real_of_mem boundary L s
        x y (Finset.mem_inter.mp hxPatch).1 (Finset.mem_inter.mp hy).1)
        hsourceDiameter
    exact (not_lt_of_ge hdistLower) hdistUpper
  have hpatchNonempty : patch.Nonempty :=
    separatedSquare_patch_nonempty boundary L ρ k Ck s hs
  have hparentExact : parent ∩ chargeSupport ρ = patch := by
    dsimp [parent, patch]
    exact separatedSquare_parent_inter_support_eq_patch boundary L ρ k
      (parentGapOffset k l hkl hgap) hL Ck s hs hsourceSide hparentDiameter
  have hparentAllowed : parent ∈ kpSquares boundary L l.val := by
    have hscale : ancestorScale k (parentGapOffset k l hkl hgap) = l.val := by
      change k.val + (l.val - k.val) = l.val
      omega
    simpa [parent, hscale] using ancestorParent_mem_kpSquares boundary L k
      (parentGapOffset k l hkl hgap) hL s
  have hpatchSupport : patch ⊆ chargeSupport ρ := Finset.inter_subset_right
  have hlocal : ∀ u ∈ Cl.val, SquareMeetsPatch patch u →
      SquareLocalToPatch (chargeSupport ρ) patch u := by
    exact squareLocalToPatch_of_pointwise_separation_diameter boundary L
      (chargeSupport ρ) s patch Cl.val (squareSeparationThreshold k) rfl
      (by
        intro y hy z hz
        exact pointwise_separation_of_separatedSquare boundary L ρ k Ck s hs y hy z hz)
      hlargerCoverDiameter
  obtain ⟨old, hold, huniq⟩ := existsUnique_squareMeetingPatch_of_minimum
    boundary L l.val ρ Cl.val Cl.property patch parent hpatchNonempty hpatchSupport
    hparentAllowed
    (by
      intro y hy
      exact (Finset.mem_inter.mp (hparentExact.symm ▸ hy)).1)
    hlocal
  have hparentMeets : SquareMeetsPatch patch parent := by
    rcases hpatchNonempty with ⟨y, hy⟩
    exact ⟨y, hy, (Finset.mem_inter.mp (hparentExact.symm ▸ hy)).1⟩
  have hparentEq : parent = old := huniq parent ⟨hintermediateInCover, hparentMeets⟩
  have htMeets : SquareMeetsPatch patch t := ⟨x, hxPatch, hpatchToT hxPatch⟩
  have htEq : t = old := huniq t ⟨(by
    have ht' := ht
    simp only [separatedSquares, Finset.mem_filter] at ht'
    exact ht'.1), htMeets⟩
  have htParent : t = parent := htEq.trans hparentEq.symm
  refine ⟨?_, htParent⟩
  calc
    s ∩ chargeSupport ρ = parent ∩ chargeSupport ρ := hparentExact.symm
    _ = t ∩ chargeSupport ρ := by rw [htParent]

end FroehlichSpencer.BKT

end
