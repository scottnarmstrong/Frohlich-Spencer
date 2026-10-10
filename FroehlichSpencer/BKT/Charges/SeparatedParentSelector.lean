/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.CompatibleCoverConstraints
public import FroehlichSpencer.BKT.Charges.ParentCompatibility
public import FroehlichSpencer.BKT.Charges.ParentScaleEstimates
public import FroehlichSpencer.BKT.Charges.PeriodicAnchorUniqueness
public import FroehlichSpencer.BKT.Charges.SeparatedPatch

/-! # One shared minimum cover for separated-square parents

This module combines the explicit parent geometry, separation of each source
patch from the remaining support, and the finite compatible-constraint
selector. The remaining geometric inputs are the target-square diameter and
cross-scale compatibility estimates from  -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- A finite compatible family of separated source squares has a common
minimum target cover containing all of its explicit parents. -/
theorem exists_minimumSquareCover_for_separated_parents
    {I : Type} [DecidableEq I]
    (boundary : SquareBoundary) (L targetScale : ℕ) (ρ : ChargeDensity L)
    (indices : Finset I)
    (sourceScale : I → PositiveSquareScale)
    (offset : I → ParentOffset)
    (htargetScale : ∀ i ∈ indices, ancestorScale (sourceScale i) (offset i) = targetScale)
    (sourceCover : ∀ i, {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L (sourceScale i).val ρ C})
    (source : I → Finset (Fin L × Fin L))
    (hL : 0 < L)
    (hseparated : ∀ i ∈ indices,
      source i ∈ separatedSquares boundary L ρ (sourceScale i) (sourceCover i))
    (hsourceSide : ∀ i ∈ indices, squareSide (sourceScale i).val ≤ L)
    (hparentDiameter : ∀ i ∈ indices,
      (squareDiameter boundary L
        (ancestorParent boundary L (sourceScale i) (offset i) hL (source i)) : ℝ) <
          squareSeparationThreshold (sourceScale i))
    (targetCover : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L targetScale ρ C})
    (htargetDiameter : ∀ i ∈ indices, ∀ t ∈ targetCover.val,
      (squareDiameter boundary L t : ℝ) < squareSeparationThreshold (sourceScale i))
    (hcompatible : ∀ i ∈ indices, ∀ j ∈ indices,
      ((source i ∩ chargeSupport ρ) ∩ (source j ∩ chargeSupport ρ)).Nonempty →
        source i ∩ chargeSupport ρ = source j ∩ chargeSupport ρ ∧
          ancestorParent boundary L (sourceScale i) (offset i) hL (source i) =
            ancestorParent boundary L (sourceScale j) (offset j) hL (source j)) :
    ∃ C', IsMinimumSquareCover boundary L targetScale ρ C' ∧
      ∀ i ∈ indices,
        ancestorParent boundary L (sourceScale i) (offset i) hL (source i) ∈ C' := by
  classical
  let patch : I → Finset (Fin L × Fin L) := fun i => source i ∩ chargeSupport ρ
  let parent : I → Finset (Fin L × Fin L) := fun i =>
    ancestorParent boundary L (sourceScale i) (offset i) hL (source i)
  have hnonempty : ∀ i ∈ indices, (patch i).Nonempty := by
    intro i hi
    exact separatedSquare_patch_nonempty boundary L ρ (sourceScale i)
      (sourceCover i) (source i) (hseparated i hi)
  have hsubsupport : ∀ i ∈ indices, patch i ⊆ chargeSupport ρ := by
    intro i hi
    exact Finset.inter_subset_right
  have hcompatible' : ∀ i ∈ indices, ∀ j ∈ indices,
      (patch i ∩ patch j).Nonempty → patch i = patch j ∧ parent i = parent j := by
    intro i hi j hj hinter
    exact hcompatible i hi j hj hinter
  have hallowed : ∀ i ∈ indices, parent i ∈ kpSquares boundary L targetScale := by
    intro i hi
    simpa [parent, htargetScale i hi] using
      ancestorParent_mem_kpSquares boundary L (sourceScale i) (offset i) hL (source i)
  have hexact : ∀ i ∈ indices, parent i ∩ chargeSupport ρ = patch i := by
    intro i hi
    exact separatedSquare_parent_inter_support_eq_patch boundary L ρ
      (sourceScale i) (offset i) hL (sourceCover i) (source i) (hseparated i hi)
      (hsourceSide i hi) (hparentDiameter i hi)
  have hlocal : ∀ i ∈ indices, ∀ t ∈ targetCover.val,
      SquareMeetsPatch (patch i) t →
        SquareLocalToPatch (chargeSupport ρ) (patch i) t := by
    intro i hi t ht hmeet
    exact squareLocalToPatch_of_pointwise_separation_diameter boundary L
      (chargeSupport ρ) (source i) (patch i) targetCover.val
      (squareSeparationThreshold (sourceScale i)) rfl
      (by
        intro x hx y hy
        exact pointwise_separation_of_separatedSquare boundary L ρ
          (sourceScale i) (sourceCover i) (source i) (hseparated i hi) x hx y hy)
      (by intro t ht; exact htargetDiameter i hi t ht)
      t ht hmeet
  obtain ⟨C', hC', hparents⟩ :=
    exists_minimumSquareCover_containing_compatible_parents boundary L targetScale ρ
      indices patch parent targetCover.val targetCover.property hnonempty hsubsupport
      hcompatible' hallowed hexact hlocal
  exact ⟨C', hC', by
    intro i hi
    exact hparents i hi⟩

/-- The compatible-parent selector with all diameter and source-fit
hypotheses discharged from the square geometry. The only remaining geometric
input is the cross-scale overlap compatibility proved during 's finite
induction. -/
theorem exists_minimumSquareCover_for_separated_parents_of_compatible
    {I : Type} [DecidableEq I]
    (boundary : SquareBoundary) (L targetScale : ℕ) (ρ : ChargeDensity L)
    (indices : Finset I)
    (sourceScale : I → PositiveSquareScale)
    (offset : I → ParentOffset)
    (htargetScale : ∀ i ∈ indices,
      ancestorScale (sourceScale i) (offset i) = targetScale)
    (sourceCover : ∀ i, {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L (sourceScale i).val ρ C})
    (source : I → Finset (Fin L × Fin L))
    (hL : 0 < L)
    (hseparated : ∀ i ∈ indices,
      source i ∈ separatedSquares boundary L ρ (sourceScale i) (sourceCover i))
    (targetCover : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L targetScale ρ C})
    (hcompatible : ∀ i ∈ indices, ∀ j ∈ indices,
      ((source i ∩ chargeSupport ρ) ∩ (source j ∩ chargeSupport ρ)).Nonempty →
        source i ∩ chargeSupport ρ = source j ∩ chargeSupport ρ ∧
          ancestorParent boundary L (sourceScale i) (offset i) hL (source i) =
            ancestorParent boundary L (sourceScale j) (offset j) hL (source j)) :
    ∃ C', IsMinimumSquareCover boundary L targetScale ρ C' ∧
      ∀ i ∈ indices,
        ancestorParent boundary L (sourceScale i) (offset i) hL (source i) ∈ C' := by
  have hsourceSide : ∀ i ∈ indices, squareSide (sourceScale i).val ≤ L := by
    intro i hi
    exact squareSide_le_domain_of_mem_separatedSquares boundary L ρ
      (sourceScale i) (sourceCover i) (source i) (hseparated i hi)
  have hLlarge : ∀ i ∈ indices, 1 < L := by
    intro i hi
    have hsideTwo : 2 ≤ squareSide (sourceScale i).val := by
      change 2 ≤ 2 ^ (sourceScale i).val
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (sourceScale i).val :=
          Nat.pow_le_pow_right (by norm_num) (sourceScale i).property
    have hfit := hsourceSide i hi
    have hsideL : 2 ≤ L := hsideTwo.trans hfit
    omega
  have hparentDiameter : ∀ i ∈ indices,
      (squareDiameter boundary L
        (ancestorParent boundary L (sourceScale i) (offset i) hL (source i)) : ℝ) <
          squareSeparationThreshold (sourceScale i) := by
    intro i hi
    exact ancestorScaleSquare_diameter_lt_threshold boundary L (hLlarge i hi)
      (sourceScale i) (offset i)
      (ancestorParent boundary L (sourceScale i) (offset i) hL (source i))
      (ancestorParent_mem_kpSquares boundary L (sourceScale i) (offset i) hL (source i))
  have htargetDiameter : ∀ i ∈ indices, ∀ t ∈ targetCover.val,
      (squareDiameter boundary L t : ℝ) < squareSeparationThreshold (sourceScale i) := by
    intro i hi t ht
    have htScale := htargetScale i hi
    have htSquare : t ∈ kpSquares boundary L (ancestorScale (sourceScale i) (offset i)) := by
      rw [htScale]
      exact targetCover.property.1.1 ht
    exact ancestorScaleSquare_diameter_lt_threshold boundary L (hLlarge i hi)
      (sourceScale i) (offset i) t htSquare
  exact exists_minimumSquareCover_for_separated_parents boundary L targetScale ρ indices
    sourceScale offset htargetScale sourceCover source hL hseparated hsourceSide
    hparentDiameter targetCover htargetDiameter hcompatible

/-- Constraints at one target scale are compatible when every lower-scale
parent has already been placed in the selected minimum cover at each
intermediate source scale. This is the overlap invariant used by the finite
induction in  -/
theorem separated_parent_constraints_compatible_of_intermediate_ordered
    {I : Type} [DecidableEq I]
    (boundary : SquareBoundary) (L targetScale : ℕ) (ρ : ChargeDensity L)
    (indices : Finset I)
    (sourceScale : I → PositiveSquareScale)
    (offset : I → ParentOffset)
    (htargetScale : ∀ i ∈ indices,
      ancestorScale (sourceScale i) (offset i) = targetScale)
    (coverAtScale : (q : PositiveSquareScale) → {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L q.val ρ C})
    (source : I → Finset (Fin L × Fin L))
    (hL : 0 < L)
    (hseparated : ∀ i ∈ indices,
      source i ∈ separatedSquares boundary L ρ (sourceScale i)
        (coverAtScale (sourceScale i)))
    (hselectedIntermediate : ∀ i ∈ indices, ∀ j ∈ indices,
      (sourceScale i).val < (sourceScale j).val →
      ∀ hOffset : (offset j).val < (offset i).val,
        ancestorParent boundary L (sourceScale i)
          (parentOffsetDiff (offset j) (offset i) hOffset) hL (source i) ∈
            (coverAtScale (sourceScale j)).val) :
    ∀ i ∈ indices, ∀ j ∈ indices,
      (sourceScale i).val < (sourceScale j).val →
        ((source i ∩ chargeSupport ρ) ∩ (source j ∩ chargeSupport ρ)).Nonempty →
          source i ∩ chargeSupport ρ = source j ∩ chargeSupport ρ ∧
            ancestorParent boundary L (sourceScale i) (offset i) hL (source i) =
              ancestorParent boundary L (sourceScale j) (offset j) hL (source j) := by
  classical
  intro i hi j hj hkl hoverlap
  have hLlarge : 1 < L := by
    have hside : 2 ≤ squareSide (sourceScale i).val := by
      change 2 ≤ 2 ^ (sourceScale i).val
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (sourceScale i).val :=
          Nat.pow_le_pow_right (by norm_num) (sourceScale i).property
    have hfit := squareSide_le_domain_of_mem_separatedSquares boundary L ρ
      (sourceScale i) (coverAtScale (sourceScale i)) (source i) (hseparated i hi)
    omega
  let k := sourceScale i
  let l := sourceScale j
  have hiTarget := htargetScale i hi
  have hjTarget := htargetScale j hj
  have hOffsets : l.val - k.val = (offset i).val - (offset j).val := by
    change k.val + (offset i).val = targetScale at hiTarget
    change l.val + (offset j).val = targetScale at hjTarget
    dsimp [k, l] at *
    omega
  have hkl' : k.val < l.val := hkl
  have hOffsetOrder : (offset j).val < (offset i).val := by omega
  have hgap : l.val - k.val ≤ 3 := by
    have hji := (offset j).property
    have hii := (offset i).property
    omega
  let gap := parentGapOffset k l hkl hgap
  have hgapEq : gap = parentOffsetDiff (offset j) (offset i) hOffsetOrder := by
    apply Subtype.ext
    dsimp [gap, parentGapOffset, parentOffsetDiff]
    omega
  have hgapTarget : ancestorScale k gap = l.val := by
    change k.val + (l.val - k.val) = l.val
    omega
  have hsourceSide := squareSide_le_domain_of_mem_separatedSquares boundary L ρ
    k (coverAtScale k) (source i) (hseparated i hi)
  have hparent : ancestorParent boundary L k gap hL (source i) ∈ kpSquares boundary L l.val := by
    rw [← hgapTarget]
    exact ancestorParent_mem_kpSquares boundary L k gap hL (source i)
  have hparentDiameter := square_diameter_lt_threshold_of_gap_le_three
    boundary L hLlarge k l hgap _ hparent
  have hsourceSquare : source i ∈ kpSquares boundary L k.val := by
    have hs' := hseparated i hi
    simp only [separatedSquares, Finset.mem_filter] at hs'
    exact (coverAtScale k).property.1.1 hs'.1
  have hsourceDiameter := square_diameter_lt_threshold_of_scale_le
    boundary L hLlarge l k (by omega) (source i) hsourceSquare
  have hlargerDiameter : ∀ u ∈ (coverAtScale l).val,
      (squareDiameter boundary L u : ℝ) < squareSeparationThreshold k := by
    intro u hu
    exact square_diameter_lt_threshold_of_gap_le_three boundary L hLlarge k l
      hgap u ((coverAtScale l).property.1.1 hu)
  have hintermediate :
      ancestorParent boundary L k gap hL (source i) ∈ (coverAtScale l).val := by
    have hsel := hselectedIntermediate i hi j hj hkl hOffsetOrder
    rw [← hgapEq] at hsel
    simpa [k, l] using hsel
  obtain ⟨hpatchEq, htParent⟩ := overlapping_separated_patch_eq_parent
    boundary L ρ k l hkl hgap hL (coverAtScale k) (coverAtScale l)
    (source i) (source j) (hseparated i hi) (hseparated j hj) hoverlap
    hsourceSide hparentDiameter hsourceDiameter hlargerDiameter hintermediate
  have hgapVal : gap.val = (offset i).val - (offset j).val := by
    simpa [parentOffsetDiff] using congrArg Subtype.val hgapEq
  have hgapLtOffset : gap.val < (offset i).val := by
    have hjpos := (offset j).property.1
    rw [hgapVal]
    omega
  have hcompOffset : parentOffsetDiff gap (offset i) hgapLtOffset = offset j := by
    apply Subtype.ext
    change (offset i).val - gap.val = (offset j).val
    rw [hgapVal]
    omega
  have hcompScale : parentScaleShift k gap = l := by
    apply Subtype.ext
    change ancestorScale k gap = l.val
    exact hgapTarget
  have htrans := ancestorParent_trans_total boundary L k gap (offset i)
    hgapLtOffset hL (source i)
  have htParent' : source j = ancestorParent boundary L k gap hL (source i) := by
    simpa [gap] using htParent
  have hparentEq :
      ancestorParent boundary L l (offset j) hL (source j) =
        ancestorParent boundary L k (offset i) hL (source i) := by
    calc
      ancestorParent boundary L l (offset j) hL (source j) =
          ancestorParent boundary L l (offset j) hL
            (ancestorParent boundary L k gap hL (source i)) := by rw [htParent']
      _ = ancestorParent boundary L (parentScaleShift k gap)
            (parentOffsetDiff gap (offset i) hgapLtOffset) hL
              (ancestorParent boundary L k gap hL (source i)) := by
        rw [hcompScale, hcompOffset]
      _ = ancestorParent boundary L k (offset i) hL (source i) := htrans
  exact ⟨hpatchEq, hparentEq.symm⟩

/-- Pairwise compatibility at a target scale follows from the intermediate
cover invariant. Equal source scales use separation in their common selected
cover; unequal scales use the ordered overlap lemma. -/
theorem separated_parent_constraints_compatible_of_intermediate
    {I : Type} [DecidableEq I]
    (boundary : SquareBoundary) (L targetScale : ℕ) (ρ : ChargeDensity L)
    (indices : Finset I)
    (sourceScale : I → PositiveSquareScale)
    (offset : I → ParentOffset)
    (htargetScale : ∀ i ∈ indices,
      ancestorScale (sourceScale i) (offset i) = targetScale)
    (coverAtScale : (q : PositiveSquareScale) → {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L q.val ρ C})
    (source : I → Finset (Fin L × Fin L))
    (hL : 0 < L)
    (hseparated : ∀ i ∈ indices,
      source i ∈ separatedSquares boundary L ρ (sourceScale i)
        (coverAtScale (sourceScale i)))
    (hselectedIntermediate : ∀ i ∈ indices, ∀ j ∈ indices,
      (sourceScale i).val < (sourceScale j).val →
      ∀ hOffset : (offset j).val < (offset i).val,
        ancestorParent boundary L (sourceScale i)
          (parentOffsetDiff (offset j) (offset i) hOffset) hL (source i) ∈
            (coverAtScale (sourceScale j)).val) :
    ∀ i ∈ indices, ∀ j ∈ indices,
      ((source i ∩ chargeSupport ρ) ∩ (source j ∩ chargeSupport ρ)).Nonempty →
        source i ∩ chargeSupport ρ = source j ∩ chargeSupport ρ ∧
          ancestorParent boundary L (sourceScale i) (offset i) hL (source i) =
            ancestorParent boundary L (sourceScale j) (offset j) hL (source j) := by
  classical
  intro i hi j hj hoverlap
  by_cases hsame : (sourceScale i).val = (sourceScale j).val
  · have hscaleEq : sourceScale i = sourceScale j := Subtype.ext hsame
    have hoffsetEq : offset i = offset j := by
      apply Subtype.ext
      have hiTarget := htargetScale i hi
      have hjTarget := htargetScale j hj
      change (sourceScale i).val + (offset i).val = targetScale at hiTarget
      change (sourceScale j).val + (offset j).val = targetScale at hjTarget
      omega
    obtain ⟨x, hx⟩ := hoverlap
    have hx' : x ∈ source i ∩ chargeSupport ρ ∧
        x ∈ source j ∩ chargeSupport ρ := by
      simpa only [Finset.mem_inter] using hx
    have htC : source j ∈ (coverAtScale (sourceScale i)).val := by
      have ht' := hseparated j hj
      simp only [separatedSquares, Finset.mem_filter] at ht'
      rw [← hscaleEq] at ht'
      exact ht'.1
    have hpatchEq : source i = source j := by
      by_contra hneq
      have hs' := hseparated i hi
      have hsData : source i ∈ (coverAtScale (sourceScale i)).val ∧
          1 < (coverAtScale (sourceScale i)).val.card ∧
          ∀ t ∈ (coverAtScale (sourceScale i)).val, t ≠ source i →
            squareSeparationThreshold (sourceScale i) ≤
              (squareDistance boundary L (source i) t : ℝ) := by
        simpa [separatedSquares, squareSeparationThreshold] using hs'
      have hneq' : source j ≠ source i := by
        intro h
        exact hneq h.symm
      have hsep := hsData.2.2 (source j) htC hneq'
      have hxi : x ∈ source i := (Finset.mem_inter.mp hx'.1).1
      have hxj : x ∈ source j := (Finset.mem_inter.mp hx'.2).1
      have hdist := squareDistance_le_latticeDistance_real_of_mem boundary L
        (source i) (source j) x x hxi hxj
      have hthreshold : 0 < squareSeparationThreshold (sourceScale i) := by
        have hlarge := squareSeparationThreshold_gt_32_side (sourceScale i)
        have hsidePosNat : 0 < squareSide (sourceScale i).val :=
          Nat.pow_pos (by decide)
        have hsidePos : 0 < (squareSide (sourceScale i).val : ℝ) := by
          exact_mod_cast hsidePosNat
        linarith
      have hzero : latticeDistance boundary L x x = 0 := by
        cases boundary <;> simp [latticeDistance]
      have hzeroR : (latticeDistance boundary L x x : ℝ) = 0 := by exact_mod_cast hzero
      have hsepZero : squareSeparationThreshold (sourceScale i) ≤ 0 := by
        exact hsep.trans (hdist.trans_eq hzeroR)
      linarith
    refine ⟨by rw [hpatchEq], ?_⟩
    simp [hpatchEq, hscaleEq, hoffsetEq]
  · by_cases hforward : (sourceScale i).val < (sourceScale j).val
    · exact separated_parent_constraints_compatible_of_intermediate_ordered
        boundary L targetScale ρ indices sourceScale offset htargetScale coverAtScale
        source hL hseparated hselectedIntermediate i hi j hj hforward hoverlap
    · have hbackward : (sourceScale j).val < (sourceScale i).val := by omega
      have hoverlap' :
          ((source j ∩ chargeSupport ρ) ∩ (source i ∩ chargeSupport ρ)).Nonempty := by
        obtain ⟨x, hx⟩ := hoverlap
        have hx' : x ∈ source i ∩ chargeSupport ρ ∧
            x ∈ source j ∩ chargeSupport ρ := by
          simpa only [Finset.mem_inter] using hx
        exact ⟨x, Finset.mem_inter.mpr ⟨hx'.2, hx'.1⟩⟩
      obtain ⟨hpatchEq, hparentEq⟩ :=
        separated_parent_constraints_compatible_of_intermediate_ordered
          boundary L targetScale ρ indices sourceScale offset htargetScale coverAtScale
          source hL hseparated hselectedIntermediate j hj i hi hbackward hoverlap'
      exact ⟨hpatchEq.symm, hparentEq.symm⟩

/-- One target-scale step of : if all intermediate parents already lie
in the selected source-scale covers, the explicit parents can be imposed in a
minimum target cover. -/
theorem exists_minimumSquareCover_for_separated_parents_of_intermediate
    {I : Type} [DecidableEq I]
    (boundary : SquareBoundary) (L targetScale : ℕ) (ρ : ChargeDensity L)
    (indices : Finset I)
    (sourceScale : I → PositiveSquareScale)
    (offset : I → ParentOffset)
    (htargetScale : ∀ i ∈ indices,
      ancestorScale (sourceScale i) (offset i) = targetScale)
    (coverAtScale : (q : PositiveSquareScale) → {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L q.val ρ C})
    (source : I → Finset (Fin L × Fin L))
    (hL : 0 < L)
    (hseparated : ∀ i ∈ indices,
      source i ∈ separatedSquares boundary L ρ (sourceScale i)
        (coverAtScale (sourceScale i)))
    (hselectedIntermediate : ∀ i ∈ indices, ∀ j ∈ indices,
      (sourceScale i).val < (sourceScale j).val →
      ∀ hOffset : (offset j).val < (offset i).val,
        ancestorParent boundary L (sourceScale i)
          (parentOffsetDiff (offset j) (offset i) hOffset) hL (source i) ∈
            (coverAtScale (sourceScale j)).val)
    (targetCover : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L targetScale ρ C}) :
    ∃ C', IsMinimumSquareCover boundary L targetScale ρ C' ∧
      ∀ i ∈ indices,
        ancestorParent boundary L (sourceScale i) (offset i) hL (source i) ∈ C' := by
  have hcompatible := separated_parent_constraints_compatible_of_intermediate
    boundary L targetScale ρ indices sourceScale offset htargetScale coverAtScale
    source hL hseparated hselectedIntermediate
  exact exists_minimumSquareCover_for_separated_parents_of_compatible
    boundary L targetScale ρ indices sourceScale offset htargetScale
    (fun i => coverAtScale (sourceScale i)) source hL hseparated targetCover hcompatible

end FroehlichSpencer.BKT

end
