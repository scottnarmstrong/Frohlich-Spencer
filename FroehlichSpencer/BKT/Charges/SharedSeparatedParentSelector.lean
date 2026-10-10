/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.SeparatedParentSelector

/-! # One shared minimum-cover selector across all scales

The finite induction constructs a minimum cover scale by scale. At a new
target scale, only the preceding four source scales can prescribe parents.
The intermediate-cover invariant makes those prescriptions compatible.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

structure SeparatedSelectorState (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) (hL : 0 < L) (n : ℕ) where
  covers : ℕ → Finset (Finset (Fin L × Fin L))
  minimum : ∀ k, IsMinimumSquareCover boundary L k ρ (covers k)
  selected : ∀ (k : ℕ) (hk : 1 ≤ k) (j : ParentOffset),
    k + j.val ≤ n →
    ∀ s ∈ separatedSquares boundary L ρ ⟨k, hk⟩ ⟨covers k, minimum k⟩,
      ancestorParent boundary L ⟨k, hk⟩ j hL s ∈ covers (k + j.val)

noncomputable def extendSeparatedSelectorState
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L) (hL : 0 < L)
    (n : ℕ) (S : SeparatedSelectorState boundary L ρ hL n) :
    SeparatedSelectorState boundary L ρ hL (n + 1) := by
  classical
  let targetScale := n + 1
  let K := {q : PositiveSquareScale // q.val ≤ n}
  let e : Fin n ≃ K := {
    toFun := fun i =>
      let h := Nat.succ_le_of_lt i.isLt
      ⟨⟨i.val + 1, by omega⟩, h⟩
    invFun := fun q => ⟨q.val.val - 1, by
      have hpos := q.val.property
      have hle := q.property
      omega⟩
    left_inv := by
      intro i
      apply Fin.ext
      simp
    right_inv := by
      intro q
      apply Subtype.ext
      apply Subtype.ext
      exact Nat.sub_add_cancel q.val.property
  }
  letI : Fintype K := Fintype.ofEquiv (Fin n) e
  let I := {p : K × Finset (Fin L × Fin L) //
    1 ≤ targetScale - p.1.val.val ∧
    targetScale - p.1.val.val ≤ 4 ∧
    p.2 ∈ separatedSquares boundary L ρ p.1.val
      ⟨S.covers p.1.val.val, S.minimum p.1.val.val⟩}
  letI : Fintype I := Fintype.ofFinite I
  let sourceScale : I → PositiveSquareScale := fun i => i.val.1.val
  let offset : I → ParentOffset := fun i =>
    ⟨targetScale - i.val.1.val.val, i.property.1, i.property.2.1⟩
  let source : I → Finset (Fin L × Fin L) := fun i => i.val.2
  let coverAtScale : (q : PositiveSquareScale) →
      {C : Finset (Finset (Fin L × Fin L)) //
        IsMinimumSquareCover boundary L q.val ρ C} :=
    fun q => ⟨S.covers q.val, S.minimum q.val⟩
  have htarget : ∀ i ∈ Finset.univ,
      ancestorScale (sourceScale i) (offset i) = targetScale := by
    intro i hi
    change i.val.1.val.val +
      (targetScale - i.val.1.val.val) = targetScale
    omega
  have hseparated : ∀ i ∈ Finset.univ,
      source i ∈ separatedSquares boundary L ρ (sourceScale i)
        (coverAtScale (sourceScale i)) := by
    intro i hi
    exact i.property.2.2
  have hselectedIntermediate : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      (sourceScale i).val < (sourceScale j).val →
      ∀ hOffset : (offset j).val < (offset i).val,
        ancestorParent boundary L (sourceScale i)
          (parentOffsetDiff (offset j) (offset i) hOffset) hL (source i) ∈
            (coverAtScale (sourceScale j)).val := by
    intro i hi j hj hkl hOffset
    let k := (sourceScale i).val
    let l := (sourceScale j).val
    have hk : 1 ≤ k := (sourceScale i).property
    have hklTarget : k + (offset i).val = targetScale := by
      simpa [ancestorScale] using htarget i hi
    have hljTarget : l + (offset j).val = targetScale := by
      simpa [ancestorScale] using htarget j hj
    have hdiff : (offset i).val - (offset j).val = l - k := by omega
    have hgapPos : 1 ≤ l - k := by omega
    have hgapLe : l - k ≤ 4 := by
      rw [← hdiff]
      have hjpos := (offset j).property.1
      have hipos := (offset i).property.1
      have hile := (offset i).property.2
      omega
    let gap : ParentOffset := ⟨l - k, hgapPos, hgapLe⟩
    have hgapEq : parentOffsetDiff (offset j) (offset i) hOffset = gap := by
      apply Subtype.ext
      exact hdiff
    have hsource : source i ∈ separatedSquares boundary L ρ
        ⟨k, hk⟩ ⟨S.covers k, S.minimum k⟩ := by
      exact i.property.2.2
    have hkgap : k + gap.val = l := by
      change k + (l - k) = l
      omega
    have hjFin : l ≤ n := by
      dsimp [l, sourceScale]
      omega
    have hprior := S.selected k hk gap (by omega) (source i) hsource
    have hprior' : ancestorParent boundary L ⟨k, hk⟩ gap hL (source i) ∈ S.covers l := by
      simpa only [hkgap] using hprior
    have hparentEq :
        ancestorParent boundary L (sourceScale i)
          (parentOffsetDiff (offset j) (offset i) hOffset) hL (source i) =
        ancestorParent boundary L ⟨k, hk⟩ gap hL (source i) := by
      rw [hgapEq]
    simpa [coverAtScale, l, hparentEq] using hprior'
  let newCover := Classical.choose
    (exists_minimumSquareCover_for_separated_parents_of_intermediate
      boundary L targetScale ρ Finset.univ sourceScale offset htarget coverAtScale
      source hL hseparated hselectedIntermediate ⟨S.covers targetScale, S.minimum targetScale⟩)
  have hselectedResult := Classical.choose_spec
    (exists_minimumSquareCover_for_separated_parents_of_intermediate
      boundary L targetScale ρ Finset.univ sourceScale offset htarget coverAtScale
      source hL hseparated hselectedIntermediate ⟨S.covers targetScale, S.minimum targetScale⟩)
  have hnewCover : IsMinimumSquareCover boundary L targetScale ρ newCover := by
    simpa [newCover] using hselectedResult.1
  have hnewParents := hselectedResult.2
  refine ⟨fun k => if k = targetScale then newCover else S.covers k, ?_, ?_⟩
  · intro k
    by_cases hk : k = targetScale
    · simpa [hk] using hnewCover
    · simpa [hk] using S.minimum k
  · intro k hk j htargetBound s hs
    by_cases hnewTarget : k + j.val = targetScale
    case pos hnewTarget =>
      have hindex : ∃ i : I, sourceScale i = ⟨k, hk⟩ ∧
          offset i = j ∧ source i = s := by
        refine ⟨⟨(⟨⟨k, hk⟩, ?_⟩, s), ⟨?_, ⟨?_, ?_⟩⟩⟩, ?_, ?_, rfl⟩
        · dsimp [targetScale] at hnewTarget ⊢
          have hj := j.property.1
          omega
        · change 1 ≤ targetScale - k
          dsimp [targetScale] at hnewTarget ⊢
          have hj := j.property.1
          omega
        · change targetScale - k ≤ 4
          dsimp [targetScale] at hnewTarget ⊢
          omega
        · have hsourceOld : k ≠ targetScale := by
            dsimp [targetScale] at hnewTarget ⊢
            have hj := j.property.1
            omega
          simpa [separatedSquares, hsourceOld] using hs
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          change targetScale - k = j.val
          dsimp [targetScale] at hnewTarget ⊢
          omega
      rcases hindex with ⟨i, hiscale, hioffset, hisource⟩
      have hmem := hnewParents i (Finset.mem_univ i)
      rw [hiscale, hioffset, hisource] at hmem
      simpa [newCover, hnewTarget] using hmem
    case neg hnewTarget =>
      have htargetOld : k + j.val ≤ n := by
        dsimp [targetScale] at htargetBound hnewTarget ⊢
        omega
      have hsourceOld : k ≠ targetScale := by
        dsimp [targetScale] at hnewTarget ⊢
        omega
      have hsOld : s ∈ separatedSquares boundary L ρ ⟨k, hk⟩ ⟨S.covers k, S.minimum k⟩ := by
        simpa [separatedSquares, hsourceOld] using hs
      have hparentOld := S.selected k hk j htargetOld s hsOld
      have htargetOldEq : k + j.val ≠ targetScale := by
        dsimp [targetScale] at hnewTarget ⊢
        exact hnewTarget
      simpa [hsourceOld, htargetOldEq] using hparentOld

noncomputable def initialSeparatedSelectorState
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L) (hL : 0 < L) :
    SeparatedSelectorState boundary L ρ hL 0 := by
  classical
  refine ⟨fun k => Classical.choose (exists_minimumSquareCover boundary L k ρ), ?_, ?_⟩
  · intro k
    exact Classical.choose_spec (exists_minimumSquareCover boundary L k ρ)
  · intro k hk j hbound s hs
    omega

noncomputable def separatedSelectorStates
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L) (hL : 0 < L) :
    (n : ℕ) → SeparatedSelectorState boundary L ρ hL n
  | 0 => initialSeparatedSelectorState boundary L ρ hL
  | n + 1 => extendSeparatedSelectorState boundary L ρ hL n
      (separatedSelectorStates boundary L ρ hL n)

theorem separatedSelectorState_cover_stable
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L) (hL : 0 < L)
    (m k : ℕ) (hkm : k ≤ m) :
    (separatedSelectorStates boundary L ρ hL m).covers k =
      (separatedSelectorStates boundary L ρ hL k).covers k := by
  induction m with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      rfl
  | succ m ih =>
      by_cases hkeq : k = m + 1
      · subst k
        rfl
      · have hkm' : k ≤ m := by omega
        exact (ite_eq_right hkeq).trans (ih hkm')

/-- The chosen minimum cover at every positive scale. -/
noncomputable def sharedMinimumSquareCover (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) (hL : 0 < L) (k : PositiveSquareScale) :
    {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val ρ C} := by
  let S := separatedSelectorStates boundary L ρ hL k.val
  exact ⟨S.covers k.val, S.minimum k.val⟩

/-- The one shared selector contains all four explicit parents of every
separated square, in both the free and periodic square families. -/
theorem sharedMinimumSquareCover_contains_separated_parents
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L) (hL : 0 < L)
    (k : PositiveSquareScale) (j : ParentOffset)
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ separatedSquares boundary L ρ k (sharedMinimumSquareCover boundary L ρ hL k)) :
    ancestorParent boundary L k j hL s ∈
      (sharedMinimumSquareCover boundary L ρ hL
        ⟨ancestorScale k j, by
          change 1 ≤ k.val + j.val
          omega⟩).val := by
  let T := ancestorScale k j
  let S := separatedSelectorStates boundary L ρ hL T
  have hstable : S.covers k.val =
      (separatedSelectorStates boundary L ρ hL k.val).covers k.val := by
    exact separatedSelectorState_cover_stable boundary L ρ hL T k.val (by
      dsimp [T, ancestorScale]
      omega)
  have hcoverEq :
      (⟨S.covers k.val, S.minimum k.val⟩ :
        {C : Finset (Finset (Fin L × Fin L)) //
          IsMinimumSquareCover boundary L k.val ρ C}) =
      sharedMinimumSquareCover boundary L ρ hL k := by
    apply Subtype.ext
    change S.covers k.val =
      (separatedSelectorStates boundary L ρ hL k.val).covers k.val
    exact hstable
  have hs' : s ∈ separatedSquares boundary L ρ k
      ⟨S.covers k.val, S.minimum k.val⟩ := by
    rw [hcoverEq]
    exact hs
  have hselected := S.selected k.val k.property j (by
    dsimp [T, ancestorScale]
    omega) s hs'
  change ancestorParent boundary L k j hL s ∈ S.covers (k.val + j.val)
  exact hselected

end FroehlichSpencer.BKT

end
