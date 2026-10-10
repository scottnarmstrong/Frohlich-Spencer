/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.Covers

/-! # Monotonicity of finite square covers

Each scale-`k` square is contained in the scale-`k+1` square with the same
statement. This gives monotonicity of the minimum cover number in KP §2.1. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Choose an statement representing a square in the scale-`k` family. The value
outside that family is irrelevant to the cover enlargement construction. -/
noncomputable def squareAnchor (boundary : SquareBoundary) (L k : ℕ)
    (hL : 0 < L) (s : Finset (Fin L × Fin L)) : Fin L × Fin L := by
  classical
  exact if hs : s ∈ kpSquares boundary L k then
    Classical.choose (Finset.mem_image.mp hs)
  else (⟨0, hL⟩, ⟨0, hL⟩)

/-- A square's chosen statement represents that square. -/
theorem kpSquare_eq_of_squareAnchor (boundary : SquareBoundary) (L k : ℕ)
    (hL : 0 < L) (s : Finset (Fin L × Fin L)) (hs : s ∈ kpSquares boundary L k) :
    kpSquare boundary L k (squareAnchor boundary L k hL s) = s := by
  classical
  unfold squareAnchor
  rw [dite_eq_left hs]
  exact (Classical.choose_spec (Finset.mem_image.mp hs)).2

/-- The chosen scale-`k+1` parent contains its scale-`k` square. -/
theorem kpSquare_subset_chosenParent (boundary : SquareBoundary) (L k : ℕ)
    (hL : 0 < L) (s : Finset (Fin L × Fin L)) (hs : s ∈ kpSquares boundary L k) :
    s ⊆ kpSquare boundary L (k + 1) (squareAnchor boundary L k hL s) := by
  calc
    s = kpSquare boundary L k (squareAnchor boundary L k hL s) :=
      (kpSquare_eq_of_squareAnchor boundary L k hL s hs).symm
    _ ⊆ kpSquare boundary L (k + 1) (squareAnchor boundary L k hL s) :=
      kpSquare_subset_succ boundary L k (squareAnchor boundary L k hL s)

/-- Enlarge every square in a cover to the next scale using the chosen
same-statement parent. -/
noncomputable def enlargeSquareCover (boundary : SquareBoundary) (L k : ℕ)
    (hL : 0 < L) (C : Finset (Finset (Fin L × Fin L))) :
    Finset (Finset (Fin L × Fin L)) := by
  classical
  exact C.image fun s => kpSquare boundary L (k + 1) (squareAnchor boundary L k hL s)

/-- The enlarged family is a cover at the next scale. -/
theorem enlargeSquareCover_isSquareCover (boundary : SquareBoundary) (L k : ℕ)
    (hL : 0 < L) (ρ : ChargeDensity L) (C : Finset (Finset (Fin L × Fin L)))
    (hC : IsSquareCover boundary L k ρ C) :
    IsSquareCover boundary L (k + 1) ρ (enlargeSquareCover boundary L k hL C) := by
  classical
  refine ⟨?_, ?_⟩
  · change (C.image fun s =>
        kpSquare boundary L (k + 1) (squareAnchor boundary L k hL s)) ⊆
      kpSquares boundary L (k + 1)
    rw [Finset.image_subset_iff]
    intro s hs
    exact Finset.mem_image.mpr
      ⟨squareAnchor boundary L k hL s, Finset.mem_univ _, rfl⟩
  · intro x hx
    rcases hC.2 x hx with ⟨s, hsC, hxs⟩
    refine ⟨kpSquare boundary L (k + 1) (squareAnchor boundary L k hL s), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨s, hsC, rfl⟩
    · exact (kpSquare_subset_chosenParent boundary L k hL s (hC.1 hsC)) hxs

/-- Passing to the next dyadic scale cannot increase the minimum number of
squares in a support cover. -/
theorem squareCoverNumber_succ_le (boundary : SquareBoundary) (L k : ℕ)
    (hL : 0 < L) (ρ : ChargeDensity L) :
    squareCoverNumber boundary L (k + 1) ρ ≤ squareCoverNumber boundary L k ρ := by
  rcases exists_squareCover_attaining_number boundary L k ρ with ⟨C, hC, hcard⟩
  calc
    squareCoverNumber boundary L (k + 1) ρ ≤
        (enlargeSquareCover boundary L k hL C).card :=
      squareCoverNumber_le boundary L (k + 1) ρ _
        (enlargeSquareCover_isSquareCover boundary L k hL ρ C hC)
    _ ≤ C.card := Finset.card_image_le
    _ = squareCoverNumber boundary L k ρ := hcard

end FroehlichSpencer.BKT

end
