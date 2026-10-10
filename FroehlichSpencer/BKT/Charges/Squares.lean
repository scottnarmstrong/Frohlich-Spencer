/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finset.Basic
public import FroehlichSpencer.BKT.Surface.SquareFree
public import FroehlichSpencer.BKT.Surface.SquarePeriodic

/-!
# Dyadic squares on the finite BKT domains

The vertices use the free and periodic carriers `Fin L × Fin L`.

The definition `kpSquare` uses the following convention: free boxes
are clipped through side `L` and become all of `Λ` above side `L`; periodic
boxes are quotient images below side `L` and become all of `Λ` at side `L`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The boundary convention used to interpret the squares in KP §2.1. -/
inductive SquareBoundary where
  | free
  | periodic
  deriving DecidableEq

/-- The side length of a scale-`k` square. -/
def squareSide (k : ℕ) : ℕ := 2 ^ k

/-- The scale-`k` square with statement `a` in the adopted free or periodic
convention. A free box is clipped at the upper boundary. A periodic box is
the quotient image of a box based at `a`. -/
def kpSquare (boundary : SquareBoundary) (L k : ℕ)
    (a : Fin L × Fin L) : Finset (Fin L × Fin L) :=
  match boundary with
  | .free =>
      if squareSide k > L then Finset.univ else
        Finset.univ.filter fun x =>
          a.1.val ≤ x.1.val ∧ x.1.val < a.1.val + squareSide k ∧
          a.2.val ≤ x.2.val ∧ x.2.val < a.2.val + squareSide k
  | .periodic =>
      if squareSide k ≥ L then Finset.univ else
        Finset.univ.filter fun x =>
          ∃ i ∈ Finset.range (squareSide k), ∃ j ∈ Finset.range (squareSide k),
            x.1.val = (a.1.val + i) % L ∧ x.2.val = (a.2.val + j) % L

/-- The family of all scale-`k` squares, with statement in the domain. -/
def kpSquares (boundary : SquareBoundary) (L k : ℕ) : Finset (Finset (Fin L × Fin L)) :=
  Finset.univ.image (kpSquare boundary L k)

/-- The statement belongs to its square at every scale. -/
theorem anchor_mem_kpSquare (boundary : SquareBoundary) (L k : ℕ)
    (a : Fin L × Fin L) : a ∈ kpSquare boundary L k a := by
  cases boundary with
  | free =>
      by_cases h : squareSide k > L
      · simp [kpSquare, h]
      · have hside : 0 < squareSide k := by
          exact Nat.pow_pos (by decide)
        simp only [kpSquare, h, ↓reduceIte, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨le_rfl, by omega, le_rfl, by omega⟩
  | periodic =>
      by_cases h : squareSide k ≥ L
      · simp [kpSquare, h]
      · have hside : 0 < squareSide k := Nat.pow_pos (by decide)
        simp only [kpSquare, h, ↓reduceIte, Finset.mem_filter, Finset.mem_univ,
          true_and]
        refine ⟨0, Finset.mem_range.mpr hside, 0, Finset.mem_range.mpr hside, ?_⟩
        constructor <;> simp [Nat.mod_eq_of_lt a.1.isLt, Nat.mod_eq_of_lt a.2.isLt]

/-- Every vertex belongs to some square at every scale. -/
theorem mem_kpSquares (boundary : SquareBoundary) (L k : ℕ)
    (x : Fin L × Fin L) : ∃ s ∈ kpSquares boundary L k, x ∈ s := by
  refine ⟨kpSquare boundary L k x, ?_, anchor_mem_kpSquare boundary L k x⟩
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

/-- A square at one scale is contained in the square with the same statement at
the next scale. -/
theorem kpSquare_subset_succ (boundary : SquareBoundary) (L k : ℕ)
    (a : Fin L × Fin L) : kpSquare boundary L k a ⊆ kpSquare boundary L (k + 1) a := by
  have hside : squareSide k ≤ squareSide (k + 1) := by
    have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
    simp only [squareSide, pow_succ]
    omega
  cases boundary with
  | free =>
      intro x hx
      by_cases h : squareSide k > L
      · have h' : squareSide (k + 1) > L := by omega
        simp [kpSquare, h']
      · by_cases h' : squareSide (k + 1) > L
        · simp [kpSquare, h']
        · have hx' : a.1.val ≤ x.1.val ∧ x.1.val < a.1.val + squareSide k ∧
              a.2.val ≤ x.2.val ∧ x.2.val < a.2.val + squareSide k := by
            simpa [kpSquare, h] using hx
          simp only [kpSquare, h', ↓reduceIte, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨hx'.1, lt_of_lt_of_le hx'.2.1 (Nat.add_le_add_left hside _),
            hx'.2.2.1, lt_of_lt_of_le hx'.2.2.2 (Nat.add_le_add_left hside _)⟩
  | periodic =>
      intro x hx
      by_cases h : squareSide k ≥ L
      · have h' : squareSide (k + 1) ≥ L := by omega
        simp [kpSquare, h']
      · by_cases h' : squareSide (k + 1) ≥ L
        · simp [kpSquare, h']
        · have hx' : ∃ i ∈ Finset.range (squareSide k),
              ∃ j ∈ Finset.range (squareSide k),
              x.1.val = (a.1.val + i) % L ∧ x.2.val = (a.2.val + j) % L := by
            simpa [kpSquare, h] using hx
          rcases hx' with ⟨i, hi, j, hj, hxy⟩
          have hi' : i ∈ Finset.range (squareSide (k + 1)) :=
            Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hside)
          have hj' : j ∈ Finset.range (squareSide (k + 1)) :=
            Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hside)
          simp only [kpSquare, h', ↓reduceIte, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨i, hi', j, hj', hxy⟩

/-- The families of allowed dyadic squares are nested from scale `k` to
scale `k+1`. -/
theorem kpSquares_nested (boundary : SquareBoundary) (L k : ℕ)
    (s : Finset (Fin L × Fin L)) (hs : s ∈ kpSquares boundary L k) :
    ∃ t ∈ kpSquares boundary L (k + 1), s ⊆ t := by
  rcases Finset.mem_image.mp hs with ⟨a, -, rfl⟩
  exact ⟨kpSquare boundary L (k + 1) a,
    Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩,
    kpSquare_subset_succ boundary L k a⟩

end FroehlichSpencer.BKT

end
