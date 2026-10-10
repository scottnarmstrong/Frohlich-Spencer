/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.L41FreeFit

/-! # Pair and triple enclosures on both square carriers

The free case uses clipped integer coordinate intervals. The periodic case
uses the coordinate-lift and span enclosure from `L41Span`. Once the target
side reaches the period or free side length, the origin square is all of Λ.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- At and above the domain side length, the origin square is all of the
free or periodic domain (with the equality case included). -/
theorem kpOriginSquare_eq_univ_of_side_ge (boundary : SquareBoundary) (L K : ℕ)
    (hL : 1 < L) (hside : L ≤ squareSide K) :
    kpSquare boundary L K (⟨0, by omega⟩, ⟨0, by omega⟩) = Finset.univ := by
  cases boundary with
  | free =>
      simpa using freeOriginSquare_eq_univ_of_side_ge L K (by omega) hside
  | periodic =>
      simp [kpSquare, hside]

/-- A linked pair of scale-`k` squares fits in one allowed scale-`K` square
on either carrier. The metric distance supplies the pair span budget. -/
theorem pairCarrierSquares_fit (boundary : SquareBoundary) (L k K : ℕ)
    (hL : 1 < L) (hkK : k < K)
    (a b x y : Fin L × Fin L)
    (hx : x ∈ kpSquare boundary L k a) (hy : y ∈ kpSquare boundary L k b)
    (hbudget : latticeDistance boundary L x y +
      2 * (squareSide k - 1) < squareSide K) :
    ∃ c : Fin L × Fin L,
      kpSquare boundary L k a ∪ kpSquare boundary L k b ⊆ kpSquare boundary L K c := by
  classical
  by_cases htarget : L ≤ squareSide K
  · refine ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), ?_⟩
    rw [kpOriginSquare_eq_univ_of_side_ge boundary L K hL htarget]
    exact Finset.union_subset_iff.mpr ⟨Finset.subset_univ _, Finset.subset_univ _⟩
  · have htarget' : squareSide K < L := by omega
    have hsource : squareSide k < L := by
      have hmono : squareSide k ≤ squareSide K := by
        exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hkK)
      omega
    have hbudgetZ : (latticeDistance boundary L x y : ℤ) +
        2 * ((squareSide k : ℤ) - 1) < squareSide K := by
      have hbudgetCast : (latticeDistance boundary L x y : ℤ) +
          2 * ((squareSide k - 1 : ℕ) : ℤ) < squareSide K := by
        exact_mod_cast hbudget
      have hsub : ((squareSide k - 1 : ℕ) : ℤ) = (squareSide k : ℤ) - 1 := by
        have hpos : 1 ≤ squareSide k := Nat.one_le_pow k 2 (by decide)
        omega
      rw [hsub] at hbudgetCast
      exact hbudgetCast
    cases boundary with
    | free =>
        have hdist := freeDistance_coordinate_bound L (by omega) x y
        obtain ⟨t, hfit⟩ := freePairSquares_fit L k K
          (latticeDistance .free L x y) (by omega) hkK a b x y hx hy
          (by omega) (by omega) (by omega) (by omega) hbudgetZ
        exact ⟨t, hfit⟩
    | periodic =>
        obtain ⟨c, hc⟩ := periodicPairSquares_fit L k K (by omega) hsource htarget'
          a b x y hx hy hbudgetZ
        exact ⟨periodicProjection L (by omega) c, hc⟩

/-- A linked three-square path fits in one allowed scale-`K` square on either
carrier. The two metric links supply the coordinate span budget. -/
theorem tripleCarrierSquares_fit (boundary : SquareBoundary) (L k K : ℕ)
    (hL : 1 < L) (hkK : k < K)
    (a b c x y z : Fin L × Fin L)
    (hx : x ∈ kpSquare boundary L k a)
    (hy : y ∈ kpSquare boundary L k b)
    (hz : z ∈ kpSquare boundary L k c)
    (hbudget : latticeDistance boundary L x y + latticeDistance boundary L y z +
      3 * (squareSide k - 1) < squareSide K) :
    ∃ t : Fin L × Fin L,
      kpSquare boundary L k a ∪ kpSquare boundary L k b ∪ kpSquare boundary L k c ⊆
        kpSquare boundary L K t := by
  classical
  by_cases htarget : L ≤ squareSide K
  · refine ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), ?_⟩
    rw [kpOriginSquare_eq_univ_of_side_ge boundary L K hL htarget]
    exact Finset.union_subset_iff.mpr ⟨Finset.union_subset_iff.mpr
      ⟨Finset.subset_univ _, Finset.subset_univ _⟩, Finset.subset_univ _⟩
  · have htarget' : squareSide K < L := by omega
    have hsource : squareSide k < L := by
      have hmono : squareSide k ≤ squareSide K := by
        exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hkK)
      omega
    have hbudgetZ : (latticeDistance boundary L x y : ℤ) +
        (latticeDistance boundary L y z : ℤ) +
        3 * ((squareSide k : ℤ) - 1) < squareSide K := by
      have hbudgetCast : ((latticeDistance boundary L x y +
          latticeDistance boundary L y z : ℕ) : ℤ) +
          3 * ((squareSide k - 1 : ℕ) : ℤ) < squareSide K := by
        exact_mod_cast hbudget
      have hsub : ((squareSide k - 1 : ℕ) : ℤ) = (squareSide k : ℤ) - 1 := by
        have hpos : 1 ≤ squareSide k := Nat.one_le_pow k 2 (by decide)
        omega
      rw [Nat.cast_add] at hbudgetCast
      rw [hsub] at hbudgetCast
      exact hbudgetCast
    cases boundary with
    | free =>
        have hd₁ := freeDistance_coordinate_bound L (by omega) x y
        have hd₂ := freeDistance_coordinate_bound L (by omega) y z
        obtain ⟨t, hfit⟩ := freeTripleSquares_fit L k K
          (latticeDistance .free L x y) (latticeDistance .free L y z)
          (by omega) hkK a b c x y z hx hy hz
          (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) hbudgetZ
        exact ⟨t, hfit⟩
    | periodic =>
        obtain ⟨t, ht⟩ := periodicTripleSquares_fit L k K (by omega) hsource htarget'
          a b c x y z hx hy hz hbudgetZ
        exact ⟨periodicProjection L (by omega) t, ht⟩

end FroehlichSpencer.BKT

end
