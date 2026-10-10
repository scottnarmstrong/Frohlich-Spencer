/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.L41Span

/-! # Free clipped-square enclosure for L4.1

The coordinate-span bounds for integer boxes are transferred to the free
finite square by clamping the target lower corner and discarding portions of
the integer boxes outside the domain. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Clamp an integer lower endpoint to the allowed statement for a clipped
length-`N` interval in a length-`L` domain. -/
def clampFreeLower (L N : ℕ) (c : ℤ) : ℤ :=
  max 0 (min c ((L - N : ℕ) : ℤ))

/-- The clamped interval contains every in-domain point of the original
length-`N` interval. -/
theorem clampFreeLower_contains (L N : ℕ) (hN : N ≤ L) (c x : ℤ)
    (hx0 : 0 ≤ x) (hxL : x < L) (hleft : c ≤ x)
    (hright : x ≤ c + (N : ℤ) - 1) :
    clampFreeLower L N c ≤ x ∧ x ≤ clampFreeLower L N c + (N : ℤ) - 1 := by
  have hu0 : 0 ≤ ((L - N : ℕ) : ℤ) := by omega
  by_cases hc0 : c ≤ 0
  · simp [clampFreeLower, min_eq_left (le_trans hc0 hu0), max_eq_left hc0]
    omega
  · have hcpos : 0 < c := by omega
    by_cases hcu : c ≤ ((L - N : ℕ) : ℤ)
    · simp [clampFreeLower, min_eq_left hcu, max_eq_right (le_of_lt hcpos)]
      omega
    · have huc : ((L - N : ℕ) : ℤ) < c := by omega
      simp [clampFreeLower, min_eq_right (le_of_lt huc)]
      have hxupper : x ≤ (L : ℤ) - 1 := by omega
      omega

/-- The origin square is all of the free domain once its side reaches `L`.
The equality case uses the clipped interval `[0,L)`. -/
theorem freeOriginSquare_eq_univ_of_side_ge (L K : ℕ) (hL : 0 < L)
    (hside : L ≤ squareSide K) :
    kpSquare .free L K (⟨0, hL⟩, ⟨0, hL⟩) = Finset.univ := by
  apply Finset.ext
  intro x
  by_cases hlarge : squareSide K > L
  · simp [kpSquare, hlarge]
  · have heq : squareSide K = L := by omega
    simp [kpSquare, heq]

private theorem freePoint_mem_liftedSquare (L k : ℕ) (a z : Fin L × Fin L)
    (hside : squareSide k ≤ L) (hz : z ∈ kpSquare .free L k a) :
    ((z.1.val : ℤ), (z.2.val : ℤ)) ∈
      liftedSquare (squareSide k) ((a.1.val : ℤ), (a.2.val : ℤ)) := by
  have hz' := hz
  simp only [kpSquare, show ¬ squareSide k > L from by omega,
    ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
  rcases hz' with ⟨hax, hxa, hay, hya⟩
  have hxaInt : (z.1.val : ℤ) < (a.1.val : ℤ) + squareSide k := by
    exact_mod_cast hxa
  have hyaInt : (z.2.val : ℤ) < (a.2.val : ℤ) + squareSide k := by
    exact_mod_cast hya
  change (a.1.val : ℤ) ≤ z.1.val ∧
    z.1.val ≤ (a.1.val : ℤ) + squareSide k - 1 ∧
    (a.2.val : ℤ) ≤ z.2.val ∧
      z.2.val ≤ (a.2.val : ℤ) + squareSide k - 1
  constructor
  · exact_mod_cast hax
  · constructor
    · omega
    · constructor
      · exact_mod_cast hay
      · omega

/-- Clamp one integer lower endpoint into the finite set of valid statement. -/
noncomputable def clampFreeFin (L N : ℕ) (hNpos : 0 < N) (hN : N < L)
    (c : ℤ) : Fin L := by
  let u := clampFreeLower L N c
  have hu0 : 0 ≤ u := le_max_left _ _
  have huUpper : u ≤ ((L - N : ℕ) : ℤ) := by
    dsimp [u, clampFreeLower]
    exact max_le (by omega) (min_le_right _ _)
  have huLt : u < L := by omega
  have huNatLt : u.toNat < L := by
    have hcast : (u.toNat : ℤ) < L := by
      rw [Int.toNat_of_nonneg hu0]
      exact huLt
    exact_mod_cast hcast
  exact ⟨u.toNat, huNatLt⟩

/-- The finite statement returned by `clampFreeFin` has the specified integer
coordinate. -/
theorem clampFreeFin_cast (L N : ℕ) (hNpos : 0 < N) (hN : N < L) (c : ℤ) :
    ((clampFreeFin L N hNpos hN c).val : ℤ) = clampFreeLower L N c := by
  unfold clampFreeFin
  dsimp
  exact Int.toNat_of_nonneg (le_max_left _ _)

/-- The common finite statement obtained by clamping a lifted target square. -/
noncomputable def clampedFreeAnchor (L K : ℕ) (hK : squareSide K < L)
    (c : LiftedPoint) : Fin L × Fin L :=
  (clampFreeFin L (squareSide K) (Nat.pow_pos (by decide)) hK c.1,
    clampFreeFin L (squareSide K) (Nat.pow_pos (by decide)) hK c.2)

/-- Every in-domain point of a lifted target square belongs to the free
clipped square based at its clamped lower corner. -/
theorem freePoint_mem_clampedSquare (L K : ℕ) (hK : squareSide K < L)
    (c : LiftedPoint) (z : Fin L × Fin L)
    (hz : ((z.1.val : ℤ), (z.2.val : ℤ)) ∈ liftedSquare (squareSide K) c) :
    z ∈ kpSquare .free L K (clampedFreeAnchor L K hK c) := by
  have hN : squareSide K ≤ L := le_of_lt hK
  have hz' : c.1 ≤ z.1.val ∧ z.1.val ≤ c.1 + (squareSide K : ℤ) - 1 ∧
      c.2 ≤ z.2.val ∧ z.2.val ≤ c.2 + (squareSide K : ℤ) - 1 := hz
  have hx := clampFreeLower_contains L (squareSide K) hN c.1 z.1.val
    (by positivity) (by exact_mod_cast z.1.isLt) hz'.1 hz'.2.1
  have hy := clampFreeLower_contains L (squareSide K) hN c.2 z.2.val
    (by positivity) (by exact_mod_cast z.2.isLt) hz'.2.2.1 hz'.2.2.2
  have hxc : (clampedFreeAnchor L K hK c).1.val ≤ z.1.val := by
    have hcast : ((clampedFreeAnchor L K hK c).1.val : ℤ) ≤ z.1.val := by
      change ((clampFreeFin L (squareSide K) (Nat.pow_pos (by decide)) hK c.1).val : ℤ) ≤ z.1.val
      rw [clampFreeFin_cast L (squareSide K) (Nat.pow_pos (by decide)) hK c.1]
      exact hx.1
    exact_mod_cast hcast
  have hyc : (clampedFreeAnchor L K hK c).2.val ≤ z.2.val := by
    have hcast : ((clampedFreeAnchor L K hK c).2.val : ℤ) ≤ z.2.val := by
      change ((clampFreeFin L (squareSide K) (Nat.pow_pos (by decide)) hK c.2).val : ℤ) ≤ z.2.val
      rw [clampFreeFin_cast L (squareSide K) (Nat.pow_pos (by decide)) hK c.2]
      exact hy.1
    exact_mod_cast hcast
  have hxt : z.1.val < (clampedFreeAnchor L K hK c).1.val + squareSide K := by
    have hcast : (z.1.val : ℤ) <
        ((clampedFreeAnchor L K hK c).1.val : ℤ) + squareSide K := by
      change (z.1.val : ℤ) <
        ((clampFreeFin L (squareSide K) (Nat.pow_pos (by decide)) hK c.1).val : ℤ) + squareSide K
      rw [clampFreeFin_cast L (squareSide K) (Nat.pow_pos (by decide)) hK c.1]
      omega
    exact_mod_cast hcast
  have hyt : z.2.val < (clampedFreeAnchor L K hK c).2.val + squareSide K := by
    have hcast : (z.2.val : ℤ) <
        ((clampedFreeAnchor L K hK c).2.val : ℤ) + squareSide K := by
      change (z.2.val : ℤ) <
        ((clampFreeFin L (squareSide K) (Nat.pow_pos (by decide)) hK c.2).val : ℤ) + squareSide K
      rw [clampFreeFin_cast L (squareSide K) (Nat.pow_pos (by decide)) hK c.2]
      omega
    exact_mod_cast hcast
  simp only [kpSquare, show ¬ squareSide K > L from by omega,
    ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hxc, hxt, hyc, hyt⟩

/-- Two free clipped squares linked by a pair of coordinate witnesses fit in
one allowed target square under the pair span budget. -/
theorem freePairSquares_fit (L k K d : ℕ) (hL : 0 < L) (hkK : k < K)
    (a b x y : Fin L × Fin L)
    (hx : x ∈ kpSquare .free L k a) (hy : y ∈ kpSquare .free L k b)
    (hdx₁ : -((d : ℤ)) ≤ (x.1.val : ℤ) - y.1.val)
    (hdx₂ : (x.1.val : ℤ) - y.1.val ≤ d)
    (hdy₁ : -((d : ℤ)) ≤ (x.2.val : ℤ) - y.2.val)
    (hdy₂ : (x.2.val : ℤ) - y.2.val ≤ d)
    (hbudget : (d : ℤ) + 2 * ((squareSide k : ℤ) - 1) < squareSide K) :
    ∃ c : Fin L × Fin L,
      kpSquare .free L k a ∪ kpSquare .free L k b ⊆ kpSquare .free L K c := by
  classical
  by_cases htarget : L ≤ squareSide K
  · refine ⟨(⟨0, hL⟩, ⟨0, hL⟩), ?_⟩
    rw [freeOriginSquare_eq_univ_of_side_ge L K hL htarget]
    exact Finset.union_subset_iff.mpr ⟨Finset.subset_univ _, Finset.subset_univ _⟩
  · have htarget' : squareSide K < L := by omega
    have hmono : squareSide k ≤ squareSide K := by
      exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hkK)
    have hsource : squareSide k < L := by omega
    let aa : LiftedPoint := ((a.1.val : ℤ), (a.2.val : ℤ))
    let bb : LiftedPoint := ((b.1.val : ℤ), (b.2.val : ℤ))
    let p : LiftedPoint := ((x.1.val : ℤ), (x.2.val : ℤ))
    let q : LiftedPoint := ((y.1.val : ℤ), (y.2.val : ℤ))
    have hp : p ∈ liftedSquare (squareSide k) aa := by
      simpa [p, aa] using freePoint_mem_liftedSquare L k a x (le_of_lt hsource) hx
    have hq : q ∈ liftedSquare (squareSide k) bb := by
      simpa [q, bb] using freePoint_mem_liftedSquare L k b y (le_of_lt hsource) hy
    obtain ⟨c0, hfit⟩ := pair_liftedSquares_fit (squareSide k) (squareSide K) d
      aa bb p q hp hq hdx₁ hdx₂ hdy₁ hdy₂ hbudget
    let c := clampedFreeAnchor L K htarget' c0
    refine ⟨c, ?_⟩
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have hzLift := freePoint_mem_liftedSquare L k a z (le_of_lt hsource) hz
      exact freePoint_mem_clampedSquare L K htarget' c0 z (hfit (Or.inl hzLift))
    · have hzLift := freePoint_mem_liftedSquare L k b z (le_of_lt hsource) hz
      exact freePoint_mem_clampedSquare L K htarget' c0 z (hfit (Or.inr hzLift))

/-- Three free clipped squares along a linked path fit in one allowed target
square under the three-box span budget. -/
theorem freeTripleSquares_fit (L k K d₁ d₂ : ℕ) (hL : 0 < L) (hkK : k < K)
    (a b c x y z : Fin L × Fin L)
    (hx : x ∈ kpSquare .free L k a) (hy : y ∈ kpSquare .free L k b)
    (hz : z ∈ kpSquare .free L k c)
    (hd₁x₁ : -((d₁ : ℤ)) ≤ (x.1.val : ℤ) - y.1.val)
    (hd₁x₂ : (x.1.val : ℤ) - y.1.val ≤ d₁)
    (hd₁y₁ : -((d₁ : ℤ)) ≤ (x.2.val : ℤ) - y.2.val)
    (hd₁y₂ : (x.2.val : ℤ) - y.2.val ≤ d₁)
    (hd₂x₁ : -((d₂ : ℤ)) ≤ (y.1.val : ℤ) - z.1.val)
    (hd₂x₂ : (y.1.val : ℤ) - z.1.val ≤ d₂)
    (hd₂y₁ : -((d₂ : ℤ)) ≤ (y.2.val : ℤ) - z.2.val)
    (hd₂y₂ : (y.2.val : ℤ) - z.2.val ≤ d₂)
    (hbudget : (d₁ : ℤ) + d₂ + 3 * ((squareSide k : ℤ) - 1) < squareSide K) :
    ∃ t : Fin L × Fin L,
      kpSquare .free L k a ∪ kpSquare .free L k b ∪ kpSquare .free L k c ⊆
        kpSquare .free L K t := by
  classical
  by_cases htarget : L ≤ squareSide K
  · refine ⟨(⟨0, hL⟩, ⟨0, hL⟩), ?_⟩
    rw [freeOriginSquare_eq_univ_of_side_ge L K hL htarget]
    exact Finset.union_subset_iff.mpr ⟨Finset.subset_univ _, Finset.subset_univ _⟩
  · have htarget' : squareSide K < L := by omega
    have hmono : squareSide k ≤ squareSide K := by
      exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hkK)
    have hsource : squareSide k < L := by omega
    let aa : LiftedPoint := ((a.1.val : ℤ), (a.2.val : ℤ))
    let bb : LiftedPoint := ((b.1.val : ℤ), (b.2.val : ℤ))
    let cc : LiftedPoint := ((c.1.val : ℤ), (c.2.val : ℤ))
    let p : LiftedPoint := ((x.1.val : ℤ), (x.2.val : ℤ))
    let q : LiftedPoint := ((y.1.val : ℤ), (y.2.val : ℤ))
    let r : LiftedPoint := ((z.1.val : ℤ), (z.2.val : ℤ))
    have hp : p ∈ liftedSquare (squareSide k) aa := by
      simpa [p, aa] using freePoint_mem_liftedSquare L k a x (le_of_lt hsource) hx
    have hq : q ∈ liftedSquare (squareSide k) bb := by
      simpa [q, bb] using freePoint_mem_liftedSquare L k b y (le_of_lt hsource) hy
    have hr : r ∈ liftedSquare (squareSide k) cc := by
      simpa [r, cc] using freePoint_mem_liftedSquare L k c z (le_of_lt hsource) hz
    obtain ⟨t0, hfit⟩ := triple_liftedSquares_fit
      (squareSide k) (squareSide K) d₁ d₂ aa bb cc p q r hp hq hr
      hd₁x₁ hd₁x₂ hd₂x₁ hd₂x₂ hd₁y₁ hd₁y₂ hd₂y₁ hd₂y₂ hbudget
    let t := clampedFreeAnchor L K htarget' t0
    refine ⟨t, ?_⟩
    intro w hw
    rcases Finset.mem_union.mp hw with hwAB | hwC
    · rcases Finset.mem_union.mp hwAB with hwA | hwB
      · have hwLift := freePoint_mem_liftedSquare L k a w (le_of_lt hsource) hwA
        exact freePoint_mem_clampedSquare L K htarget' t0 w (hfit (Or.inl (Or.inl hwLift)))
      · have hwLift := freePoint_mem_liftedSquare L k b w (le_of_lt hsource) hwB
        exact freePoint_mem_clampedSquare L K htarget' t0 w (hfit (Or.inl (Or.inr hwLift)))
    · have hwLift := freePoint_mem_liftedSquare L k c w (le_of_lt hsource) hwC
      exact freePoint_mem_clampedSquare L K htarget' t0 w (hfit (Or.inr hwLift))

end FroehlichSpencer.BKT

end
