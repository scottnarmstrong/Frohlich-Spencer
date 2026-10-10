/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.Geometry
public import FroehlichSpencer.BKT.Charges.TorusDistance
import FroehlichSpencer.BKT.Charges.L41Span
import FroehlichSpencer.BKT.Charges.SquareDiameterBounds

/-! # Packing points in the free and periodic squares

Points of the free or periodic square within graph distance `R` of a base point and pairwise at
graph distance at least `2m` number at most `(2R/m + 1)²`. The proof embeds the square into `ℤ²`
by offsets from the base point whose `ℓ¹` distance dominates the graph distance, and then counts
the `m`-boxes of the offsets. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Offsets from `y₀` in `ℤ²`, bounded by the distance to `y₀`, with `ℓ¹` distance dominating
the graph distance. -/
theorem exists_latticeOffset (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (y₀ : Fin L × Fin L) :
    ∃ off : Fin L × Fin L → ℤ × ℤ,
      (∀ p, |(off p).1| ≤ (latticeDistance boundary L p y₀ : ℤ) ∧
        |(off p).2| ≤ (latticeDistance boundary L p y₀ : ℤ)) ∧
      ∀ p q, (latticeDistance boundary L p q : ℤ) ≤
        |(off p).1 - (off q).1| + |(off p).2 - (off q).2| := by
  cases boundary with
  | free =>
    refine ⟨fun p => ((y₀.1.val : ℤ) - p.1.val, (y₀.2.val : ℤ) - p.2.val), ?_, ?_⟩
    · intro p
      obtain ⟨h1, h2, h3, h4⟩ := freeDistance_coordinate_bound L hL p y₀
      exact ⟨abs_le.2 ⟨by linarith, h2⟩, abs_le.2 ⟨by linarith, h4⟩⟩
    · intro p q
      have h := freeDistance_le_coordinateSum L p q
      rcases abs_cases ((y₀.1.val : ℤ) - p.1.val - ((y₀.1.val : ℤ) - q.1.val)) with ⟨a, _⟩ | ⟨a, _⟩ <;>
      rcases abs_cases ((y₀.2.val : ℤ) - p.2.val - ((y₀.2.val : ℤ) - q.2.val)) with ⟨b, _⟩ | ⟨b, _⟩ <;>
      · rw [a, b]
        split_ifs at h <;> omega
  | periodic =>
    have hL0 : 0 < L := by omega
    choose t1 ht1 ht1' using fun p : Fin L × Fin L => exists_abs_eq_cyclicDist L hL0 p.1 y₀.1
    choose t2 ht2 ht2' using fun p : Fin L × Fin L => exists_abs_eq_cyclicDist L hL0 p.2 y₀.2
    refine ⟨fun p => (t1 p, t2 p), ?_, ?_⟩
    · intro p
      have e : latticeDistance .periodic L p y₀ = cyclicDist L p.1 y₀.1 + cyclicDist L p.2 y₀.2 :=
        squarePeriodic_dist_eq_cyclicDist L p y₀
      simp only [e]
      push_cast
      rw [ht1', ht2']
      constructor <;> omega
    · intro p q
      have e : latticeDistance .periodic L p q = cyclicDist L p.1 q.1 + cyclicDist L p.2 q.2 :=
        squarePeriodic_dist_eq_cyclicDist L p q
      have h1 := cyclicDist_le_abs L hL0 p.1 q.1 (t1 p - t1 q)
        (by
          have := (ht1 p).sub (ht1 q)
          have h' : ((y₀.1.val : ℤ) - p.1.val) - ((y₀.1.val : ℤ) - q.1.val) =
              (q.1.val : ℤ) - p.1.val := by ring
          rwa [h'] at this)
      have h2 := cyclicDist_le_abs L hL0 p.2 q.2 (t2 p - t2 q)
        (by
          have := (ht2 p).sub (ht2 q)
          have h' : ((y₀.2.val : ℤ) - p.2.val) - ((y₀.2.val : ℤ) - q.2.val) =
              (q.2.val : ℤ) - p.2.val := by ring
          rwa [h'] at this)
      simp only [e]
      push_cast
      linarith

/-- Points of the free or periodic square that lie within graph distance `R` of `y₀` and are
pairwise at graph distance at least `2m` number at most `(2R/m + 1)²`. -/
theorem card_le_of_pairwise_latticeDistance_ge (boundary : SquareBoundary) {L : ℕ}
    (hL : 1 < L) (y₀ : Fin L × Fin L) (R m : ℕ) (hm : 1 ≤ m) (P : Finset (Fin L × Fin L))
    (hP : ∀ p ∈ P, latticeDistance boundary L p y₀ ≤ R)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * m ≤ latticeDistance boundary L p q) :
    P.card ≤ (2 * R / m + 1) ^ 2 := by
  obtain ⟨off, hoff, hdist⟩ := exists_latticeOffset boundary hL y₀
  let f : Fin L × Fin L → ℕ × ℕ := fun p =>
    (((off p).1 + R).toNat / m, ((off p).2 + R).toNat / m)
  have hmaps : ∀ p ∈ P, f p ∈ Finset.range (2 * R / m + 1) ×ˢ Finset.range (2 * R / m + 1) := by
    intro p hp
    have h := hoff p
    have hR : (latticeDistance boundary L p y₀ : ℤ) ≤ R := by exact_mod_cast hP p hp
    have a1 := (abs_le.1 h.1)
    have a2 := (abs_le.1 h.2)
    simp only [f, Finset.mem_product, Finset.mem_range]
    constructor
    · have : ((off p).1 + R).toNat ≤ 2 * R := by omega
      exact Nat.lt_succ_of_le (le_trans (Nat.div_le_div_right this) le_rfl)
    · have : ((off p).2 + R).toNat ≤ 2 * R := by omega
      exact Nat.lt_succ_of_le (le_trans (Nat.div_le_div_right this) le_rfl)
  have hinj : Set.InjOn f P := by
    intro p hp q hq hpq
    by_contra hne
    have hs := hsep p hp q hq hne
    have hd := hdist p q
    have hp' := hoff p
    have hq' := hoff q
    have hRp : (latticeDistance boundary L p y₀ : ℤ) ≤ R := by exact_mod_cast hP p hp
    have hRq : (latticeDistance boundary L q y₀ : ℤ) ≤ R := by exact_mod_cast hP q hq
    have a1 := abs_le.1 hp'.1
    have a2 := abs_le.1 hp'.2
    have b1 := abs_le.1 hq'.1
    have b2 := abs_le.1 hq'.2
    simp only [f, Prod.mk.injEq] at hpq
    obtain ⟨e1, e2⟩ := hpq
    have d1 := Nat.div_add_mod ((off p).1 + R).toNat m
    have d2 := Nat.div_add_mod ((off q).1 + R).toNat m
    have d3 := Nat.div_add_mod ((off p).2 + R).toNat m
    have d4 := Nat.div_add_mod ((off q).2 + R).toNat m
    have m1 := Nat.mod_lt ((off p).1 + R).toNat (show 0 < m by omega)
    have m2 := Nat.mod_lt ((off q).1 + R).toNat (show 0 < m by omega)
    have m3 := Nat.mod_lt ((off p).2 + R).toNat (show 0 < m by omega)
    have m4 := Nat.mod_lt ((off q).2 + R).toNat (show 0 < m by omega)
    rw [e1] at d1
    rw [e2] at d3
    have c1 : |(off p).1 - (off q).1| < m := by
      rw [abs_lt]; constructor <;> omega
    have c2 : |(off p).2 - (off q).2| < m := by
      rw [abs_lt]; constructor <;> omega
    omega
  calc P.card ≤ (Finset.range (2 * R / m + 1) ×ˢ Finset.range (2 * R / m + 1)).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ = (2 * R / m + 1) ^ 2 := by simp [sq]

end FroehlichSpencer.BKT

end
