/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.Covers

/-!
# Scale-zero covers and the singleton-square bound

KP §2.1, p. 8 (Kharash–Peled, first version) notes that
`|𝒮₀(ϱ)| = |supp ϱ|`: a `1 × 1` square is a single vertex.

Both facts hold for the free and the periodic
square families, including the overflow convention `kpSquare = univ` above side `L`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- A scale-zero square has at most one vertex. -/
theorem kpSquare_zero_card_le_one (boundary : SquareBoundary) (L : ℕ)
    (a : Fin L × Fin L) : (kpSquare boundary L 0 a).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  cases boundary with
  | free =>
      by_cases h : squareSide 0 > L
      · have hL : L = 0 := by
          simp only [squareSide, pow_zero] at h
          omega
        subst hL
        exact x.1.elim0
      · simp only [squareSide, pow_zero] at h
        simp only [kpSquare, squareSide, pow_zero, h, ↓reduceIte, Finset.mem_filter,
          Finset.mem_univ, true_and] at hx hy
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  | periodic =>
      by_cases h : squareSide 0 ≥ L
      · have hL : L ≤ 1 := by
          simpa only [squareSide, pow_zero] using h
        have hsub : Subsingleton (Fin L) := Fin.subsingleton_iff_le_one.mpr hL
        exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      · simp only [squareSide, pow_zero] at h
        simp only [kpSquare, squareSide, pow_zero, h, ↓reduceIte, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.range_one, Finset.mem_singleton, exists_eq_left,
          add_zero, Nat.mod_eq_of_lt a.1.isLt, Nat.mod_eq_of_lt a.2.isLt] at hx hy
        exact Prod.ext (Fin.ext (hx.1.trans hy.1.symm)) (Fin.ext (hx.2.trans hy.2.symm))

/-- Every allowed scale-zero square has at most one vertex. -/
theorem card_le_one_of_mem_kpSquares_zero (boundary : SquareBoundary) (L : ℕ)
    {s : Finset (Fin L × Fin L)} (hs : s ∈ kpSquares boundary L 0) : s.card ≤ 1 := by
  rcases Finset.mem_image.mp hs with ⟨a, -, rfl⟩
  exact kpSquare_zero_card_le_one boundary L a

/-- The squares anchored at the support points form a scale-`k` cover. -/
theorem isSquareCover_anchoredSquares (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) :
    IsSquareCover boundary L k ρ ((chargeSupport ρ).image (kpSquare boundary L k)) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨a, -, rfl⟩
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  · intro x hx
    exact ⟨kpSquare boundary L k x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      anchor_mem_kpSquare boundary L k x⟩

/-- : at every scale the minimum cover number is at most the support size. -/
theorem squareCoverNumber_le_card_chargeSupport (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) : squareCoverNumber boundary L k ρ ≤ (chargeSupport ρ).card :=
  (squareCoverNumber_le boundary L k ρ _ (isSquareCover_anchoredSquares boundary L k ρ)).trans
    Finset.card_image_le

/-- A scale-zero cover has at least as many squares as the support has points. -/
theorem card_chargeSupport_le_card_of_isSquareCover_zero (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Fin L × Fin L)))
    (hC : IsSquareCover boundary L 0 ρ C) : (chargeSupport ρ).card ≤ C.card := by
  classical
  choose! f hfC hxf using hC.2
  refine Finset.card_le_card_of_injOn f (fun x hx => hfC x hx) ?_
  intro x hx y hy hxy
  have hcard := card_le_one_of_mem_kpSquares_zero boundary L (hC.1 (hfC x hx))
  have hyx : y ∈ f x := hxy ▸ hxf y hy
  exact Finset.card_le_one.mp hcard x (hxf x hx) y hyx

/-- KP p. 8: `|𝒮₀(ϱ)| = |supp ϱ|`. -/
theorem squareCoverNumber_zero (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L) :
    squareCoverNumber boundary L 0 ρ = (chargeSupport ρ).card := by
  refine le_antisymm (squareCoverNumber_le_card_chargeSupport boundary L 0 ρ) ?_
  obtain ⟨C, hC, hcard⟩ := exists_squareCover_attaining_number boundary L 0 ρ
  exact hcard ▸ card_chargeSupport_le_card_of_isSquareCover_zero boundary L ρ C hC

/-- : `|𝒮_k(ϱ)| ≤ |𝒮₀(ϱ)|` at every scale `k`. -/
theorem squareCoverNumber_le_squareCoverNumber_zero (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) :
    squareCoverNumber boundary L k ρ ≤ squareCoverNumber boundary L 0 ρ := by
  rw [squareCoverNumber_zero]
  exact squareCoverNumber_le_card_chargeSupport boundary L k ρ

end FroehlichSpencer.BKT

end
