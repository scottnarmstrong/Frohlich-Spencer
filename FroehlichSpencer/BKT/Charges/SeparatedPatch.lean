/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.PatchIsolation

/-! # Isolation properties of separated minimum-cover squares

This module extracts the support-patch hypotheses from the definitions in
KP (2.4). In particular, every support point outside a separated square is
at least the separation threshold away from every point of that square. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The real separation threshold in KP (2.4), with the project-wide choice
`α = 7/4` and `M = 2^16`. -/
noncomputable def squareSeparationThreshold (k : PositiveSquareScale) : ℝ :=
  (2 * (chargeCoverScale : ℝ)) * (2 : ℝ) ^
    (chargeCoverExponent * (k.val + 1 : ℕ))

/-- A square in a minimum cover cannot have empty intersection with the charge
support: removing it would give a smaller cover. -/
theorem supportPatch_nonempty_of_mem_minimumSquareCover
    (boundary : SquareBoundary) (L k : ℕ) (ρ : ChargeDensity L)
    (C : Finset (Finset (Fin L × Fin L)))
    (hC : IsMinimumSquareCover boundary L k ρ C)
    (s : Finset (Fin L × Fin L)) (hs : s ∈ C) :
    (s ∩ chargeSupport ρ).Nonempty := by
  classical
  by_contra hne
  have hno : ∀ x, x ∉ s ∩ chargeSupport ρ := by
    intro x hx
    exact hne ⟨x, hx⟩
  let D := C.erase s
  have hDcover : IsSquareCover boundary L k ρ D := by
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hC.1.1 (Finset.mem_erase.mp ht).2
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := hC.1.2 x hx
      by_cases hts : t = s
      · subst t
        exact False.elim (hno x (Finset.mem_inter.mpr ⟨hxt, hx⟩))
      · exact ⟨t, Finset.mem_erase.mpr ⟨hts, ht⟩, hxt⟩
  have hmin := hC.2 D hDcover
  have hcard := Finset.card_erase_add_one hs
  dsimp [D] at hmin hcard
  omega

/-- Separation of a member of `S_k^sep` passes from the other cover squares
to every support point outside that square. -/
theorem pointwise_separation_of_separatedSquare
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L)
    (k : PositiveSquareScale)
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val ρ C})
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ separatedSquares boundary L ρ k C) :
    ∀ x ∈ s, ∀ y ∈ chargeSupport ρ \ s,
      squareSeparationThreshold k ≤ latticeDistance boundary L x y := by
  classical
  have hs' : s ∈ C.val ∧ 1 < C.val.card ∧
      ∀ t ∈ C.val, t ≠ s →
        (2 * (chargeCoverScale : ℝ)) * (2 : ℝ) ^
          (chargeCoverExponent * (k.val + 1 : ℕ)) ≤
            (squareDistance boundary L s t : ℝ) := by
    simpa [separatedSquares] using hs
  intro x hx y hy
  have hy' := Finset.mem_sdiff.mp hy
  obtain ⟨t, ht, hyt⟩ := C.property.1.2 y hy'.1
  have hts : t ≠ s := by
    intro hEq
    subst t
    exact hy'.2 hyt
  have hsetSep := hs'.2.2 t ht hts
  exact hsetSep.trans
    (squareDistance_le_latticeDistance_real_of_mem boundary L s t x y hx hyt)

/-- The support patch of a separated square is nonempty, by minimum-cover
minimality. -/
theorem separatedSquare_patch_nonempty
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L)
    (k : PositiveSquareScale)
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val ρ C})
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ separatedSquares boundary L ρ k C) :
    (s ∩ chargeSupport ρ).Nonempty := by
  have hsC : s ∈ C.val := by
    have hs' := hs
    simp only [separatedSquares, Finset.mem_filter] at hs'
    exact hs'.1
  exact supportPatch_nonempty_of_mem_minimumSquareCover boundary L k.val ρ
    C.val C.property s hsC

/-- A separated member cannot occur once the scale square fills the domain:
at that scale the allowed square family is a singleton and every minimum
cover has at most one member. -/
theorem squareSide_le_domain_of_mem_separatedSquares
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L)
    (k : PositiveSquareScale)
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val ρ C})
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ separatedSquares boundary L ρ k C) :
    squareSide k.val ≤ L := by
  by_contra hside
  have hlarge : L < squareSide k.val := by omega
  have hall : ∀ a : Fin L × Fin L, kpSquare boundary L k.val a = Finset.univ := by
    intro a
    cases boundary with
    | free => simp [kpSquare, hlarge]
    | periodic => simp [kpSquare, Nat.le_of_lt hlarge]
  have hsubset : C.val ⊆ {Finset.univ} := by
    intro t ht
    rcases Finset.mem_image.mp (C.property.1.1 ht) with ⟨a, -, hta⟩
    have hteq : t = Finset.univ := hta.symm.trans (hall a)
    simp [hteq]
  have hcard : C.val.card ≤ 1 := by
    calc
      C.val.card ≤ ({Finset.univ} : Finset (Finset (Fin L × Fin L))).card :=
        Finset.card_le_card hsubset
      _ = 1 := Finset.card_singleton _
  have hs' := hs
  simp only [separatedSquares, Finset.mem_filter] at hs'
  omega

/-- The explicit parent meets the support exactly in the source patch, once
the elementary target-diameter estimate is supplied. -/
theorem separatedSquare_parent_inter_support_eq_patch
    (boundary : SquareBoundary) (L : ℕ) (ρ : ChargeDensity L)
    (k : PositiveSquareScale) (j : ParentOffset) (hL : 0 < L)
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val ρ C})
    (s : Finset (Fin L × Fin L))
    (hs : s ∈ separatedSquares boundary L ρ k C)
    (hsourceSide : squareSide k.val ≤ L)
    (hparentDiameter : (squareDiameter boundary L
      (ancestorParent boundary L k j hL s) : ℝ) < squareSeparationThreshold k) :
    ancestorParent boundary L k j hL s ∩ chargeSupport ρ = s ∩ chargeSupport ρ := by
  have hsC : s ∈ C.val := by
    have hs' := hs
    simp only [separatedSquares, Finset.mem_filter] at hs'
    exact hs'.1
  apply ancestorParent_inter_support_eq_source_inter boundary L k j hL s
    (chargeSupport ρ) (C.property.1.1 hsC) hsourceSide
    (squareSeparationThreshold k) (separatedSquare_patch_nonempty boundary L ρ k C s hs)
  · intro x hx y hy
    exact pointwise_separation_of_separatedSquare boundary L ρ k C s hs x hx y hy
  · exact hparentDiameter

end FroehlichSpencer.BKT

end
