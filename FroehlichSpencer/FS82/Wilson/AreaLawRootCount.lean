/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawSource
public import FroehlichSpencer.FS82.Wilson.AreaLawSupportGraph

/-!
# Boundary roots for the Wilson rectangle

Every plaquette touching a nonzero source link is an admissible root for the
source-bearing animal. A boundary link lies on one of the `L*T` sheet faces,
so four side links per face and at most six incident plaquettes give at most
`24*L*T` roots.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

@[expose] noncomputable def rectangleBoundaryLinks {B : Box 4} (L T : ℕ)
    (hL : L ≤ B 0) (hT : T ≤ B 1) : Finset (PrimalLinks B) :=
  Finset.univ.filter fun l =>
    (boundary (wilsonRectangleSheet L T hL hT)) l.1 ≠ 0

@[expose] noncomputable def rectangleSourceRootPlaquettes {B : Box 4} (L T : ℕ)
    (hL : L ≤ B 0) (hT : T ≤ B 1) : Finset (PrimalPlaquettes B) :=
  (rectangleBoundaryLinks L T hL hT).biUnion fun l =>
    Finset.univ.filter fun p : PrimalPlaquettes B =>
      l ∈ plaquetteBoundaryLinks p

private theorem exists_nonzero_of_finset_sum_ne_zero {α : Type*}
    (s : Finset α) (f : α → ℤ) (h : (∑ x ∈ s, f x) ≠ 0) :
    ∃ x ∈ s, f x ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  apply Finset.sum_eq_zero
  intro x hx
  exact hn x hx

private theorem rectangleBoundaryLinks_subset_sheetFaceLinks {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1) :
    rectangleBoundaryLinks L T hL hT ⊆
      (Finset.univ : Finset (Fin L × Fin T)).biUnion fun x =>
        plaquetteBoundaryLinks
          (⟨wilsonRectanglePlaquette hL hT x.1 x.2, by
            rw [cellDegree, wilsonRectanglePlaquette_axes hL hT x.1 x.2]
            simp⟩ : PrimalPlaquettes B) := by
  classical
  intro l hl
  have hcoef :
      (boundary (wilsonRectangleSheet L T hL hT)) l.1 =
        ∑ x : Fin L × Fin T,
          (boundary (basisChain (wilsonRectanglePlaquette hL hT x.1 x.2))) l.1 := by
    unfold wilsonRectangleSheet
    rw [map_sum, finsupp_finset_sum_apply]
  have hsum :
      (∑ x : Fin L × Fin T,
        (boundary (basisChain (wilsonRectanglePlaquette hL hT x.1 x.2))) l.1) ≠ 0 := by
    rw [← hcoef]
    exact (Finset.mem_filter.mp hl).2
  obtain ⟨x, hx, hxne⟩ := exists_nonzero_of_finset_sum_ne_zero
    (Finset.univ : Finset (Fin L × Fin T))
    (fun x => (boundary (basisChain
      (wilsonRectanglePlaquette hL hT x.1 x.2))) l.1) hsum
  refine Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, ?_⟩
  let p : PrimalPlaquettes B := ⟨wilsonRectanglePlaquette hL hT x.1 x.2, by
    rw [cellDegree, wilsonRectanglePlaquette_axes hL hT x.1 x.2]
    simp⟩
  have hface : (boundary (Finsupp.single p.1 (1 : ℤ))) l.1 ≠ 0 := by
    simpa [p, basisChain] using hxne
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hface⟩

/-- The source loop has at most four candidate links per sheet face. -/
private theorem rectangleBoundaryLinks_card_le_four_mul_area {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1) :
    (rectangleBoundaryLinks L T hL hT).card ≤ 4 * (L * T) := by
  classical
  let faces : Finset (PrimalPlaquettes B) :=
    Finset.univ.image fun x : Fin L × Fin T =>
      (⟨wilsonRectanglePlaquette hL hT x.1 x.2, by
        rw [cellDegree, wilsonRectanglePlaquette_axes hL hT x.1 x.2]
        simp⟩ : PrimalPlaquettes B)
  let faceLinks : Finset (PrimalLinks B) :=
    faces.biUnion plaquetteBoundaryLinks
  have hfacesCover : rectangleBoundaryLinks L T hL hT ⊆ faceLinks := by
    intro l hl
    have hsub := rectangleBoundaryLinks_subset_sheetFaceLinks hL hT hl
    rcases Finset.mem_biUnion.mp hsub with ⟨x, hx, hlink⟩
    refine Finset.mem_biUnion.mpr ⟨_, ?_, hlink⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hcoverCard : faceLinks.card ≤
      ∑ p ∈ faces, (plaquetteBoundaryLinks p).card := by
    dsimp [faceLinks]
    exact Finset.card_biUnion_le
  have hsum : (∑ p ∈ faces, (plaquetteBoundaryLinks p).card) ≤
      ∑ _p ∈ faces, 4 := by
    apply Finset.sum_le_sum
    intro p hp
    exact plaquetteBoundaryLinks_card_le_four p
  have hsum' : (∑ _p ∈ faces, 4) ≤ 4 * (L * T) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hfaces : faces.card ≤ L * T := by
      dsimp [faces]
      calc
        (Finset.univ.image fun x : Fin L × Fin T =>
            (⟨wilsonRectanglePlaquette hL hT x.1 x.2, by
              rw [cellDegree, wilsonRectanglePlaquette_axes hL hT x.1 x.2]
              simp⟩ : PrimalPlaquettes B)).card ≤
            (Finset.univ : Finset (Fin L × Fin T)).card := Finset.card_image_le
        _ = L * T := by simp
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right 4 hfaces
  calc
    (rectangleBoundaryLinks L T hL hT).card ≤ faceLinks.card := Finset.card_le_card hfacesCover
    _ ≤ ∑ p ∈ faces, (plaquetteBoundaryLinks p).card := hcoverCard
    _ ≤ ∑ _p ∈ faces, 4 := hsum
    _ ≤ 4 * (L * T) := hsum'

/-- There are at most `24*L*T` plaquettes incident to the source loop. -/
theorem rectangleSourceRootPlaquettes_card_le {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) :
    (rectangleSourceRootPlaquettes L T hL hT).card ≤ 24 * (L * T) := by
  classical
  have hcover : (rectangleSourceRootPlaquettes L T hL hT).card ≤
      ∑ l ∈ rectangleBoundaryLinks L T hL hT,
        (Finset.univ.filter fun p : PrimalPlaquettes B =>
          l ∈ plaquetteBoundaryLinks p).card := by
    dsimp [rectangleSourceRootPlaquettes]
    exact Finset.card_biUnion_le
  have hsum :
      (∑ l ∈ rectangleBoundaryLinks L T hL hT,
        (Finset.univ.filter fun p : PrimalPlaquettes B =>
          l ∈ plaquetteBoundaryLinks p).card) ≤
        ∑ _l ∈ rectangleBoundaryLinks L T hL hT, 6 := by
    apply Finset.sum_le_sum
    intro l hl
    exact plaquettesAtLink_card_le_six l
  have hsum' :
      (∑ _l ∈ rectangleBoundaryLinks L T hL hT, 6) ≤
        24 * (L * T) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hlinks := rectangleBoundaryLinks_card_le_four_mul_area hL hT
    calc
      (rectangleBoundaryLinks L T hL hT).card * 6 ≤
          (4 * (L * T)) * 6 := Nat.mul_le_mul_right 6 hlinks
      _ = 24 * (L * T) := by ring
  exact hcover.trans (hsum.trans hsum')

/-- Connected supports of size `k` touching the rectangle source have at most
`24*L*T*400^k` possibilities. -/
theorem card_rectangleSourceAnimalSupports_le {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (k : ℕ) (hk : 1 ≤ k) :
    ((rectangleSourceRootPlaquettes L T hL hT).biUnion fun p =>
      FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p k).card ≤
      24 * (L * T) * 400 ^ k := by
  classical
  calc
    _ ≤ ∑ p ∈ rectangleSourceRootPlaquettes L T hL hT,
        (FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ rectangleSourceRootPlaquettes L T hL hT, 400 ^ k := by
      apply Finset.sum_le_sum
      intro p hp
      exact card_linkConnectedPlaquetteSupports_le p k hk
    _ = (rectangleSourceRootPlaquettes L T hL hT).card * 400 ^ k := by
      simp [Finset.sum_const]
    _ ≤ 24 * (L * T) * 400 ^ k :=
      Nat.mul_le_mul_right (400 ^ k)
        (rectangleSourceRootPlaquettes_card_le hL hT)

end FroehlichSpencer.FS82.Wilson

end
