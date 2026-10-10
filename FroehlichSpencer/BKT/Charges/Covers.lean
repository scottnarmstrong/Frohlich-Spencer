/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FroehlichSpencer.BKT.Charges.Geometry

/-! # Finite square covers of charge supports

This module formalizes the finite covering problem in KP §2.1, p. 8. A cover
is a finite collection of allowed scale-`k` squares covering the support of
an integer-valued charge density. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- An integer-valued charge density on the finite square domain. -/
abbrev ChargeDensity (L : ℕ) := (Fin L × Fin L) → ℤ

/-- The finite support of a charge density. -/
def chargeSupport {L : ℕ} (ρ : ChargeDensity L) : Finset (Fin L × Fin L) :=
  Finset.univ.filter fun x => ρ x ≠ 0

/-- The graph distance between the supports of two charge densities. Its
empty-support convention is zero; KP's uses of separation have nonempty
supports. -/
noncomputable def densityDistance (boundary : SquareBoundary) (L : ℕ)
    (ρ σ : ChargeDensity L) : ℕ :=
  squareDistance boundary L (chargeSupport ρ) (chargeSupport σ)

/-- The diameter of a charge support. -/
noncomputable def chargeDiameter (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) : ℕ := squareDiameter boundary L (chargeSupport ρ)


def chargeCoverScale : ℕ := 2 ^ 16


noncomputable def chargeCoverExponent : ℝ := 7 / 4

/-- A collection `C` is a scale-`k` square cover of the support of `ρ`. -/
def IsSquareCover (boundary : SquareBoundary) (L k : ℕ) (ρ : ChargeDensity L)
    (C : Finset (Finset (Fin L × Fin L))) : Prop :=
  C ⊆ kpSquares boundary L k ∧
    ∀ x ∈ chargeSupport ρ, ∃ s ∈ C, x ∈ s

/-- Every vertex, and hence every charge support, is covered by the family of
scale-`k` squares. -/
theorem kpSquares_isSquareCover (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) : IsSquareCover boundary L k ρ (kpSquares boundary L k) := by
  refine ⟨by intro s hs; exact hs, ?_⟩
  intro x hx
  exact mem_kpSquares boundary L k x

/-- The finite family of all scale-`k` square covers of the support. -/
noncomputable def squareCoverCandidates (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) : Finset (Finset (Finset (Fin L × Fin L))) := by
  classical
  exact (kpSquares boundary L k).powerset.filter fun C => IsSquareCover boundary L k ρ C

/-- Membership in the candidate family is exactly the cover property. -/
theorem mem_squareCoverCandidates_iff (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Fin L × Fin L))) :
    C ∈ squareCoverCandidates boundary L k ρ ↔ IsSquareCover boundary L k ρ C := by
  simp [squareCoverCandidates, IsSquareCover]

/-- The candidate family is nonempty: all allowed squares form a cover. -/
theorem squareCoverCandidates_nonempty (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) : (squareCoverCandidates boundary L k ρ).Nonempty := by
  refine ⟨kpSquares boundary L k, ?_⟩
  exact (mem_squareCoverCandidates_iff boundary L k ρ _).2
    (kpSquares_isSquareCover boundary L k ρ)

/-- The minimum number of scale-`k` squares needed to cover a charge support. -/
noncomputable def squareCoverNumber (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) : ℕ :=
  (squareCoverCandidates boundary L k ρ).image Finset.card |>.min'
    (Finset.image_nonempty.mpr (squareCoverCandidates_nonempty boundary L k ρ))

/-- The cutoff `n(ρ) = ⌈log₂(M d(ρ)^α)⌉` from KP (2.3), defined on the
source's locus `d(ρ) ≥ 1`. -/
noncomputable def chargeCutoff (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) (_hd : 1 ≤ chargeDiameter boundary L ρ) : ℕ :=
  Nat.ceil (Real.logb 2 ((chargeCoverScale : ℝ) *
    (chargeDiameter boundary L ρ : ℝ) ^ chargeCoverExponent))

/-- A minimum square cover is a cover whose cardinality is no larger than that
of any other cover. -/
def IsMinimumSquareCover (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Fin L × Fin L))) : Prop :=
  IsSquareCover boundary L k ρ C ∧
    ∀ D, IsSquareCover boundary L k ρ D → C.card ≤ D.card

/-- Every cover has cardinality at least the minimum cover number. -/
theorem squareCoverNumber_le (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Fin L × Fin L)))
    (hC : IsSquareCover boundary L k ρ C) : squareCoverNumber boundary L k ρ ≤ C.card := by
  have hmem : C ∈ squareCoverCandidates boundary L k ρ :=
    (mem_squareCoverCandidates_iff boundary L k ρ C).2 hC
  have hcard : C.card ∈ (squareCoverCandidates boundary L k ρ).image Finset.card :=
    Finset.mem_image.mpr ⟨C, hmem, rfl⟩
  exact Finset.min'_le _ _ hcard

/-- The minimum cover number is realized by a cover. -/
theorem exists_squareCover_attaining_number (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) :
    ∃ C, IsSquareCover boundary L k ρ C ∧ C.card = squareCoverNumber boundary L k ρ := by
  have hmem := Finset.min'_mem
    ((squareCoverCandidates boundary L k ρ).image Finset.card)
    (Finset.image_nonempty.mpr (squareCoverCandidates_nonempty boundary L k ρ))
  rcases Finset.mem_image.mp hmem with ⟨C, hC, hcard⟩
  refine ⟨C, (mem_squareCoverCandidates_iff boundary L k ρ C).1 hC, ?_⟩
  simpa [squareCoverNumber] using hcard

/-- The minimum cover number is attained by some cover. -/
theorem exists_minimumSquareCover (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) : ∃ C, IsMinimumSquareCover boundary L k ρ C := by
  have hcand := squareCoverCandidates_nonempty boundary L k ρ
  rcases Finset.exists_min_image (squareCoverCandidates boundary L k ρ) Finset.card hcand with
    ⟨C, hC, hmin⟩
  refine ⟨C, ?_, ?_⟩
  · exact (mem_squareCoverCandidates_iff boundary L k ρ C).1 hC
  · intro D hD
    exact hmin D ((mem_squareCoverCandidates_iff boundary L k ρ D).2 hD)

/-- The family of all minimum covers of a charge support. -/
noncomputable def minimumSquareCovers (boundary : SquareBoundary) (L k : ℕ)
    (ρ : ChargeDensity L) : Finset (Finset (Finset (Fin L × Fin L))) := by
  classical
  exact (squareCoverCandidates boundary L k ρ).filter fun C =>
    C.card = squareCoverNumber boundary L k ρ

/-- The complexity `A(ρ)` from KP (2.2), with the source's separate zero
diameter branch. -/
noncomputable def chargeCoverCost (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L) : ℕ :=
  if hd : chargeDiameter boundary L ρ = 0 then 0 else
    ∑ k ∈ Finset.range
      (chargeCutoff boundary L ρ (Nat.one_le_iff_ne_zero.mpr hd) + 1),
        squareCoverNumber boundary L k ρ

/-- Every minimum cover has the minimum cover number as its cardinality. -/
theorem card_eq_squareCoverNumber_of_isMinimumSquareCover (boundary : SquareBoundary)
    (L k : ℕ) (ρ : ChargeDensity L) (C : Finset (Finset (Fin L × Fin L)))
    (hC : IsMinimumSquareCover boundary L k ρ C) :
    C.card = squareCoverNumber boundary L k ρ := by
  rcases exists_squareCover_attaining_number boundary L k ρ with ⟨D, hD, hcard⟩
  apply le_antisymm
  · exact (hC.2 D hD).trans_eq hcard
  · exact squareCoverNumber_le boundary L k ρ C hC.1

/-- The separated members of a chosen scale-`k` minimum cover. The separation
threshold is the one in KP (2.4); scale zero is kept out of the interface,
where the source does not define this family. -/
noncomputable def separatedSquares (boundary : SquareBoundary) (L : ℕ)
    (ρ : ChargeDensity L)
    (k : {k : ℕ // 1 ≤ k})
    (C : {C : Finset (Finset (Fin L × Fin L)) //
      IsMinimumSquareCover boundary L k.val ρ C}) : Finset (Finset (Fin L × Fin L)) := by
  classical
  exact C.val.filter fun s => 1 < C.val.card ∧
    ∀ t ∈ C.val, t ≠ s →
      (2 * (chargeCoverScale : ℝ)) * (2 : ℝ) ^
        (chargeCoverExponent * (k.val + 1 : ℕ)) ≤
        (squareDistance boundary L s t : ℝ)

end FroehlichSpencer.BKT

end
