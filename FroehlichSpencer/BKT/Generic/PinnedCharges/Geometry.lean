/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.Covers
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary boundary geometry for pinned charge densities

This file records the Euclidean support geometry used by FS81 Appendix D on a
finite square.

It deliberately does not identify the source's Euclidean
distance with the graph distance in the KP charge API.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

abbrev Site (L : ℕ) := Fin L × Fin L

/-- Euclidean distance between two lattice sites, with coordinates embedded
in the ambient real plane. -/
def euclideanSiteDistance {L : ℕ} (x y : Site L) : ℝ :=
  Real.sqrt (((x.1.val : ℝ) - y.1.val) ^ 2 + ((x.2.val : ℝ) - y.2.val) ^ 2)

/-- Minimum Euclidean distance between two finite sets of sites.  The empty
set convention is zero; source-facing uses below require nonempty supports. -/
noncomputable def euclideanSetDistance {L : ℕ}
    (s t : Finset (Site L)) : ℝ :=
  if h : (s.product t).Nonempty then
    ((s.product t).image fun p => euclideanSiteDistance p.1 p.2).min'
      (Finset.image_nonempty.mpr h)
  else 0

/-- Euclidean diameter of a finite set, with zero value for the empty set. -/
noncomputable def euclideanSetDiameter {L : ℕ} (s : Finset (Site L)) : ℝ :=
  if h : (s.product s).Nonempty then
    ((s.product s).image fun p => euclideanSiteDistance p.1 p.2).max'
      (Finset.image_nonempty.mpr h)
  else 0

/-- Number of lattice steps from a site to the nearest site outside the
finite square.  This equals the Euclidean distance to the lattice complement. -/
def siteBoundaryDepth {L : ℕ} (x : Site L) : ℕ :=
  min (x.1.val + 1)
    (min (L - x.1.val) (min (x.2.val + 1) (L - x.2.val)))

theorem siteBoundaryDepth_pos {L : ℕ} (x : Site L) : 0 < siteBoundaryDepth x := by
  unfold siteBoundaryDepth
  omega

/-- Distance from a finite set of sites to the complement of the square. -/
noncomputable def euclideanBoundaryDistance {L : ℕ}
    (s : Finset (Site L)) : ℝ :=
  if h : s.Nonempty then
    ((s.image fun x => (siteBoundaryDepth x : ℝ)).min'
      (Finset.image_nonempty.mpr h))
  else 0

theorem euclideanBoundaryDistance_pos_of_nonempty {L : ℕ}
    (s : Finset (Site L)) (hs : s.Nonempty) : 0 < euclideanBoundaryDistance s := by
  rw [euclideanBoundaryDistance, dite_eq_left hs]
  let d : Site L → ℝ := fun x => (siteBoundaryDepth x : ℝ)
  have himage : (s.image d).Nonempty := Finset.image_nonempty.mpr hs
  obtain ⟨x, hx, hvalue⟩ := Finset.mem_image.mp
    (Finset.min'_mem (s.image d) himage)
  rw [← hvalue]
  change (0 : ℝ) < (siteBoundaryDepth x : ℝ)
  exact_mod_cast siteBoundaryDepth_pos x

theorem euclideanBoundaryDistance_ge_one_of_nonempty {L : ℕ}
    (s : Finset (Site L)) (hs : s.Nonempty) :
    1 ≤ euclideanBoundaryDistance s := by
  rw [euclideanBoundaryDistance, dite_eq_left hs]
  let d : Site L → ℝ := fun x => (siteBoundaryDepth x : ℝ)
  have himage : (s.image d).Nonempty := Finset.image_nonempty.mpr hs
  obtain ⟨x, hx, hvalue⟩ := Finset.mem_image.mp
    (Finset.min'_mem (s.image d) himage)
  rw [← hvalue]
  change (1 : ℝ) ≤ (siteBoundaryDepth x : ℝ)
  exact_mod_cast (Nat.succ_le_iff.mpr (siteBoundaryDepth_pos x))

/-- Total integer charge of a density. -/
def totalCharge {L : ℕ} (ρ : ChargeDensity L) : ℤ := ∑ x, ρ x

theorem chargeSupport_nonempty_of_ne_zero {L : ℕ} (ρ : ChargeDensity L)
    (hρ : ρ ≠ 0) : (chargeSupport ρ).Nonempty := by
  classical
  by_contra h
  have hempty : chargeSupport ρ = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hex : ∃ x, ρ x ≠ 0 := by
    by_contra hn
    apply hρ
    funext x
    by_contra hx
    exact hn ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hex
  have hmem : x ∈ chargeSupport ρ := by simp [chargeSupport, hx]
  rw [hempty] at hmem
  simp at hmem

/-- Euclidean support diameter of a charge density. -/
noncomputable def chargeEuclideanDiameter {L : ℕ} (ρ : ChargeDensity L) : ℝ :=
  euclideanSetDiameter (chargeSupport ρ)

/-- Support-to-boundary distance of a charge density. -/
noncomputable def chargeBoundaryDistance {L : ℕ} (ρ : ChargeDensity L) : ℝ :=
  euclideanBoundaryDistance (chargeSupport ρ)

theorem chargeBoundaryDistance_pos_of_ne_zero {L : ℕ} (ρ : ChargeDensity L)
    (hρ : ρ ≠ 0) : 0 < chargeBoundaryDistance ρ :=
  euclideanBoundaryDistance_pos_of_nonempty (chargeSupport ρ)
    (chargeSupport_nonempty_of_ne_zero ρ hρ)

theorem chargeBoundaryDistance_ge_one_of_ne_zero {L : ℕ}
    (ρ : ChargeDensity L) (hρ : ρ ≠ 0) :
    1 ≤ chargeBoundaryDistance ρ :=
  euclideanBoundaryDistance_ge_one_of_nonempty (chargeSupport ρ)
    (chargeSupport_nonempty_of_ne_zero ρ hρ)

/-- Appendix D's boundary-modified size `d_Λ(ρ)`. -/
noncomputable def boundaryAdjustedSize {L : ℕ} (ρ : ChargeDensity L) : ℝ :=
  if totalCharge ρ = 0 then chargeEuclideanDiameter ρ
  else max (chargeBoundaryDistance ρ) (chargeEuclideanDiameter ρ)

@[simp]
theorem boundaryAdjustedSize_of_neutral {L : ℕ} (ρ : ChargeDensity L)
    (hρ : totalCharge ρ = 0) :
    boundaryAdjustedSize ρ = chargeEuclideanDiameter ρ := by
  simp [boundaryAdjustedSize, hρ]

@[simp]
theorem boundaryAdjustedSize_of_charged {L : ℕ} (ρ : ChargeDensity L)
    (hρ : totalCharge ρ ≠ 0) :
    boundaryAdjustedSize ρ = max (chargeBoundaryDistance ρ)
      (chargeEuclideanDiameter ρ) := by
  simp [boundaryAdjustedSize, hρ]

theorem chargeEuclideanDiameter_le_boundaryAdjustedSize {L : ℕ}
    (ρ : ChargeDensity L) :
    chargeEuclideanDiameter ρ ≤ boundaryAdjustedSize ρ := by
  by_cases hρ : totalCharge ρ = 0
  · simp [boundaryAdjustedSize, hρ]
  · simp [boundaryAdjustedSize, hρ]

theorem chargeBoundaryDistance_le_boundaryAdjustedSize_of_charged {L : ℕ}
    (ρ : ChargeDensity L) (hρ : totalCharge ρ ≠ 0) :
    chargeBoundaryDistance ρ ≤ boundaryAdjustedSize ρ := by
  rw [boundaryAdjustedSize_of_charged ρ hρ]
  exact le_max_left _ _

theorem one_le_boundaryAdjustedSize_of_charged_ne_zero {L : ℕ}
    (ρ : ChargeDensity L) (hρ : totalCharge ρ ≠ 0) (hρ' : ρ ≠ 0) :
    1 ≤ boundaryAdjustedSize ρ := by
  exact (chargeBoundaryDistance_ge_one_of_ne_zero ρ hρ').trans
    (chargeBoundaryDistance_le_boundaryAdjustedSize_of_charged ρ hρ)

/-- Appendix D's boundary-adjusted dyadic scale cutoff.  Its source use is on
nonzero densities, for which `dΛ` is positive. -/
noncomputable def boundaryChargeCutoff {L : ℕ} (M α : ℝ)
    (ρ : ChargeDensity L) : ℕ :=
  Nat.ceil (Real.logb 2 (M * boundaryAdjustedSize ρ ^ α))

/-- The source's isolated-constituent relation: the child agrees with the
parent on its support, and its support lies inside the parent's support. -/
def IsConstituent {L : ℕ} (parent child : ChargeDensity L) : Prop :=
  child ≠ 0 ∧ chargeSupport child ⊆ chargeSupport parent ∧
    ∀ x ∈ chargeSupport child, parent x = child x

/-- A finite pinned ensemble consists of nonzero, pairwise support-disjoint
charge densities. -/
def IsPinnedChargeEnsemble {L : ℕ} (N : Finset (ChargeDensity L)) : Prop :=
  (∀ ρ ∈ N, ρ ≠ 0) ∧
    ∀ ρ ∈ N, ∀ σ ∈ N, ρ ≠ σ →
      Disjoint (chargeSupport ρ) (chargeSupport σ)

/-- Pairwise Appendix D separation at the source parameters `M` and `α`. -/
def IsBoundarySeparated {L : ℕ} (M α : ℝ)
    (N : Finset (ChargeDensity L)) : Prop :=
  ∀ ρ ∈ N, ∀ σ ∈ N, ρ ≠ σ →
    M * min (boundaryAdjustedSize ρ) (boundaryAdjustedSize σ) ^ α ≤
      euclideanSetDistance (chargeSupport ρ) (chargeSupport σ)

/-- Appendix D's isolation conclusion for every constituent of an ensemble. -/
def HasBoundaryIsolation {L : ℕ} (M α : ℝ)
    (N : Finset (ChargeDensity L)) : Prop :=
  ∀ ρ ∈ N, ∀ ρ₁, IsConstituent ρ ρ₁ →
    2 * M * chargeEuclideanDiameter ρ₁ ^ α ≤
      euclideanSetDistance (chargeSupport ρ₁)
        (chargeSupport (fun x => ρ x - ρ₁ x)) →
    totalCharge ρ₁ ≠ 0 ∧
      euclideanSetDistance (chargeSupport ρ₁)
        (chargeSupport (fun x => ρ x - ρ₁ x)) ≤
        2 * M * chargeBoundaryDistance ρ₁ ^ α

/-- The complete geometric part of the Appendix D layer contract.  The
mixture construction must provide these clauses for each output ensemble. -/
structure AppendixDChargeGeometry {L : ℕ} (M α : ℝ)
    (N : Finset (ChargeDensity L)) : Prop where
  ensemble : IsPinnedChargeEnsemble N
  separated : IsBoundarySeparated M α N
  isolated : HasBoundaryIsolation M α N

/-- The Dirichlet self-energy clause stated in Appendix D. -/
def HasDirichletEnergyLowerBound {L : ℕ}
    (energy : ChargeDensity L → ℝ) : Prop :=
  ∀ ρ, ρ ≠ 0 → Real.log (boundaryAdjustedSize ρ) ≤ energy ρ

/-- The source's boundary-decaying activity clause for a finite pinned
ensemble. -/
def HasBoundaryActivityBound {L : ℕ} (N : Finset (ChargeDensity L))
    (activity : ChargeDensity L → ℝ) (decayRate : ℝ) : Prop :=
  ∀ ρ ∈ N,
    |activity ρ| ≤ Real.exp (-decayRate * Real.log (boundaryAdjustedSize ρ))

/-- The square-boundary margin used in `P'_k`. -/
def scaleBoundaryMargin (k : ℕ) : ℝ := (2 : ℝ) ^ (k + 2)

/-- The extra margin in the source's one-square exception. -/
def singletonBoundaryMargin (k : ℕ) : ℝ := (2 : ℝ) ^ (k + 3)

/-- A square satisfies the pairwise part of FS81 (3.3) in a chosen minimum
cover. -/
def IsSourceSeparatedSquare {L : ℕ} (M α : ℝ) (k : ℕ)
    (C : Finset (Finset (Site L))) (s : Finset (Site L)) : Prop :=
  s ∈ C ∧ ∀ t ∈ C, t ≠ s →
    2 * M * (2 : ℝ) ^ (α * (k : ℝ)) ≤ euclideanSetDistance s t

/-- The Appendix D selected-square family `P'_k(ρ, Λ)`, kept separate from
the unmodified §3 family.  The one-cover-square rule is the source's explicit
override. -/
noncomputable def pinnedPPrime {L : ℕ} (M α : ℝ) (k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L))) :
    Finset (Finset (Site L)) := by
  classical
  exact if hsingle : C.card = 1 then
    if totalCharge ρ ≠ 0 ∧ singletonBoundaryMargin k ≤ chargeBoundaryDistance ρ
      then C else ∅
  else
    C.filter fun s =>
      IsSourceSeparatedSquare M α k C s ∧
      scaleBoundaryMargin k ≤ euclideanBoundaryDistance s

theorem mem_pinnedPPrime_of_cover_card_ne_one {L : ℕ} (M α : ℝ) (k : ℕ)
    (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : C.card ≠ 1) (s : Finset (Site L)) :
    s ∈ pinnedPPrime M α k ρ C ↔
  s ∈ C ∧
        (∀ t ∈ C, t ≠ s →
          2 * M * (2 : ℝ) ^ (α * (k : ℝ)) ≤ euclideanSetDistance s t) ∧
        scaleBoundaryMargin k ≤ euclideanBoundaryDistance s := by
  classical
  by_cases hsingle : C.card = 1
  · exact (hC hsingle).elim
  · simp [pinnedPPrime, hsingle, IsSourceSeparatedSquare, and_assoc]

theorem pinnedPPrime_eq_self_of_singleton_exception {L : ℕ} (M α : ℝ)
    (k : ℕ) (ρ : ChargeDensity L) (C : Finset (Finset (Site L)))
    (hC : C.card = 1) (hQ : totalCharge ρ ≠ 0)
    (hmargin : singletonBoundaryMargin k ≤ chargeBoundaryDistance ρ) :
    pinnedPPrime M α k ρ C = C := by
  classical
  simp [pinnedPPrime, hC, hQ, hmargin]

theorem pinnedPPrime_eq_empty_of_singleton_exception_fails {L : ℕ}
    (M α : ℝ) (k : ℕ) (ρ : ChargeDensity L)
    (C : Finset (Finset (Site L))) (hC : C.card = 1)
    (hfail : ¬ (totalCharge ρ ≠ 0 ∧
      singletonBoundaryMargin k ≤ chargeBoundaryDistance ρ)) :
    pinnedPPrime M α k ρ C = ∅ := by
  classical
  simp [pinnedPPrime, hC, hfail]

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
