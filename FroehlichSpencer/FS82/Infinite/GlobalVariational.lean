/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.LatticeOperator
public import FroehlichSpencer.FS82.Gaussian.LatticePath
public import FroehlichSpencer.FS82.Gaussian.IntegerGauge

/-!
# Compact global variational covariance

The global object is the supremum over finite-support coordinate-oriented
lattice link fields. All links and curls use the physical lattice orientation;
source-star fields are transported by the C2 twist in the finite bridge.
-/

public section

namespace FroehlichSpencer.FS82.Infinite

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

/-- The cubical degree of an integer-lattice cell. -/
@[expose] noncomputable def latticeCellDegree (c : LatticeCell 4) : ℕ := by
  classical exact (Finset.univ.filter fun i : Fin 4 => latticeIsEdge (c i)).card

/-- Finitely supported real lattice link fields. -/
abbrev GlobalLinkField := {q : RealLatticeChain 4 //
  ∀ c ∈ q.support, latticeCellDegree c = 1}

/-- Finitely supported real lattice plaquette fields. -/
abbrev GlobalPlaquetteField := {q : RealLatticeChain 4 //
  ∀ c ∈ q.support, latticeCellDegree c = 2}

/-- The full-lattice real coboundary on finitely supported fields. -/
@[expose] noncomputable def globalCoboundary :
    RealLatticeChain 4 →ₗ[ℝ] RealLatticeChain 4 :=
  sourceRealLatticeCoboundary

/-- The full-lattice real boundary, the transpose of the coboundary. -/
@[expose] noncomputable def globalBoundary :
    RealLatticeChain 4 →ₗ[ℝ] RealLatticeChain 4 :=
  realLatticeBoundary

/-- Pairing of two finitely supported lattice chains. -/
@[expose] def globalPairing (q r : RealLatticeChain 4) : ℝ :=
  q.sum fun c a => a * r c

/-- Squared Euclidean norm of a finitely supported lattice field. -/
@[expose] def globalNormSq (q : RealLatticeChain 4) : ℝ :=
  globalPairing q q

/-- Global divergence-free condition on a compactly supported link field. -/
@[expose] def globallyCoClosed (μ : GlobalLinkField) : Prop :=
  globalBoundary (μ : RealLatticeChain 4) = 0

/-- The compact-field variational objective. -/
@[expose] noncomputable def globalVariationalObjective
    (μ φ : GlobalLinkField) : ℝ :=
  2 * globalPairing (μ : RealLatticeChain 4) (φ : RealLatticeChain 4) -
    globalNormSq (globalCoboundary (φ : RealLatticeChain 4))

/-- Infinite-volume variational covariance, defined as a real supremum over all
finitely supported link fields. -/
@[expose] noncomputable def globalVariationalCovariance
    (μ : GlobalLinkField) : ℝ :=
  sSup {r : ℝ | ∃ φ : GlobalLinkField, globalVariationalObjective μ φ = r}

theorem globalPairing_eq_union (q r : RealLatticeChain 4) :
    globalPairing q r =
      ∑ c ∈ q.support ∪ r.support, q c * r c := by
  classical
  unfold globalPairing
  change (∑ c ∈ q.support, q c * r c) = _
  apply Finset.sum_subset (Finset.subset_union_left)
  intro c hcu hnot
  simp [Finsupp.notMem_support_iff.mp hnot]

theorem globalPairing_add_left (q r s : RealLatticeChain 4) :
    globalPairing (q + r) s = globalPairing q s + globalPairing r s := by
  unfold globalPairing
  rw [Finsupp.sum_add_index' (by intro c; simp)
    (by intro c a b; simp [add_mul])]

theorem globalPairing_add_right (q r s : RealLatticeChain 4) :
    globalPairing q (r + s) = globalPairing q r + globalPairing q s := by
  unfold globalPairing
  change (∑ c ∈ q.support, q c * (r c + s c)) =
    (∑ c ∈ q.support, q c * r c) + ∑ c ∈ q.support, q c * s c
  calc
    (∑ c ∈ q.support, q c * (r c + s c)) =
        ∑ c ∈ q.support, (q c * r c + q c * s c) := by
          apply Finset.sum_congr rfl
          intro c hc
          ring
    _ = _ := Finset.sum_add_distrib

theorem globalPairing_sub_left (q r s : RealLatticeChain 4) :
    globalPairing (q - r) s = globalPairing q s - globalPairing r s := by
  unfold globalPairing
  rw [Finsupp.sum_sub_index (by intro c a b; simp [sub_mul])]

theorem globalPairing_sub_right (q r s : RealLatticeChain 4) :
    globalPairing q (r - s) = globalPairing q r - globalPairing q s := by
  unfold globalPairing
  change (∑ c ∈ q.support, q c * (r c - s c)) =
    (∑ c ∈ q.support, q c * r c) - ∑ c ∈ q.support, q c * s c
  calc
    (∑ c ∈ q.support, q c * (r c - s c)) =
        ∑ c ∈ q.support, (q c * r c - q c * s c) := by
          apply Finset.sum_congr rfl
          intro c hc
          ring
    _ = _ := by rw [Finset.sum_sub_distrib]

theorem globalPairing_symm (q r : RealLatticeChain 4) :
    globalPairing q r = globalPairing r q := by
  classical
  calc
    globalPairing q r =
        ∑ c ∈ q.support ∪ r.support, q c * r c := globalPairing_eq_union q r
    _ = ∑ c ∈ r.support ∪ q.support, r c * q c := by
      rw [Finset.union_comm]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = globalPairing r q := (globalPairing_eq_union r q).symm

theorem globalPairing_smul_left (a : ℝ) (q r : RealLatticeChain 4) :
    globalPairing (a • q) r = a * globalPairing q r := by
  unfold globalPairing
  rw [Finsupp.sum_smul_index (by intro c; simp)]
  calc
    q.sum (fun c x => (a * x) * r c) =
        a • q.sum (fun c x => x * r c) := by
          change (∑ c ∈ q.support, (a * q c) * r c) =
            a • (∑ c ∈ q.support, q c * r c)
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          simp only [smul_eq_mul]
          ring
    _ = a * q.sum (fun c x => x * r c) := by simp [smul_eq_mul]

@[simp] theorem globalPairing_self_nonneg (q : RealLatticeChain 4) :
    0 ≤ globalPairing q q := by
  classical
  unfold globalPairing
  change 0 ≤ ∑ c ∈ q.support, q c * q c
  apply Finset.sum_nonneg
  intro c hc
  exact mul_self_nonneg _

private theorem globalPairing_boundary_single
    (c : LatticeCell 4) (φ : RealLatticeChain 4) :
    globalPairing (globalBoundary (Finsupp.single c (1 : ℝ))) φ =
      globalPairing (Finsupp.single c (1 : ℝ)) (globalCoboundary φ) := by
  have hcoeff : (globalCoboundary φ) c =
      globalPairing φ (castLatticeChain (latticeBoundaryBasis c)) := by
    simp [globalCoboundary, globalPairing, sourceRealLatticeCoboundary,
      Finsupp.linearCombination_apply, castLatticeChain_apply,
      latticeCoboundaryBasis_transpose]
  rw [globalBoundary, realLatticeBoundary_basis]
  calc
    globalPairing (castLatticeChain (latticeBoundaryBasis c)) φ =
        globalPairing φ (castLatticeChain (latticeBoundaryBasis c)) :=
          globalPairing_symm _ _
    _ = (globalCoboundary φ) c := hcoeff.symm
    _ = globalPairing (Finsupp.single c (1 : ℝ)) (globalCoboundary φ) := by
      simp [globalPairing]

/-- The lattice incidence matrices are transposes, so compact boundary and
coboundary are adjoints for the coefficient pairing. -/
theorem globalPairing_boundary_coboundary
    (σ φ : RealLatticeChain 4) :
    globalPairing (globalBoundary σ) φ =
      globalPairing σ (globalCoboundary φ) := by
  classical
  induction σ using Finsupp.induction_linear with
  | zero => simp [globalBoundary, globalCoboundary, globalPairing]
  | add q r hq hr =>
      rw [globalBoundary.map_add, globalPairing_add_left,
        globalPairing_add_left, hq, hr]
  | single c a =>
      have hs : Finsupp.single c a = a • Finsupp.single c (1 : ℝ) := by
        ext f
        by_cases h : f = c <;> simp [h]
      have hleft : globalBoundary (Finsupp.single c a) =
          a • globalBoundary (Finsupp.single c (1 : ℝ)) := by
        rw [hs, map_smul]
      have hright : Finsupp.single c a = a • Finsupp.single c (1 : ℝ) := hs
      rw [hleft, hright, globalPairing_smul_left, globalPairing_smul_left]
      exact congrArg (fun z : ℝ => a * z)
        (globalPairing_boundary_single c φ)

/-- A compact filling bounds every value of the variational objective by its
squared norm. -/
theorem globalVariationalObjective_le_of_filling
    (μ φ : GlobalLinkField) (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4)) :
    globalVariationalObjective μ φ ≤ globalNormSq (σ : RealLatticeChain 4) := by
  rw [globalVariationalObjective]
  rw [← hfill, globalPairing_boundary_coboundary]
  have hnonneg := globalPairing_self_nonneg
    ((σ : RealLatticeChain 4) - globalCoboundary (φ : RealLatticeChain 4))
  simp only [globalPairing_sub_left, globalPairing_sub_right] at hnonneg
  rw [globalPairing_symm (globalCoboundary (φ : RealLatticeChain 4)) σ] at hnonneg
  unfold globalNormSq
  nlinarith

/-- Any finite filling witnesses an upper bound on the variational covariance.
The existence of a compact filling for every compact co-closed μ is a separate
compact exactness theorem. -/
theorem globalVariationalCovariance_le_of_filling
    (μ : GlobalLinkField) (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4)) :
    globalVariationalCovariance μ ≤ globalNormSq (σ : RealLatticeChain 4) := by
  apply csSup_le
  · refine ⟨globalVariationalObjective μ ⟨0, by simp [latticeCellDegree]⟩, ?_⟩
    exact ⟨⟨0, by simp [latticeCellDegree]⟩, rfl⟩
  · intro r hr
    rcases hr with ⟨φ, rfl⟩
    exact globalVariationalObjective_le_of_filling μ φ σ hfill

end FroehlichSpencer.FS82.Infinite

end
