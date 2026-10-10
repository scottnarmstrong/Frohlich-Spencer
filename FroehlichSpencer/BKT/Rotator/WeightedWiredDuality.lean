/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Duality.Expectation

/-!
# Arbitrary edge weights under the wired current-height bijections

The finite current-height bijections for the wired square are combinatorial and do not depend on
the Villain Gaussian edge factor. This module records their factorized-weight form, including the
one-unit source ray. It is an internal reusable identity; the free-boundary plane-rotator Fourier
current still needs its own boundary carrier and cycle-to-face-height correspondence.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Lattice2D

variable {L : ℕ}

/-- A factorized edge weight on an integer current of the wired box. -/
def wiredCurrentFactorWeight (w : ℤ → ℝ) (q : WiredEdge L → ℤ) : ℝ :=
  ∏ e, w (q e)

/-- The corresponding factorized weight of a pinned height on the spin-site box. -/
def pinnedHeightFactorWeight (w : ℤ → ℝ) (m : PinnedDualHeight L) : ℝ :=
  ∏ e, w (dualHeightGradient m.1 e)

/-- Reindexing the wired neutral-current sum by the existing planar current-height bijection
works for every edge factor, with no Gaussian assumption. -/
theorem wiredNeutralFactorWeight_tsum_eq_height_tsum (w : ℤ → ℝ) :
    (∑' q : NeutralWiredCurrent L, wiredCurrentFactorWeight w q.1) =
      ∑' m : PinnedDualHeight L, pinnedHeightFactorWeight w m := by
  classical
  let e := neutralCurrentHeightEquiv (L := L)
  calc
    (∑' q : NeutralWiredCurrent L, wiredCurrentFactorWeight w q.1) =
        ∑' m : PinnedDualHeight L, wiredCurrentFactorWeight w (e m).1 :=
      (Equiv.tsum_eq e
        (fun q : NeutralWiredCurrent L => wiredCurrentFactorWeight w q.1)).symm
    _ = ∑' m : PinnedDualHeight L, pinnedHeightFactorWeight w m := by
      apply tsum_congr
      intro m
      simp [wiredCurrentFactorWeight, pinnedHeightFactorWeight, e,
        neutralCurrentHeightEquiv, neutralHeightCurrentMap]

/-- The corresponding factorized weight of a pinned height with the fixed unit ray added. -/
def markedHeightFactorWeight (w : ℤ → ℝ) (site : SquareFreeVertex L)
    (m : PinnedDualHeight L) : ℝ :=
  ∏ e, w (unitSourceHeightCurrent site m.1 e)

/-- Negation is an involution on heights pinned at the lower-left dual face. -/
def pinnedHeightNegEquiv : PinnedDualHeight L ≃ PinnedDualHeight L where
  toFun m := ⟨fun p => -m.1 p, by
    simp [dualBoxRoot, m.2]⟩
  invFun m := ⟨fun p => -m.1 p, by
    simp [dualBoxRoot, m.2]⟩
  left_inv := by
    intro m
    apply Subtype.ext
    funext p
    simp
  right_inv := by
    intro m
    apply Subtype.ext
    funext p
    simp

/-- Reindexing the wired unit-source current sum gives the height sum with the fixed ray crossing
the source-to-boundary path. The sign is the one in FS81's marked edge coefficient after negating
the auxiliary height convention. -/
theorem wiredSourceFactorWeight_tsum_eq_markedHeight_tsum (w : ℤ → ℝ)
    (site : SquareFreeVertex L) :
    (∑' q : SourceWiredCurrent L site, wiredCurrentFactorWeight w q.1) =
      ∑' m : PinnedDualHeight L, markedHeightFactorWeight w site m := by
  classical
  let e := sourceCurrentHeightEquiv (L := L) site
  let n := pinnedHeightNegEquiv (L := L)
  calc
    (∑' q : SourceWiredCurrent L site, wiredCurrentFactorWeight w q.1) =
        ∑' m : PinnedDualHeight L, wiredCurrentFactorWeight w (e m).1 :=
      (Equiv.tsum_eq e
        (fun q : SourceWiredCurrent L site => wiredCurrentFactorWeight w q.1)).symm
    _ = ∑' m : PinnedDualHeight L,
          ∏ edge, w (unitSourceHeightCurrent site (n m).1 edge) := by
      apply tsum_congr
      intro m
      change (∏ edge, w (unitSourceKPHeightCurrent site m.1 edge)) = _
      apply Finset.prod_congr rfl
      intro edge hedge
      change w (unitSourceRay site edge -
          (m.1 ((dualBoxGraph L).tgt edge) - m.1 ((dualBoxGraph L).src edge))) =
        w (unitSourceRay site edge +
          ((n m).1 ((dualBoxGraph L).tgt edge) -
            (n m).1 ((dualBoxGraph L).src edge)))
      congr 1
      rw [show (n m).1 ((dualBoxGraph L).tgt edge) =
          -m.1 ((dualBoxGraph L).tgt edge) by rfl,
        show (n m).1 ((dualBoxGraph L).src edge) =
          -m.1 ((dualBoxGraph L).src edge) by rfl]
      ring
    _ = ∑' m : PinnedDualHeight L, markedHeightFactorWeight w site m :=
      Equiv.tsum_eq n (fun m => markedHeightFactorWeight w site m)

/-- The ratio of source and neutral current sums is unchanged by the factorized current-height
reindexing. This is the algebraic partition-factor normalization step for any weight for which the
denominators are nonzero. -/
theorem wiredCurrentRatio_eq_heightRatio (w : ℤ → ℝ)
    (hZ : ∑' q : NeutralWiredCurrent L, wiredCurrentFactorWeight w q.1 ≠ 0)
    (site : SquareFreeVertex L) :
    (∑' q : SourceWiredCurrent L site, wiredCurrentFactorWeight w q.1) /
        (∑' q : NeutralWiredCurrent L, wiredCurrentFactorWeight w q.1) =
      (∑' m : PinnedDualHeight L, markedHeightFactorWeight w site m) /
        (∑' m : PinnedDualHeight L, pinnedHeightFactorWeight w m) ∧
      (∑' m : PinnedDualHeight L, pinnedHeightFactorWeight w m) ≠ 0 := by
  constructor
  · rw [wiredSourceFactorWeight_tsum_eq_markedHeight_tsum,
      wiredNeutralFactorWeight_tsum_eq_height_tsum]
  · rw [← wiredNeutralFactorWeight_tsum_eq_height_tsum]
    exact hZ

end FroehlichSpencer.BKT.Rotator

end
