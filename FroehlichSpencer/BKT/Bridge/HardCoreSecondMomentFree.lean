/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.CoulombPotential
public import FroehlichSpencer.BKT.Surface.HardCoreSecondMomentSpec
public import FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment
public import FroehlichSpencer.BKT.Coulomb.ThermodynamicLimit
import Mathlib.Tactic

/-!
By the characterization `hardCoreSecondMoment_spec` and the periodic limit of
`Bridge/HardCoreSecondMoment.lean`, the `hardCoreSecondMoment` is 's
`freeSecondMomentInternal` (`hardCoreSecondMoment_eq_free`); the quadratic form of the
`coulombPotential` is 's `freeQuadInternal` (`quad_eq_freeQuad`).

With 's
`free_secondMoment_lower_bound` and `free_thermodynamic_limit_exists` these lemmas prove the two
Theorem A roots (providers in `BKT/Provider/`).
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment

theorem hardCoreSecondMoment_eq_free (β : ℝ) (hβ : 0 < β) (z : ℝ) (hz : 0 ≤ z)
    (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (hg : (g.sum fun _ a => a) = 0) :
    hardCoreSecondMoment β hβ z hz Λ g hgΛ hg =
      freeSecondMomentInternal (Subtype.val : Λ → ℤ × ℤ) β z (fun v => g v) :=
  ((hardCoreSecondMoment_spec β hβ z hz Λ g hgΛ hg _).mp
    (tendsto_periodicHardCoreSecondMoment β hβ z hz Λ g hgΛ hg)).symm

theorem quad_eq_freeQuad (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ) :
    (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) =
      freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) := by
  have hin : ∀ x a, (g.sum fun y b => a * b * coulombPotential (x - y)) =
      ∑ y ∈ Λ, a * g y * coulombPotential (x - y) := fun x a =>
    Finsupp.sum_of_support_subset g hgΛ _ fun y _ => by simp
  rw [Finsupp.sum_of_support_subset g hgΛ _ fun x _ => by simp]
  simp only [hin]
  unfold freeQuadInternal
  rw [sum_mul_neg_freePotentialOp, ← Finset.sum_coe_sort Λ]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_coe_sort Λ, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  show g u * g v * -(Coulomb.potentialKernelInternal (u.1 - v.1)) = _
  ring

theorem sum_region_eq_zero (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (hg : (g.sum fun _ a => a) = 0) : ∑ v : Λ, g v = 0 := by
  have := finsupp_sum_eq_sum_region Λ g hgΛ (fun _ => 1)
  simp only [mul_one] at this
  rw [← this]; exact hg

theorem subset_box (S : Finset (ℤ × ℤ)) :
    S ⊆ boxInternal (S.sup fun x => max x.1.natAbs x.2.natAbs) := by
  intro x hx
  have h := Finset.le_sup (f := fun x : ℤ × ℤ => max x.1.natAbs x.2.natAbs) hx
  rw [mem_box_iff, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have h1 : x.1.natAbs ≤ S.sup fun x => max x.1.natAbs x.2.natAbs := (le_max_left _ _).trans h
  have h2 : x.2.natAbs ≤ S.sup fun x => max x.1.natAbs x.2.natAbs := (le_max_right _ _).trans h
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree

end
