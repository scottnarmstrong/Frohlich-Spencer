/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.PeriodicHardCoreSecondMoment
public import FroehlichSpencer.BKT.Coulomb.FreeGas
import Mathlib.Tactic

/-!
The `periodicHardCoreSecondMoment` (FS81 (1.16), (5.2), source) at the
periodic sides `L_n` is 's weighted GFF expectation (`periodicHardCoreSecondMoment_eq`), and it
converges to 's free-boundary second moment (`tendsto_periodicHardCoreSecondMoment`).

With
`prod_hardCoreWeight_nonneg_of_neutral` these lemmas prove the gates `periodicHardCorePartition_pos`
and `existsUnique_tendsto_periodicHardCoreSecondMoment` (providers in `BKT/Provider/`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open Fin.CommRing

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb

/-- The internal reduction modulo `L` is the integer cast into `Fin L`. -/
theorem latticeToSquare_eq (L : ℕ) [NeZero L] (x : ℤ × ℤ) :
    latticeToSquareInternal L x = ((x.1 : Fin L), (x.2 : Fin L)) := by
  simp [latticeToSquareInternal, squareTorusVertexEquiv, torusPointInternal, map_intCast]

/-! ### Positivity of the periodic partition function -/

/-- For a neutral hard-core configuration the activity product is nonnegative. -/
theorem prod_hardCoreWeight_nonneg_of_neutral {V : Type*} [Fintype V] [DecidableEq V] (z : ℝ)
    (q : V → ℤ) (hq : q ∈ chargeConfigsInternal V 1) (hsum : ∑ v, q v = 0) :
    0 ≤ ∏ v, hardCoreWeightInternal z (q v) := by
  have hq' : ∀ v, q v = -1 ∨ q v = 0 ∨ q v = 1 := by
    intro v
    have := Fintype.mem_piFinset.mp hq v
    simp only [Finset.mem_Icc, Nat.cast_one] at this
    omega
  set P := Finset.univ.filter fun v => q v = 1
  set N := Finset.univ.filter fun v => q v = -1
  have hw : ∀ v, hardCoreWeightInternal z (q v) =
      (if v ∈ P then z / 2 else 1) * (if v ∈ N then z / 2 else 1) := by
    intro v
    simp only [P, N, Finset.mem_filter, Finset.mem_univ, true_and, hardCoreWeightInternal]
    rcases hq' v with h | h | h <;> simp [h]
  have hcard : P.card = N.card := by
    have h1 : ∑ v, q v = ∑ v ∈ P, (1 : ℤ) + ∑ v ∈ N, (-1 : ℤ) := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rcases hq' v with h | h | h <;> simp [h]
    rw [hsum] at h1
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, smul_neg] at h1
    omega
  rw [Finset.prod_congr rfl fun v _ => hw v, Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.prod_ite_mem, Finset.univ_inter, Finset.univ_inter, Finset.prod_const,
    Finset.prod_const, hcard, ← mul_pow]
  exact pow_nonneg (mul_self_nonneg _) _

/-! ### The free-boundary limit of the periodic second moments -/

theorem periodicHardCoreSecondMoment_congr (β : ℝ) (hβ : 0 < β) (z : ℝ) (Λ : Finset (ℤ × ℤ))
    (g : ℤ × ℤ →₀ ℝ) {L L' : ℕ} (h : L = L') (hL : 1 < L) (hL' : 1 < L') :
    periodicHardCoreSecondMoment β hβ z Λ g L hL = periodicHardCoreSecondMoment β hβ z Λ g L' hL' := by
  subst h; rfl

theorem finsupp_sum_eq_sum_region (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (F : ℤ × ℤ → ℝ) : (g.sum fun x a => a * F x) = ∑ v : Λ, g v * F v := by
  rw [Finsupp.sum, Finset.sum_coe_sort Λ (fun x => g x * F x)]
  exact Finset.sum_subset hgΛ fun x _ hx => by simp [Finsupp.notMem_support_iff.mp hx]

/-- At a periodic side on which reduction is injective on `Λ`, the periodic second moment is 's
weighted GFF expectation. -/
theorem periodicHardCoreSecondMoment_eq (β : ℝ) (hβ : 0 < β) (z : ℝ) (Λ : Finset (ℤ × ℤ))
    (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ) (n : ℕ)
    (hinj : Function.Injective (torusSiteMapInternal (Subtype.val : Λ → ℤ × ℤ) n)) :
    periodicHardCoreSecondMoment β hβ z Λ g (torusSideInternal n) (one_lt_torusSide n) =
      weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) β⁻¹ (inv_pos.2 hβ) 0
        (torusWeightsInternal (Subtype.val : Λ → ℤ × ℤ) n z)
        (fun φ => (∑ j, φ j * latticePushInternal (torusSideInternal n)
          (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) j) ^ 2) := by
  set L := torusSideInternal n
  have hred : ∀ x : ℤ × ℤ, ((x.1 : Fin L), (x.2 : Fin L)) = latticeToSquareInternal L x :=
    fun x => (latticeToSquare_eq L x).symm
  have hobs : ∀ φ : Fin L × Fin L → ℝ,
      (g.sum fun x a => a * φ ((x.1 : Fin L), (x.2 : Fin L))) =
        ∑ j, φ j * latticePushInternal L (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) j := by
    intro φ
    rw [finsupp_sum_eq_sum_region Λ g hgΛ]
    simp only [hred]
    rw [← sum_latticePush_mul (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) φ]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hprod : ∀ φ : Fin L × Fin L → ℝ,
      ∏ x ∈ Λ, (1 + z * Real.cos (φ ((x.1 : Fin L), (x.2 : Fin L)))) =
        ∏ j, torusWeightsInternal (Subtype.val : Λ → ℤ × ℤ) n z j (φ j) := by
    intro φ
    simp only [torusWeightsInternal, sineGordonWeight_regionHardCore]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_image fun a _ b _ h => hinj h,
      ← Finset.prod_coe_sort Λ]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [hred]
    rfl
  unfold periodicHardCoreSecondMoment periodicHardCorePartition weightedGFFExpectation
    weightedGFFNormalizer
  simp only [hobs, hprod]
  rfl

theorem tendsto_periodicHardCoreSecondMoment (β : ℝ) (hβ : 0 < β) (z : ℝ)
    (hz : 0 ≤ z) (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (hg : (g.sum fun _ a => a) = 0) :
    Tendsto (fun n : ℕ =>
      periodicHardCoreSecondMoment β hβ z Λ g (2 * n + 2) (Nat.one_lt_succ_succ (2 * n)))
      atTop (𝓝 (freeSecondMomentInternal (Subtype.val : Λ → ℤ × ℤ) β z (fun v => g v))) := by
  have hf : ∑ v : Λ, g v = 0 := by
    have := finsupp_sum_eq_sum_region Λ g hgΛ (fun _ => 1)
    simp only [mul_one] at this
    rw [← this]; exact hg
  have hC1b := tendsto_torus_secondMoment (Subtype.val : Λ → ℤ × ℤ) Subtype.val_injective β hβ hz
    (fun v => g v) hf (fun _ => 0)
  set a : ℕ → ℝ := fun n =>
    periodicHardCoreSecondMoment β hβ z Λ g (2 * n + 2) (Nat.one_lt_succ_succ (2 * n)) with ha
  have hshift : Tendsto (fun n : ℕ => a (n + 1))
      atTop (𝓝 (freeSecondMomentInternal (Subtype.val : Λ → ℤ × ℤ) β z (fun v => g v))) := by
    refine hC1b.congr' ?_
    filter_upwards [eventually_injective_latticeToSquare (Subtype.val : Λ → ℤ × ℤ)
      Subtype.val_injective] with n hn
    rw [← periodicHardCoreSecondMoment_eq β hβ z Λ g hgΛ n hn, ha]
    exact periodicHardCoreSecondMoment_congr β hβ z Λ g (by unfold torusSideInternal; ring) _ _
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

end FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment

end
