/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.TwoPoint
public import FroehlichSpencer.BKT.Clock.Peierls.EnergyGap
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Pointwise clock-weight comparison after removing a contour

When the removed configuration is constant across the selected bonds, the original configuration
has a nontrivial clock difference there, and the two difference fields agree off those bonds, the
clock-box weight loses at least one local energy gap per selected bond.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Rotator

/-- The oriented `ZMod n` difference of the endpoint spins on an internal clock bond. -/
def clockEdgeDifference {L n : ℕ} (σ : RotatorSpinSite L → Fin n)
    (e : RotatorInternalBond L) : ZMod n :=
  (σ ((rotatorFreeGraph L).src e)).val - (σ ((rotatorFreeGraph L).tgt e)).val

/-- Equal `ZMod n` differences give the same real clock-bond cosine. -/
theorem clockAngles_cos_eq_of_zmodDifference_eq {n : ℕ} (hn : 0 < n)
    (a b c d : Fin n)
    (hdiff : (a.val : ZMod n) - (b.val : ZMod n) =
      (c.val : ZMod n) - (d.val : ZMod n)) :
    Real.cos (2 * Real.pi * ((a : ℝ) - (b : ℝ)) / (n : ℝ)) =
      Real.cos (2 * Real.pi * ((c : ℝ) - (d : ℝ)) / (n : ℝ)) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hmod : (((a.val : ℤ) - (b.val : ℤ)) : ZMod n) =
      (((c.val : ℤ) - (d.val : ℤ)) : ZMod n) := by
    calc
      (((a.val : ℤ) - (b.val : ℤ)) : ZMod n) =
          (a.val : ZMod n) - (b.val : ZMod n) := by simp
      _ = (c.val : ZMod n) - (d.val : ZMod n) := hdiff
      _ = (((c.val : ℤ) - (d.val : ℤ)) : ZMod n) := by simp
  have hmod' := hmod
  rw [← Int.cast_sub, ← Int.cast_sub] at hmod'
  have hcong : (a.val : ℤ) - (b.val : ℤ) ≡
      (c.val : ℤ) - (d.val : ℤ) [ZMOD n] :=
    (ZMod.intCast_eq_intCast_iff _ _ n).mp hmod'
  obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp hcong.symm
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hfinCast (x y : Fin n) :
      (x : ℝ) - (y : ℝ) = (((x.val : ℤ) - (y.val : ℤ)) : ℝ) := by
    push_cast
    ring
  have hkR : (((a.val : ℤ) - (b.val : ℤ)) : ℝ) =
      (((c.val : ℤ) - (d.val : ℤ)) : ℝ) + (n : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  have hphase :
      2 * Real.pi * ((a : ℝ) - (b : ℝ)) / (n : ℝ) =
        2 * Real.pi * ((c : ℝ) - (d : ℝ)) / (n : ℝ) + (k : ℝ) * (2 * Real.pi) := by
    rw [hfinCast a b, hfinCast c d, hkR]
    field_simp [hnreal]
  rw [hphase, Real.cos_add_int_mul_two_pi]

/-- A removed clock configuration has equal spins across every selected bond; the original has
distinct spins there; and their `ZMod n` edge differences agree outside the selected set. The
original finite-box weight is then bounded by the removed weight times one Peierls factor per
selected bond. -/
theorem clockBoxWeight_le_of_contour_removal
    (n L : ℕ) (hn : 2 ≤ n) (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (RotatorInternalBond L))
    (σ σ' : RotatorSpinSite L → Fin n)
    (hσ_bad : ∀ e ∈ S,
      σ ((rotatorFreeGraph L).src e) ≠ σ ((rotatorFreeGraph L).tgt e))
    (hσ'_equal : ∀ e ∈ S,
      σ' ((rotatorFreeGraph L).src e) = σ' ((rotatorFreeGraph L).tgt e))
    (hoff : ∀ e, e ∉ S → clockEdgeDifference σ e = clockEdgeDifference σ' e) :
    clockBoxWeight n L β σ ≤
      Real.exp (-(β * clockEnergyGap n) * (S.card : ℝ)) * clockBoxWeight n L β σ' := by
  have hnpos : 0 < n := by omega
  have hterm (e : RotatorInternalBond L) :
      β * Real.cos
          (clockAngles n σ ((rotatorFreeGraph L).src e) -
            clockAngles n σ ((rotatorFreeGraph L).tgt e)) ≤
        β * Real.cos
          (clockAngles n σ' ((rotatorFreeGraph L).src e) -
            clockAngles n σ' ((rotatorFreeGraph L).tgt e)) +
          (if e ∈ S then -(β * clockEnergyGap n) else 0) := by
    by_cases heS : e ∈ S
    · have hcos := clockAngles_cos_bond_le hn σ
        ((rotatorFreeGraph L).src e) ((rotatorFreeGraph L).tgt e) (hσ_bad e heS)
      have hmul := mul_le_mul_of_nonneg_left hcos hβ
      have hangle' : clockAngles n σ' ((rotatorFreeGraph L).src e) -
          clockAngles n σ' ((rotatorFreeGraph L).tgt e) = 0 := by
        unfold clockAngles
        rw [hσ'_equal e heS]
        ring
      simp only [heS, ↓reduceIte]
      rw [hangle']
      calc
        β * Real.cos
            (clockAngles n σ ((rotatorFreeGraph L).src e) -
              clockAngles n σ ((rotatorFreeGraph L).tgt e)) ≤
            β * Real.cos (2 * Real.pi / (n : ℝ)) := hmul
        _ = β * Real.cos 0 + -(β * clockEnergyGap n) := by
          rw [Real.cos_zero]
          unfold clockEnergyGap
          ring
    · have hcos := clockAngles_cos_eq_of_zmodDifference_eq hnpos
        (σ ((rotatorFreeGraph L).src e)) (σ ((rotatorFreeGraph L).tgt e))
        (σ' ((rotatorFreeGraph L).src e)) (σ' ((rotatorFreeGraph L).tgt e)) (hoff e heS)
      have hangle : clockAngles n σ ((rotatorFreeGraph L).src e) -
          clockAngles n σ ((rotatorFreeGraph L).tgt e) =
          2 * Real.pi * ((σ ((rotatorFreeGraph L).src e) : ℝ) -
            (σ ((rotatorFreeGraph L).tgt e) : ℝ)) / (n : ℝ) := by
        unfold clockAngles
        ring
      have hangle' : clockAngles n σ' ((rotatorFreeGraph L).src e) -
          clockAngles n σ' ((rotatorFreeGraph L).tgt e) =
          2 * Real.pi * ((σ' ((rotatorFreeGraph L).src e) : ℝ) -
            (σ' ((rotatorFreeGraph L).tgt e) : ℝ)) / (n : ℝ) := by
        unfold clockAngles
        ring
      simp only [heS, ↓reduceIte]
      rw [hangle, hangle', hcos]
      simp
  have henergy :
      (∑ e : RotatorInternalBond L,
        β * Real.cos (clockAngles n σ ((rotatorFreeGraph L).src e) -
          clockAngles n σ ((rotatorFreeGraph L).tgt e))) ≤
        (∑ e : RotatorInternalBond L,
          β * Real.cos (clockAngles n σ' ((rotatorFreeGraph L).src e) -
            clockAngles n σ' ((rotatorFreeGraph L).tgt e))) -
          (β * clockEnergyGap n) * (S.card : ℝ) := by
    have hcorrection :
        (∑ e : RotatorInternalBond L,
          if e ∈ S then -(β * clockEnergyGap n) else 0) =
          -(β * clockEnergyGap n) * (S.card : ℝ) := by
      rw [Finset.sum_ite_mem]
      simp [mul_comm]
    calc
      _ ≤ ∑ e : RotatorInternalBond L,
          (β * Real.cos (clockAngles n σ' ((rotatorFreeGraph L).src e) -
            clockAngles n σ' ((rotatorFreeGraph L).tgt e)) +
            if e ∈ S then -(β * clockEnergyGap n) else 0) := by
              exact Finset.sum_le_sum fun e _ => hterm e
      _ = _ := by rw [Finset.sum_add_distrib, hcorrection]; ring
  unfold clockBoxWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [henergy]

end FroehlichSpencer.BKT.Clock.Peierls

end
