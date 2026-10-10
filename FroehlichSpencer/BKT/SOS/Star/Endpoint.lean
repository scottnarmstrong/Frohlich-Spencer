/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite-shell SOS endpoint summation

This is the quantitative endpoint summation used in the SOS repair. It keeps the scale sum in
the contour profile: the endpoint difference is bounded by profileCoeff times T times area(rho),
and the area square is absorbed by half of the area activity exponent. shellMajorant is the
finite-volume packing input; it is stated independently of the endpoint sum using FS81's selected-square separation.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Star

open Finset
open Filter
open scoped Topology

/-- Absorb the squared multiscale profile size into half of its activity-area exponent. -/
theorem scaled_area_sq_exp_le {T r A : ℝ} (hT : 0 < T) (hr : 0 < r) (hA : 0 ≤ A) :
    (T * A) ^ 2 * Real.exp (-(r * T * A) / 2) ≤ 16 / r ^ 2 := by
  let y : ℝ := r * T * A / 4
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hyExp : y ≤ Real.exp y := by
    have h := Real.add_one_le_exp y
    linarith
  have hySq : y ^ 2 ≤ Real.exp (2 * y) := by
    calc
      y ^ 2 ≤ Real.exp y * Real.exp y := by
        simpa [pow_two] using
          (mul_le_mul hyExp hyExp (by positivity) (by positivity))
      _ = Real.exp (2 * y) := by rw [← Real.exp_add]; ring_nf
  have hcancel : Real.exp (2 * y) * Real.exp (-2 * y) = 1 := by
    rw [← Real.exp_add]
    simp
  have hscaled : (T * A) ^ 2 * Real.exp (-(r * T * A) / 2) =
      (16 / r ^ 2) * (y ^ 2 * Real.exp (-2 * y)) := by
    dsimp [y]
    have hr0 : r ≠ 0 := ne_of_gt hr
    field_simp [hr0]
    ring_nf
  rw [hscaled]
  have hcore : y ^ 2 * Real.exp (-2 * y) ≤ 1 := by
    calc
      y ^ 2 * Real.exp (-2 * y) ≤
          Real.exp (2 * y) * Real.exp (-2 * y) :=
        mul_le_mul_of_nonneg_right hySq (Real.exp_nonneg _)
      _ = 1 := hcancel
  exact mul_le_of_le_one_right (by positivity) hcore

/-- A finite shell family with activity damping in charge mass and area has a small endpoint
second moment. The shell-majorant bound is the only combinatorial input. -/
theorem endpoint_secondMoment_le_of_shellMajorant
    {ι : Type*} [DecidableEq ι] (N : Finset ι) (hit : ι → Prop) [DecidablePred hit]
    (z mass area profileCoeff : ι → ℝ) (shell : ι → ℕ)
    (T r b C K : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hb : 0 < b) (hK : 0 ≤ K)
    (hrate : ∀ ρ ∈ N, hit ρ → |z ρ| ≤ Real.exp (-(r * T * (mass ρ + area ρ))))
    (hmass : ∀ ρ ∈ N, hit ρ → 2 ≤ mass ρ)
    (harea : ∀ ρ ∈ N, hit ρ → b * (shell ρ : ℝ) ≤ area ρ)
    (hprofile : ∀ ρ ∈ N, hit ρ → |profileCoeff ρ| ≤ C * T * area ρ)
    (hshell : ∀ q : ℝ, 0 ≤ q → q < 1 →
      ∑ ρ ∈ N.filter hit, q ^ shell ρ ≤ K / (1 - q))
    (hq : Real.exp (-(r * T * b) / 2) ≤ 1 / 2) :
    ∑ ρ ∈ N.filter hit, |z ρ| * profileCoeff ρ ^ 2 ≤
      (32 * C ^ 2 * K / r ^ 2) * Real.exp (-2 * r * T) := by
  let S := N.filter hit
  let q : ℝ := Real.exp (-(r * T * b) / 2)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    have : q ≤ 1 / 2 := by simpa [q] using hq
    linarith
  have hden : 0 < 1 - q := by linarith
  have hsum : ∑ ρ ∈ S, q ^ shell ρ ≤ K / (1 - q) := by
    simpa [S, q] using hshell q hq0 hq1
  have hterm : ∀ ρ ∈ S,
      |z ρ| * profileCoeff ρ ^ 2 ≤
        (16 * C ^ 2 / r ^ 2) * Real.exp (-2 * r * T) * q ^ shell ρ := by
    intro ρ hρ
    have hρN : ρ ∈ N := (Finset.mem_filter.mp hρ).1
    have hρhit : hit ρ := (Finset.mem_filter.mp hρ).2
    have hmassρ := hmass ρ hρN hρhit
    have hareaρ := harea ρ hρN hρhit
    have hprofileρ := hprofile ρ hρN hρhit
    have hrateρ := hrate ρ hρN hρhit
    have hprofileSq : profileCoeff ρ ^ 2 ≤ (C * T * area ρ) ^ 2 := by
      have habs := abs_le.mp hprofileρ
      exact sq_le_sq' habs.1 habs.2
    have hA0 : 0 ≤ area ρ := le_trans (by positivity) hareaρ
    have hAbsorb := scaled_area_sq_exp_le hT hr hA0
    have hmassExp : Real.exp (-(r * T * mass ρ)) ≤ Real.exp (-2 * r * T) := by
      apply Real.exp_le_exp.mpr
      have hmult := mul_le_mul_of_nonneg_left hmassρ (by positivity : 0 ≤ r * T)
      nlinarith [hmult]
    have hareaExp : Real.exp (-(r * T * area ρ) / 2) ≤ q ^ shell ρ := by
      change Real.exp (-(r * T * area ρ) / 2) ≤
        (Real.exp (-(r * T * b) / 2)) ^ shell ρ
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hareaρ (by positivity : 0 ≤ r * T / 2)
      nlinarith
    have hrateSplit : Real.exp (-(r * T * (mass ρ + area ρ))) =
        Real.exp (-(r * T * mass ρ)) *
          Real.exp (-(r * T * area ρ) / 2) *
            Real.exp (-(r * T * area ρ) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      |z ρ| * profileCoeff ρ ^ 2 ≤
          Real.exp (-(r * T * (mass ρ + area ρ))) * (C * T * area ρ) ^ 2 :=
        mul_le_mul hrateρ hprofileSq (sq_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (-(r * T * mass ρ)) *
          ((C ^ 2) * ((T * area ρ) ^ 2 *
            Real.exp (-(r * T * area ρ) / 2)) *
              Real.exp (-(r * T * area ρ) / 2)) := by
        rw [hrateSplit]
        ring
      _ ≤ Real.exp (-2 * r * T) * (C ^ 2 * (16 / r ^ 2) *
          q ^ shell ρ) := by
        have hconst : 0 ≤ C ^ 2 * (16 / r ^ 2) := by positivity
        have hexp0 : 0 ≤ Real.exp (-(r * T * mass ρ)) := Real.exp_nonneg _
        calc
          _ ≤ Real.exp (-(r * T * mass ρ)) *
              (C ^ 2 * (16 / r ^ 2) *
                Real.exp (-(r * T * area ρ) / 2)) := by
            apply mul_le_mul_of_nonneg_left _ hexp0
            calc
              C ^ 2 * ((T * area ρ) ^ 2 *
                  Real.exp (-(r * T * area ρ) / 2)) *
                  Real.exp (-(r * T * area ρ) / 2)
                  = (C ^ 2 * ((T * area ρ) ^ 2 *
                    Real.exp (-(r * T * area ρ) / 2))) *
                      Real.exp (-(r * T * area ρ) / 2) := by ring
              _ ≤ (C ^ 2 * (16 / r ^ 2)) *
                    Real.exp (-(r * T * area ρ) / 2) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hAbsorb (sq_nonneg C))
                  (Real.exp_nonneg _)
          _ ≤ Real.exp (-2 * r * T) *
              (C ^ 2 * (16 / r ^ 2) * q ^ shell ρ) := by
            apply mul_le_mul
            · exact hmassExp
            · exact mul_le_mul_of_nonneg_left hareaExp hconst
            · positivity
            · positivity
      _ = (16 * C ^ 2 / r ^ 2) * Real.exp (-2 * r * T) * q ^ shell ρ := by ring
  calc
    ∑ ρ ∈ S, |z ρ| * profileCoeff ρ ^ 2 ≤
        ∑ ρ ∈ S, (16 * C ^ 2 / r ^ 2) * Real.exp (-2 * r * T) * q ^ shell ρ :=
      Finset.sum_le_sum hterm
    _ = (16 * C ^ 2 / r ^ 2) * Real.exp (-2 * r * T) *
        ∑ ρ ∈ S, q ^ shell ρ := by rw [Finset.mul_sum]
    _ ≤ (16 * C ^ 2 / r ^ 2) * Real.exp (-2 * r * T) * (K / (1 - q)) := by
      apply mul_le_mul_of_nonneg_left hsum
      positivity
    _ ≤ (32 * C ^ 2 * K / r ^ 2) * Real.exp (-2 * r * T) := by
      have hfactor : 1 / (1 - q) ≤ 2 := by
        apply (div_le_iff₀ hden).2
        have hq' : q ≤ 1 / 2 := by simpa [q] using hq
        linarith
      have hnonneg : 0 ≤ (16 * C ^ 2 / r ^ 2) * Real.exp (-2 * r * T) * K := by
        positivity
      calc
        (16 * C ^ 2 / r ^ 2) * Real.exp (-2 * r * T) * (K / (1 - q))
            = ((16 * C ^ 2 / r ^ 2) * Real.exp (-2 * r * T) * K) *
                (1 / (1 - q)) := by ring
        _ ≤ ((16 * C ^ 2 / r ^ 2) * Real.exp (-2 * r * T) * K) * 2 :=
          mul_le_mul_of_nonneg_left hfactor hnonneg
        _ = (32 * C ^ 2 * K / r ^ 2) * Real.exp (-2 * r * T) := by ring

/-- Exponential damping tends to zero at large SOS scale. -/
theorem sos_star_exponential_tendsto (C η : ℝ) (hη : 0 < η) :
    Tendsto (fun T : ℝ => C * Real.exp (-η * T)) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 η hη
  simpa using h.const_mul C

end FroehlichSpencer.BKT.SOS.Star

end
