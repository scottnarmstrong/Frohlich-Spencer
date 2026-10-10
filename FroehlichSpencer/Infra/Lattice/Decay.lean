/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Lattice.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential sums on the integer lattice

This module proves summability and an exponential tail estimate for polynomially
weighted Euclidean exponentials on `ℤ^ν`.

The estimates are motivated by the
lattice-point annulus estimate in Fröhlich–Spencer (1983), equation (1.26),
transcribed in Fröhlich–Spencer (1983).
-/

@[expose] public section

namespace FroehlichSpencer.Infra.Lattice

private theorem summable_exp_neg_abs_int (c : ℝ) (hc : 0 < c) :
    Summable (fun z : ℤ => Real.exp (-c * |(z : ℝ)|)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · convert (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hc)) using 1
    ext n
    simp [abs_of_nonneg]
    ring
  · convert (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hc)) using 1
    ext n
    simp [abs_of_nonneg]
    ring

private theorem summable_exp_neg_sum_abs (ν : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun x : Fin ν → ℤ =>
      Real.exp (-c * ∑ i, |(x i : ℝ)|)) := by
  induction ν with
  | zero =>
      exact .of_finite
  | succ n ih =>
      let g : (ℤ × (Fin n → ℤ)) → ℝ := fun p =>
        Real.exp (-c * (|(p.1 : ℝ)| + ∑ i, |(p.2 i : ℝ)|))
      let e : (Fin (n + 1) → ℤ) ≃ ℤ × (Fin n → ℤ) := {
        toFun := fun x => (x 0, fun i => x i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := by
          intro x
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        right_inv := by
          intro p
          rcases p with ⟨z, x⟩
          apply Prod.ext
          · rfl
          · funext i
            rfl
      }
      have hg : Summable g := by
        apply (summable_prod_of_nonneg (f := g) (fun p => Real.exp_nonneg _)).2
        constructor
        · intro z
          have h := ih
          apply (h.mul_left (Real.exp (-c * |(z : ℝ)|))).congr
          intro x
          simp [g, Real.exp_add, mul_add]
        · let T : ℝ := ∑' x : Fin n → ℤ,
              Real.exp (-c * ∑ i, |(x i : ℝ)|)
          have hT (z : ℤ) : (∑' x : Fin n → ℤ, g (z, x)) =
              Real.exp (-c * |(z : ℝ)|) * T := by
            calc
              (∑' x : Fin n → ℤ, g (z, x)) =
                  ∑' x : Fin n → ℤ,
                    Real.exp (-c * |(z : ℝ)|) *
                      Real.exp (-c * ∑ i, |(x i : ℝ)|) := by
                apply tsum_congr
                intro x
                simp [g, Real.exp_add, mul_add]
              _ = Real.exp (-c * |(z : ℝ)|) * T := by
                rw [tsum_mul_left]
          have hsum : (fun z : ℤ => ∑' x : Fin n → ℤ, g (z, x)) =
              fun z : ℤ => Real.exp (-c * |(z : ℝ)|) * T := by
            funext z
            exact hT z
          rw [hsum]
          exact (summable_exp_neg_abs_int c hc).mul_right T
      have hpi : Summable (fun x : Fin (n + 1) → ℤ => g (e x)) :=
        (e.summable_iff (f := g)).2 hg
      simpa [g, e, Fin.sum_univ_succ, Real.exp_add, mul_add, add_comm,
        add_left_comm, add_assoc] using hpi

/-- Exponential decay in the Euclidean norm is summable on every integer lattice. -/
theorem summable_exp_neg_norm_latticeCast {ν : ℕ} {c : ℝ} (hc : 0 < c) :
    Summable (fun x : Fin ν → ℤ => Real.exp (-c * ‖latticeCast x‖)) := by
  by_cases hν : ν = 0
  · subst ν
    exact .of_finite
  · have hνpos : 0 < ν := Nat.pos_of_ne_zero hν
    let c' : ℝ := c / (ν : ℝ)
    have hc' : 0 < c' := by
      dsimp [c']
      positivity
    apply (summable_exp_neg_sum_abs ν c' hc').of_nonneg_of_le
      (fun _ => Real.exp_nonneg _)
    intro x
    have hsum : (∑ i : Fin ν, |(x i : ℝ)|) ≤
        (ν : ℝ) * ‖latticeCast x‖ := by
      calc
        (∑ i : Fin ν, |(x i : ℝ)|) ≤ ∑ _i : Fin ν, ‖latticeCast x‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact abs_latticeCast_apply_le_norm x i
        _ = (ν : ℝ) * ‖latticeCast x‖ := by simp [Finset.sum_const, nsmul_eq_mul]
    have hmul := mul_le_mul_of_nonneg_left hsum (div_nonneg hc.le (Nat.cast_nonneg ν))
    have hdiv : c / (ν : ℝ) * (ν : ℝ) = c := div_mul_cancel₀ c (by exact_mod_cast hνpos.ne')
    have hmul' : c' * (∑ i : Fin ν, |(x i : ℝ)|) ≤ c * ‖latticeCast x‖ := by
      calc
        c' * (∑ i : Fin ν, |(x i : ℝ)|) ≤ c' * ((ν : ℝ) * ‖latticeCast x‖) := by
          simpa [c'] using hmul
        _ = c * ‖latticeCast x‖ := by
          dsimp [c']
          rw [← mul_assoc, hdiv]
    simpa only [neg_mul] using Real.exp_le_exp.mpr (neg_le_neg hmul')

/-- A polynomial times a negative exponential is bounded by a constant. -/
theorem pow_mul_exp_neg_le_const {a : ℕ} {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    t ^ a * Real.exp (-r * t) ≤ ((a : ℝ) / r) ^ a * Real.exp (-(a : ℝ)) := by
  by_cases ha : a = 0
  · subst a
    simpa using Real.exp_le_one_iff.mpr (show -r * t ≤ 0 by simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hr.le ht))
  · have hapos : 0 < (a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
    let y : ℝ := r * t / a
    have hy : 0 ≤ y := by dsimp [y]; positivity
    have hrel : (a : ℝ) / r * y = t := by
      dsimp [y]
      field_simp
    have hpow := pow_le_pow_left₀
      (mul_nonneg hy (Real.exp_nonneg _)) (Real.mul_exp_neg_le_exp_neg_one y) a
    have hpow' : y ^ a * Real.exp (-r * t) ≤ Real.exp (-(a : ℝ)) := by
      calc
        y ^ a * Real.exp (-r * t) = (y * Real.exp (-y)) ^ a := by
          rw [mul_pow]
          congr 1
          rw [← Real.exp_nat_mul]
          congr 1
          dsimp [y]
          field_simp
        _ ≤ Real.exp (-1) ^ a := hpow
        _ = Real.exp (-(a : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          simp
    calc
      t ^ a * Real.exp (-r * t) = ((a : ℝ) / r) ^ a *
          (y ^ a * Real.exp (-r * t)) := by
        rw [← hrel, mul_pow]
        ring
      _ ≤ ((a : ℝ) / r) ^ a * Real.exp (-(a : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hpow' (pow_nonneg (div_nonneg (Nat.cast_nonneg a) hr.le) _)

/-- Polynomially weighted exponential decay is summable on the integer lattice. -/
theorem summable_norm_pow_mul_exp_neg {ν a : ℕ} {m : ℝ} (hm : 0 < m) :
    Summable (fun x : Fin ν → ℤ =>
      ‖latticeCast x‖ ^ a * Real.exp (-m * ‖latticeCast x‖)) := by
  have hbase := summable_exp_neg_norm_latticeCast (ν := ν) (c := 3 * m / 4) (by positivity)
  let C : ℝ := ((a : ℝ) / (m / 4)) ^ a * Real.exp (-(a : ℝ))
  have hdom : Summable (fun x : Fin ν → ℤ =>
      C * Real.exp (-(3 * m / 4) * ‖latticeCast x‖)) := hbase.mul_left C
  apply Summable.of_nonneg_of_le
    (f := fun x : Fin ν → ℤ =>
      C * Real.exp (-(3 * m / 4) * ‖latticeCast x‖))
    (g := fun x => ‖latticeCast x‖ ^ a * Real.exp (-m * ‖latticeCast x‖))
  · intro x
    positivity
  · intro x
    have hbound := pow_mul_exp_neg_le_const (a := a) (r := m / 4)
      (by positivity) (norm_nonneg (latticeCast x))
    have hfactor : Real.exp (-m * ‖latticeCast x‖) =
        Real.exp (-(m / 4) * ‖latticeCast x‖) *
          Real.exp (-(3 * m / 4) * ‖latticeCast x‖) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfactor]
    calc
      ‖latticeCast x‖ ^ a *
          (Real.exp (-(m / 4) * ‖latticeCast x‖) *
            Real.exp (-(3 * m / 4) * ‖latticeCast x‖)) =
          (‖latticeCast x‖ ^ a * Real.exp (-(m / 4) * ‖latticeCast x‖)) *
            Real.exp (-(3 * m / 4) * ‖latticeCast x‖) := by ring
      _ ≤ C * Real.exp (-(3 * m / 4) * ‖latticeCast x‖) := by
        exact mul_le_mul_of_nonneg_right hbound (Real.exp_nonneg _)
  · exact hdom

/-- The polynomially weighted exponential tail decays at rate `m / 2` with a
constant depending only on the dimension, polynomial degree, and `m`. -/
theorem exists_norm_pow_exp_neg_tail_bound {ν a : ℕ} {m : ℝ} (hm : 0 < m) :
    ∃ K : ℝ, ∀ R : ℝ,
      ∑' x : Fin ν → ℤ,
        (if R ≤ ‖latticeCast x‖ then
          ‖latticeCast x‖ ^ a * Real.exp (-m * ‖latticeCast x‖) else 0) ≤
        K * Real.exp (-(m / 2) * R) := by
  let C : ℝ := ((a : ℝ) / (m / 4)) ^ a * Real.exp (-(a : ℝ))
  let K : ℝ := C * ∑' x : Fin ν → ℤ, Real.exp (-(m / 4) * ‖latticeCast x‖)
  have hbase := summable_exp_neg_norm_latticeCast (ν := ν) (c := m / 4) (by positivity)
  refine ⟨K, fun R => ?_⟩
  have hmajor : ∀ x : Fin ν → ℤ,
      (if R ≤ ‖latticeCast x‖ then
        ‖latticeCast x‖ ^ a * Real.exp (-m * ‖latticeCast x‖) else 0) ≤
        C * Real.exp (-(m / 2) * R) * Real.exp (-(m / 4) * ‖latticeCast x‖) := by
    intro x
    by_cases hx : R ≤ ‖latticeCast x‖
    · simp only [hx, ite_true]
      have hp := pow_mul_exp_neg_le_const (a := a) (r := m / 4)
        (by positivity) (norm_nonneg (latticeCast x))
      have hfactor : Real.exp (-m * ‖latticeCast x‖) =
          Real.exp (-(m / 4) * ‖latticeCast x‖) *
            (Real.exp (-(m / 2) * ‖latticeCast x‖) *
              Real.exp (-(m / 4) * ‖latticeCast x‖)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hfactor]
      calc
        ‖latticeCast x‖ ^ a *
            (Real.exp (-(m / 4) * ‖latticeCast x‖) *
              (Real.exp (-(m / 2) * ‖latticeCast x‖) *
                Real.exp (-(m / 4) * ‖latticeCast x‖))) =
            (‖latticeCast x‖ ^ a * Real.exp (-(m / 4) * ‖latticeCast x‖)) *
              (Real.exp (-(m / 2) * ‖latticeCast x‖) *
                Real.exp (-(m / 4) * ‖latticeCast x‖)) := by ring
        _ ≤ C * (Real.exp (-(m / 2) * ‖latticeCast x‖) *
              Real.exp (-(m / 4) * ‖latticeCast x‖)) := by
          exact mul_le_mul_of_nonneg_right hp (by positivity)
        _ ≤ C * (Real.exp (-(m / 2) * R) *
              Real.exp (-(m / 4) * ‖latticeCast x‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C)
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg (by positivity : 0 ≤ m / 2)
            (sub_nonneg.mpr hx)]
        _ = _ := by ring
    · simp only [hx, ite_false, C]
      positivity
  have hright : Summable (fun x : Fin ν → ℤ =>
      C * Real.exp (-(m / 2) * R) * Real.exp (-(m / 4) * ‖latticeCast x‖)) := by
    convert hbase.mul_left (C * Real.exp (-(m / 2) * R)) using 1
  have hleft : Summable (fun x : Fin ν → ℤ =>
      if R ≤ ‖latticeCast x‖ then
        ‖latticeCast x‖ ^ a * Real.exp (-m * ‖latticeCast x‖) else 0) := by
    apply Summable.of_nonneg_of_le
      (f := fun x : Fin ν → ℤ =>
        C * Real.exp (-(m / 2) * R) * Real.exp (-(m / 4) * ‖latticeCast x‖))
      (g := fun x => if R ≤ ‖latticeCast x‖ then
        ‖latticeCast x‖ ^ a * Real.exp (-m * ‖latticeCast x‖) else 0)
    · intro x
      split_ifs <;> positivity
    · exact hmajor
    · exact hright
  calc
    _ ≤ ∑' x : Fin ν → ℤ,
        C * Real.exp (-(m / 2) * R) * Real.exp (-(m / 4) * ‖latticeCast x‖) :=
      Summable.tsum_le_tsum hmajor hleft hright
    _ = K * Real.exp (-(m / 2) * R) := by
      simp only [K, tsum_mul_left]
      ring

end FroehlichSpencer.Infra.Lattice

end
