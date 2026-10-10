module

public import FroehlichSpencer.FS82.Poisson.GaussianSummable
import Mathlib.Tactic.Ring

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open Complex Matrix

private theorem symmetric_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : B.IsHermitian) (i j : ι) : B i j = B j i := by
  have heq := congrArg (fun M : Matrix ι ι ℝ => M i j) hB.eq
  simpa [Matrix.conjTranspose_apply] using heq.symm

private theorem cross_swap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.IsHermitian) (w : ι → ℂ) (k : ι → ℤ) :
    (∑ i, ∑ j, w i * (B i j : ℂ) * (k j : ℂ)) =
      ∑ i, (∑ j, (B i j : ℂ) * w j) * (k i : ℂ) := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, ∑ j, w j * (B j i : ℂ) * (k i : ℂ) := rfl
    _ = ∑ i, ∑ j, (B i j : ℂ) * w j * (k i : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [symmetric_entry hB]
      ring
    _ = _ := by simp [Finset.sum_mul, mul_assoc]

private theorem expand_shifted_quadratic {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (w : ι → ℂ) (k : ι → ℤ) :
    (∑ i, ∑ j, (w i - I * (k i : ℂ)) * (B i j : ℂ) * (w j - I * (k j : ℂ))) =
      (∑ i, ∑ j, w i * (B i j : ℂ) * w j) -
      I * (∑ i, ∑ j, (k i : ℂ) * (B i j : ℂ) * w j) -
      I * (∑ i, ∑ j, w i * (B i j : ℂ) * (k j : ℂ)) -
      (∑ i, ∑ j, (k i : ℂ) * (B i j : ℂ) * (k j : ℂ)) := by
  have hterm (i j : ι) :
      (w i - I * (k i : ℂ)) * (B i j : ℂ) * (w j - I * (k j : ℂ)) =
      w i * (B i j : ℂ) * w j - I * ((k i : ℂ) * (B i j : ℂ) * w j) -
      I * (w i * (B i j : ℂ) * (k j : ℂ)) -
      (k i : ℂ) * (B i j : ℂ) * (k j : ℂ) := by
    ring_nf
    simp [Complex.I_sq]
    ring
  simp_rw [hterm]
  simp [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem dual_exponent_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.IsHermitian) (w : ι → ℂ) (k : ι → ℤ) :
    (Real.pi : ℂ) * (∑ i, ∑ j,
      (w i - I * (k i : ℂ)) * (B i j : ℂ) * (w j - I * (k j : ℂ))) =
    (Real.pi : ℂ) * (∑ i, ∑ j, w i * (B i j : ℂ) * w j) -
      (Real.pi : ℂ) * (∑ i, ∑ j, (k i : ℂ) * (B i j : ℂ) * (k j : ℂ)) +
      2 * Real.pi * ∑ i, (-I * ∑ j, (B i j : ℂ) * w j) * (k i : ℂ) := by
  rw [expand_shifted_quadratic]
  rw [cross_swap B hB w k]
  have hlin :
      ∑ i, (-I * ∑ j, (B i j : ℂ) * w j) * (k i : ℂ) =
        -I * ∑ i, (∑ j, (B i j : ℂ) * w j) * (k i : ℂ) := by
    calc
      _ = ∑ i, (-I) * ((∑ j, (B i j : ℂ) * w j) * (k i : ℂ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hc2 :
      ∑ i, ∑ j, (k i : ℂ) * (B i j : ℂ) * w j =
        ∑ i, (∑ j, (B i j : ℂ) * w j) * (k i : ℂ) := by
    calc
      _ = ∑ i, (k i : ℂ) * ∑ j, (B i j : ℂ) * w j := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∑ j, (k i : ℂ) * ((B i j : ℂ) * w j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = _ := by rw [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hlin]
  rw [hc2]
  ring

theorem summable_dual_tilted_gaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (w : ι → ℂ) :
    Summable (fun k : ι → ℤ => cexp ((Real.pi : ℂ) * ∑ i, ∑ j,
      (w i - I * (k i : ℂ)) * ((A⁻¹ i j : ℝ) : ℂ) * (w j - I * (k j : ℂ)))) := by
  let B : Matrix ι ι ℝ := A⁻¹
  have hB : B.PosDef := by simpa [B] using hA.inv
  let w' : ι → ℂ := fun i => -I * ∑ j, (B i j : ℂ) * w j
  let c : ℂ := (Real.pi : ℂ) * ∑ i, ∑ j, w i * (B i j : ℂ) * w j
  have hs := summable_tilted_gaussian B hB w'
  have heq (k : ι → ℤ) :
      (Real.pi : ℂ) * (∑ i, ∑ j,
        (w i - I * (k i : ℂ)) * (B i j : ℂ) * (w j - I * (k j : ℂ))) =
      c + (-(Real.pi : ℂ) * ∑ i, ∑ j, (k i : ℂ) * (B i j : ℂ) * (k j : ℂ) +
        2 * Real.pi * ∑ i, w' i * (k i : ℂ)) := by
    rw [dual_exponent_expand B hB.isHermitian w k]
    simp only [c, w']
    ring
  have hterm (k : ι → ℤ) :
      cexp ((Real.pi : ℂ) * ∑ i, ∑ j,
        (w i - I * (k i : ℂ)) * (B i j : ℂ) * (w j - I * (k j : ℂ))) =
      cexp c * cexp (-(Real.pi : ℂ) * ∑ i, ∑ j, (k i : ℂ) * (B i j : ℂ) * (k j : ℂ) +
        2 * Real.pi * ∑ i, w' i * (k i : ℂ)) := by
    rw [heq, Complex.exp_add]
  have hmul := hs.mul_left (cexp c)
  exact hmul.congr fun k => (hterm k).symm

end FroehlichSpencer.FS82.Poisson
