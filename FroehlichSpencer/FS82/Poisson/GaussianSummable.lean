module

public import FroehlichSpencer.FS82.Poisson.Scalar
public import FroehlichSpencer.FS82.Poisson.PiSummable
public import FroehlichSpencer.FS82.Poisson.QuadraticBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

open Complex Matrix

private theorem summable_real_gaussian (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * a * (n : ℝ) ^ 2)) := by
  have hs := summable_scalar_gaussian (a := (a : ℂ)) (by simpa using ha) 0
  have hc : Summable (fun n : ℤ =>
      (Real.exp (-Real.pi * a * (n : ℝ) ^ 2) : ℂ)) := by
    apply hs.congr
    intro n
    simp only [zero_mul, mul_zero, add_zero]
    calc
      cexp (-Real.pi * (a : ℂ) * (n : ℂ) ^ 2) =
          cexp (((-Real.pi * a * (n : ℝ) ^ 2 : ℝ) : ℂ)) := by
        congr 1
        push_cast
        ring
      _ = (Real.exp (-Real.pi * a * (n : ℝ) ^ 2) : ℂ) :=
        (Complex.ofReal_exp _).symm
  have hr := hc.norm
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)] using hr

set_option linter.style.haveILetI false in
theorem summable_tilted_gaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (w : ι → ℂ) :
    Summable (fun n : ι → ℤ => cexp (-(Real.pi : ℂ) *
      (∑ i, ∑ j, (n i : ℂ) * (A i j : ℂ) * (n j : ℂ)) +
        2 * Real.pi * ∑ i, w i * (n i : ℂ))) := by
  classical
  let ef (n : ι → ℤ) : ℂ := -(Real.pi : ℂ) *
    (∑ i, ∑ j, (n i : ℂ) * (A i j : ℂ) * (n j : ℂ)) +
      2 * Real.pi * ∑ i, w i * (n i : ℂ)
  by_cases hι : Nonempty ι
  · letI := hι
    obtain ⟨c, hc, hq⟩ := exists_matrix_quadratic_lower_bound A hA
    let M : ℝ := Finset.univ.sup' Finset.univ_nonempty fun i => |(w i).re|
    have hM (i : ι) : |(w i).re| ≤ M :=
      Finset.le_sup' (fun j => |(w j).re|) (Finset.mem_univ i)
    let D : ℝ := Real.pi * (c / 2)
    let L : ℝ := 2 * Real.pi * M
    let C : ℝ := L ^ 2 / (4 * D)
    let g : ℤ → ℝ := fun z => Real.exp (-Real.pi * (c / 2) * (z : ℝ) ^ 2)
    let G : (ι → ℤ) → ℝ := fun n => ∏ i, g (n i)
    have hD : 0 < D := by
      dsimp [D]
      positivity
    have hL : 0 ≤ L := by
      dsimp [L, M]
      have hM0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun i => |(w i).re|) :=
        (abs_nonneg ((w (Classical.choice ‹Nonempty ι›)).re)).trans
          (Finset.le_sup' (fun i => |(w i).re|)
            (Finset.mem_univ (Classical.choice ‹Nonempty ι›)))
      positivity
    have hyoung (t : ℝ) (ht : 0 ≤ t) : L * t ≤ D * t ^ 2 + C := by
      have hsquare := sq_nonneg (2 * D * t - L)
      dsimp [C]
      field_simp [ne_of_gt hD] at hsquare ⊢
      nlinarith
    have hgauss : Summable g := by
      exact summable_real_gaussian (c / 2) (by linarith)
    have hG : Summable G := by
      exact summable_pi_prod_of_summable g hgauss
    have hmaj (n : ι → ℤ) : ‖cexp (ef n)‖ ≤ Real.exp (C * Fintype.card ι) * G n := by
      have hqcast : c * ∑ i, (n i : ℝ) ^ 2 ≤
          ∑ i, (n i : ℝ) * ∑ j, A i j * (n j : ℝ) := by
        have hh := hq (fun i => (n i : ℝ))
        have hmul : (star (fun i => (n i : ℝ)) ⬝ᵥ A *ᵥ (fun i => (n i : ℝ))) =
            ∑ i, (n i : ℝ) * ∑ j, A i j * (n j : ℝ) := by
          simp [dotProduct, Matrix.mulVec]
        rw [hmul] at hh
        exact hh
      have hQre :
          (∑ i, ∑ j, (n i : ℂ) * (A i j : ℂ) * (n j : ℂ)).re =
            ∑ i, (n i : ℝ) * ∑ j, A i j * (n j : ℝ) := by
        simp_rw [Complex.re_sum, Complex.mul_re]
        simp [Finset.mul_sum, mul_assoc]
      have hlincomplex :
          (∑ i, w i * (n i : ℂ)).re = ∑ i, (w i).re * (n i : ℝ) := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp [Complex.mul_re]
      have hRe : (ef n).re =
          -Real.pi * (∑ i, (n i : ℝ) * ∑ j, A i j * (n j : ℝ)) +
            2 * Real.pi * ∑ i, (w i).re * (n i : ℝ) := by
        dsimp [ef]
        have h₁ : (-(Real.pi : ℂ) *
            (∑ i, ∑ j, (n i : ℂ) * (A i j : ℂ) * (n j : ℂ))).re =
            -Real.pi * (∑ i, (n i : ℝ) * ∑ j, A i j * (n j : ℝ)) := by
          simp [Complex.mul_re, hQre]
        have h₂ : ((2 * (Real.pi : ℂ) * (∑ i, w i * (n i : ℂ))).re) =
            2 * Real.pi * ∑ i, (w i).re * (n i : ℝ) := by
          simp [Complex.mul_re, hlincomplex]
        rw [h₁, h₂]
      have hlinear : 2 * Real.pi * ∑ i, (w i).re * (n i : ℝ) ≤
          L * ∑ i, |(n i : ℝ)| := by
        calc
          _ ≤ ∑ i, (2 * Real.pi) * (M * |(n i : ℝ)|) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro i hi
            have h₁ : (w i).re * (n i : ℝ) ≤
                |(w i).re| * |(n i : ℝ)| := by
              calc
                _ ≤ |(w i).re * (n i : ℝ)| := le_abs_self _
                _ = |(w i).re| * |(n i : ℝ)| := abs_mul _ _
            have h₂ : |(w i).re| * |(n i : ℝ)| ≤ M * |(n i : ℝ)| :=
              mul_le_mul_of_nonneg_right (hM i) (abs_nonneg _)
            have h₃ := mul_le_mul_of_nonneg_left (h₁.trans h₂) (by positivity :
              0 ≤ 2 * Real.pi)
            simpa only [mul_assoc] using h₃
          _ = (2 * Real.pi) * ∑ i, M * |(n i : ℝ)| := by rw [← Finset.mul_sum]
          _ = L * ∑ i, |(n i : ℝ)| := by simp [L, Finset.mul_sum, mul_assoc]
      have hyoungsum : L * ∑ i, |(n i : ℝ)| ≤
          D * ∑ i, (n i : ℝ) ^ 2 + C * Fintype.card ι := by
        calc
          _ = ∑ i, L * |(n i : ℝ)| := by simp [Finset.mul_sum]
          _ ≤ ∑ i, (D * |(n i : ℝ)| ^ 2 + C) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hyoung _ (abs_nonneg _)
          _ = _ := by
            simp [Finset.sum_add_distrib, Finset.mul_sum, sq_abs]
            ring
      have htotal : (ef n).re ≤ -D * ∑ i, (n i : ℝ) ^ 2 + C * Fintype.card ι := by
        rw [hRe]
        have hquad : -Real.pi *
            (∑ i, (n i : ℝ) * ∑ j, A i j * (n j : ℝ)) ≤
            -Real.pi * (c * ∑ i, (n i : ℝ) ^ 2) :=
          mul_le_mul_of_nonpos_left hqcast (neg_nonpos.mpr (le_of_lt Real.pi_pos))
        have hlin := hlinear.trans hyoungsum
        calc
          _ ≤ -Real.pi * (c * ∑ i, (n i : ℝ) ^ 2) +
                (L * ∑ i, |(n i : ℝ)|) := add_le_add hquad hlinear
          _ ≤ -Real.pi * (c * ∑ i, (n i : ℝ) ^ 2) +
                (D * ∑ i, (n i : ℝ) ^ 2 + C * Fintype.card ι) :=
              add_le_add (le_of_eq rfl) hyoungsum
          _ = -D * ∑ i, (n i : ℝ) ^ 2 + C * Fintype.card ι := by
            dsimp [D]
            ring
      have hprod : G n = Real.exp (-D * ∑ i, (n i : ℝ) ^ 2) := by
        rw [show G n = ∏ i, Real.exp (-Real.pi * (c / 2) * (n i : ℝ) ^ 2) by rfl]
        rw [← Real.exp_sum]
        congr 1
        simp [D, Finset.mul_sum]
      calc
        ‖cexp (ef n)‖ = Real.exp (ef n).re := by simp [Complex.norm_exp]
        _ ≤ Real.exp (-D * ∑ i, (n i : ℝ) ^ 2 + C * Fintype.card ι) :=
          Real.exp_le_exp.mpr htotal
        _ = Real.exp (C * Fintype.card ι) * G n := by
          rw [hprod, ← Real.exp_add]
          congr 1
          ring
    exact Summable.of_norm_bounded (hG.mul_left (Real.exp (C * Fintype.card ι)))
      (fun n => hmaj n)
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    exact (hasSum_fintype _).summable

end FroehlichSpencer.FS82.Poisson
