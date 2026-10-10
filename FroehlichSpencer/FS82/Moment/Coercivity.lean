module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

open scoped InnerProductSpace

namespace FroehlichSpencer.FS82.Moment.Coercivity

/-- Cauchy--Schwarz for a positive semidefinite symmetric bilinear form. -/
theorem psd_cauchy_schwarz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : E →L[ℝ] E)
    (hsym : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (K x)) (x y : E) :
    (inner ℝ (K x) y)^2 ≤ (inner ℝ x (K x)) * (inner ℝ y (K y)) := by
  let a := inner ℝ (K x) y
  let b := inner ℝ y (K y)
  let c := inner ℝ x (K x)
  have hquad : ∀ t : ℝ, 0 ≤ c + 2 * t * a + t^2 * b := by
    intro t
    have hh := hpos (x + t • y)
    change 0 ≤ inner ℝ (x + t • y) (K (x + t • y)) at hh
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right] at hh
    rw [show (starRingEnd ℝ) t = t from star_trivial t] at hh
    have hyx : inner ℝ y (K x) = a := by
      dsimp [a]
      rw [real_inner_comm]
    have hxy : inner ℝ x (K y) = a := by
      dsimp [a]
      rw [← hsym x y]
    rw [hyx, hxy] at hh
    change 0 ≤ c + 2 * t * a + t^2 * b
    dsimp [a, b, c] at hh ⊢
    nlinarith [hh]
  by_cases hb : inner ℝ y (K y) = 0
  · by_cases ha : inner ℝ (K x) y = 0
    · simp [ha, hb]
    · have hval := hquad (-(inner ℝ x (K x) + 1) /
        (2 * inner ℝ (K x) y))
      have hcalc : inner ℝ x (K x) +
          2 * (-(inner ℝ x (K x) + 1) / (2 * inner ℝ (K x) y)) *
            inner ℝ (K x) y +
          (-(inner ℝ x (K x) + 1) / (2 * inner ℝ (K x) y))^2 *
            inner ℝ y (K y) = -1 := by
        rw [hb]
        field_simp [ha]
        ring
      rw [hcalc] at hval
      norm_num at hval
  · have hbpos : 0 < inner ℝ y (K y) := lt_of_le_of_ne (hpos y) (Ne.symm hb)
    have hval := hquad (-(inner ℝ (K x) y) / inner ℝ y (K y))
    have hcalc : inner ℝ x (K x) +
        2 * (-(inner ℝ (K x) y) / inner ℝ y (K y)) * inner ℝ (K x) y +
        (-(inner ℝ (K x) y) / inner ℝ y (K y))^2 * inner ℝ y (K y) =
        inner ℝ x (K x) - (inner ℝ (K x) y)^2 / inner ℝ y (K y) := by
      field_simp [ne_of_gt hbpos]
      ring
    rw [hcalc] at hval
    exact (div_le_iff₀ hbpos).mp (by linarith)


theorem inverse_quadratic_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : E →L[ℝ] E)
    (hsym : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (K x))
    (R : ℝ) (hR : 0 < R) (hK : ‖K‖ ≤ R)
    (j v : E) (hinv : K v = j) :
    inner ℝ j v ≥ ‖j‖^2 / R := by
  have hcs := psd_cauchy_schwarz K hsym hpos v j
  have hnorm : inner ℝ j j = ‖j‖^2 := by
    rw [real_inner_self_eq_norm_sq]
  have hKbound : inner ℝ j (K j) ≤ R * ‖j‖^2 := by
    calc
      inner ℝ j (K j) ≤ ‖j‖ * ‖K j‖ := real_inner_le_norm _ _
      _ ≤ ‖j‖ * (‖K‖ * ‖j‖) := by gcongr; exact K.le_opNorm j
      _ ≤ R * ‖j‖^2 := by nlinarith [norm_nonneg j, hK]
  have hineq : ‖j‖^4 ≤ (inner ℝ v (K v)) * (inner ℝ j (K j)) := by
    have hcs' : (‖j‖^2)^2 ≤ (inner ℝ v (K v)) * (inner ℝ j (K j)) := by
      simpa [hinv, hnorm] using hcs
    nlinarith [hcs']
  have hEq : inner ℝ v (K v) = inner ℝ j v := by
    rw [hinv]
    exact real_inner_comm _ _
  rw [hEq] at hineq
  have hnonneg : 0 ≤ inner ℝ j v := by
    rw [← hEq]
    exact hpos v
  by_cases hj : ‖j‖ = 0
  · simp [hj, hnonneg]
  have hden : 0 ≤ inner ℝ j (K j) := hpos j
  have hnormsqpos : 0 < ‖j‖^2 := by
    positivity
  have hmul : ‖j‖^2 * ‖j‖^2 ≤
      inner ℝ j v * (R * ‖j‖^2) := by
    calc
      ‖j‖^2 * ‖j‖^2 ≤ inner ℝ j v * inner ℝ j (K j) := by
        nlinarith [hineq]
      _ ≤ inner ℝ j v * (R * ‖j‖^2) :=
        mul_le_mul_of_nonneg_left hKbound hnonneg
  have hmain : ‖j‖^2 ≤ R * inner ℝ j v := by
    have hmul' : ‖j‖^2 * ‖j‖^2 ≤
        (R * inner ℝ j v) * ‖j‖^2 := by
      calc
        ‖j‖^2 * ‖j‖^2 ≤ inner ℝ j v * (R * ‖j‖^2) := hmul
        _ = (R * inner ℝ j v) * ‖j‖^2 := by ring
    exact le_of_mul_le_mul_right hmul' hnormsqpos
  rw [ge_iff_le]
  exact (div_le_iff₀ hR).2 (by nlinarith [hmain])

end FroehlichSpencer.FS82.Moment.Coercivity
