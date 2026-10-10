/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Selected-block decomposition of a finite curl energy

If no plaquette sees two selected links, the selected block of the curl
quadratic form is diagonal. This algebraic theorem isolates the precision
matrix calculation used by the tree-chart conditional law.
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic

/-- The square of a sum with pairwise-zero cross terms is the sum of squares. -/
theorem sum_sq_of_pairwise_orthogonal {E : Type*} [DecidableEq E]
    (T : Finset E) (f : E → ℝ)
    (hcross : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → f a * f b = 0) :
    (∑ a ∈ T, f a) ^ 2 = ∑ a ∈ T, f a ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hfa : f a = 0
  · simp [hfa]
  · have hrest : ∑ b ∈ T.erase a, f b = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hbT : b ∈ T := (Finset.mem_erase.mp hb).2
      have hprod := hcross a ha b hbT (Ne.symm hba)
      rcases mul_eq_zero.mp hprod with h | h
      · exact (hfa h).elim
      · exact h
    have hsum : ∑ b ∈ T, f b = f a := by
      rw [← Finset.add_sum_erase T f ha, hrest]
      ring
    calc
      ∑ b ∈ T, f a * f b = f a * ∑ b ∈ T, f b := by rw [Finset.mul_sum]
      _ = f a ^ 2 := by rw [hsum]; ring

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

/-- The curl of an edge field under a finite plaquette-link incidence matrix. -/
def curlField (s : P → E → ℝ) (a : E → ℝ) (p : P) : ℝ :=
  ∑ e : E, s p e * a e

/-- The quadratic action associated with the incidence matrix. -/
def curlEnergy (s : P → E → ℝ) (a : E → ℝ) : ℝ :=
  ∑ p : P, (curlField s a p) ^ 2

/-- The selected-link component of an edge field. -/
def selectedPart (T : Finset E) (x : E → ℝ) : E → ℝ :=
  fun e => if e ∈ T then x e else 0

/-- Diagonal precision coefficient of a selected link. For incidence matrices
with entries in `{0, ±1}`, this is its number of incident plaquettes. -/
def selectedDiagonalMass (s : P → E → ℝ) (b : E) : ℝ :=
  ∑ p : P, (s p b) ^ 2

/-- Linear offset seen by a selected link after the retained field is fixed. -/
def selectedLinearOffset (s : P → E → ℝ) (y : E → ℝ) (b : E) : ℝ :=
  ∑ p : P, s p b * curlField s y p

/-- The selected contribution to the curl on each plaquette. -/
def selectedCurl (s : P → E → ℝ) (T : Finset E) (x : E → ℝ) (p : P) : ℝ :=
  ∑ b ∈ T, s p b * x b

omit [Fintype P] [DecidableEq P] in
theorem curlField_add_selected (s : P → E → ℝ) (T : Finset E)
    (y x : E → ℝ) (p : P) :
    curlField s (y + selectedPart T x) p =
      curlField s y p + selectedCurl s T x p := by
  classical
  unfold curlField selectedCurl selectedPart
  change (∑ e : E, s p e * (y e + if e ∈ T then x e else 0)) =
    (∑ e : E, s p e * y e) + ∑ b ∈ T, s p b * x b
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ e : E, s p e * (if e ∈ T then x e else 0)) =
        ∑ e ∈ T, s p e * x e := by
          simpa only [mul_ite, mul_zero] using
            (Finset.sum_ite_mem_eq T (fun e => s p e * x e))
    _ = ∑ b ∈ T, s p b * x b := rfl

-- Exact decomposition of the curl energy around a selected block. The
-- plaquette-independence assumption makes the selected precision block
-- diagonal, with diagonal entries `selectedDiagonalMass`.
omit [DecidableEq P] in
theorem curlEnergy_decompose_selected (s : P → E → ℝ) (T : Finset E)
    (y x : E → ℝ)
    (hno : ∀ p, ∀ b₁ ∈ T, ∀ b₂ ∈ T, b₁ ≠ b₂ →
      s p b₁ = 0 ∨ s p b₂ = 0) :
    curlEnergy s (y + selectedPart T x) =
      curlEnergy s y +
        ∑ b ∈ T,
          (selectedDiagonalMass s b * x b ^ 2 +
            2 * selectedLinearOffset s y b * x b) := by
  classical
  have hselectedSq (p : P) :
      (selectedCurl s T x p) ^ 2 =
        ∑ b ∈ T, (s p b * x b) ^ 2 := by
    unfold selectedCurl
    apply sum_sq_of_pairwise_orthogonal T (fun b => s p b * x b)
    intro b₁ hb₁ b₂ hb₂ hne
    rcases hno p b₁ hb₁ b₂ hb₂ hne with h | h <;> simp [h]
  have hcross (p : P) :
      2 * curlField s y p * selectedCurl s T x p =
        ∑ b ∈ T, 2 * (s p b * curlField s y p) * x b := by
    unfold selectedCurl
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  calc
    curlEnergy s (y + selectedPart T x) =
        ∑ p : P, ((curlField s y p) ^ 2 +
          2 * curlField s y p * selectedCurl s T x p +
            (selectedCurl s T x p) ^ 2) := by
              unfold curlEnergy
              apply Finset.sum_congr rfl
              intro p hp
              rw [curlField_add_selected]
              ring
    _ = curlEnergy s y +
        ((∑ p : P, 2 * curlField s y p * selectedCurl s T x p) +
        ∑ p : P, (selectedCurl s T x p) ^ 2) := by
          unfold curlEnergy
          simp_rw [Finset.sum_add_distrib]
          ring
    _ = curlEnergy s y +
        ((∑ b ∈ T, 2 * selectedLinearOffset s y b * x b) +
        ∑ b ∈ T, selectedDiagonalMass s b * x b ^ 2) := by
          have hCrossEq :
              (∑ p : P, 2 * curlField s y p * selectedCurl s T x p) =
                ∑ b ∈ T, 2 * selectedLinearOffset s y b * x b := by
            calc
              _ = ∑ p : P, ∑ b ∈ T,
                    2 * (s p b * curlField s y p) * x b := by
                      apply Finset.sum_congr rfl
                      intro p hp
                      exact hcross p
              _ = ∑ b ∈ T, ∑ p : P,
                    2 * (s p b * curlField s y p) * x b := Finset.sum_comm
              _ = ∑ b ∈ T, 2 * selectedLinearOffset s y b * x b := by
                    apply Finset.sum_congr rfl
                    intro b hb
                    unfold selectedLinearOffset
                    calc
                      (∑ p : P, 2 * (s p b * curlField s y p) * x b) =
                          ∑ p : P, (2 * x b) *
                            (s p b * curlField s y p) := by
                              apply Finset.sum_congr rfl
                              intro p hp
                              ring
                      _ = (2 * x b) *
                            ∑ p : P, s p b * curlField s y p :=
                              (Finset.mul_sum ..).symm
                      _ = 2 * (∑ p : P,
                            s p b * curlField s y p) * x b := by ring
          have hDiagEq :
              (∑ p : P, (selectedCurl s T x p) ^ 2) =
                ∑ b ∈ T, selectedDiagonalMass s b * x b ^ 2 := by
            calc
              _ = ∑ p : P, ∑ b ∈ T, (s p b * x b) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    exact hselectedSq p
              _ = ∑ b ∈ T, ∑ p : P, (s p b * x b) ^ 2 := Finset.sum_comm
              _ = ∑ b ∈ T, selectedDiagonalMass s b * x b ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro b hb
                    unfold selectedDiagonalMass
                    calc
                      (∑ p : P, (s p b * x b) ^ 2) =
                          ∑ p : P, (s p b) ^ 2 * x b ^ 2 := by
                            apply Finset.sum_congr rfl
                            intro p hp
                            ring
                      _ = (∑ p : P, (s p b) ^ 2) * x b ^ 2 :=
                            (Finset.sum_mul ..).symm
          rw [hCrossEq, hDiagEq]
    _ = curlEnergy s y +
        ∑ b ∈ T,
          (selectedDiagonalMass s b * x b ^ 2 +
            2 * selectedLinearOffset s y b * x b) := by
          apply congrArg (fun q : ℝ => curlEnergy s y + q)
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro b hb
          ring

/-- Scalar completed-square identity; the conditional mean has the minus
sign forced by the positive off-diagonal term `2 ℓ x`. -/
theorem selectedQuadratic_completeSquare (n ell x : ℝ) (hn : 0 < n) :
    n * x ^ 2 + 2 * ell * x =
      n * (x + ell / n) ^ 2 - ell ^ 2 / n := by
  field_simp [ne_of_gt hn]
  ring

-- Complete the square in every selected coordinate at once. Combined with
-- `curlEnergy_decompose_selected`, this identifies the conditional means
-- `-ℓ_b(y)/n_b` and the diagonal variances `β/n_b`.
omit [Fintype E] [DecidableEq E] in
theorem selectedBlock_completeSquare (T : Finset E) (n ell x : E → ℝ)
    (hn : ∀ b ∈ T, 0 < n b) :
    (∑ b ∈ T, (n b * x b ^ 2 + 2 * ell b * x b)) =
      ∑ b ∈ T, (n b * (x b + ell b / n b) ^ 2 - ell b ^ 2 / n b) := by
  apply Finset.sum_congr rfl
  intro b hb
  exact selectedQuadratic_completeSquare (n b) (ell b) (x b) (hn b hb)


end FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic

end
