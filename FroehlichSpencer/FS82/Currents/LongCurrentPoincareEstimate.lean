/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import FroehlichSpencer.FS82.Currents.LongCurrentEstimate
public import FroehlichSpencer.FS82.Gaussian.LatticePoincare
public section
open scoped BigOperators InnerProductSpace
namespace FroehlichSpencer.FS82.Currents.LongCurrentPoincare
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents.LongCurrentEstimate
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.Packing

/-- Long-current Jensen errors satisfy the LongCurrentEstimate c=1 estimate with no supplied
spectral-gap premise: the required estimate follows from lattice Poincare. -/
theorem longCurrent_jensen_error_c1
    {B : SourceBox} (origin : Fin 4 → ℤ) (N m : ℕ) (a : ℝ)
    (T : Finset (ClosedIntegerCurrent B))
    (τ : coClosed (latticeExactOneComplex (B := B) origin))
    (z : IntegerCurrent B → ℝ)
    (hBmax : ∀ i : Fin 4, B i ≤ N)
    (hm : 1 ≤ m) (ha : 8 ≤ a)
    (hdisj : (↑T : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
      (fun j => currentSupport (fun e : Link B => j.1 e)))
    (hlong : ∀ j ∈ T,
      m ≤ (currentSupport (fun e : Link B => j.1 e)).card)
    (hz0 : ∀ j ∈ T, 0 ≤ z j.1)
    (hz : ∀ j ∈ T,
      z j.1 ≤ Real.exp (-(a *
        (integerCurrentNormSq (fun e : Link B => j.1 e) +
          ((currentSupport (fun e : Link B => j.1 e)).card : ℝ))))) :
    (∑ j ∈ T, jensenGamma (z j.1) *
      (latticeCurrentPhase origin j.1 j.2 τ)^2) ≤
      (16 * Real.pi^2 / (a * Real.exp 1)) *
        (N + 1 : ℝ)^6 * Real.exp (-(a * m)) *
        ‖(latticeExactOneComplex (B := B) origin).d₁
          (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
  have hP :
      ‖(τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 ≤
        (N + 1 : ℝ)^2 *
          ‖(latticeExactOneComplex (B := B) origin).d₁
            (τ : EuclideanSpace ℝ (SourceDualOneCells B))‖^2 := by
    have h := latticeW_poincare origin N hBmax τ
    rw [latticeStencil_inner_eq_d1_norm_sq] at h
    simpa [Nat.cast_add] using h
  exact longCurrent_jensen_error_c1_of_poincare
    origin N m a T τ z hBmax hm ha hdisj hlong hz0 hz hP

end FroehlichSpencer.FS82.Currents.LongCurrentPoincare
end
