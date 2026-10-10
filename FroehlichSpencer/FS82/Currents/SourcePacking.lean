/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.Comparison
public import FroehlichSpencer.FS82.Moment.SourceConstructor
public import FroehlichSpencer.FS82.Currents.IncidenceComponentPacking
public import FroehlichSpencer.FS82.Currents.LongCurrentPoincareEstimate
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# source packing coefficient

This module records the explicit short-component plus long-current coefficient,
its log-thick decay, and the finite-union assembly of already established
aggregate budgets.

The geometric source producers remain explicit inputs at the
assembly boundary.
-/

@[expose] public section

open Filter

namespace FroehlichSpencer.FS82.Currents.SourcePacking

open FroehlichSpencer.FS82.Currents.ComponentPacking
open FroehlichSpencer.FS82.Currents.LongCurrentEstimate
open FroehlichSpencer.FS82.Currents.LongCurrentPoincare
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.Comparison
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Moment.SourceConstructor

noncomputable section


/-- The component polynomial tail at unit exponential rate. -/
noncomputable def componentPolyTail13 : ℝ :=
  ∑' L : ℕ, (L : ℝ)^13 * Real.exp (-(L : ℝ))

/-- Corrected SourcePacking short activity: the Jensen estimate proves the coefficient
`20 C^2/a^2`, with no additional `e^-2` factor. -/
noncomputable def sourceComponentActivityL5 (a C : ℝ) (L : ℕ) : ℝ :=
  (20 * C^2 / a^2) * (L : ℝ)^10 * Real.exp (-(a * (L : ℝ)))

/-- Corrected SourcePacking short tail, with the coefficient actually proved by the
L^5 Jensen estimate. -/
noncomputable def sourceComponentCpackPrime (a C : ℝ) : ℝ :=
  (1280 * C^2 / a^2) *
    ∑' L : ℕ, (L : ℝ)^13 * Real.exp (-(a * (L : ℝ)))

/-- Corrected side-six conversion for the actual L^5 majorant. -/
theorem sourceComponentActivityL5_budget_side_six (a C : ℝ)
    (ha : 0 < a) (K : Finset ℕ) :
    (∑ L ∈ K, 5184 * (L : ℝ)^3 * sourceComponentActivityL5 a C L) ≤
      81 * sourceComponentCpackPrime a C := by
  have hs : Summable (fun L : ℕ =>
      (L : ℝ)^13 * Real.exp (-(a * (L : ℝ)))) := by
    simpa only [neg_mul] using
      (Real.summable_pow_mul_exp_neg_nat_mul 13 (r := a) ha)
  have hsum := hs.sum_le_tsum K (by intro L hL; positivity)
  have hfinite :
      (∑ L ∈ K, 5184 * (L : ℝ)^3 * sourceComponentActivityL5 a C L) =
        (103680 * C^2 / a^2) *
          ∑ L ∈ K, (L : ℝ)^13 * Real.exp (-(a * (L : ℝ))) := by
    simp only [sourceComponentActivityL5]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro L hL
    ring
  rw [hfinite]
  have hcoef : 0 ≤ 103680 * C^2 / a^2 := by positivity
  calc
    (103680 * C^2 / a^2) *
        ∑ L ∈ K, (L : ℝ)^13 * Real.exp (-(a * (L : ℝ)))
      ≤ (103680 * C^2 / a^2) *
        ∑' L : ℕ, (L : ℝ)^13 * Real.exp (-(a * (L : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum hcoef
    _ = 81 * sourceComponentCpackPrime a C := by
      simp only [sourceComponentCpackPrime]
      ring

theorem componentPolyTail13_nonneg : 0 ≤ componentPolyTail13 := by
  unfold componentPolyTail13
  exact tsum_nonneg fun L => by positivity


/-- The exact L^5 short-component coefficient is bounded by an explicit
exponential tail. -/
theorem sourceComponentCpackPrime_exp_bound (a C : ℝ) (ha : 1 ≤ a) :
    sourceComponentCpackPrime a C ≤
      (1280 * C^2) *
        Real.exp (1 - a) * componentPolyTail13 := by
  have ha0 : 0 < a := by linarith
  let fA : ℕ → ℝ := fun L => (L : ℝ)^13 * Real.exp (-(a * (L : ℝ)))
  let f1 : ℕ → ℝ := fun L => (L : ℝ)^13 * Real.exp (-(L : ℝ))
  have hsA : Summable fA := by
    simpa [fA, neg_mul] using
      (Real.summable_pow_mul_exp_neg_nat_mul 13 (r := a) ha0)
  have hs1 : Summable f1 := by
    simpa [f1] using
      (Real.summable_pow_mul_exp_neg_nat_mul 13 (r := (1 : ℝ)) (by norm_num))
  have hpoint : ∀ L, fA L ≤ Real.exp (1 - a) * f1 L := by
    intro L
    by_cases hL : L = 0
    · simp [fA, f1, hL]
    · have hL1 : 1 ≤ (L : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hL)
      have hLsub : 0 ≤ (L : ℝ) - 1 := by linarith
      have harg : -(a * ((L : ℝ) - 1)) ≤ -((L : ℝ) - 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ha) hLsub]
      have hexp : Real.exp (-(a * ((L : ℝ) - 1))) ≤
          Real.exp (-((L : ℝ) - 1)) := Real.exp_le_exp.mpr harg
      have hfactor : Real.exp (-(a * (L : ℝ))) =
          Real.exp (-a) * Real.exp (-(a * ((L : ℝ) - 1))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hfactor1 : Real.exp (-(L : ℝ)) =
          Real.exp (-1) * Real.exp (-((L : ℝ) - 1)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp [fA, f1]
      rw [hfactor, hfactor1]
      have hExpScale : Real.exp (-a) = Real.exp (1 - a) * Real.exp (-1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hExpScale]
      calc
        (L : ℝ)^13 * (Real.exp (1 - a) * Real.exp (-1) *
            Real.exp (-(a * ((L : ℝ) - 1)))) =
          ((L : ℝ)^13 * Real.exp (1 - a) * Real.exp (-1)) *
            Real.exp (-(a * ((L : ℝ) - 1))) := by ring
        _ ≤ ((L : ℝ)^13 * Real.exp (1 - a) * Real.exp (-1)) *
            Real.exp (-((L : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = Real.exp (1 - a) *
            ((L : ℝ)^13 * (Real.exp (-1) *
              Real.exp (-((L : ℝ) - 1)))) := by ring
  have hsum : (∑' L : ℕ, fA L) ≤
      ∑' L : ℕ, Real.exp (1 - a) * f1 L :=
    Summable.tsum_le_tsum hpoint hsA (hs1.mul_left _)
  have hscale : (∑' L : ℕ, Real.exp (1 - a) * f1 L) =
      Real.exp (1 - a) * componentPolyTail13 := by
    simpa [f1, componentPolyTail13] using
      (hs1.tsum_mul_left (Real.exp (1 - a)))
  have hsum' : (∑' L : ℕ, fA L) ≤
      Real.exp (1 - a) * componentPolyTail13 := by rw [← hscale]; exact hsum
  have hcoef : 0 ≤ 1280 * C^2 / a^2 := by positivity
  have hcoef' : 1280 * C^2 / a^2 ≤ 1280 * C^2 := by
    apply (div_le_iff₀ (by positivity)).2
    have haSq : 1 ≤ a^2 := by nlinarith [sq_nonneg (a - 1)]
    nlinarith [mul_nonneg (sq_nonneg C) (sub_nonneg.mpr haSq)]
  unfold sourceComponentCpackPrime
  calc
    (1280 * C^2 / a^2) * ∑' L : ℕ, fA L ≤
        (1280 * C^2 / a^2) *
          (Real.exp (1 - a) * componentPolyTail13) :=
      mul_le_mul_of_nonneg_left hsum' hcoef
    _ ≤ (1280 * C^2) *
        (Real.exp (1 - a) * componentPolyTail13) :=
      mul_le_mul_of_nonneg_right hcoef' (mul_nonneg (Real.exp_pos _).le
        componentPolyTail13_nonneg)
    _ = (1280 * C^2) *
        Real.exp (1 - a) * componentPolyTail13 := by ring

/-- The long-current coefficient from LongCurrentEstimate, retaining its exponential factor
rather than replacing it by a uniform log-thick constant. -/
noncomputable def longCoefficient (a : ℝ) (N m : ℕ) : ℝ :=
  (16 * Real.pi ^ 2 / (a * Real.exp 1)) *
    ((N + 1 : ℕ) : ℝ)^6 * Real.exp (-(a * (m : ℝ)))

/-- The unconditional LongCurrentPoincare long-current estimate on the source lattice
carrier, with its field energy expanded on the source dual two-cells. -/
theorem longCurrent_jensen_error_c1_sourceField
    {B : FroehlichSpencer.FS82.Cubical.Box 4}
    (N m : ℕ) (a : ℝ)
    (T : Finset (ClosedIntegerCurrent B))
    (τ : SourceW B) (z : FroehlichSpencer.FS82.Currents.IntegerCurrent B → ℝ)
    (hBmax : ∀ i : Fin 4, B i ≤ N)
    (hm : 1 ≤ m) (ha : 8 ≤ a)
    (hdisj : (↑T : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
      (fun j =>
        FroehlichSpencer.FS82.Currents.currentSupport
          (fun e : FroehlichSpencer.FS82.Currents.Link B => j.1 e)))
    (hlong : ∀ j ∈ T,
      m ≤ (FroehlichSpencer.FS82.Currents.currentSupport
        (fun e : FroehlichSpencer.FS82.Currents.Link B => j.1 e)).card)
    (hz0 : ∀ j ∈ T, 0 ≤ z j.1)
    (hz : ∀ j ∈ T,
      z j.1 ≤ Real.exp (-(a *
        (FroehlichSpencer.FS82.Currents.integerCurrentNormSq
            (fun e : FroehlichSpencer.FS82.Currents.Link B => j.1 e) +
          ((FroehlichSpencer.FS82.Currents.currentSupport
            (fun e : FroehlichSpencer.FS82.Currents.Link B => j.1 e)).card : ℝ))))) :
    (∑ j ∈ T, jensenGamma (z j.1) *
      (latticeCurrentPhase Cubical.originZero j.1 j.2 τ)^2) ≤
      longCoefficient a N m *
        ∑ p : FroehlichSpencer.FS82.Gaussian.SourceDualTwoCells B,
          ((sourceLatticeComplex (B := B)).d₁
            (τ : EuclideanSpace ℝ
              (FroehlichSpencer.FS82.Gaussian.SourceDualOneCells B)) p)^2 := by
  let C := sourceLatticeComplex (B := B)
  have hLongCurrent :=
    FroehlichSpencer.FS82.Currents.LongCurrentPoincare.longCurrent_jensen_error_c1
      Cubical.originZero N m a T τ z hBmax hm ha hdisj hlong hz0 hz
  have hnorm :
      ‖C.d₁ (τ : EuclideanSpace ℝ
        (FroehlichSpencer.FS82.Gaussian.SourceDualOneCells B))‖^2 =
        ∑ p : FroehlichSpencer.FS82.Gaussian.SourceDualTwoCells B,
          (C.d₁ (τ : EuclideanSpace ℝ
            (FroehlichSpencer.FS82.Gaussian.SourceDualOneCells B)) p)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ j ∈ T, jensenGamma (z j.1) *
        (latticeCurrentPhase Cubical.originZero j.1 j.2 τ)^2) ≤
      (16 * Real.pi^2 / (a * Real.exp 1)) * (N + 1 : ℝ)^6 *
        Real.exp (-(a * (m : ℝ))) *
        ‖C.d₁ (τ : EuclideanSpace ℝ
          (FroehlichSpencer.FS82.Gaussian.SourceDualOneCells B))‖^2 := by
      simpa [C, longCoefficient] using hLongCurrent
    _ = longCoefficient a N m *
        ∑ p : FroehlichSpencer.FS82.Gaussian.SourceDualTwoCells B,
          (C.d₁ (τ : EuclideanSpace ℝ
            (FroehlichSpencer.FS82.Gaussian.SourceDualOneCells B)) p)^2 := by
      rw [hnorm]
      simp [longCoefficient]

/-- The explicit combined coefficient prescribed by the L^5 short estimate
and the LongCurrentEstimate long-current estimate. -/
noncomputable def sourcePackingCoefficient
    (beta beta₁ C : ℝ) (N m : ℕ) : ℝ :=
  81 * sourceComponentCpackPrime (currentRate beta beta₁) C +
    longCoefficient (currentRate beta beta₁) N m

/-- The explicit constant in the uniform exponential tail for the combined
short and long coefficient. -/
noncomputable def sourcePackingTailConstant (beta₁ C : ℝ) : ℝ :=
  81 * (1280 * C^2) *
      Real.exp (1 + beta₁ / 2) * componentPolyTail13 +
    (2 * Real.pi^2 / Real.exp 1) * Real.exp (6 + beta₁ / 2)

theorem longCoefficient_logThick_bound (a : ℝ) (N m : ℕ)
    (hN : 1 ≤ N) (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (ha : 8 ≤ a) :
    longCoefficient a N m ≤
      (16 * Real.pi ^ 2 / (a * Real.exp 1)) *
        Real.exp (-((a - 6) * (m : ℝ))) := by
  have hN1 : 0 < (N + 1 : ℝ) := by positivity
  have hmpos : 0 < (m : ℝ) := by
    have hlog : 0 < Real.log (N + 1 : ℝ) := by
      apply Real.log_pos
      norm_num
      exact_mod_cast hN
    exact lt_of_lt_of_le hlog hm
  have hNexp : (N + 1 : ℝ) ≤ Real.exp (m : ℝ) :=
    (Real.log_le_iff_le_exp hN1).1 hm
  have hN6 : (N + 1 : ℝ)^6 ≤ Real.exp (6 * (m : ℝ)) := by
    calc
      (N + 1 : ℝ)^6 ≤ (Real.exp (m : ℝ))^6 := by gcongr
      _ = Real.exp (6 * (m : ℝ)) := by
        rw [show (6 : ℝ) * (m : ℝ) = (6 : ℕ) * (m : ℝ) by norm_num]
        rw [← Real.exp_nat_mul]
  have hExp : Real.exp (-(a * (m : ℝ))) ≤
      Real.exp (-(a * (m : ℝ)) + 6 * (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hmpos.le]
  have hprod : ((N + 1 : ℕ) : ℝ)^6 * Real.exp (-(a * (m : ℝ))) ≤
      Real.exp (-((a - 6) * (m : ℝ))) := by
    have hcast : ((N + 1 : ℕ) : ℝ) = (N + 1 : ℝ) := by norm_num
    rw [hcast]
    calc
      (N + 1 : ℝ)^6 * Real.exp (-(a * (m : ℝ))) ≤
          Real.exp (6 * (m : ℝ)) * Real.exp (-(a * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right hN6 (Real.exp_pos _).le
      _ = Real.exp (6 * (m : ℝ) + -(a * (m : ℝ))) := by
        rw [← Real.exp_add]
      _ = Real.exp (-((a - 6) * (m : ℝ))) := by congr 1; ring
  have hcoef : 0 ≤ 16 * Real.pi ^ 2 / (a * Real.exp 1) := by positivity
  unfold longCoefficient
  calc
    16 * Real.pi ^ 2 / (a * Real.exp 1) * ((N + 1 : ℕ) : ℝ)^6 *
        Real.exp (-(a * (m : ℝ))) =
      (16 * Real.pi ^ 2 / (a * Real.exp 1)) *
        (((N + 1 : ℕ) : ℝ)^6 * Real.exp (-(a * (m : ℝ)))) := by ring
    _ ≤ (16 * Real.pi ^ 2 / (a * Real.exp 1)) *
        Real.exp (-((a - 6) * (m : ℝ))) := mul_le_mul_of_nonneg_left hprod hcoef

theorem longCoefficient_logThick_exp_bound (a : ℝ) (N m : ℕ)
    (hN : 1 ≤ N) (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (ha : 8 ≤ a) :
    longCoefficient a N m ≤
      (2 * Real.pi ^ 2 / Real.exp 1) * Real.exp (-(a - 6)) := by
  have hmpos : 1 ≤ (m : ℝ) := by
    have hlog : 0 < Real.log (N + 1 : ℝ) := by
      apply Real.log_pos
      norm_num
      exact_mod_cast hN
    have hmp : 0 < m := by exact_mod_cast (lt_of_lt_of_le hlog hm)
    have hmNat : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmp)
    exact_mod_cast hmNat
  have ha6 : 0 < a - 6 := by linarith
  have hExp : Real.exp (-((a - 6) * (m : ℝ))) ≤ Real.exp (-(a - 6)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha6.le (sub_nonneg.mpr hmpos)]
  have hrecip : 1 / a ≤ 1 / 8 := by
    have ha0 : 0 < a := by linarith
    have h8a : 8 / a ≤ 1 := (div_le_one₀ ha0).2 ha
    calc
      1 / a = (1 / 8) * (8 / a) := by field_simp
      _ ≤ (1 / 8) * 1 := mul_le_mul_of_nonneg_left h8a (by norm_num)
      _ = 1 / 8 := by ring
  have hcoef : 0 ≤ (16 * Real.pi ^ 2 / (a * Real.exp 1)) := by positivity
  have hcoef' : 16 * Real.pi ^ 2 / (a * Real.exp 1) ≤
      2 * Real.pi ^ 2 / Real.exp 1 := by
    have ha0 : 0 < a := by linarith
    have h8a : 8 / a ≤ 1 := (div_le_one₀ ha0).2 ha
    calc
      16 * Real.pi ^ 2 / (a * Real.exp 1) =
          (2 * Real.pi ^ 2 / Real.exp 1) * (8 / a) := by field_simp; ring
      _ ≤ (2 * Real.pi ^ 2 / Real.exp 1) * 1 :=
        mul_le_mul_of_nonneg_left h8a (by positivity)
      _ = 2 * Real.pi ^ 2 / Real.exp 1 := by ring
  calc
    longCoefficient a N m ≤
        (16 * Real.pi ^ 2 / (a * Real.exp 1)) *
          Real.exp (-((a - 6) * (m : ℝ))) :=
      longCoefficient_logThick_bound a N m hN hm ha
    _ ≤ (16 * Real.pi ^ 2 / (a * Real.exp 1)) * Real.exp (-(a - 6)) :=
      mul_le_mul_of_nonneg_left hExp hcoef
    _ ≤ (2 * Real.pi ^ 2 / Real.exp 1) * Real.exp (-(a - 6)) :=
      mul_le_mul_of_nonneg_right hcoef' (Real.exp_pos _).le

/-- Short plus long coefficient has a uniform exponential tail on every fixed
log-thick class. The rate is exactly the corrected source rate. -/
theorem sourcePackingCoefficient_exp_bound
    (beta beta₁ C : ℝ) (N m : ℕ)
    (hN : 1 ≤ N) (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hRate : 8 ≤ currentRate beta beta₁) :
    sourcePackingCoefficient beta beta₁ C N m ≤
      ((81 * (1280 * C^2) *
          Real.exp (1 + beta₁ / 2) * componentPolyTail13) +
        (2 * Real.pi^2 / Real.exp 1) * Real.exp (6 + beta₁ / 2)) *
          Real.exp (-(beta / 432)) := by
  have hshort := sourceComponentCpackPrime_exp_bound
    (currentRate beta beta₁) C (by linarith)
  have hrateId : currentRate beta beta₁ = beta / 432 - beta₁ / 2 := by
    simp [currentRate]
    ring
  have hshortExp : Real.exp (1 - currentRate beta beta₁) =
      Real.exp (1 + beta₁ / 2) * Real.exp (-(beta / 432)) := by
    rw [hrateId, ← Real.exp_add]
    congr 1
    ring
  have hlong := longCoefficient_logThick_exp_bound
    (currentRate beta beta₁) N m hN hm hRate
  have hlongExp : Real.exp (-(currentRate beta beta₁ - 6)) =
      Real.exp (6 + beta₁ / 2) * Real.exp (-(beta / 432)) := by
    rw [hrateId, ← Real.exp_add]
    congr 1
    ring
  have hshort' : 81 * sourceComponentCpackPrime (currentRate beta beta₁) C ≤
      (81 * (1280 * C^2) *
        Real.exp (1 + beta₁ / 2) * componentPolyTail13) *
        Real.exp (-(beta / 432)) := by
    rw [hshortExp] at hshort
    have h81 : 0 ≤ (81 : ℝ) := by norm_num
    have h := mul_le_mul_of_nonneg_left hshort h81
    nlinarith [h]
  have hlong' : longCoefficient (currentRate beta beta₁) N m ≤
      ((2 * Real.pi^2 / Real.exp 1) * Real.exp (6 + beta₁ / 2)) *
        Real.exp (-(beta / 432)) := by
    rw [hlongExp] at hlong
    calc
      longCoefficient (currentRate beta beta₁) N m ≤
          (2 * Real.pi^2 / Real.exp 1) *
            (Real.exp (6 + beta₁ / 2) * Real.exp (-(beta / 432))) := hlong
      _ = ((2 * Real.pi^2 / Real.exp 1) * Real.exp (6 + beta₁ / 2)) *
            Real.exp (-(beta / 432)) := by ring
  unfold sourcePackingCoefficient
  have hsum := add_le_add hshort' hlong'
  calc
    81 * sourceComponentCpackPrime (currentRate beta beta₁) C +
      longCoefficient (currentRate beta beta₁) N m ≤
      (81 * (1280 * C^2) *
          Real.exp (1 + beta₁ / 2) * componentPolyTail13) *
          Real.exp (-(beta / 432)) +
        ((2 * Real.pi^2 / Real.exp 1) * Real.exp (6 + beta₁ / 2)) *
          Real.exp (-(beta / 432)) := hsum
    _ = ((81 * (1280 * C^2) *
          Real.exp (1 + beta₁ / 2) * componentPolyTail13) +
        (2 * Real.pi^2 / Real.exp 1) * Real.exp (6 + beta₁ / 2)) *
          Real.exp (-(beta / 432)) := by ring

theorem sourcePackingTailConstant_pos (beta₁ C : ℝ) :
    0 < sourcePackingTailConstant beta₁ C := by
  unfold sourcePackingTailConstant
  have hlong : 0 < (2 * Real.pi^2 / Real.exp 1) *
      Real.exp (6 + beta₁ / 2) := by positivity
  have hshort : 0 ≤ 81 * (1280 * C^2) *
      Real.exp (1 + beta₁ / 2) * componentPolyTail13 := by
    apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg C)))
        (Real.exp_pos _).le
    · exact componentPolyTail13_nonneg
  linarith

theorem sourceComponentCpackPrime_nonneg (a C : ℝ) (ha : 0 < a) :
    0 ≤ sourceComponentCpackPrime a C := by
  unfold sourceComponentCpackPrime
  apply mul_nonneg
  · positivity
  · apply tsum_nonneg
    intro L
    positivity


end

end SourcePacking
