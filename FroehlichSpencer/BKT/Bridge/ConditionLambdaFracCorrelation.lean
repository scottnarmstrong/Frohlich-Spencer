/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ConditionLambdaGas
public import FroehlichSpencer.BKT.Surface.ConditionLambdaFracCorrelationLimit
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBGeneral
public import FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree
public import FroehlichSpencer.BKT.Surface.CoulombGasSummability
public import FroehlichSpencer.BKT.Surface.CoulombGasPartitionPos
import Mathlib.Tactic

/-!
# Bridge: the general fractional-charge correlation (1.23)

* `fracCorrelation_eq_region`: the (1.23) is the positive-vacancy gas estimate's `regionConditionLambdaFracCorrInternal`
  (expansion of `E(q + ξf)`, `q ↦ −q` symmetrization, every series convergent on the carrier).
* `fracCorrelation_self`: `G(a, a) = 1` (it consumes the positivity gate).
* `fracNumerator_summable`: the numerator series of (1.23) converges on the whole carrier.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ConditionLambdaFracCorrelation

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation
open FroehlichSpencer.BKT.Generic.Marked (dipoleMark dipoleGap dipoleGap_pos)
open FroehlichSpencer.BKT.Bridge.ConditionLambdaGas

section Frac

variable (Λ : Finset (ℤ × ℤ))

/--
**The bridge**: for even `λ`, the (1.23) is the positive-vacancy gas estimate's region correlation.
-/
theorem fracCorrelation_eq_region (β : ℝ) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q)
    (hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam) (hev : ∀ n, lam (-n) = lam n) (ξ : ℝ)
    (a b : Λ) :
    conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ Λ a b =
      regionConditionLambdaFracCorrInternal Λ β lam ξ a b := by
  unfold regionConditionLambdaFracCorrInternal
  simp only [a.2, b.2, and_self, ↓reduceDIte, Subtype.coe_eta]
  unfold freeConditionLambdaFracCorrInternal fullGasExpectationInternal
  set f₀ : Λ → ℝ := dipoleRealInternal a b with hf₀
  have hf : (fun j : Λ => (if j = a then ξ else 0) - (if j = b then ξ else 0)) = ξ • f₀ := by
    funext j
    simp only [hf₀, dipoleRealInternal, dipoleMark, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hSG : ∀ t : ℝ, Summable fun q : Λ → ℤ =>
      gasWeightInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β (fun _ => lam) q *
        Real.exp (t * ∑ j, |(q j : ℝ)|) :=
    fun t => (hS Λ t).congr fun q => by rw [coulombGasWeight_eq]
  set G : (Λ → ℤ) → ℝ := gasWeightInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
    (fun _ => lam) with hG
  set X : (Λ → ℤ) → ℝ := fun q => β * ξ * pairC Λ (fun j => (q j : ℝ)) f₀ with hX
  have hGneg : ∀ q, G (-q) = G q := fun q => gasWeight_neg _ β _ (fun _ n => hev n) q
  have hXneg : ∀ q, X (-q) = -X q := by
    intro q
    simp only [hX]
    have : (fun j => (((-q) j : ℤ) : ℝ)) = -(fun j => (q j : ℝ)) := by funext j; simp
    rw [this, pairC_neg_left]
    ring
  have hG0 : ∀ q, 0 ≤ G q := fun q => by
    rw [hG, ← coulombGasWeight_eq]; exact coulombGasWeight_nonneg hlam Λ q
  -- every series converges
  set M : ℝ := ∑ i : Λ, |∑ j : Λ, f₀ j * coulombPotential ((i : ℤ × ℤ) - j)| with hM
  have hXle : ∀ q, |X q| ≤ |β * ξ| * M * ∑ i, |(q i : ℝ)| := fun q => by
    simp only [hX]
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_pairC_le Λ q f₀) (abs_nonneg _)
  have hsumE : ∀ s : ℝ, |s| ≤ 1 → Summable fun q => G q * Real.exp (s * X q) := by
    intro s hs
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (hG0 q) (Real.exp_pos _).le)
      (fun q => mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hG0 q))
      (hSG (|β * ξ| * M))
    calc s * X q ≤ |s * X q| := le_abs_self _
      _ = |s| * |X q| := abs_mul _ _
      _ ≤ 1 * |X q| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ ≤ |β * ξ| * M * ∑ i, |(q i : ℝ)| := by rw [one_mul]; exact hXle q
  have hplus : Summable fun q => G q * Real.exp (X q) := by
    simpa using hsumE 1 (by norm_num)
  have hminus : Summable fun q => G q * Real.exp (-X q) := by
    simpa using hsumE (-1) (by norm_num)
  -- symmetrization
  have hflip : ∑' q, G q * Real.exp (-X q) = ∑' q, G q * Real.exp (X q) := by
    rw [← (Equiv.neg (Λ → ℤ)).tsum_eq (fun q => G q * Real.exp (X q))]
    refine tsum_congr fun q => ?_
    simp only [Equiv.neg_apply, hGneg, hXneg]
  have hcosh : ∑' q, G q * Real.cosh (X q) = ∑' q, G q * Real.exp (-X q) := by
    have : ∀ q, G q * Real.cosh (X q) = (G q * Real.exp (X q) + G q * Real.exp (-X q)) / 2 :=
      fun q => by rw [Real.cosh_eq]; ring
    rw [tsum_congr this, tsum_div_const, hplus.tsum_add hminus, ← hflip]
    ring
  -- the weights
  have hw : ∀ q : Λ → ℤ, (if ∑ j, q j = 0 then ∏ j, lam (q j) else 0) *
      Real.exp (-β * (pairC Λ (fun j => (q j : ℝ)) (fun j => (q j : ℝ)) / 2)) = G q := by
    intro q
    rw [hG, ← coulombGasWeight_eq]
    unfold coulombGasWeight pairC
    split_ifs <;> simp
  have hnum : ∑' q : Λ → ℤ, (if ∑ j, q j = 0 then ∏ j, lam (q j) else 0) *
      Real.exp (-β * (pairC Λ (fun j => (q j : ℝ) + (ξ • f₀) j)
        (fun j => (q j : ℝ) + (ξ • f₀) j) / 2)) =
      Real.exp (-(β * ξ ^ 2 * pairC Λ f₀ f₀ / 2)) * ∑' q, G q * Real.cosh (X q) := by
    rw [hcosh, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    have hsplit : (fun j => (q j : ℝ) + (ξ • f₀) j) = (fun j => (q j : ℝ)) + ξ • f₀ := rfl
    rw [hsplit, pairC_add_smul, ← hw q]
    simp only [hX]
    exact exp_split β ξ _ _ _ _
  have hden : coulombGasPartition β lam hS Λ =
      fullGasPartitionInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
        (fun _ => lam) := by
    unfold coulombGasPartition fullGasPartitionInternal
    exact tsum_congr fun q => coulombGasWeight_eq β lam Λ q
  have hdef : conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ Λ a b =
      (∑' q : Λ → ℤ, (if ∑ j, q j = 0 then ∏ j, lam (q j) else 0) *
        Real.exp (-β * (pairC Λ (fun j => (q j : ℝ) + (ξ • f₀) j)
          (fun j => (q j : ℝ) + (ξ • f₀) j) / 2))) / coulombGasPartition β lam hS Λ := by
    rw [← hf]
    rfl
  rw [hdef, hnum, hden, freeQuad_eq, mul_div_assoc]
  congr 2
  refine tsum_congr fun q => ?_
  change G q * Real.cosh (X q) =
    G q * Real.cosh (ξ * (β * freeChargePairingInternal (Subtype.val : Λ → ℤ × ℤ) f₀ q))
  rw [freeChargePairing_eq]
  simp only [hX]
  ring_nf

/-- At a single site the fractional dipole vanishes and `G_{ξ,Λ}(a, a) = Z/Z = 1`. -/
theorem fracCorrelation_self (β : ℝ) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0)
    (hS : IsCoulombGasSummable β lam) (ξ : ℝ) (a : Λ) :
    conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ Λ a a = 1 := by
  have hZ := FroehlichSpencer.BKT.coulombGasPartition_pos β lam hlam hlam0 hS Λ
  unfold conditionLambdaFracCorrelation
  simp only [sub_self, add_zero]
  rw [div_eq_one_iff_eq hZ.ne']
  unfold coulombGasPartition
  refine tsum_congr fun q => ?_
  unfold coulombGasWeight
  split_ifs <;> simp

/--
**The (1.23) numerator converges** on the whole public carrier of
`conditionLambdaFracCorrelation` (no evenness of `λ` needed): its terms are
`e^{−βξ²E(f)} w(q) e^{−βξ⟨q, Cf⟩}`, dominated by `w(q) e^{|β| M Σ|q_j|}`.
-/
theorem fracNumerator_summable (β : ℝ) (lam : ℤ → ℝ) (hS : IsCoulombGasSummable β lam) (ξ : ℝ)
    (a b : Λ) :
    Summable fun q : Λ → ℤ =>
      (if ∑ j, q j = 0 then ∏ j, lam (q j) else 0) *
        Real.exp (-β * ((∑ i, ∑ j,
          ((q i : ℝ) + ((if i = a then ξ else 0) - (if i = b then ξ else 0))) *
          ((q j : ℝ) + ((if j = a then ξ else 0) - (if j = b then ξ else 0))) *
            coulombPotential ((i : ℤ × ℤ) - j)) / 2)) := by
  set f : Λ → ℝ := fun j => (if j = a then ξ else 0) - (if j = b then ξ else 0) with hf
  set M : ℝ := ∑ i : Λ, |∑ j : Λ, f j * coulombPotential ((i : ℤ × ℤ) - j)|
  have key : ∀ q : Λ → ℤ,
      (if ∑ j, q j = 0 then ∏ j, lam (q j) else 0) *
        Real.exp (-β * ((∑ i, ∑ j, ((q i : ℝ) + f i) * ((q j : ℝ) + f j) *
          coulombPotential ((i : ℤ × ℤ) - j)) / 2)) =
      Real.exp (-(β * 1 ^ 2 * pairC Λ f f / 2)) *
        (coulombGasWeight β lam Λ q * Real.exp (-(β * 1 * pairC Λ (fun j => (q j : ℝ)) f))) := by
    intro q
    have h1 : (∑ i, ∑ j, ((q i : ℝ) + f i) * ((q j : ℝ) + f j) *
        coulombPotential ((i : ℤ × ℤ) - j)) =
        pairC Λ ((fun j => (q j : ℝ)) + (1 : ℝ) • f) ((fun j => (q j : ℝ)) + (1 : ℝ) • f) := by
      unfold pairC; simp
    rw [h1, pairC_add_smul, exp_split]
    congr 2
    unfold coulombGasWeight pairC
    split_ifs <;> simp
  refine Summable.of_norm_bounded
    (((hS Λ (|β| * M)).abs).mul_left (Real.exp (-(β * 1 ^ 2 * pairC Λ f f / 2)))) ?_
  intro q
  rw [key q, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
  have hp := abs_pairC_le Λ q f
  have : -(β * 1 * pairC Λ (fun j => (q j : ℝ)) f) ≤ |β| * |pairC Λ (fun j => (q j : ℝ)) f| := by
    rw [mul_one, ← abs_mul]; exact neg_le_abs _
  calc -(β * 1 * pairC Λ (fun j => (q j : ℝ)) f) ≤ |β| * |pairC Λ (fun j => (q j : ℝ)) f| := this
    _ ≤ |β| * (M * ∑ i, |(q i : ℝ)|) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ = |β| * M * ∑ i, |(q i : ℝ)| := by ring

end Frac

end FroehlichSpencer.BKT.Bridge.ConditionLambdaFracCorrelation

end
