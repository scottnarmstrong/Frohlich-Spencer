/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremB
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaFree
public import FroehlichSpencer.BKT.Coulomb.TheoremBLimit
import Mathlib.Tactic

/-!
# FS81 Theorem B for a restricted Condition-λ regime with free boundary conditions

For a physical Condition-λ law with `ε < min(1/16, η²/128)`, the fractional-charge correlation is
first bounded at every finite Fourier cutoff. Periodic squares transfer that bound to the
whole-plane potential on every finite set of sites. A Gaussian majorant for the `cosh` insertion
then removes the cutoff; the result is uniform in the finite region and passes to every
thermodynamic limit point. The full FS81 range `ε < 1/16` remains open in this implementation.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory Filter Topology FroehlichSpencer.BKT.Generic.Marked

/-! ### The finite-cutoff free correlation -/

section FreeCutoff

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The charge representation of the fractional correlation at Fourier cutoff `N`, for a finite
set of distinct lattice sites and the whole-plane potential. -/
def freeConditionLambdaFracCorrCutoffInternal (pos : V → ℤ × ℤ) (N : ℕ) (κ : ℝ)
    (lam : ℤ → ℝ) (ξ : ℝ) (o x : V) : ℝ :=
  Real.exp (-(κ * ξ ^ 2 * freeQuadInternal pos (dipoleRealInternal o x) / 2)) *
    gasExpectationInternal N (freePotentialOpInternal pos) κ (fun _ => lam)
      (fun q => Real.cosh (ξ * (κ * freeChargePairingInternal pos (dipoleRealInternal o x) q)))

/-- **Periodic-to-free transfer at fixed cutoff** for a general even physical Condition-λ law.
For each finite set of distinct sites, the periodic sine-Gordon correlation converges to the
whole-plane charge formula. -/
theorem tendsto_torus_conditionLambdaFracCorrCutoff (pos : V → ℤ × ℤ)
    (hpos : Function.Injective pos) (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (lam : ℤ → ℝ)
    (hev : ∀ n, lam (-n) = lam n) (hphys : PhysicalWeightInternal lam) (ξ : ℝ)
    (o x : V) (root : ∀ n, Fin (torusSideInternal n) × Fin (torusSideInternal n)) :
    Tendsto (fun n => weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusCutoffWeightsInternal pos n N lam)
        (fun φ => Real.cos (ξ * (φ (torusSiteMapInternal pos n o) -
          φ (torusSiteMapInternal pos n x)))))
      atTop (𝓝 (freeConditionLambdaFracCorrCutoffInternal pos N κ lam ξ o x)) := by
  set f := dipoleRealInternal o x with hf
  have hf0 : ∑ v, f v = 0 := sum_dipoleRealInternal o x
  have hobs : ∀ n (φ : Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℝ),
      ξ * (φ (torusSiteMapInternal pos n o) - φ (torusSiteMapInternal pos n x)) =
        ξ * ∑ j, φ j * latticePushInternal (torusSideInternal n) pos f j := by
    intro n φ
    congr 1
    rw [Finset.sum_congr rfl fun j _ => mul_comm (φ j) _, sum_latticePush_mul, hf,
      sum_dipoleRealInternal_mul]
    rfl
  have hrep : ∀ᶠ n in atTop,
      Real.exp (-(κ * ξ ^ 2 *
        (∑ v, f v * -(torusPullbackOpInternal pos n f v)) / 2)) *
        gasExpectationInternal N (torusPullbackOpInternal pos n) κ (fun _ => lam)
          (fun p => Real.cosh (ξ * (κ *
            ∑ v, (p v : ℝ) * -(torusPullbackOpInternal pos n f v)))) =
      weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ) (root n)
        (torusCutoffWeightsInternal pos n N lam)
        (fun φ => Real.cos (ξ * (φ (torusSiteMapInternal pos n o) -
          φ (torusSiteMapInternal pos n x)))) := by
    filter_upwards [eventually_injective_latticeToSquare pos hpos] with n hinj
    have hne : gasPartitionInternal N (torusPullbackOpInternal pos n) κ (fun _ => lam) ≠ 0 :=
      (gasPartition_pos N _ κ _ (fun _ => hphys.2)
        (fun j => by rw [hphys.1]; exact one_pos)).ne'
    simp_rw [hobs n]
    rw [weightedGFFExpectation_cos_sineGordon
      (squarePeriodic (torusSideInternal n))
      (squarePeriodic_connected _ (one_lt_torusSide n)) κ hκ (root n) N
      (fun j => regionWeightInternal (Finset.univ.image (torusSiteMapInternal pos n)) lam j)
      (fun j q => regionWeight_neg _ hev j q) (torusGreenOpInternal n)
      (isLaplacianPseudoinverse_torusGreenOp n)
      (latticePushInternal (torusSideInternal n) pos f)
      (by rw [sum_latticePush]; exact hf0) ξ,
      torus_cutoff_gasExpectation_eq pos n hinj N κ lam
        (fun y => Real.cosh (ξ * (κ * y))) f,
      ← sum_mul_neg_torusPullbackOp]
  refine Tendsto.congr' hrep ?_
  unfold freeConditionLambdaFracCorrCutoffInternal freeQuadInternal freeChargePairingInternal
  refine Tendsto.mul ((Real.continuous_exp.tendsto _).comp ?_) ?_
  · exact (((tendsto_sum_mul_neg_torusPullbackOp pos f f hf0).const_mul (κ * ξ ^ 2)).div_const
      2).neg
  · refine tendsto_gasExpectation_of_tendsto N _ _ κ _ _ _
      (fun p hp => tendsto_chargeEnergy_torusPullbackOp pos p hp) (fun p => ?_)
      (gasPartition_pos N _ κ (fun _ => lam) (fun _ => hphys.2)
        (fun _ => by rw [hphys.1]; exact one_pos)).ne'
    exact (Real.continuous_cosh.tendsto _).comp
      (((tendsto_sum_mul_neg_torusPullbackOp pos _ f hf0).const_mul κ).const_mul ξ)

end FreeCutoff

/-! ### Removing the frequency cutoff for a fractional insertion -/

section FullFree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The full free-boundary Condition-λ fractional correlation, defined by the whole-plane charge
formula. -/
def freeConditionLambdaFracCorrInternal (pos : V → ℤ × ℤ) (κ : ℝ) (lam : ℤ → ℝ)
    (ξ : ℝ) (o x : V) : ℝ :=
  Real.exp (-(κ * ξ ^ 2 * freeQuadInternal pos (dipoleRealInternal o x) / 2)) *
    fullGasExpectationInternal (freePotentialOpInternal pos) κ (fun _ => lam)
      (fun q => Real.cosh (ξ * (κ * freeChargePairingInternal pos (dipoleRealInternal o x) q)))

private theorem scalar_abs_mul_le {d u v : ℝ} (hd : 0 < d) :
    |u| * |v| ≤ d / 2 * v ^ 2 + u ^ 2 / (2 * d) := by
  have hden : 0 < 2 * d := by positivity
  have hsq : 2 * d * (|u| * |v|) ≤ d ^ 2 * |v| ^ 2 + |u| ^ 2 := by
    nlinarith [sq_nonneg (d * |v| - |u|)]
  have hsq' : 2 * d * (|u| * |v|) ≤ d ^ 2 * v ^ 2 + u ^ 2 := by
    simpa only [sq_abs] using hsq
  have hrewrite : d / 2 * v ^ 2 + u ^ 2 / (2 * d) =
      (d ^ 2 * v ^ 2 + u ^ 2) / (2 * d) := by
    field_simp
  rw [hrewrite, le_div_iff₀ hden]
  nlinarith [hsq']

/-- A linear charge insertion is absorbed by any positive Gaussian energy margin. -/
private theorem abs_scaled_pairing_le {V : Type*} [Fintype V] (q : V → ℤ) (h : V → ℝ)
    (b : ℝ) (hb : 0 < b) (B : ℝ) :
    |B * ∑ j, (q j : ℝ) * h j| ≤
      b / 2 * ∑ j, (q j : ℝ) ^ 2 +
        ∑ j, (B * h j) ^ 2 / (2 * (b / (Fintype.card V + 1))) := by
  let d := b / (Fintype.card V + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdb : d ≤ b := by
    dsimp [d]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Fintype.card V : ℝ) + 1)]
    have hnNat : 1 ≤ Fintype.card V + 1 := by omega
    have hn : (1 : ℝ) ≤ (Fintype.card V : ℝ) + 1 := by exact_mod_cast hnNat
    calc b = b * 1 := by ring
      _ ≤ b * ((Fintype.card V : ℝ) + 1) := mul_le_mul_of_nonneg_left hn hb.le
  calc
    |B * ∑ j, (q j : ℝ) * h j| = |∑ j, B * ((q j : ℝ) * h j)| := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j, |B * ((q j : ℝ) * h j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |B * h j| * |(q j : ℝ)| := by
      refine Finset.sum_congr rfl fun j _ => ?_
      calc |B * ((q j : ℝ) * h j)| = |B| * |(q j : ℝ)| * |h j| := by
            simp only [abs_mul]
            ring
        _ = |B * h j| * |(q j : ℝ)| := by
            rw [abs_mul]
            ring
    _ ≤ ∑ j, (d / 2 * (q j : ℝ) ^ 2 + (B * h j) ^ 2 / (2 * d)) :=
      Finset.sum_le_sum fun j _ => scalar_abs_mul_le hd
    _ = d / 2 * ∑ j, (q j : ℝ) ^ 2 +
        ∑ j, (B * h j) ^ 2 / (2 * d) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ b / 2 * ∑ j, (q j : ℝ) ^ 2 +
        ∑ j, (B * h j) ^ 2 / (2 * d) := by
      gcongr

omit [DecidableEq V] in
/-- Gaussian domination gives absolute summability of the full gas weight times the fractional
`cosh` observable. The multiplicative constant may depend on the finite observable; the required
threshold `a < κ c` depends only on the law and the energy coercivity. -/
theorem summable_gasWeight_mul_cosh {T : (V → ℝ) →ₗ[ℝ] V → ℝ} {κ c a C : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (lam : V → ℤ → ℝ)
    (hE : ∀ q : V → ℤ, ∑ j, q j = 0 →
      c * ∑ j, (q j : ℝ) ^ 2 ≤ chargeEnergyInternal T q)
    (hlam : ∀ j n, |lam j n| ≤ C * Real.exp (a * (n : ℝ) ^ 2))
    (hac : a < κ * c) (B : ℝ) (h : V → ℝ) :
    Summable fun q => gasWeightInternal T κ lam q *
      Real.cosh (B * ∑ j, (q j : ℝ) * h j) := by
  let b := κ * c - a
  have hb : 0 < b := by dsimp [b]; linarith
  let d := b / (Fintype.card V + 1)
  let K := ∑ j, (B * h j) ^ 2 / (2 * d)
  let M := C ^ Fintype.card V * Real.exp K
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbase := summable_intGaussianPiV V (half_pos hb)
  refine Summable.of_norm_bounded (hbase.mul_left M) fun q => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ Real.cosh (B * ∑ j, (q j : ℝ) * h j))]
  have hweight := abs_gasWeight_le T hκ hC lam hE hlam q
  have hlinear := abs_scaled_pairing_le q h b hb B
  have hq : 0 ≤ ∑ j, (q j : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcosh : Real.cosh (B * ∑ j, (q j : ℝ) * h j) ≤
      Real.exp |B * ∑ j, (q j : ℝ) * h j| := by
    rw [Real.cosh_eq]
    calc (Real.exp (B * ∑ j, (q j : ℝ) * h j) +
        Real.exp (-(B * ∑ j, (q j : ℝ) * h j))) / 2
        ≤ (Real.exp |B * ∑ j, (q j : ℝ) * h j| +
          Real.exp |B * ∑ j, (q j : ℝ) * h j|) / 2 := by
            apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
            exact add_le_add (Real.exp_le_exp.2 (le_abs_self _))
              (Real.exp_le_exp.2 (neg_le_abs _))
      _ = Real.exp |B * ∑ j, (q j : ℝ) * h j| := by ring
  have hgauss : intGaussianPiV V b q =
      Real.exp (-(b * ∑ j, (q j : ℝ) ^ 2)) := intGaussianPiV_eq b q
  have hbound : |gasWeightInternal T κ lam q| *
      Real.cosh (B * ∑ j, (q j : ℝ) * h j) ≤ M * intGaussianPiV V (b / 2) q := by
    calc |gasWeightInternal T κ lam q| * Real.cosh (B * ∑ j, (q j : ℝ) * h j)
        ≤ (C ^ Fintype.card V * intGaussianPiV V b q) *
            Real.exp |B * ∑ j, (q j : ℝ) * h j| :=
          mul_le_mul hweight hcosh (by positivity)
            (mul_nonneg (pow_nonneg hC _) (by unfold intGaussianPiV; positivity))
      _ = C ^ Fintype.card V * Real.exp (-(b * ∑ j, (q j : ℝ) ^ 2) +
            |B * ∑ j, (q j : ℝ) * h j|) := by
          calc _ = C ^ Fintype.card V *
                (Real.exp (-(b * ∑ j, (q j : ℝ) ^ 2)) *
                  Real.exp |B * ∑ j, (q j : ℝ) * h j|) := by rw [hgauss]; ring
            _ = _ := by rw [← Real.exp_add]
      _ ≤ C ^ Fintype.card V * Real.exp (-(b / 2 * ∑ j, (q j : ℝ) ^ 2) + K) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC _)
          apply Real.exp_le_exp.mpr
          dsimp [K, d] at hlinear ⊢
          linarith
      _ = M * intGaussianPiV V (b / 2) q := by
          have hgaussHalf : intGaussianPiV V (b / 2) q =
              Real.exp (-(b / 2 * ∑ j, (q j : ℝ) ^ 2)) := intGaussianPiV_eq (b / 2) q
          rw [hgaussHalf]
          dsimp [M]
          calc C ^ Fintype.card V * Real.exp (-(b / 2 * ∑ j, (q j : ℝ) ^ 2) + K) =
                C ^ Fintype.card V * (Real.exp K *
                  Real.exp (-(b / 2 * ∑ j, (q j : ℝ) ^ 2))) := by
                    rw [← Real.exp_add]
                    congr 1
                    ring_nf
            _ = C ^ Fintype.card V * Real.exp K *
                Real.exp (-(b / 2 * ∑ j, (q j : ℝ) ^ 2)) := by ring_nf
  exact hbound

/-- The cutoff fractional correlations converge to the full free charge formula, uniformly for
each fixed finite region. -/
theorem tendsto_freeConditionLambdaFracCorrCutoff (pos : V → ℤ × ℤ)
    (κ : ℝ)
    (lam : ℤ → ℝ) (hphys : PhysicalWeightInternal lam)
    (hGate : GateInternal (freePotentialOpInternal pos) κ (fun _ => lam))
    (ξ : ℝ) (o x : V) :
    Tendsto (fun N => freeConditionLambdaFracCorrCutoffInternal pos N κ lam ξ o x) atTop
      (𝓝 (freeConditionLambdaFracCorrInternal pos κ lam ξ o x)) := by
  let T := freePotentialOpInternal pos
  let f := dipoleRealInternal o x
  let h := fun j => -(T f j)
  let F := fun q : V → ℤ => Real.cosh (ξ * (κ * ∑ j, (q j : ℝ) * h j))
  have hden : Summable fun q : V → ℤ => gasWeightInternal T κ (fun _ => lam) q :=
    GateInternal.summable hGate
  obtain ⟨hκG, c, a, C, hC, hac, hE, hlam⟩ := hGate
  have hnum : Summable fun q : V → ℤ => gasWeightInternal T κ (fun _ => lam) q * F q := by
    simpa [T, F, h, mul_assoc] using
      (summable_gasWeight_mul_cosh hκG hC (fun _ => lam) hE hlam hac (ξ * κ) h)
  have hZpos : 0 < fullGasPartitionInternal T κ (fun _ => lam) := by
    have hZ := one_le_fullGasPartition hden (fun _ n => hphys.2 n) (fun _ => hphys.1)
    linarith
  have hN := tendsto_sum_chargeConfigs hnum
  have hZ := tendsto_sum_chargeConfigs hden
  have hEcut : Tendsto (fun N => gasExpectationInternal N T κ (fun _ => lam) F) atTop
      (𝓝 (fullGasExpectationInternal T κ (fun _ => lam) F)) := by
    unfold gasExpectationInternal gasPartitionInternal fullGasExpectationInternal
    exact hN.div hZ hZpos.ne'
  unfold freeConditionLambdaFracCorrCutoffInternal freeConditionLambdaFracCorrInternal
    freeQuadInternal freeChargePairingInternal
  simpa [F, T, h] using tendsto_const_nhds.mul hEcut

end FullFree

/-! ### Finite free regions -/

section TheoremB

/-- The Condition-λ fractional correlation on a finite lattice region, with free boundary
conditions. -/
def regionConditionLambdaFracCorrInternal (Λ : Finset (ℤ × ℤ)) (κ : ℝ) (lam : ℤ → ℝ)
    (ξ : ℝ) (x y : ℤ × ℤ) : ℝ :=
  if h : x ∈ Λ ∧ y ∈ Λ then
    freeConditionLambdaFracCorrInternal (fun v : Λ => (v : ℤ × ℤ)) κ lam ξ
      ⟨x, h.1⟩ ⟨y, h.2⟩
  else 0

/-- **FS81 Theorem B in the restricted Condition-λ regime, free boundary condition.** For fixed
growth data `(C, α, ε)` satisfying `ε < min(1/16, η²/128)`, the threshold depends on these data
and the fractional gap `η`, but works for every physical law satisfying them, finite region,
frequency cutoff and site pair. The same power bound holds after removing the cutoff. -/
theorem coulombB_conditionLambda_free :
    ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 →
      ∀ η : ℝ, 0 < η → ε < η ^ 2 / 128 →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
          ConditionLambdaInternal C α ε κ lam → PhysicalWeightInternal lam →
          ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
            x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
            0 ≤ regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ∧
              regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ≤
                2 * ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                  (-(c * η ^ 2 * κ))) := by
  obtain ⟨cB, hcB, hSquare⟩ := markedConditionLambdaSquareBound_exists
  let c := cB / Real.log 2
  have hc : 0 < c := div_pos hcB (Real.log_pos (by norm_num))
  refine ⟨c, hc, fun C α ε hC hα hε η hη hεη => ?_⟩
  obtain ⟨κB, hκB, hSquare⟩ := hSquare C α ε hC hα hε η hη hεη
  obtain ⟨κA, hκA, hFree⟩ := free_conditionLambda_bound (1 / 2) (by norm_num) C α ε hε
  let κ₀ := max κB κA
  have hκ₀ : 0 < κ₀ := by dsimp [κ₀]; exact lt_of_lt_of_le hκA (le_max_right _ _)
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ lam hlam hphys Λ ξ x y hx hy hxy hξ0 hξ1 hηξ => ?_⟩
  have hκB' : κB < κ := lt_of_le_of_lt (le_max_left _ _) hκκ₀
  have hκA' : κA < κ := lt_of_le_of_lt (le_max_right _ _) hκκ₀
  have hκ : 0 < κ := (hκ₀.trans hκκ₀)
  have hfree := hFree Λ κ hκA' lam hlam hphys.1
  have hgate : GateInternal
      (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ (fun _ => lam) := hfree.2.1
  let pos : Λ → ℤ × ℤ := Subtype.val
  let ox : Λ := ⟨x, hx⟩
  let oy : Λ := ⟨y, hy⟩
  have hpos : Function.Injective pos := Subtype.val_injective
  have hox : ox ≠ oy := fun he => hxy (congrArg Subtype.val he)
  let B := 2 * (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
    (-(c * η ^ 2 * κ))
  have hCutBound : ∀ N, 0 ≤ freeConditionLambdaFracCorrCutoffInternal pos N κ lam ξ ox oy ∧
      freeConditionLambdaFracCorrCutoffInternal pos N κ lam ξ ox oy ≤ B := by
    intro N
    have hT := tendsto_torus_conditionLambdaFracCorrCutoff pos hpos κ hκ N lam hlam.1 hphys ξ
      ox oy (fun n => torusSiteMapInternal pos n ox)
    have hev : ∀ᶠ n in atTop,
        0 ≤ weightedGFFExpectation (squarePeriodic (torusSideInternal n))
            (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ)
            (torusSiteMapInternal pos n ox)
            (torusCutoffWeightsInternal pos n N lam)
            (fun φ => Real.cos (ξ * (φ (torusSiteMapInternal pos n ox) -
              φ (torusSiteMapInternal pos n oy)))) ∧
          weightedGFFExpectation (squarePeriodic (torusSideInternal n))
            (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ)
            (torusSiteMapInternal pos n ox)
            (torusCutoffWeightsInternal pos n N lam)
            (fun φ => Real.cos (ξ * (φ (torusSiteMapInternal pos n ox) -
              φ (torusSiteMapInternal pos n oy)))) ≤ B := by
      filter_upwards [eventually_injective_latticeToSquare pos hpos,
        eventually_latticeDistance_torus (pos ox) (pos oy)] with n hinj hdist
      let site := torusSiteMapInternal pos n
      let A := Finset.univ.image site
      have hne : site ox ≠ site oy := fun h => hox (hinj h)
      obtain ⟨hZ, hI⟩ := ((hSquare (torusSideInternal n) (one_lt_torusSide n)).2
        (even_torusSide n)) κ hκB' hκ lam hlam hphys.1 N A (site ox) (site ox) (site oy)
        hne ξ hξ0 hξ1 hηξ
      let G := squarePeriodic (torusSideInternal n)
      let hG := squarePeriodic_connected _ (one_lt_torusSide n)
      let root := site ox
      let weights : (Fin (torusSideInternal n) × Fin (torusSideInternal n)) → ℝ → ℝ :=
        fun j => sineGordonWeightInternal N (regionWeightInternal A lam j)
      let obs : ((Fin (torusSideInternal n) × Fin (torusSideInternal n)) → ℝ) → ℝ :=
        fun φ => Real.cos (ξ * (φ (site ox) - φ (site oy)))
      have hnorm := weightedGFFNormalizer_eq G hG κ⁻¹ (inv_pos.2 hκ) root weights
      have hcorrEq : weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) root weights obs =
          (∫ φ, obs φ * ∏ j, weights j (φ j) ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) root) /
            weightedGFFNormalizer G hG κ⁻¹ (inv_pos.2 hκ) root weights := by
        rw [weightedGFFExpectation_eq, ← hnorm]
      let f := dipoleRealInternal (site ox) (site oy)
      have hsum : ∀ φ : (Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℝ),
          ∑ j, φ j * f j = φ (site ox) - φ (site oy) := by
        intro φ
        calc ∑ j, φ j * f j = ∑ j, f j * φ j := by
              exact Finset.sum_congr rfl fun j _ => mul_comm _ _
          _ = _ := sum_dipoleRealInternal_mul _ _ φ
      have hnum : 0 ≤ ∫ φ, obs φ * ∏ j, weights j (φ j)
          ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) root := by
        have hbase := integral_cos_mul_prod_sineGordonWeight_nonneg G hG κ⁻¹
          (inv_pos.2 hκ) root N (fun j => regionWeightInternal A lam j)
          (fun j q => regionWeight_neg A hlam.1 j q)
          (fun j q => regionWeight_nonneg A hphys.2 j q) f (sum_dipoleRealInternal _ _) ξ
        simpa [obs, weights, hsum] using hbase
      have hdist' : latticeDistance .periodic (torusSideInternal n) (site ox) (site oy) =
          (y.1 - x.1).natAbs + (y.2 - x.2).natAbs := hdist
      have hdpos : (0 : ℝ) <
          ((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 := by positivity
      have hexp : Real.exp (-(cB * η ^ 2 * κ) * Real.logb 2
          (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1)) =
          (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
            (-(c * η ^ 2 * κ)) := by
        rw [Real.rpow_def_of_pos hdpos, Real.logb]
        congr 1
        dsimp [c]
        ring
      have hI' := hI
      rw [hdist'] at hI'
      have hnumle : (∫ φ, obs φ * ∏ j, weights j (φ j)
          ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) root) ≤
          B * weightedGFFNormalizer G hG κ⁻¹ (inv_pos.2 hκ) root weights := by
        calc _ ≤ |∫ φ, obs φ * ∏ j, weights j (φ j)
              ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) root| := le_abs_self _
          _ ≤ 2 * Real.exp (-(cB * η ^ 2 * κ) * Real.logb 2
                (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1)) *
                weightedGFFNormalizer G hG κ⁻¹ (inv_pos.2 hκ) root weights := by
                  simpa [obs, weights, A, site] using hI'
          _ = B * weightedGFFNormalizer G hG κ⁻¹ (inv_pos.2 hκ) root weights := by
                rw [hexp]
      have hcorr0 : 0 ≤ weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) root weights obs := by
        rw [hcorrEq]
        exact div_nonneg hnum hZ.le
      have hcorrle : weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) root weights obs ≤ B := by
        rw [hcorrEq]
        exact (div_le_iff₀ hZ).2 hnumle
      simpa [G, hG, root, weights, obs] using ⟨hcorr0, hcorrle⟩
    exact ⟨ge_of_tendsto hT (hev.mono fun n h => h.1),
      le_of_tendsto hT (hev.mono fun n h => h.2)⟩
  have hTfull := tendsto_freeConditionLambdaFracCorrCutoff pos κ lam hphys hgate ξ ox oy
  have hbound : 0 ≤ freeConditionLambdaFracCorrInternal pos κ lam ξ ox oy ∧
      freeConditionLambdaFracCorrInternal pos κ lam ξ ox oy ≤ B :=
    ⟨ge_of_tendsto hTfull (Eventually.of_forall fun N => (hCutBound N).1),
      le_of_tendsto hTfull (Eventually.of_forall fun N => (hCutBound N).2)⟩
  unfold regionConditionLambdaFracCorrInternal
  simpa [regionConditionLambdaFracCorrInternal, pos, ox, oy, hx, hy, B] using hbound

/-- **Every thermodynamic limit point** of free-boundary Condition-λ correlations in the restricted
growth range satisfies the same power bound. The bound is uniform in the finite regions. -/
theorem coulombB_conditionLambda_thermodynamicLimit :
    ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 →
      ∀ η : ℝ, 0 < η → ε < η ^ 2 / 128 →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
        ConditionLambdaInternal C α ε κ lam → PhysicalWeightInternal lam →
        ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
        ∀ x y : ℤ × ℤ, x ≠ y → ∀ Λs : ℕ → Finset (ℤ × ℤ),
          (∀ k, x ∈ Λs k ∧ y ∈ Λs k) →
          (∀ k, 0 ≤ regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ∧
            regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ≤
              2 * (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                (-(c * η ^ 2 * κ))) ∧
          (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto (fun k => regionConditionLambdaFracCorrInternal (Λs (φ k)) κ lam ξ x y)
              atTop (𝓝 ℓ)) ∧
          ∀ ℓ : ℝ, MapClusterPt ℓ atTop
              (fun k => regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y) →
            0 ≤ ℓ ∧ ℓ ≤
              2 * (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                (-(c * η ^ 2 * κ)) := by
  obtain ⟨c, hc, hfree⟩ := coulombB_conditionLambda_free
  refine ⟨c, hc, fun C α ε hC hα hε η hη hεη => ?_⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := hfree C α ε hC hα hε η hη hεη
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ lam hlam hphys ξ hξ0 hξ1 hηξ x y hxy Λs hΛs => ?_⟩
  let B : ℝ := 2 * (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
    (-(c * η ^ 2 * κ))
  have hk : ∀ k, 0 ≤ regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ∧
      regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ≤ B := by
    intro k
    exact hF κ hκκ₀ lam hlam hphys (Λs k) ξ x y (hΛs k).1 (hΛs k).2 hxy hξ0 hξ1 hηξ
  have hmem : ∀ k, regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ∈ Set.Icc 0 B :=
    fun k => hk k
  refine ⟨hk, ?_, fun ℓ hℓ =>
    isClosed_Icc.mem_of_mapClusterPt hℓ (Eventually.of_forall hmem)⟩
  obtain ⟨ℓ, -, φ, hφ, hT⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 B) hmem
  exact ⟨ℓ, φ, hφ, hT⟩

end TheoremB

end FroehlichSpencer.BKT.Coulomb
