/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.IntegerGFFObservable
public import FroehlichSpencer.BKT.Bridge.IntegerGFFSymmetry
public import FroehlichSpencer.BKT.Bridge.SquareCarriers
public import FroehlichSpencer.BKT.Gaussian.IntegerField
public import FroehlichSpencer.BKT.Potential.NashWilliams
public import FroehlichSpencer.BKT.Roots.IntegerGFFSecondMoment
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverse
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverseWellDefined
public import FroehlichSpencer.BKT.Surface.SquareFree
public import FroehlichSpencer.BKT.Surface.SquarePeriodic
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Finite second moments of integer GFF linear observables

For a finite connected multigraph, every linear observable of the pinned
integer Gaussian free field has a summable square-weighted density. This is
the integrability input for the second-order moment consequence of KP (1.6),
p. 3.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

open Multigraph MeasureTheory
open Filter Topology

universe u v

/-- A real square is dominated by two exponential tilts. -/
private theorem sq_le_four_exp_add (x : ℝ) :
    x ^ 2 ≤ 4 * (Real.exp x + Real.exp (-x)) := by
  have hu : 0 ≤ |x| / 2 := by positivity
  have hlin : 1 + |x| / 2 ≤ Real.exp (|x| / 2) := by
    simpa [add_comm] using Real.add_one_le_exp (|x| / 2)
  have hsq : (1 + |x| / 2) ^ 2 ≤ Real.exp (|x| / 2) ^ 2 :=
    by simpa only [← pow_two] using mul_self_le_mul_self (by positivity) hlin
  have hexp : Real.exp (|x| / 2) ^ 2 = Real.exp |x| := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hpoly : x ^ 2 ≤ 4 * Real.exp |x| := by
    rw [← sq_abs x]
    nlinarith [hsq, hexp]
  have habs : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · have hx' : x < 0 := lt_of_not_ge hx
      rw [abs_of_neg hx']
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  nlinarith

private theorem cosh_sub_one_le_half_sq_exp_abs (x : ℝ) :
    Real.cosh x - 1 ≤ x ^ 2 / 2 * Real.exp |x| := by
  let a := |x|
  have ha : 0 ≤ a := abs_nonneg _
  have hline : 1 - a ≤ Real.exp (-a) := by
    have h := Real.add_one_le_exp (-a)
    linarith
  have hexp : Real.exp a * Real.exp (-a) = 1 := by
    rw [← Real.exp_add]
    simp
  have hdiff : Real.exp a - 1 ≤ a * Real.exp a := by
    have hmul := mul_le_mul_of_nonneg_left hline (Real.exp_pos a).le
    nlinarith [hmul, hexp]
  have hsq : (Real.exp a - 1) ^ 2 ≤ (a * Real.exp a) ^ 2 := by
    have hnonneg : 0 ≤ Real.exp a - 1 := by
      have h := Real.add_one_le_exp a
      linarith
    simpa only [pow_two] using mul_self_le_mul_self hnonneg hdiff
  have hid : Real.cosh x - 1 =
      (Real.exp a - 1) ^ 2 / (2 * Real.exp a) := by
    rw [← Real.cosh_abs x, Real.cosh_eq]
    dsimp [a]
    field_simp [ne_of_gt (Real.exp_pos |x|)]
    nlinarith [hexp]
  calc
    Real.cosh x - 1 = (Real.exp a - 1) ^ 2 / (2 * Real.exp a) := hid
    _ ≤ (a * Real.exp a) ^ 2 / (2 * Real.exp a) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    _ = x ^ 2 / 2 * Real.exp |x| := by
      dsimp [a]
      field_simp [ne_of_gt (Real.exp_pos |x|)]
      rw [sq_abs]

private theorem cosh_difference_quotient_bound (t x : ℝ)
    (ht : |t| ≤ 1) (htne : t ≠ 0) :
    (Real.cosh (t * x) - 1) / t ^ 2 ≤ x ^ 2 / 2 * Real.exp |x| := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero htne
  have habs : |t * x| ≤ |x| := by
    rw [abs_mul]
    calc
      |t| * |x| ≤ 1 * |x| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      _ = |x| := one_mul _
  have hscalar := cosh_sub_one_le_half_sq_exp_abs (t * x)
  have hexp : Real.exp |t * x| ≤ Real.exp |x| := Real.exp_le_exp.mpr habs
  have hfactor : 0 ≤ (t * x) ^ 2 / 2 := by positivity
  have hnum : (Real.cosh (t * x) - 1) ≤
      (t * x) ^ 2 / 2 * Real.exp |x| := by
    calc
      Real.cosh (t * x) - 1 ≤ (t * x) ^ 2 / 2 * Real.exp |t * x| := hscalar
      _ ≤ (t * x) ^ 2 / 2 * Real.exp |x| :=
        mul_le_mul_of_nonneg_left hexp hfactor
  calc
    (Real.cosh (t * x) - 1) / t ^ 2 ≤
        ((t * x) ^ 2 / 2 * Real.exp |x|) / t ^ 2 :=
      (div_le_div_iff_of_pos_right ht2).2 hnum
    _ = x ^ 2 / 2 * Real.exp |x| := by
      field_simp [htne]

private theorem exp_add_abs_le_exp_two_add (x : ℝ) :
    (Real.exp x + Real.exp (-x)) * Real.exp |x| ≤
      Real.exp (2 * x) + 2 + Real.exp (-2 * x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, add_mul]
    have h₁ : Real.exp x * Real.exp x = Real.exp (2 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h₂ : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    rw [h₁, h₂]
    nlinarith [Real.exp_pos (-2 * x)]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hx', add_mul]
    have h₁ : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    have h₂ : Real.exp (-x) * Real.exp (-x) = Real.exp (-2 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h₁, h₂]
    nlinarith [Real.exp_pos (2 * x)]

/-- A summable exponential majorant for the centered second difference of
the pinned IGFF cosh moment. -/
private theorem summable_igffCoshDifferenceMajorant {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] (G : Multigraph V E)
    (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V) (f : V → ℝ) :
    Summable (fun m : pinnedIntegerField V root =>
      4 * (Real.exp (2 * pairing (fun j => (m.1 j : ℝ)) f) + 2 +
        Real.exp (-2 * pairing (fun j => (m.1 j : ℝ)) f)) * igffWeight G β m) := by
  let X : pinnedIntegerField V root → ℝ := fun m =>
    pairing (fun j => (m.1 j : ℝ)) f
  have hweight := summable_igffWeight G hG β hβ root
  have hplus := summable_igffTiltedWeight G hG β hβ root (2 • f)
  have hminus := summable_igffTiltedWeight G hG β hβ root (-2 • f)
  have hplus' : Summable (fun m : pinnedIntegerField V root =>
      Real.exp (2 * X m) * igffWeight G β m) := by
    have hp (m : pinnedIntegerField V root) :
        pairing (fun j => (m.1 j : ℝ)) (2 • f) = 2 * X m := by
      unfold Multigraph.pairing
      simp only [Pi.smul_apply]
      calc
        _ = (∑ j : V, (m.1 j : ℝ) * f j) * 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by
          dsimp [X, Multigraph.pairing]
          ring
    have hplus0 : Summable (fun m : pinnedIntegerField V root =>
        Real.exp (pairing (fun j => (m.1 j : ℝ)) (2 • f)) *
          igffWeight G β m) := by
      simpa [igffTiltedWeight] using hplus
    simpa only [hp] using hplus0
  have hminus' : Summable (fun m : pinnedIntegerField V root =>
      Real.exp (-2 * X m) * igffWeight G β m) := by
    have hp (m : pinnedIntegerField V root) :
        pairing (fun j => (m.1 j : ℝ)) (-2 • f) = -2 * X m := by
      unfold Multigraph.pairing
      simp only [Pi.smul_apply]
      calc
        _ = (∑ j : V, (m.1 j : ℝ) * f j) * (-2) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by
          dsimp [X, Multigraph.pairing]
          ring
    have hminus0 : Summable (fun m : pinnedIntegerField V root =>
        Real.exp (pairing (fun j => (m.1 j : ℝ)) (-2 • f)) *
          igffWeight G β m) := by
      simpa [igffTiltedWeight] using hminus
    simpa only [hp] using hminus0
  have hmajor : Summable (fun m : pinnedIntegerField V root =>
      4 * (Real.exp (2 * X m) * igffWeight G β m +
        2 * igffWeight G β m + Real.exp (-2 * X m) * igffWeight G β m)) :=
    ((hplus'.add (hweight.mul_left 2)).add hminus').mul_left 4
  convert hmajor using 1
  funext m
  dsimp [X]
  ring

/-- The normalized pinned IGFF expectation of the centered cosh quotient
converges to half of its second moment. This is the discrete dominated
convergence step in the implication (1.6) ⇒ (1.7) (KP p. 3). -/
theorem tendsto_igffExpectation_cosh_difference_quotient
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (f : V → ℝ) :
    Tendsto (fun t : ℝ => igffExpectation G hG β hβ root
        (fun m => (Real.cosh (t * pairing (fun j => (m.1 j : ℝ)) f) - 1) / t ^ 2))
      (𝓝[≠] 0)
      (𝓝 (igffExpectation G hG β hβ root
        (fun m => (pairing (fun j => (m.1 j : ℝ)) f) ^ 2 / 2))) := by
  let X : pinnedIntegerField V root → ℝ := fun m =>
    pairing (fun j => (m.1 j : ℝ)) f
  let q : ℝ → pinnedIntegerField V root → ℝ := fun t m =>
    (Real.cosh (t * X m) - 1) / t ^ 2
  let bound : pinnedIntegerField V root → ℝ := fun m =>
    4 * (Real.exp (2 * X m) + 2 + Real.exp (-2 * X m)) * igffWeight G β m
  have hMajor := summable_igffCoshDifferenceMajorant G hG β hβ root f
  have hpoint (m : pinnedIntegerField V root) :
      Tendsto (fun t : ℝ => q t m) (𝓝[≠] 0)
        (𝓝 (X m ^ 2 / 2)) := by
    simpa [q, X] using tendsto_cosh_sub_one_div_sq (X m)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| ≤ 1 := by
    have hsmall' : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Set.Icc (-1) 1 :=
      Icc_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hsmall'.filter_mono nhdsWithin_le_nhds] with t ht
    exact abs_le.mpr ht
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ m,
      ‖q t m * igffWeight G β m‖ ≤ bound m := by
    filter_upwards [hsmall] with t ht m
    have hw : 0 < igffWeight G β m := Real.exp_pos _
    have hqnonneg : 0 ≤ q t m := by
      by_cases ht0 : t = 0
      · simp [q, ht0]
      · have hnum : 0 ≤ Real.cosh (t * X m) - 1 := by
          linarith [Real.one_le_cosh (t * X m)]
        exact div_nonneg hnum (sq_nonneg t)
    have hquot : q t m ≤ X m ^ 2 / 2 * Real.exp |X m| := by
      by_cases ht0 : t = 0
      · simp [q, ht0]
        positivity
      · exact cosh_difference_quotient_bound t (X m) ht ht0
    have hsq := sq_le_four_exp_add (X m)
    have hmajorX := exp_add_abs_le_exp_two_add (X m)
    have hXbound : X m ^ 2 * Real.exp |X m| ≤
        4 * (Real.exp (2 * X m) + 2 + Real.exp (-2 * X m)) := by
      calc
        X m ^ 2 * Real.exp |X m| ≤
            4 * (Real.exp (X m) + Real.exp (-X m)) * Real.exp |X m| :=
          mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
        _ = 4 * ((Real.exp (X m) + Real.exp (-X m)) * Real.exp |X m|) := by ring
        _ ≤ 4 * (Real.exp (2 * X m) + 2 + Real.exp (-2 * X m)) := by
          exact mul_le_mul_of_nonneg_left hmajorX
            (by positivity : (0 : ℝ) ≤ 4)
    have hquot' : q t m ≤ 4 *
        (Real.exp (2 * X m) + 2 + Real.exp (-2 * X m)) := by
      calc
        q t m ≤ X m ^ 2 / 2 * Real.exp |X m| := hquot
        _ ≤ X m ^ 2 * Real.exp |X m| := by
          exact mul_le_mul_of_nonneg_right
            (div_le_self (sq_nonneg _) (by norm_num : (1 : ℝ) ≤ 2))
            (Real.exp_pos _).le
        _ ≤ _ := hXbound
    have hterm : 0 ≤ q t m * igffWeight G β m := mul_nonneg hqnonneg hw.le
    rw [Real.norm_of_nonneg hterm]
    dsimp [bound]
    exact mul_le_mul_of_nonneg_right hquot' hw.le
  have htsum := tendsto_tsum_of_dominated_convergence hMajor
    (fun m => (hpoint m).mul_const (igffWeight G β m)) hbound
  have hnorm : Tendsto
      (fun t : ℝ => igffExpectation G hG β hβ root (fun m => q t m))
      (𝓝[≠] 0)
      (𝓝 (igffExpectation G hG β hβ root (fun m => X m ^ 2 / 2))) := by
    unfold igffExpectation
    change Tendsto (fun t => (∑' m : pinnedIntegerField V root,
      q t m * igffWeight G β m) / igffPartitionFunction G β root)
      (𝓝[≠] 0)
      (𝓝 ((∑' m : pinnedIntegerField V root,
        (X m ^ 2 / 2) * igffWeight G β m) / igffPartitionFunction G β root))
    exact htsum.div_const (igffPartitionFunction G β root)
  simpa [q, X, igffExpectation] using hnorm

/-- The square of a linear observable is summable against the pinned IGFF
weight. The proof uses the Gaussian exponential-tilt majorant from
`Gaussian/IntegerField.lean` at the two opposite tilts. -/
theorem summable_igffPairing_sq_mul_weight {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] (G : Multigraph V E)
    (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V) (f : V → ℝ) :
    Summable (fun m : pinnedIntegerField V root =>
      (pairing (fun j => (m.1 j : ℝ)) f) ^ 2 * igffWeight G β m) := by
  let X : pinnedIntegerField V root → ℝ := fun m =>
    pairing (fun j => (m.1 j : ℝ)) f
  have hplus := summable_igffTiltedWeight G hG β hβ root f
  have hminus := summable_igffTiltedWeight G hG β hβ root (-f)
  have hmajor : Summable (fun m : pinnedIntegerField V root =>
      4 * (igffTiltedWeight G β f m + igffTiltedWeight G β (-f) m)) :=
    (hplus.add hminus).mul_left 4
  refine hmajor.of_norm_bounded ?_
  intro m
  have hneg : pairing (fun j => (m.1 j : ℝ)) (-f) = -X m := by
    simp [X, pairing, Finset.sum_neg_distrib]
  have hnonneg : 0 ≤ X m ^ 2 * igffWeight G β m :=
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hnonneg]
  change X m ^ 2 * igffWeight G β m ≤ _
  rw [igffTiltedWeight, igffTiltedWeight, hneg]
  have hw : 0 ≤ igffWeight G β m := (Real.exp_pos _).le
  have hsq := mul_le_mul_of_nonneg_right (sq_le_four_exp_add (X m)) hw
  calc
    X m ^ 2 * igffWeight G β m ≤
        4 * (Real.exp (X m) + Real.exp (-X m)) * igffWeight G β m := hsq
    _ = 4 * (Real.exp (X m) * igffWeight G β m +
        Real.exp (-X m) * igffWeight G β m) := by ring

/-- The absolute value of a linear observable is summable under the pinned
IGFF weight. -/
theorem summable_igffPairing_abs_mul_weight {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] (G : Multigraph V E)
    (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V) (f : V → ℝ) :
    Summable (fun m : pinnedIntegerField V root =>
      |pairing (fun j => (m.1 j : ℝ)) f| * igffWeight G β m) := by
  let X : pinnedIntegerField V root → ℝ := fun m =>
    pairing (fun j => (m.1 j : ℝ)) f
  have hsq := summable_igffPairing_sq_mul_weight G hG β hβ root f
  have hw := summable_igffWeight G hG β hβ root
  have hmajor : Summable (fun m : pinnedIntegerField V root =>
      (X m ^ 2 + 1) * igffWeight G β m) := by
    convert hsq.add hw using 1
    ext m
    ring
  refine hmajor.of_norm_bounded ?_
  intro m
  have hnonneg : 0 ≤ |X m| * igffWeight G β m :=
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hnonneg]
  have habs : |X m| ≤ X m ^ 2 + 1 := by
    have h := sq_nonneg (|X m| - 1 / 2)
    nlinarith [h, sq_abs (X m)]
  have hwpos : 0 ≤ igffWeight G β m := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right habs hwpos

/--
The -law Bochner integral of a linear observable is its normalized
pinned-lattice expectation.

The absolute summability bound justifies the
signed integral and its positive/negative-part decomposition (KP p. 3).
-/
theorem integerGFFLaw_integral_pairing_eq_igffExpectation
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) (f : V → ℝ) :
    (∫ m, pairing (fun j => (m j : ℝ)) f
      ∂integerGFFLaw G hG β hβ root) =
      igffExpectation G (by
        change G.toSimpleGraph.Connected
        exact hG) β hβ root
        (fun m => pairing (fun j => (m.1 j : ℝ)) f) := by
  classical
  change G.Connected at hG
  let X : (V → ℤ) → ℝ := fun m => pairing (fun j => (m j : ℝ)) f
  let Xp : pinnedIntegerField V root → ℝ := fun m => X m.1
  let P : (V → ℤ) → ℝ := fun m => max (X m) 0
  let N : (V → ℤ) → ℝ := fun m => max (-X m) 0
  have hAbs : Summable (fun m : pinnedIntegerField V root =>
      |Xp m| * igffWeight G β m) :=
    summable_igffPairing_abs_mul_weight G hG β hβ root f
  have hPos : Summable (fun m : pinnedIntegerField V root =>
      P m.1 * igffWeight G β m) := hAbs.of_norm_bounded (by
    intro m
    have hnonneg : 0 ≤ P m.1 * igffWeight G β m :=
      mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hnonneg]
    have hp : P m.1 ≤ |Xp m| := by
      dsimp [P]
      exact max_le (le_abs_self _) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)
  have hNeg : Summable (fun m : pinnedIntegerField V root =>
      N m.1 * igffWeight G β m) := hAbs.of_norm_bounded (by
    intro m
    have hnonneg : 0 ≤ N m.1 * igffWeight G β m :=
      mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hnonneg]
    have hn : N m.1 ≤ |Xp m| := by
      dsimp [N]
      calc
        max (-Xp m) 0 ≤ |-Xp m| := max_le (le_abs_self _) (abs_nonneg _)
        _ = |Xp m| := abs_neg _
    exact mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le)
  have hP : ∀ m : V → ℤ, 0 ≤ P m :=
    fun m => le_max_right _ _
  have hN : ∀ m : V → ℤ, 0 ≤ N m :=
    fun m => le_max_right _ _
  have hPlaw := integerGFFLaw_lintegral_ofReal_eq_igffExpectation
    G hG β hβ root P hP hPos
  have hNlaw := integerGFFLaw_lintegral_ofReal_eq_igffExpectation
    G hG β hβ root N hN hNeg
  have hAbsLaw := integerGFFLaw_lintegral_ofReal_eq_igffExpectation
    G hG β hβ root (fun m => |X m|) (fun _ => abs_nonneg _) hAbs
  have hmeasX : AEStronglyMeasurable X (integerGFFLaw G hG β hβ root) :=
    (measurable_of_countable X).aestronglyMeasurable
  have hAbsInt : Integrable (fun m => |X m|) (integerGFFLaw G hG β hβ root) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (f := fun m => |X m|) (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ (fun _ => abs_nonneg _))).mp
    rw [hAbsLaw]
    exact ENNReal.ofReal_ne_top
  have hXint : Integrable X (integerGFFLaw G hG β hβ root) :=
    hAbsInt.mono' hmeasX (ae_of_all _ (fun _ => le_of_eq (Real.norm_eq_abs _)))
  have hPint : Integrable P (integerGFFLaw G hG β hβ root) := hXint.pos_part
  have hNint : Integrable N (integerGFFLaw G hG β hβ root) :=
    (hXint.neg).pos_part
  have hPnonneg : 0 ≤ᵐ[integerGFFLaw G hG β hβ root] P :=
    ae_of_all _ (fun _ => le_max_right _ _)
  have hNnonneg : 0 ≤ᵐ[integerGFFLaw G hG β hβ root] N :=
    ae_of_all _ (fun _ => le_max_right _ _)
  have hPint' := ofReal_integral_eq_lintegral_ofReal hPint hPnonneg
  have hNint' := ofReal_integral_eq_lintegral_ofReal hNint hNnonneg
  have hPexpect : 0 ≤ igffExpectation G hG β hβ root (fun m => P m.1) := by
    unfold igffExpectation
    apply div_nonneg
    · exact tsum_nonneg fun m => mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
    · exact (igffPartitionFunction_pos G hG β hβ root).le
  have hNexpect : 0 ≤ igffExpectation G hG β hβ root (fun m => N m.1) := by
    unfold igffExpectation
    apply div_nonneg
    · exact tsum_nonneg fun m => mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
    · exact (igffPartitionFunction_pos G hG β hβ root).le
  have hparts : ∀ m : pinnedIntegerField V root,
      Xp m = P m.1 - N m.1 := by
    intro m
    dsimp [Xp, X, P, N]
    by_cases hx : 0 ≤ pairing (fun j => (m.1 j : ℝ)) f
    · simp [max_eq_left hx, max_eq_right (by linarith :
        -pairing (fun j => (m.1 j : ℝ)) f ≤ 0)]
    · have hx' : pairing (fun j => (m.1 j : ℝ)) f < 0 := lt_of_not_ge hx
      rw [max_eq_right hx'.le, max_eq_left (by linarith)]
      ring
  have hTsum :
      (∑' m : pinnedIntegerField V root, Xp m * igffWeight G β m) =
        (∑' m : pinnedIntegerField V root, P m.1 * igffWeight G β m) -
          (∑' m : pinnedIntegerField V root, N m.1 * igffWeight G β m) := by
    rw [← hPos.tsum_sub hNeg]
    apply tsum_congr
    intro m
    rw [hparts m]
    ring
  have hEparts :
      igffExpectation G hG β hβ root Xp =
        igffExpectation G hG β hβ root (fun m => P m.1) -
          igffExpectation G hG β hβ root (fun m => N m.1) := by
    unfold igffExpectation
    rw [hTsum]
    ring
  change (∫ m, X m ∂integerGFFLaw G hG β hβ root) =
    igffExpectation G hG β hβ root Xp
  calc
    (∫ m, X m ∂integerGFFLaw G hG β hβ root) =
        ENNReal.toReal (∫⁻ m, ENNReal.ofReal (P m) ∂integerGFFLaw G hG β hβ root) -
          ENNReal.toReal (∫⁻ m, ENNReal.ofReal (N m) ∂integerGFFLaw G hG β hβ root) :=
      by
        simpa [P, N] using
          (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hXint)
    _ = ENNReal.toReal (ENNReal.ofReal
          (igffExpectation G hG β hβ root (fun m => P m.1))) -
        ENNReal.toReal (ENNReal.ofReal
          (igffExpectation G hG β hβ root (fun m => N m.1))) := by rw [hPlaw, hNlaw]
    _ = igffExpectation G hG β hβ root (fun m => P m.1) -
        igffExpectation G hG β hβ root (fun m => N m.1) := by
      rw [ENNReal.toReal_ofReal hPexpect, ENNReal.toReal_ofReal hNexpect]
    _ = igffExpectation G hG β hβ root Xp := hEparts.symm

/--
Sign symmetry makes every linear observable have zero Bochner mean under
the integer GFF law.
-/
theorem integerGFFLaw_integral_pairing_eq_zero
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) (f : V → ℝ) :
    (∫ m, pairing (fun j => (m j : ℝ)) f
      ∂integerGFFLaw G hG β hβ root) = 0 := by
  rw [integerGFFLaw_integral_pairing_eq_igffExpectation G hG β hβ root f]
  exact igffExpectation_pairing_eq_zero G (by
    change G.toSimpleGraph.Connected
    exact hG) β hβ root f

/--
The integer GFF law has a finite nonnegative second moment for every
linear observable, and its `∫⁻` is exactly the corresponding normalized
pinned-lattice expectation (KP p. 3).
-/
theorem integerGFFLaw_lintegral_pairing_sq_eq_igffExpectation
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) (f : V → ℝ) :
    (∫⁻ m, ENNReal.ofReal
      ((pairing (fun j => (m j : ℝ)) f) ^ 2)
      ∂integerGFFLaw G hG β hβ root) =
      ENNReal.ofReal (igffExpectation G (by
        change G.toSimpleGraph.Connected
        exact hG) β hβ root
        (fun m => (pairing (fun j => (m.1 j : ℝ)) f) ^ 2)) := by
  change G.Connected at hG
  apply integerGFFLaw_lintegral_ofReal_eq_igffExpectation G hG β hβ root
  · intro m
    exact sq_nonneg _
  · exact summable_igffPairing_sq_mul_weight G hG β hβ root f

/-- Scalar multiplication in the second slot of the finite vertex pairing. -/
private theorem pairing_smul_right {V : Type u} [Fintype V]
    (g f : V → ℝ) (c : ℝ) :
    pairing g (c • f) = c * pairing g f := by
  unfold Multigraph.pairing
  simp only [Pi.smul_apply]
  calc
    _ = (∑ j, g j * f j) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by ring

/--
The integer GFF law's exponential lintegral is the normalized
pinned-lattice exponential moment.

Exponential tilts are summable by the
finite-dimensional Gaussian domination lemma (KP p. 3).
-/
theorem integerGFFLaw_lintegral_exp_pairing_eq_igffExpectation
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) (f : V → ℝ) (t : ℝ) :
    (∫⁻ m, ENNReal.ofReal (Real.exp
      (t * pairing (fun j => (m j : ℝ)) f))
      ∂integerGFFLaw G hG β hβ root) =
      ENNReal.ofReal (igffExpectation G (by
        change G.toSimpleGraph.Connected
        exact hG) β hβ root
        (fun m => Real.exp
          (t * pairing (fun j => (m.1 j : ℝ)) f))) := by
  change G.Connected at hG
  have htilt := summable_igffTiltedWeight G hG β hβ root (t • f)
  have hsum : Summable (fun m : pinnedIntegerField V root =>
      Real.exp (t * pairing (fun j => (m.1 j : ℝ)) f) * igffWeight G β m) := by
    simpa [igffTiltedWeight, pairing_smul_right, mul_comm] using htilt
  have hnonneg : ∀ m : V → ℤ,
      0 ≤ Real.exp (t * pairing (fun j => (m j : ℝ)) f) :=
    fun m => (Real.exp_pos _).le
  simpa using integerGFFLaw_lintegral_ofReal_eq_igffExpectation
    G hG β hβ root
    (fun m => Real.exp (t * pairing (fun j => (m j : ℝ)) f))
    hnonneg hsum

/-- Sign symmetry identifies the pinned IGFF exponential moment with its
hyperbolic cosine moment. The two exponential tilts justify the tsum
linearity used here. -/
theorem igffExpectation_exp_eq_cosh
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (f : V → ℝ) (t : ℝ) :
    igffExpectation G hG β hβ root
        (fun m => Real.exp (t * pairing (fun j => (m.1 j : ℝ)) f)) =
      igffExpectation G hG β hβ root
        (fun m => Real.cosh (t * pairing (fun j => (m.1 j : ℝ)) f)) := by
  let X : pinnedIntegerField V root → ℝ := fun m =>
    pairing (fun j => (m.1 j : ℝ)) f
  let A : pinnedIntegerField V root → ℝ := fun m =>
    Real.exp (t * X m) * igffWeight G β m
  let B : pinnedIntegerField V root → ℝ := fun m =>
    Real.exp (-t * X m) * igffWeight G β m
  let e := pinnedIntegerFieldNegEquiv root
  have hA : Summable A := by
    have h := summable_igffTiltedWeight G hG β hβ root (t • f)
    simpa [A, X, igffTiltedWeight, pairing_smul_right, mul_comm] using h
  have hpair (m : pinnedIntegerField V root) : X (e m) = -X m := by
    change pairing (fun j => ((-m.1 j : ℤ) : ℝ)) f = _
    exact pairing_intField_neg m.1 f
  have hweight (m : pinnedIntegerField V root) :
      igffWeight G β (e m) = igffWeight G β m := igffWeight_neg G β m
  have hBpoint (m : pinnedIntegerField V root) : B m = A (e m) := by
    dsimp [A, B]
    rw [hweight]
    have harg : -t * X m = t * X (e m) := by rw [hpair]; ring
    rw [harg]
  have hB : Summable B := by
    have hcomp : Summable (fun m : pinnedIntegerField V root => A (e m)) :=
      (Equiv.summable_iff (f := A) e).mpr hA
    have hBfun : B = fun m => A (e m) := funext hBpoint
    rw [hBfun]
    exact hcomp
  have hBA : (∑' m, B m) = ∑' m, A m := by
    calc
      (∑' m, B m) = ∑' m, A (e m) := by
        apply tsum_congr
        intro m
        exact hBpoint m
      _ = ∑' m, A m := Equiv.tsum_eq e A
  have hCoshsum : (∑' m, Real.cosh (t * X m) * igffWeight G β m) =
      ∑' m, A m := by
    have hAB : Summable (fun m => A m + B m) := hA.add hB
    calc
      (∑' m, Real.cosh (t * X m) * igffWeight G β m) =
          ∑' m, (1 / 2 : ℝ) * (A m + B m) := by
        apply tsum_congr
        intro m
        have hpoint : Real.cosh (t * X m) * igffWeight G β m =
            (1 / 2 : ℝ) * (A m + B m) := by
          rw [Real.cosh_eq]
          dsimp [A, B]
          rw [show -(t * X m) = -t * X m by ring]
          ring
        exact hpoint
      _ = (1 / 2 : ℝ) * (∑' m : pinnedIntegerField V root, (A m + B m)) :=
        hAB.tsum_mul_left (1 / 2 : ℝ)
      _ = (1 / 2 : ℝ) * ((∑' m, A m) + (∑' m, B m)) := by
        rw [← hA.tsum_add hB]
      _ = ∑' m, A m := by rw [hBA]; ring
  unfold igffExpectation
  rw [hCoshsum]

/-- The second-order normalized cosh quotient differs from the normalized
cosh moment by exactly the scalar quotient `(F(t) - 1) / t²`. This uses the
partition sum as the normalization. -/
theorem igffExpectation_cosh_quotient_eq
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (f : V → ℝ) {t : ℝ} (ht : t ≠ 0) :
    igffExpectation G hG β hβ root
        (fun m => (Real.cosh (t * pairing (fun j => (m.1 j : ℝ)) f) - 1) / t ^ 2) =
      (igffExpectation G hG β hβ root
        (fun m => Real.cosh (t * pairing (fun j => (m.1 j : ℝ)) f)) - 1) / t ^ 2 := by
  let X : pinnedIntegerField V root → ℝ := fun m =>
    pairing (fun j => (m.1 j : ℝ)) f
  let W : pinnedIntegerField V root → ℝ := fun m => igffWeight G β m
  let C : pinnedIntegerField V root → ℝ := fun m => Real.cosh (t * X m) * W m
  let D : pinnedIntegerField V root → ℝ := fun m => W m
  let Q : pinnedIntegerField V root → ℝ := fun m =>
    ((Real.cosh (t * X m) - 1) / t ^ 2) * W m
  have hC : Summable C := by
    have hplus := summable_igffTiltedWeight G hG β hβ root (t • f)
    have hminus := summable_igffTiltedWeight G hG β hβ root (-t • f)
    have hsum : Summable (fun m =>
        Real.exp (t * X m) * W m + Real.exp (-t * X m) * W m) := by
      have hp (m : pinnedIntegerField V root) :
          Real.exp (t * X m) * W m = igffTiltedWeight G β (t • f) m := by
        simp [igffTiltedWeight, X, W, pairing_smul_right, mul_comm]
      have hm (m : pinnedIntegerField V root) :
          Real.exp (-t * X m) * W m = igffTiltedWeight G β (-t • f) m := by
        have hpair : pairing (fun j => (m.1 j : ℝ)) (-(t • f)) = -(t * X m) := by
          rw [← neg_smul]
          rw [pairing_smul_right]
          dsimp [X]
          ring
        rw [igffTiltedWeight, neg_smul, hpair]
        dsimp [W]
        rw [show -t * X m = -(t * X m) by ring]
      simpa only [← hp, ← hm] using hplus.add hminus
    have heq : C = fun m => (1 / 2 : ℝ) *
        (Real.exp (t * X m) * W m + Real.exp (-t * X m) * W m) := by
      funext m
      dsimp [C]
      rw [Real.cosh_eq]
      rw [show -(t * X m) = -t * X m by ring]
      ring
    rw [heq]
    exact hsum.mul_left (1 / 2 : ℝ)
  have hD : Summable D := by
    simpa [D, W] using summable_igffWeight G hG β hβ root
  have hDiff : Summable (fun m => C m - D m) := hC.sub hD
  have hQ : Summable Q := by
    have heq : (fun m => Q m) = fun m => (1 / t ^ 2) * (C m - D m) := by
      funext m
      dsimp [Q, C, D, X, W]
      field_simp [ht]
    change Summable (fun m => Q m)
    rw [heq]
    exact hDiff.mul_left (1 / t ^ 2)
  have hsumQ : (∑' m, Q m) =
      ((∑' m, C m) - ∑' m, D m) / t ^ 2 := by
    calc
      (∑' m, Q m) = ∑' m, (1 / t ^ 2) * (C m - D m) := by
        apply tsum_congr
        intro m
        dsimp [Q, C, D, X, W]
        field_simp [ht]
      _ = (1 / t ^ 2) * ∑' m, (C m - D m) :=
        hDiff.tsum_mul_left (1 / t ^ 2)
      _ = ((∑' m, C m) - ∑' m, D m) / t ^ 2 := by
        rw [hC.tsum_sub hD]
        ring
  have hZeq : (∑' m : pinnedIntegerField V root, D m) =
      igffPartitionFunction G β root := by rfl
  unfold igffExpectation
  change (∑' m, Q m) / igffPartitionFunction G β root =
      ((∑' m, C m) / igffPartitionFunction G β root - 1) / t ^ 2
  rw [hsumQ, hZeq]
  have hZ : 0 < igffPartitionFunction G β root :=
    igffPartitionFunction_pos G hG β hβ root
  field_simp [ne_of_gt hZ, ht]

/-- The normalized cosh second difference converges to half the normalized
second moment, by dominated convergence on the pinned integer field. -/
theorem tendsto_igffExpectation_cosh_moment_quotient
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (f : V → ℝ) :
    Tendsto (fun t : ℝ =>
      (igffExpectation G hG β hβ root
        (fun m => Real.cosh (t * pairing (fun j => (m.1 j : ℝ)) f)) - 1) / t ^ 2)
      (𝓝[≠] 0)
      (𝓝 (igffExpectation G hG β hβ root
        (fun m => (pairing (fun j => (m.1 j : ℝ)) f) ^ 2) / 2)) := by
  have hlim := tendsto_igffExpectation_cosh_difference_quotient
    G hG β hβ root f
  have hEq : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      (igffExpectation G hG β hβ root
        (fun m => (Real.cosh (t * pairing (fun j => (m.1 j : ℝ)) f) - 1) / t ^ 2)) =
        (igffExpectation G hG β hβ root
          (fun m => Real.cosh (t * pairing (fun j => (m.1 j : ℝ)) f)) - 1) / t ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := by simpa using ht
    exact igffExpectation_cosh_quotient_eq G hG β hβ root f htne
  have hlim' := hlim.congr' hEq
  have hSq := summable_igffPairing_sq_mul_weight G hG β hβ root f
  have htarget : igffExpectation G hG β hβ root
      (fun m => (pairing (fun j => (m.1 j : ℝ)) f) ^ 2 * (1 / 2 : ℝ)) =
      (1 / 2 : ℝ) * igffExpectation G hG β hβ root
        (fun m => (pairing (fun j => (m.1 j : ℝ)) f) ^ 2) := by
    unfold igffExpectation
    have hsum : (∑' m : pinnedIntegerField V root,
        ((pairing (fun j => (m.1 j : ℝ)) f) ^ 2 * (1 / 2 : ℝ)) *
          igffWeight G β m) = (1 / 2 : ℝ) *
          ∑' m : pinnedIntegerField V root,
            (pairing (fun j => (m.1 j : ℝ)) f) ^ 2 * igffWeight G β m := by
      calc
        _ = ∑' m : pinnedIntegerField V root, (1 / 2 : ℝ) *
            ((pairing (fun j => (m.1 j : ℝ)) f) ^ 2 * igffWeight G β m) := by
              apply tsum_congr
              intro m
              ring
        _ = _ := hSq.tsum_mul_left (1 / 2 : ℝ)
    rw [hsum]
    ring
  have htarget' : igffExpectation G hG β hβ root
      (fun m => (pairing (fun j => (m.1 j : ℝ)) f) ^ 2 / 2) =
      (1 / 2 : ℝ) * igffExpectation G hG β hβ root
        (fun m => (pairing (fun j => (m.1 j : ℝ)) f) ^ 2) := by
    simpa [div_eq_mul_inv, mul_comm] using htarget
  rw [htarget'] at hlim'
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlim'

/--
KP's implication (1.6) ⇒ (1.7) for the integer GFF law.

A lower
bound on every nonzero exponential tilt yields the corresponding second
moment bound; sign symmetry and the dominated second-order limit supply the
analytic step (KP p. 3).
-/
theorem integerGFFLaw_lintegral_pairing_sq_ge_of_expMoment_lower
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) (f : V → ℝ) (a : ℝ)
    (hExp : ∀ t : ℝ, t ≠ 0 →
      ENNReal.ofReal (Real.exp (a * t ^ 2)) ≤
        ∫⁻ m, ENNReal.ofReal (Real.exp
          (t * pairing (fun j => (m j : ℝ)) f))
          ∂integerGFFLaw G hG β hβ root) :
    ENNReal.ofReal (2 * a) ≤
      ∫⁻ m, ENNReal.ofReal
        ((pairing (fun j => (m j : ℝ)) f) ^ 2)
        ∂integerGFFLaw G hG β hβ root := by
  change G.Connected at hG
  let X : pinnedIntegerField V root → ℝ := fun m =>
    pairing (fun j => (m.1 j : ℝ)) f
  let F : ℝ → ℝ := fun t => igffExpectation G hG β hβ root
    (fun m => Real.cosh (t * X m))
  have hExpReal : ∀ t : ℝ, t ≠ 0 → Real.exp (a * t ^ 2) ≤ F t := by
    intro t ht
    have hchar := integerGFFLaw_lintegral_exp_pairing_eq_igffExpectation
      G hG β hβ root f t
    have hcosh := igffExpectation_exp_eq_cosh G hG β hβ root f t
    have hnonneg : 0 ≤ igffExpectation G hG β hβ root
        (fun m => Real.exp (t * X m)) := by
      unfold igffExpectation
      apply div_nonneg
      · exact tsum_nonneg fun m =>
          mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      · exact (igffPartitionFunction_pos G hG β hβ root).le
    have hENN := hExp t ht
    rw [hchar] at hENN
    have hreal := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hENN
    simpa [F, X, hcosh] using hreal
  have hlimit : Tendsto (fun t : ℝ => (F t - 1) / t ^ 2)
      (𝓝[≠] 0)
      (𝓝 (igffExpectation G hG β hβ root
        (fun m => X m ^ 2) / 2)) := by
    simpa [F, X] using tendsto_igffExpectation_cosh_moment_quotient
      G hG β hβ root f
  have hsecond := second_moment_ge_half_of_exponential_lower hlimit hExpReal
  have hreal : 2 * a ≤ igffExpectation G hG β hβ root (fun m => X m ^ 2) := by
    linarith
  have hmoment := integerGFFLaw_lintegral_pairing_sq_eq_igffExpectation
    G hG β hβ root f
  rw [hmoment]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Scaling both inputs of the finite pairing scales it quadratically. -/
private theorem pairing_smul_both {V : Type u} [Fintype V]
    (f g : V → ℝ) (t : ℝ) :
    pairing (t • f) (t • g) = t ^ 2 * pairing f g := by
  unfold Multigraph.pairing
  simp only [Pi.smul_apply]
  calc
    (∑ j, (t * f j) * (t * g j)) =
        ∑ j, t ^ 2 * (f j * g j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = t ^ 2 * ∑ j, f j * g j := (Finset.mul_sum _ _ _).symm

/--
The second-moment conclusion (1.7) follows from (1.6) on the law,
for every zero-sum observable and every Laplacian pseudoinverse.

The proof
applies (1.6) to scalar multiples of the observable and invokes the
second-order limit above (KP p. 3).
-/
theorem integerGFFLaw_lintegral_pairing_sq_ge_of_expMoment_family
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β ε : ℝ)
    (hβ : 0 < β) (hε : 0 < ε) (root : V)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : V → ℝ) (hf : ∑ j, f j = 0)
    (hExp : ∀ g : V → ℝ, (∑ j, g j = 0) →
      ENNReal.ofReal (Real.exp
        (pairing g (-(T g)) / (2 * (1 + ε) * β))) ≤
        ∫⁻ m, ENNReal.ofReal (Real.exp
          (pairing (fun j => (m j : ℝ)) g))
          ∂integerGFFLaw G hG β hβ root) :
    ENNReal.ofReal
        (pairing f (-(T f)) / ((1 + ε) * β)) ≤
      ∫⁻ m, ENNReal.ofReal
        ((pairing (fun j => (m j : ℝ)) f) ^ 2)
        ∂integerGFFLaw G hG β hβ root := by
  let a := pairing f (-(T f)) / (2 * (1 + ε) * β)
  have hExpScaled : ∀ t : ℝ, t ≠ 0 →
      ENNReal.ofReal (Real.exp (a * t ^ 2)) ≤
        ∫⁻ m, ENNReal.ofReal (Real.exp
          (t * pairing (fun j => (m j : ℝ)) f))
          ∂integerGFFLaw G hG β hβ root := by
    intro t ht
    have hzero : ∑ j, (t • f) j = 0 := by
      change ∑ j, t * f j = 0
      rw [← Finset.mul_sum, hf, mul_zero]
    have h := hExp (t • f) hzero
    have hscale : pairing (t • f) (-(T (t • f))) =
        t ^ 2 * pairing f (-(T f)) := by
      rw [map_smul, ← smul_neg]
      exact pairing_smul_both f (-(T f)) t
    have hexp : pairing (t • f) (-(T (t • f))) /
        (2 * (1 + ε) * β) = a * t ^ 2 := by
      rw [hscale]
      dsimp [a]
      field_simp [ne_of_gt hβ, ne_of_gt (by linarith : 0 < 1 + ε)]
    rw [hexp] at h
    simpa only [pairing_smul_right] using h
  have hmain := integerGFFLaw_lintegral_pairing_sq_ge_of_expMoment_lower
    G hG β hβ root f a hExpScaled
  have hcoeff : 2 * a = pairing f (-(T f)) / ((1 + ε) * β) := by
    dsimp [a]
    field_simp [ne_of_gt hβ, ne_of_gt (by linarith : 0 < 1 + ε)]
  rw [hcoeff] at hmain
  exact hmain

/--
The dipole consequence of the exponential-moment bound at `ε = 1`.

The mean-zero inverse uniqueness identifies an arbitrary pseudoinverse
with `greenOp`; the factor is therefore `c = 1/48` (KP Theorem 1.1, p. 3).
-/
theorem integerGFFLaw_dipole_lintegral_ge_log_of_expMoment
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (root : V) (T : (V → ℝ) →ₗ[ℝ] V → ℝ)
    (hT : G.IsLaplacianPseudoinverse T)
    (hExp : ∀ f : V → ℝ, (∑ j, f j = 0) →
      ENNReal.ofReal (Real.exp
        (pairing f (-(T f)) / (4 * β))) ≤
        ∫⁻ m, ENNReal.ofReal (Real.exp
          (pairing (fun j => (m j : ℝ)) f))
          ∂integerGFFLaw G hG β hβ root)
    (hLog : ∀ j k : V,
      (1 / 24 : ℝ) * Real.log (↑(G.toSimpleGraph.dist j k + 1) : ℝ) ≤
        pairing (pointDipole j k)
          (-(G.greenOp (by change G.toSimpleGraph.Connected; exact hG)
            (pointDipole j k))))
    (j k : V) :
    ENNReal.ofReal ((1 / 48 : ℝ) / β *
      Real.log (↑(G.toSimpleGraph.dist j k + 1) : ℝ)) ≤
      ∫⁻ m, ENNReal.ofReal (((m j : ℝ) - (m k : ℝ)) ^ 2)
        ∂integerGFFLaw G hG β hβ root := by
  have hzero : ∑ x, pointDipole j k x = 0 := sum_pointDipole_eq_zero j k
  have hmoment := integerGFFLaw_lintegral_pairing_sq_ge_of_expMoment_family
    G hG β 1 hβ (by norm_num)
    root T (pointDipole j k) hzero (by
      intro f hf
      simpa only [show (4 : ℝ) = 2 * (1 + 1) by norm_num] using hExp f hf)
  have hGreen : G.IsLaplacianPseudoinverse (G.greenOp hG) := by
    constructor
    · intro g hg
      exact ⟨G.laplacian_greenOp_of_sum_eq_zero hG g hg,
        G.greenOp_laplacian_of_sum_eq_zero hG g hg⟩
    · intro c
      exact G.greenOp_const hG c
  obtain ⟨T₀, hT₀, hT₀_unique⟩ :=
    existsUnique_isLaplacianPseudoinverse G hG
  have hT_eq : T = T₀ := hT₀_unique T hT
  have hGreen_eq : G.greenOp hG = T₀ := hT₀_unique _ hGreen
  have hunique : T = G.greenOp hG := hT_eq.trans hGreen_eq.symm
  have hLogGreen := hLog j k
  have hpair (m : V → ℤ) :
      pairing (fun x => (m x : ℝ)) (pointDipole j k) =
        (m j : ℝ) - (m k : ℝ) := by
    classical
    unfold Multigraph.pairing pointDipole
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hsum (p : V) :
        (∑ x, (m x : ℝ) * (if x = p then 1 else 0)) = (m p : ℝ) := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro x hx hxp
        simp [hxp]
      · simp
    rw [hsum j, hsum k]
  have hmoment' : ENNReal.ofReal
      (pairing (pointDipole j k)
        (-(T (pointDipole j k))) / ((1 + 1) * β)) ≤
      ∫⁻ m, ENNReal.ofReal (((m j : ℝ) - (m k : ℝ)) ^ 2)
        ∂integerGFFLaw G hG β hβ root := by
    simpa [hpair] using hmoment
  have hcoef : (1 / 48 : ℝ) / β *
      Real.log (↑(G.toSimpleGraph.dist j k + 1) : ℝ) ≤
      pairing (pointDipole j k) (-(T (pointDipole j k))) /
        ((1 + 1) * β) := by
    have hscale := mul_le_mul_of_nonneg_right hLogGreen
      (by positivity : (0 : ℝ) ≤ 1 / (2 * β))
    calc
      (1 / 48 : ℝ) / β *
          Real.log (↑(G.toSimpleGraph.dist j k + 1) : ℝ) =
        (1 / (2 * β)) *
          ((1 / 24 : ℝ) * Real.log
            (↑(G.toSimpleGraph.dist j k + 1) : ℝ)) := by ring
      _ = ((1 / 24 : ℝ) *
          Real.log (↑(G.toSimpleGraph.dist j k + 1) : ℝ)) *
          (1 / (2 * β)) := by ring
      _ ≤ pairing (pointDipole j k)
            (-(G.greenOp hG (pointDipole j k))) * (1 / (2 * β)) := hscale
      _ = (1 / (2 * β)) * pairing (pointDipole j k)
            (-(G.greenOp hG (pointDipole j k))) := by ring
      _ = _ := by rw [← hunique]; ring
  exact (ENNReal.ofReal_le_ofReal hcoef).trans hmoment'

/--
Assemble KP Theorem 1.1 in the root's exact local `let bounds`
shape.

The small-temperature cutoff is the minimum of the cutoff for the
requested `ε` and the cutoff at `ε = 1`; the latter supplies the universal
`1/48` dipole constant.

-/
theorem integerGFF_delocalization_assemble
    (βSmall : ℝ → ℝ) (hβSmall : ∀ ε : ℝ, 0 < ε → 0 < βSmall ε)
    (hExpFree : ∀ (L : ℕ) (hL : 1 < L) (ε : ℝ), 0 < ε →
      ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < βSmall ε →
      ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
        Multigraph.IsLaplacianPseudoinverse (squareFree L) T →
        ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
          ENNReal.ofReal (Real.exp
            (pairing f (-(T f)) / (2 * (1 + ε) * β))) ≤
            ∫⁻ m, ENNReal.ofReal
              (Real.exp (pairing (fun j => (m j : ℝ)) f))
              ∂integerGFFLaw (squareFree L) (squareFree_connected L hL) β hβ v)
    (hExpPeriodic : ∀ (L : ℕ) (hL : 1 < L) (ε : ℝ), 0 < ε → Even L →
      ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < βSmall ε →
      ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
        Multigraph.IsLaplacianPseudoinverse (squarePeriodic L) T →
        ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
          ENNReal.ofReal (Real.exp
            (pairing f (-(T f)) / (2 * (1 + ε) * β))) ≤
            ∫⁻ m, ENNReal.ofReal
              (Real.exp (pairing (fun j => (m j : ℝ)) f))
              ∂integerGFFLaw (squarePeriodic L)
                (squarePeriodic_connected L hL) β hβ v) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ (L : ℕ) (hL : 1 < L),
        let bounds : ∀ {E : Type} [Fintype E]
            (Λ : Multigraph (Fin L × Fin L) E),
            Λ.toSimpleGraph.Connected → Prop :=
          fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
            (∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
              Multigraph.IsLaplacianPseudoinverse Λ T →
              ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
                ENNReal.ofReal (Real.exp
                    (pairing f (-(T f)) / (2 * (1 + ε) * β))) ≤
                    ∫⁻ m, ENNReal.ofReal
                      (Real.exp (pairing (fun j => (m j : ℝ)) f))
                      ∂(integerGFFLaw Λ hΛ β hβ v) ∧
                  ENNReal.ofReal
                    (pairing f (-(T f)) / ((1 + ε) * β)) ≤
                    ∫⁻ m, ENNReal.ofReal
                      ((pairing (fun j => (m j : ℝ)) f) ^ 2)
                      ∂(integerGFFLaw Λ hΛ β hβ v)) ∧
            ∀ j k : Fin L × Fin L,
              ENNReal.ofReal ((1 / 48 : ℝ) / β *
                Real.log (↑(Λ.toSimpleGraph.dist j k + 1) : ℝ)) ≤
                ∫⁻ m, ENNReal.ofReal (((m j : ℝ) - m k) ^ 2)
                  ∂(integerGFFLaw Λ hΛ β hβ v)
        bounds (squareFree L) (squareFree_connected L hL) ∧
          (Even L → bounds (squarePeriodic L) (squarePeriodic_connected L hL)) := by
  refine ⟨(1 / 48 : ℝ), by norm_num, ?_⟩
  intro ε hε
  let β₀ := min (βSmall ε) (βSmall 1)
  have hβ₀ : 0 < β₀ := lt_min (hβSmall ε hε) (hβSmall 1 (by norm_num))
  refine ⟨β₀, hβ₀, ?_⟩
  intro L hL
  let bounds : ∀ {E : Type} [Fintype E]
      (Λ : Multigraph (Fin L × Fin L) E), Λ.toSimpleGraph.Connected → Prop :=
    fun Λ hΛ => ∀ (v : Fin L × Fin L) (β : ℝ) (hβ : 0 < β), β < β₀ →
      (∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
        Multigraph.IsLaplacianPseudoinverse Λ T →
        ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
          ENNReal.ofReal (Real.exp
              (pairing f (-(T f)) / (2 * (1 + ε) * β))) ≤
              ∫⁻ m, ENNReal.ofReal
                (Real.exp (pairing (fun j => (m j : ℝ)) f))
                ∂(integerGFFLaw Λ hΛ β hβ v) ∧
            ENNReal.ofReal (pairing f (-(T f)) / ((1 + ε) * β)) ≤
              ∫⁻ m, ENNReal.ofReal
                ((pairing (fun j => (m j : ℝ)) f) ^ 2)
                ∂(integerGFFLaw Λ hΛ β hβ v)) ∧
      ∀ j k : Fin L × Fin L,
        ENNReal.ofReal ((1 / 48 : ℝ) / β *
          Real.log (↑(Λ.toSimpleGraph.dist j k + 1) : ℝ)) ≤
          ∫⁻ m, ENNReal.ofReal (((m j : ℝ) - m k) ^ 2)
            ∂(integerGFFLaw Λ hΛ β hβ v)
  have buildBounds : ∀ {E : Type} [Fintype E]
      (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected),
      (∀ δ : ℝ, 0 < δ →
        ∀ (v : Fin L × Fin L) (b : ℝ) (hb : 0 < b), b < βSmall δ →
        ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
          Multigraph.IsLaplacianPseudoinverse Λ T →
          ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
            ENNReal.ofReal (Real.exp
              (pairing f (-(T f)) / (2 * (1 + δ) * b))) ≤
              ∫⁻ m, ENNReal.ofReal
                (Real.exp (pairing (fun j => (m j : ℝ)) f))
                ∂integerGFFLaw Λ hΛ b hb v) →
      (∀ j k : Fin L × Fin L,
        (1 / 24 : ℝ) * Real.log
          (↑(Λ.toSimpleGraph.dist j k + 1) : ℝ) ≤
          pairing (pointDipole j k) (-(Λ.greenOp hΛ (pointDipole j k)))) →
        bounds Λ hΛ := by
    intro E instE Λ hΛ hExpGraph hLogGraph v β hβ hβ₀'
    have hβε : β < βSmall ε := lt_of_lt_of_le hβ₀' (min_le_left _ _)
    have hβone : β < βSmall 1 := lt_of_lt_of_le hβ₀' (min_le_right _ _)
    constructor
    · intro T hT f hf
      have hExpε : ∀ g : Fin L × Fin L → ℝ, (∑ j, g j = 0) →
          ENNReal.ofReal (Real.exp
            (pairing g (-(T g)) / (2 * (1 + ε) * β))) ≤
            ∫⁻ m, ENNReal.ofReal
              (Real.exp (pairing (fun j => (m j : ℝ)) g))
              ∂integerGFFLaw Λ hΛ β hβ v := by
        intro g hg
        exact hExpGraph ε hε v β hβ hβε T hT g hg
      constructor
      · exact hExpGraph ε hε v β hβ hβε T hT f hf
      · exact integerGFFLaw_lintegral_pairing_sq_ge_of_expMoment_family
          Λ hΛ β ε hβ hε v T f hf hExpε
    · let T := Λ.greenOp hΛ
      have hT : Multigraph.IsLaplacianPseudoinverse Λ T := by
        dsimp [T]
        constructor
        · intro g hg
          exact ⟨Λ.laplacian_greenOp_of_sum_eq_zero hΛ g hg,
            Λ.greenOp_laplacian_of_sum_eq_zero hΛ g hg⟩
        · intro c
          exact Λ.greenOp_const hΛ c
      have hExpOne : ∀ g : Fin L × Fin L → ℝ, (∑ j, g j = 0) →
          ENNReal.ofReal (Real.exp
            (pairing g (-(T g)) / (4 * β))) ≤
            ∫⁻ m, ENNReal.ofReal
              (Real.exp (pairing (fun j => (m j : ℝ)) g))
              ∂integerGFFLaw Λ hΛ β hβ v := by
        intro g hg
        have h := hExpGraph 1 (by norm_num) v β hβ hβone T hT g hg
        simpa only [show (4 : ℝ) = 2 * (1 + 1) by norm_num] using h
      intro j k
      exact integerGFFLaw_dipole_lintegral_ge_log_of_expMoment
        Λ hΛ β hβ v T hT hExpOne hLogGraph j k
  have hFreeExpGraph : ∀ δ : ℝ, 0 < δ →
      ∀ (v : Fin L × Fin L) (b : ℝ) (hb : 0 < b), b < βSmall δ →
      ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
        Multigraph.IsLaplacianPseudoinverse (squareFree L) T →
        ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
          ENNReal.ofReal (Real.exp
            (pairing f (-(T f)) / (2 * (1 + δ) * b))) ≤
            ∫⁻ m, ENNReal.ofReal
              (Real.exp (pairing (fun j => (m j : ℝ)) f))
              ∂integerGFFLaw (squareFree L)
                (squareFree_connected L hL) b hb v := by
    intro δ hδ v b hb hcut T hT f hf
    exact hExpFree L hL δ hδ v b hb hcut T hT f hf
  have hFree := buildBounds (squareFree L) (squareFree_connected L hL)
    hFreeExpGraph (fun j k => squareFree_source_pairing_dipole_ge_log hL j k)
  have hPeriodic : Even L → bounds (squarePeriodic L)
      (squarePeriodic_connected L hL) := by
    intro hEven
    have hPeriodicExpGraph : ∀ δ : ℝ, 0 < δ →
        ∀ (v : Fin L × Fin L) (b : ℝ) (hb : 0 < b), b < βSmall δ →
        ∀ T : (Fin L × Fin L → ℝ) →ₗ[ℝ] Fin L × Fin L → ℝ,
          Multigraph.IsLaplacianPseudoinverse (squarePeriodic L) T →
          ∀ f : Fin L × Fin L → ℝ, ∑ j, f j = 0 →
            ENNReal.ofReal (Real.exp
              (pairing f (-(T f)) / (2 * (1 + δ) * b))) ≤
              ∫⁻ m, ENNReal.ofReal
                (Real.exp (pairing (fun j => (m j : ℝ)) f))
                ∂integerGFFLaw (squarePeriodic L)
                  (squarePeriodic_connected L hL) b hb v := by
      intro δ hδ v b hb hcut T hT f hf
      exact hExpPeriodic L hL δ hδ hEven v b hb hcut T hT f hf
    exact buildBounds (squarePeriodic L) (squarePeriodic_connected L hL)
      hPeriodicExpGraph
      (fun j k => squarePeriodic_even_source_pairing_dipole_ge_log
        hL hEven j k)
  exact ⟨hFree, hPeriodic⟩

end FroehlichSpencer.BKT

end
