/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.DualityFinite
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Positive partition-sum cancellation

An injective decomposition of source configurations into a source polymer and
a neutral remainder bounds the constrained sum by the product of the two
positive partition sums. This is the inequality form used to cancel neutral
components against the vacuum partition function.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

/-- Injective source/remainder decomposition bounds a positive source sum by
the product of the unrestricted positive sums of its two parts. -/
theorem positiveTsum_le_product_of_injective_decomposition
    {X P N : Type*} (split : X → P × N) (hsplit : Function.Injective split)
    (w : X → ℝ) (u : P → ℝ) (v : N → ℝ)
    (hfactor : ∀ x, w x = u (split x).1 * v (split x).2)
    (hu : Summable u) (hv : Summable v)
    (huv : Summable fun z : P × N => u z.1 * v z.2)
    (hnonneg : ∀ z : P × N, 0 ≤ u z.1 * v z.2) :
    (∑' x, w x) ≤ (∑' p, u p) * (∑' n, v n) := by
  have hcomp : (∑' x, w x) ≤ ∑' z : P × N, u z.1 * v z.2 := by
    rw [show (fun x => w x) = fun x => u (split x).1 * v (split x).2 by
      funext x
      exact hfactor x]
    exact tsum_comp_le_tsum_of_inj huv hnonneg hsplit
  rw [← hu.tsum_mul_tsum hv huv] at hcomp
  exact hcomp


theorem dualWilsonPartition_eq_sourceMode_tsum {B : Cubical.Box 4}
    (β : ℝ) (S : Cubical.Chain 4 B) :
    dualWilsonPartition (B := B) β S =
      ∑' m : {m : PrimalPlaquettes B → ℤ //
        plaquetteModeDivergence m = primalSheetLoopFrequency S},
        dualGaussianProduct β m.1 := by
  let P : Set (PrimalPlaquettes B → ℤ) :=
    {m | plaquetteModeDivergence m = primalSheetLoopFrequency S}
  have hterm (m : PrimalPlaquettes B → ℤ) :
      dualWilsonTerm β S m = P.indicator (dualGaussianProduct β) m := by
    by_cases hm : m ∈ P
    · change plaquetteModeDivergence m = primalSheetLoopFrequency S at hm
      simp [dualWilsonTerm, P, hm]
    · change ¬ plaquetteModeDivergence m = primalSheetLoopFrequency S at hm
      simp [dualWilsonTerm, P, hm]
  unfold dualWilsonPartition
  rw [show (fun m : PrimalPlaquettes B → ℤ => dualWilsonTerm β S m) =
      P.indicator (dualGaussianProduct β) by funext m; exact hterm m]
  rw [← tsum_subtype P (dualGaussianProduct β)]
  rfl

private theorem summable_prod_of_nonneg_factors {P N : Type*}
    (u : P → ℝ) (v : N → ℝ)
    (hu : Summable u) (hv : Summable v)
    (hu0 : ∀ p, 0 ≤ u p) (hv0 : ∀ n, 0 ≤ v n) :
    Summable fun z : P × N => u z.1 * v z.2 := by
  rw [summable_prod_of_nonneg (fun z => mul_nonneg (hu0 z.1) (hv0 z.2))]
  constructor
  · intro p
    simpa using hv.mul_left (u p)
  · have houter : Summable (fun p => u p * ∑' n, v n) :=
      hu.mul_right (∑' n, v n)
    apply houter.congr
    intro p
    change u p * ∑' n, v n = ∑' n, u p * v n
    rw [← tsum_mul_left]

/-- Component cancellation in the inequality form: once source modes are
injectively split into connected source fields and neutral remainders, the
neutral factor is bounded by the full vacuum partition sum. -/
theorem dualWilsonPartition_le_sourceCluster_mul_vacuum
    {B : Cubical.Box 4} (β : ℝ) (hβ : 0 < β) (S : Cubical.Chain 4 B)
    (C : (PrimalPlaquettes B → ℤ) → Prop)
    (split : {m : PrimalPlaquettes B → ℤ //
      plaquetteModeDivergence m = primalSheetLoopFrequency S} →
      ({c : PrimalPlaquettes B → ℤ //
        plaquetteModeDivergence c = primalSheetLoopFrequency S ∧ C c} ×
        (PrimalPlaquettes B → ℤ)))
    (hinj : Function.Injective split)
    (hfactor : ∀ m,
      dualGaussianProduct β m.1 =
        dualGaussianProduct β (split m).1.1 *
          dualWilsonTerm β (0 : Cubical.Chain 4 B) (split m).2) :
    dualWilsonPartition (B := B) β S ≤
      (∑' c : {c : PrimalPlaquettes B → ℤ //
        plaquetteModeDivergence c = primalSheetLoopFrequency S ∧ C c},
        dualGaussianProduct β c.1) *
        dualWilsonPartition (B := B) β (0 : Cubical.Chain 4 B) := by
  let X := {m : PrimalPlaquettes B → ℤ //
    plaquetteModeDivergence m = primalSheetLoopFrequency S}
  let P := {c : PrimalPlaquettes B → ℤ //
    plaquetteModeDivergence c = primalSheetLoopFrequency S ∧ C c}
  let u : P → ℝ := fun c => dualGaussianProduct β c.1
  let v : (PrimalPlaquettes B → ℤ) → ℝ :=
    dualWilsonTerm β (0 : Cubical.Chain 4 B)
  let w : X → ℝ := fun m => dualGaussianProduct β m.1
  have hGauss := dualGaussianProduct_summable (B := B) β hβ
  have hu : Summable u := by
    apply hGauss.comp_injective
    intro c d h
    apply Subtype.ext
    exact h
  have hv : Summable v := dualWilsonTerm_summable (B := B) β hβ 0
  have hu0 (c : P) : 0 ≤ u c := dualGaussianProduct_nonneg β c.1
  have hv0 (n : PrimalPlaquettes B → ℤ) : 0 ≤ v n :=
    dualWilsonTerm_nonneg β 0 n
  have huv : Summable fun z : P × (PrimalPlaquettes B → ℤ) =>
      u z.1 * v z.2 :=
    summable_prod_of_nonneg_factors u v hu hv hu0 hv0
  have hsum := positiveTsum_le_product_of_injective_decomposition
    (split := split) hinj w u v
    (by intro m; exact hfactor m) hu hv huv
    (fun z => mul_nonneg (hu0 z.1) (hv0 z.2))
  have hsource : dualWilsonPartition (B := B) β S = ∑' m : X, w m := by
    simpa [X, w] using dualWilsonPartition_eq_sourceMode_tsum β S
  have hvac : (∑' n : PrimalPlaquettes B → ℤ, v n) =
      dualWilsonPartition (B := B) β (0 : Cubical.Chain 4 B) := rfl
  rw [← hsource, hvac] at hsum
  simpa [u] using hsum

end FroehlichSpencer.FS82.Wilson

end
