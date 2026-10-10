/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Duality.Expectation
public import FroehlichSpencer.BKT.Bridge.FreeLineSource
public import FroehlichSpencer.BKT.Gaussian.Fejer
public import FroehlichSpencer.BKT.Gaussian.FejerAverage
public import FroehlichSpencer.BKT.Surface.SubGaussian

/-!
# Line-source field observable as an exponential pairing

KP Proposition 6.1's line observable is an exponential of a pairing with the line source of
KP (6.3), up to a constant factor; the rooted IGFF expectation is homogeneous; and KP's Fejér
polynomials are `(1, 0, 0)`-sub-Gaussian (KP §5.1).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

/-- The rooted IGFF expectation is homogeneous in the observable. -/
theorem igffExpectation_const_mul {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V) (c : ℝ)
    (F : pinnedIntegerField V root → ℝ) :
    igffExpectation G hG β hβ root (fun m => c * F m) = c * igffExpectation G hG β hβ root F := by
  change (∑' m, (c * F m) * igffWeight G β m) / igffPartitionFunction G β root =
    c * ((∑' m, F m * igffWeight G β m) / igffPartitionFunction G β root)
  rw [← mul_div_assoc, ← tsum_mul_left]
  simp only [mul_assoc]

/-- KP Proposition 6.1's line observable is the exponential of a pairing with the line source of
KP (6.3) on the side-`(L+1)` dual box (`y₀ = x₀ + 1`, `y₁ = x₁`), times `e^{-(L - x₀)/(2β)}`. -/
theorem kpPrintedLineSourceFieldObservable_eq {L : ℕ} (β : ℝ) (site : Lattice2D.SquareFreeVertex L)
    (m : Lattice2D.SquareFreeVertex (L + 1) → ℤ) :
    Duality.kpPrintedLineSourceFieldObservable β site m =
      Real.exp (Multigraph.pairing (fun j => (m j : ℝ))
        (fun j => -(1 / β) * Lattice2D.squareFreeLineSource (L + 1) (site.1.val + 1) site.2.val j)) *
      Real.exp (-(((L - site.1.val : ℕ) : ℝ) / (2 * β))) := by
  rw [← Real.exp_add]
  unfold Duality.kpPrintedLineSourceFieldObservable Duality.kpPrintedLineSourceFieldSum
  congr 1
  have hp : Multigraph.pairing (fun j => (m j : ℝ))
      (fun j => -(1 / β) * Lattice2D.squareFreeLineSource (L + 1) (site.1.val + 1)
        site.2.val j) = -(1 / β) * ∑ t : Fin (L + 1) with site.1.val + 1 ≤ t.val,
        ((m (t, ⟨site.2.val, by omega⟩) : ℝ) - (m (t, ⟨site.2.val + 1, by omega⟩) : ℝ)) := by
    rw [← sum_mul_squareFreeLineSource (site.1.val + 1) site.2.val (by omega : site.2.val + 1 < L + 1)
      (fun j => (m j : ℝ)), Finset.mul_sum]
    unfold Multigraph.pairing
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hp, Finset.sum_filter, Fin.sum_univ_succ]
  have h0 : ¬ (site.1.val + 1 ≤ ((0 : Fin (L + 1)) : ℕ)) := by simp
  simp only [h0, ite_false, zero_add, Fin.val_succ, Nat.add_le_add_iff_right]
  have hc : ((L - site.1.val : ℕ) : ℝ) = ∑ t : Fin L, if site.1.val ≤ t.val then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_le_val]
    simp
  rw [hc]
  have key : ∀ t : Fin L, (if site.1.val ≤ t.val then
      (m (Duality.highIndex t, Duality.lowIndex site.2) : ℝ) -
        (m (Duality.highIndex t, Duality.highIndex site.2) : ℝ) + (1 / 2 : ℝ) else 0) =
      (if site.1.val ≤ t.val then
        ((m (t.succ, ⟨site.2.val, by omega⟩) : ℝ) - (m (t.succ, ⟨site.2.val + 1, by omega⟩) : ℝ))
        else 0) + (1 / 2 : ℝ) * (if site.1.val ≤ t.val then (1 : ℝ) else 0) := by
    intro t
    split_ifs <;> simp [Duality.highIndex, Duality.lowIndex, Fin.succ]
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  field_simp
  ring

/-- KP's Fejér polynomials are `(1, 0, 0)`-sub-Gaussian at every `β` (KP §5.1). -/
theorem isSubGaussian_fejerPolynomial (N : ℕ) (hN : 0 < N) (β : ℝ) :
    IsSubGaussian 1 0 0 β (fejerPolynomial N) := by
  refine ⟨N, hN, fun q => fejerFourierCoefficient N (q : ℤ), ?_, ?_, ?_⟩
  · intro q hq
    change fejerFourierCoefficient N (q : ℤ) = 0
    rw [fejerFourierCoefficient_nat]
    simp [not_le_of_gt hq]
  · intro φ
    rw [fejerPolynomial_eq_fourierCosineExpansion]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  · intro q hq
    have hcoeff := fejerFourierCoefficient_mem_unitInterval N (q : ℤ)
    have habs : |fejerFourierCoefficient N (q : ℤ)| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_trans (by norm_num) hcoeff.1, hcoeff.2⟩
    simpa using habs

end FroehlichSpencer.BKT

end
