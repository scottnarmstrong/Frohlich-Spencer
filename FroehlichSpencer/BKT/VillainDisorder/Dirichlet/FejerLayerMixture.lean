/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.FejerAverage
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerComb
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerCoefficient

/-! # Fejér site mixtures on the rooted square

Each Fejér polynomial is a convex mixture of the same single-site charge factors used by the
Appendix D comb selection.  The frequency coefficient is multiplied by the triangular Fejér
factor, so it is bounded by the comb coefficient independently of the cutoff.  On the rooted
carrier, the exterior coordinate contributes the explicit scalar `N`; the layer itself uses the
unit root factor.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Rotator

/-- The Fejér site factor away from the pinned exterior coordinate. -/
def rootedFejerLam (L N : ℕ) : RotatorDualFace L → ℝ → ℝ :=
  fun j θ => if j = none then 1 else fejerPolynomial N θ

/-- The triangular Fejér multiplier on a single-site frequency. -/
def fejerTriangularFactor (N q : ℕ) : ℝ := 1 - (q : ℝ) / N

/-- The charge-factor coefficient in the convex Fejér mixture. -/
def fejerMixtureCoeff (N q : ℕ) : ℝ := combCoeff N q * fejerTriangularFactor N q

/-- The activity carried by a density in the Fejér selection.  On an initial single-site density
of frequency `q`, this equals `fejerMixtureCoeff N q`. -/
def fejerActivity {L : ℕ} (N : ℕ) (ρ : ChargeDensity L) : ℝ :=
  combActivity N ρ * max 0 (1 - (nrm ρ : ℝ) / N)

/-- The single-site activity is precisely the triangular multiple of the comb activity. -/
theorem fejerActivity_siteCharge {L N : ℕ} (f : Site L → ℕ) (x : Site L) :
    f x ≤ N → fejerActivity N (siteCharge f x) = fejerMixtureCoeff N (f x) := by
  intro hfreq
  by_cases hN : N = 0
  · subst N
    have hfx : f x = 0 := by omega
    simp [fejerActivity, fejerMixtureCoeff, fejerTriangularFactor,
      nrm_siteCharge, combActivity_siteCharge, hfx]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    rw [fejerActivity, fejerMixtureCoeff, fejerTriangularFactor,
      nrm_siteCharge, combActivity_siteCharge]
    have htri : 0 ≤ 1 - (f x : ℝ) / N := by
      rw [sub_nonneg]
      have hfx' : (f x : ℝ) ≤ N := by exact_mod_cast hfreq
      exact (div_le_one (by exact_mod_cast hNpos : (0 : ℝ) < N)).2 hfx'
    rw [max_eq_right htri]

/-- The truncated Fejér activity is bounded by the comb activity on every density. -/
theorem fejerActivity_abs_le_combActivity {L N : ℕ} (ρ : ChargeDensity L) :
    |fejerActivity N ρ| ≤ |combActivity N ρ| := by
  have hnorm : 0 ≤ combActivity N ρ := by
    unfold combActivity combNorm
    positivity
  have hratio0 : 0 ≤ max 0 (1 - (nrm ρ : ℝ) / N) := le_max_left _ _
  have hratio1 : max 0 (1 - (nrm ρ : ℝ) / N) ≤ 1 := by
    apply max_le
    · norm_num
    · have hquot : 0 ≤ (nrm ρ : ℝ) / N := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith
  rw [fejerActivity, abs_of_nonneg (mul_nonneg hnorm hratio0), abs_of_nonneg hnorm]
  exact mul_le_of_le_one_right hnorm hratio1

/-- Fejér mixture coefficients are nonnegative on the cutoff interval. -/
theorem fejerMixtureCoeff_nonneg {N q : ℕ} (hN : 1 ≤ N)
    (hq : q ∈ Finset.Icc 1 N) : 0 ≤ fejerMixtureCoeff N q := by
  have hqN : q ≤ N := (Finset.mem_Icc.mp hq).2
  have htri : 0 ≤ fejerTriangularFactor N q := by
    unfold fejerTriangularFactor
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hN
    have hq' : (q : ℝ) ≤ N := by exact_mod_cast hqN
    rw [sub_nonneg]
    exact (div_le_one hNpos).2 hq'
  exact mul_nonneg (combCoeff_pos hN q).le htri

/-- Fejér mixture coefficients are bounded by the comb coefficients, uniformly in `N`. -/
theorem fejerMixtureCoeff_le_combCoeff {N q : ℕ} (hN : 1 ≤ N)
    (hq : q ∈ Finset.Icc 1 N) : fejerMixtureCoeff N q ≤ combCoeff N q := by
  have htri0 : 0 ≤ fejerTriangularFactor N q := by
    unfold fejerTriangularFactor
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hN
    have hq' : (q : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hq).2
    rw [sub_nonneg]
    exact (div_le_one hNpos).2 hq'
  have htri1 : fejerTriangularFactor N q ≤ 1 := by
    unfold fejerTriangularFactor
    have hq0 : 0 ≤ (q : ℝ) / N := by positivity
    linarith
  unfold fejerMixtureCoeff
  exact mul_le_of_le_one_right (combCoeff_pos hN q).le htri1

/-- The convex Fejér mixture at one site, with the same geometric weights as the comb expansion. -/
theorem fejerPolynomial_eq_singleSiteMixture {L N : ℕ} (hN : 1 ≤ N)
    (x : Site L) (ψ : Site L → ℝ) :
    fejerPolynomial N (ψ x) =
      ∑ q ∈ Finset.Icc 1 N, combWeight N q *
        (1 + fejerMixtureCoeff N q * Real.cos ((q : ℝ) * ψ x)) := by
  rw [fejerPolynomial_eq_kp]
  simp only [mul_add, Finset.sum_add_distrib, mul_one]
  rw [sum_combWeight hN]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  calc
    2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * ψ x) =
        (combWeight N q * combCoeff N q) *
          (fejerTriangularFactor N q * Real.cos ((q : ℝ) * ψ x)) := by
            rw [combWeight_mul_combCoeff hN]
            simp [fejerTriangularFactor, fejerCosineCoefficient]
            ring
    _ = combWeight N q *
        (fejerMixtureCoeff N q * Real.cos ((q : ℝ) * ψ x)) := by
          simp only [fejerMixtureCoeff]
          ring

/-- The full GFF Fejér product has the explicit exterior-root factor `N`. -/
theorem gffFejerWeight_eq_rootFactor_mul_rootedProduct {L N : ℕ} (hN : 1 ≤ N)
    (ψ : RotatorDualFace L → ℝ) (hψ : ψ none = 0) :
    gffFejerWeight N ψ = (N : ℝ) * ∏ j, rootedFejerLam L N j (ψ j) := by
  simp only [gffFejerWeight, rootedFejerLam, Fintype.prod_option,
    ite_true, Option.some_ne_none, ite_false, one_mul]
  rw [hψ, fejerPolynomial_zero N (by omega : 0 < N)]

/-- A product of one-site factors is the terminal charge product for that assignment. -/
theorem prod_singleSite_eq_fejerActivity {L N : ℕ} {f : Site L → ℕ}
    (hf : ∀ x, 1 ≤ f x) (φ : Site L → ℝ) :
    ∏ x, (1 + fejerActivity N (siteCharge f x) *
      Real.cos ((f x : ℝ) * φ x)) =
      chargeFactorProduct (singleSiteEnsemble f) (fejerActivity N) φ := by
  unfold chargeFactorProduct singleSiteEnsemble
  rw [Finset.prod_image fun x _ y _ h => siteCharge_injective hf h]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [chargeFactor, chargePhase_siteCharge]

/-- Expanding every site gives a finite convex mixture of single-site charge ensembles. -/
theorem prod_fejerPolynomial_eq_singleSiteMixture {L N : ℕ} (hN : 1 ≤ N)
    (φ : Site L → ℝ) :
    ∏ x, fejerPolynomial N (φ x) =
      ∑ f ∈ Fintype.piFinset (fun _ : Site L => Finset.Icc 1 N),
        (∏ x, combWeight N (f x)) *
          chargeFactorProduct (singleSiteEnsemble f) (fejerActivity N) φ := by
  classical
  simp_rw [fejerPolynomial_eq_singleSiteMixture hN]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf1 : ∀ x, 1 ≤ f x := fun x =>
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf x)).1
  rw [Finset.prod_mul_distrib, ← prod_singleSite_eq_fejerActivity hf1]
  apply congrArg
  apply Finset.prod_congr rfl
  intro x hx
  rw [fejerActivity_siteCharge f x ((Finset.mem_Icc.mp
    (Fintype.mem_piFinset.mp hf x)).2)]

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
