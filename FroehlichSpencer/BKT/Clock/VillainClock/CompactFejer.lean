/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.CompactLaw
public import FroehlichSpencer.BKT.Clock.VillainClock.DualGinibre
public import FroehlichSpencer.BKT.Clock.Disorder.GridSeam
import Mathlib.Tactic

/-!
# The Fejér limit of the compact Villain law

The Villain analogue of `Clock/Compact/FejerLimit.lean` and `Clock/Compact/TwoPoint.lean`: the
Fejér-weighted compact Villain law converges to the `ℤ_N` Villain clock. Concretely, the Fejér
ratio of `cos((ξ/N)(φ_o − φ_x))` tends to the Villain-clock two-point function
`VillainClock.model` on the square `{0, …, L}²`.

* `integral_villainCompactLaw_eq_base`: the law as a density on the box;
* `tendsto_integral_villainCompactLaw_fejer`: the Fejér limit (cell-center sums);
* `villainCompactDensity_cellCenter`: the density at the cell centers is the Villain-clock weight;
* **`tendsto_villainFejerRatio`**.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Disorder

section Law

variable {V : Type} [Fintype V] {E : Type} [Fintype E]

/-- The unnormalized Villain density on fields indexed by `V`. -/
def villainCompactDensity (β n : ℝ) (G : Multigraph V E) (φ : V → ℝ) : ℝ :=
  ∏ e, villainWeight β (G.grad φ e / n)

omit [Fintype V] in
theorem villainCompactDensity_pos {β : ℝ} (hβ : 0 < β) (n : ℝ) (G : Multigraph V E)
    (φ : V → ℝ) : 0 < villainCompactDensity β n G φ :=
  Finset.prod_pos fun _ _ => VillainWeight.villainWeight_pos hβ _

theorem villainBoxDensity_eq (β n : ℝ) (G : Multigraph V E) (φ : Fin (Fintype.card V) → ℝ) :
    villainBoxDensity β n (relabelGraph G (siteEquiv V)) φ =
      villainCompactDensity β n G (pullField V φ) := by
  unfold villainBoxDensity villainCompactDensity
  rw [grad_pullField]

theorem continuous_villainCompactDensity {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (G : Multigraph V E) : Continuous (villainCompactDensity β n G) := by
  have h := continuous_villainBoxDensity hβ hn (relabelGraph G (siteEquiv V))
  have hpush : villainCompactDensity β n G = fun ψ =>
      villainBoxDensity β n (relabelGraph G (siteEquiv V))
        (fun j => ψ ((siteEquiv V).symm j)) := by
    funext ψ
    rw [villainBoxDensity_eq]
    congr 1
    funext v
    simp [pullField]
  rw [hpush]
  exact h.comp (by fun_prop)

omit [Fintype V] in
theorem villainCompactDensity_le {β : ℝ} (hβ : 0 < β) (n : ℝ) (G : Multigraph V E)
    (φ : V → ℝ) : villainCompactDensity β n G φ ≤ villainWeight β 0 ^ Fintype.card E := by
  unfold villainCompactDensity
  calc
    ∏ e, villainWeight β (G.grad φ e / n) ≤ ∏ _e : E, villainWeight β 0 :=
      Finset.prod_le_prod₀ (fun _ _ => (VillainWeight.villainWeight_pos hβ _).le)
        fun e _ => villainWeight_le_zero hβ _
    _ = _ := by simp

theorem integral_villainCompactLaw_eq_base {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (G : Multigraph V E) (f : (V → ℝ) → ℝ) :
    ∫ φ, f φ ∂villainCompactLaw β n G =
      ((villainBoxMass β n (relabelGraph G (siteEquiv V)))⁻¹).toReal *
        ∫ φ, villainCompactDensity β n G (pullField V φ) * f (pullField V φ)
          ∂clockAngleBaseMeasure n := by
  rw [integral_villainCompactLaw]
  set G' := relabelGraph G (siteEquiv V)
  set ρ := villainBoxDensity β n G'
  have hρmeas : Measurable ρ := (continuous_villainBoxDensity hβ hn G').measurable
  have hρnonneg : ∀ φ, 0 ≤ ρ φ := fun φ =>
    (pow_pos (Real.exp_pos _) _).le.trans (villainBoxDensity_bounds hβ n G' φ).1
  have hbase :
      ∫ φ, f (pullField V φ) ∂(clockAngleBaseMeasure n).withDensity
          (fun φ => ENNReal.ofReal (ρ φ)) =
        ∫ φ, ρ φ * f (pullField V φ) ∂clockAngleBaseMeasure n := by
    calc
      _ = ∫ φ, (ENNReal.ofReal (ρ φ)).toReal • f (pullField V φ) ∂clockAngleBaseMeasure n :=
        integral_withDensity_eq_integral_toReal_smul
          (ENNReal.measurable_ofReal.comp hρmeas)
          (Filter.Eventually.of_forall fun φ => ENNReal.ofReal_lt_top) _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with φ
        simp [ENNReal.toReal_ofReal (hρnonneg φ)]
  change ∫ φ, f (pullField V φ) ∂((villainBoxMass β n G')⁻¹ •
    (clockAngleBaseMeasure n).withDensity fun φ => ENNReal.ofReal (ρ φ)) = _
  rw [integral_smul_measure, hbase, smul_eq_mul]
  congr 1

/-- The Fejér-weighted Villain-law integral converges to the cell-center sum. -/
theorem tendsto_integral_villainCompactLaw_fejer [DecidableEq V] {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n)
    (G : Multigraph V E) (g : (V → ℝ) → ℝ) (hg : Continuous g) {C : ℝ}
    (hgb : ∀ φ, |g φ| ≤ C) :
    Tendsto (fun M : ℕ => ∫ φ, g φ * ∏ v, fejerPolynomial M (φ v - clockOffset n)
        ∂villainCompactLaw β n G) atTop
      (𝓝 (((villainBoxMass β n (relabelGraph G (siteEquiv V)))⁻¹).toReal *
        ((2 * Real.pi) ^ Fintype.card V * ∑ k : V → Fin n,
          villainCompactDensity β n G (fun v => cellCenter n (k v)) *
            g (fun v => cellCenter n (k v))))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set e := siteEquiv V
  set G₁ : (Fin (Fintype.card V) → ℝ) → ℝ := fun φ =>
    villainCompactDensity β n G (pullField V φ) * g (pullField V φ) with hG₁
  have hpull : Continuous (pullField V) := by
    unfold pullField; fun_prop
  have hG₁c : Continuous G₁ :=
    ((continuous_villainCompactDensity hβ hn' G).comp hpull).mul (hg.comp hpull)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgb 0)
  have hG₁b : ∀ φ, |G₁ φ| ≤ villainWeight β 0 ^ Fintype.card E * C := by
    intro φ
    simp only [hG₁]
    rw [abs_mul, abs_of_pos (villainCompactDensity_pos hβ _ G _)]
    exact mul_le_mul (villainCompactDensity_le hβ _ G _) (hgb _) (abs_nonneg _)
      (pow_nonneg (VillainWeight.villainWeight_pos hβ 0).le _)
  have hlim := tendsto_integral_compactAngleBase_fejer (n := n) G₁ hG₁c hG₁b
  have heq : ∀ M : ℕ, ∫ φ, g φ * ∏ v, fejerPolynomial M (φ v - clockOffset n)
      ∂villainCompactLaw β n G =
      ((villainBoxMass β n (relabelGraph G e))⁻¹).toReal *
        ∫ φ, G₁ φ * ∏ j, fejerPolynomial M (φ j - clockOffset n)
          ∂compactAngleBaseMeasure (2 * Real.pi * n) := by
    intro M
    rw [integral_villainCompactLaw_eq_base hβ hn']
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp only [hG₁, pullField]
    rw [← e.prod_comp fun j => fejerPolynomial M (φ j - clockOffset n)]
    ring
  simp_rw [heq]
  convert hlim.const_mul ((villainBoxMass β n (relabelGraph G e))⁻¹).toReal using 3
  · symm
    congr 1
    refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl (Fin n)))
      (fun k : Fin (Fintype.card V) → Fin n => G₁ fun j => cellCenter n (k j))
      (fun k : V → Fin n => villainCompactDensity β n G (fun v => cellCenter n (k v)) *
        g (fun v => cellCenter n (k v))) fun k => ?_
    simp only [hG₁, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply]
    congr 2

end Law

/-! ### The two-point function -/

/-- The free-square Villain density at the cell centers is the Villain-clock weight. -/
theorem villainCompactDensity_cellCenter (N L : ℕ) (hN : 0 < N) (β : ℝ)
    (k : RotatorSpinSite L → Fin N) :
    villainCompactDensity β N (squareFree (L + 1)) (fun v => cellCenter N (k v)) =
      configurationWeight (rotatorFreeGraph L) β N k := by
  unfold villainCompactDensity configurationWeight
  refine Fintype.prod_equiv (squareFreeSourceGraphIsomorphism (L + 1)).edges _ _ fun e => ?_
  rw [squareFree_grad_eq_gridSign]
  have hcc : ∀ e' : RotatorInternalBond L,
      (Lattice2D.squareFreeGraph (L + 1)).grad (fun v => cellCenter N (k v)) e' / N =
        angleField N k ((rotatorFreeGraph L).src e') -
          angleField N k ((rotatorFreeGraph L).tgt e') := by
    intro e'
    rw [Multigraph.grad, cellCenter_sub N _ _ hN]
    rfl
  rcases gridSign_eq (L + 1) e with h | h
  · rw [h, one_mul, hcc]
  · rw [h, neg_one_mul, neg_div, VillainWeight.villainWeight_neg, hcc]

/-- **The Fejér ratio converges to the Villain-clock two-point function**: under the compact
Villain law on the KP free square of side `L + 1`, the ratio of the Fejér-weighted integrals of
`cos((ξ/N)(φ_o − φ_x))` and of `1` tends to the two-point function of the Villain clock on
`{0, …, L}²`. -/
theorem tendsto_villainFejerRatio (N L : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 < β) (ξ : ℕ)
    (o x : RotatorSpinSite L) :
    Tendsto (fun M : ℕ =>
      (∫ φ, Real.cos ((ξ : ℝ) / N * (φ o - φ x)) * ∏ v, fejerPolynomial M (φ v - clockOffset N)
          ∂villainCompactLaw β N (squareFree (L + 1))) /
        ∫ φ, ∏ v, fejerPolynomial M (φ v - clockOffset N)
          ∂villainCompactLaw β N (squareFree (L + 1)))
      atTop (𝓝 ((model N hN β hβ).twoPoint (ξ : ℤ) (squareBoxZ L) (siteToZ o) (siteToZ x))) := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set G := squareFree (L + 1)
  set m := ((villainBoxMass β N (relabelGraph G (siteEquiv (RotatorSpinSite L))))⁻¹).toReal
  have hm : 0 < m := by
    have h0 := villainBoxMass_pos hβ hN' (relabelGraph G (siteEquiv (RotatorSpinSite L)))
    have h1 := villainBoxMass_ne_top hβ (N : ℝ) (relabelGraph G (siteEquiv (RotatorSpinSite L)))
    exact ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0.ne')
  have hnum := tendsto_integral_villainCompactLaw_fejer hβ hN G
    (fun φ => Real.cos ((ξ : ℝ) / N * (φ o - φ x))) (by fun_prop) (C := 1)
    (fun φ => Real.abs_cos_le_one _)
  have hden := tendsto_integral_villainCompactLaw_fejer hβ hN G (fun _ => (1 : ℝ))
    continuous_const (C := 1) (fun _ => by simp)
  simp only [one_mul, mul_one] at hden
  have hS0 : 0 < ∑ k : RotatorSpinSite L → Fin N,
      villainCompactDensity β N G (fun v => cellCenter N (k v)) :=
    Finset.sum_pos (fun k _ => villainCompactDensity_pos hβ _ G _)
      ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  have hA : 0 < m * (2 * Real.pi) ^ Fintype.card (RotatorSpinSite L) :=
    mul_pos hm (pow_pos (by positivity) _)
  have hlim := hnum.div hden (by rw [← mul_assoc]; exact (mul_pos hA hS0).ne')
  rw [villainClockModel_twoPoint_squareBox N L hN hβ (ξ : ℤ) o x]
  convert hlim using 2
  rw [← mul_assoc, ← mul_assoc, mul_div_mul_left _ _ hA.ne']
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [villainCompactDensity_cellCenter N L hN β k, mul_comm]
    congr 1
    rw [show ((ξ : ℤ) : ℝ) = (ξ : ℝ) by push_cast; rfl, mul_sub, mul_sub]
    unfold clockAngles cellCenter
    field_simp
    ring_nf
  · exact Finset.sum_congr rfl fun k _ => (villainCompactDensity_cellCenter N L hN β k).symm

end FroehlichSpencer.BKT.Clock.VillainClock

end
