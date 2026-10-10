/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.SOSDirichletLaw
public import FroehlichSpencer.BKT.SOS.Source.Theorem73
public import FroehlichSpencer.BKT.SOS.Peierls.Variance
public import Mathlib.Probability.Notation
import Mathlib.Tactic

/-!
The distance lemmas serve Theorem 7.3
(`log(1 + r₂) ≤ 2 log(1 + r_∞)`, the boundary depth), and `lintegral_sq_eq` the roughening
transition.

The gate and the two roots are proved in
`BKT/Provider/`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.SOSDirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site siteBoundaryDepth euclideanSiteDistance)
open FroehlichSpencer.BKT.SOS.Roughening (sosHeightWeight sosHeightWeight_pos sosPartition
  sosVariance pinnedGrad pinnedField linfDist)

/-! ### The weight -/

/-- The surface bond weight of `sosDirichletLaw`. -/
def dirichletWeight (L : ℕ) (β : ℝ) (n : Fin L × Fin L → ℤ) : ℝ :=
  ∏ e, Real.exp (-(β * |((((squareZero L).src e).elim 0 n -
    ((squareZero L).tgt e).elim 0 n : ℤ) : ℝ)|))

theorem cast_elim_sub {L : ℕ} (n : Fin L × Fin L → ℤ) (a b : Option (Fin L × Fin L)) :
    (((a.elim 0 n - b.elim 0 n : ℤ)) : ℝ) =
      pinnedField (fun x => (n x : ℝ)) a - pinnedField (fun x => (n x : ℝ)) b := by
  cases a <;> cases b <;> simp only [pinnedField, Option.elim_none, Option.elim_some,
    Int.cast_sub, Int.cast_zero]

theorem dirichletWeight_eq (L : ℕ) (β : ℝ) (n : Fin L × Fin L → ℤ) :
    dirichletWeight L β n = sosHeightWeight L β n := by
  unfold dirichletWeight sosHeightWeight
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [cast_elim_sub, SOS.Roughening.pinnedGrad_apply]
  rfl

theorem dirichletWeight_pos (L : ℕ) (β : ℝ) (n : Fin L × Fin L → ℤ) : 0 < dirichletWeight L β n :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

theorem summable_exp_neg_abs_int (c : ℝ) (hc : 0 < c) :
    Summable (fun z : ℤ => Real.exp (-c * |(z : ℝ)|)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · convert (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hc)) using 1
    ext n
    simp [abs_of_nonneg]
    ring
  · convert (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hc)) using 1
    ext n
    simp [abs_of_nonneg]
    ring

/-- `SquareFreeEdge 1` is empty: `{0}²` has no two distinct points. -/
theorem squareFreeEdge_one_isEmpty : IsEmpty (SquareFreeEdge 1) :=
  ⟨fun e => by
    have h := e.2.1
    have : e.1.1 = e.1.2 := Subsingleton.elim _ _
    rw [this] at h
    exact lt_irrefl _ h⟩

theorem summable_dirichletWeight (L : ℕ) {β : ℝ} (hβ : 0 < β) :
    Summable (dirichletWeight L β) := by
  rcases Nat.lt_or_ge 1 L with hL | hL
  · rw [show dirichletWeight L β = sosHeightWeight L β from funext (dirichletWeight_eq L β)]
    exact SOS.Source.sosHeightWeight_summable_all_beta hL hβ
  · rcases Nat.lt_or_ge L 1 with h0 | h1
    · have : L = 0 := by omega
      subst this
      exact .of_finite
    · have : L = 1 := by omega
      subst this
      -- one site, with a bond to the wired vertex
      let j : Fin 1 × Fin 1 := (0, 0)
      have hcard : (Finset.univ.filter fun e : SquareFreeEdge 1 =>
          (squareFree 1).src e = j ∨ (squareFree 1).tgt e = j).card = 0 := by
        have := squareFreeEdge_one_isEmpty
        simp
      let e₀ : SquareFreeEdge 1 ⊕ Σ j : Fin 1 × Fin 1, Fin (4 - (Finset.univ.filter
          fun e : SquareFreeEdge 1 => (squareFree 1).src e = j ∨ (squareFree 1).tgt e = j).card) :=
        Sum.inr ⟨j, ⟨0, by rw [hcard]; norm_num⟩⟩
      have hle : ∀ n : Fin 1 × Fin 1 → ℤ,
          dirichletWeight 1 β n ≤ Real.exp (-β * |((n j : ℤ) : ℝ)|) := by
        intro n
        unfold dirichletWeight
        set f := fun e => Real.exp (-(β * |((((squareZero 1).src e).elim 0 n -
              ((squareZero 1).tgt e).elim 0 n : ℤ) : ℝ)|)) with hf
        have hf1 : ∀ e, f e ≤ 1 := fun e => Real.exp_le_one_iff.mpr (by
          have := abs_nonneg ((((squareZero 1).src e).elim 0 n -
            ((squareZero 1).tgt e).elim 0 n : ℤ) : ℝ)
          nlinarith)
        have hrest : ∏ e ∈ Finset.univ.erase e₀, f e ≤ 1 :=
          Finset.prod_le_one₀ (fun _ _ => (Real.exp_pos _).le) fun e _ => hf1 e
        calc ∏ e, f e = f e₀ * ∏ e ∈ Finset.univ.erase e₀, f e :=
              (Finset.mul_prod_erase _ _ (Finset.mem_univ e₀)).symm
          _ ≤ f e₀ * 1 := mul_le_mul_of_nonneg_left hrest (Real.exp_pos _).le
          _ = Real.exp (-β * |((n j : ℤ) : ℝ)|) := by
              simp [hf, e₀, squareZero, j]
      have hs : Summable fun n : Fin 1 × Fin 1 → ℤ => Real.exp (-β * |((n j : ℤ) : ℝ)|) :=
        (summable_exp_neg_abs_int β hβ).comp_injective (fun a b h => by
          funext x
          have hx : x = j := Subsingleton.elim _ _
          subst hx
          exact h)
      exact Summable.of_nonneg_of_le (fun n => (dirichletWeight_pos 1 β n).le) hle hs

/-! ### The law -/

/-- The unnormalized measure of `sosDirichletLaw`. -/
def dirichletMass (L : ℕ) (β : ℝ) : Measure (Fin L × Fin L → ℤ) :=
  Measure.sum fun n => ENNReal.ofReal (dirichletWeight L β n) • Measure.dirac n

theorem sosDirichletLaw_eq (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    sosDirichletLaw L β hβ = (dirichletMass L β Set.univ)⁻¹ • dirichletMass L β := rfl

theorem dirichletMass_univ (L : ℕ) {β : ℝ} (hβ : 0 < β) :
    dirichletMass L β Set.univ = ENNReal.ofReal (∑' n, dirichletWeight L β n) := by
  rw [dirichletMass, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun n => (dirichletWeight_pos L β n).le)
    (summable_dirichletWeight L hβ)).symm

theorem tsum_dirichletWeight_pos (L : ℕ) {β : ℝ} (hβ : 0 < β) :
    0 < ∑' n, dirichletWeight L β n :=
  (summable_dirichletWeight L hβ).tsum_pos (fun n => (dirichletWeight_pos L β n).le) 0
    (dirichletWeight_pos L β 0)

/-- For `L > 1` the surface law is the internal pinned law. -/
theorem sosDirichletLaw_eq_sosLaw {L : ℕ} (hL : 1 < L) {β : ℝ} (hβ : 0 < β) :
    sosDirichletLaw L β hβ = SOS.Source.sosLaw hL β hβ := by
  have hZ : 0 < sosPartition L β := (SOS.Source.sosPartition_finite_positive hL hβ).2
  have htsum : ∑' n, dirichletWeight L β n = sosPartition L β := by
    simp_rw [dirichletWeight_eq]; rfl
  ext s hs
  rw [sosDirichletLaw_eq, Measure.smul_apply, smul_eq_mul, dirichletMass_univ L hβ, htsum,
    SOS.Source.sosLaw, dirichletMass, Measure.sum_apply _ hs, Measure.sum_apply _ hs,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [Measure.smul_apply, smul_eq_mul, dirichletWeight_eq]
  rw [← mul_assoc, ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm (ENNReal.ofReal _)]

/-! ### Theorem 7.3 -/

theorem euclid_le_two_linf {L : ℕ} (u v : Site L) :
    euclideanSiteDistance u v ≤ 2 * (linfDist u v : ℝ) := by
  have h1 : Int.natAbs ((u.1.val : ℤ) - v.1.val) ≤ linfDist u v := by
    unfold linfDist; exact le_max_left _ _
  have h2 : Int.natAbs ((u.2.val : ℤ) - v.2.val) ≤ linfDist u v := by
    unfold linfDist; exact le_max_right _ _
  have ha : |((u.1.val : ℝ) - v.1.val)| ≤ (linfDist u v : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h1
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at h
    exact h
  have hb : |((u.2.val : ℝ) - v.2.val)| ≤ (linfDist u v : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h2
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at h
    exact h
  unfold euclideanSiteDistance
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs ((u.1.val : ℝ) - v.1.val), sq_abs ((u.2.val : ℝ) - v.2.val),
    abs_nonneg ((u.1.val : ℝ) - v.1.val), abs_nonneg ((u.2.val : ℝ) - v.2.val)]

/-- `log (1 + min e d) ≤ 2 log (1 + min ℓ d)` when `e ≤ 2ℓ`. -/
theorem log_min_le {e ℓ d : ℝ} (he : 0 ≤ e) (hℓ : 0 ≤ ℓ) (hd : 0 ≤ d) (heℓ : e ≤ 2 * ℓ) :
    Real.log (1 + min e d) ≤ 2 * Real.log (1 + min ℓ d) := by
  have hm : 0 ≤ min ℓ d := le_min hℓ hd
  rw [← Real.log_rpow (by positivity)]
  apply Real.log_le_log (by positivity)
  have : 1 + min e d ≤ (1 + min ℓ d) ^ 2 := by
    rcases le_total ℓ d with h | h
    · rw [min_eq_left h]
      have : min e d ≤ e := min_le_left _ _
      nlinarith
    · rw [min_eq_right h]
      have : min e d ≤ d := min_le_right _ _
      nlinarith
  simpa [Real.rpow_two] using this

theorem depth_eq {L : ℕ} (u : Fin L × Fin L) :
    ((min (min ((u.1 : ℕ) + 1) (L - u.1)) (min ((u.2 : ℕ) + 1) (L - u.2)) : ℕ) : ℝ) =
      (siteBoundaryDepth u : ℝ) := by
  unfold siteBoundaryDepth
  congr 1
  omega

theorem euclid_eq {L : ℕ} (u v : Fin L × Fin L) :
    Real.sqrt ((((u.1 : ℕ) : ℝ) - v.1) ^ 2 + (((u.2 : ℕ) : ℝ) - v.2) ^ 2) =
      euclideanSiteDistance u v := rfl

/-! ### The roughening transition -/

theorem sosVariance_self (L : ℕ) (β : ℝ) (u : Site L) : sosVariance L β u u = 0 := by
  simp [sosVariance]

theorem lintegral_sq_eq {L : ℕ} (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (u v : Fin L × Fin L) :
    ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ =
      ENNReal.ofReal (sosVariance L β u v) := by
  rw [sosDirichletLaw_eq_sosLaw hL hβ, ← SOS.Source.sosVarianceIntegral_eq_sosVariance hL hβ u v]
  exact (ofReal_integral_eq_lintegral_ofReal (SOS.Source.sosVarianceIntegral_integrable hL hβ u v)
    (Eventually.of_forall fun _ => sq_nonneg _)).symm

end FroehlichSpencer.BKT.Bridge.SOSDirichlet

end
