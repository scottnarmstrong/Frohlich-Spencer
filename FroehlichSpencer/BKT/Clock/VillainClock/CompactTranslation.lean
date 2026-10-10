/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.CompactLaw
public import FroehlichSpencer.BKT.Clock.Compact.Translation
import Mathlib.Tactic

/-!
# The translation step on the compact Villain law

The Villain analogue of `Clock/Compact/Translation.lean`, for the marked expansion of FS81
Theorem 7.1(2) under Remark 4. The shift cost is the cosine clock cost `β(cosh(u/n) − 1)`, which
bounds the Villain shift ratio (`villainClockEdgeWeight_ratio_le_clockCost`). Every statement here
therefore reads as its cosine counterpart with the Villain law and the Villain local factors.

* `norm_edgeRatio_villain_le`, `integrable_character_mul_edgeRatio_villain`;
* `villainLocalFactor_norm_le_one`, `villainLocalFactor_im_eq_zero`: the Villain local factors are
  real and bounded by one;
* `integral_character_villainCompactLaw_eq_zero`: charged characters integrate to zero;
* **`integral_prod_add_mul_cos_villainCompactLaw`**: the translated product.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open MeasureTheory Complex
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Reduction (gffCharacter norm_gffCharacter signSet mem_signSet)

variable {V : Type} [Fintype V] {E : Type} [Fintype E]

/-! ### The Villain edge ratio -/

/-- The Villain edge ratio is continuous in the real gradients. -/
theorem continuous_edgeRatio_villain {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n) (b : E → ℝ) :
    Continuous fun x : E → ℝ => edgeRatio (villainClockEdgeWeight β n) b x := by
  unfold edgeRatio
  refine continuous_finsetProd _ fun e _ => ?_
  refine Continuous.div ?_ ?_ fun x => villainClockEdgeWeight_ofReal_ne_zero β n (x e) hβ
  · exact (continuous_villainClockEdgeWeight β hβ hn).comp (by fun_prop)
  · exact (continuous_villainClockEdgeWeight β hβ hn).comp (by fun_prop)

/-- `|R_b(x)| ≤ e^{∑_e c(b_e)}` for the Villain weight, with the cosine clock cost. -/
theorem norm_edgeRatio_villain_le {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n) (b x : E → ℝ) :
    ‖edgeRatio (villainClockEdgeWeight β n) b x‖ ≤ Real.exp (∑ e, clockShiftCost β n (b e)) := by
  unfold edgeRatio
  rw [norm_prod, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun e _ => norm_nonneg _)
    fun e _ => villainClockEdgeWeight_ratio_le_clockCost hβ hn (x e) (b e)

theorem integrable_character_mul_edgeRatio_villain {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] (G : Multigraph V E) (τ : V → ℝ) (b : E → ℝ) :
    Integrable (fun φ => gffCharacter τ φ * edgeRatio (villainClockEdgeWeight β n) b (G.grad φ))
      μ := by
  refine Integrable.of_bound ?_ (Real.exp (∑ e, clockShiftCost β n (b e)))
    (ae_of_all _ fun φ => ?_)
  · refine ((Reduction.continuous_gffCharacter τ).mul
      ((continuous_edgeRatio_villain hβ hn b).comp ?_)).aestronglyMeasurable
    unfold Multigraph.grad
    fun_prop
  · rw [norm_mul, norm_gffCharacter, one_mul]
    exact norm_edgeRatio_villain_le hβ hn b _

/-- The Villain local factors are bounded by one. -/
theorem villainLocalFactor_norm_le_one {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn : 0 < n)
    (b x : E → ℝ) {W : ℝ} (hb : ∀ e, |b e| ≤ W) (θ : ℝ) :
    ‖localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) b x θ‖ ≤ 1 :=
  norm_localFactor_le_one (fun t u _ => villainClockEdgeWeight_ratio_le_clockCost hβ hn t u)
    b x hb θ

/-- The Villain local factors are real. -/
theorem villainLocalFactor_im_eq_zero (β n : ℝ) (b x : E → ℝ) {W : ℝ} (hb : ∀ e, |b e| ≤ W)
    (θ : ℝ) :
    (localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) b x θ).im = 0 :=
  localFactor_im_eq_zero (fun z _ => villainClockEdgeWeight_conj β n z)
    (fun u => by simp [clockShiftCost, neg_div, Real.cosh_neg]) b x hb θ

/-- Characters of a compatible charge with nonzero total charge integrate to zero (the constant
imaginary shift of the compact box). -/
theorem integral_character_villainCompactLaw_eq_zero {n β : ℝ} (hn : 0 < n) (hβ : 0 < β)
    (G : Multigraph V E) (τ : V → ℝ) (hτ : IsClockCompatible n τ) (hQ : ∑ j, τ j ≠ 0) :
    ∫ φ, gffCharacter τ φ ∂villainCompactLaw β n G = 0 := by
  set t : ℝ := 1 / ∑ j, τ j
  have h := integral_villainCompactLaw_characterTranslation hn hβ G τ (fun _ => t) hτ
  have hg : G.grad (fun _ : V => t) = 0 := by
    funext e; simp [Multigraph.grad]
  have hR : ∀ φ : V → ℝ,
      edgeRatio (villainClockEdgeWeight β n) (G.grad fun _ : V => t) (G.grad φ) = 1 := by
    intro φ
    rw [hg]
    exact edgeRatio_zero _ _ fun e => villainClockEdgeWeight_ofReal_ne_zero β n _ hβ
  simp_rw [hR, mul_one] at h
  have hsum : ∑ j, t * τ j = 1 := by
    rw [← Finset.mul_sum]
    exact one_div_mul_cancel hQ
  rw [hsum] at h
  have hne : Complex.exp (-((1 : ℝ) : ℂ)) ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re, Complex.one_re] at this
    have h2 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have h3 : (1 - Complex.exp (-((1 : ℝ) : ℂ))) * ∫ φ, gffCharacter τ φ ∂villainCompactLaw β n G = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd (sub_eq_zero.1 h4).symm hne
  · exact h4

/-- **The translation step on the compact Villain law** (FS81 Lemma 4.3/(6.18) for the compact
box): for compatible real densities `ϱ_i` (no neutrality needed), factors `A_i + B_i cos θ_i`,
`θ_i = ⟨φ, ϱ_i⟩ + s_i`, and real waves with `⟨a_i, ϱ_{i'}⟩ = 0` for `i ≠ i'` and pairwise disjoint
gradient supports, `∫ ∏ (A_i + B_i cos θ_i) dμ = ∫ ∏ (A_i + B_i e^{-E_c(a_i, ϱ_i)} F_i) dμ`
with the clock cost and `F_i = localFactor w c (∇a_i) (∇φ) θ_i`. No strip condition is needed. -/
theorem integral_prod_add_mul_cos_villainCompactLaw {n β : ℝ} (hn : 0 < n) (hβ : 0 < β)
    (G : Multigraph V E) {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (hcomp : ∀ i, IsClockCompatible n (ϱ i)) (A B s : ι → ℝ) (a : ι → V → ℝ)
    (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, G.grad (a i) e = 0 ∨ G.grad (a i') e = 0) :
    ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) ∂villainCompactLaw β n G =
      ∫ φ, ∏ i, ((A i : ℂ) +
        ((B i * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear G) (a i) (ϱ i)) :
          ℝ) : ℂ) *
        localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) (gradLinear G (a i))
          (gradLinear G φ) (∑ j, φ j * ϱ i j + s i)) ∂villainCompactLaw β n G := by
  classical
  have hμ := isProbabilityMeasure_villainCompactLaw G hβ hn
  set w := villainClockEdgeWeight β n
  set D := gradLinear G
  have hDg : ∀ f : V → ℝ, D f = G.grad f := fun f => rfl
  set P := Fintype.piFinset fun _ : ι => signSet with hP
  set coef : (ι → ℤ) → ℂ := fun m =>
    ∏ i, (mixedCoeff (A i) (B i) (m i) * Complex.exp (I * ((m i : ℂ) * s i))) with hcoef
  set τ : (ι → ℤ) → V → ℝ := fun m j => ∑ i, (m i : ℝ) * ϱ i j with hτ
  set an : (ι → ℤ) → V → ℝ := fun m j => ∑ i, (m i : ℝ) * a i j with han
  set ε : ι → ℝ := fun i => ∑ j, a i j * ϱ i j with hε
  have hτc : ∀ m, IsClockCompatible n (τ m) := fun m =>
    IsClockCompatible.sum_smul Finset.univ m ϱ fun i _ => hcomp i
  have hwx : ∀ φ : V → ℝ, ∀ e, w ((D φ + 0) e) ≠ 0 := fun φ e => villainClockEdgeWeight_ofReal_ne_zero β n _ hβ
  have hleft : ∀ φ : V → ℝ,
      ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) =
        ∑ m ∈ P, coef m * gffCharacter (τ m) φ := by
    intro φ
    rw [prod_add_mul_cos_eq_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.prod_mul_distrib, prod_exp_eq_character m ϱ s φ, hcoef, ← mul_assoc,
      ← Finset.prod_mul_distrib]
  have hright : ∀ φ : V → ℝ,
      ∏ i, ((A i : ℂ) + ((B i * Real.exp (-∑ j, a i j * ϱ i j) : ℝ) : ℂ) *
          translatedCos w (D (a i)) (D φ + 0) (∑ j, φ j * ϱ i j + s i)) =
        ∑ m ∈ P, coef m * Complex.exp (-((∑ j, an m j * τ m j : ℝ) : ℂ)) *
          (gffCharacter (τ m) φ * edgeRatio w (D (an m)) (D φ + 0)) := by
    intro φ
    rw [prod_translated_eq_sum A B (fun i => ∑ j, φ j * ϱ i j + s i) ε w (fun i => D (a i))
      (D φ + 0) (hwx φ)]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hratio : edgeRatio w (D (an m)) (D φ + 0) =
        ∏ i, edgeRatio w ((m i : ℝ) • D (a i)) (D φ + 0) := by
      rw [grad_signVector D a m]
      refine edgeRatio_sum Finset.univ w _ _ (hwx φ) fun i _ i' _ hne e => ?_
      rcases hdisj i i' hne e with h | h
      · exact Or.inl (by simp [hDg, h])
      · exact Or.inr (by simp [hDg, h])
    have hpair : Complex.exp (-((∑ j, an m j * τ m j : ℝ) : ℂ)) =
        ∏ i, Complex.exp (-((m i : ℂ) ^ 2 * ε i)) := by
      rw [← Complex.exp_sum]
      congr 1
      simp only [han, hτ, hε]
      rw [pairing_signVector a ϱ horth m]
      push_cast
      rw [← Finset.sum_neg_distrib]
    rw [hratio, hpair]
    simp only [Finset.prod_mul_distrib]
    rw [prod_exp_eq_character m ϱ s φ]
    simp only [hcoef, Finset.prod_mul_distrib]
    ring
  have hint : ∀ m ∈ P, Integrable
      (fun φ => coef m * Complex.exp (-((∑ j, an m j * τ m j : ℝ) : ℂ)) *
        (gffCharacter (τ m) φ * edgeRatio w (D (an m)) (D φ + 0))) (villainCompactLaw β n G) := by
    intro m _
    refine Integrable.const_mul ?_ _
    have := integrable_character_mul_edgeRatio_villain hβ hn (villainCompactLaw β n G) G (τ m)
      (D (an m))
    simpa [hDg] using this
  have htrans : ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ)
      ∂villainCompactLaw β n G =
      ∫ φ, ∏ i, ((A i : ℂ) + ((B i * Real.exp (-∑ j, a i j * ϱ i j) : ℝ) : ℂ) *
        translatedCos w (D (a i)) (D φ + 0) (∑ j, φ j * ϱ i j + s i)) ∂villainCompactLaw β n G := by
    simp_rw [hleft, hright]
    rw [integral_finsetSum P fun m _ =>
        (Reduction.integrable_gffCharacter _ (τ m)).const_mul _,
      integral_finsetSum P hint]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, integral_const_mul,
      integral_villainCompactLaw_characterTranslation hn hβ G (τ m) (an m) (hτc m), mul_assoc]
    congr 2
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    simp only [hDg, add_zero]
    rfl
  rw [htrans]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  have hc : ∀ u, clockShiftCost β n (-u) = clockShiftCost β n u := fun u => by
    simp [clockShiftCost, neg_div, Real.cosh_neg]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, mul_assoc, mul_assoc,
    exp_mul_translatedCos w (c := clockShiftCost β n) hc D (a i) (ϱ i), add_zero]


end FroehlichSpencer.BKT.Clock.VillainClock

end
