/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.Law
public import FroehlichSpencer.BKT.Generic.Renormalization.Assembly
public import FroehlichSpencer.BKT.Clock.Periodic.Weight
import Mathlib.Tactic

/-!
# The translation step on the compact clock law

The compact-weight replacement of the generic translation step (`Generic/Translation.lean`,
`Generic/Renormalization/AllCharge.lean`). There, `CharacterTranslation` is an interface for the
real-line laws of strip weights. The compact clock law instead translates exactly the compatible
characters, for every real shift.

* `norm_edgeRatio_clock_le`, `integrable_character_mul_edgeRatio_clock`: the clock edge ratio
  `R_b(x)` is continuous and bounded by `e^{∑_e c(b_e)}`.
* `integral_character_clockLaw_eq_zero`: a compatible character of nonzero total charge has
  integral zero. This follows from a constant imaginary shift; it replaces the root-phase
  mechanism of the rooted real-line law.
* **`integral_prod_add_mul_cos_clockLaw`**: the translated product
  `∫ ∏ (A_i + B_i cos θ_i) dμ = ∫ ∏ (A_i + B_i e^{−E_c(a_i, ϱ_i)} F_i) dμ`. It holds for
  compatible real densities and waves with orthogonality and disjoint gradient supports, with the
  clock cost `c(u) = β(cosh(u/n) − 1)` and local factors `F_i` (FS81 (6.18)).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Compact

open MeasureTheory Complex
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Reduction (gffCharacter norm_gffCharacter signSet mem_signSet)

variable {V : Type*} [Fintype V] {E : Type*} [Fintype E]

/-! ### The clock edge ratio -/

theorem clockEdgeWeight_ofReal_ne_zero (β n t : ℝ) : clockEdgeWeight β n (t : ℂ) ≠ 0 :=
  clockEdgeWeight_ne_zero β n _

theorem continuous_clockEdgeWeight (β n : ℝ) : Continuous (clockEdgeWeight β n) := by
  unfold clockEdgeWeight
  fun_prop

/-- The clock edge ratio is continuous in the real gradients. -/
theorem continuous_edgeRatio_clock (β n : ℝ) (b : E → ℝ) :
    Continuous fun x : E → ℝ => edgeRatio (clockEdgeWeight β n) b x := by
  unfold edgeRatio
  refine continuous_finsetProd _ fun e _ => ?_
  refine Continuous.div ?_ ?_ fun x => clockEdgeWeight_ofReal_ne_zero β n (x e)
  · exact (continuous_clockEdgeWeight β n).comp (by fun_prop)
  · exact (continuous_clockEdgeWeight β n).comp (by fun_prop)

/-- `|R_b(x)| ≤ e^{∑_e c(b_e)}` for the clock weight. -/
theorem norm_edgeRatio_clock_le {β : ℝ} (hβ : 0 ≤ β) (n : ℝ) (b x : E → ℝ) :
    ‖edgeRatio (clockEdgeWeight β n) b x‖ ≤ Real.exp (∑ e, clockShiftCost β n (b e)) := by
  unfold edgeRatio
  rw [norm_prod, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun e _ => norm_nonneg _)
    fun e _ => clockEdgeWeight_ratio_le β n hβ (x e) (b e)

theorem integrable_character_mul_edgeRatio_clock {β n : ℝ} (hβ : 0 ≤ β)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] (G : Multigraph V E) (τ : V → ℝ) (b : E → ℝ) :
    Integrable (fun φ => gffCharacter τ φ * edgeRatio (clockEdgeWeight β n) b (G.grad φ)) μ := by
  refine Integrable.of_bound ?_ (Real.exp (∑ e, clockShiftCost β n (b e)))
    (ae_of_all _ fun φ => ?_)
  · refine ((Reduction.continuous_gffCharacter τ).mul
      ((continuous_edgeRatio_clock β n b).comp ?_)).aestronglyMeasurable
    unfold Multigraph.grad
    fun_prop
  · rw [norm_mul, norm_gffCharacter, one_mul]
    exact norm_edgeRatio_clock_le hβ n b _

/-! ### Compatible charges -/

omit [Fintype V] in
theorem isClockCompatible_intCast (n : ℕ) (ϱ : V → ℤ) :
    IsClockCompatible (n : ℝ) (fun j => (ϱ j : ℝ)) :=
  fun j => ⟨(n : ℤ) * ϱ j, by push_cast; ring⟩

omit [Fintype V] in
theorem IsClockCompatible.sum_smul {n : ℝ} {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (ϱ : ι → V → ℝ) (h : ∀ i ∈ s, IsClockCompatible n (ϱ i)) :
    IsClockCompatible n (fun j => ∑ i ∈ s, (c i : ℝ) * ϱ i j) := by
  intro j
  choose! k hk using h
  refine ⟨∑ i ∈ s, c i * k i j, ?_⟩
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hk i hi j]
  ring

/-- Characters of a compatible charge with nonzero total charge integrate to zero (the constant
imaginary shift of the compact box). -/
theorem integral_character_clockLaw_eq_zero {n β : ℝ} (hn : 0 < n) (hβ : 0 ≤ β)
    (G : Multigraph V E) (τ : V → ℝ) (hτ : IsClockCompatible n τ) (hQ : ∑ j, τ j ≠ 0) :
    ∫ φ, gffCharacter τ φ ∂clockLaw β n G = 0 := by
  set t : ℝ := 1 / ∑ j, τ j
  have h := integral_clockLaw_characterTranslation hn hβ G τ (fun _ => t) hτ
  have hg : G.grad (fun _ : V => t) = 0 := by
    funext e; simp [Multigraph.grad]
  have hR : ∀ φ : V → ℝ,
      edgeRatio (clockEdgeWeight β n) (G.grad fun _ : V => t) (G.grad φ) = 1 := by
    intro φ
    rw [hg]
    exact edgeRatio_zero _ _ fun e => clockEdgeWeight_ofReal_ne_zero β n _
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
  have h3 : (1 - Complex.exp (-((1 : ℝ) : ℂ))) * ∫ φ, gffCharacter τ φ ∂clockLaw β n G = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd (sub_eq_zero.1 h4).symm hne
  · exact h4

/-! ### The translated product -/

/-- **The translation step on the compact clock law** (FS81 Lemma 4.3/(6.18) for the compact
box): for compatible real densities `ϱ_i` (no neutrality needed), factors `A_i + B_i cos θ_i`,
`θ_i = ⟨φ, ϱ_i⟩ + s_i`, and real waves with `⟨a_i, ϱ_{i'}⟩ = 0` for `i ≠ i'` and pairwise disjoint
gradient supports, `∫ ∏ (A_i + B_i cos θ_i) dμ = ∫ ∏ (A_i + B_i e^{-E_c(a_i, ϱ_i)} F_i) dμ`
with the clock cost and `F_i = localFactor w c (∇a_i) (∇φ) θ_i`. No strip condition is needed. -/
theorem integral_prod_add_mul_cos_clockLaw {n β : ℝ} (hn : 0 < n) (hβ : 0 ≤ β)
    (G : Multigraph V E) {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (hcomp : ∀ i, IsClockCompatible n (ϱ i)) (A B s : ι → ℝ) (a : ι → V → ℝ)
    (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, G.grad (a i) e = 0 ∨ G.grad (a i') e = 0) :
    ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) ∂clockLaw β n G =
      ∫ φ, ∏ i, ((A i : ℂ) +
        ((B i * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear G) (a i) (ϱ i)) :
          ℝ) : ℂ) *
        localFactor (clockEdgeWeight β n) (clockShiftCost β n) (gradLinear G (a i))
          (gradLinear G φ) (∑ j, φ j * ϱ i j + s i)) ∂clockLaw β n G := by
  classical
  have hμ := isProbabilityMeasure_clockLaw G hβ hn
  set w := clockEdgeWeight β n
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
  have hwx : ∀ φ : V → ℝ, ∀ e, w ((D φ + 0) e) ≠ 0 := fun φ e => clockEdgeWeight_ne_zero β n _
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
        (gffCharacter (τ m) φ * edgeRatio w (D (an m)) (D φ + 0))) (clockLaw β n G) := by
    intro m _
    refine Integrable.const_mul ?_ _
    have := integrable_character_mul_edgeRatio_clock (n := n) hβ (clockLaw β n G) G (τ m)
      (D (an m))
    simpa [hDg] using this
  have htrans : ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ)
      ∂clockLaw β n G =
      ∫ φ, ∏ i, ((A i : ℂ) + ((B i * Real.exp (-∑ j, a i j * ϱ i j) : ℝ) : ℂ) *
        translatedCos w (D (a i)) (D φ + 0) (∑ j, φ j * ϱ i j + s i)) ∂clockLaw β n G := by
    simp_rw [hleft, hright]
    rw [integral_finsetSum P fun m _ =>
        (Reduction.integrable_gffCharacter _ (τ m)).const_mul _,
      integral_finsetSum P hint]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, integral_const_mul,
      integral_clockLaw_characterTranslation hn hβ G (τ m) (an m) (hτc m), mul_assoc]
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

end FroehlichSpencer.BKT.Clock.Compact

end
