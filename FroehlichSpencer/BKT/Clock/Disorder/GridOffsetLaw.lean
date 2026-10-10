/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.OffsetTranslation
public import FroehlichSpencer.BKT.Clock.Disorder.CompactShift
public import FroehlichSpencer.BKT.Clock.Disorder.CompactLowerBranch
public import FroehlichSpencer.BKT.Generic.Moment.LayerActivity
import Mathlib.Tactic

/-!
# The offset compact clock measure and its renormalization identity

On a finite vertex set `V`, `gridBoxMeasure n V` is the product Lebesgue measure on the compact
box `(−πn, πn]^V`. `gridOffsetMeasure β n G θ` has density
`∏_e exp(β cos((∇φ_e + θ_e)/n))` (`compactClockBondProduct`) with respect to it. This is the
compact clock weight with a fixed real bond offset `θ`, the measure on the shifted side of the
disorder estimate.

* `integral_gridOffsetMeasure`: integrals are density integrals over the box.
* `gridOffset_characterTranslation`: the compact character translation for a clock-compatible
  charge and any real wave, with the offset in the edge ratio. It is
  `integral_clockOffsetCharacterTranslation` transported from `Fin |V|`.
* The translated product, the charged vanishing, one ensemble, and **the T1.6-NG identity**
  `gridOffset_renormalization_of_chargeLayer`. These are the compact clock proofs of
  `Clock/Compact/{Translation,Assembly}.lean`, with `clockLaw` replaced by the offset measure. The
  waves and activities are those of the unshifted identity, for every `θ`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open MeasureTheory Complex
open scoped NNReal ENNReal
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Reduction (gffCharacter norm_gffCharacter signSet mem_signSet)

variable {V : Type} [Fintype V] {E : Type} [Fintype E]

/-! ### The box measure and the offset measure -/

/-- The product Lebesgue measure on the compact box `(−πn, πn]^V`. -/
def gridBoxMeasure (n : ℝ) (V : Type) [Fintype V] : Measure (V → ℝ) :=
  (clockAngleBaseMeasure n : Measure (Fin (Fintype.card V) → ℝ)).map (pullField V)

instance isFiniteMeasure_gridBoxMeasure (n : ℝ) : IsFiniteMeasure (gridBoxMeasure n V) := by
  unfold gridBoxMeasure
  have := isFiniteMeasure_clockAngleBaseMeasure (d := Fintype.card V) (n := n)
  infer_instance

theorem integral_gridBoxMeasure {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℝ)
    (f : (V → ℝ) → F) :
    ∫ φ, f φ ∂gridBoxMeasure n V =
      ∫ φ, f (pullField V φ) ∂(clockAngleBaseMeasure n : Measure (Fin (Fintype.card V) → ℝ)) :=
  measurableEmbedding_pullField.integral_map _

/-- The box measure is invariant under field inversion. -/
theorem measurePreserving_neg_gridBoxMeasure (n : ℝ) :
    MeasurePreserving (fun φ : V → ℝ => -φ) (gridBoxMeasure n V) (gridBoxMeasure n V) := by
  have hpull : (fun φ : V → ℝ => -φ) ∘ pullField V = pullField V ∘ fun φ => -φ := by
    funext φ v
    rfl
  have hneg := measurePreserving_neg_clockAngleBaseMeasure (d := Fintype.card V) n
  have hmeas : Measurable (pullField V) := measurableEmbedding_pullField.measurable
  refine ⟨measurable_neg, ?_⟩
  unfold gridBoxMeasure
  rw [Measure.map_map measurable_neg hmeas, hpull, ← Measure.map_map hmeas measurable_neg,
    hneg.map_eq]

omit [Fintype V] in
theorem compactClockBondProduct_pos (G : Multigraph V E) (β n : ℝ) (φ : V → ℝ) (θ : E → ℝ) :
    0 < compactClockBondProduct G β n φ θ :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

omit [Fintype V] in
theorem continuous_compactClockBondProduct (G : Multigraph V E) (β n : ℝ) (θ : E → ℝ) :
    Continuous fun φ : V → ℝ => compactClockBondProduct G β n φ θ := by
  unfold compactClockBondProduct Multigraph.grad
  fun_prop

omit [Fintype V] in
theorem compactClockBondProduct_le (G : Multigraph V E) {β : ℝ} (hβ : 0 ≤ β) (n : ℝ)
    (φ : V → ℝ) (θ : E → ℝ) :
    compactClockBondProduct G β n φ θ ≤ Real.exp (β * Fintype.card E) := by
  unfold compactClockBondProduct
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  calc ∑ e, β * Real.cos ((G.grad φ e + θ e) / n) ≤ ∑ _e : E, β :=
        Finset.sum_le_sum fun e _ => by
          have := Real.cos_le_one ((G.grad φ e + θ e) / n)
          nlinarith
    _ = β * Fintype.card E := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The density of the offset measure. -/
def gridOffsetDensity (β n : ℝ) (G : Multigraph V E) (θ : E → ℝ) (φ : V → ℝ) : ℝ≥0 :=
  (compactClockBondProduct G β n φ θ).toNNReal

/-- **The compact clock measure with a real bond offset** `θ`. -/
def gridOffsetMeasure (β n : ℝ) (G : Multigraph V E) (θ : E → ℝ) : Measure (V → ℝ) :=
  (gridBoxMeasure n V).withDensity fun φ => (gridOffsetDensity β n G θ φ : ℝ≥0∞)

theorem measurable_gridOffsetDensity (β n : ℝ) (G : Multigraph V E) (θ : E → ℝ) :
    Measurable (gridOffsetDensity β n G θ) :=
  (continuous_compactClockBondProduct G β n θ).measurable.real_toNNReal

theorem integral_gridOffsetMeasure {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β n : ℝ) (G : Multigraph V E) (θ : E → ℝ) (f : (V → ℝ) → F) :
    ∫ φ, f φ ∂gridOffsetMeasure β n G θ =
      ∫ φ, compactClockBondProduct G β n φ θ • f φ ∂gridBoxMeasure n V := by
  unfold gridOffsetMeasure
  rw [integral_withDensity_eq_integral_smul (measurable_gridOffsetDensity β n G θ)]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  simp only [gridOffsetDensity, NNReal.smul_def, Real.coe_toNNReal _
    (compactClockBondProduct_pos G β n φ θ).le]

theorem isFiniteMeasure_gridOffsetMeasure {β : ℝ} (hβ : 0 ≤ β) (n : ℝ) (G : Multigraph V E)
    (θ : E → ℝ) : IsFiniteMeasure (gridOffsetMeasure β n G θ) := by
  unfold gridOffsetMeasure
  refine isFiniteMeasure_withDensity (ne_of_lt ?_)
  calc ∫⁻ φ, (gridOffsetDensity β n G θ φ : ℝ≥0∞) ∂gridBoxMeasure n V
      ≤ ∫⁻ _φ, ENNReal.ofReal (Real.exp (β * Fintype.card E)) ∂gridBoxMeasure n V := by
        refine lintegral_mono fun φ => ?_
        rw [gridOffsetDensity, ENNReal.ofReal]
        exact ENNReal.coe_le_coe.mpr (Real.toNNReal_le_toNNReal
          (compactClockBondProduct_le G hβ n φ θ))
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-! ### The offset character translation -/

/-- **Compact character translation under the offset measure**: for a clock-compatible charge `τ`
and every real wave `a`, `∫ χ_τ dμ_θ = e^{−⟨a, τ⟩} ∫ χ_τ R_{∇a}(∇φ + θ) dμ_θ`. -/
theorem gridOffset_characterTranslation {n β : ℝ} (hn : 0 < n) (hβ : 0 ≤ β)
    (G : Multigraph V E) (θ : E → ℝ) (τ a : V → ℝ) (hτ : IsClockCompatible n τ) :
    ∫ φ, gffCharacter τ φ ∂gridOffsetMeasure β n G θ =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, gffCharacter τ φ * edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ + θ)
          ∂gridOffsetMeasure β n G θ := by
  set e := siteEquiv V
  set G' := relabelGraph G e
  set τ' : Fin (Fintype.card V) → ℝ := fun j => τ (e.symm j)
  set a' : Fin (Fintype.card V) → ℝ := fun j => a (e.symm j)
  have hτ' : ClockCompatibleCharge n τ' := fun j => hτ (e.symm j)
  have hga : G'.grad a' = G.grad a := by
    funext x
    simp only [Multigraph.grad, G', relabelGraph, a', Equiv.symm_apply_apply]
  have hsum : ∑ j, a' j * τ' j = ∑ j, a j * τ j :=
    e.symm.sum_comp fun j => a j * τ j
  have hdens : ∀ φ : Fin (Fintype.card V) → ℝ,
      compactClockBondProduct G β n (pullField V φ) θ = clockOffsetDensity β n G' θ φ := by
    intro φ
    rfl
  rw [integral_gridOffsetMeasure, integral_gridOffsetMeasure, integral_gridBoxMeasure,
    integral_gridBoxMeasure]
  simp_rw [hdens, gffCharacter_pullField, grad_pullField, Complex.real_smul]
  have key := integral_clockOffsetCharacterTranslation hn hβ G' τ' a' hτ' θ
  rw [hga, hsum] at key
  rw [key]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  ring

theorem integrable_character_mul_edgeRatio_clock_offset {β n : ℝ} (hβ : 0 ≤ β)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] (G : Multigraph V E) (θ : E → ℝ) (τ : V → ℝ)
    (b : E → ℝ) :
    Integrable (fun φ => gffCharacter τ φ * edgeRatio (clockEdgeWeight β n) b (G.grad φ + θ)) μ := by
  refine Integrable.of_bound ?_ (Real.exp (∑ e, clockShiftCost β n (b e)))
    (ae_of_all _ fun φ => ?_)
  · refine ((Reduction.continuous_gffCharacter τ).mul
      ((continuous_edgeRatio_clock β n b).comp ?_)).aestronglyMeasurable
    refine continuous_pi fun e => ?_
    simp only [Pi.add_apply, Multigraph.grad]
    fun_prop
  · rw [norm_mul, Reduction.norm_gffCharacter, one_mul]
    exact norm_edgeRatio_clock_le hβ n b _

/-! ### The compact clock proofs under the offset measure -/

/-- Characters of a compatible charge with nonzero total charge integrate to zero (the constant
imaginary shift of the compact box). -/
theorem integral_character_gridOffset_eq_zero {n β : ℝ} (hn : 0 < n) (hβ : 0 ≤ β)
    (G : Multigraph V E) (θ : E → ℝ) (τ : V → ℝ) (hτ : IsClockCompatible n τ) (hQ : ∑ j, τ j ≠ 0) :
    ∫ φ, gffCharacter τ φ ∂gridOffsetMeasure β n G θ = 0 := by
  set t : ℝ := 1 / ∑ j, τ j
  have h := gridOffset_characterTranslation hn hβ G θ τ (fun _ => t) hτ
  have hg : G.grad (fun _ : V => t) = 0 := by
    funext e; simp [Multigraph.grad]
  have hR : ∀ φ : V → ℝ,
      edgeRatio (clockEdgeWeight β n) (G.grad fun _ : V => t) (G.grad φ + θ) = 1 := by
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
  have h3 : (1 - Complex.exp (-((1 : ℝ) : ℂ))) * ∫ φ, gffCharacter τ φ ∂gridOffsetMeasure β n G θ = 0 := by
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
theorem integral_prod_add_mul_cos_gridOffset {n β : ℝ} (hn : 0 < n) (hβ : 0 ≤ β)
    (G : Multigraph V E) (θ : E → ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (hcomp : ∀ i, IsClockCompatible n (ϱ i)) (A B s : ι → ℝ) (a : ι → V → ℝ)
    (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, G.grad (a i) e = 0 ∨ G.grad (a i') e = 0) :
    ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) ∂gridOffsetMeasure β n G θ =
      ∫ φ, ∏ i, ((A i : ℂ) +
        ((B i * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear G) (a i) (ϱ i)) :
          ℝ) : ℂ) *
        localFactor (clockEdgeWeight β n) (clockShiftCost β n) (gradLinear G (a i))
          (gradLinear G φ + θ) (∑ j, φ j * ϱ i j + s i)) ∂gridOffsetMeasure β n G θ := by
  classical
  have hμ := isFiniteMeasure_gridOffsetMeasure hβ n G θ
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
  have hwx : ∀ φ : V → ℝ, ∀ e, w ((D φ + θ) e) ≠ 0 := fun φ e => clockEdgeWeight_ne_zero β n _
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
          translatedCos w (D (a i)) (D φ + θ) (∑ j, φ j * ϱ i j + s i)) =
        ∑ m ∈ P, coef m * Complex.exp (-((∑ j, an m j * τ m j : ℝ) : ℂ)) *
          (gffCharacter (τ m) φ * edgeRatio w (D (an m)) (D φ + θ)) := by
    intro φ
    rw [prod_translated_eq_sum A B (fun i => ∑ j, φ j * ϱ i j + s i) ε w (fun i => D (a i))
      (D φ + θ) (hwx φ)]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hratio : edgeRatio w (D (an m)) (D φ + θ) =
        ∏ i, edgeRatio w ((m i : ℝ) • D (a i)) (D φ + θ) := by
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
        (gffCharacter (τ m) φ * edgeRatio w (D (an m)) (D φ + θ))) (gridOffsetMeasure β n G θ) := by
    intro m _
    refine Integrable.const_mul ?_ _
    have := integrable_character_mul_edgeRatio_clock_offset (n := n) hβ (gridOffsetMeasure β n G θ) G θ (τ m)
      (D (an m))
    simpa [hDg] using this
  have htrans : ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ)
      ∂gridOffsetMeasure β n G θ =
      ∫ φ, ∏ i, ((A i : ℂ) + ((B i * Real.exp (-∑ j, a i j * ϱ i j) : ℝ) : ℂ) *
        translatedCos w (D (a i)) (D φ + θ) (∑ j, φ j * ϱ i j + s i)) ∂gridOffsetMeasure β n G θ := by
    simp_rw [hleft, hright]
    rw [integral_finsetSum P fun m _ =>
        (Reduction.integrable_gffCharacter _ (τ m)).const_mul _,
      integral_finsetSum P hint]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, integral_const_mul,
      gridOffset_characterTranslation hn hβ G θ (τ m) (an m) (hτc m), mul_assoc]
    congr 2
  rw [htrans]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  have hc : ∀ u, clockShiftCost β n (-u) = clockShiftCost β n u := fun u => by
    simp [clockShiftCost, neg_div, Real.cosh_neg]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, mul_assoc, mul_assoc,
    exp_mul_translatedCos w (c := clockShiftCost β n) hc D (a i) (ϱ i)]


/-! ### Charged characters against renormalizable products -/

/-- A compatible character of nonzero total charge, times a product of factors
`A_i + B_i cos(⟨φ, ϱ_i⟩ + s_i)` with compatible neutral densities, integrates to zero under the
clock law (each term of the product's character expansion has the same nonzero charge). -/
theorem integral_character_mul_prod_gridOffset_eq_zero {n β : ℝ} (hn : 0 < n) (hβ : 0 ≤ β)
    (G : Multigraph V E) (θ : E → ℝ) (τ : V → ℝ) (hτc : IsClockCompatible n τ) (hτ : ∑ j, τ j ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (hc : ∀ i, IsClockCompatible n (ϱ i)) (hneu : ∀ i, ∑ j, ϱ i j = 0) (A B s : ι → ℝ) :
    ∫ φ, gffCharacter τ φ * ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ)
      ∂gridOffsetMeasure β n G θ = 0 := by
  classical
  have hμ := isFiniteMeasure_gridOffsetMeasure hβ n G θ
  set P := Fintype.piFinset fun _ : ι => signSet
  set coef : (ι → ℤ) → ℂ := fun m =>
    ∏ i, (mixedCoeff (A i) (B i) (m i) * Complex.exp (I * ((m i : ℂ) * s i))) with hcoef
  set τm : (ι → ℤ) → V → ℝ := fun m j => τ j + ∑ i, (m i : ℝ) * ϱ i j with hτm
  have hleft : ∀ φ : V → ℝ,
      ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) =
        ∑ m ∈ P, coef m * gffCharacter (fun j => ∑ i, (m i : ℝ) * ϱ i j) φ := by
    intro φ
    rw [prod_add_mul_cos_eq_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.prod_mul_distrib, prod_exp_eq_character m ϱ s φ, hcoef, ← mul_assoc,
      ← Finset.prod_mul_distrib]
  have hpt : ∀ φ : V → ℝ, gffCharacter τ φ *
      ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) =
        ∑ m ∈ P, coef m * gffCharacter (τm m) φ := by
    intro φ
    rw [hleft, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show gffCharacter (τm m) φ = gffCharacter τ φ *
        gffCharacter (fun j => ∑ i, (m i : ℝ) * ϱ i j) φ from (Generic.gffCharacter_mul _ _ _).symm]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum P fun m _ => (Reduction.integrable_gffCharacter _ (τm m)).const_mul _]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [integral_const_mul]
  have hcomp : IsClockCompatible n (τm m) := by
    intro j
    obtain ⟨k, hk⟩ := hτc j
    obtain ⟨k', hk'⟩ := IsClockCompatible.sum_smul Finset.univ m ϱ (fun i _ => hc i) j
    exact ⟨k + k', by simp only [hτm]; push_cast; rw [← hk, ← hk']; ring⟩
  have hQ : ∑ j, τm m j ≠ 0 := by
    simp only [hτm, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hneu, mul_zero, Finset.sum_const_zero, add_zero]
    exact hτ
  rw [integral_character_gridOffset_eq_zero hn hβ G θ _ hcomp hQ, mul_zero]

/-! ### One ensemble -/

/-- **Renormalization of one ensemble under the clock law** (KP §2.3.3; FS81 (6.18), (7.9)–(7.14)
on the compact box). The non-neutral density drops out
(`integral_character_mul_prod_gridOffset_eq_zero`)
and every neutral density is translated by its own spin wave. -/
theorem gridOffset_integral_ensemble_eq [DecidableEq V] {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β)
    (G : Multigraph V E) (θ : E → ℝ) (N : Finset (V → ℤ)) (hNa : AtMostOneNonNeutral N) (K : (V → ℤ) → ℝ)
    (σ : V → ℝ) (centerOf : (V → ℤ) → V) (a : (V → ℤ) → V → ℝ)
    (hconst : ∀ ϱ ∈ neutralPart N, ∀ ϱ' ∈ G.comparableDensities (neutralPart N) ϱ,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ' (centerOf ϱ'), a ϱ j = c)
    (hsupp : ∀ ϱ ∈ neutralPart N, Function.support (a ϱ) ⊆ G.densityDomain ϱ (centerOf ϱ))
    (horth : ∀ ϱ ∈ neutralPart N, ∀ ϱ' ∈ neutralPart N, ϱ ≠ ϱ' →
      ∑ j, a ϱ j * (ϱ' j : ℝ) = 0) :
    ∫ φ, ((∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)
        ∂gridOffsetMeasure β n G θ =
      ∫ φ, ∏ ϱ ∈ neutralPart N, ((1 : ℂ) +
        ((K ϱ * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear G) (a ϱ)
          fun j => (ϱ j : ℝ)) : ℝ) : ℂ) *
          localFactor (clockEdgeWeight β n) (clockShiftCost β n) (gradLinear G (a ϱ))
            (gradLinear G φ + θ) (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂gridOffsetMeasure β n G θ := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set P := neutralPart N with hPdef
  have hPneutral : ∀ ϱ ∈ P, ∑ j, ϱ j = 0 := fun ϱ hϱ => (mem_neutralPart.mp hϱ).2
  have hfin : IsFiniteMeasure (gridOffsetMeasure β n G θ) := isFiniteMeasure_gridOffsetMeasure hβ n G θ
  set Rest : (V → ℝ) → ℝ := fun φ =>
    ∏ ϱ ∈ P, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) with hRest
  have hθ : ∀ (φ : V → ℝ) (ϱ : V → ℤ), ∑ j, (φ j + σ j) * (ϱ j : ℝ) =
      ∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ) := by
    intro φ ϱ
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the rest as a product over the subtype
  have hRestP : ∀ φ : V → ℝ, ((Rest φ : ℝ) : ℂ) =
      ((∏ ϱ : P, (1 + K ϱ * Real.cos (∑ j, φ j * ((ϱ : V → ℤ) j : ℝ) +
        ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ))) : ℝ) : ℂ) := by
    intro φ
    simp only [hRest]
    rw [← Finset.prod_coe_sort P]
    congr 2
    funext ϱ
    rw [hθ]
  -- Step 1: the non-neutral density drops out
  have hdrop : ∫ φ, ((∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)
      ∂gridOffsetMeasure β n G θ = ∫ φ, ((Rest φ : ℝ) : ℂ) ∂gridOffsetMeasure β n G θ := by
    by_cases hch : ∃ ϱc ∈ N, ∑ j, ϱc j ≠ 0
    · obtain ⟨ϱc, hϱc, hne⟩ := hch
      have hcP : ϱc ∉ P := fun h => hne (hPneutral ϱc h)
      have hN : N = insert ϱc P := by
        ext ϱ
        simp only [Finset.mem_insert, hPdef, mem_neutralPart]
        constructor
        · intro hϱ
          by_cases h0 : ∑ j, ϱ j = 0
          · exact Or.inr ⟨hϱ, h0⟩
          · exact Or.inl (hNa ϱ hϱ ϱc hϱc h0 hne)
        · rintro (rfl | ⟨hϱ, _⟩)
          · exact hϱc
          · exact hϱ
      have hpt : ∀ φ : V → ℝ,
          ((∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ) =
            ((Rest φ : ℝ) : ℂ) + ((K ϱc / 2 : ℝ) : ℂ) *
              (Complex.exp (I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ)) *
                  (gffCharacter (fun j => (ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ)) +
                Complex.exp (-(I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ))) *
                  (gffCharacter (fun j => -(ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ))) := by
        intro φ
        rw [hN, Finset.prod_insert hcP]
        change (((1 + K ϱc * Real.cos (∑ j, (φ j + σ j) * (ϱc j : ℝ))) * Rest φ : ℝ) : ℂ) = _
        generalize Rest φ = R
        rw [hθ]
        have hc1 : gffCharacter (fun j => (ϱc j : ℝ)) φ =
            Complex.exp (I * ((∑ j, φ j * (ϱc j : ℝ) : ℝ) : ℂ)) := by
          unfold gffCharacter; congr 1; push_cast; ring
        have hc2 : gffCharacter (fun j => -(ϱc j : ℝ)) φ =
            Complex.exp (-(I * ((∑ j, φ j * (ϱc j : ℝ) : ℝ) : ℂ))) := by
          unfold gffCharacter; congr 1
          push_cast
          rw [← mul_neg, ← Finset.sum_neg_distrib]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hc1, hc2]
        generalize (∑ j, φ j * (ϱc j : ℝ)) = θ₀
        generalize (∑ j, σ j * (ϱc j : ℝ)) = s
        have h1 : Complex.exp (((θ₀ : ℂ) + (s : ℂ)) * I) =
            Complex.exp (I * (s : ℂ)) * Complex.exp (I * (θ₀ : ℂ)) := by
          rw [← Complex.exp_add]; congr 1; ring
        have h2 : Complex.exp (-((θ₀ : ℂ) + (s : ℂ)) * I) =
            Complex.exp (-(I * (s : ℂ))) * Complex.exp (-(I * (θ₀ : ℂ))) := by
          rw [← Complex.exp_add]; congr 1; ring
        push_cast
        rw [Complex.cos, h1, h2]
        ring
      simp_rw [hpt]
      have hRest_meas : Measurable Rest := by
        refine (continuous_finsetProd _ fun ϱ _ => ?_).measurable
        fun_prop
      have hint₀ : Integrable (fun φ => ((Rest φ : ℝ) : ℂ)) (gridOffsetMeasure β n G θ) :=
        Integrable.of_bound (Complex.measurable_ofReal.comp hRest_meas).aestronglyMeasurable
          _ (Filter.Eventually.of_forall fun φ => norm_prod_one_add_mul_cos_le P K _)
      have hintχ : ∀ τ : V → ℝ, Integrable
          (fun φ => gffCharacter τ φ * ((Rest φ : ℝ) : ℂ)) (gridOffsetMeasure β n G θ) :=
        fun τ => Integrable.of_bound
          (((Reduction.continuous_gffCharacter _).aestronglyMeasurable).mul
            (Complex.measurable_ofReal.comp hRest_meas).aestronglyMeasurable)
          (∏ ϱ ∈ P, (1 + |K ϱ|)) (Filter.Eventually.of_forall fun φ => by
            rw [norm_mul, Reduction.norm_gffCharacter, one_mul]
            exact norm_prod_one_add_mul_cos_le P K _)
      have hzero : ∀ τ : V → ℝ, IsClockCompatible (n : ℝ) τ → ∑ j, τ j ≠ 0 →
          ∫ φ, gffCharacter τ φ * ((Rest φ : ℝ) : ℂ) ∂gridOffsetMeasure β n G θ = 0 := by
        intro τ hτc hτ
        simp_rw [hRestP]
        exact integral_character_mul_prod_gridOffset_eq_zero hn' hβ G θ τ hτc hτ
          (fun (ϱ : P) j => ((ϱ : V → ℤ) j : ℝ))
          (fun ϱ => isClockCompatible_intCast n _)
          (fun ϱ => by exact_mod_cast hPneutral ϱ ϱ.2) (fun _ => 1) (fun ϱ => K ϱ)
          (fun ϱ => ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ))
      have hz₁ := hzero (fun j => (ϱc j : ℝ)) (isClockCompatible_intCast n ϱc)
        (by exact_mod_cast hne)
      have hz₂ := hzero (fun j => -(ϱc j : ℝ))
        (by
          intro j
          obtain ⟨k, hk⟩ := isClockCompatible_intCast n ϱc j
          exact ⟨-k, by push_cast; rw [← hk]; ring⟩)
        (by
          rw [Finset.sum_neg_distrib, neg_ne_zero]
          exact_mod_cast hne)
      have hA := (hintχ fun j => (ϱc j : ℝ)).const_mul
        (Complex.exp (I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ)))
      have hB := (hintχ fun j => -(ϱc j : ℝ)).const_mul
        (Complex.exp (-(I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ))))
      have hAB : Integrable (fun φ => ((K ϱc / 2 : ℝ) : ℂ) *
          (Complex.exp (I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ)) *
              (gffCharacter (fun j => (ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ)) +
            Complex.exp (-(I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ))) *
              (gffCharacter (fun j => -(ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ))))
          (gridOffsetMeasure β n G θ) := (hA.add hB).const_mul _
      rw [integral_add hint₀ hAB, integral_const_mul, integral_add hA hB,
        integral_const_mul, integral_const_mul, hz₁, hz₂]
      simp
    · push Not at hch
      have hN : N = P := by
        ext ϱ
        simp only [hPdef, mem_neutralPart]
        exact ⟨fun h => ⟨h, hch ϱ h⟩, fun h => h.1⟩
      rw [hN]
  rw [hdrop]
  -- Step 2: translate the neutral densities
  have hdisj := grad_disjoint_of_spinWave_clauses G P centerOf a hconst hsupp
  have key := integral_prod_add_mul_cos_gridOffset hn' hβ G θ (ι := P)
    (fun ϱ j => ((ϱ : V → ℤ) j : ℝ)) (fun ϱ => isClockCompatible_intCast n _)
    (fun _ => 1) (fun ϱ => K ϱ) (fun ϱ => ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ)) (fun ϱ => a ϱ)
    (fun ϱ ϱ' hne => horth ϱ ϱ.2 ϱ' ϱ'.2 fun h => hne (Subtype.ext h))
    (fun ϱ ϱ' hne e => hdisj ϱ ϱ.2 ϱ' ϱ'.2 (fun h => hne (Subtype.ext h)) e)
  simp_rw [hRestP]
  rw [key]
  congr 1
  funext φ
  rw [← Finset.prod_coe_sort P]
  rfl

/-! ### The T1.6-NG assembly on the compact clock law -/


section Layer

variable [DecidableEq V] {G : Multigraph V E}
  {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V} {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- **The T1.6-NG identity under the offset clock measure**: for every real site shift `σ`,
`∫ ∏_j λ_j(φ_j + σ_j) dμ_θ = ∑_i c_i ∫ ∏_{ϱ ∈ ℛ_i} [1 + z_i(ϱ) F_{i,ϱ}(∇φ + θ, ⟨φ + σ, ϱ⟩)] dμ_θ`,
with the spin waves `layerSpinWave` and activities `layerActivity` of the clock cost. These do not
depend on `θ` or `σ`. -/
theorem gridOffset_renormalization_of_chargeLayer {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β)
    (θ : E → ℝ) (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hroot : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i))
    (κ amp : ℝ) (k₀ : ℕ) (σ : V → ℝ) :
    ∫ φ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) ∂gridOffsetMeasure β n G θ =
      ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.R i, ((1 : ℂ) +
        (layerActivity CL (clockShiftCost β n) κ amp k₀ i ϱ : ℂ) *
          localFactor (clockEdgeWeight β n) (clockShiftCost β n)
            (gradLinear G (layerSpinWave CL κ amp k₀ i ϱ))
            (gradLinear G φ + θ) (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ)))
        ∂gridOffsetMeasure β n G θ := by
  classical
  have hfin : IsFiniteMeasure (gridOffsetMeasure β n G θ) :=
    isFiniteMeasure_gridOffsetMeasure hβ n G θ
  have hpt : ∀ φ : V → ℝ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) =
      ∑ i, (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
        (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ) := by
    intro φ
    rw [CL.expand fun j => φ j + σ j]
    push_cast
    rfl
  have hint : ∀ i, Integrable (fun φ : V → ℝ => (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
      (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ))
      (gridOffsetMeasure β n G θ) := by
    intro i
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound ?_ (∏ ϱ ∈ CL.N i, (1 + |CL.K i ϱ|))
      (Filter.Eventually.of_forall fun φ => norm_prod_one_add_mul_cos_le _ _ _)
    refine (Complex.continuous_ofReal.comp
      (continuous_finsetProd _ fun ϱ _ => ?_)).aestronglyMeasurable
    fun_prop
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  congr 1
  obtain ⟨hR, hNa⟩ := hroot i
  obtain ⟨hconst, hsupp, horth⟩ := layerSpinWave_clauses CL κ amp k₀ i
  rw [hR] at hconst hsupp horth
  have key := gridOffset_integral_ensemble_eq hn hβ G θ (CL.N i) hNa (CL.K i) σ centerOf
    (layerSpinWave CL κ amp k₀ i) hconst hsupp horth
  rw [key, hR]
  rfl

end Layer

end FroehlichSpencer.BKT.Clock.Disorder

end
