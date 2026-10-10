/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.Gas
public import FroehlichSpencer.BKT.Gaussian.WeightedGFF
public import FroehlichSpencer.BKT.Surface.LaplacianPseudoinverse
import FroehlichSpencer.BKT.Gaussian.ComplexCharacteristic
import FroehlichSpencer.BKT.Gaussian.EnsembleSelection
import FroehlichSpencer.BKT.Gaussian.WeightedShift
import Mathlib.Tactic

/-!
# The sine-Gordon representation of the finite Coulomb gas

* `integral_cos_charge_gffLaw`: for an integer charge `q` and a phase `s`,
  `∫ cos (⟨φ, q⟩ + s) dμ = 𝟙[∑ q = 0] e^{-⟨q, C q⟩ / (2β)} cos s`.

The vanishing for non-neutral
  `q` is the integration over the constant mode, which ranges over a full period: this is how
  the rooted GFF reproduces the neutrality of FS81's free boundary condition ((1.14)).
* `integral_exp_mul_cos_charge_gffLaw`: completing the square (FS81 (5.8)–(5.12), KP (3.1)).
* `integral_exp_mul_prod_sineGordonWeight` (**the representation identity**): for even charge
  weights `λ_j` (cut off at `|q| ≤ N`), a Laplacian pseudoinverse `T` (`C = -T`) and zero-sum `f`,
  `∫ e^{⟨φ,f⟩} ∏_j λ̂_j(φ_j) dμ_κ = e^{κ ⟨f, C f⟩ / 2} ∑_q w_κ(q) cos (κ ⟨q, C f⟩)`,
  where `w_κ(q) = 𝟙[∑ q = 0] ∏_j λ_j(q_j) e^{-κ E(q)}` is the gas weight (1.7).
* `weightedGFFNormalizer_sineGordon` (FS81 (1.15)): `∫ ∏_j λ̂_j(φ_j) dμ_κ = Z_Λ`.
* `weightedGFFExpectation_exp_sineGordon` (FS81 (1.16), (5.12)): the normalized generating
  functional of the field is `e^{κ ⟨f, C f⟩/2}` times the charge characteristic function
  `⟨cos (κ ⟨q, C f⟩)⟩_Λ` of the gas.

No positivity of the weights is assumed: the identities hold for signed `λ` as well
(FS81 p. 570 allows signed weights for weighted-field results).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

section Gaussian

variable {E : Type*} [Fintype E]

/-- FS81 (1.13)–(1.14) for the rooted GFF: the cosine of an integer charge integrates to
`e^{-⟨q, -Δ⁻¹ q⟩/(2β)} cos s` if the charge is neutral and to `0` otherwise (integration over
the constant mode, KP §2.3.1 Step 1). -/
theorem integral_cos_charge_gffLaw (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (β : ℝ) (hβ : 0 < β) (v : V) (q : V → ℤ) (s : ℝ) :
    ∫ φ, Real.cos (∑ j, φ j * (q j : ℝ) + s) ∂gffLaw G hG β hβ v =
      if ∑ j, q j = 0 then
        Real.exp (-(Multigraph.pairing (fun j => (q j : ℝ))
          (-G.greenOp hG (fun j => (q j : ℝ)))) / (2 * β)) * Real.cos s
      else 0 := by
  split_ifs with hq
  · have hτ : ∑ j, (q j : ℝ) = 0 := by exact_mod_cast hq
    have hchar := gff_characteristic_function G hG β hβ v (fun j => (q j : ℝ)) hτ
    rw [← gffLaw_eq_gffMeasure] at hchar
    have := isProbabilityMeasure_gffLaw G hG β hβ v
    have hint : Integrable (fun φ : V → ℝ => Complex.exp (Complex.I *
        ((Multigraph.pairing φ (fun j => (q j : ℝ)) : ℝ) : ℂ))) (gffLaw G hG β hβ v) := by
      refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) 1
        (ae_of_all _ fun φ => ?_)
      · unfold Multigraph.pairing
        fun_prop
      · rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
    have hpt : ∀ φ : V → ℝ, Real.cos (∑ j, φ j * (q j : ℝ) + s) =
        RCLike.re (Complex.exp (Complex.I * (s : ℂ)) * Complex.exp (Complex.I *
          ((Multigraph.pairing φ (fun j => (q j : ℝ)) : ℝ) : ℂ))) := by
      intro φ
      rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, mul_comm Complex.I,
        RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re]
      unfold Multigraph.pairing
      ring_nf
    simp_rw [hpt]
    rw [integral_re (hint.const_mul _), integral_const_mul, hchar]
    set Q := Multigraph.pairing (fun j => (q j : ℝ)) (-(G.greenOp hG) fun j => (q j : ℝ))
    have hcast : Complex.exp (-(Q : ℂ) / (2 * (β : ℂ))) = ((Real.exp (-Q / (2 * β)) : ℝ) : ℂ) := by
      push_cast
      ring_nf
    rw [hcast, RCLike.re_to_complex, Complex.re_mul_ofReal, mul_comm Complex.I,
      Complex.exp_ofReal_mul_I_re, mul_comm]
  · have h := gffLaw_integral_cos_charge_mul_eq_zero G hG β hβ v q hq s (fun _ => 1)
      (fun _ _ => rfl) measurable_const 1 (fun _ => by simp)
    simpa using h

/-- Completing the square (FS81 (5.8)–(5.12)) against one charge character. -/
theorem integral_exp_mul_cos_charge_gffLaw (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) (f : V → ℝ)
    (hf : ∑ j, f j = 0) (q : V → ℤ) :
    ∫ φ, Real.exp (∑ j, φ j * f j) * Real.cos (∑ j, φ j * (q j : ℝ)) ∂gffLaw G hG β hβ v =
      Real.exp (Multigraph.pairing f (-G.greenOp hG f) / (2 * β)) *
        if ∑ j, q j = 0 then
          Real.exp (-(Multigraph.pairing (fun j => (q j : ℝ))
            (-G.greenOp hG (fun j => (q j : ℝ)))) / (2 * β)) *
            Real.cos ((∑ j, (q j : ℝ) * -(G.greenOp hG f j)) / β)
        else 0 := by
  rw [integral_exp_pairing_mul_gffLaw G hG β hβ v f hf
    (fun φ => Real.cos (∑ j, φ j * (q j : ℝ))) (by fun_prop) 1
    (fun φ => Real.abs_cos_le_one _)]
  congr 1
  set σ := gffShift G hG β f v
  have hpt : ∀ φ : V → ℝ, Real.cos (∑ j, (φ + σ) j * (q j : ℝ)) =
      Real.cos (∑ j, φ j * (q j : ℝ) + ∑ j, σ j * (q j : ℝ)) := by
    intro φ
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  simp_rw [hpt]
  rw [integral_cos_charge_gffLaw]
  split_ifs with hq
  · congr 2
    have hqR : ∑ j, (q j : ℝ) = 0 := by exact_mod_cast hq
    simp only [σ, gffShift]
    have : ∑ j, (-(G.greenOp hG f j) / β + G.greenOp hG f v / β) * (q j : ℝ) =
        ∑ j, (q j : ℝ) * -(G.greenOp hG f j) / β +
          G.greenOp hG f v / β * ∑ j, (q j : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, hqR, mul_zero, add_zero, Finset.sum_div]
  · rfl

end Gaussian

/-! ### The sine-Gordon representation -/

section Representation

variable {E : Type*} [Fintype E]

/-- FS81 (1.15)–(1.16), (5.6)–(5.12) in finite volume: the sine-Gordon representation of the
neutral gas with the generating functional of the field. -/
theorem integral_exp_mul_prod_sineGordonWeight (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ) (hκ : 0 < κ) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T)
    (f : V → ℝ) (hf : ∑ j, f j = 0) :
    ∫ φ, Real.exp (∑ j, φ j * f j) * ∏ j, sineGordonWeightInternal N (lam j) (φ j)
        ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) v =
      Real.exp (κ * (∑ j, f j * -(T f j)) / 2) *
        ∑ q ∈ chargeConfigsInternal V N,
          gasWeightInternal T κ lam q * Real.cos (κ * ∑ j, (q j : ℝ) * -(T f j)) := by
  have hTg : T = G.greenOp hG := G.greenOp_unique hG T hT.1 hT.2
  subst hTg
  have hβ : 0 < κ⁻¹ := inv_pos.2 hκ
  have := isProbabilityMeasure_gffLaw G hG κ⁻¹ hβ v
  simp_rw [prod_sineGordonWeight_eq_sum N lam hlam, Finset.mul_sum]
  have hexp := integrable_exp_pairing_gffLaw G hG κ⁻¹ hβ v f hf
  rw [integral_finsetSum _ fun q _ => ?_]
  swap
  · have hc : Continuous fun φ : V → ℝ =>
        (∏ j, lam j (q j)) * Real.cos (∑ j, φ j * (q j : ℝ)) := by fun_prop
    refine (hexp.bdd_mul (c := |∏ j, lam j (q j)|)
      hc.aestronglyMeasurable (ae_of_all _ fun φ => ?_)).congr
      (ae_of_all _ fun φ => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · simp only
      ring
  refine Finset.sum_congr rfl fun q _ => ?_
  have hrw : ∀ φ : V → ℝ, Real.exp (∑ j, φ j * f j) *
      ((∏ j, lam j (q j)) * Real.cos (∑ j, φ j * (q j : ℝ))) =
      (∏ j, lam j (q j)) * (Real.exp (∑ j, φ j * f j) * Real.cos (∑ j, φ j * (q j : ℝ))) := by
    intro φ; ring
  simp_rw [hrw]
  rw [integral_const_mul, integral_exp_mul_cos_charge_gffLaw G hG κ⁻¹ hβ v f hf q]
  unfold gasWeightInternal chargeEnergyInternal
  have e1 : ∀ a : ℝ, a / (2 * κ⁻¹) = κ * a / 2 := fun a => by field_simp
  have e2 : ∀ a : ℝ, a / κ⁻¹ = κ * a := fun a => by field_simp
  split_ifs with hq
  · simp only [e1, e2, Multigraph.pairing, ← Finset.mul_sum, Pi.neg_apply]
    ring_nf
  · simp

/-- FS81 (1.15): `Z_Λ = ∫ ∏_j λ̂_j(φ_j) dμ_κ`. -/
theorem weightedGFFNormalizer_sineGordon (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ) (hκ : 0 < κ) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T) :
    weightedGFFNormalizer G hG κ⁻¹ (inv_pos.2 hκ) v
        (fun j => sineGordonWeightInternal N (lam j)) =
      gasPartitionInternal N T κ lam := by
  have h := integral_exp_mul_prod_sineGordonWeight G hG κ hκ v N lam hlam T hT 0
    (by simp)
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Real.exp_zero, one_mul,
    map_zero, neg_zero, zero_div, Real.cos_zero, mul_one] at h
  exact h

/-- FS81 (1.16), (5.6), (5.12): the normalized generating functional of the sine-Gordon field
is `e^{κ ⟨f, C f⟩ / 2}` times the charge characteristic function at `κ C f`. -/
theorem weightedGFFExpectation_exp_sineGordon (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) (κ : ℝ) (hκ : 0 < κ) (v : V) (N : ℕ)
    (lam : V → ℤ → ℝ) (hlam : ∀ j n, lam j (-n) = lam j n)
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (hT : G.IsLaplacianPseudoinverse T)
    (f : V → ℝ) (hf : ∑ j, f j = 0) :
    weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) v
        (fun j => sineGordonWeightInternal N (lam j)) (fun φ => Real.exp (∑ j, φ j * f j)) =
      Real.exp (κ * (∑ j, f j * -(T f j)) / 2) *
        gasExpectationInternal N T κ lam
          (fun q => Real.cos (κ * ∑ j, (q j : ℝ) * -(T f j))) := by
  rw [weightedGFFExpectation, weightedGFFNormalizer_sineGordon G hG κ hκ v N lam hlam T hT,
    integral_exp_mul_prod_sineGordonWeight G hG κ hκ v N lam hlam T hT f hf,
    gasExpectationInternal, mul_div_assoc]

end Representation

end FroehlichSpencer.BKT.Coulomb
