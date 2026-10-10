/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.CompactTranslation
public import FroehlichSpencer.BKT.Clock.Compact.Assembly
import Mathlib.Tactic

/-!
# The charge-layer renormalization on the compact Villain law

The Villain analogue of `Clock/Compact/Assembly.lean`: the translated product of
`VillainTranslation.lean` assembled over a charge layer. The statements are those of the cosine
file with the Villain law and the Villain local factors; the cost is the cosine clock cost.

* `integral_character_mul_prod_villainCompactLaw_eq_zero`;
* `villainCompactLaw_integral_ensemble_eq`;
* **`villainCompactLaw_renormalization_of_chargeLayer`**, `villainCompactLaw_renormalization_kp`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open MeasureTheory Complex
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Reduction (gffCharacter norm_gffCharacter signSet mem_signSet)

variable {V : Type} [Fintype V] {E : Type} [Fintype E]

/-- A compatible character of nonzero total charge, times a product of factors
`A_i + B_i cos(⟨φ, ϱ_i⟩ + s_i)` with compatible neutral densities, integrates to zero under the
compact Villain law (each term of the product's character expansion has the same nonzero charge). -/
theorem integral_character_mul_prod_villainCompactLaw_eq_zero {n β : ℝ} (hn : 0 < n) (hβ : 0 < β)
    (G : Multigraph V E) (τ : V → ℝ) (hτc : IsClockCompatible n τ) (hτ : ∑ j, τ j ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℝ)
    (hc : ∀ i, IsClockCompatible n (ϱ i)) (hneu : ∀ i, ∑ j, ϱ i j = 0) (A B s : ι → ℝ) :
    ∫ φ, gffCharacter τ φ * ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ)
      ∂villainCompactLaw β n G = 0 := by
  classical
  have hμ := isProbabilityMeasure_villainCompactLaw G hβ hn
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
  rw [integral_character_villainCompactLaw_eq_zero hn hβ G _ hcomp hQ, mul_zero]

/-- **Renormalization of one ensemble under the compact Villain law** (KP §2.3.3; FS81 (6.18), (7.9)–(7.14)
on the compact box). The non-neutral density drops out
(`integral_character_mul_prod_villainCompactLaw_eq_zero`)
and every neutral density is translated by its own spin wave. -/
theorem villainCompactLaw_integral_ensemble_eq [DecidableEq V] {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 < β)
    (G : Multigraph V E) (N : Finset (V → ℤ)) (hNa : AtMostOneNonNeutral N) (K : (V → ℤ) → ℝ)
    (σ : V → ℝ) (centerOf : (V → ℤ) → V) (a : (V → ℤ) → V → ℝ)
    (hconst : ∀ ϱ ∈ neutralPart N, ∀ ϱ' ∈ G.comparableDensities (neutralPart N) ϱ,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ' (centerOf ϱ'), a ϱ j = c)
    (hsupp : ∀ ϱ ∈ neutralPart N, Function.support (a ϱ) ⊆ G.densityDomain ϱ (centerOf ϱ))
    (horth : ∀ ϱ ∈ neutralPart N, ∀ ϱ' ∈ neutralPart N, ϱ ≠ ϱ' →
      ∑ j, a ϱ j * (ϱ' j : ℝ) = 0) :
    ∫ φ, ((∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)
        ∂villainCompactLaw β n G =
      ∫ φ, ∏ ϱ ∈ neutralPart N, ((1 : ℂ) +
        ((K ϱ * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear G) (a ϱ)
          fun j => (ϱ j : ℝ)) : ℝ) : ℂ) *
          localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) (gradLinear G (a ϱ))
            (gradLinear G φ) (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂villainCompactLaw β n G := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set P := neutralPart N with hPdef
  have hPneutral : ∀ ϱ ∈ P, ∑ j, ϱ j = 0 := fun ϱ hϱ => (mem_neutralPart.mp hϱ).2
  have hfin : IsProbabilityMeasure (villainCompactLaw β n G) := isProbabilityMeasure_villainCompactLaw G hβ hn'
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
      ∂villainCompactLaw β n G = ∫ φ, ((Rest φ : ℝ) : ℂ) ∂villainCompactLaw β n G := by
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
      have hint₀ : Integrable (fun φ => ((Rest φ : ℝ) : ℂ)) (villainCompactLaw β n G) :=
        Integrable.of_bound (Complex.measurable_ofReal.comp hRest_meas).aestronglyMeasurable
          _ (Filter.Eventually.of_forall fun φ => norm_prod_one_add_mul_cos_le P K _)
      have hintχ : ∀ τ : V → ℝ, Integrable
          (fun φ => gffCharacter τ φ * ((Rest φ : ℝ) : ℂ)) (villainCompactLaw β n G) :=
        fun τ => Integrable.of_bound
          (((Reduction.continuous_gffCharacter _).aestronglyMeasurable).mul
            (Complex.measurable_ofReal.comp hRest_meas).aestronglyMeasurable)
          (∏ ϱ ∈ P, (1 + |K ϱ|)) (Filter.Eventually.of_forall fun φ => by
            rw [norm_mul, Reduction.norm_gffCharacter, one_mul]
            exact norm_prod_one_add_mul_cos_le P K _)
      have hzero : ∀ τ : V → ℝ, IsClockCompatible (n : ℝ) τ → ∑ j, τ j ≠ 0 →
          ∫ φ, gffCharacter τ φ * ((Rest φ : ℝ) : ℂ) ∂villainCompactLaw β n G = 0 := by
        intro τ hτc hτ
        simp_rw [hRestP]
        exact integral_character_mul_prod_villainCompactLaw_eq_zero hn' hβ G τ hτc hτ
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
          (villainCompactLaw β n G) := (hA.add hB).const_mul _
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
  have key := integral_prod_add_mul_cos_villainCompactLaw hn' hβ G (ι := P)
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

section Layer

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {G : Multigraph V E}
  {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V} {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/--
For a rooted-compatible charge
layer and the clock cost with a two-branch envelope, the waves `layerSpinWave` give, for every
real shift `σ`,
`∫ ∏_j λ_j(φ_j + σ_j) dμ = ∑_i c_i ∫ ∏_{ϱ ∈ ℛ_i} [1 + z_i(ϱ) F_{i,ϱ}] dμ` under the compact Villain law,
with the activity bound of the layer, the gradient bound `|∇a| ≤ W`, locality, `|F| ≤ 1` and `F`
real.

The strip decay of `IsStripWeight` is replaced by the compact character translation
(`integral_villainCompactLaw_characterTranslation`) and the constant-mode vanishing of charged compatible
characters; no strip condition enters the translation.
-/
theorem villainCompactLaw_renormalization_of_chargeLayer {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 < β)
    (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hroot : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i))
    {κ κ' W : ℝ} (hc : IsCostEnvelope (clockShiftCost β n) κ κ' W) (hκ : 0 < κ) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W)
    (hW1 : 1 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀)) (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁) :
    ∃ (z : Fin CL.n → (V → ℤ) → ℝ) (a : Fin CL.n → (V → ℤ) → V → ℝ),
      (∀ σ : V → ℝ, ∫ φ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) ∂villainCompactLaw β n G =
        ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.R i, ((1 : ℂ) + (z i ϱ : ℂ) *
          localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) (gradLinear G (a i ϱ))
            (gradLinear G φ) (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂villainCompactLaw β n G) ∧
      ∀ i, ∀ ϱ ∈ CL.R i,
        |z i ϱ| ≤ Real.exp (D₂ * A ϱ) * Zent ϱ *
          Real.exp (-(amp / 8 * ∑ j, |(ϱ j : ℝ)|) - amp / (8 * D₁) * A ϱ) ∧
        (∀ e, |G.grad (a i ϱ) e| ≤ W) ∧
        Function.support (a i ϱ) ⊆ G.densityDomain ϱ (centerOf ϱ) ∧
        ∀ (φ : V → ℝ) (θ : ℝ),
          ‖localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) (gradLinear G (a i ϱ))
            (gradLinear G φ) θ‖ ≤ 1 ∧
          (localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) (gradLinear G (a i ϱ))
            (gradLinear G φ) θ).im = 0 := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set a : Fin CL.n → (V → ℤ) → V → ℝ := fun i ϱ => layerSpinWave CL κ amp k₀ i ϱ with ha
  set z : Fin CL.n → (V → ℤ) → ℝ := fun i ϱ =>
    CL.K i ϱ * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear G) (a i ϱ)
      fun j => (ϱ j : ℝ)) with hz
  have hgrad : ∀ i, ∀ ϱ ∈ CL.R i, ∀ e, |G.grad (a i ϱ) e| ≤ W := by
    intro i ϱ hϱ e
    obtain ⟨hα, hK0, hK1, -⟩ := Classical.choose_spec (CL.wave i ϱ hϱ)
    simp only [ha, layerSpinWave, dite_eq_left hϱ]
    refine (abs_grad_envelopeWave_le _ hκ (by rw [hK0]; exact hK₀) (by rw [hK1]; exact hK₁)
      hamp k₀ e).trans ?_
    rw [hK1]
    exact max_le hampW hW1
  refine ⟨z, a, fun σ => ?_, fun i ϱ hϱ => ⟨?_, hgrad i ϱ hϱ, ?_, fun φ θ => ⟨?_, ?_⟩⟩⟩
  · have hfin : IsProbabilityMeasure (villainCompactLaw β n G) := isProbabilityMeasure_villainCompactLaw G hβ hn'
    have hpt : ∀ φ : V → ℝ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) =
        ∑ i, (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
          (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ) := by
      intro φ
      rw [CL.expand fun j => φ j + σ j]
      push_cast
      rfl
    have hint : ∀ i, Integrable (fun φ : V → ℝ => (CL.c i : ℂ) * ((∏ ϱ ∈ CL.N i,
        (1 + CL.K i ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ))
        (villainCompactLaw β n G) := by
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
    have key := villainCompactLaw_integral_ensemble_eq hn hβ G (CL.N i) hNa (CL.K i) σ centerOf (a i)
      hconst hsupp horth
    rw [key, hR]
  · have hgain := layer_gain CL hc hκ hK₀ hK₁ hD₁ hamp hampW hk₀ hexp hquad₁ hquad₂ i ϱ hϱ
    have hK := CL.entropy i ϱ hϱ
    simp only [hz, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hZ : 0 ≤ Real.exp (D₂ * A ϱ) * Zent ϱ := (abs_nonneg _).trans hK
    refine mul_le_mul hK (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hZ
    simp only [ha] at hgain ⊢
    linarith
  · simp only [ha]
    exact (layerSpinWave_clauses CL κ amp k₀ i).2.1 ϱ hϱ
  · exact villainLocalFactor_norm_le_one hβ hn' _ _ (fun e => hgrad i ϱ hϱ e) θ
  · exact villainLocalFactor_im_eq_zero β n _ _ (fun e => hgrad i ϱ hϱ e) θ

/-- **The T1.6-NG theorem on KP's square domains for the compact Villain law** (the Villain instance;
compare `edgeLaw_renormalization_kp`): a finite convex family of neutral KP ensembles such that,
for every real shift `σ`,
`∫ ∏_j λ_j(φ_j + σ_j) dμ = ∑_i c_i ∫ ∏_{ϱ ∈ 𝒩_i} [1 + z_i(ϱ) F_{i,ϱ}] dμ` under the compact Villain law, with
`|z| ≤ e^{200 A(ϱ)} Z(ϱ) exp(−(λ/8)∑|ϱ| − λ/(8D₁) A(ϱ))`, `|∇a| ≤ W`, locality, `|F| ≤ 1`, `F`
real, and KP's domain disjointness at each dyadic scale. -/
theorem villainCompactLaw_renormalization_kp (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (hdom : boundary = .free ∨ Even L) {E : Type} [Fintype E] (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ) {D₁ : ℝ}
    (hD₁ : 0 < D₁) (h21 : Reduction.P21Step boundary L D₁)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hNq : ∀ j, 0 < Nq j)
    (hcut : ∀ j q, Nq j < q → lamHat j q = 0)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hζpos : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) {n : ℕ} (hn : 0 < n) {β : ℝ}
    (hβ : 0 < β) {κ κ' W : ℝ} (hc : IsCostEnvelope (clockShiftCost β n) κ κ' W) (hκ : 0 < κ)
    {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * 28 ≤ W) (hW1 : 1 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28) :
    ∃ (m : ℕ) (N : Fin m → Finset (Fin L × Fin L → ℤ)) (cc : Fin m → ℝ)
      (z : Fin m → (Fin L × Fin L → ℤ) → ℝ)
      (a : Fin m → (Fin L × Fin L → ℤ) → Fin L × Fin L → ℝ),
      (∀ i, IsChargeEnsemble (N i)) ∧ (∀ i, 0 < cc i) ∧ ∑ i, cc i = 1 ∧
      (∀ i, ∀ ϱ ∈ N i, ∑ j, ϱ j = 0) ∧
      (∀ σ : Fin L × Fin L → ℝ, ∫ φ, ((∏ j, lam j (φ j + σ j) : ℝ) : ℂ) ∂villainCompactLaw β n Λ =
        ∑ i, (cc i : ℂ) * ∫ φ, ∏ ϱ ∈ N i, ((1 : ℂ) + (z i ϱ : ℂ) *
          localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) (gradLinear Λ (a i ϱ))
            (gradLinear Λ φ) (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂villainCompactLaw β n Λ) ∧
      ∀ i, (∀ ϱ ∈ N i,
          |z i ϱ| ≤ Real.exp (200 * (chargeCoverCost boundary L ϱ : ℝ)) *
              (∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs) *
            Real.exp (-(amp / 8 * ∑ j, |(ϱ j : ℝ)|) -
              amp / (8 * D₁) * (chargeCoverCost boundary L ϱ : ℝ)) ∧
          (∀ e, |Λ.grad (a i ϱ) e| ≤ W) ∧
          Function.support (a i ϱ) ⊆ Λ.densityDomain ϱ (centerOf ϱ) ∧
          ∀ (φ : Fin L × Fin L → ℝ) (θ : ℝ),
            ‖localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) (gradLinear Λ (a i ϱ))
              (gradLinear Λ φ) θ‖ ≤ 1 ∧
            (localFactor (villainClockEdgeWeight β n) (clockShiftCost β n) (gradLinear Λ (a i ϱ))
              (gradLinear Λ φ) θ).im = 0) ∧
        ∀ ϱ₁ ∈ N i, ∀ ϱ₂ ∈ N i, ϱ₁ ≠ ϱ₂ → ∀ k : ℕ, 1 ≤ k →
          Λ.densityDiameter ϱ₁ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
          Λ.densityDiameter ϱ₂ ∈ Set.Icc (2 ^ k - 1) (2 ^ (k + 1) - 2) →
          ∀ j₁ j₂ : Fin L × Fin L, Λ.IsDensityCenter ϱ₁ j₁ → Λ.IsDensityCenter ϱ₂ j₂ →
            Λ.densityDomain ϱ₁ j₁ ∩ Λ.densityDomain ϱ₂ j₂ = ∅ := by
  obtain ⟨CL, hCL⟩ := exists_kpChargeLayer boundary hL hdom Λ hΛ hdist B h46 hD₁.le h21
    centerOf hcenter lam Nq lamHat ζ hNq hcut hlam hζpos hζsum
  obtain ⟨z, a, hid, hz⟩ := villainCompactLaw_renormalization_of_chargeLayer hn hβ CL
    (fun i => ⟨(hCL i).1, (hCL i).2.1⟩) hc hκ (by norm_num) (by norm_num) hD₁ hamp hampW hW1
    hk₀ hexp hquad₁ hquad₂
  refine ⟨CL.n, CL.R, CL.c, z, a, fun i => ?_, CL.c_pos, CL.c_sum, fun i ϱ hϱ => ?_, hid,
    fun i => ⟨hz i, ?_⟩⟩
  · rw [(hCL i).1]; exact (hCL i).2.2.1.neutralPart
  · rw [(hCL i).1] at hϱ; exact (mem_neutralPart.mp hϱ).2
  · intro ϱ₁ h₁ ϱ₂ h₂ hne k hk hd₁ hd₂ j₁ j₂ hj₁ hj₂
    rw [(hCL i).1] at h₁ h₂
    exact Reduction.densityDomain_inter_eq_empty boundary Λ hΛ hdist
      ((hCL i).2.2.2.1 ϱ₁ (mem_neutralPart.mp h₁).1 ϱ₂ (mem_neutralPart.mp h₂).1 hne) hk hd₁ hd₂
      hj₁ hj₂

end Layer

end FroehlichSpencer.BKT.Clock.VillainClock

end
