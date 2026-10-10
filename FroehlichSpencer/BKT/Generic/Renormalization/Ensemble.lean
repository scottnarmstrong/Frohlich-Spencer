/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeLaw.Translation
public import FroehlichSpencer.BKT.Generic.EdgeLaw.Charged
public import FroehlichSpencer.BKT.Generic.GradientDisjoint
public import FroehlichSpencer.BKT.Reduction.T16AssemblyStatements

/-!
# Renormalization of one ensemble under the rooted edge law (generic core)

`edgeLaw_integral_ensemble_eq`: for an ensemble `𝒩` with at most one non-neutral density, real
shifts `σ`, and spin waves `a_ϱ` (`ϱ ∈ 𝒩₀`, the neutral part) with the support and constancy
clauses of KP Proposition 2.4, `⟨a_ϱ, ϱ'⟩ = 0` for `ϱ ≠ ϱ'`, and `|∇a_ϱ| ≤ W`,

`∫ ∏_{ϱ ∈ 𝒩} [1 + K(ϱ) cos⟨φ + σ, ϱ⟩] dμ = ∫ ∏_{ϱ ∈ 𝒩₀} [1 + K(ϱ) e^{-E_c(a_ϱ, ϱ)} F_ϱ] dμ`,

with `F_ϱ = localFactor w c (∇a_ϱ) (∇φ) (⟨φ, ϱ⟩ + ⟨σ, ϱ⟩)` (FS81 (6.18)).

* The non-neutral density drops out (KP T1.6 lists only neutral densities).

The rest of the
  product is invariant under constant shifts of `φ`, and a charged character times such a function
  integrates to zero under the rooted law (`integral_character_mul_edgeLaw_eq_zero_of_invariant`,
  the shift-invariant form of `integral_character_mul_edgeLaw_eq_zero`).
* The neutral densities are translated by `edgeLaw_integral_prod_add_mul_cos_eq_localFactor`
  , with gradient disjointness from `grad_disjoint_of_spinWave_clauses` .
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Reduction (gffCharacter)
open FroehlichSpencer.BKT.Rotator.Contour (glue glue_self glue_of_ne
  integral_eq_integral_integral_glue)

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]

/-- **FS81 (6.3) for integer charges, shift-invariant form.** Under the rooted edge law a character
of nonzero integer total charge, times a bounded measurable function invariant under constant
shifts of the field, integrates to zero. -/
theorem integral_character_mul_edgeLaw_eq_zero_of_invariant (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c)
    (v : V) (τ : V → ℤ) (hτ : ∑ j, τ j ≠ 0) (g : (V → ℝ) → ℂ) (hg : Measurable g)
    (hbdd : ∃ M : ℝ, ∀ φ, ‖g φ‖ ≤ M) (hinv : ∀ (φ : V → ℝ) (s : ℝ), g (fun j => φ j + s) = g φ) :
    ∫ φ, gffCharacter (fun j => (τ j : ℝ)) φ * g φ ∂edgeLaw G w v = 0 := by
  obtain ⟨M, hM⟩ := hbdd
  rw [edgeLaw_eq_densityLaw,
    integral_densityLaw (edgeDensity_nonneg G hw v) (measurable_edgeDensity G hw v)]
  suffices h : ∫ φ, ((edgeDensity G w v φ : ℝ) : ℂ) *
      (gffCharacter (fun j => (τ j : ℝ)) φ * g φ) = 0 by
    rw [h, mul_zero]
  set Q : ℤ := ∑ j, τ j with hQ
  set u : V → ℝ := fun j => if j = v then 0 else 1 with hu_def
  have hu : u v = 0 := by simp [hu_def]
  set f : (V → ℝ) → ℂ := fun φ => ((edgeDensity G w v φ : ℝ) : ℂ) *
    (gffCharacter (fun j => (τ j : ℝ)) φ * g φ) with hf
  have hf_int : Integrable f := by
    have hint := (integrable_edgeDensity G hG hw v).ofReal (𝕜 := ℂ)
    refine hint.mul_of_top_left (memLp_top_of_bound ?_ M (Filter.Eventually.of_forall fun φ => ?_))
    · exact ((Reduction.continuous_gffCharacter _).aestronglyMeasurable).mul
        hg.aestronglyMeasurable
    · rw [norm_mul, Reduction.norm_gffCharacter, one_mul]; exact hM _
  have hshear : ∀ (ψ : {j // j ≠ v} → ℝ) (x : ℝ),
      shear v u (glue v ψ x) = fun j => glue v ψ 0 j + x := by
    intro ψ x
    funext j
    rw [shear_apply_apply, glue_self]
    by_cases h : j = v
    · subst h; simp [glue_self, hu]
    · simp [glue_of_ne _ _ h, hu_def, h]
  have hpt : ∀ (ψ : {j // j ≠ v} → ℝ) (x : ℝ), f (shear v u (glue v ψ x)) =
      (((∏ e, (w ((G.grad (glue v ψ 0) e : ℝ) : ℂ)).re : ℝ) : ℂ) *
        gffCharacter (fun j => (τ j : ℝ)) (glue v ψ 0) * g (glue v ψ 0)) *
      ((((Set.Ico (-Real.pi) Real.pi).indicator 1 x : ℝ) : ℂ) *
        Complex.exp (I * ((Q : ℂ) * (x : ℂ)))) := by
    intro ψ x
    rw [hshear]
    have hgr : G.grad (fun j => glue v ψ 0 j + x) = G.grad (glue v ψ 0) := by
      funext e; simp only [Multigraph.grad]; ring
    have hv : glue v ψ 0 v + x = x := by rw [glue_self, zero_add]
    have hchar : gffCharacter (fun j => (τ j : ℝ)) (fun j => glue v ψ 0 j + x) =
        gffCharacter (fun j => (τ j : ℝ)) (glue v ψ 0) *
          Complex.exp (I * ((Q : ℂ) * (x : ℂ))) := by
      unfold gffCharacter
      rw [← Complex.exp_add]
      congr 1
      simp only [hQ]
      push_cast
      rw [Finset.sum_mul, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [hf, edgeDensity, hgr, hv, hchar, hinv]
    push_cast
    ring
  rw [← integral_comp_shear hu f,
    integral_eq_integral_integral_glue v ((integrable_comp_shear_iff hu).mpr hf_int)]
  simp_rw [hpt, integral_const_mul, integral_indicator_mul_exp_eq_zero hτ, mul_zero,
    integral_zero]

omit [DecidableEq V] in
/-- The product of renormalizable factors over the neutral part is invariant under constant
shifts of the field. -/
lemma prod_neutral_shift_invariant (P : Finset (V → ℤ)) (hP : ∀ ϱ ∈ P, ∑ j, ϱ j = 0)
    (K : (V → ℤ) → ℝ) (σ : V → ℝ) (φ : V → ℝ) (s : ℝ) :
    ∏ ϱ ∈ P, (1 + K ϱ * Real.cos (∑ j, ((φ j + s) + σ j) * (ϱ j : ℝ))) =
      ∏ ϱ ∈ P, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) := by
  refine Finset.prod_congr rfl fun ϱ hϱ => ?_
  have h : ∑ j, ((φ j + s) + σ j) * (ϱ j : ℝ) = ∑ j, (φ j + σ j) * (ϱ j : ℝ) + s * ∑ j, (ϱ j : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h0 : ∑ j, (ϱ j : ℝ) = 0 := by exact_mod_cast hP ϱ hϱ
  rw [h, h0, mul_zero, add_zero]

omit [Fintype V] [DecidableEq V] in
/-- Every factor `1 + K cos θ` is bounded by `1 + |K|`. -/
lemma norm_prod_one_add_mul_cos_le (P : Finset (V → ℤ)) (K : (V → ℤ) → ℝ) (θ : (V → ℤ) → ℝ) :
    ‖((∏ ϱ ∈ P, (1 + K ϱ * Real.cos (θ ϱ)) : ℝ) : ℂ)‖ ≤ ∏ ϱ ∈ P, (1 + |K ϱ|) := by
  rw [Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ϱ _ => ?_
  calc |1 + K ϱ * Real.cos (θ ϱ)| ≤ |1| + |K ϱ * Real.cos (θ ϱ)| := abs_add_le _ _
    _ ≤ 1 + |K ϱ| := by
      rw [abs_one, abs_mul]
      have := Real.abs_cos_le_one (θ ϱ)
      nlinarith [abs_nonneg (K ϱ)]

/-- **Renormalization of one ensemble under the rooted edge law** (KP §2.3.3; FS81 Theorem 6.1,
(6.18)). The non-neutral density drops out and every neutral density is translated by its own
spin wave. -/
theorem edgeLaw_integral_ensemble_eq (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) (v : V)
    (N : Finset (V → ℤ)) (hNa : AtMostOneNonNeutral N) (K : (V → ℤ) → ℝ) (σ : V → ℝ)
    (centerOf : (V → ℤ) → V) (a : (V → ℤ) → V → ℝ)
    (hconst : ∀ ϱ ∈ neutralPart N, ∀ ϱ' ∈ G.comparableDensities (neutralPart N) ϱ,
      ∃ c : ℝ, ∀ j ∈ G.densityDomainPlus ϱ' (centerOf ϱ'), a ϱ j = c)
    (hsupp : ∀ ϱ ∈ neutralPart N, Function.support (a ϱ) ⊆ G.densityDomain ϱ (centerOf ϱ))
    (horth : ∀ ϱ ∈ neutralPart N, ∀ ϱ' ∈ neutralPart N, ϱ ≠ ϱ' →
      ∑ j, a ϱ j * (ϱ' j : ℝ) = 0)
    (hW : ∀ ϱ ∈ neutralPart N, ∀ e, |G.grad (a ϱ) e| ≤ W) :
    ∫ φ, ((∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)
        ∂edgeLaw G w v =
      ∫ φ, ∏ ϱ ∈ neutralPart N, ((1 : ℂ) +
        ((K ϱ * Real.exp (-translationEnergy c (gradLinear G) (a ϱ) fun j => (ϱ j : ℝ)) : ℝ) :
          ℂ) * localFactor w c (gradLinear G (a ϱ)) (gradLinear G φ + 0)
            (∑ j, φ j * (ϱ j : ℝ) + ∑ j, σ j * (ϱ j : ℝ))) ∂edgeLaw G w v := by
  classical
  set P := neutralPart N with hPdef
  have hPneutral : ∀ ϱ ∈ P, ∑ j, ϱ j = 0 := fun ϱ hϱ => (mem_neutralPart.mp hϱ).2
  have hfin : IsProbabilityMeasure (edgeLaw G w v) := isProbabilityMeasure_edgeLaw G hG hw v
  set Rest : (V → ℝ) → ℝ := fun φ =>
    ∏ ϱ ∈ P, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) with hRest
  -- Step 1: the non-neutral density drops out
  have hdrop : ∫ φ, ((∏ ϱ ∈ N, (1 + K ϱ * Real.cos (∑ j, (φ j + σ j) * (ϱ j : ℝ))) : ℝ) : ℂ)
      ∂edgeLaw G w v = ∫ φ, ((Rest φ : ℝ) : ℂ) ∂edgeLaw G w v := by
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
                  (gffCharacter (fun j => ((-ϱc) j : ℝ)) φ * ((Rest φ : ℝ) : ℂ))) := by
        intro φ
        rw [hN, Finset.prod_insert hcP]
        change (((1 + K ϱc * Real.cos (∑ j, (φ j + σ j) * (ϱc j : ℝ))) * Rest φ : ℝ) : ℂ) = _
        generalize Rest φ = R
        have hθ : ∑ j, (φ j + σ j) * (ϱc j : ℝ) =
            ∑ j, φ j * (ϱc j : ℝ) + ∑ j, σ j * (ϱc j : ℝ) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [hθ]
        have hc1 : gffCharacter (fun j => (ϱc j : ℝ)) φ =
            Complex.exp (I * ((∑ j, φ j * (ϱc j : ℝ) : ℝ) : ℂ)) := by
          unfold gffCharacter; congr 1; push_cast; ring
        have hc2 : gffCharacter (fun j => ((-ϱc) j : ℝ)) φ =
            Complex.exp (-(I * ((∑ j, φ j * (ϱc j : ℝ) : ℝ) : ℂ))) := by
          unfold gffCharacter; congr 1
          simp only [Pi.neg_apply, Int.cast_neg]
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
      -- the charged characters integrate to zero against the shift-invariant rest
      have hRest_meas : Measurable Rest := by
        refine (continuous_finsetProd _ fun ϱ _ => ?_).measurable
        fun_prop
      have hRest_bdd : ∃ M : ℝ, ∀ φ, ‖((Rest φ : ℝ) : ℂ)‖ ≤ M :=
        ⟨∏ ϱ ∈ P, (1 + |K ϱ|), fun φ => norm_prod_one_add_mul_cos_le P K _⟩
      have hRest_inv : ∀ (φ : V → ℝ) (s : ℝ), ((Rest fun j => φ j + s : ℝ) : ℂ) =
          ((Rest φ : ℝ) : ℂ) := by
        intro φ s
        simp only [hRest]
        rw [prod_neutral_shift_invariant P hPneutral K σ φ s]
      have hz₁ := integral_character_mul_edgeLaw_eq_zero_of_invariant G hG hw v ϱc hne
        (fun φ => ((Rest φ : ℝ) : ℂ)) (Complex.measurable_ofReal.comp hRest_meas) hRest_bdd
        hRest_inv
      have hneg : ∑ j, (-ϱc) j ≠ 0 := by
        simp only [Pi.neg_apply, Finset.sum_neg_distrib, neg_ne_zero]; exact hne
      have hz₂ := integral_character_mul_edgeLaw_eq_zero_of_invariant G hG hw v (-ϱc) hneg
        (fun φ => ((Rest φ : ℝ) : ℂ)) (Complex.measurable_ofReal.comp hRest_meas) hRest_bdd
        hRest_inv
      have hint₀ : Integrable (fun φ => ((Rest φ : ℝ) : ℂ)) (edgeLaw G w v) :=
        Integrable.of_bound (Complex.measurable_ofReal.comp hRest_meas).aestronglyMeasurable
          _ (Filter.Eventually.of_forall fun φ => norm_prod_one_add_mul_cos_le P K _)
      have hintχ : ∀ τ : V → ℤ, Integrable
          (fun φ => gffCharacter (fun j => (τ j : ℝ)) φ * ((Rest φ : ℝ) : ℂ)) (edgeLaw G w v) :=
        fun τ => Integrable.of_bound
          (((Reduction.continuous_gffCharacter _).aestronglyMeasurable).mul
            (Complex.measurable_ofReal.comp hRest_meas).aestronglyMeasurable)
          (∏ ϱ ∈ P, (1 + |K ϱ|)) (Filter.Eventually.of_forall fun φ => by
            rw [norm_mul, Reduction.norm_gffCharacter, one_mul]
            exact norm_prod_one_add_mul_cos_le P K _)
      have hA := (hintχ ϱc).const_mul (Complex.exp (I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ)))
      have hB := (hintχ (-ϱc)).const_mul
        (Complex.exp (-(I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ))))
      have hAB : Integrable (fun φ => ((K ϱc / 2 : ℝ) : ℂ) *
          (Complex.exp (I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ)) *
              (gffCharacter (fun j => (ϱc j : ℝ)) φ * ((Rest φ : ℝ) : ℂ)) +
            Complex.exp (-(I * ((∑ j, σ j * (ϱc j : ℝ) : ℝ) : ℂ))) *
              (gffCharacter (fun j => ((-ϱc) j : ℝ)) φ * ((Rest φ : ℝ) : ℂ))))
          (edgeLaw G w v) := (hA.add hB).const_mul _
      rw [integral_add hint₀ hAB, integral_const_mul, integral_add hA hB, integral_const_mul,
        integral_const_mul, hz₁, hz₂]
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
  have key := edgeLaw_integral_prod_add_mul_cos_eq_localFactor G hG hw v
    (ι := P) (fun ϱ j => ((ϱ : V → ℤ) j : ℝ))
    (fun ϱ => by exact_mod_cast hPneutral ϱ ϱ.2) (fun _ => 1) (fun ϱ => K ϱ)
    (fun ϱ => ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ)) (fun ϱ => a ϱ)
    (fun ϱ ϱ' hne => horth ϱ ϱ.2 ϱ' ϱ'.2 fun h => hne (Subtype.ext h))
    (fun ϱ ϱ' hne e => hdisj ϱ ϱ.2 ϱ' ϱ'.2 (fun h => hne (Subtype.ext h)) e)
    (fun ϱ e => hW ϱ ϱ.2 e)
  have hl : ∀ φ : V → ℝ, ((Rest φ : ℝ) : ℂ) =
      ((∏ ϱ : P, (1 + K ϱ * Real.cos (∑ j, φ j * ((ϱ : V → ℤ) j : ℝ) +
        ∑ j, σ j * ((ϱ : V → ℤ) j : ℝ))) : ℝ) : ℂ) := by
    intro φ
    simp only [hRest]
    rw [← Finset.prod_coe_sort P]
    congr 2
    funext ϱ
    congr 3
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hl]
  rw [key]
  congr 1
  funext φ
  rw [← Finset.prod_coe_sort P]
  rfl

end FroehlichSpencer.BKT.Generic

end
