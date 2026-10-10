/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.LocalFactor
import FroehlichSpencer.BKT.FiniteGraph.Laplacian
import FroehlichSpencer.BKT.Surface.GFFWellDefined

/-!
# The Gaussian instance of the generic translation step

The KP law `gffLaw G hG β hβ v` (`Surface/GFFLaw.lean`) has density
`e^{-(β/2) ∑_e ∇φ(e)²} = ∏_e w(∇φ(e))` for the Gaussian bond weight `w(z) = e^{-βz²/2}`
(`gaussianWeight`), with the root phase in `[-π, π)`.

This module shows that it satisfies the
generic interface of `Generic/Translation.lean`, from the KP (2.19)
(`Reduction.gffLaw_integral_gffCharacter_translation`), and that the generic objects reduce to
KP's:

* `edgeRatio_gaussianWeight`: `R_b(x) = e^{(β/2)∑ b²} e^{-iβ∑ x b}`; at `b = ∇a`, `x = ∇φ` this
  is `e^{(β/2)‖∇a‖²}` times the character of `βΔa` (summation by parts).
* `characterTranslation_gffLaw`: `CharacterTranslation (gffLaw …) (gradLinear G) (gaussianWeight β) 0 W`
  for every strip width `W` (the Gaussian weight is entire).
* `translationEnergy_gaussian`: with the cost `c(u) = βu²/2`, `E_c` is KP's
  `SpinWaves.energyFunctional` (2.12).
* `localFactor_gaussian`: the local factor is the cosine `cos(θ + β⟨φ, Δa⟩)`; the generic
  theorem therefore reproduces KP (2.20) (`gffLaw_integral_prod_add_mul_cos_eq`).
* `grad_disjoint_of_spinWave_clauses`: the support and constancy clauses of KP P2.4
  (`Reduction.P24Step`) give pairwise disjoint gradient supports, the hypothesis of the generic
  theorem; KP's weaker `⟨a, Δa'⟩ = 0` suffices only for a quadratic weight.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Reduction (gffCharacter)

/-- The KP Gaussian bond weight `w(z) = e^{-βz²/2}`. -/
def gaussianWeight (β : ℝ) (z : ℂ) : ℂ := Complex.exp (-((β / 2 : ℝ) : ℂ) * z ^ 2)

section EdgeAlgebra

variable {E : Type*} [Fintype E]

/-- `R_b(x) = e^{(β/2) ∑_e b_e²} e^{-iβ ∑_e x_e b_e}` for the Gaussian weight. -/
theorem edgeRatio_gaussianWeight_eq (β : ℝ) (b x : E → ℝ) :
    edgeRatio (gaussianWeight β) b x =
      ((Real.exp (β / 2 * ∑ e, b e ^ 2) : ℝ) : ℂ) *
        Complex.exp (-(I * ((β * ∑ e, x e * b e : ℝ) : ℂ))) := by
  unfold edgeRatio gaussianWeight
  have hfac : ∀ e, Complex.exp (-((β / 2 : ℝ) : ℂ) * ((x e : ℂ) + (b e : ℂ) * I) ^ 2) /
      Complex.exp (-((β / 2 : ℝ) : ℂ) * ((x e : ℝ) : ℂ) ^ 2) =
        Complex.exp (((β / 2 * b e ^ 2 : ℝ) : ℂ) + -(I * ((β * (x e * b e) : ℝ) : ℂ))) := by
    intro e
    rw [← Complex.exp_sub]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [Finset.prod_congr rfl fun e _ => hfac e, ← Complex.exp_sum, Finset.sum_add_distrib,
    Complex.exp_add, Complex.ofReal_exp]
  congr 1
  · congr 1
    push_cast
    rw [Finset.mul_sum]
  · congr 1
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_neg_distrib]

/-- The Gaussian weight never vanishes. -/
theorem gaussianWeight_ne_zero (β : ℝ) (z : ℂ) : gaussianWeight β z ≠ 0 := Complex.exp_ne_zero _

/-- The Gaussian normalized ratio is the pure phase `e^{-iβ ∑ x b}`. -/
theorem normalizedEdgeRatio_gaussianWeight (β : ℝ) (b x : E → ℝ) :
    normalizedEdgeRatio (gaussianWeight β) (fun u => β / 2 * u ^ 2) b x =
      Complex.exp (-(I * ((β * ∑ e, x e * b e : ℝ) : ℂ))) := by
  unfold normalizedEdgeRatio
  rw [edgeRatio_gaussianWeight_eq, Finset.mul_sum, mul_comm, ← mul_assoc, Complex.ofReal_exp,
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- The Gaussian local factor is the cosine `cos(θ - β ∑ x b)`. -/
theorem localFactor_gaussianWeight (β : ℝ) (b x : E → ℝ) (θ : ℝ) :
    localFactor (gaussianWeight β) (fun u => β / 2 * u ^ 2) b x θ =
      Real.cos (θ - β * ∑ e, x e * b e) := by
  unfold localFactor
  rw [normalizedEdgeRatio_gaussianWeight, normalizedEdgeRatio_gaussianWeight]
  have hneg : ∑ e, x e * (-b) e = -∑ e, x e * b e := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun e _ => by rw [Pi.neg_apply, mul_neg]
  rw [hneg, ← Complex.exp_add, ← Complex.exp_add, Complex.ofReal_cos, Complex.cos]
  congr 2
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

end EdgeAlgebra

section Graph

variable {V : Type*} {E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The multigraph gradient `f ↦ (e ↦ f(src e) - f(tgt e))` as a linear map. -/
def gradLinear (G : Multigraph V E) : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun f := G.grad f
  map_add' f g := by
    funext e
    simp only [Multigraph.grad, Pi.add_apply]
    ring
  map_smul' t f := by
    funext e
    simp only [Multigraph.grad, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem gradLinear_apply (G : Multigraph V E) (f : V → ℝ) (e : E) :
    gradLinear G f e = G.grad f e := rfl

/-- Summation by parts: `-β ∑_e ∇φ(e) ∇a(e) = β ⟨φ, Δa⟩`. -/
theorem neg_mul_sum_grad_mul (G : Multigraph V E) (β : ℝ) (a φ : V → ℝ) :
    -(β * ∑ e, G.grad φ e * G.grad a e) = β * ∑ j, φ j * G.laplacian a j := by
  have h := Multigraph.pairing_laplacian_eq_neg_sum_grad_mul G φ a
  simp only [Multigraph.pairing] at h
  rw [h]
  ring

omit [Fintype E] [DecidableEq V] in
/-- The product of two characters is the character of the sum. -/
theorem gffCharacter_mul (τ σ φ : V → ℝ) :
    gffCharacter τ φ * gffCharacter σ φ = gffCharacter (fun j => τ j + σ j) φ := by
  unfold gffCharacter
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- `R_{∇a}(∇φ) = e^{(β/2)‖∇a‖²} e^{iβ⟨φ, Δa⟩}` for the Gaussian weight. -/
theorem edgeRatio_gaussianWeight (G : Multigraph V E) (β : ℝ) (a φ : V → ℝ) :
    edgeRatio (gaussianWeight β) (G.grad a) (G.grad φ) =
      ((Real.exp (β / 2 * G.energy a) : ℝ) : ℂ) *
        gffCharacter (fun j => β * G.laplacian a j) φ := by
  rw [edgeRatio_gaussianWeight_eq]
  congr 1
  unfold gffCharacter
  congr 1
  rw [← mul_neg, ← Complex.ofReal_neg, neg_mul_sum_grad_mul G β a φ]
  push_cast
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/--
**The GFF instance.** The KP law satisfies the generic character-translation interface
with the Gaussian bond weight, for every strip width (KP (2.19)).
-/
theorem characterTranslation_gffLaw (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (β : ℝ) (hβ : 0 < β) (v : V) (W : ℝ) :
    CharacterTranslation (gffLaw G hG β hβ v) (gradLinear G) (gaussianWeight β) 0 W := by
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  have hprod : ∀ τ a φ : V → ℝ, gffCharacter τ φ *
      edgeRatio (gaussianWeight β) (gradLinear G a) (gradLinear G φ + 0) =
        ((Real.exp (β / 2 * G.energy a) : ℝ) : ℂ) *
          gffCharacter (fun j => τ j + β * G.laplacian a j) φ := by
    intro τ a φ
    have hφ : gradLinear G φ + 0 = G.grad φ := by rw [add_zero]; rfl
    rw [hφ, show gradLinear G a = G.grad a from rfl, edgeRatio_gaussianWeight, mul_left_comm,
      gffCharacter_mul]
  refine ⟨fun τ a _ _ => ?_, fun τ a hτ _ => ?_⟩
  · simp_rw [hprod τ a]
    exact (Reduction.integrable_gffCharacter _ _).const_mul _
  · simp_rw [hprod τ a]
    rw [integral_const_mul, Reduction.gffLaw_integral_gffCharacter_translation G hG β hβ v a τ hτ,
      ← mul_assoc]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add, gffTranslationEnergy]
    congr 1
    simp only [Multigraph.pairing]
    push_cast
    ring

omit [DecidableEq V] in
/-- With the cost `c(u) = βu²/2`, the translation energy is KP's (2.12). -/
theorem translationEnergy_gaussian (G : Multigraph V E) (β : ℝ) (a : V → ℝ) (ϱ : V → ℤ) :
    translationEnergy (fun u => β / 2 * u ^ 2) (gradLinear G) a (fun j => (ϱ j : ℝ)) =
      SpinWaves.energyFunctional G β a ϱ := by
  rw [SpinWaves.energyFunctional_eq_KP, translationEnergy, Finset.mul_sum]
  rfl

/-- The Gaussian local factor is KP's renormalized cosine `cos(θ + β⟨φ, Δa⟩)`. -/
theorem localFactor_gaussian (G : Multigraph V E) (β : ℝ) (a φ : V → ℝ) (θ : ℝ) :
    localFactor (gaussianWeight β) (fun u => β / 2 * u ^ 2) (gradLinear G a)
        (gradLinear G φ + 0) θ =
      Real.cos (θ + β * ∑ j, φ j * G.laplacian a j) := by
  rw [add_zero, localFactor_gaussianWeight, sub_eq_add_neg]
  simp only [gradLinear_apply]
  rw [neg_mul_sum_grad_mul G β a φ]

/--
**Consistency with KP (2.20).** At the GFF instance the generic translation step
(`integral_prod_add_mul_cos_eq_localFactor`) is KP's renormalized identity: for integer neutral
densities and spin waves with `⟨a_i, ϱ_{i'}⟩ = 0` and disjoint gradient supports (`i ≠ i'`),
`∫ ∏_i [A_i + K_i cos θ_i] dμ = ∫ ∏_i [A_i + K_i e^{-E_β(a_i, ϱ_i)} cos(⟨φ, ϱ_i + βΔa_i⟩ + s_i)] dμ`
for the law `gffLaw` (compare `Reduction.gffLaw_integral_prod_spinWave_translation`, with
`A_i = 1` and KP's orthogonality `⟨a_i, Δa_{i'}⟩ = 0` in place of gradient disjointness).
-/
theorem gffLaw_integral_prod_add_mul_cos_eq (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (β : ℝ) (hβ : 0 < β) (v : V) {ι : Type*} [Fintype ι] [DecidableEq ι] (ϱ : ι → V → ℤ)
    (hneutral : ∀ i, ∑ j, ϱ i j = 0) (A K s : ι → ℝ) (a : ι → V → ℝ)
    (horth : ∀ i i', i ≠ i' → ∑ j, a i j * (ϱ i' j : ℝ) = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, G.grad (a i) e = 0 ∨ G.grad (a i') e = 0) :
    ∫ φ, ∏ i, (A i + K i * Real.cos (∑ j, φ j * (ϱ i j : ℝ) + s i)) ∂gffLaw G hG β hβ v =
      ∫ φ, ∏ i, (A i + K i * Real.exp (-SpinWaves.energyFunctional G β (a i) (ϱ i)) *
        Real.cos (∑ j, φ j * ((ϱ i j : ℝ) + β * G.laplacian (a i) j) + s i))
          ∂gffLaw G hG β hβ v := by
  have := isProbabilityMeasure_gffLaw G hG β hβ v
  set W : ℝ := ∑ i, ∑ e, |G.grad (a i) e| with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun e _ => abs_nonneg _
  have hW : ∀ i e, |gradLinear G (a i) e| ≤ W := fun i e =>
    calc |gradLinear G (a i) e| = |G.grad (a i) e| := rfl
      _ ≤ ∑ e, |G.grad (a i) e| :=
          Finset.single_le_sum (f := fun e => |G.grad (a i) e|) (fun e _ => abs_nonneg _)
            (Finset.mem_univ e)
      _ ≤ W := Finset.single_le_sum (f := fun i => ∑ e, |G.grad (a i) e|)
            (fun i _ => Finset.sum_nonneg fun e _ => abs_nonneg _) (Finset.mem_univ i)
  have h := integral_prod_add_mul_cos_eq_localFactor (gffLaw G hG β hβ v) (gradLinear G)
    (gaussianWeight β) (fun u => β / 2 * u ^ 2) (fun u => by ring) 0 hW0
    (characterTranslation_gffLaw G hG β hβ v W) (fun t => gaussianWeight_ne_zero β t)
    (fun i j => (ϱ i j : ℝ)) (fun i => by exact_mod_cast hneutral i) A K s a horth hdisj hW
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [localFactor_gaussian, translationEnergy_gaussian]
  have harg : ∑ j, φ j * ((ϱ i j : ℝ) + β * G.laplacian (a i) j) + s i =
      ∑ j, φ j * (ϱ i j : ℝ) + s i + β * ∑ j, φ j * G.laplacian (a i) j := by
    have hsum : ∑ j, φ j * ((ϱ i j : ℝ) + β * G.laplacian (a i) j) =
        ∑ j, φ j * (ϱ i j : ℝ) + β * ∑ j, φ j * G.laplacian (a i) j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    ring
  rw [harg]
  push_cast
  ring

end Graph

end FroehlichSpencer.BKT.Generic

end
