/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Contour.OneSite
public import FroehlichSpencer.BKT.Rotator.Contour.Split
public import FroehlichSpencer.BKT.Rotator.Contour.Factor
import FroehlichSpencer.BKT.Rotator.Contour.StripBounds

/-!
# The one-site contour translation in a finite pinned box

A finite pinned graph has sites `V` and edges `E`. Each edge has a head site and a tail that is
either a site or the pinned exterior, where the field takes the prescribed value `pin e` (FS81
(1.35): the exterior value is fixed). For a real field `φ : V → ℝ`, the box integrand is

`e^{i⟨q, φ⟩} · obs φ · ∏_e I_β(∇φ(e))`,

with the edge weights the Appendix B interpolation `I_β = besselInterp β` and `obs` independent of
the field at a site `j₀`. Translating the field at `j₀` by `it` (`|t| ≤ β/2`) leaves the integral
over `V → ℝ` unchanged (`integral_boxIntegrand_shift`). This is the finite-box product-measure
form of FS81 (4.15) for the non-Gaussian weight. The proof is Fubini along the coordinate `j₀`
(`integral_eq_integral_integral_glue`) and the one-dimensional contour identity
`integral_siteIntegrand_shift`; the translated integrand is dominated by a constant multiple of
the real one (`exists_norm_besselInterp_add_le`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Contour

open Complex MeasureTheory
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

/-- A finite pinned graph: each edge has a head site and a tail that is a site or the exterior,
where the field takes the value `pin e`. -/
structure PinnedGraph (V E : Type*) where
  head : E → V
  tail : E → Option V
  pin : E → ℝ

namespace PinnedGraph

variable {V E : Type*} (G : PinnedGraph V E)

/-- The edge gradient `ζ(head e) − ζ(tail e)` of a complex field (exterior value `pin e`). -/
def grad (ζ : V → ℂ) (e : E) : ℂ := ζ (G.head e) - (G.tail e).elim (G.pin e : ℂ) ζ

/-- The edge gradient of a real field. -/
def realGrad (φ : V → ℝ) (e : E) : ℝ := φ (G.head e) - (G.tail e).elim (G.pin e) φ

/-- The incidence coefficient of the site `j₀` on the edge `e`, in `{-1, 0, 1}`. -/
def incidence [DecidableEq V] (j₀ : V) (e : E) : ℝ :=
  (if G.head e = j₀ then 1 else 0) - (if G.tail e = some j₀ then 1 else 0)

lemma grad_ofReal (φ : V → ℝ) (e : E) :
    G.grad (fun j => (φ j : ℂ)) e = (G.realGrad φ e : ℂ) := by
  unfold grad realGrad
  cases G.tail e <;> simp

lemma abs_incidence_le [DecidableEq V] (j₀ : V) (e : E) : |G.incidence j₀ e| ≤ 1 := by
  unfold incidence
  split_ifs <;> norm_num

end PinnedGraph

variable {V E : Type*} [DecidableEq V]

/-- The real field translated by `w` at the site `j₀`. -/
def shiftField (j₀ : V) (w : ℂ) (φ : V → ℝ) : V → ℂ := fun j => (φ j : ℂ) + if j = j₀ then w else 0

lemma PinnedGraph.grad_shiftField (G : PinnedGraph V E) (j₀ : V) (w : ℂ) (φ : V → ℝ) (e : E) :
    G.grad (shiftField j₀ w φ) e = (G.realGrad φ e : ℂ) + G.incidence j₀ e * w := by
  unfold PinnedGraph.grad PinnedGraph.realGrad PinnedGraph.incidence shiftField
  rcases h : G.tail e with _ | k
  · simp only [Option.elim_none, reduceCtorEq, ite_false]
    split_ifs <;> push_cast <;> ring
  · simp only [Option.elim_some, Option.some.injEq]
    split_ifs <;> push_cast <;> ring

lemma ofReal_glue_eq_shiftField (j₀ : V) (ψ : {j // j ≠ j₀} → ℝ) (u : ℝ) :
    (fun j => (glue j₀ ψ u j : ℂ)) = shiftField j₀ (u : ℂ) (glue j₀ ψ 0) := by
  funext j
  unfold shiftField
  by_cases h : j = j₀
  · subst h; simp [glue_self]
  · simp [glue_of_ne _ _ h, h]

lemma shiftField_glue (j₀ : V) (ψ : {j // j ≠ j₀} → ℝ) (u t : ℝ) :
    shiftField j₀ (t * I) (glue j₀ ψ u) = shiftField j₀ ((u : ℂ) + t * I) (glue j₀ ψ 0) := by
  funext j
  unfold shiftField
  by_cases h : j = j₀
  · subst h; simp [glue_self]
  · simp [glue_of_ne _ _ h, h]

section Box

variable [Fintype V] [Fintype E]

/-- The box integrand at a complex field `ζ` with observable evaluated at the real field `φ`:
`e^{i Σ_j q_j ζ_j} · obs φ · ∏_e I_β(∇ζ(e))`. -/
def boxIntegrandAt (β : ℝ) (G : PinnedGraph V E) (q : V → ℝ) (obs : (V → ℝ) → ℂ)
    (φ : V → ℝ) (ζ : V → ℂ) : ℂ :=
  Complex.exp (I * ∑ j, (q j : ℂ) * ζ j) * obs φ * ∏ e, besselInterp β (G.grad ζ e)

/-- The real box integrand `e^{i⟨q, φ⟩} obs φ ∏_e I_β(∇φ(e))`. -/
def boxIntegrand (β : ℝ) (G : PinnedGraph V E) (q : V → ℝ) (obs : (V → ℝ) → ℂ)
    (φ : V → ℝ) : ℂ :=
  boxIntegrandAt β G q obs φ (fun j => (φ j : ℂ))

/-- The box integrand with the field at `j₀` translated by `it`. -/
def shiftedBoxIntegrand (β : ℝ) (G : PinnedGraph V E) (q : V → ℝ) (obs : (V → ℝ) → ℂ)
    (j₀ : V) (t : ℝ) (φ : V → ℝ) : ℂ :=
  boxIntegrandAt β G q obs φ (shiftField j₀ (t * I) φ)

lemma sum_mul_shiftField (q : V → ℝ) (j₀ : V) (w : ℂ) (φ : V → ℝ) :
    ∑ j, (q j : ℂ) * shiftField j₀ w φ j = ∑ j, (q j : ℂ) * (φ j : ℂ) + q j₀ * w := by
  unfold shiftField
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- At the glued field, both integrands are a constant times the one-site integrand. -/
lemma boxIntegrandAt_glue (β : ℝ) (G : PinnedGraph V E) (q : V → ℝ) (obs : (V → ℝ) → ℂ)
    (j₀ : V) (ψ : {j // j ≠ j₀} → ℝ) (w : ℂ) (φ : V → ℝ)
    (hobs : obs φ = obs (glue j₀ ψ 0)) :
    boxIntegrandAt β G q obs φ (shiftField j₀ w (glue j₀ ψ 0)) =
      (Complex.exp (I * ∑ j, (q j : ℂ) * (glue j₀ ψ 0 j : ℂ)) * obs (glue j₀ ψ 0)) *
        siteIntegrand β (q j₀) Finset.univ (G.incidence j₀) (G.realGrad (glue j₀ ψ 0)) w := by
  unfold boxIntegrandAt siteIntegrand
  rw [sum_mul_shiftField, hobs, mul_add, Complex.exp_add]
  have hprod : ∏ e, besselInterp β (G.grad (shiftField j₀ w (glue j₀ ψ 0)) e) =
      ∏ e, besselInterp β (G.incidence j₀ e * w + G.realGrad (glue j₀ ψ 0) e) := by
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [G.grad_shiftField, add_comm]
  rw [hprod]
  ring_nf

/-- Domination: the translated integrand is at most `e^{-q_{j₀} t} R^{|E|}` times the real one. -/
lemma norm_shiftedBoxIntegrand_le {β : ℝ} (G : PinnedGraph V E) (q : V → ℝ)
    (obs : (V → ℝ) → ℂ) (j₀ : V) {t R : ℝ}
    (hR : ∀ x s : ℝ, |s| ≤ β / 2 → ‖besselInterp β ((x : ℂ) + s * I)‖ ≤ R * ‖besselInterp β x‖)
    (ht : |t| ≤ β / 2) (φ : V → ℝ) :
    ‖shiftedBoxIntegrand β G q obs j₀ t φ‖ ≤
      Real.exp (-(q j₀ * t)) * R ^ Fintype.card E * ‖boxIntegrand β G q obs φ‖ := by
  unfold shiftedBoxIntegrand boxIntegrand boxIntegrandAt
  rw [sum_mul_shiftField, mul_add, Complex.exp_add]
  have hchar : ‖Complex.exp (I * ((q j₀ : ℂ) * (t * I)))‖ = Real.exp (-(q j₀ * t)) := by
    rw [Complex.norm_exp]; congr 1
    simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_im]; ring
  have hprod : ‖∏ e, besselInterp β (G.grad (shiftField j₀ (t * I) φ) e)‖ ≤
      R ^ Fintype.card E * ‖∏ e, besselInterp β (G.grad (fun j => (φ j : ℂ)) e)‖ := by
    rw [norm_prod, norm_prod, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun e _ => ?_
    rw [G.grad_shiftField, G.grad_ofReal]
    have hs : |G.incidence j₀ e * t| ≤ β / 2 := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg t) (G.abs_incidence_le j₀ e)).trans ht
    have := hR (G.realGrad φ e) (G.incidence j₀ e * t) hs
    simpa [mul_assoc] using this
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hchar]
  have h1 := norm_nonneg (Complex.exp (I * ∑ j, (q j : ℂ) * (φ j : ℂ)))
  have h2 := norm_nonneg (obs φ)
  have h3 := Real.exp_pos (-(q j₀ * t))
  calc ‖Complex.exp (I * ∑ j, (q j : ℂ) * (φ j : ℂ))‖ * Real.exp (-(q j₀ * t)) * ‖obs φ‖ *
        ‖∏ e, besselInterp β (G.grad (shiftField j₀ (t * I) φ) e)‖
      ≤ ‖Complex.exp (I * ∑ j, (q j : ℂ) * (φ j : ℂ))‖ * Real.exp (-(q j₀ * t)) * ‖obs φ‖ *
        (R ^ Fintype.card E * ‖∏ e, besselInterp β (G.grad (fun j => (φ j : ℂ)) e)‖) := by
        gcongr
    _ = Real.exp (-(q j₀ * t)) * R ^ Fintype.card E *
        (‖Complex.exp (I * ∑ j, (q j : ℂ) * (φ j : ℂ))‖ * ‖obs φ‖ *
          ‖∏ e, besselInterp β (G.grad (fun j => (φ j : ℂ)) e)‖) := by ring

omit [Fintype V] in
/-- Continuity of the edge weights along a translated real field, inside the strip. -/
lemma continuous_prod_shifted {β : ℝ} (hβ : 1 ≤ β) (G : PinnedGraph V E) (j₀ : V) {t : ℝ}
    (ht : |t| ≤ β / 2) :
    Continuous fun φ : V → ℝ => ∏ e, besselInterp β (G.grad (shiftField j₀ (t * I) φ) e) := by
  refine continuous_finsetProd _ fun e _ => ?_
  have hβ0 : 0 < β := by linarith
  refine continuous_iff_continuousAt.mpr fun φ => ?_
  have hg : Continuous fun φ : V → ℝ => G.grad (shiftField j₀ (t * I) φ) e := by
    simp_rw [G.grad_shiftField]
    unfold PinnedGraph.realGrad
    cases G.tail e <;> · simp only [Option.elim_none, Option.elim_some]; fun_prop
  have him : |(G.grad (shiftField j₀ (t * I) φ) e).im| < β := by
    have him_eq : (G.grad (shiftField j₀ (t * I) φ) e).im = G.incidence j₀ e * t := by
      rw [G.grad_shiftField]; simp
    rw [him_eq, abs_mul]
    calc |G.incidence j₀ e| * |t| ≤ 1 * |t| :=
          mul_le_mul_of_nonneg_right (G.abs_incidence_le j₀ e) (abs_nonneg t)
      _ < β := by linarith
  exact ContinuousAt.comp (g := besselInterp β)
    (Contour.differentiableAt_besselInterp hβ0 him).continuousAt hg.continuousAt

/-- The one-site contour translation in a finite pinned box (product-measure form of FS81 (4.15)
for the Appendix B weight): if the real box integrand is integrable, `obs` is measurable and
independent of the field at `j₀`, and `j₀` is an endpoint of some non-loop edge, then translating
the field at `j₀` by `it`, `|t| ≤ β/2`, does not change the integral. -/
theorem integral_boxIntegrand_shift {β : ℝ} (hβ : 1 ≤ β) (G : PinnedGraph V E) (q : V → ℝ)
    (obs : (V → ℝ) → ℂ) (hobs_meas : Measurable obs) (j₀ : V)
    (hobs : ∀ (φ : V → ℝ) (u : ℝ), obs (Function.update φ j₀ u) = obs φ)
    (hedge : ∃ e : E, G.incidence j₀ e ≠ 0) {t : ℝ} (ht : |t| ≤ β / 2)
    (hint : Integrable (boxIntegrand β G q obs)) :
    ∫ φ, boxIntegrand β G q obs φ = ∫ φ, shiftedBoxIntegrand β G q obs j₀ t φ := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_besselInterp_add_le hβ
  obtain ⟨e₀, he₀⟩ := hedge
  -- integrability of the translated integrand
  have hmeas : AEStronglyMeasurable (shiftedBoxIntegrand β G q obs j₀ t) := by
    unfold shiftedBoxIntegrand boxIntegrandAt
    refine ((Continuous.aestronglyMeasurable (by
      simp_rw [sum_mul_shiftField]; fun_prop)).mul hobs_meas.aestronglyMeasurable).mul
      (continuous_prod_shifted hβ G j₀ ht).aestronglyMeasurable
  have hint' : Integrable (shiftedBoxIntegrand β G q obs j₀ t) :=
    (hint.norm.const_mul (Real.exp (-(q j₀ * t)) * R ^ Fintype.card E)).mono' hmeas
      (Filter.Eventually.of_forall (norm_shiftedBoxIntegrand_le G q obs j₀ hR ht))
  rw [integral_eq_integral_integral_glue j₀ hint, integral_eq_integral_integral_glue j₀ hint']
  congr 1
  funext ψ
  have hobsψ : ∀ u : ℝ, obs (glue j₀ ψ u) = obs (glue j₀ ψ 0) := fun u => by
    rw [glue_eq_update j₀ ψ u, hobs]
  have hreal : ∀ u : ℝ, boxIntegrand β G q obs (glue j₀ ψ u) =
      (Complex.exp (I * ∑ j, (q j : ℂ) * (glue j₀ ψ 0 j : ℂ)) * obs (glue j₀ ψ 0)) *
        siteIntegrand β (q j₀) Finset.univ (G.incidence j₀) (G.realGrad (glue j₀ ψ 0)) u := by
    intro u
    unfold boxIntegrand
    rw [ofReal_glue_eq_shiftField]
    exact boxIntegrandAt_glue β G q obs j₀ ψ u _ (hobsψ u)
  have hshift : ∀ u : ℝ, shiftedBoxIntegrand β G q obs j₀ t (glue j₀ ψ u) =
      (Complex.exp (I * ∑ j, (q j : ℂ) * (glue j₀ ψ 0 j : ℂ)) * obs (glue j₀ ψ 0)) *
        siteIntegrand β (q j₀) Finset.univ (G.incidence j₀) (G.realGrad (glue j₀ ψ 0))
          ((u : ℂ) + t * I) := by
    intro u
    unfold shiftedBoxIntegrand
    rw [shiftField_glue]
    exact boxIntegrandAt_glue β G q obs j₀ ψ _ _ (hobsψ u)
  simp_rw [hreal, hshift]
  rw [integral_const_mul, integral_const_mul,
    integral_siteIntegrand_shift hβ (q j₀) Finset.univ (G.incidence j₀)
      (G.realGrad (glue j₀ ψ 0)) (fun e _ => G.abs_incidence_le j₀ e) (Finset.mem_univ e₀) he₀ ht]

/-- The normalized box integrand of FS81 (4.15):
`e^{i⟨q, φ⟩} obs φ ∏_e i_β(σ_e t; ∇φ(e)) ∏_e I_β(∇φ(e))`, with `σ_e` the incidence of `j₀`. -/
def normalizedBoxIntegrand (β C : ℝ) (G : PinnedGraph V E) (q : V → ℝ) (obs : (V → ℝ) → ℂ)
    (j₀ : V) (t : ℝ) (φ : V → ℝ) : ℂ :=
  Complex.exp (I * ∑ j, (q j : ℂ) * (φ j : ℂ)) * obs φ *
    (∏ e, normalizedFactor β C (G.incidence j₀ e * t) (G.realGrad φ e)) *
    ∏ e, besselInterp β (G.realGrad φ e)

/-- Pointwise: the translated integrand is `e^{-q_{j₀} t} e^{Σ_e g(σ_e t)/β}` times the
normalized one. -/
lemma shiftedBoxIntegrand_eq {β C : ℝ} (hβ : 1 ≤ β) (G : PinnedGraph V E) (q : V → ℝ)
    (obs : (V → ℝ) → ℂ) (j₀ : V) (t : ℝ) (φ : V → ℝ) :
    shiftedBoxIntegrand β G q obs j₀ t φ =
      Complex.exp (-((q j₀ * t : ℝ) : ℂ)) *
        Complex.exp (((∑ e, cEnvelope C (G.incidence j₀ e * t) / β : ℝ)) : ℂ) *
        normalizedBoxIntegrand β C G q obs j₀ t φ := by
  have hβ0 : 0 < β := by linarith
  unfold shiftedBoxIntegrand boxIntegrandAt normalizedBoxIntegrand
  rw [sum_mul_shiftField, mul_add, Complex.exp_add]
  have hprod : ∏ e, besselInterp β (G.grad (shiftField j₀ (t * I) φ) e) =
      ∏ e, besselInterp β ((G.realGrad φ e : ℂ) + (G.incidence j₀ e * t : ℝ) * I) := by
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [G.grad_shiftField]; push_cast; ring_nf
  rw [hprod, prod_besselInterp_add_mul_I_eq (C := C) Finset.univ (fun e => G.incidence j₀ e * t)
    (fun e => (G.realGrad φ e : ℂ))
    (fun e _ => besselInterp_ne_zero hβ0 (by simpa using hβ0))]
  have hchar : Complex.exp (I * ((q j₀ : ℂ) * (t * I))) = Complex.exp (-((q j₀ * t : ℝ) : ℂ)) := by
    congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [hchar]
  ring

/-- FS81 (4.15) in a finite pinned box, normalized form:
`∫ e^{i⟨q,φ⟩} obs ∏ I_β(∇φ) = e^{-q_{j₀} t} e^{Σ_e g(σ_e t)/β} ∫ e^{i⟨q,φ⟩} obs ∏ i_β(σ_e t; ∇φ) ∏ I_β(∇φ)`,
for any envelope constant `C` (the identity is exact; the envelope only enters bounds). -/
theorem integral_boxIntegrand_eq_normalized {β C : ℝ} (hβ : 1 ≤ β) (G : PinnedGraph V E)
    (q : V → ℝ) (obs : (V → ℝ) → ℂ) (hobs_meas : Measurable obs) (j₀ : V)
    (hobs : ∀ (φ : V → ℝ) (u : ℝ), obs (Function.update φ j₀ u) = obs φ)
    (hedge : ∃ e : E, G.incidence j₀ e ≠ 0) {t : ℝ} (ht : |t| ≤ β / 2)
    (hint : Integrable (boxIntegrand β G q obs)) :
    ∫ φ, boxIntegrand β G q obs φ =
      Complex.exp (-((q j₀ * t : ℝ) : ℂ)) *
        Complex.exp (((∑ e, cEnvelope C (G.incidence j₀ e * t) / β : ℝ)) : ℂ) *
        ∫ φ, normalizedBoxIntegrand β C G q obs j₀ t φ := by
  rw [integral_boxIntegrand_shift hβ G q obs hobs_meas j₀ hobs hedge ht hint]
  simp_rw [shiftedBoxIntegrand_eq (C := C) hβ G q obs j₀ t]
  rw [integral_const_mul]

/-- The one-site contour estimate in a finite pinned box (FS81 (4.15)–(4.16) for the Appendix B
weight): with the envelope `g` of property (c), for `β ≥ β₀` and `|t| ≤ β/2`,
`‖∫ e^{i⟨q,φ⟩} obs ∏ I_β(∇φ)‖ ≤ e^{-q_{j₀} t + Σ_e g(σ_e t)/β} ∫ ‖e^{i⟨q,φ⟩} obs ∏ I_β(∇φ)‖`. -/
theorem norm_integral_boxIntegrand_le :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧ ∀ β : ℝ, β₀ ≤ β → 1 ≤ β →
      ∀ {V E : Type} [DecidableEq V] [Fintype V] [Fintype E] (G : PinnedGraph V E)
        (q : V → ℝ) (obs : (V → ℝ) → ℂ), Measurable obs → ∀ j₀ : V,
        (∀ (φ : V → ℝ) (u : ℝ), obs (Function.update φ j₀ u) = obs φ) →
        (∃ e : E, G.incidence j₀ e ≠ 0) → ∀ t : ℝ, |t| ≤ β / 2 →
        Integrable (boxIntegrand β G q obs) →
        ‖∫ φ, boxIntegrand β G q obs φ‖ ≤
          Real.exp (-(q j₀ * t) + ∑ e, cEnvelope C (G.incidence j₀ e * t) / β) *
            ∫ φ, ‖boxIntegrand β G q obs φ‖ := by
  obtain ⟨β₀, C, hβ₀, hC, hc⟩ := exists_translation_envelope
  refine ⟨β₀, C, hβ₀, hC, fun β hββ₀ hβ V E _ _ _ G q obs hobs_meas j₀ hobs hedge t ht hint => ?_⟩
  rw [integral_boxIntegrand_eq_normalized (C := C) hβ G q obs hobs_meas j₀ hobs hedge ht hint,
    norm_mul, norm_mul, norm_cexp_neg_ofReal]
  have hE : ‖Complex.exp (((∑ e, cEnvelope C (G.incidence j₀ e * t) / β : ℝ)) : ℂ)‖ =
      Real.exp (∑ e, cEnvelope C (G.incidence j₀ e * t) / β) := by
    rw [Complex.norm_exp, ofReal_re]
  rw [hE, Real.exp_add]
  have hpt : ∀ φ : V → ℝ, ‖normalizedBoxIntegrand β C G q obs j₀ t φ‖ ≤
      ‖boxIntegrand β G q obs φ‖ := by
    intro φ
    unfold normalizedBoxIntegrand boxIntegrand boxIntegrandAt
    have hn : ‖∏ e, normalizedFactor β C (G.incidence j₀ e * t) (G.realGrad φ e)‖ ≤ 1 :=
      norm_prod_normalizedFactor_le_one Finset.univ _ _ fun e _ => hc β hββ₀ _ _ (by
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg t) (G.abs_incidence_le j₀ e)).trans ht)
    have hgr : ∏ e, besselInterp β (G.grad (fun j => (φ j : ℂ)) e) =
        ∏ e, besselInterp β (G.realGrad φ e) :=
      Finset.prod_congr rfl fun e _ => by rw [G.grad_ofReal]
    rw [hgr, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    have h1 := norm_nonneg (Complex.exp (I * ∑ j, (q j : ℂ) * (φ j : ℂ)))
    have h2 := norm_nonneg (obs φ)
    have h3 := norm_nonneg (∏ e, besselInterp β (G.realGrad φ e))
    calc ‖Complex.exp (I * ∑ j, (q j : ℂ) * (φ j : ℂ))‖ * ‖obs φ‖ *
          ‖∏ e, normalizedFactor β C (G.incidence j₀ e * t) (G.realGrad φ e)‖ *
          ‖∏ e, besselInterp β (G.realGrad φ e)‖
        ≤ ‖Complex.exp (I * ∑ j, (q j : ℂ) * (φ j : ℂ))‖ * ‖obs φ‖ * 1 *
          ‖∏ e, besselInterp β (G.realGrad φ e)‖ := by gcongr
      _ = _ := by ring
  have hmono : ‖∫ φ, normalizedBoxIntegrand β C G q obs j₀ t φ‖ ≤
      ∫ φ, ‖boxIntegrand β G q obs φ‖ :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint.norm
        (Filter.Eventually.of_forall hpt))
  calc Real.exp (-(q j₀ * t)) * Real.exp (∑ e, cEnvelope C (G.incidence j₀ e * t) / β) *
        ‖∫ φ, normalizedBoxIntegrand β C G q obs j₀ t φ‖
      ≤ Real.exp (-(q j₀ * t)) * Real.exp (∑ e, cEnvelope C (G.incidence j₀ e * t) / β) *
        ∫ φ, ‖boxIntegrand β G q obs φ‖ := by gcongr

end Box

end FroehlichSpencer.BKT.Rotator.Contour
