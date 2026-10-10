/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeLaw.Translation
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The tilted character translation (the dipole tilt construction, the real tilt of FS81 (7.21))

FS81's SOS observable `e^{ε[φ(0) − φ(x)]}` is a real exponential tilt of the field. Write it on
the edges as `e^{⟨Dφ, b⟩}` (`tiltExponent`), with `b` an edge field: for the SOS argument
`b = (ε/2π)∇g` with `g` the unit dipole potential (`Tilt/Potential.lean`).
Under the complex translation `φ ↦ φ + i a` of FS81 (7.25) the tilt is entire and picks up the
**phase** `e^{i⟨Da, b⟩}`: the endpoint phase `α_ρ` of (7.29).

`integral_density_tilt_mul_character_translate` is the tilted version of the generic Lebesgue
identity `integral_density_mul_character_translate`:

`∫ ρ_b χ_τ = e^{−⟨a, τ⟩} e^{i⟨Da, b⟩} ∫ ρ_b χ_τ R_{Da}(Dφ + r)`, with
`ρ_b = h e^{⟨Dφ, b⟩} ∏_e w(Dφ + r)`.

It is the multi-site contour shift `integral_add_mul_I_eq`. The tilt grows exponentially along the
shift direction, so the domination needs an **exponential majorant** of the weight on its strip
(`HasExpMajorant w W η K`: `‖w(t + iu)‖ ≤ K e^{−η|t|}`) and a tilt with `|b| ≤ η/2`. The edge
product then decays like `e^{−η|x| Σ|Dâ|}` along the shift line, against a tilt growth of at most
`e^{(η/2)|x| Σ|Dâ|}`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Tilt

open MeasureTheory Complex Filter Topology
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Reduction (gffCharacter)

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- An exponential majorant of a weight on the strip `|Im| ≤ W`. -/
def HasExpMajorant (w : ℂ → ℂ) (W η K : ℝ) : Prop :=
  ∀ t u : ℝ, |u| ≤ W → ‖w ((t : ℂ) + (u : ℂ) * I)‖ ≤ K * Real.exp (-(η * |t|))

/-- The tilt exponent `⟨Dφ, b⟩ = Σ_e b(e) Dφ(e)`. -/
def tiltExponent (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (b : E → ℝ) (φ : V → ℝ) : ℝ := ∑ e, b e * D φ e

omit [Fintype V] [DecidableEq V] in
theorem tiltExponent_add (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (b : E → ℝ) (φ ψ : V → ℝ) :
    tiltExponent D b (φ + ψ) = tiltExponent D b φ + tiltExponent D b ψ := by
  simp only [tiltExponent, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [Fintype V] [DecidableEq V] in
theorem tiltExponent_neg (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (b : E → ℝ) (φ : V → ℝ) :
    tiltExponent D b (-φ) = -tiltExponent D b φ := by
  simp only [tiltExponent, map_neg, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

omit [DecidableEq V] in
theorem continuous_tiltExponent (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (b : E → ℝ) :
    Continuous (tiltExponent D b) := by
  unfold tiltExponent
  exact continuous_finsetSum _ fun e _ => continuous_const.mul
    ((continuous_apply e).comp (LinearMap.continuous_of_finiteDimensional D))

/-- `x ↦ e^{−c|x|}` is integrable for `c > 0`. -/
theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun x : ℝ => Real.exp (-(c * |x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-(c * |x|))) (Set.Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [abs_of_pos (Set.mem_Ioi.mp hx), neg_mul]
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-(c * |x|))) (Set.Iic 0) := by
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(c * |x|))) (Set.Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mpr hpos
    have h2 := h1.comp_neg
    simp only [abs_neg] at h2
    simpa [Set.neg_Ici] using h2
  have := hneg.union hpos
  rwa [Set.Iic_union_Ioi, integrableOn_univ] at this

/-! ## The tilted Lebesgue identity -/

/-- **The tilted Lebesgue form of the character translation.** -/
theorem integral_density_tilt_mul_character_translate (hw : IsStripWeight w W c) {η K : ℝ}
    (hη : 0 < η) (hexp : HasExpMajorant w W η K)
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (r : E → ℝ) (h : (V → ℝ) → ℝ)
    (hh0 : ∀ φ, 0 ≤ h φ) (hh1 : ∀ φ, h φ ≤ 1) (b : E → ℝ) (hb : ∀ e, |b e| ≤ η / 2)
    (τ a : V → ℝ) (haW : ∀ e, |D a e| ≤ W)
    (hinv : ∀ (φ : V → ℝ) (s : ℝ), h (φ + s • a) = h φ) (hedge : a ≠ 0 → ∃ e, D a e ≠ 0)
    (hint : Integrable fun φ => h φ * Real.exp (tiltExponent D b φ) *
      ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re) :
    ∫ φ, ((h φ * Real.exp (tiltExponent D b φ) * ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re : ℝ) : ℂ) *
        gffCharacter τ φ =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        Complex.exp (((tiltExponent D b a : ℝ) : ℂ) * I) *
        ∫ φ, ((h φ * Real.exp (tiltExponent D b φ) *
          ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re : ℝ) : ℂ) *
          (gffCharacter τ φ * edgeRatio w (D a) (D φ + r)) := by
  classical
  set ρ : (V → ℝ) → ℝ := fun φ => h φ * Real.exp (tiltExponent D b φ) *
    ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re with hρ
  have hreal : ∀ φ : V → ℝ, ((ρ φ : ℝ) : ℂ) =
      (h φ : ℂ) * Complex.exp ((tiltExponent D b φ : ℝ) : ℂ) * ∏ e, w ((D φ + r) e) := by
    intro φ
    simp only [hρ, Complex.ofReal_mul, Complex.ofReal_prod, Pi.add_apply, Complex.ofReal_exp]
    congr 1
    exact Finset.prod_congr rfl fun e _ => (hw.ofReal_eq _).symm
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, Complex.ofReal_zero,
      neg_zero, Complex.exp_zero, one_mul, tiltExponent, mul_zero]
    congr 1
    funext φ
    rw [edgeRatio_zero w _ fun e => hw.ofReal_ne_zero _, mul_one]
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, a j₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ha (funext hc)
  obtain ⟨e₁, he₁⟩ := hedge ha
  obtain ⟨â, hâ_def⟩ : ∃ â : V → ℝ, â = fun j => a j / a j₀ := ⟨_, rfl⟩
  have hâj : ∀ j, a j / a j₀ = â j := fun j => by rw [hâ_def]
  have hâ_smul : â = (a j₀)⁻¹ • a := by
    funext j; simp [hâ_def, div_eq_inv_mul]
  have hDâ : ∀ e, D â e = D a e / a j₀ := by
    intro e; rw [hâ_smul, map_smul, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  -- the holomorphic integrand on complex fields
  set F : (V → ℂ) → ℂ := fun ζ =>
    Complex.exp (I * ∑ j, ζ j * (τ j : ℂ)) * ((h fun j => (ζ j).re : ℝ) : ℂ) *
      Complex.exp (∑ e, (b e : ℂ) * (((D (fun j => (ζ j).re) e : ℝ) : ℂ) +
        ((D (fun j => (ζ j).im) e : ℝ) : ℂ) * I)) *
      ∏ e, w (((D (fun j => (ζ j).re) e + r e : ℝ) : ℂ) +
        ((D (fun j => (ζ j).im) e : ℝ) : ℂ) * I) with hF
  have hline : ∀ (φ : V → ℝ) (z : ℂ), F (fun j => (φ j : ℂ) + z * ((a j / a j₀ : ℝ) : ℂ)) =
      Complex.exp (I * ∑ j, ((φ j : ℂ) + z * (â j : ℂ)) * (τ j : ℂ)) * (h φ : ℂ) *
        Complex.exp (∑ e, (b e : ℂ) * ((D φ e : ℂ) + z * (D â e : ℂ))) *
        ∏ e, w (((D φ e + r e : ℝ) : ℂ) + z * (D â e : ℂ)) := by
    intro φ z
    simp only [hF, hâj]
    have hh : (h fun j => ((φ j : ℂ) + z * (â j : ℂ)).re) = h φ := by
      have : (fun j => ((φ j : ℂ) + z * (â j : ℂ)).re) = φ + (z.re / a j₀) • a := by
        funext j
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          mul_zero, sub_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hâj]
        ring
      rw [this, hinv]
    rw [hh]
    congr 1
    · congr 1
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [linear_re_im D φ â z e]
    · refine Finset.prod_congr rfl fun e _ => ?_
      congr 1
      have := linear_re_im D φ â z e
      push_cast at this ⊢
      linear_combination this
  have hF₀ : ∀ φ : V → ℝ, F (fun j => (φ j : ℂ)) = ((ρ φ : ℝ) : ℂ) * gffCharacter τ φ := by
    intro φ
    simp only [hF, Complex.ofReal_re, Complex.ofReal_im, hreal, gffCharacter]
    have h0 : (D fun _ => (0 : ℝ)) = 0 := map_zero D
    simp only [show (fun j : V => φ j) = φ from rfl, h0, Pi.zero_apply, Complex.ofReal_zero,
      zero_mul, add_zero, Pi.add_apply, tiltExponent]
    push_cast
    ring
  have hF₁ : ∀ φ : V → ℝ, F (fun j => (φ j : ℂ) + (a j : ℂ) * I) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        Complex.exp (((tiltExponent D b a : ℝ) : ℂ) * I) *
        (((ρ φ : ℝ) : ℂ) * (gffCharacter τ φ * edgeRatio w (D a) (D φ + r))) := by
    intro φ
    have hre : (fun j => ((φ j : ℂ) + (a j : ℂ) * I).re) = φ := by funext j; simp
    have him : (fun j => ((φ j : ℂ) + (a j : ℂ) * I).im) = a := by funext j; simp
    simp only [hF, hre, him, hreal, gffCharacter]
    have hprod := prod_mul_edgeRatio hw (D a) (D φ + r)
    have hexp : Complex.exp (I * ∑ j, ((φ j : ℂ) + (a j : ℂ) * I) * (τ j : ℂ)) =
        Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
          Complex.exp (I * ∑ j, (φ j : ℂ) * (τ j : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      have hj : ∀ j, ((φ j : ℂ) + (a j : ℂ) * I) * (τ j : ℂ) =
          (φ j : ℂ) * (τ j : ℂ) + (a j : ℂ) * (τ j : ℂ) * I := fun j => by ring
      simp_rw [hj, Finset.sum_add_distrib, ← Finset.sum_mul]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    have htilt : Complex.exp (∑ e, (b e : ℂ) * (((D φ e : ℝ) : ℂ) + ((D a e : ℝ) : ℂ) * I)) =
        Complex.exp ((tiltExponent D b φ : ℝ) : ℂ) *
          Complex.exp (((tiltExponent D b a : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [tiltExponent]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    rw [hexp, htilt]
    have hprod' : ∏ e, w (((D φ e + r e : ℝ) : ℂ) + ((D a e : ℝ) : ℂ) * I) =
        (∏ e, w ((D φ + r) e)) * edgeRatio w (D a) (D φ + r) := by
      rw [hprod]; simp only [Pi.add_apply]
    rw [hprod']
    ring
  -- bounds
  have hK0 : 0 ≤ K := by
    have := hexp 0 0 (by simpa using hw.width_nonneg)
    have hn := norm_nonneg (w ((0 : ℝ) + ((0 : ℝ) : ℂ) * I))
    by_contra hK
    push Not at hK
    have : K * Real.exp (-(η * |(0 : ℝ)|)) < 0 := mul_neg_of_neg_of_pos hK (Real.exp_pos _)
    linarith
  have hstrip : ∀ (y : ℝ) (e : E), |y| ≤ |a j₀| → |y * D â e| ≤ W := by
    intro y e hy
    rw [hDâ, abs_mul, abs_div]
    calc |y| * (|D a e| / |a j₀|) ≤ |a j₀| * (|D a e| / |a j₀|) :=
          mul_le_mul_of_nonneg_right hy (by positivity)
      _ = |D a e| := by field_simp
      _ ≤ W := haW e
  have hdiff : ∀ (φ : V → ℝ) (z : ℂ), |z.im| ≤ |a j₀| →
      DifferentiableAt ℂ (fun z : ℂ => F fun j => (φ j : ℂ) + z * ((a j / a j₀ : ℝ) : ℂ)) z := by
    intro φ z hz
    simp_rw [hline φ]
    refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul (by fun_prop)
      (differentiableAt_const _)) (by fun_prop)) (DifferentiableAt.fun_finsetProd fun e _ => ?_)
    have him : |(((D φ e + r e : ℝ) : ℂ) + z * (D â e : ℂ)).im| ≤ W := by
      simpa [mul_comm] using hstrip z.im e hz
    exact ((hw.analyticAt _ him).differentiableAt).comp z (by fun_prop)
  set S : ℝ := ∑ e, |D â e| with hS
  have hSpos : 0 < S := by
    have hs : D â e₁ ≠ 0 := by rw [hDâ]; exact div_ne_zero he₁ hj₀
    exact lt_of_lt_of_le (abs_pos.mpr hs)
      (Finset.single_le_sum (f := fun e => |D â e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e₁))
  have hdom : ∀ φ : V → ℝ, ∃ B' : ℝ → ℝ, Integrable B' ∧ Tendsto B' (cocompact ℝ) (𝓝 0) ∧
      ∀ x y : ℝ, |y| ≤ |a j₀| →
        ‖F fun j => (φ j : ℂ) + ((x : ℂ) + y * I) * ((a j / a j₀ : ℝ) : ℂ)‖ ≤ B' x := by
    intro φ
    set Kτ : ℝ := Real.exp (|a j₀| * |∑ j, â j * τ j|)
    set C : ℝ := Kτ * Real.exp (tiltExponent D b φ) *
      (K ^ Fintype.card E * Real.exp (η * ∑ e, |D φ e + r e|))
    have hC0 : 0 ≤ C := by positivity
    refine ⟨fun x => C * Real.exp (-((η / 2 * S) * |x|)), ?_, ?_, ?_⟩
    · exact (integrable_exp_neg_mul_abs (by positivity)).const_mul C
    · have hlim : Tendsto (fun x : ℝ => Real.exp (-((η / 2 * S) * |x|))) (cocompact ℝ) (𝓝 0) := by
        have h1 : Tendsto (fun x : ℝ => (η / 2 * S) * |x|) (cocompact ℝ) atTop :=
          ((tendsto_norm_cocompact_atTop (E := ℝ)).congr fun x => Real.norm_eq_abs x
            : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop).const_mul_atTop (by positivity)
        exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      simpa using hlim.const_mul C
    · intro x y hy
      rw [hline φ]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hh0 φ)]
      have hexpτ : ‖Complex.exp (I * ∑ j, ((φ j : ℂ) + ((x : ℂ) + y * I) * (â j : ℂ)) *
          (τ j : ℂ))‖ ≤ Kτ := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have hre : (I * ∑ j, ((φ j : ℂ) + ((x : ℂ) + y * I) * (â j : ℂ)) * (τ j : ℂ)).re =
            -(y * ∑ j, â j * τ j) := by
          rw [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
            Complex.im_sum]
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
          ring
        rw [hre]
        calc -(y * ∑ j, â j * τ j) ≤ |y * ∑ j, â j * τ j| := neg_le_abs _
          _ = |y| * |∑ j, â j * τ j| := abs_mul _ _
          _ ≤ |a j₀| * |∑ j, â j * τ j| := mul_le_mul_of_nonneg_right hy (abs_nonneg _)
      have htiltn : ‖Complex.exp (∑ e, (b e : ℂ) * ((D φ e : ℂ) + ((x : ℂ) + y * I) *
          (D â e : ℂ)))‖ ≤ Real.exp (tiltExponent D b φ) * Real.exp ((η / 2) * |x| * S) := by
        rw [Complex.norm_exp, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hre : (∑ e, (b e : ℂ) * ((D φ e : ℂ) + ((x : ℂ) + y * I) * (D â e : ℂ))).re =
            tiltExponent D b φ + x * ∑ e, b e * D â e := by
          rw [Complex.re_sum, tiltExponent, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun e _ => ?_
          simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
          ring
        rw [hre]
        have hbound : x * ∑ e, b e * D â e ≤ (η / 2) * |x| * S := by
          calc x * ∑ e, b e * D â e ≤ |x * ∑ e, b e * D â e| := le_abs_self _
            _ = |x| * |∑ e, b e * D â e| := abs_mul _ _
            _ ≤ |x| * ∑ e, |b e| * |D â e| := by
                gcongr
                exact (Finset.abs_sum_le_sum_abs _ _).trans (by simp [abs_mul])
            _ ≤ |x| * ∑ e, (η / 2) * |D â e| := by
                gcongr with e _
                exact hb e
            _ = (η / 2) * |x| * S := by rw [← Finset.mul_sum, hS]; ring
        linarith
      have hprod : ‖∏ e, w (((D φ e + r e : ℝ) : ℂ) + ((x : ℂ) + y * I) * (D â e : ℂ))‖ ≤
          K ^ Fintype.card E * Real.exp (η * ∑ e, |D φ e + r e|) *
            Real.exp (-(η * |x| * S)) := by
        rw [norm_prod]
        have hpt : ∀ e, ((D φ e + r e : ℝ) : ℂ) + ((x : ℂ) + y * I) * (D â e : ℂ) =
            ((D φ e + r e + x * D â e : ℝ) : ℂ) + ((y * D â e : ℝ) : ℂ) * I := by
          intro e; push_cast; ring
        have hfac : ∀ e, ‖w (((D φ e + r e : ℝ) : ℂ) + ((x : ℂ) + y * I) * (D â e : ℂ))‖ ≤
            K * (Real.exp (η * |D φ e + r e|) * Real.exp (-(η * (|x| * |D â e|)))) := by
          intro e
          rw [hpt e]
          refine (hexp _ _ (hstrip y e hy)).trans ?_
          rw [← Real.exp_add]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0
          have h1 : |x| * |D â e| ≤ |D φ e + r e + x * D â e| + |D φ e + r e| := by
            have := abs_sub_abs_le_abs_sub (x * D â e) (-(D φ e + r e))
            rw [abs_mul, abs_neg] at this
            have e2 : x * D â e - -(D φ e + r e) = D φ e + r e + x * D â e := by ring
            rw [e2] at this
            linarith
          nlinarith
        calc ∏ e, ‖w (((D φ e + r e : ℝ) : ℂ) + ((x : ℂ) + y * I) * (D â e : ℂ))‖
            ≤ ∏ e, (K * (Real.exp (η * |D φ e + r e|) * Real.exp (-(η * (|x| * |D â e|))))) :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun e _ => hfac e
          _ = K ^ Fintype.card E * Real.exp (η * ∑ e, |D φ e + r e|) *
              Real.exp (-(η * |x| * S)) := by
              rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
                Finset.card_univ, ← Real.exp_sum, ← Real.exp_sum, mul_assoc]
              congr 2
              · rw [Finset.mul_sum]
              · rw [hS, Finset.mul_sum, ← Finset.sum_neg_distrib]
                congr 1
                refine Finset.sum_congr rfl fun e _ => ?_
                ring
      have hK1 : 0 ≤ K ^ Fintype.card E * Real.exp (η * ∑ e, |D φ e + r e|) := by positivity
      calc ‖Complex.exp (I * ∑ j, ((φ j : ℂ) + ((x : ℂ) + y * I) * (â j : ℂ)) * (τ j : ℂ))‖ *
            h φ * ‖Complex.exp (∑ e, (b e : ℂ) * ((D φ e : ℂ) + ((x : ℂ) + y * I) *
              (D â e : ℂ)))‖ *
            ‖∏ e, w (((D φ e + r e : ℝ) : ℂ) + ((x : ℂ) + y * I) * (D â e : ℂ))‖
          ≤ Kτ * 1 * (Real.exp (tiltExponent D b φ) * Real.exp ((η / 2) * |x| * S)) *
            (K ^ Fintype.card E * Real.exp (η * ∑ e, |D φ e + r e|) *
              Real.exp (-(η * |x| * S))) := by
            have n1 := norm_nonneg (Complex.exp (I * ∑ j, ((φ j : ℂ) + ((x : ℂ) + y * I) *
              (â j : ℂ)) * (τ j : ℂ)))
            have n2 := norm_nonneg (Complex.exp (∑ e, (b e : ℂ) * ((D φ e : ℂ) +
              ((x : ℂ) + y * I) * (D â e : ℂ))))
            have n3 := norm_nonneg (∏ e, w (((D φ e + r e : ℝ) : ℂ) + ((x : ℂ) + y * I) *
              (D â e : ℂ)))
            exact mul_le_mul (mul_le_mul (mul_le_mul hexpτ (hh1 φ) (hh0 φ) (by positivity))
              htiltn n2 (by positivity)) hprod n3 (by positivity)
        _ = C * Real.exp (-((η / 2 * S) * |x|)) := by
            simp only [C]
            have : Real.exp ((η / 2) * |x| * S) * Real.exp (-(η * |x| * S)) =
                Real.exp (-((η / 2 * S) * |x|)) := by
              rw [← Real.exp_add]; congr 1; ring
            calc Kτ * 1 * (Real.exp (tiltExponent D b φ) * Real.exp ((η / 2) * |x| * S)) *
                  (K ^ Fintype.card E * Real.exp (η * ∑ e, |D φ e + r e|) *
                    Real.exp (-(η * |x| * S)))
                = Kτ * Real.exp (tiltExponent D b φ) *
                    (K ^ Fintype.card E * Real.exp (η * ∑ e, |D φ e + r e|)) *
                    (Real.exp ((η / 2) * |x| * S) * Real.exp (-(η * |x| * S))) := by ring
              _ = _ := by rw [this]
  -- integrability
  have hmeas_char : Continuous (gffCharacter τ) := Reduction.continuous_gffCharacter τ
  have hcontR : Continuous fun φ : V → ℝ => edgeRatio w (D a) (D φ + r) :=
    continuous_edgeRatio hw (D a) haW
      ((LinearMap.continuous_of_finiteDimensional D).add continuous_const)
  have hint₀ : Integrable fun φ : V → ℝ => F fun j => (φ j : ℂ) := by
    simp_rw [hF₀]
    refine (hint.ofReal (𝕜 := ℂ)).mul_of_top_left ?_
    exact memLp_top_of_bound hmeas_char.aestronglyMeasurable 1
      (Eventually.of_forall fun φ => (Reduction.norm_gffCharacter τ φ).le)
  have hint₁ : Integrable fun φ : V → ℝ => F fun j => (φ j : ℂ) + (a j : ℂ) * I := by
    simp_rw [hF₁]
    refine Integrable.const_mul ?_ _
    refine (hint.ofReal (𝕜 := ℂ)).mul_of_top_left ?_
    refine memLp_top_of_bound (hmeas_char.mul hcontR).aestronglyMeasurable
      (Real.exp (∑ e, c (D a e))) (Eventually.of_forall fun φ => ?_)
    rw [norm_mul, Reduction.norm_gffCharacter, one_mul]
    exact norm_edgeRatio_le hw _ _ haW
  have key := integral_add_mul_I_eq F a j₀ hj₀ hdiff hdom hint₀ hint₁
  simp_rw [hF₀, hF₁] at key
  rw [key, integral_const_mul]

/-! ## The tilted density law -/

/-- **The character translation of a tilted density law** (the normalized form). -/
theorem translate_densityLaw_tilt (hw : IsStripWeight w W c) {η K : ℝ}
    (hη : 0 < η) (hexp : HasExpMajorant w W η K)
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (r : E → ℝ) (h : (V → ℝ) → ℝ) (hh_meas : Measurable h)
    (hh0 : ∀ φ, 0 ≤ h φ) (hh1 : ∀ φ, h φ ≤ 1) (b : E → ℝ) (hb : ∀ e, |b e| ≤ η / 2)
    (τ a : V → ℝ) (haW : ∀ e, |D a e| ≤ W)
    (hinv : ∀ (φ : V → ℝ) (s : ℝ), h (φ + s • a) = h φ) (hedge : a ≠ 0 → ∃ e, D a e ≠ 0) :
    ∫ φ, gffCharacter τ φ ∂densityLaw (fun φ => h φ * Real.exp (tiltExponent D b φ) *
        ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        Complex.exp (((tiltExponent D b a : ℝ) : ℂ) * I) *
        ∫ φ, gffCharacter τ φ * edgeRatio w (D a) (D φ + r) ∂densityLaw (fun φ => h φ *
          Real.exp (tiltExponent D b φ) * ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re) := by
  set ρ : (V → ℝ) → ℝ := fun φ => h φ * Real.exp (tiltExponent D b φ) *
    ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re with hρ
  have hρ0 : ∀ φ, 0 ≤ ρ φ := fun φ => mul_nonneg (mul_nonneg (hh0 φ) (Real.exp_pos _).le)
    (Finset.prod_nonneg fun _ _ => (hw.ofReal_re_pos _).le)
  have hρm : Measurable ρ := by
    refine (hh_meas.mul (continuous_tiltExponent D b).measurable.exp).mul
      (continuous_finsetProd _ fun e _ => ?_).measurable
    exact Complex.continuous_re.comp (hw.continuous_ofReal.comp
      ((continuous_apply e).comp ((LinearMap.continuous_of_finiteDimensional D).add
        continuous_const)))
  rw [integral_densityLaw hρ0 hρm, integral_densityLaw hρ0 hρm]
  by_cases hZ : densityMass ρ = ⊤
  · simp [hZ]
  rw [integral_density_tilt_mul_character_translate hw hη hexp D r h hh0 hh1 b hb τ a haW hinv
    hedge (integrable_of_densityMass_ne_top hρ0 hρm hZ)]
  ring

end FroehlichSpencer.BKT.SOS.Tilt

end
