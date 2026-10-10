/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeLaw.Defs
public import FroehlichSpencer.BKT.Generic.EdgeLaw.MultiSiteShift

/-!
# Character translation for the edge laws (generic core)

* `characterTranslation_edgeLaw`: the rooted law `edgeLaw G w v` on a connected multigraph admits
  the complex translation `φ ↦ φ + i a` of every neutral character, for every real `a` with
  `|∇a| ≤ W`;
* `characterTranslation_pinnedEdgeLaw`: the same for the pinned law on an anchored pinned graph
  (no nonzero field has zero linear gradient), for every character;
* `edgeLaw_integral_prod_add_mul_cos_eq_localFactor`: the generic translation step of
  `Generic/LocalFactor.lean` on the rooted law.

Both follow from one Lebesgue identity, `integral_density_mul_character_translate`, for a density
`h(φ) ∏_e w(Dφ(e) + r(e))` whose extra factor `h` is invariant along `a`; it is the multi-site
contour shift `integral_add_mul_I_eq` applied to
`F(ζ) = e^{i⟨ζ, τ⟩} h(Re ζ) ∏_e w(D(Re ζ)(e) + r(e) + i D(Im ζ)(e))`.

For the rooted law
`h = 𝟙_{[-π, π)}(φ(v))`, and a neutral character lets one replace `a` by `a − a(v)`, which fixes
the root coordinate without changing `⟨a, τ⟩` or `∇a`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Filter Topology
open FroehlichSpencer.BKT.Reduction (gffCharacter)
open FroehlichSpencer.BKT.Rotator.Contour (PinnedGraph)

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-! ## The edge ratio of a strip weight -/

omit [Fintype V] [DecidableEq V] in
/-- `|R_b(x)| ≤ e^{∑_e c(b_e)}` for a strip weight, when `|b| ≤ W`. -/
theorem norm_edgeRatio_le (hw : IsStripWeight w W c) (b x : E → ℝ) (hb : ∀ e, |b e| ≤ W) :
    ‖edgeRatio w b x‖ ≤ Real.exp (∑ e, c (b e)) := by
  unfold edgeRatio
  rw [norm_prod, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun e _ => hw.ratio_le _ _ (hb e)

omit [Fintype V] [DecidableEq V] in
/-- The edge ratio along a continuous family of real gradients is continuous. -/
theorem continuous_edgeRatio (hw : IsStripWeight w W c) (b : E → ℝ) (hb : ∀ e, |b e| ≤ W)
    {X : Type*} [TopologicalSpace X] {x : X → E → ℝ} (hx : Continuous x) :
    Continuous fun p => edgeRatio w b (x p) := by
  unfold edgeRatio
  refine continuous_finsetProd _ fun e _ => Continuous.div ?_ ?_ fun p => hw.ofReal_ne_zero _
  · refine continuous_iff_continuousAt.mpr fun p => ?_
    have him : |((x p e : ℂ) + (b e : ℂ) * I).im| ≤ W := by simpa using hb e
    have hc : Continuous fun p => (x p e : ℂ) + (b e : ℂ) * I :=
      (Complex.continuous_ofReal.comp ((continuous_apply e).comp hx)).add continuous_const
    exact ContinuousAt.comp (g := w) (hw.analyticAt _ him).continuousAt hc.continuousAt
  · exact hw.continuous_ofReal.comp (continuous_apply e |>.comp hx)

omit [Fintype V] [DecidableEq V] in
/-- `∏_e w(x_e) · R_b(x) = ∏_e w(x_e + i b_e)` (the weight cancels). -/
theorem prod_mul_edgeRatio (hw : IsStripWeight w W c) (b x : E → ℝ) :
    (∏ e, w (x e)) * edgeRatio w b x = ∏ e, w ((x e : ℂ) + (b e : ℂ) * I) := by
  unfold edgeRatio
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e _ => mul_div_cancel₀ _ (hw.ofReal_ne_zero _)

/-! ## The Lebesgue identity -/

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- The complexification of a real-linear gradient along a complex line `φ + z â`. -/
lemma linear_re_im (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (φ â : V → ℝ) (z : ℂ) (e : E) :
    ((D (fun j => ((φ j : ℂ) + z * (â j : ℂ)).re) e : ℝ) : ℂ) +
        ((D (fun j => ((φ j : ℂ) + z * (â j : ℂ)).im) e : ℝ) : ℂ) * I =
      (D φ e : ℂ) + z * (D â e : ℂ) := by
  have hre : (fun j => ((φ j : ℂ) + z * (â j : ℂ)).re) = φ + z.re • â := by
    funext j; simp
  have him : (fun j => ((φ j : ℂ) + z * (â j : ℂ)).im) = z.im • â := by
    funext j; simp
  rw [hre, him, map_add, map_smul, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]
  apply Complex.ext <;> simp

/-- **The Lebesgue form of the character translation.** For a strip weight `w`, a real-linear
gradient `D` with offsets `r`, a bounded measurable factor `h ≥ 0` invariant along `a`, and a
translation `a` with `|D a| ≤ W` (and `D a ≠ 0` unless `a = 0`), if the density
`h ∏_e w(Dφ + r)` is integrable then
`∫ ρ χ_τ = e^{-⟨a, τ⟩} ∫ ρ χ_τ R_{Da}(Dφ + r)`. -/
theorem integral_density_mul_character_translate (hw : IsStripWeight w W c)
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (r : E → ℝ) (h : (V → ℝ) → ℝ) (hh_meas : Measurable h)
    (hh0 : ∀ φ, 0 ≤ h φ) (hh1 : ∀ φ, h φ ≤ 1) (τ a : V → ℝ) (haW : ∀ e, |D a e| ≤ W)
    (hinv : ∀ (φ : V → ℝ) (s : ℝ), h (φ + s • a) = h φ) (hedge : a ≠ 0 → ∃ e, D a e ≠ 0)
    (hint : Integrable fun φ => h φ * ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re) :
    ∫ φ, ((h φ * ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re : ℝ) : ℂ) * gffCharacter τ φ =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, ((h φ * ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re : ℝ) : ℂ) *
          (gffCharacter τ φ * edgeRatio w (D a) (D φ + r)) := by
  classical
  set ρ : (V → ℝ) → ℝ := fun φ => h φ * ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re with hρ
  -- the weight is real on the axis
  have hreal : ∀ φ : V → ℝ, ((ρ φ : ℝ) : ℂ) = (h φ : ℂ) * ∏ e, w ((D φ + r) e) := by
    intro φ
    simp only [hρ, Complex.ofReal_mul, Complex.ofReal_prod, Pi.add_apply]
    congr 1
    exact Finset.prod_congr rfl fun e _ => (hw.ofReal_eq _).symm
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, Complex.ofReal_zero,
      neg_zero, Complex.exp_zero, one_mul]
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
      ∏ e, w (((D (fun j => (ζ j).re) e + r e : ℝ) : ℂ) +
        ((D (fun j => (ζ j).im) e : ℝ) : ℂ) * I) with hF
  -- `F` along the complex line `φ + z â`
  have hline : ∀ (φ : V → ℝ) (z : ℂ), F (fun j => (φ j : ℂ) + z * ((a j / a j₀ : ℝ) : ℂ)) =
      Complex.exp (I * ∑ j, ((φ j : ℂ) + z * (â j : ℂ)) * (τ j : ℂ)) * (h φ : ℂ) *
        ∏ e, w (((D φ e + r e : ℝ) : ℂ) + z * (D â e : ℂ)) := by
    intro φ z
    simp only [hF, hâj]
    have hh : (h fun j => ((φ j : ℂ) + z * (â j : ℂ)).re) = h φ := by
      have : (fun j => ((φ j : ℂ) + z * (â j : ℂ)).re) =
          φ + (z.re / a j₀) • a := by
        funext j
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          mul_zero, sub_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hâj]
        ring
      rw [this, hinv]
    rw [hh]
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun e _ => ?_)
    congr 1
    have := linear_re_im D φ â z e
    push_cast at this ⊢
    linear_combination this
  -- the real and the translated integrands
  have hF₀ : ∀ φ : V → ℝ, F (fun j => (φ j : ℂ)) = ((ρ φ : ℝ) : ℂ) * gffCharacter τ φ := by
    intro φ
    simp only [hF, Complex.ofReal_re, Complex.ofReal_im, hreal, gffCharacter]
    have h0 : (D fun _ => (0 : ℝ)) = 0 := map_zero D
    simp only [show (fun j : V => φ j) = φ from rfl, h0, Pi.zero_apply, Complex.ofReal_zero,
      zero_mul, add_zero, Pi.add_apply]
    ring
  have hF₁ : ∀ φ : V → ℝ, F (fun j => (φ j : ℂ) + (a j : ℂ) * I) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
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
    rw [hexp]
    have hprod' : ∏ e, w (((D φ e + r e : ℝ) : ℂ) + ((D a e : ℝ) : ℂ) * I) =
        (∏ e, w ((D φ + r) e)) * edgeRatio w (D a) (D φ + r) := by
      rw [hprod]; simp only [Pi.add_apply]
    rw [hprod']
    ring
  -- bounds
  obtain ⟨M, hM⟩ := hw.bounded
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0 (by simpa using hw.width_nonneg))
  obtain ⟨B, hB, hBlim, hBdom⟩ := hw.majorant
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
    refine DifferentiableAt.mul (DifferentiableAt.mul (by fun_prop) (differentiableAt_const _))
      (DifferentiableAt.fun_finsetProd fun e _ => ?_)
    have him : |(((D φ e + r e : ℝ) : ℂ) + z * (D â e : ℂ)).im| ≤ W := by
      simpa [mul_comm] using hstrip z.im e hz
    exact ((hw.analyticAt _ him).differentiableAt).comp z (by fun_prop)
  have hdom : ∀ φ : V → ℝ, ∃ B' : ℝ → ℝ, Integrable B' ∧ Tendsto B' (cocompact ℝ) (𝓝 0) ∧
      ∀ x y : ℝ, |y| ≤ |a j₀| →
        ‖F fun j => (φ j : ℂ) + ((x : ℂ) + y * I) * ((a j / a j₀ : ℝ) : ℂ)‖ ≤ B' x := by
    intro φ
    set K : ℝ := Real.exp (|a j₀| * |∑ j, â j * τ j|)
    set C : ℝ := ∏ e ∈ Finset.univ.erase e₁, M
    have hs : D â e₁ ≠ 0 := by rw [hDâ]; exact div_ne_zero he₁ hj₀
    refine ⟨fun x => K * C * B (D φ e₁ + r e₁ + x * D â e₁), ?_, ?_, ?_⟩
    · have h1 : Integrable fun x => B (x * D â e₁ + (D φ e₁ + r e₁)) :=
        (hB.comp_add_right (D φ e₁ + r e₁)).comp_mul_right' hs
      exact (h1.congr (Eventually.of_forall fun x => by simp only; ring_nf)).const_mul _
    · have hcont : Tendsto (fun x : ℝ => D φ e₁ + r e₁ + x * D â e₁) (cocompact ℝ)
          (cocompact ℝ) :=
        ((Homeomorph.mulRight₀ (D â e₁) hs).trans
          (Homeomorph.addLeft (D φ e₁ + r e₁))).isClosedEmbedding.tendsto_cocompact
      have := (hBlim.comp hcont).const_mul (K * C)
      simpa using this
    · intro x y hy
      rw [hline φ]
      have hz : ((x : ℂ) + y * I).im = y := by simp
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hh0 φ)]
      have hexp : ‖Complex.exp (I * ∑ j, ((φ j : ℂ) + ((x : ℂ) + y * I) * (â j : ℂ)) *
          (τ j : ℂ))‖ ≤ K := by
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
      have hprod : ‖∏ e, w (((D φ e + r e : ℝ) : ℂ) + ((x : ℂ) + y * I) * (D â e : ℂ))‖ ≤
          C * B (D φ e₁ + r e₁ + x * D â e₁) := by
        rw [norm_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e₁)]
        have hpt : ∀ e, ((D φ e + r e : ℝ) : ℂ) + ((x : ℂ) + y * I) * (D â e : ℂ) =
            ((D φ e + r e + x * D â e : ℝ) : ℂ) + ((y * D â e : ℝ) : ℂ) * I := by
          intro e; push_cast; ring
        rw [hpt e₁, mul_comm C]
        refine mul_le_mul (hBdom _ _ (hstrip y e₁ hy)) ?_
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) ((norm_nonneg _).trans
            (hBdom _ _ (hstrip y e₁ hy)))
        exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun e _ => by
          rw [hpt e]; exact hM _ _ (hstrip y e hy)
      have hC : 0 ≤ C := Finset.prod_nonneg fun _ _ => hM0
      calc ‖Complex.exp (I * ∑ j, ((φ j : ℂ) + ((x : ℂ) + y * I) * (â j : ℂ)) * (τ j : ℂ))‖ *
            h φ * ‖∏ e, w (((D φ e + r e : ℝ) : ℂ) + ((x : ℂ) + y * I) * (D â e : ℂ))‖
          ≤ K * 1 * (C * B (D φ e₁ + r e₁ + x * D â e₁)) :=
            mul_le_mul (mul_le_mul hexp (hh1 φ) (hh0 φ) (Real.exp_pos _).le) hprod
              (norm_nonneg _) (by positivity)
        _ = K * C * B (D φ e₁ + r e₁ + x * D â e₁) := by ring
  -- integrability
  have hmeas_char : Continuous (gffCharacter τ) := Reduction.continuous_gffCharacter τ
  have hρ_meas : Measurable ρ := by
    refine hh_meas.mul (continuous_finsetProd _ fun e _ => ?_).measurable
    exact Complex.continuous_re.comp (hw.continuous_ofReal.comp
      ((continuous_apply e).comp ((LinearMap.continuous_of_finiteDimensional D).add
        continuous_const)))
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

/-! ## The two edge laws -/

omit [DecidableEq V] in
/-- A density of finite mass is integrable. -/
theorem integrable_of_densityMass_ne_top {ρ : (V → ℝ) → ℝ} (hρ0 : ∀ φ, 0 ≤ ρ φ)
    (hρm : Measurable ρ) (hZ : densityMass ρ ≠ ⊤) : Integrable ρ :=
  ⟨hρm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hρ0)).mpr
    (lt_top_iff_ne_top.mpr hZ)⟩

/-- The character translation of a normalized density `h ∏_e w(Dφ + r)` reduces to the Lebesgue
identity; the case of infinite mass is trivial. -/
theorem translate_densityLaw (hw : IsStripWeight w W c) (D : (V → ℝ) →ₗ[ℝ] (E → ℝ))
    (r : E → ℝ) (h : (V → ℝ) → ℝ) (hh_meas : Measurable h) (hh0 : ∀ φ, 0 ≤ h φ)
    (hh1 : ∀ φ, h φ ≤ 1) (τ a : V → ℝ) (haW : ∀ e, |D a e| ≤ W)
    (hinv : ∀ (φ : V → ℝ) (s : ℝ), h (φ + s • a) = h φ) (hedge : a ≠ 0 → ∃ e, D a e ≠ 0) :
    ∫ φ, gffCharacter τ φ ∂densityLaw (fun φ => h φ * ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re) =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, gffCharacter τ φ * edgeRatio w (D a) (D φ + r)
          ∂densityLaw (fun φ => h φ * ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re) := by
  set ρ : (V → ℝ) → ℝ := fun φ => h φ * ∏ e, (w ((D φ e + r e : ℝ) : ℂ)).re with hρ
  have hρ0 : ∀ φ, 0 ≤ ρ φ := fun φ =>
    mul_nonneg (hh0 φ) (Finset.prod_nonneg fun _ _ => (hw.ofReal_re_pos _).le)
  have hρm : Measurable ρ := by
    refine hh_meas.mul (continuous_finsetProd _ fun e _ => ?_).measurable
    exact Complex.continuous_re.comp (hw.continuous_ofReal.comp
      ((continuous_apply e).comp ((LinearMap.continuous_of_finiteDimensional D).add
        continuous_const)))
  rw [integral_densityLaw hρ0 hρm, integral_densityLaw hρ0 hρm]
  by_cases hZ : densityMass ρ = ⊤
  · simp [hZ]
  rw [integral_density_mul_character_translate hw D r h hh_meas hh0 hh1 τ a haW hinv hedge
    (integrable_of_densityMass_ne_top hρ0 hρm hZ)]
  ring

omit [DecidableEq V] in
/-- The character-translation integrand is bounded and continuous, hence integrable against any
normalized density. -/
theorem integrable_character_mul_edgeRatio (hw : IsStripWeight w W c)
    (D : (V → ℝ) →ₗ[ℝ] (E → ℝ)) (r : E → ℝ) (ρ : (V → ℝ) → ℝ) (τ a : V → ℝ)
    (haW : ∀ e, |D a e| ≤ W) :
    Integrable (fun φ => gffCharacter τ φ * edgeRatio w (D a) (D φ + r)) (densityLaw ρ) := by
  refine integrable_densityLaw_of_bound ρ ?_ (M := Real.exp (∑ e, c (D a e))) fun φ => ?_
  · exact ((Reduction.continuous_gffCharacter τ).mul (continuous_edgeRatio hw (D a) haW
      ((LinearMap.continuous_of_finiteDimensional D).add continuous_const))).aestronglyMeasurable
  · rw [norm_mul, Reduction.norm_gffCharacter, one_mul]
    exact norm_edgeRatio_le hw _ _ haW


theorem characterTranslation_edgeLaw (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) (v : V) :
    CharacterTranslation (edgeLaw G w v) (gradLinear G) w 0 W := by
  set h : (V → ℝ) → ℝ := fun φ => (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v) with hh
  have hlaw : edgeLaw G w v =
      densityLaw (fun φ => h φ * ∏ e, (w ((gradLinear G φ e + (0 : E → ℝ) e : ℝ) : ℂ)).re) := by
    rw [edgeLaw_eq_densityLaw]
    congr 1
    funext φ
    simp only [edgeDensity, gradLinear_apply, Pi.zero_apply, add_zero, hh]
    ring
  have hh_meas : Measurable h :=
    (measurable_const.indicator measurableSet_Ico).comp (measurable_pi_apply v)
  have hh0 : ∀ φ, 0 ≤ h φ := fun φ => by
    simp only [hh]; by_cases hφ : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hφ]
  have hh1 : ∀ φ, h φ ≤ 1 := fun φ => by
    simp only [hh]; by_cases hφ : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [hφ]
  rw [hlaw]
  refine ⟨fun τ a _ haW => integrable_character_mul_edgeRatio hw _ _ _ τ a haW,
    fun τ a hτ haW => ?_⟩
  -- replace `a` by `a - a(v)`, which fixes the root and changes neither `∇a` nor `⟨a, τ⟩`
  set a' : V → ℝ := fun j => a j - a v with ha'
  have hDa' : gradLinear G a' = gradLinear G a := by
    funext e
    simp only [gradLinear_apply, Multigraph.grad, ha']
    ring
  have hpair : ∑ j, a' j * τ j = ∑ j, a j * τ j := by
    simp only [ha', sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hτ, mul_zero, sub_zero]
  rw [← hDa', ← hpair]
  have haW' : ∀ e, |gradLinear G a' e| ≤ W := by rw [hDa']; exact haW
  have hinv : ∀ (φ : V → ℝ) (s : ℝ), h (φ + s • a') = h φ := by
    intro φ s
    simp only [hh, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha', sub_self, mul_zero, add_zero]
  have hedge : a' ≠ 0 → ∃ e, gradLinear G a' e ≠ 0 := by
    intro ha0
    by_contra hc
    push Not at hc
    have hE : G.energy a' = 0 := by
      simp only [Multigraph.energy]
      exact Finset.sum_eq_zero fun e _ => by rw [← gradLinear_apply, hc e]; ring
    obtain ⟨k, hk⟩ := (Multigraph.energy_eq_zero_iff_exists_const G hG a').mp hE
    have hk0 : k = 0 := by
      have := congrFun hk v
      simp only [ha', sub_self] at this
      exact this.symm
    exact ha0 (by rw [hk, hk0]; rfl)
  exact translate_densityLaw hw (gradLinear G) 0 h hh_meas hh0 hh1 τ a' haW' hinv hedge

/-- **The pinned edge law admits character translations**, on an anchored pinned graph (a field
with zero linear gradient vanishes), for every character. -/
theorem characterTranslation_pinnedEdgeLaw (G : PinnedGraph V E)
    (hanchor : ∀ a : V → ℝ, pinnedGradLinear G a = 0 → a = 0)
    {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c) :
    CharacterTranslation (pinnedEdgeLaw G w) (pinnedGradLinear G) w (pinOffset G) W := by
  have hlaw : pinnedEdgeLaw G w = densityLaw (fun φ => (fun _ => (1 : ℝ)) φ *
      ∏ e, (w ((pinnedGradLinear G φ e + pinOffset G e : ℝ) : ℂ)).re) := by
    rw [pinnedEdgeLaw_eq_densityLaw]
    congr 1
    funext φ
    simp only [pinnedEdgeDensity, one_mul, realGrad_eq, Pi.add_apply]
  rw [hlaw]
  refine ⟨fun τ a _ haW => integrable_character_mul_edgeRatio hw _ _ _ τ a haW,
    fun τ a _ haW => ?_⟩
  refine translate_densityLaw hw (pinnedGradLinear G) (pinOffset G) (fun _ => 1)
    measurable_const (fun _ => zero_le_one) (fun _ => le_rfl) τ a haW (fun _ _ => rfl) ?_
  intro ha0
  by_contra hc
  push Not at hc
  exact ha0 (hanchor a (funext hc))

/-- **The generic translation step on the rooted edge law** (KP (2.18)–(2.20); FS81 Theorem 6.1,
(6.18)): `integral_prod_add_mul_cos_eq_localFactor` at `edgeLaw G w v` for a strip weight `w`. -/
theorem edgeLaw_integral_prod_add_mul_cos_eq_localFactor (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
    (hw : IsStripWeight w W c) (v : V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ϱ : ι → V → ℝ) (hneutral : ∀ i, ∑ j, ϱ i j = 0) (A B s : ι → ℝ) (a : ι → V → ℝ)
    (horth : ∀ i i', i ≠ i' → ∑ j, a i j * ϱ i' j = 0)
    (hdisj : ∀ i i', i ≠ i' → ∀ e, G.grad (a i) e = 0 ∨ G.grad (a i') e = 0)
    (hW : ∀ i e, |G.grad (a i) e| ≤ W) :
    ∫ φ, ((∏ i, (A i + B i * Real.cos (∑ j, φ j * ϱ i j + s i)) : ℝ) : ℂ) ∂edgeLaw G w v =
      ∫ φ, ∏ i, ((A i : ℂ) +
        ((B i * Real.exp (-translationEnergy c (gradLinear G) (a i) (ϱ i)) : ℝ) : ℂ) *
          localFactor w c (gradLinear G (a i)) (gradLinear G φ + 0) (∑ j, φ j * ϱ i j + s i))
            ∂edgeLaw G w v := by
  have : IsFiniteMeasure (edgeLaw G w v) := by rw [edgeLaw_eq_densityLaw]; infer_instance
  exact integral_prod_add_mul_cos_eq_localFactor _ (gradLinear G) w c hw.cost_even 0
    hw.width_nonneg (characterTranslation_edgeLaw G hG hw v) hw.ofReal_ne_zero ϱ hneutral A B s a
    horth hdisj hW

end FroehlichSpencer.BKT.Generic

end
