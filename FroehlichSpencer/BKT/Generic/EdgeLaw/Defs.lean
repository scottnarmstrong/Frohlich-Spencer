/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.StripWeight
public import FroehlichSpencer.BKT.Generic.GaussianInstance
public import FroehlichSpencer.BKT.Rotator.Contour.Box

/-!
# Edge-product laws (generic core)

* `edgeLaw G w v`: KP's rooted law `gffLaw` (`Surface/GFFLaw.lean`) with the Gaussian bond weight
  replaced by a strip weight `w`: density `∏_e w(∇φ(e))` on a finite multigraph, with the root
  phase `φ(v)` in `[-π, π)`, normalized by its total mass;
* `pinnedEdgeLaw G w`: the finite pinned law on a `Rotator.Contour.PinnedGraph`, density
  `∏_e w(∇φ(e))` with the exterior values `pin`, normalized.

Both are `densityLaw ρ` for a nonnegative density `ρ` (`edgeLaw_eq_densityLaw`,
`pinnedEdgeLaw_eq_densityLaw`).

`densityLaw ρ` is always a finite measure, and its integrals are
`Z⁻¹ ∫ ρ f dφ` with `Z = ∫ ρ` (`integral_densityLaw`); when `Z = ∞` both sides vanish.

The pinned
gradient splits as a linear part plus the real exterior offsets (`realGrad_eq`), which is the
form `D φ + r` of `CharacterTranslation`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Rotator.Contour (PinnedGraph)

variable {V : Type*} [Fintype V]

/-! ## Normalized density measures -/

/-- The probability measure (when normalizable) with density `ρ` with respect to Lebesgue measure on
`V → ℝ`: `(∫ ρ)⁻¹ ρ(φ) dφ`. -/
def densityLaw (ρ : (V → ℝ) → ℝ) : Measure (V → ℝ) :=
  let μ : Measure (V → ℝ) := (Measure.pi fun _ : V => (volume : Measure ℝ)).withDensity fun φ =>
    ENNReal.ofReal (ρ φ)
  (μ Set.univ)⁻¹ • μ

/-- The total mass `∫⁻ ρ` of the unnormalized density measure. -/
def densityMass (ρ : (V → ℝ) → ℝ) : ENNReal := ∫⁻ φ, ENNReal.ofReal (ρ φ)

lemma withDensity_univ (ρ : (V → ℝ) → ℝ) :
    ((Measure.pi fun _ : V => (volume : Measure ℝ)).withDensity fun φ => ENNReal.ofReal (ρ φ))
      Set.univ = densityMass ρ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, densityMass, volume_pi]

/-- A normalized density measure is always finite (it is zero when the mass is `0` or `∞`). -/
instance isFiniteMeasure_densityLaw (ρ : (V → ℝ) → ℝ) : IsFiniteMeasure (densityLaw ρ) := by
  refine ⟨?_⟩
  simp only [densityLaw, Measure.smul_apply, smul_eq_mul, withDensity_univ]
  rcases eq_or_ne (densityMass ρ) 0 with h | h
  · rw [h, mul_zero]; exact ENNReal.zero_lt_top
  rcases eq_or_ne (densityMass ρ) ⊤ with h' | h'
  · rw [h', ENNReal.inv_top, zero_mul]; exact ENNReal.zero_lt_top
  rw [ENNReal.inv_mul_cancel h h']; exact ENNReal.one_lt_top

/-- A density of positive finite mass gives a probability measure. -/
theorem isProbabilityMeasure_densityLaw {ρ : (V → ℝ) → ℝ} (h0 : densityMass ρ ≠ 0)
    (htop : densityMass ρ ≠ ⊤) : IsProbabilityMeasure (densityLaw ρ) := by
  refine ⟨?_⟩
  simp only [densityLaw, Measure.smul_apply, smul_eq_mul, withDensity_univ]
  exact ENNReal.inv_mul_cancel h0 htop

/-- Integrals against `densityLaw ρ`: `∫ f = Z⁻¹ ∫ ρ f dφ`, `Z = densityMass ρ` (also when
`Z ∈ {0, ∞}`, where both sides vanish). -/
theorem integral_densityLaw {ρ : (V → ℝ) → ℝ} (hρ : ∀ φ, 0 ≤ ρ φ) (hmeas : Measurable ρ)
    (f : (V → ℝ) → ℂ) :
    ∫ φ, f φ ∂densityLaw ρ = ((densityMass ρ)⁻¹.toReal : ℂ) * ∫ φ, (ρ φ : ℂ) * f φ := by
  simp only [densityLaw, withDensity_univ]
  rw [integral_smul_measure]
  have hw : (fun φ => ENNReal.ofReal (ρ φ)) = fun φ => ((Real.toNNReal (ρ φ) : NNReal) : ENNReal) :=
    rfl
  rw [hw, integral_withDensity_eq_integral_smul hmeas.real_toNNReal, ← volume_pi,
    Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hρ φ), Complex.real_smul]

/-- A bounded measurable function is integrable against `densityLaw ρ`. -/
theorem integrable_densityLaw_of_bound (ρ : (V → ℝ) → ℝ) {f : (V → ℝ) → ℂ}
    (hf : AEStronglyMeasurable f (densityLaw ρ)) {M : ℝ} (hM : ∀ φ, ‖f φ‖ ≤ M) :
    Integrable f (densityLaw ρ) :=
  Integrable.of_bound hf M (Filter.Eventually.of_forall hM)

/-! ## The rooted edge law -/

variable {E : Type*} [Fintype E]

/-- The density `∏_e w(∇φ(e)) · 𝟙_{[-π, π)}(φ(v))` of the rooted edge law. -/
def edgeDensity (G : Multigraph V E) (w : ℂ → ℂ) (v : V) (φ : V → ℝ) : ℝ :=
  (∏ e, (w ((G.grad φ e : ℝ) : ℂ)).re) * (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v)

/-- KP's rooted law `gffLaw` with the Gaussian bond weight replaced by `w`: density
`∏_e w(∇φ(e))` with the root phase in `[-π, π)`, normalized. -/
def edgeLaw (G : Multigraph V E) (w : ℂ → ℂ) (v : V) : Measure (V → ℝ) :=
  let μ : Measure (V → ℝ) := (Measure.pi fun _ : V => (volume : Measure ℝ)).withDensity fun φ =>
    ENNReal.ofReal ((∏ e, (w ((G.grad φ e : ℝ) : ℂ)).re) *
      (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v))
  (μ Set.univ)⁻¹ • μ

theorem edgeLaw_eq_densityLaw (G : Multigraph V E) (w : ℂ → ℂ) (v : V) :
    edgeLaw G w v = densityLaw (edgeDensity G w v) := rfl

/-! ## The pinned edge law -/

/-- The linear part `φ(head e) - φ(tail e)` (zero for an exterior tail) of a pinned gradient. -/
def pinnedGradLinear (G : PinnedGraph V E) : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun φ e := φ (G.head e) - (G.tail e).elim 0 φ
  map_add' φ ψ := by
    funext e
    simp only [Pi.add_apply]
    rcases G.tail e with _ | k
    · simp only [Option.elim_none]; ring
    · simp only [Option.elim_some, Pi.add_apply]; ring
  map_smul' t φ := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rcases G.tail e with _ | k
    · simp only [Option.elim_none]; ring
    · simp only [Option.elim_some, Pi.smul_apply, smul_eq_mul]; ring

/-- The exterior offset `-pin(e)` of a boundary edge (zero for an interior edge). -/
def pinOffset (G : PinnedGraph V E) (e : E) : ℝ :=
  -(G.tail e).elim (G.pin e) fun _ => 0

omit [Fintype V] [Fintype E] in
/-- The pinned gradient is its linear part plus the exterior offsets. -/
theorem realGrad_eq (G : PinnedGraph V E) (φ : V → ℝ) :
    G.realGrad φ = pinnedGradLinear G φ + pinOffset G := by
  funext e
  simp only [PinnedGraph.realGrad, pinnedGradLinear, pinOffset, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.add_apply]
  rcases G.tail e with _ | k
  · simp only [Option.elim_none]; ring
  · simp only [Option.elim_some]; ring

/-- The density `∏_e w(∇φ(e))` of the pinned edge law. -/
def pinnedEdgeDensity (G : PinnedGraph V E) (w : ℂ → ℂ) (φ : V → ℝ) : ℝ :=
  ∏ e, (w ((G.realGrad φ e : ℝ) : ℂ)).re

/-- The finite pinned law: density `∏_e w(∇φ(e))` with exterior values `pin`, normalized. -/
def pinnedEdgeLaw (G : PinnedGraph V E) (w : ℂ → ℂ) : Measure (V → ℝ) :=
  let μ : Measure (V → ℝ) := (Measure.pi fun _ : V => (volume : Measure ℝ)).withDensity fun φ =>
    ENNReal.ofReal (∏ e, (w ((G.realGrad φ e : ℝ) : ℂ)).re)
  (μ Set.univ)⁻¹ • μ

theorem pinnedEdgeLaw_eq_densityLaw (G : PinnedGraph V E) (w : ℂ → ℂ) :
    pinnedEdgeLaw G w = densityLaw (pinnedEdgeDensity G w) := rfl

/-! ## Elementary facts about the densities -/

namespace IsStripWeight

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- A strip weight is continuous on the real axis. -/
theorem continuous_ofReal (hw : IsStripWeight w W c) : Continuous fun x : ℝ => w x :=
  continuous_iff_continuousAt.mpr fun x =>
    ((hw.analyticAt x (by simpa using hw.width_nonneg)).continuousAt).comp
      Complex.continuous_ofReal.continuousAt

/-- The real part of a strip weight is positive and at most the bound `M` (with `M ≥ 0`). -/
theorem exists_re_le (hw : IsStripWeight w W c) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, (w x).re ≤ M := by
  obtain ⟨M, hM⟩ := hw.bounded
  have h0 := hM 0 0 (by simpa using hw.width_nonneg)
  refine ⟨M, (norm_nonneg _).trans h0, fun x => ?_⟩
  have := hM x 0 (by simpa using hw.width_nonneg)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
  exact (Complex.re_le_norm _).trans this

end IsStripWeight

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

omit [Fintype V] in
theorem edgeDensity_nonneg (G : Multigraph V E) (hw : IsStripWeight w W c) (v : V)
    (φ : V → ℝ) : 0 ≤ edgeDensity G w v φ := by
  unfold edgeDensity
  refine mul_nonneg (Finset.prod_nonneg fun e _ => (hw.ofReal_re_pos _).le) ?_
  by_cases h : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [h]

theorem measurable_edgeDensity (G : Multigraph V E) (hw : IsStripWeight w W c) (v : V) :
    Measurable (edgeDensity G w v) := by
  unfold edgeDensity
  refine Measurable.mul ?_ ?_
  · refine (continuous_finsetProd _ fun e _ => ?_).measurable
    have hg : Continuous fun φ : V → ℝ => G.grad φ e := by
      unfold Multigraph.grad; fun_prop
    exact Complex.continuous_re.comp (hw.continuous_ofReal.comp hg)
  · exact (measurable_const.indicator measurableSet_Ico).comp (measurable_pi_apply v)

omit [Fintype V] in
theorem pinnedEdgeDensity_nonneg (G : PinnedGraph V E) (hw : IsStripWeight w W c)
    (φ : V → ℝ) : 0 ≤ pinnedEdgeDensity G w φ :=
  Finset.prod_nonneg fun _ _ => (hw.ofReal_re_pos _).le

theorem measurable_pinnedEdgeDensity (G : PinnedGraph V E) (hw : IsStripWeight w W c) :
    Measurable (pinnedEdgeDensity G w) := by
  unfold pinnedEdgeDensity
  refine (continuous_finsetProd _ fun e _ => ?_).measurable
  have hg : Continuous fun φ : V → ℝ => G.realGrad φ e := by
    unfold PinnedGraph.realGrad
    cases G.tail e <;> · simp only [Option.elim_none, Option.elim_some]; fun_prop
  exact Complex.continuous_re.comp (hw.continuous_ofReal.comp hg)

end FroehlichSpencer.BKT.Generic

end
