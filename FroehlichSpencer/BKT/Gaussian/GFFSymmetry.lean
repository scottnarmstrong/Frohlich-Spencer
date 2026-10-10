/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.GFFLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Evenness of the GFF law

KP (1.3), p. 2: the density of the Gaussian free field is even in `φ`, because the energy
`∑ (φ j - φ ℓ)²` is.

The only asymmetry is the pinning window `[-π, π)` at the root `v`, which
`φ ↦ -φ` maps to `(-π, π]`; the two differ by the null set `{φ v = π} ∪ {φ v = -π}`.

Hence the `gffLaw` is invariant under `φ ↦ -φ` (`gffLaw_map_neg`) and integrals against it
are invariant under `φ ↦ -φ` (`integral_comp_neg_gffLaw`).
-/

open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.BKT

variable {V : Type*} {E : Type*} [Fintype V] [Fintype E]

/-- Product Lebesgue measure on `V → ℝ` is invariant under negation. -/
theorem pi_volume_map_neg :
    (Measure.pi fun _ : V => (volume : Measure ℝ)).map (fun φ => -φ) =
      Measure.pi fun _ : V => (volume : Measure ℝ) := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_neg (MeasurableSet.univ_pi hs)]
  have h : (fun φ : V → ℝ => -φ) ⁻¹' Set.univ.pi s = Set.univ.pi fun i => -s i := by
    ext φ; simp [Set.mem_pi]
  rw [h, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : -s i = (fun x : ℝ => (-1 : ℝ) • x) ⁻¹' s i := by ext x; simp
  rw [e, Measure.addHaar_preimage_smul volume (by norm_num)]
  simp

/-- A coordinate hyperplane is null for product Lebesgue measure. -/
theorem pi_volume_coord_eq_null (v : V) (c : ℝ) :
    (Measure.pi fun _ : V => (volume : Measure ℝ)) {φ : V → ℝ | φ v = c} = 0 := by
  classical
  have h : {φ : V → ℝ | φ v = c} =
      Set.univ.pi (Function.update (fun _ : V => (Set.univ : Set ℝ)) v {c}) := by
    ext φ
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      by_cases hi : i = v
      · subst hi; simp [h]
      · simp [hi]
    · intro h; simpa using h v
  rw [h, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp)

/-- The unnormalized GFF density is even, up to the null set `{φ v = ±π}`. -/
theorem gffDensity_comp_neg_ae (G : Multigraph V E) (β : ℝ) (v : V) :
    (fun φ : V → ℝ => ENNReal.ofReal (Real.exp (-(β / 2) * ∑ e, ((-φ) (G.src e) -
        (-φ) (G.tgt e)) ^ 2) * (Set.Ico (-Real.pi) Real.pi).indicator 1 ((-φ) v))) =ᵐ[
      Measure.pi fun _ : V => (volume : Measure ℝ)]
    fun φ => ENNReal.ofReal (Real.exp (-(β / 2) * ∑ e, (φ (G.src e) - φ (G.tgt e)) ^ 2) *
        (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v)) := by
  have hnull : (Measure.pi fun _ : V => (volume : Measure ℝ))
      ({φ : V → ℝ | φ v = Real.pi} ∪ {φ : V → ℝ | φ v = -Real.pi}) = 0 :=
    measure_union_null (pi_volume_coord_eq_null v _) (pi_volume_coord_eq_null v _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with φ hφ
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hφ
  have hind : (Set.Ico (-Real.pi) Real.pi).indicator (1 : ℝ → ℝ) ((-φ) v) =
      (Set.Ico (-Real.pi) Real.pi).indicator (1 : ℝ → ℝ) (φ v) := by
    have hmem : (-φ) v ∈ Set.Ico (-Real.pi) Real.pi ↔ φ v ∈ Set.Ico (-Real.pi) Real.pi := by
      simp only [Set.mem_Ico, Pi.neg_apply]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, lt_of_le_of_ne (by linarith) hφ.1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, lt_of_le_of_ne (by linarith) (by intro h; apply hφ.2; linarith)⟩
    by_cases h : φ v ∈ Set.Ico (-Real.pi) Real.pi
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mpr h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.mp h'))]
  have hen : ∑ e, ((-φ) (G.src e) - (-φ) (G.tgt e)) ^ 2 =
      ∑ e, (φ (G.src e) - φ (G.tgt e)) ^ 2 :=
    Finset.sum_congr rfl fun e _ => by simp only [Pi.neg_apply]; ring
  simp only [hind, hen]

/--
The GFF law is invariant under `φ ↦ -φ`.
-/
theorem gffLaw_map_neg (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ)
    (hβ : 0 < β) (v : V) :
    (gffLaw G hG β hβ v).map (fun φ => -φ) = gffLaw G hG β hβ v := by
  unfold gffLaw
  simp only
  rw [Measure.map_smul _ measurable_neg.aemeasurable]
  congr 1
  set μ : Measure (V → ℝ) := Measure.pi fun _ : V => (volume : Measure ℝ) with hμ
  set f : (V → ℝ) → ENNReal := fun φ =>
    ENNReal.ofReal (Real.exp (-(β / 2) * ∑ e, (φ (G.src e) - φ (G.tgt e)) ^ 2) *
      (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ v)) with hf
  have hae : (fun φ => f (-φ)) =ᵐ[μ] f := gffDensity_comp_neg_ae G β v
  have hemb : MeasurableEmbedding (fun φ : V → ℝ => -φ) :=
    (MeasurableEquiv.neg (V → ℝ)).measurableEmbedding
  ext s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_neg hs),
    ← lintegral_indicator hs]
  have h1 : (fun x : V → ℝ => ((fun φ : V → ℝ => -φ) ⁻¹' s).indicator f x) =
      fun x => (s.indicator fun φ => f (-φ)) (-x) := by
    ext x
    by_cases hx : -x ∈ s
    · rw [Set.indicator_of_mem hx (fun φ => f (-φ)), neg_neg]
      exact Set.indicator_of_mem (show x ∈ (fun φ : V → ℝ => -φ) ⁻¹' s from hx) f
    · rw [Set.indicator_of_notMem hx (fun φ => f (-φ))]
      exact Set.indicator_of_notMem (show x ∉ (fun φ : V → ℝ => -φ) ⁻¹' s from hx) f
  rw [h1, ← hemb.lintegral_map (μ := μ)]
  rw [show μ.map (fun φ : V → ℝ => -φ) = μ from pi_volume_map_neg]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with φ hφ
  by_cases hs' : φ ∈ s
  · simp [Set.indicator_of_mem hs', hφ]
  · simp [Set.indicator_of_notMem hs']

/--
Integrals against the GFF law are invariant under `φ ↦ -φ`.
-/
theorem integral_comp_neg_gffLaw (G : Multigraph V E) (hG : G.toSimpleGraph.Connected)
    (β : ℝ) (hβ : 0 < β) (v : V) (g : (V → ℝ) → ℝ) :
    ∫ φ, g (-φ) ∂gffLaw G hG β hβ v = ∫ φ, g φ ∂gffLaw G hG β hβ v := by
  have h := integral_map_equiv (μ := gffLaw G hG β hβ v) (MeasurableEquiv.neg (V → ℝ)) g
  change ∫ y, g y ∂(gffLaw G hG β hβ v).map (fun φ => -φ) = _ at h
  rw [gffLaw_map_neg] at h
  exact h.symm

end FroehlichSpencer.BKT

end
