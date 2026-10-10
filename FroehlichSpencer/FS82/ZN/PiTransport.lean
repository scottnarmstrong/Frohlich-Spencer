/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.Convergence
import all FroehlichSpencer.FS82.ZN.Convergence
public import FroehlichSpencer.FS82.ZN.TorusIntegral

/-!
# transport of the pinned product measure

The pinning factor is a probability density on the circle (`znLinkMeasure`).

For a finite index
type `K`, the integral against `∏_k pin(θ_k)` is the integral against the product of the one-link
laws (`integral_pi_znLinkMeasure`).

Hence:

* `integral_pin_restrict`: for an injection `f : ι → κ`, a function of the coordinates in the
  range of `f` has the same pinned integral over `κ` as over `ι`; the extra variables integrate
  to one.
* `integral_flip`: a coordinatewise change of sign `θ_i ↦ ±θ_i` preserves the Haar integral.
* `znPinningFactor_neg`: the pinning factor is even.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

local instance piTransport_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance piTransport_measureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance piTransport_isAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The product of the one-link pinning laws has the product density. -/
theorem pi_znLinkMeasure_eq {K : Type*} [Fintype K] (N : ℕ) (h : NNReal) :
    Measure.pi (fun _ : K => znLinkMeasure N h) =
      (Measure.pi fun _ : K => (volume : Measure UnitAddCircle)).withDensity
        (fun θ => ((∏ k, znLinkDensityNN N h (θ k) : NNReal) : ENNReal)) := by
  have hsig : ∀ _ : K, SigmaFinite ((volume : Measure UnitAddCircle).withDensity
      (fun z => (znLinkDensityNN N h z : ENNReal))) := by
    intro _
    have : IsProbabilityMeasure ((volume : Measure UnitAddCircle).withDensity
        (fun z => (znLinkDensityNN N h z : ENNReal))) := znLinkMeasure_isProbabilityMeasure N h
    infer_instance
  exact measure_pi_withDensity_nnreal (fun _ : K => (volume : Measure UnitAddCircle))
    (fun _ => znLinkDensityNN N h)
    (fun _ => measurable_real_toNNReal.comp (continuous_znPinningFactor N h).measurable)

/-- The integral against the product of the one-link pinning laws. -/
theorem integral_pi_znLinkMeasure {K : Type*} [Fintype K] (N : ℕ) (h : NNReal)
    (F : (K → UnitAddCircle) → ℝ) :
    (∫ θ, F θ ∂(Measure.pi fun _ : K => znLinkMeasure N h)) =
      ∫ θ : K → UnitAddCircle, (∏ k, znPinningFactor N h (θ k)) * F θ := by
  classical
  have hmeas : Measurable fun θ : K → UnitAddCircle => (∏ k, znLinkDensityNN N h (θ k) : NNReal) :=
    Finset.measurable_prod Finset.univ fun k _ =>
      (measurable_real_toNNReal.comp (continuous_znPinningFactor N h).measurable).comp
        (measurable_pi_apply k)
  rw [pi_znLinkMeasure_eq, ← MeasureTheory.volume_pi,
    integral_withDensity_eq_integral_smul hmeas F]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  change ((∏ k, znLinkDensityNN N h (θ k) : NNReal) : ℝ) * F θ = _
  rw [NNReal.coe_prod]
  simp_rw [znLinkDensityNN_coe]

/-- Restriction to the coordinates in the range of an injection preserves a product of copies of
a probability measure. -/
theorem measurePreserving_comp_injective {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (f : ι → κ)
    (hf : Function.Injective f) :
    MeasurePreserving (fun x : κ → X => fun i => x (f i))
      (Measure.pi fun _ : κ => μ) (Measure.pi fun _ : ι => μ) := by
  classical
  have hmeas : Measurable fun x : κ → X => fun i => x (f i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (f i)
  refine ⟨hmeas, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  set t : κ → Set X := fun k => if h : ∃ i, f i = k then s (Classical.choose h) else Set.univ
    with ht
  have htf : ∀ i, t (f i) = s i := by
    intro i
    have h : ∃ j, f j = f i := ⟨i, rfl⟩
    rw [ht]
    simp only [dite_eq_left h]
    rw [hf (Classical.choose_spec h)]
  have hpre : (fun x : κ → X => fun i => x (f i)) ⁻¹' Set.pi Set.univ s = Set.pi Set.univ t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx k
      by_cases h : ∃ i, f i = k
      · obtain ⟨i, rfl⟩ := h
        rw [htf]
        exact hx i
      · rw [ht]
        simp [h]
    · intro hx i
      rw [← htf]
      exact hx (f i)
  rw [hpre, Measure.pi_pi]
  have hrest : ∀ k ∈ (Finset.univ : Finset κ), k ∉ Finset.univ.image f → μ (t k) = 1 := by
    intro k _ hk
    have h : ¬ ∃ i, f i = k := fun ⟨i, hi⟩ =>
      hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    rw [ht]
    simp [h]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image f)) hrest,
    Finset.prod_image fun i _ j _ hij => hf hij]
  exact Finset.prod_congr rfl fun i _ => by rw [htf]

/-- **Restriction of the pinned integral.** -/
theorem integral_pin_restrict {ι κ : Type*} [Fintype ι] [Fintype κ] (N : ℕ) (h : NNReal)
    (f : ι → κ) (hf : Function.Injective f) (G : (ι → UnitAddCircle) → ℝ) (hG : Continuous G) :
    ∫ θ : κ → UnitAddCircle, (∏ k, znPinningFactor N h (θ k)) * G (fun i => θ (f i)) =
      ∫ θ : ι → UnitAddCircle, (∏ i, znPinningFactor N h (θ i)) * G θ := by
  have := znLinkMeasure_isProbabilityMeasure N h
  have hmp := measurePreserving_comp_injective (znLinkMeasure N h) f hf
  rw [← integral_pi_znLinkMeasure N h (fun θ : κ → UnitAddCircle => G (fun i => θ (f i))),
    ← integral_pi_znLinkMeasure N h G, ← hmp.map_eq,
    integral_map hmp.measurable.aemeasurable hG.aestronglyMeasurable]

theorem znPinningFactor_neg (N : ℕ) (h : NNReal) (z : UnitAddCircle) :
    znPinningFactor N h (-z) = znPinningFactor N h z := by
  obtain ⟨x, rfl⟩ := Torus.exists_real_lift z
  unfold znPinningFactor
  rw [← AddCircle.coe_neg, circleCosCharacter_real, circleCosCharacter_real, mul_neg,
    Real.cos_neg]

theorem znPinningFactor_zsmul (N : ℕ) (h : NNReal) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (z : UnitAddCircle) : znPinningFactor N h (s • z) = znPinningFactor N h z := by
  rcases hs with rfl | rfl
  · rw [one_zsmul]
  · rw [neg_zsmul, one_zsmul, znPinningFactor_neg]

/-- A coordinatewise change of sign preserves the Haar integral. -/
theorem integral_flip {ι : Type*} [Fintype ι] (s : ι → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (F : (ι → UnitAddCircle) → ℝ) (hF : Continuous F) :
    ∫ θ : ι → UnitAddCircle, F (fun i => s i • θ i) = ∫ θ : ι → UnitAddCircle, F θ := by
  have hneg := Torus.volume_isNegInvariant
  have hcoord : ∀ i, MeasurePreserving (fun z : UnitAddCircle => s i • z) volume volume := by
    intro i
    rcases hs i with h | h
    · rw [h]
      have hid : (fun z : UnitAddCircle => (1 : ℤ) • z) = id := by
        funext z
        simp
      rw [hid]
      exact MeasurePreserving.id (volume : Measure UnitAddCircle)
    · rw [h]
      have hng : (fun z : UnitAddCircle => (-1 : ℤ) • z) = Neg.neg := by
        funext z
        simp
      rw [hng]
      exact Measure.measurePreserving_neg (volume : Measure UnitAddCircle)
  have hmp := measurePreserving_pi (fun _ : ι => (volume : Measure UnitAddCircle))
    (fun _ : ι => (volume : Measure UnitAddCircle)) hcoord
  rw [MeasureTheory.volume_pi]
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable]

end

end FroehlichSpencer.FS82.ZN

end
