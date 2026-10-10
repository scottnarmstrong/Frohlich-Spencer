/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

public section

namespace FroehlichSpencer.FS82.Gaussian


open MeasureTheory MeasureTheory.Measure

/-- Under a linear equivalence, Lebesgue measure changes by a finite positive
constant. This is the determinant factor; it disappears after normalization. -/
theorem map_volume_linearEquiv_smul
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (f : E ≃L[ℝ] F) :
    ∃ c : ENNReal, 0 < c ∧ c ≠ ⊤ ∧ Measure.map f volume = c • volume := by
  let bE := (stdOrthonormalBasis ℝ E).toBasis
  have hE : bE.addHaar = (volume : Measure E) :=
    (stdOrthonormalBasis ℝ E).addHaar_eq_volume
  have hmap : Measure.map f (volume : Measure E) = (bE.map f.toLinearEquiv).addHaar := by
    rw [← hE]
    exact Module.Basis.map_addHaar bE f
  let ν := (bE.map f.toLinearEquiv).addHaar
  let K : TopologicalSpace.PositiveCompacts F := Classical.arbitrary _
  let v : ENNReal := volume (K : Set F)
  let u : ENNReal := ν (K : Set F)
  let c : ENNReal := u / v
  have hvpos : 0 < v := by
    dsimp [v]
    exact Measure.measure_pos_of_nonempty_interior volume K.interior_nonempty'
  have hvfinite : v < ⊤ := by
    dsimp [v]
    exact K.isCompact.measure_lt_top
  have hupos : 0 < u := by
    dsimp [u, ν]
    exact Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty'
  have hufinite : u < ⊤ := by
    dsimp [u, ν]
    exact K.isCompact.measure_lt_top
  have hν : ν = u • Measure.addHaarMeasure K := by
    dsimp [ν, u]
    exact Measure.addHaarMeasure_unique _ K
  have hvolume : (volume : Measure F) = v • Measure.addHaarMeasure K := by
    dsimp [v]
    exact Measure.addHaarMeasure_unique _ K
  have hcpos : 0 < c := by
    dsimp [c]
    exact ENNReal.div_pos (ne_of_gt hupos) (ne_of_lt hvfinite)
  have hcfinite : c ≠ (⊤ : ENNReal) := by
    dsimp [c]
    exact ENNReal.div_ne_top (ne_of_lt hufinite) (ne_of_gt hvpos)
  refine ⟨c, hcpos, hcfinite, ?_⟩
  calc
    Measure.map f (volume : Measure E) = ν := hmap
    _ = u • Measure.addHaarMeasure K := hν
    _ = c • (volume : Measure F) := by
      rw [hvolume, smul_smul]
      congr 1
      dsimp [c]
      exact (ENNReal.div_mul_cancel (ne_of_gt hvpos) (ne_of_lt hvfinite) (b := u)).symm

/-- Normalize a finite positive measure. -/
@[expose] noncomputable def normalizedMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) : Measure X := (μ Set.univ)⁻¹ • μ

theorem normalizedMeasure_smul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (c : ENNReal) (hcpos : 0 < c) (hcfinite : c ≠ ⊤) :
    normalizedMeasure (c • μ) = normalizedMeasure μ := by
  ext s hs
  simp only [normalizedMeasure, Measure.smul_apply]
  change ((c * μ Set.univ)⁻¹ * (c * μ s)) =
    (μ Set.univ)⁻¹ * μ s
  rw [ENNReal.mul_inv (Or.inl (ne_of_gt hcpos)) (Or.inl hcfinite)]
  calc
    c⁻¹ * (μ Set.univ)⁻¹ * (c * μ s) =
        (μ Set.univ)⁻¹ * (c⁻¹ * c) * μ s := by ac_rfl
    _ = (μ Set.univ)⁻¹ * μ s := by
      rw [ENNReal.inv_mul_cancel (ne_of_gt hcpos) hcfinite]
      ring

/-- Push-forward through a linear equivalence commutes with normalizing the
total mass. -/
theorem map_normalizedMeasure_linearEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    [MeasurableSpace E] [MeasurableSpace F]
    [BorelSpace F] [OpensMeasurableSpace E] [OpensMeasurableSpace F]
    (f : E ≃L[ℝ] F) (μ : Measure E) :
    Measure.map f (normalizedMeasure μ) = normalizedMeasure (Measure.map f μ) := by
  have hmass : (Measure.map f μ) Set.univ = μ Set.univ := by
    rw [Measure.map_apply f.continuous.measurable MeasurableSet.univ]
    simp
  unfold normalizedMeasure
  rw [Measure.map_smul _ f.continuous.measurable.aemeasurable, hmass]

/-- Transport a density along a continuous linear equivalence before applying
the linear change-of-variables formula for volume. -/
theorem map_withDensity_linearEquiv_general
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    [MeasurableSpace E] [MeasurableSpace F]
    [BorelSpace F] [OpensMeasurableSpace E] [OpensMeasurableSpace F]
    (f : E ≃L[ℝ] F) (μ : Measure E) (g : F → ENNReal) (hg : Measurable g) :
    Measure.map f (μ.withDensity (g ∘ f)) =
      (Measure.map f μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply f.continuous.measurable hs,
    withDensity_apply _ (hs.preimage f.continuous.measurable),
    withDensity_apply _ hs]
  exact (setLIntegral_map hs hg f.continuous.measurable).symm

/-- Mapping a density pulled back along a linear equivalence gives the
corresponding density against the transported volume measure. -/
theorem map_withDensity_linearEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (f : E ≃L[ℝ] F) (g : F → ENNReal) (hg : Measurable g) :
    Measure.map f (volume.withDensity (g ∘ f)) =
      (Measure.map f volume).withDensity g := by
  ext s hs
  rw [Measure.map_apply f.continuous.measurable hs,
    withDensity_apply _ (hs.preimage f.continuous.measurable),
    withDensity_apply _ hs]
  exact (setLIntegral_map hs hg f.continuous.measurable).symm

/-- The determinant factor cancels from normalized density transport under
any finite-dimensional linear equivalence. -/
theorem normalizedDensity_map_linearEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (f : E ≃L[ℝ] F) (g : F → ENNReal) (hg : Measurable g) :
    Measure.map f (normalizedMeasure (volume.withDensity (g ∘ f))) =
      normalizedMeasure (volume.withDensity g) := by
  obtain ⟨c, hcpos, hcfinite, hcvol⟩ := map_volume_linearEquiv_smul f
  have hmap := map_withDensity_linearEquiv f g hg
  rw [hcvol, withDensity_smul_measure] at hmap
  have hmass : (volume.withDensity (g ∘ f)) Set.univ =
      c * (volume.withDensity g) Set.univ := by
    have h := congrArg (fun μ : Measure F => μ Set.univ) hmap
    rw [Measure.map_apply f.continuous.measurable MeasurableSet.univ] at h
    simpa [Measure.smul_apply, ENNReal.smul_def] using h
  unfold normalizedMeasure
  rw [Measure.map_smul _ f.continuous.measurable.aemeasurable, hmap, smul_smul]
  rw [hmass]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (ne_of_gt hcpos)) (Or.inl hcfinite)]
  calc
    c⁻¹ * ((volume.withDensity g) Set.univ)⁻¹ * c =
        ((volume.withDensity g) Set.univ)⁻¹ * (c⁻¹ * c) := by ac_rfl
    _ = ((volume.withDensity g) Set.univ)⁻¹ := by
      rw [ENNReal.inv_mul_cancel (ne_of_gt hcpos) hcfinite]
      ring

end FroehlichSpencer.FS82.Gaussian

end
