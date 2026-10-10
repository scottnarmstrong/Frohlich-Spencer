/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.CosineExpectation
public import FroehlichSpencer.BKT.Potential.Transport
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Symmetry invariance of rooted Villain expectations

Root-fixing graph automorphisms act by coordinate permutations on the pinned angle box. The
product Lebesgue measure and the Villain density are invariant under this action (KP §1.4,
p. 4).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.BKT.Villain

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The induced permutation of non-root vertices for a graph isomorphism fixing the root. -/
def rootedVertexEquiv (G : Multigraph V E) (z : V)
    (I : Multigraph.Isomorphism G G) (hz : I.vertices z = z) :
    FreeVertices V z ≃ FreeVertices V z where
  toFun j := ⟨I.vertices j.1, by
    intro hj
    apply j.2
    apply I.vertices.injective
    calc
      I.vertices j.1 = z := hj
      _ = I.vertices z := hz.symm⟩
  invFun j := ⟨I.vertices.symm j.1, by
    intro hj
    apply j.2
    calc
      j.1 = I.vertices (I.vertices.symm j.1) := (I.vertices.apply_symm_apply _).symm
      _ = I.vertices z := congrArg I.vertices hj
      _ = z := hz⟩
  left_inv j := Subtype.ext (I.vertices.symm_apply_apply j.1)
  right_inv j := Subtype.ext (I.vertices.apply_symm_apply j.1)

/-- The induced measurable permutation of root-pinned angle configurations. -/
def rootedAngleMeasurableEquiv (G : Multigraph V E) (z : V)
    (I : Multigraph.Isomorphism G G) (hz : I.vertices z = z) :
    FreeAngles V z ≃ᵐ FreeAngles V z :=
  MeasurableEquiv.piCongrLeft (fun _ : FreeVertices V z => ℝ)
    (rootedVertexEquiv G z I hz)

omit [Fintype E] in
/-- The rooted angle product measure is preserved by the coordinate permutation. -/
theorem rootedAngleMeasurePreserving (G : Multigraph V E) (z : V)
    (I : Multigraph.Isomorphism G G) (hz : I.vertices z = z) :
    MeasurePreserving (rootedAngleMeasurableEquiv G z I hz)
      (rootedAngleMeasure z) (rootedAngleMeasure z) := by
  classical
  change MeasurePreserving
    (⇑(MeasurableEquiv.piCongrLeft (fun _ : FreeVertices V z => ℝ)
      (rootedVertexEquiv G z I hz)))
    (Measure.pi fun _ : FreeVertices V z => volume.restrict (Set.Ico (-Real.pi) Real.pi))
    (Measure.pi fun _ : FreeVertices V z => volume.restrict (Set.Ico (-Real.pi) Real.pi))
  exact MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : FreeVertices V z => volume.restrict (Set.Ico (-Real.pi) Real.pi))
    (rootedVertexEquiv G z I hz)

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem rootedAngleMeasurableEquiv_apply_image (G : Multigraph V E) (z : V)
    (I : Multigraph.Isomorphism G G) (hz : I.vertices z = z)
    (θ : FreeAngles V z) (j : FreeVertices V z) :
    rootedAngleMeasurableEquiv G z I hz θ (rootedVertexEquiv G z I hz j) = θ j := by
  simp [rootedAngleMeasurableEquiv, rootedVertexEquiv,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

omit [Fintype V] [Fintype E] in
private theorem pinnedAngle_rootedAngleMeasurableEquiv_image (G : Multigraph V E) (z : V)
    (I : Multigraph.Isomorphism G G) (hz : I.vertices z = z)
    (θ : FreeAngles V z) (j : V) :
    pinnedAngle z (rootedAngleMeasurableEquiv G z I hz θ) (I.vertices j) =
      pinnedAngle z θ j := by
  by_cases hj : j = z
  · subst j
    simp [hz]
  · have hIj : I.vertices j ≠ z := by
      intro h
      apply hj
      calc
        j = I.vertices.symm (I.vertices j) := (I.vertices.symm_apply_apply j).symm
        _ = I.vertices.symm z := congrArg I.vertices.symm h
        _ = z := by
          calc
            I.vertices.symm z = I.vertices.symm (I.vertices z) := congrArg I.vertices.symm hz.symm
            _ = z := I.vertices.symm_apply_apply z
    simp [pinnedAngle, hj, hIj, rootedAngleMeasurableEquiv, rootedVertexEquiv,
      MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

omit [Fintype V] in
/-- The real edge density is unchanged after transporting angles through a root-fixing
isomorphism of a graph to itself. -/
theorem villainRealDensity_rootedAngleMeasurableEquiv (G : Multigraph V E) (z : V)
    (β : ℝ) (I : Multigraph.Isomorphism G G) (hz : I.vertices z = z)
    (θ : FreeAngles V z) :
    villainRealDensity G z β (rootedAngleMeasurableEquiv G z I hz θ) =
      villainRealDensity G z β θ := by
  classical
  unfold villainRealDensity
  rw [← I.edges.prod_comp]
  apply Finset.prod_congr rfl
  intro e he
  rcases I.endpoints e with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
  · rw [hsrc, htgt, pinnedAngle_rootedAngleMeasurableEquiv_image,
      pinnedAngle_rootedAngleMeasurableEquiv_image]
  · rw [hsrc, htgt, pinnedAngle_rootedAngleMeasurableEquiv_image,
      pinnedAngle_rootedAngleMeasurableEquiv_image]
    rw [show pinnedAngle z θ (G.tgt e) - pinnedAngle z θ (G.src e) =
      -(pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) by ring,
      VillainWeight.villainWeight_neg]

/-- The unnormalized rooted Villain angle measure, characterized by the KP product density on the
rooted Lebesgue box (KP §1.4, p. 4). -/
noncomputable def rootedVillainDensityMeasure (G : Multigraph V E) (z : V) (β : ℝ) :
    Measure (FreeAngles V z) :=
  (rootedAngleMeasure z).withDensity
    (fun θ => ENNReal.ofReal (villainRealDensity G z β θ))

/-- The rooted Villain density is integrable because the one-edge Fourier series gives a uniform
finite bound on the finite angle box. -/
theorem integrable_villainRealDensity (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) : Integrable (villainRealDensity G z β) (rootedAngleMeasure z) := by
  classical
  have hμ : IsFiniteMeasure (rootedAngleMeasure z) := by
    dsimp [rootedAngleMeasure]
    infer_instance
  have hcont : Continuous (villainRealDensity G z β) :=
    continuous_villainRealDensity G z β hβ
  have hbound (θ : FreeAngles V z) :
      ‖villainRealDensity G z β θ‖ ≤
        ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
          ∑' q : ℤ, Real.exp (-((q : ℝ) ^ 2) / (2 * β))) ^ Fintype.card E := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (villainRealDensity_nonneg_le G z β hβ θ).1]
    exact (villainRealDensity_nonneg_le G z β hβ θ).2
  exact Integrable.of_bound hcont.aestronglyMeasurable _
    (Filter.Eventually.of_forall hbound)

/-- The unnormalized internal Villain measure has total mass equal to the rooted partition
function (KP §1.4, p. 4). -/
theorem rootedVillainDensityMeasure_mass (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) :
    rootedVillainDensityMeasure G z β Set.univ =
      ENNReal.ofReal (villainPartitionFunction G z β) := by
  rw [rootedVillainDensityMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  calc
    (∫⁻ θ in Set.univ, ENNReal.ofReal (villainRealDensity G z β θ)
        ∂rootedAngleMeasure z) =
        ∫⁻ θ, ENNReal.ofReal (villainRealDensity G z β θ) ∂rootedAngleMeasure z := by
      rw [← MeasureTheory.lintegral_indicator MeasurableSet.univ]
      simp
    _ = ENNReal.ofReal (villainPartitionFunction G z β) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrable_villainRealDensity G z β hβ)
        (Filter.Eventually.of_forall fun θ =>
          (villainRealDensity_nonneg_le G z β hβ θ).1)]
      simp [villainPartitionFunction, villainRealDensity]

/-- The normalized internal rooted Villain measure associated with KP's rooted angle integral. -/
noncomputable def rootedVillainMeasure (G : Multigraph V E) (z : V) (β : ℝ)
    (_hβ : 0 < β) : Measure (FreeAngles V z) :=
  (ENNReal.ofReal (villainPartitionFunction G z β))⁻¹ •
    rootedVillainDensityMeasure G z β

/-- The normalized internal rooted Villain measure is a probability measure. -/
theorem rootedVillainMeasure_isProbabilityMeasure (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) : IsProbabilityMeasure (rootedVillainMeasure G z β hβ) := by
  rw [isProbabilityMeasure_iff]
  rw [rootedVillainMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul,
    rootedVillainDensityMeasure_mass G z β hβ]
  have hZ : 0 < villainPartitionFunction G z β :=
    villain_partition_integral_pos G z β hβ
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hZ).ne'
    (ne_of_lt ENNReal.ofReal_lt_top)

/-- Integrating the cosine against the normalized internal rooted Villain measure gives the
rooted Villain expectation from the Fourier expansion API (KP §1.4, p. 4). -/
theorem rootedVillainMeasure_cosIntegral_eq_villainCosExpectation
    (G : Multigraph V E) (z : V) (β : ℝ) (hβ : 0 < β)
    (site : FreeVertices V z) :
    (∫ θ, Real.cos (θ site) ∂rootedVillainMeasure G z β hβ) =
      villainCosExpectation G z β site := by
  let ρ : FreeAngles V z → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal (villainRealDensity G z β θ)
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact ENNReal.measurable_ofReal.comp
      (continuous_villainRealDensity G z β hβ).measurable
  have hρtop : ∀ᵐ θ ∂rootedAngleMeasure z, ρ θ < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hZ : 0 < villainPartitionFunction G z β :=
    villain_partition_integral_pos G z β hβ
  have hscale :
      ((ENNReal.ofReal (villainPartitionFunction G z β))⁻¹).toReal =
        (villainPartitionFunction G z β)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  have hinner :
      (∫ θ, (ρ θ).toReal * Real.cos (θ site) ∂rootedAngleMeasure z) =
        ∫ θ, villainCosineIntegrand G z β site θ ∂rootedAngleMeasure z := by
    apply integral_congr_ae
    filter_upwards with θ
    simp [ρ, villainCosineIntegrand,
      ENNReal.toReal_ofReal (villainRealDensity_nonneg_le G z β hβ θ).1]
  unfold villainCosExpectation
  rw [rootedVillainMeasure, MeasureTheory.integral_smul_measure,
    rootedVillainDensityMeasure,
    integral_withDensity_eq_integral_toReal_smul hρ hρtop]
  rw [hscale]
  simp only [smul_eq_mul]
  rw [hinner]
  field_simp [ne_of_gt hZ]

/-- A root-fixing graph automorphism preserves the unnormalized internal Villain measure. -/
theorem rootedVillainDensityMeasure_map_rootedAngleMeasurableEquiv
    (G : Multigraph V E) (z : V) (β : ℝ) (hβ : 0 < β)
    (I : Multigraph.Isomorphism G G) (hz : I.vertices z = z) :
    Measure.map (rootedAngleMeasurableEquiv G z I hz)
        (rootedVillainDensityMeasure G z β) = rootedVillainDensityMeasure G z β := by
  classical
  let A := rootedAngleMeasurableEquiv G z I hz
  let μ := rootedAngleMeasure z
  let ρ : FreeAngles V z → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal (villainRealDensity G z β θ)
  have hμ := rootedAngleMeasurePreserving G z I hz
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact ENNReal.measurable_ofReal.comp
      (continuous_villainRealDensity G z β hβ).measurable
  have hinv (θ : FreeAngles V z) : ρ (A θ) = ρ θ := by
    simp [ρ, A, villainRealDensity_rootedAngleMeasurableEquiv G z β I hz θ]
  change Measure.map A (μ.withDensity ρ) = μ.withDensity ρ
  apply MeasureTheory.Measure.ext
  intro s hs
  rw [MeasureTheory.Measure.map_apply A.measurable hs,
    MeasureTheory.withDensity_apply ρ (hs.preimage A.measurable),
    MeasureTheory.withDensity_apply ρ hs]
  calc
    (∫⁻ θ in A ⁻¹' s, ρ θ ∂μ) =
        ∫⁻ θ, (A ⁻¹' s).indicator ρ θ ∂μ :=
      (MeasureTheory.lintegral_indicator (hs.preimage A.measurable) ρ).symm
    _ = ∫⁻ θ, s.indicator ρ (A θ) ∂μ := by
      congr 1
      funext θ
      by_cases hθ : A θ ∈ s <;> simp [Set.indicator, hθ, hinv θ]
    _ = ∫⁻ θ, s.indicator ρ θ ∂μ :=
      MeasureTheory.MeasurePreserving.lintegral_comp hμ (hρ.indicator hs)
    _ = ∫⁻ θ in s, ρ θ ∂μ := MeasureTheory.lintegral_indicator hs ρ

/-- The normalized rooted Villain measure is invariant under a root-fixing graph automorphism. -/
theorem rootedVillainMeasure_map_rootedAngleMeasurableEquiv
    (G : Multigraph V E) (z : V) (β : ℝ) (hβ : 0 < β)
    (I : Multigraph.Isomorphism G G) (hz : I.vertices z = z) :
    Measure.map (rootedAngleMeasurableEquiv G z I hz)
        (rootedVillainMeasure G z β hβ) = rootedVillainMeasure G z β hβ := by
  rw [rootedVillainMeasure, MeasureTheory.Measure.map_smul
      (ENNReal.ofReal (villainPartitionFunction G z β))⁻¹
      (rootedAngleMeasurableEquiv G z I hz).measurable.aemeasurable,
    rootedVillainDensityMeasure_map_rootedAngleMeasurableEquiv G z β hβ I hz]

/-- The rooted Villain cosine expectation is invariant under any graph automorphism fixing the
pinned root (KP §1.4, p. 4). -/
theorem villainCosExpectation_rootedAutomorphism (G : Multigraph V E) (z : V)
    (β : ℝ) (_hβ : 0 < β) (I : Multigraph.Isomorphism G G)
    (hz : I.vertices z = z) (site : FreeVertices V z) :
    villainCosExpectation G z β (rootedVertexEquiv G z I hz site) =
      villainCosExpectation G z β site := by
  let A := rootedAngleMeasurableEquiv G z I hz
  let μ := rootedAngleMeasure z
  have hμ := rootedAngleMeasurePreserving G z I hz
  have hnum :
      (∫ θ, villainCosineIntegrand G z β
          (rootedVertexEquiv G z I hz site) θ ∂μ) =
        ∫ θ, villainCosineIntegrand G z β site θ ∂μ := by
    calc
      _ = ∫ θ, villainCosineIntegrand G z β
          (rootedVertexEquiv G z I hz site) (A θ) ∂μ := by
        symm
        exact hμ.integral_comp' (villainCosineIntegrand G z β
          (rootedVertexEquiv G z I hz site))
      _ = ∫ θ, villainCosineIntegrand G z β site θ ∂μ := by
        apply integral_congr_ae
        filter_upwards with θ
        simp [villainCosineIntegrand, A,
          villainRealDensity_rootedAngleMeasurableEquiv]
  unfold villainCosExpectation
  rw [hnum]

end FroehlichSpencer.BKT.Villain

end
