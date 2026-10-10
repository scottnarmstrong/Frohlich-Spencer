/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.GraphSymmetry

/-! # Villain measures under rooted graph isomorphisms

The rooted angle box and Villain measure are natural under a multigraph isomorphism that sends
the pinned vertex to the pinned vertex (KP §1.4, p. 4).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.BKT.Villain

variable {V E W F : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
  [DecidableEq V] [DecidableEq W]

/-- The induced equivalence of vertices away from corresponding roots. -/
def rootedVertexIso {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w) :
    FreeVertices V z ≃ FreeVertices W w where
  toFun j := ⟨I.vertices j.1, by
    intro h
    apply j.2
    apply I.vertices.injective
    exact h.trans hz.symm⟩
  invFun j := ⟨I.vertices.symm j.1, by
    intro h
    apply j.2
    calc
      j.1 = I.vertices (I.vertices.symm j.1) := (I.vertices.apply_symm_apply _).symm
      _ = I.vertices z := congrArg I.vertices h
      _ = w := hz⟩
  left_inv j := Subtype.ext (I.vertices.symm_apply_apply j.1)
  right_inv j := Subtype.ext (I.vertices.apply_symm_apply j.1)

/-- The corresponding measurable equivalence of rooted angle coordinates. -/
def rootedAngleIso {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w) :
    FreeAngles V z ≃ᵐ FreeAngles W w :=
  MeasurableEquiv.piCongrLeft (fun _ : FreeVertices W w => ℝ)
    (rootedVertexIso I z w hz)

omit [Fintype V] [Fintype E] [Fintype W] [Fintype F] [DecidableEq V] [DecidableEq W] in
@[simp] theorem rootedAngleIso_apply {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w)
    (θ : FreeAngles V z) (j : FreeVertices V z) :
    rootedAngleIso I z w hz θ (rootedVertexIso I z w hz j) = θ j := by
  simp [rootedAngleIso, rootedVertexIso, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply]

omit [Fintype V] [Fintype E] [Fintype W] [Fintype F] in
private theorem rootedAngleIso_pinned {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w)
    (θ : FreeAngles V z) (v : V) :
    pinnedAngle w (rootedAngleIso I z w hz θ) (I.vertices v) = pinnedAngle z θ v := by
  by_cases hv : v = z
  · subst v
    simp [hz]
  · have hIv : I.vertices v ≠ w := by
      intro h
      apply hv
      apply I.vertices.injective
      exact h.trans hz.symm
    have hidx : rootedVertexIso I z w hz ⟨v, hv⟩ = ⟨I.vertices v, hIv⟩ := rfl
    rw [pinnedAngle_of_ne w (I.vertices v) _ hIv,
      pinnedAngle_of_ne z v _ hv]
    rw [← hidx, rootedAngleIso_apply]

omit [Fintype V] [Fintype W] in
/-- The Villain edge density is transported by a rooted multigraph isomorphism. -/
theorem villainRealDensity_rootedAngleIso {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w)
    (β : ℝ) (θ : FreeAngles V z) :
    villainRealDensity H w β (rootedAngleIso I z w hz θ) =
      villainRealDensity G z β θ := by
  classical
  unfold villainRealDensity
  rw [← I.edges.prod_comp]
  apply Finset.prod_congr rfl
  intro e he
  rcases I.endpoints e with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs, ht, rootedAngleIso_pinned, rootedAngleIso_pinned]
  · rw [hs, ht, rootedAngleIso_pinned, rootedAngleIso_pinned]
    rw [show pinnedAngle z θ (G.tgt e) - pinnedAngle z θ (G.src e) =
      -(pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) by ring,
      VillainWeight.villainWeight_neg]

omit [Fintype E] [Fintype F] in
/-- The rooted product angle measure is preserved under a graph isomorphism. -/
theorem rootedAngleMeasurePreserving_iso {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w) :
    MeasurePreserving (rootedAngleIso I z w hz) (rootedAngleMeasure z)
      (rootedAngleMeasure w) := by
  change MeasurePreserving
    (⇑(MeasurableEquiv.piCongrLeft (fun _ : FreeVertices W w => ℝ)
      (rootedVertexIso I z w hz)))
    (Measure.pi fun _ : FreeVertices V z => volume.restrict (Set.Ico (-Real.pi) Real.pi))
    (Measure.pi fun _ : FreeVertices W w => volume.restrict (Set.Ico (-Real.pi) Real.pi))
  exact MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : FreeVertices W w => volume.restrict (Set.Ico (-Real.pi) Real.pi))
    (rootedVertexIso I z w hz)

/-- The internal unnormalized rooted Villain measure pushes forward under a rooted graph
isomorphism. -/
theorem rootedVillainDensityMeasure_map_rootedAngleIso
    {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w)
    (β : ℝ) (hβ : 0 < β) :
    Measure.map (rootedAngleIso I z w hz) (rootedVillainDensityMeasure G z β) =
      rootedVillainDensityMeasure H w β := by
  classical
  let A := rootedAngleIso I z w hz
  let μ := rootedAngleMeasure z
  let ν := rootedAngleMeasure w
  let ρ : FreeAngles V z → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal (villainRealDensity G z β θ)
  let σ : FreeAngles W w → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal (villainRealDensity H w β θ)
  have hμ := rootedAngleMeasurePreserving_iso I z w hz
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact ENNReal.measurable_ofReal.comp
      (continuous_villainRealDensity G z β hβ).measurable
  have hσ : Measurable σ := by
    dsimp [σ]
    exact ENNReal.measurable_ofReal.comp
      (continuous_villainRealDensity H w β hβ).measurable
  have hinv (θ : FreeAngles V z) : σ (A θ) = ρ θ := by
    simp [σ, ρ, A, villainRealDensity_rootedAngleIso]
  change Measure.map A (μ.withDensity ρ) = ν.withDensity σ
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply A.measurable hs,
    MeasureTheory.withDensity_apply σ hs,
    MeasureTheory.withDensity_apply ρ (hs.preimage A.measurable)]
  calc
    (∫⁻ θ in A ⁻¹' s, ρ θ ∂μ) =
        ∫⁻ θ, (A ⁻¹' s).indicator ρ θ ∂μ :=
      (lintegral_indicator (hs.preimage A.measurable) ρ).symm
    _ = ∫⁻ θ, s.indicator σ (A θ) ∂μ := by
      congr 1
      funext θ
      by_cases hθ : A θ ∈ s <;> simp [Set.indicator, hθ, hinv θ]
    _ = ∫⁻ θ, s.indicator σ θ ∂ν := hμ.lintegral_comp (hσ.indicator hs)
    _ = ∫⁻ θ in s, σ θ ∂ν := lintegral_indicator hs σ

/-- Rooted Villain partition functions agree under a rooted graph isomorphism. -/
theorem villainPartitionFunction_iso {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w)
    (β : ℝ) (_hβ : 0 < β) :
    villainPartitionFunction H w β = villainPartitionFunction G z β := by
  let A := rootedAngleIso I z w hz
  let hμ := rootedAngleMeasurePreserving_iso I z w hz
  calc
    villainPartitionFunction H w β =
        ∫ θ, villainRealDensity H w β θ ∂rootedAngleMeasure w := rfl
    _ = ∫ θ, villainRealDensity H w β (A θ) ∂rootedAngleMeasure z := by
      symm
      exact hμ.integral_comp' (villainRealDensity H w β)
    _ = villainPartitionFunction G z β := by
      simp [A, villainRealDensity_rootedAngleIso]
      rfl

/-- The normalized rooted Villain measure pushes forward exactly under a rooted graph
isomorphism. -/
theorem rootedVillainMeasure_map_rootedAngleIso {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w)
    (β : ℝ) (hβ : 0 < β) :
  Measure.map (rootedAngleIso I z w hz) (rootedVillainMeasure G z β hβ) =
      rootedVillainMeasure H w β hβ := by
  rw [rootedVillainMeasure, rootedVillainMeasure,
    Measure.map_smul (ENNReal.ofReal (villainPartitionFunction G z β))⁻¹
      (rootedAngleIso I z w hz).measurable.aemeasurable,
    villainPartitionFunction_iso I z w hz β hβ,
    rootedVillainDensityMeasure_map_rootedAngleIso I z w hz β hβ]

/-- The cosine expectation transports along the rooted vertex map of a graph isomorphism. -/
theorem villainCosExpectation_iso {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (z : V) (w : W) (hz : I.vertices z = w)
    (β : ℝ) (hβ : 0 < β) (site : FreeVertices V z) :
    villainCosExpectation H w β (rootedVertexIso I z w hz site) =
      villainCosExpectation G z β site := by
  unfold villainCosExpectation
  let hμ := rootedAngleMeasurePreserving_iso I z w hz
  rw [villainPartitionFunction_iso I z w hz β hβ]
  congr 1
  rw [← hμ.integral_comp' (villainCosineIntegrand H w β
    (rootedVertexIso I z w hz site))]
  apply integral_congr_ae
  filter_upwards with θ
  simp [villainCosineIntegrand, rootedAngleIso_apply,
    villainRealDensity_rootedAngleIso]

end FroehlichSpencer.BKT.Villain

end
