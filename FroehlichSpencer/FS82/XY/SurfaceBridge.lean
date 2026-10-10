/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.SurfaceXY.All
public import FroehlichSpencer.FS82.XY.SpinTheoremD
public import FroehlichSpencer.FS82.XY.SpinRoot3
import Mathlib.Tactic

/-!
# FS82 §4: providers of the literal XY surface

The literal surface `FroehlichSpencer.FS82.SurfaceXY` (finite free-box Villain XY model: boxes,
cells, the cubical boundary, the Villain weight (4.4), the finite law (4.5), the spin observable
(4.22)) is bridged to the internal model of `XY/SpinLaw.lean`, in every dimension:

* the literal site and bond types are the internal ones (`sourceSiteEquiv`, `sourceBondEquiv`),
  and the configuration spaces are measurably equivalent, preserving the product Haar measure;
* the literal cubical boundary is `Cubical.boundary`; the literal Villain weight is the internal
  periodized Gaussian (reindexing `n ↦ −n`); hence the densities, partition functions and spin
  correlations agree (`sourceSpinCorrelation_eq_internal`).

Providers of the four theorem statement:
-/

open scoped BigOperators
open MeasureTheory

public section

namespace FroehlichSpencer.FS82.SurfaceXYBridge

noncomputable section

open FroehlichSpencer.FS82.SurfaceXY
open FroehlichSpencer.FS82.Cubical
open Classical

local instance surfaceBridgeFactOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance surfaceBridgeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-! ## Carriers -/

theorem sourceDegree_eq_internal {D : ℕ} {B : XYBox D} (c : XYCell B) :
    xyCellDegree c = cellDegree c := by
  have haxes : xyCellAxes c = cellAxes c := by
    unfold xyCellAxes FroehlichSpencer.FS82.Cubical.cellAxes
    apply Finset.filter_congr
    intro i hi
    rfl
  rw [xyCellDegree, cellDegree, haxes]

/-- The literal sites are the internal sites. -/
def sourceSiteEquiv {D : ℕ} (B : XYBox D) :
    XYSite B ≃ FroehlichSpencer.FS82.XY.XYSites B where
  toFun x := ⟨x.1, by rw [← sourceDegree_eq_internal]; exact x.2⟩
  invFun x := ⟨x.1, by rw [sourceDegree_eq_internal]; exact x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem sourceRank_eq_internal {D : ℕ} {B : XYBox D}
    (c : XYCell B) (i : Fin D) :
    xyCellRankBefore c i = FroehlichSpencer.FS82.Cubical.cellRankBefore c i := by
  unfold xyCellRankBefore FroehlichSpencer.FS82.Cubical.cellRankBefore
    xyCoordIsEdge FroehlichSpencer.FS82.Cubical.coordIsEdge
  congr 1
  ext j
  simp

/-- The literal bonds are the internal bonds. -/
def sourceBondEquiv {D : ℕ} (B : XYBox D) :
    XYBond B ≃ FroehlichSpencer.FS82.XY.XYBonds B where
  toFun x := ⟨x.1, by rw [← sourceDegree_eq_internal]; exact x.2⟩
  invFun x := ⟨x.1, by rw [sourceDegree_eq_internal]; exact x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- The literal configurations are the internal configurations. -/
def sourceConfigEquiv {D : ℕ} (B : XYBox D) :
    SurfaceXY.XYAngleConfig B ≃ᵐ FroehlichSpencer.FS82.XY.XYAngleConfig B :=
  MeasurableEquiv.piCongrLeft (fun _ : FroehlichSpencer.FS82.XY.XYSites B => UnitAddCircle)
    (sourceSiteEquiv B)

theorem sourceAngleCochain_mapped {D : ℕ} {B : XYBox D}
    (θ : SurfaceXY.XYAngleConfig B) (c : XYCell B) :
    SurfaceXY.xyAngleCochain θ c = FroehlichSpencer.FS82.XY.xyAngleCochain
      (sourceConfigEquiv B θ) c := by
  by_cases h : xyCellDegree c = 0
  · have hi : cellDegree c = 0 := by
      rw [← sourceDegree_eq_internal c]
      exact h
    have hsite : sourceSiteEquiv B ⟨c, h⟩ =
        (⟨c, hi⟩ : FroehlichSpencer.FS82.XY.XYSites B) := by
      apply Subtype.ext
      rfl
    simp only [SurfaceXY.xyAngleCochain, FroehlichSpencer.FS82.XY.xyAngleCochain,
      dite_eq_left h, dite_eq_left hi]
    change θ ⟨c, h⟩ = (sourceConfigEquiv B θ) ⟨c, hi⟩
    rw [← hsite]
    change θ ((sourceSiteEquiv B).symm (sourceSiteEquiv B ⟨c, h⟩)) = θ ⟨c, h⟩
    simp
  · have hi : cellDegree c ≠ 0 := by
      intro hi
      apply h
      rw [sourceDegree_eq_internal c]
      exact hi
    simp [SurfaceXY.xyAngleCochain, FroehlichSpencer.FS82.XY.xyAngleCochain, h, hi]

/-! ## Boundary, weight, measure -/

theorem sourceBoundary_eq_internal {D : ℕ} {B : XYBox D} :
    xyBoundary (B := B) = FroehlichSpencer.FS82.Cubical.boundary := by
  ext q c
  simp [xyBoundary, FroehlichSpencer.FS82.Cubical.boundary, xyAxisBoundary,
    FroehlichSpencer.FS82.Cubical.axisBoundary, xyAxisBoundaryBasis,
    FroehlichSpencer.FS82.Cubical.axisBoundaryBasis, xyBasisChain,
    FroehlichSpencer.FS82.Cubical.basisChain, xyUpperFace,
    FroehlichSpencer.FS82.Cubical.upperFace, xyLowerFace,
    FroehlichSpencer.FS82.Cubical.lowerFace,
    FroehlichSpencer.FS82.Cubical.vertexUpdate,
    sourceRank_eq_internal]
  rfl

theorem circleRepresentative_eq (z : UnitAddCircle) :
    xyCircleRepresentative z = FroehlichSpencer.FS82.Wilson.circleRepresentative z := by
  rfl

theorem periodized_plus_eq_minus (β x : ℝ) :
    (∑' n : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * (n : ℝ)) ^ 2)) =
      (∑' n : ℤ, Real.exp (-(β / 2) * (x - 2 * Real.pi * (n : ℝ)) ^ 2)) := by
  conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro n
  congr 3
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

theorem sourceWeight_eq_internal (β : ℝ) (hβ : 0 < β) (z : UnitAddCircle) :
    xyVillainWeight β z = FroehlichSpencer.FS82.Wilson.villainCircleWeight β z := by
  rw [FroehlichSpencer.FS82.Wilson.villainCircleWeight_eq_periodized β z hβ]
  rw [xyVillainWeight, circleRepresentative_eq]
  exact periodized_plus_eq_minus β (2 * Real.pi *
    FroehlichSpencer.FS82.Wilson.circleRepresentative z)

theorem sourceHaar_measurePreserving {D : ℕ} (B : XYBox D) :
    MeasurePreserving (sourceConfigEquiv B) (xyAngleHaarMeasure B)
      (Measure.pi fun _ : FroehlichSpencer.FS82.XY.XYSites B => AddCircle.haarAddCircle) := by
  exact MeasureTheory.measurePreserving_piCongrLeft
      (α := fun _ : FroehlichSpencer.FS82.XY.XYSites B => UnitAddCircle)
      (μ := fun _ : FroehlichSpencer.FS82.XY.XYSites B => AddCircle.haarAddCircle)
      (sourceSiteEquiv B)

theorem internalVolume_eq_pi {D : ℕ} (B : XYBox D) :
    (volume : Measure (FroehlichSpencer.FS82.XY.XYAngleConfig B)) =
      Measure.pi (fun _ : FroehlichSpencer.FS82.XY.XYSites B => AddCircle.haarAddCircle) := by
  have hvol : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := rfl
  rw [MeasureTheory.volume_pi]
  simp [hvol]

/-! ## Density, partition function, correlation -/

theorem sourceBondDifference_mapped {D : ℕ} {B : XYBox D}
    (θ : SurfaceXY.XYAngleConfig B) (b : XYBond B) :
    SurfaceXY.xyBondDifference θ b =
      FroehlichSpencer.FS82.XY.xyBondDifference (sourceConfigEquiv B θ) (sourceBondEquiv B b) := by
  unfold SurfaceXY.xyBondDifference FroehlichSpencer.FS82.XY.xyBondDifference
  rw [sourceBoundary_eq_internal]
  have hb : (sourceBondEquiv B b).1 = b.1 := rfl
  rw [hb]
  unfold SurfaceXY.xyCircleChainPairing FroehlichSpencer.FS82.XY.xyCircleChainPairing
  have hf : SurfaceXY.xyAngleCochain θ =
      FroehlichSpencer.FS82.XY.xyAngleCochain (sourceConfigEquiv B θ) := by
    funext c
    exact sourceAngleCochain_mapped θ c
  rw [hf]

theorem sourceDensity_mapped {D : ℕ} {B : XYBox D} (β : ℝ)
    (hβ : 0 < β) (θ : SurfaceXY.XYAngleConfig B) :
    SurfaceXY.xyVillainDensity (B := B) β θ =
      FroehlichSpencer.FS82.XY.xyVillainDensity β (sourceConfigEquiv B θ) := by
  unfold SurfaceXY.xyVillainDensity FroehlichSpencer.FS82.XY.xyVillainDensity
  calc
    (∏ b : XYBond B, xyVillainWeight β (SurfaceXY.xyBondDifference θ b)) =
        ∏ b : XYBond B,
          FroehlichSpencer.FS82.Wilson.villainCircleWeight β
            (FroehlichSpencer.FS82.XY.xyBondDifference
              (sourceConfigEquiv B θ) (sourceBondEquiv B b)) := by
          apply Finset.prod_congr rfl
          intro b hb
          rw [sourceBondDifference_mapped]
          exact sourceWeight_eq_internal β hβ _
    _ = ∏ b : FroehlichSpencer.FS82.XY.XYBonds B,
          FroehlichSpencer.FS82.Wilson.villainCircleWeight β
            (FroehlichSpencer.FS82.XY.xyBondDifference (sourceConfigEquiv B θ) b) := by
          simpa using (Equiv.prod_comp (sourceBondEquiv B)
            (fun b : FroehlichSpencer.FS82.XY.XYBonds B =>
              FroehlichSpencer.FS82.Wilson.villainCircleWeight β
                (FroehlichSpencer.FS82.XY.xyBondDifference (sourceConfigEquiv B θ) b)))

theorem sourcePartition_eq_internal {D : ℕ} {B : XYBox D} (β : ℝ) (hβ : 0 < β) :
    SurfaceXY.xyVillainPartition (B := B) β =
      FroehlichSpencer.FS82.XY.xyVillainPartition (B := B) β := by
  unfold SurfaceXY.xyVillainPartition FroehlichSpencer.FS82.XY.xyVillainPartition
  rw [internalVolume_eq_pi B]
  calc
    (∫ θ : SurfaceXY.XYAngleConfig B, SurfaceXY.xyVillainDensity (B := B) β θ
        ∂xyAngleHaarMeasure B) =
        ∫ θ : SurfaceXY.XYAngleConfig B,
          FroehlichSpencer.FS82.XY.xyVillainDensity β (sourceConfigEquiv B θ)
            ∂xyAngleHaarMeasure B := by
              apply integral_congr_ae
              filter_upwards with θ
              exact sourceDensity_mapped β hβ θ
    _ = ∫ θ : FroehlichSpencer.FS82.XY.XYAngleConfig B,
          FroehlichSpencer.FS82.XY.xyVillainDensity β θ
          ∂(Measure.pi fun _ : FroehlichSpencer.FS82.XY.XYSites B =>
            AddCircle.haarAddCircle) :=
          (sourceHaar_measurePreserving B).integral_comp' _

theorem sourceSpinDot_mapped {D : ℕ} {B : XYBox D}
    (θ : SurfaceXY.XYAngleConfig B) (x y : XYSite B) :
    xySpinDot θ x y = FroehlichSpencer.FS82.XY.xyEndpointCos
      (sourceConfigEquiv B θ) (sourceSiteEquiv B x) (sourceSiteEquiv B y) := by
  have hx : (sourceConfigEquiv B θ) (sourceSiteEquiv B x) = θ x := by
    change θ ((sourceSiteEquiv B).symm (sourceSiteEquiv B x)) = θ x
    simp
  have hy : (sourceConfigEquiv B θ) (sourceSiteEquiv B y) = θ y := by
    change θ ((sourceSiteEquiv B).symm (sourceSiteEquiv B y)) = θ y
    simp
  simp [xySpinDot, xySpinCharacter, FroehlichSpencer.FS82.XY.xyEndpointCos,
    FroehlichSpencer.FS82.XY.xyEndpointCharacter, hx, hy]

theorem sourceSpinCorrelation_eq_internal {D : ℕ} {B : XYBox D}
    (β : ℝ) (hβ : 0 < β) (x y : XYSite B) :
    xySpinCorrelation (B := B) β x y =
      FroehlichSpencer.FS82.XY.xyEndpointCosExpectation β
        (sourceSiteEquiv B x) (sourceSiteEquiv B y) := by
  unfold xySpinCorrelation FroehlichSpencer.FS82.XY.xyEndpointCosExpectation
    FroehlichSpencer.FS82.XY.xyEndpointCosNumerator
  rw [sourcePartition_eq_internal β hβ]
  congr 1
  rw [internalVolume_eq_pi B]
  calc
    (∫ θ : SurfaceXY.XYAngleConfig B,
      SurfaceXY.xyVillainDensity (B := B) β θ * xySpinDot θ x y ∂xyAngleHaarMeasure B) =
        ∫ θ : SurfaceXY.XYAngleConfig B,
          FroehlichSpencer.FS82.XY.xyVillainDensity β (sourceConfigEquiv B θ) *
            FroehlichSpencer.FS82.XY.xyEndpointCos (sourceConfigEquiv B θ)
              (sourceSiteEquiv B x) (sourceSiteEquiv B y) ∂xyAngleHaarMeasure B := by
                apply integral_congr_ae
                filter_upwards with θ
                rw [sourceDensity_mapped β hβ θ, sourceSpinDot_mapped]
    _ = ∫ θ : FroehlichSpencer.FS82.XY.XYAngleConfig B,
          FroehlichSpencer.FS82.XY.xyVillainDensity β θ *
            FroehlichSpencer.FS82.XY.xyEndpointCos θ
              (sourceSiteEquiv B x) (sourceSiteEquiv B y)
          ∂(Measure.pi fun _ : FroehlichSpencer.FS82.XY.XYSites B =>
            AddCircle.haarAddCircle) :=
          (sourceHaar_measurePreserving B).integral_comp'
            (fun θ : FroehlichSpencer.FS82.XY.XYAngleConfig B =>
              FroehlichSpencer.FS82.XY.xyVillainDensity β θ *
                FroehlichSpencer.FS82.XY.xyEndpointCos θ
                  (sourceSiteEquiv B x) (sourceSiteEquiv B y))

/-! ## The literal law: positivity, normalization, expectation -/

theorem literalDensity_eq_comp {D : ℕ} {B : XYBox D} (β : ℝ) (hβ : 0 < β) :
    (fun θ : SurfaceXY.XYAngleConfig B => SurfaceXY.xyVillainDensity (B := B) β θ) =
      fun θ => FroehlichSpencer.FS82.XY.xyVillainDensity β (sourceConfigEquiv B θ) :=
  funext (sourceDensity_mapped β hβ)

theorem literalDensity_pos {D : ℕ} {B : XYBox D} (β : ℝ) (hβ : 0 < β)
    (θ : SurfaceXY.XYAngleConfig B) : 0 < SurfaceXY.xyVillainDensity (B := B) β θ := by
  rw [sourceDensity_mapped β hβ θ]
  exact FroehlichSpencer.FS82.XY.xyVillainDensity_pos β _ hβ

theorem literalDensity_measurable {D : ℕ} {B : XYBox D} (β : ℝ) (hβ : 0 < β) :
    Measurable fun θ : SurfaceXY.XYAngleConfig B => SurfaceXY.xyVillainDensity (B := B) β θ := by
  rw [literalDensity_eq_comp β hβ]
  exact (FroehlichSpencer.FS82.XY.xyVillainDensity_continuous (B := B) β).measurable.comp
    (sourceConfigEquiv B).measurable

theorem literalDensity_integrable {D : ℕ} {B : XYBox D} (β : ℝ) (hβ : 0 < β) :
    Integrable (fun θ : SurfaceXY.XYAngleConfig B => SurfaceXY.xyVillainDensity (B := B) β θ)
      (xyAngleHaarMeasure B) := by
  rw [literalDensity_eq_comp β hβ]
  have hint := FroehlichSpencer.FS82.XY.xyVillainPartition_integrable (B := B) β
  rw [internalVolume_eq_pi B] at hint
  exact ((sourceHaar_measurePreserving B).integrable_comp_emb
    (sourceConfigEquiv B).measurableEmbedding).mpr hint

/-- **Provider of the gate `xyVillainPartition_pos`.** -/
theorem xyVillainPartition_pos {D : ℕ} (B : XYBox D) (β : ℝ) (hβ : 0 < β) :
    0 < SurfaceXY.xyVillainPartition (B := B) β := by
  rw [sourcePartition_eq_internal β hβ]
  exact FroehlichSpencer.FS82.XY.xyVillainPartition_pos β hβ

/-- **Provider of the gate `xyVillainLaw_isProbabilityMeasure`.** -/
theorem xyVillainLaw_isProbabilityMeasure {D : ℕ} (B : XYBox D) (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure (xyVillainLaw (B := B) β hβ) := by
  have hZ := xyVillainPartition_pos B β hβ
  have hint := literalDensity_integrable (B := B) β hβ
  have hnonneg : ∀ θ : SurfaceXY.XYAngleConfig B,
      0 ≤ SurfaceXY.xyVillainDensity (B := B) β θ / SurfaceXY.xyVillainPartition (B := B) β :=
    fun θ => div_nonneg (literalDensity_pos β hβ θ).le hZ.le
  refine ⟨?_⟩
  unfold xyVillainLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hint.div_const _) (ae_of_all _ hnonneg),
    integral_div]
  change ENNReal.ofReal (SurfaceXY.xyVillainPartition (B := B) β /
    SurfaceXY.xyVillainPartition (B := B) β) = 1
  rw [div_self hZ.ne', ENNReal.ofReal_one]

/-- **Provider of the gate `xySpinCorrelation_eq_integral`.** -/
theorem xySpinCorrelation_eq_integral {D : ℕ} (B : XYBox D) (β : ℝ) (hβ : 0 < β)
    (x y : XYSite B) :
    xySpinCorrelation β x y =
      ∫ θ : SurfaceXY.XYAngleConfig B, xySpinDot θ x y ∂xyVillainLaw (B := B) β hβ := by
  have hZ := xyVillainPartition_pos B β hβ
  have hmeas : Measurable fun θ : SurfaceXY.XYAngleConfig B => ENNReal.ofReal
      (SurfaceXY.xyVillainDensity (B := B) β θ / SurfaceXY.xyVillainPartition (B := B) β) :=
    ((literalDensity_measurable β hβ).div_const _).ennreal_ofReal
  unfold xySpinCorrelation xyVillainLaw
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun θ => ENNReal.ofReal_lt_top), ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  have hnonneg : 0 ≤ SurfaceXY.xyVillainDensity (B := B) β θ /
      SurfaceXY.xyVillainPartition (B := B) β := div_nonneg (literalDensity_pos β hβ θ).le hZ.le
  simp only [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]
  ring

/-! ## The roots -/


theorem fs82_xy_spinCorrelation_root :
    ∀ D : ℕ, 3 ≤ D →
      ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 ≤ C ∧
        ∀ β : ℝ, β₀ ≤ β → ∀ N : ℕ,
          ∀ x y : XYSite (xyCubeFamily D N),
            Real.exp (-(C / β)) ≤ xySpinCorrelation β x y := by
  intro D hD
  obtain ⟨β₀, C, hβ₀, hC, hroot⟩ :=
    FroehlichSpencer.FS82.XY.DualD.fs82_xyD_spinCorrelation_root hD
  refine ⟨β₀, C, hβ₀, hC.le, ?_⟩
  intro β hβ N x y
  have hβpos : 0 < β := lt_of_lt_of_le hβ₀ hβ
  have h := hroot β hβ (xyCubeFamily D N) (by intro i j; rfl)
    (sourceSiteEquiv (xyCubeFamily D N) x) (sourceSiteEquiv (xyCubeFamily D N) y)
  simpa only [sourceSpinCorrelation_eq_internal β hβpos x y] using h


end
end FroehlichSpencer.FS82.SurfaceXYBridge

end
