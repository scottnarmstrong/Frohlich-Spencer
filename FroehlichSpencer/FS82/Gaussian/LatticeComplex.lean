/- The physical Λ* complex and its lattice Gaussian. -/
module

public import FroehlichSpencer.FS82.Gaussian.LatticeOperator
public import FroehlichSpencer.FS82.Gaussian.SourceGaussian
public import FroehlichSpencer.FS82.Gaussian.LatticePath

/-!
# The finite lattice one-form complex

The physical Λ* link coordinates carry the source complex after the C2
orientation involution. Its form Laplacian is the compressed physical lattice
stencil, so the generic finite Hodge and quotient-Gaussian construction applies.
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open FroehlichSpencer.FS82.Cubical
open scoped InnerProductSpace

@[expose] noncomputable def sourceDualTLinear {B : SourceBox} :
    EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualOneCells B) :=
  finsuppToEuclidean.comp
    ((sourceDualTMap (B := B)).comp euclideanToFinsupp)

@[simp] theorem sourceDualTLinear_apply {B : SourceBox}
    (x : EuclideanSpace ℝ (SourceDualOneCells B))
    (e : SourceDualOneCells B) :
    sourceDualTLinear x e = dualCellOrientationSign e.1 * x e := by
  simp [sourceDualTLinear, sourceDualTMap_apply]

theorem dualCellOrientationSign_sq {B : SourceBox}
    (e : SourceDualOneCells B) : dualCellOrientationSign e.1 ^ 2 = 1 := by
  unfold dualCellOrientationSign axisSetOrientationSign
  rw [pow_two, ← mul_pow]
  norm_num

theorem sourceDualTLinear_involutive {B : SourceBox} :
    (sourceDualTLinear (B := B)).comp (sourceDualTLinear (B := B)) =
      (LinearMap.id : EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ]
        EuclideanSpace ℝ (SourceDualOneCells B)) := by
  apply LinearMap.ext
  intro x
  ext e
  rw [LinearMap.comp_apply, sourceDualTLinear_apply, sourceDualTLinear_apply]
  calc
    dualCellOrientationSign e.1 *
        (dualCellOrientationSign e.1 * x e) =
      (dualCellOrientationSign e.1 ^ 2) * x e := by ring
    _ = x e := by rw [dualCellOrientationSign_sq]; norm_num

theorem sourceDualTLinear_apply_apply {B : SourceBox}
    (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sourceDualTLinear (sourceDualTLinear x) = x := by
  have h := congrArg (fun T : EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ]
    EuclideanSpace ℝ (SourceDualOneCells B) => T x)
    (sourceDualTLinear_involutive (B := B))
  simpa [LinearMap.comp_apply] using h

theorem sourceDualTLinear_symmetric {B : SourceBox} :
    (sourceDualTLinear (B := B)).IsSymmetric := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro e he
  simp [sourceDualTLinear_apply]
  ring

@[expose] noncomputable def latticeStencilOperator {B : SourceBox}
    (origin : Fin 4 → ℤ) :
    EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualOneCells B) :=
  finsuppToEuclidean.comp
    ((Cubical.piLambdaStarDeltaDReal (B := B) origin).comp euclideanToFinsupp)

@[expose] noncomputable def latticeExactOneComplex {B : SourceBox}
    (_origin : Fin 4 → ℤ) :
    ExactOneComplex (SourceDualZeroCells B) (SourceDualOneCells B)
      (SourceDualTwoCells B) where
  d₀ := (sourceDualTLinear (B := B)).comp sourceDualD₀
  d₁ := sourceDualD₁.comp (sourceDualTLinear (B := B))
  complex := by
    apply LinearMap.ext
    intro u
    change sourceDualD₁
      (sourceDualTLinear (sourceDualTLinear (sourceDualD₀ u))) = 0
    rw [sourceDualTLinear_apply_apply]
    have h := congrArg (fun F : EuclideanSpace ℝ (SourceDualZeroCells B) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualTwoCells B) => F u)
      (sourceDualD₁_comp_D₀_zero (B := B))
    simpa [LinearMap.comp_apply] using h
  exactOne := by
    intro x hx
    have hD : sourceDualD₁ (sourceDualTLinear x) = 0 :=
      LinearMap.mem_ker.mp hx
    have hExact := (sourceDualComplex (B := B)).exactOne
      (LinearMap.mem_ker.mpr hD)
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hExact
    refine ⟨u, ?_⟩
    have hxx := sourceDualTLinear_apply_apply x
    have hu' : sourceDualD₀ u = sourceDualTLinear x := by
      simpa [sourceDualComplex] using hu
    calc
      (sourceDualTLinear (B := B)) (sourceDualD₀ u) =
          sourceDualTLinear (sourceDualTLinear x) := by rw [hu']
      _ = x := hxx

theorem latticeFormLaplacian_eq_stencil {B : SourceBox}
    (origin : Fin 4 → ℤ) :
    formLaplacian (latticeExactOneComplex (B := B) origin) =
      latticeStencilOperator (B := B) origin := by
  have hTadj : (sourceDualTLinear (B := B)).adjoint = sourceDualTLinear :=
    sourceDualTLinear_symmetric.adjoint_eq
  have hsource := sourceDualFiniteOperator_eq_conj_piLambdaStarDeltaDReal
    (B := B) origin
  have hsource' : sourceDualFiniteOperator (B := B) =
      ((sourceDualTLinear (B := B)).comp
        (latticeStencilOperator (B := B) origin)).comp
          (sourceDualTLinear (B := B)) := by
    rw [hsource]
    apply LinearMap.ext
    intro x
    ext e
    simp [sourceDualTLinear, latticeStencilOperator, LinearMap.comp_apply]
  change ((sourceDualD₁.comp sourceDualTLinear).adjoint.comp
      (sourceDualD₁.comp sourceDualTLinear)) = latticeStencilOperator (B := B) origin
  rw [LinearMap.adjoint_comp, hTadj]
  change ((sourceDualTLinear (B := B)).comp
      (sourceDualFiniteOperator (B := B))).comp
        (sourceDualTLinear (B := B)) = latticeStencilOperator (B := B) origin
  apply LinearMap.ext
  intro x
  change sourceDualTLinear (sourceDualFiniteOperator (sourceDualTLinear x)) =
    latticeStencilOperator (B := B) origin x
  rw [hsource']
  simp only [LinearMap.comp_apply]
  rw [sourceDualTLinear_apply_apply x, sourceDualTLinear_apply_apply]

theorem latticeStencil_mem_coClosed {B : SourceBox}
    (origin : Fin 4 → ℤ) (μ : EuclideanSpace ℝ (SourceDualOneCells B)) :
    latticeStencilOperator (B := B) origin μ ∈
      coClosed (latticeExactOneComplex (B := B) origin) := by
  rw [← latticeFormLaplacian_eq_stencil]
  exact formLaplacian_mem_coClosed (latticeExactOneComplex (B := B) origin) μ

/-- The covariance `V_Λ` on the lattice co-closed one-forms: the inverse of
the compressed lattice form Laplacian. -/
@[expose] noncomputable def latticeVΛ {B : SourceBox}
    (origin : Fin 4 → ℤ) :
    coClosed (latticeExactOneComplex (B := B) origin) →ₗ[ℝ]
      coClosed (latticeExactOneComplex (B := B) origin) :=
  hodgeInverseOnCoClosed (latticeExactOneComplex (B := B) origin)

theorem latticeVΛ_is_inverse {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (μ : coClosed (latticeExactOneComplex (B := B) origin)) :
    hodgeOnCoClosed (latticeExactOneComplex (B := B) origin)
        (latticeVΛ (B := B) origin μ) = μ := by
  exact hodgeOnCoClosed_hodgeInverse
    (latticeExactOneComplex (B := B) origin) μ

theorem latticeVΛ_inverse_stencil {B : SourceBox}
    (origin : Fin 4 → ℤ)
    (μ : coClosed (latticeExactOneComplex (B := B) origin)) :
    latticeStencilOperator (B := B) origin
        (latticeVΛ (B := B) origin μ :
          EuclideanSpace ℝ (SourceDualOneCells B)) =
      (μ : EuclideanSpace ℝ (SourceDualOneCells B)) := by
  have h := congrArg
    (fun z : coClosed (latticeExactOneComplex (B := B) origin) =>
      (z : EuclideanSpace ℝ (SourceDualOneCells B)))
    (latticeVΛ_is_inverse (B := B) origin μ)
  change formLaplacian (latticeExactOneComplex (B := B) origin)
      (latticeVΛ (B := B) origin μ :
        EuclideanSpace ℝ (SourceDualOneCells B)) =
    (μ : EuclideanSpace ℝ (SourceDualOneCells B)) at h
  rw [latticeFormLaplacian_eq_stencil] at h
  exact h


@[expose] noncomputable def latticeQuotientGaussian {B : SourceBox}
    (origin : Fin 4 → ℤ) (β : ℝ) (hβ : 0 ≤ β) :=
  finiteComplexQuotientGaussian (latticeExactOneComplex (B := B) origin) β hβ


theorem latticeQuotientGaussian_characteristic {B : SourceBox}
    (origin : Fin 4 → ℤ) {β : ℝ} (hβ : 0 ≤ β)
    (μ : coClosed (latticeExactOneComplex (B := B) origin)) :
    MeasureTheory.charFun
      (MeasureTheory.Measure.map
        (finiteComplexQuotientTestFunctional
          (latticeExactOneComplex (B := B) origin) μ)
        (latticeQuotientGaussian (B := B) origin β hβ)) 1 =
      Complex.exp (-↑(inner ℝ (μ : EuclideanSpace ℝ (SourceDualOneCells B))
        ((β • hodgeInverseOnCoClosed
          (latticeExactOneComplex (B := B) origin)) μ :
          EuclideanSpace ℝ (SourceDualOneCells B)) / 2)) := by
  have h := finiteComplexQuotientGaussian_charFunDual
    (latticeExactOneComplex (B := B) origin) hβ μ
  simpa [latticeQuotientGaussian, finiteComplexAmbientCovariance_coClosed_apply] using h

/-- The quotient characteristic in the source's `V_Λ` notation. -/
theorem latticeQuotientGaussian_characteristic_VΛ {B : SourceBox}
    (origin : Fin 4 → ℤ) {β : ℝ} (hβ : 0 ≤ β)
    (μ : coClosed (latticeExactOneComplex (B := B) origin)) :
    MeasureTheory.charFun
      (MeasureTheory.Measure.map
        (finiteComplexQuotientTestFunctional
          (latticeExactOneComplex (B := B) origin) μ)
        (latticeQuotientGaussian (B := B) origin β hβ)) 1 =
      Complex.exp (-↑((β / 2) * inner ℝ
        (μ : EuclideanSpace ℝ (SourceDualOneCells B))
        (latticeVΛ (B := B) origin μ :
          EuclideanSpace ℝ (SourceDualOneCells B)))) := by
  rw [latticeQuotientGaussian_characteristic]
  congr 1
  simp only [LinearMap.smul_apply, latticeVΛ]
  rw [show ((β • (hodgeInverseOnCoClosed
      (latticeExactOneComplex (B := B) origin)) μ :
        coClosed (latticeExactOneComplex (B := B) origin)) :
          EuclideanSpace ℝ (SourceDualOneCells B)) =
      β • ((hodgeInverseOnCoClosed
        (latticeExactOneComplex (B := B) origin) μ :
          coClosed (latticeExactOneComplex (B := B) origin)) :
            EuclideanSpace ℝ (SourceDualOneCells B)) by rfl]
  rw [real_inner_smul_right]
  ring_nf

theorem sourceDualD₀_coefficient {B : SourceBox}
    (u : EuclideanSpace ℝ (SourceDualZeroCells B))
    (e : SourceDualOneCells B) :
    sourceDualD₀ u e =
      Cubical.dualExteriorDifference (sourceDualZeroToChain u)
        (sourceDualOneEmbedding e) := by
  simp [sourceDualD₀, LinearMap.comp_apply, compressDualSubtype_apply]


end FroehlichSpencer.FS82.Gaussian

end
