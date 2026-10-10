/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import FroehlichSpencer.FS82.Currents.ActivityRate
public import FroehlichSpencer.FS82.Moment.CurrentDecay

public import FroehlichSpencer.FS82.Moment.RowSum
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

/-!
# FS82 SourceCoercivity: concrete source coercivity and the current decay estimate

The finite row estimate is derived from the cubical stencil: a link is in at
most six plaquettes and each plaquette has four sides. The resulting bound
is uniform over every rectangular box.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Moment.SourceCoercivity

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Moment.Coercivity
open FroehlichSpencer.FS82.Moment.CurrentDecay
open Classical

noncomputable section


private noncomputable def sourceRealCurrentVector {B : SourceBox}
    (j : IntegerCurrent B) : EuclideanSpace ℝ (SourceDualOneCells B) :=
  finsuppToEuclidean
    (compressDualSubtype sourceDualOneEmbedding (realCurrent j))

noncomputable def sourcePhysicalCurrentVector {B : SourceBox}
    (j : IntegerCurrent B) : EuclideanSpace ℝ (SourceDualOneCells B) :=
  finsuppToEuclidean
    (compressDualSubtype sourceDualOneEmbedding (physicalCurrent j))

private theorem sourceRealCurrentVector_apply {B : SourceBox}
    (j : IntegerCurrent B) (e : SourceDualOneCells B) :
    sourceRealCurrentVector j e = (j e : ℝ) := by
  simp only [sourceRealCurrentVector, finsuppToEuclidean_apply,
    compressDualSubtype_apply, realCurrent]
  change Finsupp.embDomain
      (⟨Subtype.val, Subtype.val_injective⟩ : Link B ↪ Cubical.DualCell 4 B)
      _ ((⟨Subtype.val, Subtype.val_injective⟩ :
        Link B ↪ Cubical.DualCell 4 B) e) = _
  rw [Finsupp.embDomain_apply_self]
  simp

private theorem sourcePhysicalCurrentVector_apply {B : SourceBox}
    (j : IntegerCurrent B) (e : SourceDualOneCells B) :
    sourcePhysicalCurrentVector j e = (2 * Real.pi) * (j e : ℝ) := by
  simp only [sourcePhysicalCurrentVector, finsuppToEuclidean_apply,
    compressDualSubtype_apply, physicalCurrent]
  change Finsupp.embDomain
      (⟨Subtype.val, Subtype.val_injective⟩ : Link B ↪ Cubical.DualCell 4 B)
      _ ((⟨Subtype.val, Subtype.val_injective⟩ :
        Link B ↪ Cubical.DualCell 4 B) e) = _
  rw [Finsupp.embDomain_apply_self]
  simp

private theorem sourcePhysicalCurrentVector_eq_smul {B : SourceBox}
    (j : IntegerCurrent B) :
    sourcePhysicalCurrentVector j = (2 * Real.pi) • sourceRealCurrentVector j := by
  ext e
  simp [sourcePhysicalCurrentVector_apply, sourceRealCurrentVector_apply,
    smul_eq_mul]


private theorem sourceDualD₀_adjoint_single_apply {B : SourceBox}
    (e : SourceDualOneCells B) (v : SourceDualZeroCells B) :
    sourceDualD₀.adjoint (EuclideanSpace.single e (1 : ℝ)) v =
      Cubical.dualExteriorDifference (Finsupp.single v.1 (1 : ℝ)) e.1 := by
  calc
    sourceDualD₀.adjoint (EuclideanSpace.single e (1 : ℝ)) v =
        inner ℝ (EuclideanSpace.single v (1 : ℝ))
          (sourceDualD₀.adjoint (EuclideanSpace.single e (1 : ℝ))) := by
      rw [EuclideanSpace.inner_single_left]
      simp
    _ = inner ℝ (sourceDualD₀ (EuclideanSpace.single v (1 : ℝ)))
          (EuclideanSpace.single e (1 : ℝ)) :=
        sourceDualD₀.adjoint_inner_right _ _
    _ = sourceDualD₀ (EuclideanSpace.single v (1 : ℝ)) e := by
      rw [EuclideanSpace.inner_single_right]
      simp
    _ = Cubical.dualExteriorDifference
          (Finsupp.single v.1 (1 : ℝ)) e.1 := by
      simp [sourceDualD₀, LinearMap.comp_apply, sourceDualZeroToChain,
        sourceDualOneEmbedding, sourceDualZeroEmbedding,
        euclideanToFinsupp_single, embedDualSubtype_apply_single]

private theorem sourceRealCurrentVector_add {B : SourceBox}
    (j k : IntegerCurrent B) :
    sourceRealCurrentVector (j + k) =
      sourceRealCurrentVector j + sourceRealCurrentVector k := by
  ext e
  simp [sourceRealCurrentVector_apply, Finsupp.add_apply, Int.cast_add]

private theorem sourceRealCurrentVector_single {B : SourceBox}
    (e : SourceDualOneCells B) (n : ℤ) :
    sourceRealCurrentVector (Finsupp.single e n) =
      (n : ℝ) • EuclideanSpace.single e (1 : ℝ) := by
  ext f
  simp [sourceRealCurrentVector_apply, EuclideanSpace.single,
    Finsupp.single_apply, eq_comm]

private theorem sourceDualD₀_adjoint_realCurrentVector_eq_divergence
    {B : SourceBox} (j : IntegerCurrent B) (v : SourceDualZeroCells B) :
    sourceDualD₀.adjoint (sourceRealCurrentVector j) v =
      currentDivergence j v := by
  induction j using Finsupp.induction_linear with
  | zero => simp [sourceRealCurrentVector, currentDivergence, realCurrent]
  | add j k hj hk =>
      calc
        sourceDualD₀.adjoint (sourceRealCurrentVector (j + k)) v =
            (sourceDualD₀.adjoint (sourceRealCurrentVector j) +
              sourceDualD₀.adjoint (sourceRealCurrentVector k)) v := by
          rw [sourceRealCurrentVector_add, map_add]
        _ = currentDivergence (j + k) v := by
          rw [PiLp.add_apply, hj, hk, currentDivergence_add]
  | single e n =>
      rw [sourceRealCurrentVector_single, map_smul]
      simp [smul_eq_mul, sourceDualD₀_adjoint_single_apply,
        currentDivergence_single, mul_comm]

theorem sourcePhysicalCurrentVector_mem_coClosed_of_divergence_zero
    {B : SourceBox} (origin : Fin 4 → ℤ) (j : IntegerCurrent B)
    (hdiv : currentDivergence j = 0) :
    sourceDualTLinear (sourcePhysicalCurrentVector j) ∈
      coClosed (latticeExactOneComplex (B := B) origin) := by
  rw [coClosed, LinearMap.mem_ker]
  let T := sourceDualTLinear (B := B)
  let D₀ := sourceDualD₀ (B := B)
  let C := latticeExactOneComplex (B := B) origin
  have hreal : D₀.adjoint (sourceRealCurrentVector j) = 0 := by
    ext v
    rw [sourceDualD₀_adjoint_realCurrentVector_eq_divergence, hdiv]
    rfl
  have hTadj : T.adjoint = T := by
    simpa [T] using sourceDualTLinear_symmetric.adjoint_eq
  change C.d₀.adjoint (T (sourcePhysicalCurrentVector j)) = 0
  have hC : C.d₀ = T.comp D₀ := by rfl
  rw [hC, LinearMap.adjoint_comp, hTadj]
  rw [LinearMap.comp_apply, sourceDualTLinear_apply_apply]
  rw [sourcePhysicalCurrentVector_eq_smul, map_smul, hreal]
  simp

noncomputable def sourcePhysicalCurrentCoClosed {B : SourceBox}
    (origin : Fin 4 → ℤ) (j : IntegerCurrent B)
    (hdiv : currentDivergence j = 0) :
    coClosed (latticeExactOneComplex (B := B) origin) :=
  ⟨sourceDualTLinear (sourcePhysicalCurrentVector j),
    sourcePhysicalCurrentVector_mem_coClosed_of_divergence_zero
      origin j hdiv⟩


end
end FroehlichSpencer.FS82.Moment.SourceCoercivity

end
