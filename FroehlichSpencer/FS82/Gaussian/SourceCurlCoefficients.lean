/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.SourceGaussian
public import FroehlichSpencer.FS82.Gaussian.SelectedLinkQuadratic

/-!
# Source curl coefficients

The source differential on edge fields is represented by its oriented
plaquette-link coefficient matrix.

This module connects it to generic
curl-energy algebra.
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open scoped BigOperators InnerProductSpace

variable {B : SourceBox}

/-- The oriented coefficient of a source link in the curl of a source plaquette. -/
noncomputable def sourceCurlCoefficient (p : SourceDualTwoCells B)
    (e : SourceDualOneCells B) : ℝ :=
  sourceDualD₁ (EuclideanSpace.single e 1) p

theorem sourceCurlCoefficient_eq_dualExteriorDifference
    (p : SourceDualTwoCells B) (e : SourceDualOneCells B) :
    sourceCurlCoefficient p e =
      Cubical.dualExteriorDifference
        (Finsupp.single (sourceDualOneEmbedding e) (1 : ℝ))
        (sourceDualTwoEmbedding p) := by
  have hs : sourceDualOneToChain (EuclideanSpace.single e 1) =
      Finsupp.single (sourceDualOneEmbedding e) (1 : ℝ) := by
    ext c
    simp [sourceDualOneToChain, embedDualSubtype, euclideanToFinsupp]
  have h := congrArg (fun q : Cubical.DualRealChain 4 B =>
    q (sourceDualTwoEmbedding p))
    (sourceDualD₁_embed_eq_derivative (EuclideanSpace.single e 1))
  rw [hs] at h
  simpa [sourceCurlCoefficient, sourceDualTwoToChain, LinearMap.comp_apply,
    Finsupp.single_apply] using h

theorem sourceCurlCoefficient_eq_coordinateStencil
    (p : SourceDualTwoCells B) (e : SourceDualOneCells B) :
    sourceCurlCoefficient p e =
      Cubical.dualExteriorDifferenceStencilBasis
        (sourceDualOneEmbedding e) (sourceDualTwoEmbedding p) := by
  rw [sourceCurlCoefficient_eq_dualExteriorDifference,
    Cubical.dualExteriorDifference_eq_coordinateStencil,
    Cubical.dualExteriorDifferenceStencil, Finsupp.linearCombination_single]
  simp

theorem sourceDualD₁_eq_sourceCurl_sum
    (x : EuclideanSpace ℝ (SourceDualOneCells B))
    (p : SourceDualTwoCells B) :
    sourceDualD₁ x p =
      ∑ e : SourceDualOneCells B, sourceCurlCoefficient p e * x e := by
  classical
  have hre : x = ∑ e : SourceDualOneCells B, x e • EuclideanSpace.single e 1 := by
    have h := (EuclideanSpace.basisFun (SourceDualOneCells B) ℝ).sum_repr x
    simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using h.symm
  calc
    sourceDualD₁ x p = sourceDualD₁
        (∑ e : SourceDualOneCells B, x e • EuclideanSpace.single e 1) p := by
          exact congrArg (fun y : EuclideanSpace ℝ (SourceDualTwoCells B) => y p)
            (congrArg sourceDualD₁ hre)
    _ = (∑ e : SourceDualOneCells B,
        sourceDualD₁ (x e • EuclideanSpace.single e 1)) p := by rw [map_sum]
    _ = ∑ e : SourceDualOneCells B, sourceCurlCoefficient p e * x e := by
      simp [sourceCurlCoefficient, smul_eq_mul, mul_comm]


end FroehlichSpencer.FS82.Gaussian
end
