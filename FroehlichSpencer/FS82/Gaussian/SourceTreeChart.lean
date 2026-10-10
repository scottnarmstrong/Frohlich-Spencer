/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.SourceModel
public import FroehlichSpencer.FS82.Gaussian.TreeGaugeQuotient
public import FroehlichSpencer.FS82.Gaussian.SourceCurlCoefficients

/-!
# The source Gaussian quotient in a source tree chart

The source dual coordinates differ from physical link coordinates by the
source orientation involution. This module records the compatible endpoint
interface and transports the exact source kernel through that involution.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Gaussian.SourceTreeChart

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Gaussian.TreeGaugeQuotient

variable {B : SourceBox}


/-- The source-graph coboundary, represented in Euclidean link coordinates. -/
noncomputable def treeGradientEuclidean
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B)) :
    (SourcePoissonVertex B → ℝ) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualOneCells B) where
  toFun p := WithLp.toLp 2 (fun e => T.coboundary p e)
  map_add' p q := by
    ext e
    simp [RootedTreeGauge.coboundary, sub_add_sub_comm]
  map_smul' r p := by
    ext e
    simp [RootedTreeGauge.coboundary, mul_sub]

/-- The physical source D₀ range is the gradient range for any rooted tree
with the source graph's endpoint maps. -/
theorem sourceLatticeD₀_range_eq_treeGradient
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    LinearMap.range ((sourceDualTLinear (B := B)).comp
      (sourceDualD₀ (B := B))) =
        LinearMap.range (treeGradientEuclidean (B := B) T) := by
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    obtain ⟨p, hp⟩ := (sourceLatticeD0_range_eq_treeCoboundary
      (B := B) (fun _ => 0)
      ((sourceDualTLinear (B := B)).comp (sourceDualD₀ (B := B)) u)).mp
        ⟨u, rfl⟩
    refine ⟨p, ?_⟩
    ext e
    have heq := hp e
    change sourceTreeCoboundary B p e = _ at heq
    change p (T.edgeTarget e) - p (T.edgeSource e) = _
    rw [congrFun hT.2 e, congrFun hT.1 e]
    simpa [sourceRootedTree, sourceTreeCoboundary] using heq
  · rintro x ⟨p, rfl⟩
    have hp : ∀ e, sourceTreeCoboundary B p e =
        treeGradientEuclidean (B := B) T p e := by
      intro e
      change p (sourcePoissonEdgeUpperVertex e) -
          p (sourcePoissonEdgeLowerVertex e) =
            p (T.edgeTarget e) - p (T.edgeSource e)
      rw [congrFun hT.2 e, congrFun hT.1 e]
      rfl
    obtain ⟨u, hu⟩ := (sourceLatticeD0_range_eq_treeCoboundary
      (B := B) (fun _ => 0) (treeGradientEuclidean (B := B) T p)).mpr
        ⟨p, hp⟩
    exact ⟨u, hu⟩

/-- The raw source exact directions are the orientation transport of the
source-graph tree gradients. -/
theorem sourceDualD₀_range_eq_orientedTreeGradient
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    LinearMap.range (sourceDualD₀ (B := B)) =
      LinearMap.range ((sourceDualTLinear (B := B)).comp
        (treeGradientEuclidean (B := B) T)) := by
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    have hx : (sourceDualTLinear (B := B)) (sourceDualD₀ u) ∈
        LinearMap.range (treeGradientEuclidean (B := B) T) := by
      rw [← sourceLatticeD₀_range_eq_treeGradient T hT]
      exact ⟨u, rfl⟩
    obtain ⟨p, hp⟩ := LinearMap.mem_range.mp hx
    refine ⟨p, ?_⟩
    have hp' := congrArg (sourceDualTLinear (B := B)) hp
    simpa [LinearMap.comp_apply, sourceDualTLinear_apply_apply] using hp'
  · rintro x ⟨p, rfl⟩
    have hx : treeGradientEuclidean (B := B) T p ∈
        LinearMap.range ((sourceDualTLinear (B := B)).comp
          (sourceDualD₀ (B := B))) := by
      rw [sourceLatticeD₀_range_eq_treeGradient T hT]
      exact ⟨p, rfl⟩
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hx
    refine ⟨u, ?_⟩
    have hu' := congrArg (sourceDualTLinear (B := B)) hu
    simpa [LinearMap.comp_apply, sourceDualTLinear_apply_apply] using hu'

/-- Kernel exactness for a tree whose endpoints are the source graph's
endpoints. The source dual basis is transported by its orientation involution
before it is compared with the graph coboundary. -/
theorem sourceCurlKernel_eq_treeGradient
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    (sourceDualD₁ (B := B)).ker =
      LinearMap.range ((sourceDualTLinear (B := B)).comp
        (treeGradientEuclidean (B := B) T)) := by
  rw [sourceDualD₁_kernel_eq_sourceDualD₀_range]
  exact sourceDualD₀_range_eq_orientedTreeGradient T hT

/-- The quotient carrier of the source curl, displayed in its defining form. -/
abbrev SourceCurlQuotient (B : SourceBox) :=
  EuclideanSpace ℝ (SourceDualOneCells B) ⧸ (sourceDualD₁ (B := B)).ker

/-- Convert Euclidean link coordinates to the underlying link-indexed
function. -/
noncomputable def sourceEuclideanToFunction :
    EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ]
      SourceDualOneCells B → ℝ :=
  (EuclideanSpace.equiv (SourceDualOneCells B) ℝ).toLinearMap

/-- Convert a link-indexed function to Euclidean link coordinates. -/
noncomputable def sourceFunctionToEuclidean :
    (SourceDualOneCells B → ℝ) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualOneCells B) :=
  (EuclideanSpace.equiv (SourceDualOneCells B) ℝ).symm.toLinearMap

@[simp] theorem sourceFunctionToEuclidean_sourceEuclideanToFunction
    (x : EuclideanSpace ℝ (SourceDualOneCells B)) :
    sourceFunctionToEuclidean (B := B)
      (sourceEuclideanToFunction (B := B) x) = x := by
  change (EuclideanSpace.equiv (SourceDualOneCells B) ℝ).symm
    ((EuclideanSpace.equiv (SourceDualOneCells B) ℝ) x) = x
  exact ContinuousLinearEquiv.symm_apply_apply _ _

@[simp] theorem sourceEuclideanToFunction_sourceFunctionToEuclidean
    (x : SourceDualOneCells B → ℝ) :
    sourceEuclideanToFunction (B := B)
      (sourceFunctionToEuclidean (B := B) x) = x := by
  change (EuclideanSpace.equiv (SourceDualOneCells B) ℝ)
    ((EuclideanSpace.equiv (SourceDualOneCells B) ℝ).symm x) = x
  exact ContinuousLinearEquiv.apply_symm_apply _ _

/-- The source quotient maps to the graph gauge quotient after applying the
source orientation involution. -/
noncomputable def sourceCurlQuotientToTreeGauge
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    SourceCurlQuotient B →ₗ[ℝ] RealGaugeQuotient T := by
  let f : EuclideanSpace ℝ (SourceDualOneCells B) →ₗ[ℝ]
      RealGaugeQuotient T :=
    (LinearMap.range (realCoboundaryMap T)).mkQ.comp
      ((sourceEuclideanToFunction (B := B)).comp
        (sourceDualTLinear (B := B)))
  have hf : (sourceDualD₁ (B := B)).ker ≤ LinearMap.ker f := by
    intro x hx
    have hx' : x ∈ LinearMap.range
        ((sourceDualTLinear (B := B)).comp (treeGradientEuclidean (B := B) T)) := by
      rw [← sourceCurlKernel_eq_treeGradient T hT]
      exact hx
    obtain ⟨p, hp⟩ := LinearMap.mem_range.mp hx'
    have hp' : treeGradientEuclidean (B := B) T p =
        sourceDualTLinear (B := B) x := by
      have hh := congrArg (sourceDualTLinear (B := B)) hp
      rw [LinearMap.comp_apply, sourceDualTLinear_apply_apply] at hh
      exact hh
    apply LinearMap.mem_ker.mpr
    change (LinearMap.range (realCoboundaryMap T)).mkQ
      (sourceEuclideanToFunction (B := B) (sourceDualTLinear x)) = 0
    have hpFun : sourceEuclideanToFunction (B := B)
        (sourceDualTLinear x) = realCoboundaryMap T p := by
      ext e
      have he := congrFun
        (congrArg (EuclideanSpace.equiv (SourceDualOneCells B) ℝ) hp') e
      have hgrad : sourceEuclideanToFunction (B := B)
          (treeGradientEuclidean (B := B) T p) = realCoboundaryMap T p := by
        ext f
        rfl
      change sourceEuclideanToFunction (B := B)
          (treeGradientEuclidean (B := B) T p) e =
        sourceEuclideanToFunction (B := B) (sourceDualTLinear x) e at he
      rw [hgrad] at he
      exact he.symm
    rw [hpFun]
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range (realCoboundaryMap T))).2
      (LinearMap.mem_range.mpr ⟨p, rfl⟩)
  exact (sourceDualD₁ (B := B)).ker.liftQ f hf

/-- The graph gauge quotient maps back to the source curl quotient by applying
the same orientation involution. -/
noncomputable def treeGaugeToSourceCurlQuotient
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    RealGaugeQuotient T →ₗ[ℝ] SourceCurlQuotient B := by
  let f : (SourceDualOneCells B → ℝ) →ₗ[ℝ] SourceCurlQuotient B :=
    ((sourceDualD₁ (B := B)).ker).mkQ.comp
      ((sourceDualTLinear (B := B)).comp
        (sourceFunctionToEuclidean (B := B)))
  have hf : LinearMap.range (realCoboundaryMap T) ≤ LinearMap.ker f := by
    intro x hx
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hx
    apply LinearMap.mem_ker.mpr
    change ((sourceDualD₁ (B := B)).ker).mkQ
      (sourceDualTLinear
        (sourceFunctionToEuclidean (realCoboundaryMap T p))) = 0
    have hmem : sourceDualTLinear
        (sourceFunctionToEuclidean (realCoboundaryMap T p)) ∈
        LinearMap.range ((sourceDualTLinear (B := B)).comp
          (treeGradientEuclidean (B := B) T)) := by
      refine ⟨p, ?_⟩
      change sourceDualTLinear
          (sourceFunctionToEuclidean (realCoboundaryMap T p)) =
        sourceDualTLinear (treeGradientEuclidean (B := B) T p)
      congr 1
    have hker : sourceDualTLinear
        (sourceFunctionToEuclidean (realCoboundaryMap T p)) ∈
        (sourceDualD₁ (B := B)).ker := by
      rw [sourceCurlKernel_eq_treeGradient T hT]
      exact hmem
    exact (Submodule.Quotient.mk_eq_zero ((sourceDualD₁ (B := B)).ker)).2 hker
  exact (LinearMap.range (realCoboundaryMap T)).liftQ f hf

/-- Linear equivalence between the source curl quotient and the graph gauge
quotient for every compatible source tree. -/
noncomputable def sourceCurlQuotientTreeGaugeEquiv
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    SourceCurlQuotient B ≃ₗ[ℝ] RealGaugeQuotient T where
  toFun := sourceCurlQuotientToTreeGauge T hT
  invFun := treeGaugeToSourceCurlQuotient T hT
  left_inv := by
    intro q
    refine Submodule.Quotient.induction_on
      (p := (sourceDualD₁ (B := B)).ker) q ?_
    intro a
    simp only [sourceCurlQuotientToTreeGauge, treeGaugeToSourceCurlQuotient,
      Submodule.liftQ_apply, Submodule.mkQ_apply, LinearMap.comp_apply,
      sourceFunctionToEuclidean_sourceEuclideanToFunction,
      sourceDualTLinear_apply_apply]
  right_inv := by
    intro q
    refine Submodule.Quotient.induction_on
      (p := LinearMap.range (realCoboundaryMap T)) q ?_
    intro a
    simp only [sourceCurlQuotientToTreeGauge, treeGaugeToSourceCurlQuotient,
      Submodule.liftQ_apply, Submodule.mkQ_apply, LinearMap.comp_apply,
      sourceEuclideanToFunction_sourceFunctionToEuclidean,
      sourceDualTLinear_apply_apply]
  map_add' := (sourceCurlQuotientToTreeGauge T hT).map_add
  map_smul' := (sourceCurlQuotientToTreeGauge T hT).map_smul

/-- The literal source curl of the tree-zero representative in chord
coordinates. -/
noncomputable def sourceTreeChartCurlLinear
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B)) :
    (T.Chord → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (SourceDualTwoCells B) :=
  (sourceDualD₁ (B := B)).comp
    ((sourceFunctionToEuclidean (B := B)).comp
      (extendChordsLinear T))

/-- The oriented source curl coefficient in tree chord coordinates. -/
noncomputable def sourceTreeChartCurlCoefficient
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (p : SourceDualTwoCells B) (e : T.Chord) : ℝ :=
  sourceTreeChartCurlLinear (B := B) T (Pi.single e 1) p

/--
In chord coordinates, each coefficient is literally already
identified source curl coefficient.
-/
theorem sourceTreeChartCurlCoefficient_eq_sourceCurlCoefficient
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (p : SourceDualTwoCells B) (e : T.Chord) :
    sourceTreeChartCurlCoefficient (B := B) T p e =
      sourceCurlCoefficient p e.1 := by
  classical
  have htreeZero : ∀ v : {v : SourcePoissonVertex B // v ≠ T.root},
      extendChordsLinear T (Pi.single e 1) (T.treeEdge v) = 0 :=
    extendChordsLinear_mem_treeGauge T (Pi.single e 1)
  have hchordValue (f : SourceDualOneCells B) (hf : f ∉ Set.range T.treeEdge) :
      extendChordsLinear T (Pi.single e 1) f =
        (Pi.single e (1 : ℝ) : T.Chord → ℝ) ⟨f, hf⟩ := by
    have h := congrFun (treeChordMap_extendChords T (Pi.single e 1)) ⟨f, hf⟩
    rw [treeChordMap, LinearMap.comp_apply, treeNormalize_extendChords] at h
    change extendChordsLinear T (Pi.single e 1) f = _ at h
    exact h
  have hcoord (f : SourceDualOneCells B) :
      (sourceFunctionToEuclidean (B := B)
        (extendChordsLinear T (Pi.single e 1))) f =
          extendChordsLinear T (Pi.single e 1) f := by
    have h := congrFun (sourceEuclideanToFunction_sourceFunctionToEuclidean
      (B := B) (extendChordsLinear T (Pi.single e 1))) f
    change (sourceFunctionToEuclidean (B := B)
      (extendChordsLinear T (Pi.single e 1))) f = _ at h
    exact h
  change sourceDualD₁
      (sourceFunctionToEuclidean (B := B)
        (extendChordsLinear T (Pi.single e 1))) p = _
  rw [sourceDualD₁_eq_sourceCurl_sum]
  rw [Finset.sum_eq_single e.1]
  · rw [hcoord, hchordValue e.1 e.2]
    simp
  · intro f hf hfe
    by_cases ht : f ∈ Set.range T.treeEdge
    · obtain ⟨v, rfl⟩ := ht
      rw [hcoord, htreeZero]
      simp
    · have hval := hchordValue f ht
      have hneq : (⟨f, ht⟩ : T.Chord) ≠ e := by
        intro h
        exact hfe (congrArg Subtype.val h)
      rw [hcoord, hval]
      simp [hneq]
  · simp

/-- Finite coefficient expansion of the source curl in tree chord
coordinates. -/
theorem sourceTreeChartCurlLinear_apply
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (x : T.Chord → ℝ) (p : SourceDualTwoCells B) :
    sourceTreeChartCurlLinear (B := B) T x p =
      ∑ e : T.Chord, sourceTreeChartCurlCoefficient (B := B) T p e * x e := by
  classical
  have hx : x = ∑ e : T.Chord, x e • Pi.single e (1 : ℝ) := by
    simpa [Pi.basisFun_repr, Pi.basisFun] using
      ((Pi.basisFun ℝ T.Chord).sum_repr x).symm
  calc
    sourceTreeChartCurlLinear (B := B) T x p =
        sourceTreeChartCurlLinear (B := B) T
          (∑ e : T.Chord, x e • Pi.single e (1 : ℝ)) p :=
          congrArg (fun w => sourceTreeChartCurlLinear (B := B) T w p) hx
    _ = ∑ e : T.Chord, x e *
        sourceTreeChartCurlLinear (B := B) T (Pi.single e 1) p := by
      simp [map_sum, map_smul, smul_eq_mul]
    _ = ∑ e : T.Chord,
        sourceTreeChartCurlCoefficient (B := B) T p e * x e := by
      apply Finset.sum_congr rfl
      intro e he
      simp [sourceTreeChartCurlCoefficient, mul_comm]


/--
The chart energy is the literal source coefficient quadratic appearing in
the chart density.
-/
theorem sourceTreeChartCurl_energy_literal
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (x : T.Chord → ℝ) :
    ∑ p : SourceDualTwoCells B,
      (sourceTreeChartCurlLinear (B := B) T x p) ^ 2 =
        ∑ p : SourceDualTwoCells B,
          (∑ e : T.Chord, sourceCurlCoefficient p e.1 * x e) ^ 2 := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [sourceTreeChartCurlLinear_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [sourceTreeChartCurlCoefficient_eq_sourceCurlCoefficient]


/-- Correct the physical chord coordinates back to the raw source basis.
The correction is the source orientation sign on each chord. -/
noncomputable def sourceChordOrientationLinear
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B)) :
  (T.Chord → ℝ) →ₗ[ℝ] (T.Chord → ℝ) where
  toFun x c := dualCellOrientationSign c.1.1 * x c
  map_add' x y := by
    funext c
    change dualCellOrientationSign c.1.1 * (x c + y c) =
      dualCellOrientationSign c.1.1 * x c + dualCellOrientationSign c.1.1 * y c
    ring
  map_smul' r x := by
    funext c
    change dualCellOrientationSign c.1.1 * (r * x c) =
      r * (dualCellOrientationSign c.1.1 * x c)
    ring

/-- The chord orientation correction is an involutive linear equivalence. -/
noncomputable def sourceChordOrientationEquiv
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B)) :
    (T.Chord → ℝ) ≃ₗ[ℝ] (T.Chord → ℝ) where
  toFun := sourceChordOrientationLinear (B := B) T
  invFun := sourceChordOrientationLinear (B := B) T
  left_inv x := by
    funext c
    change dualCellOrientationSign c.1.1 *
      (dualCellOrientationSign c.1.1 * x c) = x c
    have hs : dualCellOrientationSign c.1.1 ^ 2 = 1 :=
      dualCellOrientationSign_sq c.1
    calc
      dualCellOrientationSign c.1.1 *
          (dualCellOrientationSign c.1.1 * x c) =
        (dualCellOrientationSign c.1.1 ^ 2) * x c := by ring
      _ = x c := by rw [hs]; ring
  right_inv x := by
    funext c
    change dualCellOrientationSign c.1.1 *
      (dualCellOrientationSign c.1.1 * x c) = x c
    have hs : dualCellOrientationSign c.1.1 ^ 2 = 1 :=
      dualCellOrientationSign_sq c.1
    calc
      dualCellOrientationSign c.1.1 *
          (dualCellOrientationSign c.1.1 * x c) =
        (dualCellOrientationSign c.1.1 ^ 2) * x c := by ring
      _ = x c := by rw [hs]; ring
  map_add' := (sourceChordOrientationLinear (B := B) T).map_add
  map_smul' := (sourceChordOrientationLinear (B := B) T).map_smul

/-- The quotient-to-chord map is an equivalence for the actual source quotient. -/
noncomputable def sourceCurlQuotientChordEquiv
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget) :
    SourceCurlQuotient B ≃ₗ[ℝ] (T.Chord → ℝ) :=
  ((sourceCurlQuotientTreeGaugeEquiv T hT).trans
    (realGaugeQuotientChordEquiv T)).trans
      (sourceChordOrientationEquiv (B := B) T)


end FroehlichSpencer.FS82.Gaussian.SourceTreeChart

end
