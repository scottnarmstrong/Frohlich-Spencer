/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.PoissonBridgeD
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Integral cycle coordinates over the reals

This module transports the integral cubical cycle basis to the real cycle
space. These coordinates are the higher-cell replacement for the D=3
rooted-tree chord chart.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open Module

/-- The real degree-one cubical cycle subspace. -/
def degreeOneRealCycleSubspace {d : ℕ} {B : Box d} :
    Submodule ℝ (RealChain d B) where
  carrier := {q | realHomogeneousSupport q 1 ∧ realBoundary q = 0}
  zero_mem' := by simp [realHomogeneousSupport]
  add_mem' := by
    intro q r hq hr
    constructor
    · intro c hc
      have hc' : c ∈ q.support ∪ r.support := by
        by_contra hn
        have hq0 : q c = 0 := by
          by_contra hq0
          exact hn (Finset.mem_union.mpr (Or.inl
            (Finsupp.mem_support_iff.mpr hq0)))
        have hr0 : r c = 0 := by
          by_contra hr0
          exact hn (Finset.mem_union.mpr (Or.inr
            (Finsupp.mem_support_iff.mpr hr0)))
        exact (Finsupp.mem_support_iff.mp hc) (by simp [hq0, hr0])
      rcases Finset.mem_union.mp hc' with hq' | hr'
      · exact hq.1 c hq'
      · exact hr.1 c hr'
    · rw [map_add, hq.2, hr.2, add_zero]
  smul_mem' := by
    intro a q hq
    constructor
    · intro c hc
      by_cases ha : a = 0
      · simp [ha] at hc
      · exact hq.1 c (by
          rw [Finsupp.mem_support_iff] at hc ⊢
          simpa [Finsupp.smul_apply, ha] using hc)
    · rw [map_smul, hq.2, smul_zero]

/-- The integer basis vectors of the cubical degree-one cycle lattice,
viewed in the ambient integer chain coordinates. -/
noncomputable def degreeOneCycleBasisChain {d : ℕ} (B : Box d)
    (i : Fin (degreeOneCycleBasis B).1) : Chain d B :=
  (((degreeOneCycleBasis B).2 i).1).1

@[simp] theorem castIntegerChain_apply {d : ℕ} {B : Box d}
    (q : Chain d B) (c : Cell d B) :
    castIntegerChain q c = (q c : ℝ) := by
  simp [castIntegerChain, Finsupp.mapRange_apply]

/-- Integer coefficient extension, as a linear map over the smaller scalar
ring. -/
noncomputable def castIntegerChainLinear {d : ℕ} {B : Box d} :
    Chain d B →ₗ[ℤ] RealChain d B where
  toFun := castIntegerChain
  map_add' q r := by ext c; simp [castIntegerChain_apply]
  map_smul' z q := by ext c; simp [castIntegerChain_apply]

/-- The integral cycle basis remains linearly independent after coefficient
extension from `ℤ` to `ℝ`. -/
theorem degreeOneCycleBasisChain_cast_linearIndependent {d : ℕ} (B : Box d) :
    LinearIndependent ℝ (fun i : Fin (degreeOneCycleBasis B).1 =>
      castIntegerChain (degreeOneCycleBasisChain B i)) := by
  let b := (degreeOneCycleBasis B).2
  let f : degreeOneCycleSubmodule (B := B) →ₗ[ℤ] Chain d B :=
    (degreeChainSubmodule (B := B) 1).subtype.comp
      (degreeOneCycleSubmodule (B := B)).subtype
  have hf : LinearMap.ker f = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hliZ : LinearIndependent ℤ (degreeOneCycleBasisChain B) := by
    change LinearIndependent ℤ (fun i => f (b i))
    exact b.linearIndependent.map' f hf
  let FZ := Finsupp.linearEquivFunOnFinite ℤ ℤ (Cell d B)
  let FR := Finsupp.linearEquivFunOnFinite ℝ ℝ (Cell d B)
  have hliPiZ : LinearIndependent ℤ (fun i c => FZ (degreeOneCycleBasisChain B i) c) :=
    hliZ.map' FZ.toLinearMap (by
      simp)
  have hliPiR : LinearIndependent ℝ
      (fun i c => ((FZ (degreeOneCycleBasisChain B i) c : ℤ) : ℝ)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ)
      (v := fun i c => FZ (degreeOneCycleBasisChain B i) c)).2 hliPiZ
  have hliPiReal : LinearIndependent ℝ
      (fun i c => castIntegerChain (degreeOneCycleBasisChain B i) c) := by
    convert hliPiR using 1
    ext i c
    rw [castIntegerChain_apply]
    rfl
  have hfun : (fun i => FR (castIntegerChain (degreeOneCycleBasisChain B i))) =
      (fun i c => castIntegerChain (degreeOneCycleBasisChain B i) c) := by
    funext i
    funext c
    rfl
  have hli := hliPiReal.map' FR.symm.toLinearMap (by simp)
  have hreal : (fun i => FR.symm
      (fun c => castIntegerChain (degreeOneCycleBasisChain B i) c)) =
      (fun i => castIntegerChain (degreeOneCycleBasisChain B i)) := by
    funext i
    calc
      FR.symm (fun c => castIntegerChain (degreeOneCycleBasisChain B i) c) =
          FR.symm (FR (castIntegerChain (degreeOneCycleBasisChain B i))) := by
            exact congrArg FR.symm (congrFun hfun i).symm
      _ = castIntegerChain (degreeOneCycleBasisChain B i) :=
        FR.symm_apply_apply _
  convert hli using 1
  ext i c
  exact congrArg (fun q : RealChain d B => q c) (congrFun hreal i).symm

/-- Every integral degree-one cycle lies in the real span of the chosen
integral cycle basis after coefficient extension. -/
theorem castIntegerCycle_mem_realCycleBasisSpan {d : ℕ} (B : Box d)
    (q : Chain d B) (hq : homogeneousSupport q 1)
    (hcycle : boundary q = 0) :
    castIntegerChain q ∈ Submodule.span ℝ
      (Set.range (fun i : Fin (degreeOneCycleBasis B).1 =>
        castIntegerChain (degreeOneCycleBasisChain B i))) := by
  let S := Submodule.span ℝ
    (Set.range (fun i : Fin (degreeOneCycleBasis B).1 =>
      castIntegerChain (degreeOneCycleBasisChain B i)))
  let b := (degreeOneCycleBasis B).2
  let x : degreeOneCycleSubmodule (B := B) := ⟨⟨q, hq⟩, hcycle⟩
  let f : degreeOneCycleSubmodule (B := B) →ₗ[ℤ] RealChain d B :=
    castIntegerChainLinear.comp
      ((degreeChainSubmodule (B := B) 1).subtype.comp
        (degreeOneCycleSubmodule (B := B)).subtype)
  have hx : (x : degreeOneCycleSubmodule (B := B)) ∈
      Submodule.span ℤ (Set.range b) := by
    rw [b.span_eq]
    exact Submodule.mem_top
  have hP : ∀ y : degreeOneCycleSubmodule (B := B),
      y ∈ Submodule.span ℤ (Set.range b) → f y ∈ S := by
    intro y hy
    exact Submodule.span_induction
      (p := fun z _ => f z ∈ S)
      (mem := by
        intro z hz
        rcases hz with ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, by
          simp [f, castIntegerChainLinear, degreeOneCycleBasisChain, b]⟩)
      (zero := by simp [f])
      (add := by
        intro z w hz hw ihz ihw
        simpa [f] using S.add_mem ihz ihw)
      (smul := by
        intro a z hz ih
        simpa [f, Int.cast_smul_eq_zsmul] using S.smul_mem (a : ℝ) ih)
      hy
  have himage : f x ∈ S := hP x hx
  simpa [x, f, castIntegerChainLinear] using himage

/-- The boundary of a real degree-two chain is in the real span of the
integer cycle basis. Expand the chain in cubical cells and use integral cycle
coordinates on each cell boundary. -/
theorem realBoundary_degreeTwo_mem_realCycleBasisSpan {d : ℕ} (B : Box d)
    (p : RealChain d B) (hp : realHomogeneousSupport p 2) :
    realBoundary p ∈ Submodule.span ℝ
      (Set.range (fun i : Fin (degreeOneCycleBasis B).1 =>
        castIntegerChain (degreeOneCycleBasisChain B i))) := by
  let S := Submodule.span ℝ
    (Set.range (fun i : Fin (degreeOneCycleBasis B).1 =>
      castIntegerChain (degreeOneCycleBasisChain B i)))
  have hsum : p = ∑ c : Cell d B, p c • Finsupp.single c (1 : ℝ) := by
    ext c
    simp
  rw [hsum, map_sum]
  apply S.sum_mem
  intro c hc
  by_cases hpc : p c = 0
  · simp [hpc, S]
  · have hcdeg : cellDegree c = 2 := hp c (Finsupp.mem_support_iff.mpr hpc)
    have hbc : homogeneousSupport (basisChain c) 2 := by
      simpa [hcdeg] using homogeneousSupport_basis c
    have hbddeg : homogeneousSupport (boundary (basisChain c)) 1 := by
      have h := xyIntegerBoundary_homogeneousSupport (basisChain c) 2 (by omega) hbc
      simpa using h
    have hbdcycle : boundary (boundary (basisChain c)) = 0 := by
      have h := congrArg
        (fun f : Chain d B →ₗ[ℤ] Chain d B => f (basisChain c))
        (boundary_square_zero (d := d) (B := B))
      simpa [LinearMap.comp_apply] using h
    have hcastBoundary : realBoundary (Finsupp.single c (1 : ℝ)) =
        castIntegerChain (boundary (basisChain c)) := by
      rw [← castIntegerChain_basis c]
      simpa [realBoundary] using
        (realifyLinearMap_cast boundary (basisChain c))
    have hcyclemem := castIntegerCycle_mem_realCycleBasisSpan B
      (boundary (basisChain c)) hbddeg hbdcycle
    have hterm : realBoundary (p c • Finsupp.single c (1 : ℝ)) ∈ S := by
      rw [map_smul, hcastBoundary]
      exact S.smul_mem (p c) hcyclemem
    exact hterm

/-- The chosen integral cycle basis, after coefficient extension, spans the
entire real degree-one cycle subspace. -/
theorem degreeOneRealCycleSubspace_eq_realCycleBasisSpan {d : ℕ} (B : Box d) :
    degreeOneRealCycleSubspace (B := B) = Submodule.span ℝ
      (Set.range (fun i : Fin (degreeOneCycleBasis B).1 =>
        castIntegerChain (degreeOneCycleBasisChain B i))) := by
  apply le_antisymm
  · intro q hq
    rcases hq with ⟨hqdeg, hcycle⟩
    let anchor : Anchor d B := fun i => ⟨0, Nat.zero_lt_succ (B i)⟩
    obtain ⟨hfill, hfilldeg⟩ := real_positiveDegree_filling
      anchor q 1 (by omega) hqdeg hcycle
    rw [← hfill]
    exact realBoundary_degreeTwo_mem_realCycleBasisSpan B
      (realFillingOperator anchor q) hfilldeg
  · apply Submodule.span_le.2
    rintro q ⟨i, rfl⟩
    let b := (degreeOneCycleBasis B).2 i
    have hq : homogeneousSupport (degreeOneCycleBasisChain B i) 1 := b.1.2
    have hcycle : boundary (degreeOneCycleBasisChain B i) = 0 := b.2
    constructor
    · intro c hc
      exact hq c (Finsupp.support_mapRange hc)
    · have hcast : realBoundary
          (castIntegerChain (degreeOneCycleBasisChain B i)) =
          castIntegerChain (boundary (degreeOneCycleBasisChain B i)) := by
        simpa [realBoundary] using
          (realifyLinearMap_cast boundary (degreeOneCycleBasisChain B i))
      rw [hcast, hcycle]
      ext c
      simp [castIntegerChain]

/-- The coefficient-extended integral cycle basis is a genuine real basis of
the full real cycle subspace. -/
noncomputable def degreeOneRealCycleBasis {d : ℕ} (B : Box d) :
    Σ n : ℕ, Basis (Fin n) ℝ (degreeOneRealCycleSubspace (B := B)) := by
  let n := (degreeOneCycleBasis B).1
  have hmem (i : Fin n) :
      castIntegerChain (degreeOneCycleBasisChain B i) ∈
        degreeOneRealCycleSubspace (B := B) := by
    rw [degreeOneRealCycleSubspace_eq_realCycleBasisSpan]
    exact Submodule.subset_span ⟨i, rfl⟩
  let v : Fin n → degreeOneRealCycleSubspace (B := B) :=
    Set.codRestrict
      (fun i : Fin n => castIntegerChain (degreeOneCycleBasisChain B i))
      (degreeOneRealCycleSubspace (B := B)) hmem
  let fsub : degreeOneRealCycleSubspace (B := B) →ₗ[ℝ] RealChain d B :=
    (degreeOneRealCycleSubspace (B := B)).subtype
  have hli : LinearIndependent ℝ v := by
    simpa [v, n] using
      (degreeOneCycleBasisChain_cast_linearIndependent B).codRestrict
        (degreeOneRealCycleSubspace (B := B)) hmem
  have hrange :
      (degreeOneRealCycleSubspace (B := B)).subtype '' Set.range v =
        Set.range (fun i : Fin n =>
          castIntegerChain (degreeOneCycleBasisChain B i)) := by
    ext q
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  have hmap : (Submodule.span ℝ (Set.range v)).map
      (degreeOneRealCycleSubspace (B := B)).subtype =
        degreeOneRealCycleSubspace (B := B) := by
    rw [Submodule.map_span]
    rw [hrange]
    simpa [v] using
      (degreeOneRealCycleSubspace_eq_realCycleBasisSpan B).symm
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    apply (Submodule.map_injective_of_injective
      (f := fsub)
      Subtype.val_injective)
    rw [Submodule.map_top, Submodule.range_subtype]
    exact hmap
  refine ⟨n, Basis.mk hli ?_⟩
  rw [hspan]

/-- The real cycle basis with its integral cycle index exposed in its type.
This is the same coefficient-extended basis, presented without hiding the
dimension in a sigma projection. -/
noncomputable def degreeOneRealCycleBasisExplicit {d : ℕ} (B : Box d) :
    Basis (Fin (degreeOneCycleBasis B).1) ℝ
      (degreeOneRealCycleSubspace (B := B)) := by
  let n := (degreeOneCycleBasis B).1
  have hmem (i : Fin n) :
      castIntegerChain (degreeOneCycleBasisChain B i) ∈
        degreeOneRealCycleSubspace (B := B) := by
    rw [degreeOneRealCycleSubspace_eq_realCycleBasisSpan]
    exact Submodule.subset_span ⟨i, rfl⟩
  let v : Fin n → degreeOneRealCycleSubspace (B := B) :=
    Set.codRestrict
      (fun i : Fin n => castIntegerChain (degreeOneCycleBasisChain B i))
      (degreeOneRealCycleSubspace (B := B)) hmem
  let fsub : degreeOneRealCycleSubspace (B := B) →ₗ[ℝ] RealChain d B :=
    (degreeOneRealCycleSubspace (B := B)).subtype
  have hli : LinearIndependent ℝ v := by
    simpa [v, n] using
      (degreeOneCycleBasisChain_cast_linearIndependent B).codRestrict
        (degreeOneRealCycleSubspace (B := B)) hmem
  have hrange :
      (degreeOneRealCycleSubspace (B := B)).subtype '' Set.range v =
        Set.range (fun i : Fin n =>
          castIntegerChain (degreeOneCycleBasisChain B i)) := by
    ext q
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  have hmap : (Submodule.span ℝ (Set.range v)).map
      (degreeOneRealCycleSubspace (B := B)).subtype =
        degreeOneRealCycleSubspace (B := B) := by
    rw [Submodule.map_span, hrange]
    simpa [v] using
      (degreeOneRealCycleSubspace_eq_realCycleBasisSpan B).symm
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    apply (Submodule.map_injective_of_injective
      (f := fsub)
      Subtype.val_injective)
    rw [Submodule.map_top, Submodule.range_subtype]
    exact hmap
  exact Basis.mk hli (by rw [hspan])

@[simp] theorem degreeOneRealCycleBasisExplicit_val {d : ℕ} (B : Box d)
    (i : Fin (degreeOneCycleBasis B).1) :
    (degreeOneRealCycleBasisExplicit B i).1 =
      castIntegerChain (degreeOneCycleBasisChain B i) := by
  unfold degreeOneRealCycleBasisExplicit
  rw [Basis.mk_apply]
  rfl

/-- The Gram matrix of the integral cycle basis in the ambient Euclidean
bond space. -/
noncomputable def degreeOneCycleGramMatrix {d : ℕ} (B : Box d) :
    Matrix (Fin (degreeOneCycleBasis B).1)
      (Fin (degreeOneCycleBasis B).1) ℝ :=
  Matrix.gram ℝ (fun i => finsuppToEuclidean
    (castIntegerChain (degreeOneCycleBasisChain B i)))

/-- The cycle Gram matrix is positive definite because the integral cycle
basis remains independent over the reals. -/
theorem degreeOneCycleGramMatrix_posDef {d : ℕ} (B : Box d) :
    (degreeOneCycleGramMatrix B).PosDef := by
  have hinj : Function.Injective (finsuppToEuclidean (α := Cell d B)) := by
    intro q r h
    apply Finsupp.ext
    intro c
    have hc := congrArg (fun x : EuclideanSpace ℝ (Cell d B) => x c) h
    simpa using hc
  have hker : LinearMap.ker (finsuppToEuclidean (α := Cell d B)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hli := (degreeOneCycleBasisChain_cast_linearIndependent B).map'
    (finsuppToEuclidean (α := Cell d B)) hker
  exact Matrix.posDef_gram_of_linearIndependent hli

/-- The cubical star is an isometry for coefficient Euclidean norms. -/
theorem starMap_finsuppToEuclidean_inner {d : ℕ} {B : Box d}
    (q r : RealChain d B) :
    inner ℝ (finsuppToEuclidean (starMap q))
        (finsuppToEuclidean (starMap r)) =
      inner ℝ (finsuppToEuclidean q) (finsuppToEuclidean r) := by
  classical
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rw [Fintype.sum_equiv primalDualCellEquiv]
  simp [finsuppToEuclidean_apply, starMap,
    Finsupp.equivMapDomain_apply]


end FroehlichSpencer.FS82.XY

end
