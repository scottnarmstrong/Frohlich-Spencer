/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.PoissonCycleD
public import FroehlichSpencer.FS82.Poisson.FiniteModel
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# All-dimensional shifted XY Poisson phase

The finite cycle lattice is charted by the integral basis of cubical bond
cycles. Its integer dual is the gauge quotient of dual `(d - 2)`-forms. This
module carries the D=3 shifted Poisson argument through that basis chart.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open scoped BigOperators InnerProductSpace

/-- Integral coordinates of the finite XY cycle lattice in its cubical
cycle basis. -/
noncomputable def xyDCycleCoordinatesEquiv {d : ℕ} {B : Box d} :
    XYEndpointCycleModes (B := B) ≃
      (Fin (degreeOneCycleBasis B).1 → ℤ) where
  toFun c := (degreeOneCycleBasis B).2.equivFun
    (xyBondCycleModesEquivDegreeOneCycles (B := B) c)
  invFun q := (xyBondCycleModesEquivDegreeOneCycles (B := B)).symm
    ((degreeOneCycleBasis B).2.equivFun.symm q)
  left_inv c := by
    change (xyBondCycleModesEquivDegreeOneCycles (B := B)).symm
      ((degreeOneCycleBasis B).2.equivFun.symm
        ((degreeOneCycleBasis B).2.equivFun
          (xyBondCycleModesEquivDegreeOneCycles (B := B) c))) = c
    rw [(degreeOneCycleBasis B).2.equivFun.symm_apply_apply]
    exact (xyBondCycleModesEquivDegreeOneCycles (B := B)).symm_apply_apply c
  right_inv q := by
    change (degreeOneCycleBasis B).2.equivFun
      (xyBondCycleModesEquivDegreeOneCycles (B := B)
        ((xyBondCycleModesEquivDegreeOneCycles (B := B)).symm
          ((degreeOneCycleBasis B).2.equivFun.symm q))) = q
    rw [(xyBondCycleModesEquivDegreeOneCycles (B := B)).apply_symm_apply]
    exact (degreeOneCycleBasis B).2.equivFun.apply_symm_apply q

/-- The shifted Gaussian weight of an integral XY bond cycle. -/
noncomputable def dualDXYCycleGaussianWeight {d : ℕ} {B : Box d}
    (β : ℝ) (path : XYBondModes (B := B))
    (c : XYEndpointCycleModes (B := B)) : ℝ :=
  ∏ b : XYBonds B,
    Real.exp (-(((c.1 b + path b : ℤ) : ℝ) ^ 2) / (2 * β))

/-- In the integral basis chart, the bond cycle is the integer linear
combination of its basis cycles. -/
theorem xyDCycleModeChain_coordinates {d : ℕ} {B : Box d}
    (n : Fin (degreeOneCycleBasis B).1 → ℤ) :
    xyBondModeChain ((xyDCycleCoordinatesEquiv (B := B)).symm n).1 =
      ∑ i, n i • degreeOneCycleBasisChain B i := by
  let b := (degreeOneCycleBasis B).2
  let c := (xyDCycleCoordinatesEquiv (B := B)).symm n
  have hcoord : xyBondCycleModesEquivDegreeOneCycles (B := B) c =
      b.equivFun.symm n := by
    apply b.equivFun.injective
    have heq := (xyDCycleCoordinatesEquiv (B := B)).apply_symm_apply n
    change b.equivFun (xyBondCycleModesEquivDegreeOneCycles (B := B) c) = n at heq
    rw [heq]
    exact (b.equivFun.apply_symm_apply n).symm
  let chainMap : degreeOneCycleSubmodule (B := B) →ₗ[ℤ] Chain d B :=
    ((degreeChainSubmodule (B := B) 1).subtype).comp
      (degreeOneCycleSubmodule (B := B)).subtype
  have hsum : ∑ i, n i • b i = b.equivFun.symm n := by
    simp
  have hsumMap : chainMap (∑ i, n i • b i) =
      ∑ i, n i • degreeOneCycleBasisChain B i := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul]
    rfl
  have hmodeMap : chainMap
      (xyBondCycleModesEquivDegreeOneCycles (B := B) c) =
        xyBondModeChain c.1 := rfl
  have h := congrArg chainMap (hsum.trans hcoord.symm)
  rw [hsumMap, hmodeMap] at h
  exact h.symm

/-- Integer coefficient extension preserves finite cycle-coordinate sums. -/
theorem castIntegerChain_sum_smul {d : ℕ} {B : Box d}
    (n : Fin (degreeOneCycleBasis B).1 → ℤ) :
    castIntegerChain (∑ i, n i • degreeOneCycleBasisChain B i) =
      ∑ i, (n i : ℝ) • castIntegerChain (degreeOneCycleBasisChain B i) := by
  ext c
  simp [castIntegerChain_apply]

/-- The real cubical bond vector represented by an integral XY cycle. -/
noncomputable def dualDXYCycleVector {d : ℕ} {B : Box d}
    (n : Fin (degreeOneCycleBasis B).1 → ℤ) :
    EuclideanSpace ℝ (Cell d B) :=
  finsuppToEuclidean (castIntegerChain
    (xyBondModeChain ((xyDCycleCoordinatesEquiv (B := B)).symm n).1))

/-- The real cubical vector of the endpoint path. -/
noncomputable def dualDXYPathChainVector {d : ℕ} {B : Box d}
    (x y : XYSites B) : EuclideanSpace ℝ (Cell d B) :=
  finsuppToEuclidean (castIntegerChain
    (xyBondModeChain (xyEndpointPathModes x y)))

/-- In the coordinate chart the real cycle vector is the same combination of
the realified integral cycle basis. -/
theorem dualDXYCycleVector_coordinates {d : ℕ} {B : Box d}
    (n : Fin (degreeOneCycleBasis B).1 → ℤ) :
    dualDXYCycleVector n = ∑ i, (n i : ℝ) •
      finsuppToEuclidean (castIntegerChain (degreeOneCycleBasisChain B i)) := by
  rw [dualDXYCycleVector, xyDCycleModeChain_coordinates,
    castIntegerChain_sum_smul]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]

/-- Euclidean pairing of degree-one chains is the bond-coordinate pairing. -/
theorem realBondChain_inner {d : ℕ} {B : Box d}
    (p r : RealChain d B) (hp : realHomogeneousSupport p 1) :
    inner ℝ (finsuppToEuclidean p) (finsuppToEuclidean r) =
      ∑ b : XYBonds B, p b.1 * r b.1 := by
  classical
  let f : Cell d B → ℝ := fun c => r c * p c
  have hzero (c : {c : Cell d B // cellDegree c ≠ 1}) :
      f c.1 = 0 := by
    have hp0 : p c.1 = 0 := by
      by_contra h
      exact c.2 (hp c.1 (Finsupp.mem_support_iff.mpr h))
    simp [f, hp0]
  have hzerosum :
      (∑ c : {c : Cell d B // cellDegree c ≠ 1}, f c.1) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    exact hzero c
  have hparts := (Fintype.sum_subtype_add_sum_subtype
    (fun c : Cell d B => cellDegree c = 1) f).symm
  have hpos :
      @Finset.sum {c : Cell d B // cellDegree c = 1} ℝ inferInstance
        (@Finset.univ _
          (Subtype.fintype (fun c : Cell d B => cellDegree c = 1)))
        (fun c => f c.1) = ∑ b : XYBonds B, f b.1 := by
    let e : {c : Cell d B // cellDegree c = 1} ≃ XYBonds B := Equiv.refl _
    exact @Fintype.sum_equiv
      {c : Cell d B // cellDegree c = 1} (XYBonds B) ℝ
      (Subtype.fintype (fun c : Cell d B => cellDegree c = 1))
      (xyBondsFintype) inferInstance e _ _ (by intro c; rfl)
  rw [hpos] at hparts
  rw [PiLp.inner_apply]
  simp only [finsuppToEuclidean_apply, RCLike.inner_apply]
  change (∑ c : Cell d B, f c) = _
  calc
    (∑ c : Cell d B, f c) =
        (∑ b : XYBonds B, f b.1) +
          ∑ c : {c : Cell d B // cellDegree c ≠ 1}, f c.1 := by
            exact hparts
    _ = ∑ b : XYBonds B, p b.1 * r b.1 := by
          rw [hzerosum, add_zero]
          apply Finset.sum_congr rfl
          intro b hb
          dsimp [f]
          ring

/-- Coordinates of the codifferential of the endpoint path in the cycle
chart. -/
noncomputable def dualDXYPathCoordinates {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} (x y : XYSites B) :
    Fin (degreeOneCycleBasis B).1 → ℝ :=
  hodgeLiftCoordinates (dualDExactOneComplex hd B)
    (dualDImageCycleBasisForHodge hd B)
    (dualDCycleFillingLift ∘ degreeOneRealCycleBasisExplicit B)
    (dualDXYPathSource hd x y)

/-- The path-source coordinates are its ordinary bond pairing with the cycle
basis. -/
theorem dualDXYPathCoordinates_eq_inner {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} (x y : XYSites B)
    (i : Fin (degreeOneCycleBasis B).1) :
    dualDXYPathCoordinates hd x y i =
      inner ℝ (dualDXYPathChainVector x y)
        (finsuppToEuclidean (castIntegerChain
          (degreeOneCycleBasisChain B i))) := by
  let C := dualDExactOneComplex hd B
  let lift := dualDCycleFillingLift ∘ degreeOneRealCycleBasisExplicit B
  change inner ℝ ((dualDD₁ (B := B)).adjoint (dualDXYPathVector x y))
      (lift i) = _
  rw [LinearMap.adjoint_inner_left]
  have hlift : dualDD₁ (lift i) =
      (dualDImageCycleBasis hd B i :
        EuclideanSpace ℝ (DualDForm B (d - 1))) := by
    change dualDD₁ (dualDCycleFillingLift
        (degreeOneRealCycleBasisExplicit B i)) =
      (dualDImageCycleBasis hd B i :
        EuclideanSpace ℝ (DualDForm B (d - 1)))
    rw [dualDImageCycleBasis_apply]
    rfl
  rw [hlift]
  rw [← dualDFormToChain_inner (d - 1) (dualDXYPathVector x y)
    (dualDImageCycleBasis hd B i :
      EuclideanSpace ℝ (DualDForm B (d - 1)))]
  rw [dualDXYPathVector_embed, dualDImageCycleBasis_toChain]
  change inner ℝ
      (finsuppToEuclidean (starMap (castIntegerChain
        (xyBondModeChain (xyEndpointPathModes x y)))))
      (finsuppToEuclidean (starMap (castIntegerChain
        (degreeOneCycleBasisChain B i)))) = _
  rw [starMap_finsuppToEuclidean_inner]
  rfl

/-- The endpoint path has the same Euclidean energy in bond and dual-star
coordinates. -/
theorem dualDXYPathVector_energy_eq_chain {d : ℕ} {B : Box d}
    (x y : XYSites B) :
    inner ℝ (dualDXYPathVector x y) (dualDXYPathVector x y) =
      inner ℝ (dualDXYPathChainVector x y) (dualDXYPathChainVector x y) := by
  rw [← dualDFormToChain_inner (d - 1)
    (dualDXYPathVector x y) (dualDXYPathVector x y)]
  rw [dualDXYPathVector_embed]
  exact starMap_finsuppToEuclidean_inner _ _

/-- The inverse-Gram energy of a real cycle in its basis coordinates. -/
theorem dualDXYCycleVector_energy {d : ℕ} {B : Box d}
    (n : Fin (degreeOneCycleBasis B).1 → ℤ) :
    inner ℝ (dualDXYCycleVector n) (dualDXYCycleVector n) =
      dotProduct (fun i => (n i : ℝ))
        ((degreeOneCycleGramMatrix B).mulVec (fun i => (n i : ℝ))) := by
  rw [dualDXYCycleVector_coordinates]
  simpa [degreeOneCycleGramMatrix] using
    (Matrix.star_dotProduct_gram_mulVec
      (fun i : Fin (degreeOneCycleBasis B).1 =>
        finsuppToEuclidean (castIntegerChain (degreeOneCycleBasisChain B i)))
      (fun i => (n i : ℝ)) (fun i => (n i : ℝ))).symm

/-- Mixed cycle/path energy is the cycle-coordinate linear source. -/
theorem dualDXYCyclePath_inner {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} (n : Fin (degreeOneCycleBasis B).1 → ℤ)
    (x y : XYSites B) :
    inner ℝ (dualDXYCycleVector n) (dualDXYPathChainVector x y) =
      dotProduct (fun i => (n i : ℝ)) (dualDXYPathCoordinates hd x y) := by
  rw [dualDXYCycleVector_coordinates, sum_inner]
  simp only [real_inner_smul_left]
  rw [show dotProduct (fun i => (n i : ℝ))
        (dualDXYPathCoordinates hd x y) =
      ∑ i, (n i : ℝ) * dualDXYPathCoordinates hd x y i by
        simp [dotProduct]]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dualDXYPathCoordinates_eq_inner hd x y i, real_inner_comm]

/-- Realification preserves the homogeneous cubical support degree. -/
theorem castIntegerChain_realHomogeneousSupport {d : ℕ} {B : Box d}
    (q : Chain d B) (k : ℕ) (hq : homogeneousSupport q k) :
    realHomogeneousSupport (castIntegerChain q) k := by
  intro c hc
  exact hq c (Finsupp.support_mapRange hc)

/-- The shifted product of bond Gaussians is the Gaussian of the cubical
cycle-plus-path energy. -/
theorem dualDXYCycleGaussianWeight_eq_energy {d : ℕ} {B : Box d}
    {β : ℝ} (c : XYEndpointCycleModes (B := B))
    (path : XYBondModes (B := B)) :
    dualDXYCycleGaussianWeight β path c =
      Real.exp (-inner ℝ
        (finsuppToEuclidean (castIntegerChain
          (xyBondModeChain (c.1 + path))))
        (finsuppToEuclidean (castIntegerChain
          (xyBondModeChain (c.1 + path)))) / (2 * β)) := by
  rw [dualDXYCycleGaussianWeight, ← Real.exp_sum]
  congr 1
  let z := castIntegerChain (xyBondModeChain (c.1 + path))
  have hz : realHomogeneousSupport z 1 :=
    castIntegerChain_realHomogeneousSupport _ 1
      (xyBondModeChain_homogeneousSupport (c.1 + path))
  rw [realBondChain_inner z z hz]
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
  apply congrArg (fun s : ℝ => s / (2 * β))
  apply Finset.sum_congr rfl
  intro b hb
  have hzval : z b.1 = ((c.1 b + path b : ℤ) : ℝ) := by
    simp [z, castIntegerChain_apply, xyBondModeChain_coeff]
  rw [hzval]
  ring_nf

/-- The cycle-coordinate Gaussian has its Gram quadratic and the endpoint
linear source as its exponent. -/
theorem dualDXYCycleGaussianWeight_eq_coordinateTerm {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} {β : ℝ}
    (x y : XYSites B) (n : Fin (degreeOneCycleBasis B).1 → ℤ) :
    dualDXYCycleGaussianWeight β (xyEndpointPathModes x y)
        ((xyDCycleCoordinatesEquiv (B := B)).symm n) =
      Real.exp (-(inner ℝ (dualDXYPathChainVector x y)
          (dualDXYPathChainVector x y) +
        dotProduct (fun i => (n i : ℝ))
          ((degreeOneCycleGramMatrix B).mulVec (fun i => (n i : ℝ))) +
        2 * dotProduct (fun i => (n i : ℝ))
          (dualDXYPathCoordinates hd x y)) / (2 * β)) := by
  rw [dualDXYCycleGaussianWeight_eq_energy]
  have hcycle : dualDXYCycleVector n = finsuppToEuclidean
      (castIntegerChain (xyBondModeChain
        (((xyDCycleCoordinatesEquiv (B := B)).symm n).1))) := by
    simp [dualDXYCycleVector]
  have hshift :
      finsuppToEuclidean (castIntegerChain
        (xyBondModeChain
            ((((xyDCycleCoordinatesEquiv (B := B)).symm n).1) +
              xyEndpointPathModes x y))) =
        dualDXYCycleVector n + dualDXYPathChainVector x y := by
    change finsuppToEuclidean (castIntegerChain (xyBondModeChain
        ((((xyDCycleCoordinatesEquiv (B := B)).symm n).1) +
          xyEndpointPathModes x y))) =
      finsuppToEuclidean (castIntegerChain
        (xyBondModeChain ((xyDCycleCoordinatesEquiv (B := B)).symm n).1)) +
        finsuppToEuclidean (castIntegerChain
          (xyBondModeChain (xyEndpointPathModes x y)))
    rw [xyBondModeChain_add, castIntegerChain_add, map_add]
  rw [hshift]
  simp only [inner_add_left, inner_add_right]
  rw [dualDXYCycleVector_energy, dualDXYCyclePath_inner hd]
  have hcross : inner ℝ (dualDXYPathChainVector x y)
      (dualDXYCycleVector n) =
        dotProduct (fun i => (n i : ℝ)) (dualDXYPathCoordinates hd x y) := by
    rw [real_inner_comm (dualDXYCycleVector n)
      (dualDXYPathChainVector x y)]
    exact dualDXYCyclePath_inner hd n x y
  rw [hcross]
  ring_nf

/-- The positive-definite finite Poisson matrix in cycle coordinates. -/
noncomputable def dualDXYCoordinateMatrix {d : ℕ} {B : Box d} (β : ℝ) :
    Matrix (Fin (degreeOneCycleBasis B).1)
      (Fin (degreeOneCycleBasis B).1) ℝ :=
  ((2 * Real.pi * β)⁻¹) • degreeOneCycleGramMatrix B

theorem dualDXYCoordinateMatrix_posDef {d : ℕ} {B : Box d}
    {β : ℝ} (hβ : 0 < β) :
    (dualDXYCoordinateMatrix (B := B) β).PosDef := by
  have hscale : 0 < (2 * Real.pi * β)⁻¹ := by positivity
  exact (degreeOneCycleGramMatrix_posDef B).smul hscale

/-- The determinant factor from finite-dimensional Poisson summation in the
cycle basis. -/
noncomputable def dualDXYPoissonConstant {d : ℕ} {B : Box d}
    (β : ℝ) : ℂ :=
  ((Real.sqrt (dualDXYCoordinateMatrix (B := B) β).det : ℝ) : ℂ)⁻¹

/-- The all-dimensional shifted phase on the dual integer-current lattice,
written in its integral cycle-dual coordinates. -/
noncomputable def dualDXYCurrentPhase {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} {β : ℝ} (hβ : 0 ≤ β) (x y : XYSites B)
    (q : Fin (degreeOneCycleBasis B).1 → ℤ) : ℂ :=
  dualDPathPhase hd B hβ
    (dualDCoordinateCurrent hd B (fun i => (q i : ℝ)))
    (dualDXYPathTau hd x y)

/-- Hodge quadratic of an integral-coordinate current is the inverse cycle
Gram quadratic. -/
theorem dualDXYCoordinateCurrent_hodgeQuadratic {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} (q : Fin (degreeOneCycleBasis B).1 → ℝ) :
    inner ℝ (dualDCoordinateCurrent hd B q)
        (hodgeInverseOnCoClosed (dualDExactOneComplex hd B)
          (dualDCoordinateCurrent hd B q)) =
      dotProduct q ((degreeOneCycleGramMatrix B)⁻¹.mulVec q) := by
  have h := dualDHodgeInverse_eq_inverseCycleGram hd B
    (dualDCoordinateCurrent hd B q)
  rw [dualDCoordinateCurrent_liftCoordinates hd B q] at h
  simpa using h

/-- The mixed Hodge inverse pairing with the endpoint path is the inverse
cycle-Gram pairing of their chart coordinates. -/
theorem dualDXYCoordinateCurrent_pathPairing {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} (x y : XYSites B)
    (q : Fin (degreeOneCycleBasis B).1 → ℝ) :
    inner ℝ (dualDCoordinateCurrent hd B q)
        (dualDXYPathTau hd x y) =
      dotProduct q ((degreeOneCycleGramMatrix B)⁻¹.mulVec
        (dualDXYPathCoordinates hd x y)) := by
  let C := dualDExactOneComplex hd B
  let b := dualDImageCycleBasisForHodge hd B
  let lift := dualDCycleFillingLift ∘ degreeOneRealCycleBasisExplicit B
  have hlift (i : Fin (degreeOneCycleBasis B).1) :
      C.d₁ (lift i) = (b i : EuclideanSpace ℝ (DualDForm B (d - 1))) := by
    change dualDD₁ (dualDCycleFillingLift
        (degreeOneRealCycleBasisExplicit B i)) =
      (dualDImageCycleBasis hd B i :
        EuclideanSpace ℝ (DualDForm B (d - 1)))
    rw [dualDImageCycleBasis_apply]
    rfl
  have h := hodgeInversePairing_eq_inverseImageGram C b lift hlift
    (dualDCoordinateCurrent hd B q) (dualDXYPathSource hd x y)
  have hgram : hodgeImageGram C b = degreeOneCycleGramMatrix B := by
    change Matrix.gram ℝ (fun i =>
      (dualDImageCycleBasisForHodge hd B i :
        EuclideanSpace ℝ (DualDForm B (d - 1)))) = degreeOneCycleGramMatrix B
    exact dualDImageCycleGram_eq_cycleGram hd B
  rw [hgram] at h
  rw [dualDCoordinateCurrent_liftCoordinates hd B q] at h
  simpa [dualDXYPathTau, dualDXYPathCoordinates, C, b, lift,
    hodgeLiftCoordinates] using h

/-- In cycle-dual coordinates, the quotient-Gaussian phase is the centered
characteristic times the endpoint path Fourier phase. -/
theorem dualDXYCurrentPhase_eq_formula {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} {β : ℝ} (hβ : 0 ≤ β) (x y : XYSites B)
    (q : Fin (degreeOneCycleBasis B).1 → ℤ) :
    dualDXYCurrentPhase hd hβ x y q =
      Complex.exp (-(2 * Real.pi ^ 2 * β *
        dotProduct (fun i => (q i : ℝ))
          ((degreeOneCycleGramMatrix B)⁻¹.mulVec (fun i => (q i : ℝ))) : ℝ)) *
      Complex.exp (Complex.I * (2 * Real.pi : ℂ) *
        ((dotProduct (fun i => (q i : ℝ))
          ((degreeOneCycleGramMatrix B)⁻¹.mulVec
            (dualDXYPathCoordinates hd x y)) : ℝ) : ℂ)) := by
  let qR : Fin (degreeOneCycleBasis B).1 → ℝ := fun i => (q i : ℝ)
  let μ := dualDCoordinateCurrent hd B qR
  have hquad : quotientCovarianceQuadratic (dualDExactOneComplex hd B) μ =
      dotProduct qR ((degreeOneCycleGramMatrix B)⁻¹.mulVec qR) := by
    rw [quotientCovarianceQuadratic]
    exact dualDXYCoordinateCurrent_hodgeQuadratic hd qR
  have hpair : inner ℝ μ.1 (dualDXYPathTau hd x y).1 =
      dotProduct qR ((degreeOneCycleGramMatrix B)⁻¹.mulVec
        (dualDXYPathCoordinates hd x y)) :=
    dualDXYCoordinateCurrent_pathPairing hd x y qR
  change dualDPathPhase hd B hβ μ (dualDXYPathTau hd x y) = _
  rw [dualDPathPhase_eq, hquad, hpair]
  have hcoeff : β * (2 * Real.pi) ^ 2 *
        dotProduct qR ((degreeOneCycleGramMatrix B)⁻¹.mulVec qR) / 2 =
      2 * Real.pi ^ 2 * β *
        dotProduct qR ((degreeOneCycleGramMatrix B)⁻¹.mulVec qR) := by
    ring
  have hcast :
      -((β * (2 * Real.pi) ^ 2 *
        dotProduct qR ((degreeOneCycleGramMatrix B)⁻¹.mulVec qR) / 2 : ℝ) : ℂ) =
      -((2 * Real.pi ^ 2 * β *
        dotProduct qR ((degreeOneCycleGramMatrix B)⁻¹.mulVec qR) : ℝ) : ℂ) := by
    exact congrArg (fun z : ℂ => -z)
      (congrArg (fun r : ℝ => (r : ℂ)) hcoeff)
  rw [hcast]

set_option linter.style.haveILetI false in
/-- Inverse scaling of the cycle Gram matrix in the finite Poisson chart. -/
theorem dualDXYCoordinateMatrix_inv {d : ℕ} {B : Box d} {β : ℝ}
    (hβ : 0 < β) :
    (dualDXYCoordinateMatrix (B := B) β)⁻¹ =
      (2 * Real.pi * β) • (degreeOneCycleGramMatrix B)⁻¹ := by
  let G := degreeOneCycleGramMatrix B
  let c := (2 * Real.pi * β)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (by positivity : 2 * Real.pi * β ≠ 0)
  letI : Invertible c := invertibleOfNonzero hc
  have hGdet : IsUnit G.det :=
    (Matrix.isUnit_iff_isUnit_det G).mp
      (degreeOneCycleGramMatrix_posDef B).isUnit
  rw [show dualDXYCoordinateMatrix (B := B) β = c • G by
    simp [dualDXYCoordinateMatrix, G, c]]
  rw [Matrix.inv_smul G c hGdet]
  have hcinv : ⅟c = 2 * Real.pi * β := by simp [c]
  rw [hcinv]

/-- The tested-primal and Poisson quadratic normalizations agree in an
arbitrary finite cycle chart. -/
theorem dualDTestedPrimalTerm_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (τ : ι → ℝ) (t : ℝ)
    (n : ι → ℤ) :
    testedPrimalTerm A τ t n =
      primalQuadraticExp A (realTiltParameter τ t) n := by
  unfold testedPrimalTerm primalQuadraticExp realTiltParameter
  apply congrArg Complex.exp
  congr 1
  calc
    (t : ℂ) * ∑ i, (τ i : ℂ) * (n i : ℂ) =
        ∑ i, (t : ℂ) * ((τ i : ℂ) * (n i : ℂ)) := by
          rw [Finset.mul_sum]
    _ = ∑ i, (2 * Real.pi : ℂ) *
        (((t * τ i / (2 * Real.pi : ℝ) : ℝ) : ℂ) * (n i : ℂ)) := by
      apply Fintype.sum_congr
      intro i
      push_cast
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp [hpi]
    _ = (2 * Real.pi : ℂ) *
        ∑ i, (((t * τ i / (2 * Real.pi : ℝ) : ℝ) : ℂ) * (n i : ℂ)) :=
          (Finset.mul_sum ..).symm


/-- Complex bilinear extension of a real cycle-coordinate matrix. -/
def dualDComplexBilinear {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x y : ι → ℝ) : ℂ :=
  ∑ i, ∑ j, (x i : ℂ) * (A i j : ℂ) * (y j : ℂ)

theorem dualDComplexBilinear_eq_dotProduct {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    dualDComplexBilinear A x y =
      (dotProduct x (Matrix.mulVec A y) : ℝ) := by
  simp [dualDComplexBilinear, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_left_comm, mul_comm]

theorem dualDComplexBilinear_comm {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (x y : ι → ℝ) :
    dualDComplexBilinear A x y = dualDComplexBilinear A y x := by
  classical
  have hsymm (i j : ι) : A i j = A j i := by
    have h := congrFun (congrFun hA.eq i) j
    simpa using h.symm
  unfold dualDComplexBilinear
  calc
    _ = ∑ j, ∑ i, (x i : ℂ) * (A i j : ℂ) * (y j : ℂ) := by
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (y i : ℂ) * (A i j : ℂ) * (x j : ℂ) := by
          apply Fintype.sum_congr
          intro i
          apply Fintype.sum_congr
          intro j
          rw [hsymm j i]
          ring
    _ = _ := rfl

/-- Split the real and Fourier terms in a dual Gaussian quadratic. -/
theorem dualDComplexQuadraticExpansion {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι ℝ) (w : ι → ℝ) (k : ι → ℤ) :
    Complex.exp ((Real.pi : ℂ) * ∑ i, ∑ j,
      ((w i : ℂ) - Complex.I * (k i : ℂ)) *
        ((M i j : ℝ) : ℂ) * ((w j : ℂ) - Complex.I * (k j : ℂ))) =
      Complex.exp ((Real.pi : ℂ) * dualDComplexBilinear M w w) *
      Complex.exp (-(Real.pi : ℂ) *
        dualDComplexBilinear M (fun i => (k i : ℝ))
          (fun i => (k i : ℝ))) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I *
        (dualDComplexBilinear M w (fun i => (k i : ℝ)) +
          dualDComplexBilinear M (fun i => (k i : ℝ)) w)) := by
  let kr : ι → ℝ := fun i => (k i : ℝ)
  let Qww := dualDComplexBilinear M w w
  let Qkk := dualDComplexBilinear M kr kr
  let Qwk := dualDComplexBilinear M w kr
  let Qkw := dualDComplexBilinear M kr w
  have hCross :
      (∑ i, ∑ j, Complex.I *
        ((w i : ℂ) * ((M i j : ℝ) : ℂ) * (k j : ℂ) +
          (k i : ℂ) * ((M i j : ℝ) : ℂ) * (w j : ℂ))) =
        Complex.I * ((∑ i, ∑ j,
          (w i : ℂ) * ((M i j : ℝ) : ℂ) * (k j : ℂ)) +
          (∑ i, ∑ j,
          (k i : ℂ) * ((M i j : ℝ) : ℂ) * (w j : ℂ))) := by
    calc
      _ = ∑ i, Complex.I * ((∑ j,
          (w i : ℂ) * ((M i j : ℝ) : ℂ) * (k j : ℂ)) +
          (∑ j, (k i : ℂ) * ((M i j : ℝ) : ℂ) * (w j : ℂ))) := by
            apply Fintype.sum_congr
            intro i
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = Complex.I * (∑ i, ((∑ j,
          (w i : ℂ) * ((M i j : ℝ) : ℂ) * (k j : ℂ)) +
          (∑ j, (k i : ℂ) * ((M i j : ℝ) : ℂ) * (w j : ℂ)))) := by
            rw [← Finset.mul_sum]
      _ = _ := by rw [Finset.sum_add_distrib]
  have hquad :
      (∑ i, ∑ j,
        ((w i : ℂ) - Complex.I * (k i : ℂ)) *
          ((M i j : ℝ) : ℂ) *
          ((w j : ℂ) - Complex.I * (k j : ℂ))) =
        Qww - Qkk - Complex.I * (Qwk + Qkw) := by
    calc
      _ = ∑ i, ∑ j,
          ((w i : ℂ) * ((M i j : ℝ) : ℂ) * (w j : ℂ) -
            (k i : ℂ) * ((M i j : ℝ) : ℂ) * (k j : ℂ) -
            Complex.I * ((w i : ℂ) * ((M i j : ℝ) : ℂ) * (k j : ℂ) +
              (k i : ℂ) * ((M i j : ℝ) : ℂ) * (w j : ℂ))) := by
            apply Fintype.sum_congr
            intro i
            apply Fintype.sum_congr
            intro j
            ring_nf
            simp only [Complex.I_sq]
            ring
      _ = Qww - Qkk - Complex.I * (Qwk + Qkw) := by
            simp only [Finset.sum_sub_distrib]
            rw [hCross]
            rfl
  rw [hquad]
  have hexp : (Real.pi : ℂ) * (Qww - Qkk - Complex.I * (Qwk + Qkw)) =
      (Real.pi : ℂ) * Qww + (-(Real.pi : ℂ) * Qkk) +
        (-(Real.pi : ℂ) * Complex.I * (Qwk + Qkw)) := by ring
  rw [hexp, Complex.exp_add, Complex.exp_add]

theorem dualDXYDualQuadraticExp_real {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ)
    (w : ι → ℝ) (k : ι → ℤ) :
    dualQuadraticExp A (fun i => (w i : ℂ)) k =
      Complex.exp ((Real.pi : ℂ) * dualDComplexBilinear A⁻¹ w w) *
      Complex.exp (-(Real.pi : ℂ) *
        dualDComplexBilinear A⁻¹ (fun i => (k i : ℝ))
          (fun i => (k i : ℝ))) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I *
        (dualDComplexBilinear A⁻¹ w (fun i => (k i : ℝ)) +
          dualDComplexBilinear A⁻¹ (fun i => (k i : ℝ)) w)) := by
  simpa [dualQuadraticExp] using dualDComplexQuadraticExpansion A⁻¹ w k

/-- The shifted XY dual Gaussian is exactly its cycle-class sum in every
dimension. -/
theorem xyShiftedCycleGaussianSumD_eq_cycleTsum {d : ℕ} {B : Box d}
    (β : ℝ) (x y : XYSites B) :
    xyShiftedCycleGaussianSum β x y =
      ∑' c : XYEndpointCycleModes (B := B),
        dualDXYCycleGaussianWeight β (xyEndpointPathModes x y) c := by
  rw [xyShiftedCycleGaussianSum_eq_fourierCoefficientGaussian]
  let s : Set (XYBondModes (B := B)) :=
    {m | xyBondModeDivergence m = 0}
  let f : XYBondModes (B := B) → ℝ := fun m =>
    ∏ b : XYBonds B, Real.exp
      (-(((m b + xyEndpointPathModes x y b : ℤ) : ℝ) ^ 2) / (2 * β))
  calc
    _ = ∑' m : XYBondModes (B := B), s.indicator f m := by
          apply tsum_congr
          intro m
          by_cases h : xyBondModeDivergence m = 0 <;> simp [s, f, h]
    _ = ∑' c : s, f c := (tsum_subtype s f).symm
    _ = _ := by
          apply tsum_congr
          intro c
          rfl

/-- Reindex the cycle-class sum by the integer basis coordinates. -/
theorem xyShiftedCycleGaussianSum_eq_cycleCoordinateTsum {d : ℕ}
    {B : Box d} (β : ℝ) (x y : XYSites B) :
    xyShiftedCycleGaussianSum β x y =
      ∑' n : Fin (degreeOneCycleBasis B).1 → ℤ,
        dualDXYCycleGaussianWeight β (xyEndpointPathModes x y)
          ((xyDCycleCoordinatesEquiv (B := B)).symm n) := by
  rw [xyShiftedCycleGaussianSumD_eq_cycleTsum]
  let e := xyDCycleCoordinatesEquiv (B := B)
  calc
    _ = ∑' c : XYEndpointCycleModes (B := B),
          dualDXYCycleGaussianWeight β (xyEndpointPathModes x y)
            (e.symm (e c)) := by
          apply tsum_congr
          intro c
          simp [e]
    _ = ∑' n : Fin (degreeOneCycleBasis B).1 → ℤ,
          dualDXYCycleGaussianWeight β (xyEndpointPathModes x y)
          (e.symm n) :=
          e.tsum_eq (fun n => dualDXYCycleGaussianWeight β
            (xyEndpointPathModes x y) (e.symm n))

set_option linter.style.haveILetI false in
/-- The inverse Poisson bilinear form is the `2πβ`-scaled inverse cycle Gram
form. -/
theorem dualDXYBilinear_scaledInverse {d : ℕ} {B : Box d} {β : ℝ}
    (hβ : 0 < β)
    (u v : Fin (degreeOneCycleBasis B).1 → ℝ) :
    dualDComplexBilinear (dualDXYCoordinateMatrix (B := B) β)⁻¹ u v =
      ((2 * Real.pi * β * dotProduct u
        ((degreeOneCycleGramMatrix B)⁻¹.mulVec v) : ℝ) : ℂ) := by
  rw [dualDComplexBilinear_eq_dotProduct, dualDXYCoordinateMatrix_inv hβ]
  simp [Matrix.smul_mulVec, dotProduct_smul]

/-- The shifted cycle summand is the path norm times the tested primal
Gaussian in cycle coordinates. -/
theorem dualDXYCycleGaussianWeight_eq_testedPrimalTerm {d : ℕ}
    (hd : 3 ≤ d) {B : Box d} {β : ℝ} (hβ : 0 < β)
    (x y : XYSites B) (n : Fin (degreeOneCycleBasis B).1 → ℤ) :
    ((dualDXYCycleGaussianWeight β (xyEndpointPathModes x y)
      ((xyDCycleCoordinatesEquiv (B := B)).symm n) : ℝ) : ℂ) =
      Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
        (dualDXYPathChainVector x y) : ℝ) / (2 * β)) *
        testedPrimalTerm (dualDXYCoordinateMatrix (B := B) β)
          (dualDXYPathCoordinates hd x y) (-β⁻¹) n := by
  let G := degreeOneCycleGramMatrix B
  let A := dualDXYCoordinateMatrix (B := B) β
  let p := dualDXYPathCoordinates hd x y
  let nr : Fin (degreeOneCycleBasis B).1 → ℝ := fun i => (n i : ℝ)
  rw [dualDXYCycleGaussianWeight_eq_coordinateTerm hd x y n]
  rw [dualDTestedPrimalTerm_eq]
  unfold primalQuadraticExp realTiltParameter
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  apply congrArg Complex.exp
  have hquad :
      (∑ i, ∑ j, (n i : ℂ) * (A i j : ℂ) * (n j : ℂ)) =
        ((dotProduct nr (A.mulVec nr) : ℝ) : ℂ) := by
    simpa [dualDComplexBilinear, nr] using
      (dualDComplexBilinear_eq_dotProduct A nr nr)
  have hscaled : dotProduct nr (A.mulVec nr) =
      (2 * Real.pi * β)⁻¹ *
        dotProduct nr (G.mulVec nr) := by
    simp [A, G, dualDXYCoordinateMatrix, Matrix.smul_mulVec,
      dotProduct_smul, nr]
  have hlinReal :
      (2 * Real.pi) * ∑ i,
        ((-β⁻¹ * p i / (2 * Real.pi)) * nr i) =
          -dotProduct nr p / β := by
    have hcoeff (i : Fin (degreeOneCycleBasis B).1) :
        2 * Real.pi * (-β⁻¹ * p i / (2 * Real.pi)) = -β⁻¹ * p i := by
      field_simp [Real.pi_ne_zero]
    calc
      _ = ∑ i, (2 * Real.pi *
          (-β⁻¹ * p i / (2 * Real.pi))) * nr i := by
            rw [Finset.mul_sum]
            apply Fintype.sum_congr
            intro i
            ring
      _ = ∑ i, (-β⁻¹ * p i) * nr i := by
            apply Fintype.sum_congr
            intro i
            rw [hcoeff]
      _ = ∑ i, (-β⁻¹) * (p i * nr i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = -β⁻¹ * ∑ i, p i * nr i := (Finset.mul_sum ..).symm
      _ = -dotProduct nr p / β := by
            simp [dotProduct, mul_comm, div_eq_mul_inv]
  have hlin :
      (2 * Real.pi : ℂ) * ∑ i,
        (((-β⁻¹ * p i / (2 * Real.pi) : ℝ) : ℂ) * (n i : ℂ)) =
          ((-dotProduct nr p / β : ℝ) : ℂ) := by
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) hlinReal
    simpa [nr, Complex.ofReal_mul, Complex.ofReal_div] using hcast
  rw [hquad, hscaled, hlin]
  dsimp [A, G, p, nr]
  push_cast
  field_simp [Real.pi_ne_zero, ne_of_gt hβ]
  ring_nf

/-- A cycle-coordinate current contributes the centered quotient-Gaussian
characteristic and its endpoint path phase to the shifted dual Gaussian. -/
theorem dualDXYDualTerm_eq_correctedPhase {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} {β : ℝ} (hβ : 0 < β) (x y : XYSites B)
    (k : Fin (degreeOneCycleBasis B).1 → ℤ) :
    dualQuadraticExp (dualDXYCoordinateMatrix (B := B) β)
        (realTiltParameter (dualDXYPathCoordinates hd x y) (-β⁻¹)) k =
      Complex.exp ((inner ℝ (dualDXYPathSource hd x y)
        (dualDXYPathTau hd x y) : ℝ) / (2 * β)) *
        dualDXYCurrentPhase hd (le_of_lt hβ) x y k := by
  let G := degreeOneCycleGramMatrix B
  let A := dualDXYCoordinateMatrix (B := B) β
  let p := dualDXYPathCoordinates hd x y
  let wr : Fin (degreeOneCycleBasis B).1 → ℝ :=
    fun i => -β⁻¹ * p i / (2 * Real.pi)
  let kr : Fin (degreeOneCycleBasis B).1 → ℝ := fun i => (k i : ℝ)
  let μ := dualDCoordinateCurrent hd B kr
  have hwr : wr = (-(2 * Real.pi * β)⁻¹) • p := by
    funext i
    dsimp [wr]
    field_simp [Real.pi_ne_zero, ne_of_gt hβ]
  have hApos : A.PosDef := dualDXYCoordinateMatrix_posDef hβ
  have hAsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hApos.isHermitian
  have hAinvSymm : A⁻¹.IsSymm := hAsymm.inv
  have hcomm := dualDComplexBilinear_comm A⁻¹ hAinvSymm wr kr
  have hsourcePair :
      inner ℝ (dualDXYPathSource hd x y)
          (dualDXYPathTau hd x y) =
        dotProduct p (G⁻¹.mulVec p) := by
    have h := dualDHodgeInverse_eq_inverseCycleGram hd B
      (dualDXYPathSource hd x y)
    simpa [dualDXYPathTau, dualDXYPathCoordinates,
      hodgeLiftCoordinates, p, G] using h
  have hpair : inner ℝ μ.1 (dualDXYPathTau hd x y).1 =
      dotProduct kr (G⁻¹.mulVec p) := by
    exact dualDXYCoordinateCurrent_pathPairing hd x y kr
  have hscaleDot :
      dotProduct ((-(2 * Real.pi * β)⁻¹) • p)
        (G⁻¹.mulVec ((-(2 * Real.pi * β)⁻¹) • p)) =
        (-(2 * Real.pi * β)⁻¹) ^ 2 * dotProduct p (G⁻¹.mulVec p) := by
    calc
      _ = dotProduct ((-(2 * Real.pi * β)⁻¹) • p)
          ((-(2 * Real.pi * β)⁻¹) • G⁻¹.mulVec p) := by
            rw [Matrix.mulVec_smul]
      _ = (-(2 * Real.pi * β)⁻¹) ^ 2 * dotProduct p (G⁻¹.mulVec p) := by
            rw [smul_dotProduct, dotProduct_smul]
            simp only [smul_eq_mul]
            ring
  have hww : (Real.pi : ℂ) * dualDComplexBilinear A⁻¹ wr wr =
      ((inner ℝ (dualDXYPathSource hd x y)
        (dualDXYPathTau hd x y) / (2 * β) : ℝ) : ℂ) := by
    rw [dualDXYBilinear_scaledInverse hβ, hwr, hscaleDot, ← hsourcePair]
    push_cast
    field_simp [Real.pi_ne_zero, ne_of_gt hβ]
  have hkk : -(Real.pi : ℂ) *
      dualDComplexBilinear A⁻¹ kr kr =
        ((-(2 * Real.pi ^ 2 * β * dotProduct kr (G⁻¹.mulVec kr)) : ℝ) : ℂ) := by
    rw [dualDXYBilinear_scaledInverse hβ]
    push_cast
    ring
  have hgauss : Complex.exp (-(Real.pi : ℂ) *
      dualDComplexBilinear A⁻¹ kr kr) =
      Complex.exp (-(2 * Real.pi ^ 2 * β *
          dotProduct kr (G⁻¹.mulVec kr) : ℝ)) := by
    rw [hkk]
    simp only [Complex.ofReal_neg]
  have hrightScale : dotProduct kr
      (G⁻¹.mulVec ((-(2 * Real.pi * β)⁻¹) • p)) =
      (-(2 * Real.pi * β)⁻¹) * dotProduct kr (G⁻¹.mulVec p) := by
    calc
      _ = dotProduct kr ((-(2 * Real.pi * β)⁻¹) • G⁻¹.mulVec p) := by
            rw [Matrix.mulVec_smul]
      _ = (-(2 * Real.pi * β)⁻¹) • dotProduct kr (G⁻¹.mulVec p) :=
            dotProduct_smul _ _ _
      _ = _ := by simp [smul_eq_mul]
  have hkw : dualDComplexBilinear A⁻¹ kr wr =
      -((dotProduct kr (G⁻¹.mulVec p) : ℝ) : ℂ) := by
    rw [dualDXYBilinear_scaledInverse hβ, hwr, hrightScale]
    push_cast
    field_simp [Real.pi_ne_zero, ne_of_gt hβ]
  have hmixed : -(Real.pi : ℂ) * Complex.I *
      (dualDComplexBilinear A⁻¹ wr kr +
        dualDComplexBilinear A⁻¹ kr wr) =
      Complex.I * (2 * Real.pi : ℂ) *
        ((dotProduct kr (G⁻¹.mulVec p) : ℝ) : ℂ) := by
    rw [hcomm, hkw]
    ring
  have hparam : (fun i => (wr i : ℂ)) =
      realTiltParameter p (-β⁻¹) := by
    funext i
    simp [wr, realTiltParameter]
  have hexpand := dualDXYDualQuadraticExp_real A wr k
  rw [hparam, hww, hgauss, hmixed] at hexpand
  rw [dualDXYCurrentPhase_eq_formula hd (le_of_lt hβ) x y k]
  change dualQuadraticExp A (realTiltParameter p (-β⁻¹)) k =
      Complex.exp ((inner ℝ (dualDXYPathSource hd x y)
        (dualDXYPathTau hd x y) : ℝ) / (2 * β)) *
        (Complex.exp (-(2 * Real.pi ^ 2 * β *
          dotProduct kr (G⁻¹.mulVec kr) : ℝ)) *
        Complex.exp (Complex.I * (2 * Real.pi : ℂ) *
          ((dotProduct kr (G⁻¹.mulVec p) : ℝ) : ℂ)))
  calc
    _ = Complex.exp ((inner ℝ (dualDXYPathSource hd x y)
          (dualDXYPathTau hd x y) : ℝ) / (2 * β)) *
        Complex.exp (-(2 * Real.pi ^ 2 * β *
          dotProduct kr (G⁻¹.mulVec kr) : ℝ)) *
        Complex.exp (Complex.I * (2 * Real.pi : ℂ) *
          ((dotProduct kr (G⁻¹.mulVec p) : ℝ) : ℂ)) := by
            simpa only [Complex.ofReal_div, Complex.ofReal_mul,
              Complex.ofReal_ofNat, Complex.ofReal_natCast] using hexpand
    _ = _ := by ring

/-- The shifted cycle weight is summable, by restricting the shifted bond
Gaussian to the divergence-free sublattice. -/
theorem dualDXYCycleGaussianWeight_coordinate_summable {d : ℕ}
    {B : Box d} {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    Summable (fun n : Fin (degreeOneCycleBasis B).1 → ℤ =>
      dualDXYCycleGaussianWeight β (xyEndpointPathModes x y)
        ((xyDCycleCoordinatesEquiv (B := B)).symm n)) := by
  have hcycle : Summable (fun c : XYEndpointCycleModes (B := B) =>
      dualDXYCycleGaussianWeight β (xyEndpointPathModes x y) c) := by
    have hsub : Summable (fun c : XYEndpointCycleModes (B := B) =>
        xyShiftedCycleGaussianTerm β x y c.1) :=
      (xyShiftedCycleGaussianTerm_summable β hβ x y).subtype
        (fun m => xyBondModeDivergence m = 0)
    apply hsub.congr
    intro c
    simp [xyShiftedCycleGaussianTerm, dualDXYCycleGaussianWeight,
      xyDualGaussianProduct, xyVillainGaussianCoeff, c.2]
  let e := xyDCycleCoordinatesEquiv (B := B)
  let f : XYEndpointCycleModes (B := B) → ℝ := fun c =>
    dualDXYCycleGaussianWeight β (xyEndpointPathModes x y) c
  have hcomp : Summable (fun n : Fin (degreeOneCycleBasis B).1 → ℤ =>
      f (e.symm n)) := (Equiv.summable_iff (f := f) e.symm).2 hcycle
  simpa [f, e] using hcomp

set_option linter.style.haveILetI false in
/-- Finite-dimensional Poisson summation for the all-dimensional shifted XY
cycle Gaussian, before factoring the endpoint residual. -/
theorem xyShiftedCycleGaussianSum_eq_coordinatePoisson {d : ℕ}
    (hd : 3 ≤ d) {B : Box d} {β : ℝ} (hβ : 0 < β)
    (x y : XYSites B) :
    ((xyShiftedCycleGaussianSum β x y : ℝ) : ℂ) =
      dualDXYPoissonConstant (B := B) β *
        Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
          (dualDXYPathChainVector x y) : ℝ) / (2 * β)) *
        ∑' k : Fin (degreeOneCycleBasis B).1 → ℤ,
          dualQuadraticExp (dualDXYCoordinateMatrix (B := B) β)
            (realTiltParameter (dualDXYPathCoordinates hd x y) (-β⁻¹)) k := by
  let A := dualDXYCoordinateMatrix (B := B) β
  let p := dualDXYPathCoordinates hd x y
  let w := realTiltParameter p (-β⁻¹)
  let f : (Fin (degreeOneCycleBasis B).1 → ℤ) → ℝ := fun n =>
    dualDXYCycleGaussianWeight β (xyEndpointPathModes x y)
      ((xyDCycleCoordinatesEquiv (B := B)).symm n)
  have hf : Summable f := by
    simpa [f] using dualDXYCycleGaussianWeight_coordinate_summable hβ x y
  have hPoisson := tsum_cexp_neg_quadratic_pi A
    (dualDXYCoordinateMatrix_posDef hβ) w
  have hPoisson' :
      (∑' n : Fin (degreeOneCycleBasis B).1 → ℤ,
        primalQuadraticExp A w n) =
        ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
          ∑' k : Fin (degreeOneCycleBasis B).1 → ℤ,
            dualQuadraticExp A w k := by
    simpa [primalQuadraticExp, dualQuadraticExp] using hPoisson
  calc
    ((xyShiftedCycleGaussianSum β x y : ℝ) : ℂ) =
        Complex.ofReal (∑' c : XYEndpointCycleModes (B := B),
          dualDXYCycleGaussianWeight β (xyEndpointPathModes x y) c) := by
          rw [xyShiftedCycleGaussianSumD_eq_cycleTsum]
    _ = Complex.ofReal (∑' n : Fin (degreeOneCycleBasis B).1 → ℤ, f n) := by
          congr 1
          calc
            _ = xyShiftedCycleGaussianSum β x y :=
              (xyShiftedCycleGaussianSumD_eq_cycleTsum β x y).symm
            _ = _ := by
              simpa [f] using xyShiftedCycleGaussianSum_eq_cycleCoordinateTsum β x y
    _ = ∑' n : Fin (degreeOneCycleBasis B).1 → ℤ, (f n : ℂ) :=
          Complex.ofReal_tsum (f := f)
    _ = ∑' n : Fin (degreeOneCycleBasis B).1 → ℤ,
          Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
            (dualDXYPathChainVector x y) : ℝ) / (2 * β)) *
            testedPrimalTerm A p (-β⁻¹) n := by
          apply tsum_congr
          intro n
          simpa [A, p, f] using
            dualDXYCycleGaussianWeight_eq_testedPrimalTerm hd hβ x y n
    _ = Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
          (dualDXYPathChainVector x y) : ℝ) / (2 * β)) *
          ∑' n : Fin (degreeOneCycleBasis B).1 → ℤ,
            testedPrimalTerm A p (-β⁻¹) n := by
          rw [← tsum_mul_left]
    _ = Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
          (dualDXYPathChainVector x y) : ℝ) / (2 * β)) *
          ∑' n : Fin (degreeOneCycleBasis B).1 → ℤ,
            primalQuadraticExp A w n := by
          congr 1
          apply tsum_congr
          intro n
          exact dualDTestedPrimalTerm_eq A p (-β⁻¹) n
    _ = Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
          (dualDXYPathChainVector x y) : ℝ) / (2 * β)) *
          (((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
            ∑' k : Fin (degreeOneCycleBasis B).1 → ℤ,
              dualQuadraticExp A w k) := by
          rw [hPoisson']
    _ = dualDXYPoissonConstant β *
          Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
            (dualDXYPathChainVector x y) : ℝ) / (2 * β)) *
          ∑' k : Fin (degreeOneCycleBasis B).1 → ℤ,
            dualQuadraticExp A w k := by
          simp [dualDXYPoissonConstant, A]
          ring

set_option linter.style.haveILetI false in
/-- The all-dimensional shifted cycle sum equals the centered current phase
series with its path-residual correction. -/
theorem xyShiftedCycleGaussianSumD_eq_dualPhase {d : ℕ} (hd : 3 ≤ d)
    {B : Box d} {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    ((xyShiftedCycleGaussianSum β x y : ℝ) : ℂ) =
      dualDXYPoissonConstant (B := B) β *
        Complex.exp (-dualDXYResidualEnergy hd x y / (2 * β)) *
        ∑' q : Fin (degreeOneCycleBasis B).1 → ℤ,
          dualDXYCurrentPhase hd (le_of_lt hβ) x y q := by
  let A := dualDXYCoordinateMatrix (B := B) β
  let p := dualDXYPathCoordinates hd x y
  let w := realTiltParameter p (-β⁻¹)
  let corr : ℂ := Complex.exp
    (((inner ℝ (dualDXYPathSource hd x y)
      (dualDXYPathTau hd x y) : ℝ) : ℂ) / (2 * (β : ℂ)))
  have hdualTsum :
      (∑' k : Fin (degreeOneCycleBasis B).1 → ℤ,
        dualQuadraticExp A w k) =
        corr * ∑' q : Fin (degreeOneCycleBasis B).1 → ℤ,
          dualDXYCurrentPhase hd (le_of_lt hβ) x y q := by
    calc
      _ = ∑' k : Fin (degreeOneCycleBasis B).1 → ℤ,
          corr * dualDXYCurrentPhase hd (le_of_lt hβ) x y k := by
            apply tsum_congr
            intro k
            simpa [corr, A, w, Complex.ofReal_div, Complex.ofReal_mul,
              Complex.ofReal_ofNat, Complex.ofReal_natCast] using
                dualDXYDualTerm_eq_correctedPhase hd hβ x y k
      _ = corr * ∑' k : Fin (degreeOneCycleBasis B).1 → ℤ,
          dualDXYCurrentPhase hd (le_of_lt hβ) x y k := by
            rw [← tsum_mul_left]
  have hexp :
      Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
        (dualDXYPathChainVector x y) : ℝ) / (2 * β)) * corr =
        Complex.exp (-dualDXYResidualEnergy hd x y / (2 * β)) := by
    dsimp [corr]
    rw [← Complex.exp_add]
    congr 1
    rw [dualDXYResidualEnergy, dualDXYPathVector_energy_eq_chain]
    field_simp [ne_of_gt hβ]
    rw [Complex.ofReal_sub]
    ring
  calc
    _ = dualDXYPoissonConstant (B := B) β *
        Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
          (dualDXYPathChainVector x y) : ℝ) / (2 * β)) *
        (corr * ∑' q : Fin (degreeOneCycleBasis B).1 → ℤ,
          dualDXYCurrentPhase hd (le_of_lt hβ) x y q) := by
          rw [xyShiftedCycleGaussianSum_eq_coordinatePoisson hd hβ x y,
            hdualTsum]
    _ = dualDXYPoissonConstant (B := B) β *
        (Complex.exp (-(inner ℝ (dualDXYPathChainVector x y)
          (dualDXYPathChainVector x y) : ℝ) / (2 * β)) * corr) *
        ∑' q : Fin (degreeOneCycleBasis B).1 → ℤ,
          dualDXYCurrentPhase hd (le_of_lt hβ) x y q := by ring
    _ = _ := by rw [hexp]


end FroehlichSpencer.FS82.XY

end
