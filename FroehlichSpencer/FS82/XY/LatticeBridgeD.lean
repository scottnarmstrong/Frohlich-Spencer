/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.MixtureD
public import FroehlichSpencer.FS82.XY.PoissonPhaseD

/-!
This file identifies the two:

* the prism filling of an integer cycle is integer-valued, so an integer co-closed form has
  integral coordinates (`inner_currentVector_cycleLift_int`);
* the boundary of a plaquette is an integer combination of the basis cycles, and a co-closed form
  does not see `ker d₁`, so a form with integral coordinates is integer-valued
  (`coClosed_apply_eq_sum_coords`, `coordinateCurrent_int`);
* a co-closed form with zero coordinates is zero (`coClosed_eq_zero_of_liftCoordinates`).

Hence `coordinateCurrentEquiv : (Fin r → ℤ) ≃ {j // j integer-valued and co-closed}`, and

`∑_q dualDXYCurrentPhase hd hβ x y q = closedCharacterSum hd β (2π τ)`
(`tsum_dualDXYCurrentPhase_eq`), with `τ = dualDXYPathTau hd x y`.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.XY.GaugeAverage
open Module

/-! ## Co-closed forms and lift coordinates in an exact-one complex -/

section Abstract

variable {V E P : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

/-- A co-closed form is orthogonal to the kernel of `d₁`. -/
theorem inner_coClosed_ker_eq_zero (C : ExactOneComplex V E P) (μ : coClosed C)
    (x : EuclideanSpace ℝ E) (hx : C.d₁ x = 0) : inner ℝ (μ : EuclideanSpace ℝ E) x = 0 := by
  obtain ⟨w, rfl⟩ := C.exactOne (LinearMap.mem_ker.mpr hx)
  rw [← LinearMap.adjoint_inner_left]
  have hμ : C.d₀.adjoint (μ : EuclideanSpace ℝ E) = 0 := LinearMap.mem_ker.mp μ.2
  rw [hμ, inner_zero_left]

/-- A co-closed form with zero lift coordinates is zero. -/
theorem coClosed_eq_zero_of_liftCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ExactOneComplex V E P) (b : Basis ι ℝ C.d₁.range) (lift : ι → EuclideanSpace ℝ E)
    (hlift : ∀ i, C.d₁ (lift i) = (b i : EuclideanSpace ℝ P)) (μ : coClosed C)
    (h : ∀ i, inner ℝ (μ : EuclideanSpace ℝ E) (lift i) = 0) :
    (μ : EuclideanSpace ℝ E) = 0 := by
  set u : EuclideanSpace ℝ E := (hodgeInverseOnCoClosed C μ : EuclideanSpace ℝ E) with hu
  have hval : formLaplacian C u = μ := congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C μ)
  have horth : ∀ i, inner ℝ (C.d₁ u) (b i : EuclideanSpace ℝ P) = 0 := by
    intro i
    rw [← hlift i, ← LinearMap.adjoint_inner_left]
    change inner ℝ (formLaplacian C u) (lift i) = 0
    rw [hval]
    exact h i
  let y : C.d₁.range := ⟨C.d₁ u, ⟨u, rfl⟩⟩
  have hrepr : C.d₁ u = ∑ i, b.repr y i • (b i : EuclideanSpace ℝ P) := by
    have hsum := congrArg (fun z : C.d₁.range => (z : EuclideanSpace ℝ P)) (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    exact hsum.symm
  have hy : inner ℝ (C.d₁ u) (C.d₁ u) = 0 := by
    nth_rewrite 2 [hrepr]
    rw [inner_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [real_inner_smul_right, horth i, mul_zero]
  have hd₁ : C.d₁ u = 0 := inner_self_eq_zero.mp hy
  rw [← hval]
  change C.d₁.adjoint (C.d₁ u) = 0
  rw [hd₁, map_zero]

end Abstract

/-! ## The cycle lifts of the dual complex -/

variable {d : ℕ} {B : Box d}

/-- The star and compression of a chain, in coordinates. -/
theorem dualDStarCompressLinear_apply (k : ℕ) (p : RealChain d B) (e : DualDForm B (d - k)) :
    dualDStarCompressLinear (B := B) k p e = p (primalDualCellEquiv.symm e.1) := by
  simp [dualDStarCompressLinear, starMap, dualDFormEmbedding, Finsupp.equivMapDomain_apply]

/-- The prism lift of the `i`-th basis cycle. -/
noncomputable abbrev cycleLift (B : Box d) (i : Fin (degreeOneCycleBasis B).1) :
    EuclideanSpace ℝ (DualDForm B (d - 2)) :=
  dualDCycleFillingLift (degreeOneRealCycleBasisExplicit B i)

/-- The prism lift of an integral cycle is integer-valued. -/
theorem cycleLift_int (i : Fin (degreeOneCycleBasis B).1) (e : DualDForm B (d - 2)) :
    ∃ n : ℤ, cycleLift B i e = (n : ℝ) := by
  refine ⟨fillingOperator (fun i => ⟨0, Nat.zero_lt_succ (B i)⟩)
    (degreeOneCycleBasisChain B i) (primalDualCellEquiv.symm e.1), ?_⟩
  change dualDStarCompressLinear (B := B) 2
    (realFillingOperator (fun i => ⟨0, Nat.zero_lt_succ (B i)⟩)
      (degreeOneRealCycleBasisExplicit B i).1) e = _
  rw [dualDStarCompressLinear_apply, degreeOneRealCycleBasisExplicit_val, realFillingOperator,
    realifyLinearMap_cast, castIntegerChain_apply]

/-- An integer current has integral lift coordinates. -/
theorem inner_currentVector_cycleLift_int (j : DualDForm B (d - 2) → ℤ)
    (i : Fin (degreeOneCycleBasis B).1) :
    ∃ n : ℤ, inner ℝ (currentVector j) (cycleLift B i) = (n : ℝ) := by
  choose m hm using cycleLift_int (B := B) i
  refine ⟨∑ e, j e * m e, ?_⟩
  rw [PiLp.inner_apply, Int.cast_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hm e, currentVector_apply]
  push_cast
  ring

theorem dualDD₁_cycleLift (hd : 3 ≤ d) (i : Fin (degreeOneCycleBasis B).1) :
    dualDD₁ (cycleLift B i) =
      dualDStarCompressLinear (B := B) 1 (castIntegerChain (degreeOneCycleBasisChain B i)) := by
  rw [dualDD₁_cycleFillingLift hd, degreeOneRealCycleBasisExplicit_val]

theorem cycleLift_hlift (hd : 3 ≤ d) (i : Fin (degreeOneCycleBasis B).1) :
    (dualDExactOneComplex hd B).d₁ (cycleLift B i) =
      (dualDImageCycleBasisForHodge hd B i : EuclideanSpace ℝ (DualDForm B (d - 1))) := by
  change dualDD₁ (dualDCycleFillingLift (degreeOneRealCycleBasisExplicit B i)) =
    (dualDImageCycleBasis hd B i : EuclideanSpace ℝ (DualDForm B (d - 1)))
  rw [dualDImageCycleBasis_apply]
  rfl

/-- The indicator of a cell of degree `d − 2` is the star of its plaquette. -/
theorem single_eq_starCompress (e : DualDForm B (d - 2)) :
    (EuclideanSpace.single e (1 : ℝ) : EuclideanSpace ℝ (DualDForm B (d - 2))) =
      dualDStarCompressLinear (B := B) 2 (Finsupp.single (primalDualCellEquiv.symm e.1) 1) := by
  ext f
  rw [dualDStarCompressLinear_apply]
  by_cases hfe : f = e
  · subst hfe
    simp
  · have hne : primalDualCellEquiv.symm e.1 ≠ primalDualCellEquiv.symm f.1 := fun h =>
      hfe (Subtype.ext (primalDualCellEquiv.symm.injective h.symm))
    simp [hfe, hne]

/-- **The boundary of a plaquette in the cycle basis**: the indicator of a cell differs from an
integer combination of the cycle lifts by an element of `ker d₁`. -/
theorem exists_single_sub_lift_mem_ker (hd : 3 ≤ d) (e : DualDForm B (d - 2)) :
    ∃ n : Fin (degreeOneCycleBasis B).1 → ℤ,
      dualDD₁ ((EuclideanSpace.single e (1 : ℝ) : EuclideanSpace ℝ (DualDForm B (d - 2))) -
        ∑ i, (n i : ℝ) • cycleLift B i) = 0 := by
  classical
  set p : Cell d B := primalDualCellEquiv.symm e.1 with hp
  have hpdeg : cellDegree p = 2 := by
    have h := dualDStarComplementaryDegree (primalDualCellEquiv.symm e.1)
    rw [Equiv.apply_symm_apply, e.2] at h
    rw [hp]
    omega
  have hbasis : homogeneousSupport (basisChain p) 2 := by
    intro c hc
    have hcp : c = p := by
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hc) (by simp [basisChain, hne])
    rw [hcp, hpdeg]
  have hbd : homogeneousSupport (boundary (basisChain p)) 1 :=
    xyIntegerBoundary_homogeneousSupport (basisChain p) 2 (by norm_num) hbasis
  have hsq : boundary (boundary (basisChain p)) = 0 := by
    have h := congrArg (fun f : Chain d B →ₗ[ℤ] Chain d B => f (basisChain p))
      (boundary_square_zero (d := d) (B := B))
    exact h
  let z : degreeOneCycleSubmodule (B := B) := ⟨⟨boundary (basisChain p), hbd⟩, hsq⟩
  let n : Fin (degreeOneCycleBasis B).1 → ℤ := fun i => (degreeOneCycleBasis B).2.repr z i
  have hz : boundary (basisChain p) = ∑ i, n i • degreeOneCycleBasisChain B i := by
    have hsum := congrArg
      (fun w : degreeOneCycleSubmodule (B := B) => ((w : degreeChainSubmodule (B := B) 1) :
        Chain d B)) ((degreeOneCycleBasis B).2.sum_repr z)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    exact hsum.symm
  refine ⟨n, ?_⟩
  rw [map_sub, map_sum, single_eq_starCompress]
  have hsingle : realHomogeneousSupport (Finsupp.single p (1 : ℝ)) 2 := by
    intro c hc
    have hcp : c = p := by
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hc) (by simp [Ne.symm hne])
    rw [hcp, hpdeg]
  rw [dualDD₁_starFilling hd _ hsingle]
  have hreal : realBoundary (Finsupp.single p (1 : ℝ)) =
      castIntegerChain (boundary (basisChain p)) := by
    rw [realBoundary, realifyLinearMap_single, one_smul]
  rw [hreal, hz]
  have hcast : castIntegerChain (∑ i, n i • degreeOneCycleBasisChain B i) =
      ∑ i, (n i : ℝ) • castIntegerChain (degreeOneCycleBasisChain B i) := by
    ext c
    simp [castIntegerChain_apply, Finsupp.finsetSum_apply]
  rw [hcast, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, dualDD₁_cycleLift hd]

/-- **A co-closed form in lift coordinates**, cell by cell. -/
theorem coClosed_apply_eq_sum_coords (hd : 3 ≤ d) (e : DualDForm B (d - 2)) :
    ∃ n : Fin (degreeOneCycleBasis B).1 → ℤ, ∀ μ : coClosed (dualDExactOneComplex hd B),
      (μ : EuclideanSpace ℝ (DualDForm B (d - 2))) e =
        ∑ i, (n i : ℝ) * inner ℝ (μ : EuclideanSpace ℝ (DualDForm B (d - 2))) (cycleLift B i) := by
  obtain ⟨n, hn⟩ := exists_single_sub_lift_mem_ker hd e
  refine ⟨n, fun μ => ?_⟩
  have h0 := inner_coClosed_ker_eq_zero (dualDExactOneComplex hd B) μ _ hn
  rw [inner_sub_right, inner_sum, sub_eq_zero] at h0
  have hleft : inner ℝ (μ : EuclideanSpace ℝ (DualDForm B (d - 2)))
      (EuclideanSpace.single e (1 : ℝ)) = (μ : EuclideanSpace ℝ (DualDForm B (d - 2))) e := by
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [← hleft, h0]
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_right]

/-! ## The coordinate currents are the integer co-closed currents -/

theorem coordinateCurrent_coords (hd : 3 ≤ d) (q : Fin (degreeOneCycleBasis B).1 → ℝ)
    (i : Fin (degreeOneCycleBasis B).1) :
    inner ℝ ((dualDCoordinateCurrent hd B q : DualDCoClosed hd B) :
      EuclideanSpace ℝ (DualDForm B (d - 2))) (cycleLift B i) = q i :=
  congrFun (dualDCoordinateCurrent_liftCoordinates hd B q) i

/-- A coordinate current with integral coordinates is integer-valued. -/
theorem coordinateCurrent_int (hd : 3 ≤ d) (q : Fin (degreeOneCycleBasis B).1 → ℤ)
    (e : DualDForm B (d - 2)) :
    ∃ m : ℤ, ((dualDCoordinateCurrent hd B fun i => (q i : ℝ) : DualDCoClosed hd B) :
      EuclideanSpace ℝ (DualDForm B (d - 2))) e = (m : ℝ) := by
  obtain ⟨n, hn⟩ := coClosed_apply_eq_sum_coords hd e
  refine ⟨∑ i, n i * q i, ?_⟩
  rw [hn (dualDCoordinateCurrent hd B fun i => (q i : ℝ)), Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordinateCurrent_coords hd]
  push_cast
  ring

/-- The integer current of integral cycle coordinates. -/
noncomputable def coordinateCurrentInt (hd : 3 ≤ d) (q : Fin (degreeOneCycleBasis B).1 → ℤ) :
    DualDForm B (d - 2) → ℤ :=
  fun e => Classical.choose (coordinateCurrent_int hd q e)

theorem currentVector_coordinateCurrentInt (hd : 3 ≤ d)
    (q : Fin (degreeOneCycleBasis B).1 → ℤ) :
    currentVector (coordinateCurrentInt hd q) =
      ((dualDCoordinateCurrent hd B fun i => (q i : ℝ) : DualDCoClosed hd B) :
        EuclideanSpace ℝ (DualDForm B (d - 2))) := by
  ext e
  rw [currentVector_apply]
  exact (Classical.choose_spec (coordinateCurrent_int hd q e)).symm

theorem coordinateCurrentInt_closed (hd : 3 ≤ d) (q : Fin (degreeOneCycleBasis B).1 → ℤ) :
    ClosedD stencilInt (coordinateCurrentInt hd q) := by
  rw [closedD_stencilInt_iff hd, currentVector_coordinateCurrentInt]
  exact (dualDCoordinateCurrent hd B fun i => (q i : ℝ)).2

/-- **Integral cycle coordinates and integer co-closed currents.** -/
noncomputable def coordinateCurrentEquiv (hd : 3 ≤ d) :
    (Fin (degreeOneCycleBasis B).1 → ℤ) ≃
      {j : DualDForm B (d - 2) → ℤ // ClosedD stencilInt j} :=
  Equiv.ofBijective (fun q => ⟨coordinateCurrentInt hd q, coordinateCurrentInt_closed hd q⟩) (by
    constructor
    · intro q q' h
      have hval : coordinateCurrentInt hd q = coordinateCurrentInt hd q' := congrArg Subtype.val h
      have hvec := congrArg currentVector hval
      rw [currentVector_coordinateCurrentInt, currentVector_coordinateCurrentInt] at hvec
      funext i
      have h1 := coordinateCurrent_coords hd (fun i => (q i : ℝ)) i
      have h2 := coordinateCurrent_coords hd (fun i => (q' i : ℝ)) i
      rw [hvec] at h1
      have : (q i : ℝ) = (q' i : ℝ) := h1.symm.trans h2
      exact_mod_cast this
    · rintro ⟨j, hj⟩
      have hco := (closedD_stencilInt_iff hd j).mp hj
      choose m hm using inner_currentVector_cycleLift_int (B := B) j
      refine ⟨m, Subtype.ext ?_⟩
      have hdiff : ((dualDCoordinateCurrent hd B fun i => (m i : ℝ) : DualDCoClosed hd B) :
          EuclideanSpace ℝ (DualDForm B (d - 2))) - currentVector j = 0 := by
        have hmem : ((dualDCoordinateCurrent hd B fun i => (m i : ℝ) : DualDCoClosed hd B) :
            EuclideanSpace ℝ (DualDForm B (d - 2))) - currentVector j ∈
              coClosed (dualDExactOneComplex hd B) :=
          Submodule.sub_mem _ (dualDCoordinateCurrent hd B fun i => (m i : ℝ)).2 hco
        refine coClosed_eq_zero_of_liftCoordinates (dualDExactOneComplex hd B)
          (dualDImageCycleBasisForHodge hd B) (cycleLift B) (cycleLift_hlift hd) ⟨_, hmem⟩ ?_
        intro i
        change inner ℝ (((dualDCoordinateCurrent hd B fun i => (m i : ℝ) : DualDCoClosed hd B) :
          EuclideanSpace ℝ (DualDForm B (d - 2))) - currentVector j) (cycleLift B i) = 0
        rw [inner_sub_left, coordinateCurrent_coords hd, hm i, sub_self]
      have hvec : currentVector (coordinateCurrentInt hd m) = currentVector j := by
        rw [currentVector_coordinateCurrentInt]
        exact sub_eq_zero.mp hdiff
      funext e
      have he := congrFun (congrArg (fun a : EuclideanSpace ℝ (DualDForm B (d - 2)) => a.ofLp)
        hvec) e
      change ((coordinateCurrentInt hd m e : ℤ) : ℝ) = ((j e : ℤ) : ℝ) at he
      exact_mod_cast he)

theorem coordinateCurrentEquiv_apply (hd : 3 ≤ d) (q : Fin (degreeOneCycleBasis B).1 → ℤ) :
    ((coordinateCurrentEquiv hd q : {j : DualDForm B (d - 2) → ℤ // ClosedD stencilInt j}) :
      DualDForm B (d - 2) → ℤ) = coordinateCurrentInt hd q := rfl

/-! ## The Poisson sum over the integer co-closed currents -/

/-- The translation of the field by the path potential, in radians. -/
noncomputable def pathShift (τ : EuclideanSpace ℝ (DualDForm B (d - 2))) :
    DualDForm B (d - 2) → ℝ := fun e => 2 * Real.pi * τ e

theorem linkPairing_pathShift (τ : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (j : DualDForm B (d - 2) → ℤ) :
    linkPairing (pathShift τ) j = 2 * Real.pi * inner ℝ (currentVector j) τ := by
  unfold linkPairing pathShift
  rw [PiLp.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rw [currentVector_apply]
  ring


theorem tsum_dualDXYCurrentPhase_eq (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    ∑' q : Fin (degreeOneCycleBasis B).1 → ℤ, dualDXYCurrentPhase hd (le_of_lt hβ) x y q =
      closedCharacterSum hd β (pathShift (dualDXYPathTau hd x y).1) := by
  unfold closedCharacterSum
  rw [← (coordinateCurrentEquiv (B := B) hd).tsum_eq]
  refine tsum_congr fun q => ?_
  rw [coordinateCurrentEquiv_apply]
  have hco := (closedD_stencilInt_iff hd _).mp (coordinateCurrentInt_closed (B := B) hd q)
  have hsub : (⟨currentVector (coordinateCurrentInt hd q), hco⟩ :
      coClosed (dualDExactOneComplex hd B)) =
      dualDCoordinateCurrent hd B fun i => (q i : ℝ) :=
    Subtype.ext (currentVector_coordinateCurrentInt hd q)
  rw [linkPairing_pathShift, quadraticD_dualCovariance hd β _ hco, hsub,
    currentVector_coordinateCurrentInt]
  unfold dualDXYCurrentPhase
  rw [dualDPathPhase_eq, mul_comm]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

end FroehlichSpencer.FS82.XY.DualD

end
