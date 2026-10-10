/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.SpinLaw
public import FroehlichSpencer.FS82.Cubical.IntegerExactness
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex
public import FroehlichSpencer.FS82.Poisson.PiSummable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Rank-zero Villain XY Fourier duality

For a finite free box, character expansion assigns an integer mode to every
bond.  Integrating the site angles imposes the endpoint divergence constraint.
The cubical prism homotopy supplies path sources and fills every divergence-free
bond field by an integer plaquette field.
-/

public section

namespace FroehlichSpencer.FS82.XY

noncomputable section

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open MeasureTheory
open scoped BigOperators

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance instIsProbabilityMeasureUnitAddCircleVolume_froehlichSpencer_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Integer Fourier modes on the free-box bonds. -/
abbrev XYBondModes {D : ℕ} {B : Box D} := XYBonds B → ℤ

private theorem homogeneousSupport_finite_sum {D : ℕ} {B : Box D}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Chain D B) (k : ℕ)
    (hf : ∀ i ∈ s, homogeneousSupport (f i) k) :
    homogeneousSupport (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [homogeneousSupport]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply homogeneousSupport_add
      · exact hf i (Finset.mem_insert_self i s)
      · apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)

/-- The integer bond chain carried by a field of Fourier modes. -/
@[expose] noncomputable def xyBondModeChain {D : ℕ} {B : Box D}
    (m : XYBondModes (B := B)) : Chain D B :=
  ∑ b : XYBonds B, (m b) • basisChain b.1

theorem xyBondModeChain_homogeneousSupport {D : ℕ} {B : Box D}
    (m : XYBondModes (B := B)) : homogeneousSupport (xyBondModeChain m) 1 := by
  classical
  unfold xyBondModeChain
  apply homogeneousSupport_finite_sum
  intro b hb
  have hbase := homogeneousSupport_basis b.1
  rw [b.2] at hbase
  exact homogeneousSupport_smul (m b) hbase


theorem xyBondModeChain_add {D : ℕ} {B : Box D}
    (m n : XYBondModes (B := B)) :
    xyBondModeChain (m + n) = xyBondModeChain m + xyBondModeChain n := by
  classical
  ext c
  simp [xyBondModeChain, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem xyBondModeChain_restrict {D : ℕ} {B : Box D}
    (q : Chain D B) (hq : homogeneousSupport q 1) :
    xyBondModeChain (fun b : XYBonds B => q b.1) = q := by
  classical
  apply Finsupp.ext
  intro c
  by_cases hc : cellDegree c = 1
  · let b₀ : XYBonds B := ⟨c, hc⟩
    have hsum :
        (∑ b : XYBonds B, (q b.1) • basisChain b.1) c = q c := by
      rw [Finsupp.finsetSum_apply]
      calc
        _ = ((q b₀.1) • basisChain b₀.1) c := by
          apply Fintype.sum_eq_single b₀
          intro b hne
          have hcell : b.1 ≠ c := fun heq => hne (Subtype.ext heq)
          simp [basisChain, hcell]
        _ = q c := by simp [b₀, basisChain]
    simpa [xyBondModeChain] using hsum
  · have hqc : q c = 0 := by
      by_contra hne
      have hcSupport : c ∈ q.support := Finsupp.mem_support_iff.mpr hne
      have := hq c hcSupport
      omega
    have hsum : (∑ b : XYBonds B, (q b.1) • basisChain b.1) c = 0 := by
      rw [Finsupp.finsetSum_apply]
      apply Fintype.sum_eq_zero
      intro b
      have hcell : b.1 ≠ c := by
        intro heq
        subst c
        exact hc b.2
      simp [basisChain, hcell]
    simpa [xyBondModeChain, hqc] using hsum

/-- The site divergence of the integer bond field. -/
@[expose] noncomputable def xyBondModeDivergence {D : ℕ} {B : Box D}
    (m : XYBondModes (B := B)) : XYSites B → ℤ :=
  fun x => boundary (xyBondModeChain m) x.1

theorem xyBondModeDivergence_add {D : ℕ} {B : Box D}
    (m n : XYBondModes (B := B)) :
    xyBondModeDivergence (m + n) = xyBondModeDivergence m + xyBondModeDivergence n := by
  funext x
  simp [xyBondModeDivergence, xyBondModeChain_add, map_add]


/-- The oriented endpoint source `δₓ−δᵧ`, as a cubical zero-chain. -/
@[expose] noncomputable def xyEndpointSource {D : ℕ} {B : Box D}
    (x y : XYSites B) : Chain D B := basisChain x.1 - basisChain y.1

@[expose] noncomputable def xyEndpointFrequency {D : ℕ} {B : Box D}
    (x y : XYSites B) : XYSites B → ℤ :=
  fun z => xyEndpointSource x y z.1

/-- The endpoint path, built by the cubical prism filling from the lower box
corner. -/
@[expose] noncomputable def xyEndpointPath {D : ℕ} {B : Box D}
    (x y : XYSites B) : Chain D B :=
  fillingOperator (fun i : Fin D => (⟨0, Nat.zero_lt_succ (B i)⟩ : Fin (B i + 1)))
    (xyEndpointSource x y)

@[expose] noncomputable def xyEndpointPathModes {D : ℕ} {B : Box D}
    (x y : XYSites B) : XYBondModes (B := B) :=
  fun b => xyEndpointPath x y b.1

private def xyProjectCellList {D : ℕ} {B : Box D}
    (anchor : Anchor D B) : List (Fin D) → Cell D B → Cell D B
  | [], c => c
  | i :: is, c => vertexUpdate (xyProjectCellList anchor is c) i (anchor i)

private def xyAllVertices {D : ℕ} {B : Box D} (c : Cell D B) : Prop :=
  ∀ i, ¬ coordIsEdge (c i)

private theorem xySite_allVertices {D : ℕ} {B : Box D} (x : XYSites B) :
    xyAllVertices x.1 := by
  intro i hi
  have hiAxes : i ∈ cellAxes x.1 := by
    simp [cellAxes, hi]
  have hpos : 0 < cellDegree x.1 := Finset.card_pos.mpr ⟨i, hiAxes⟩
  omega

private theorem xyProjectCellList_allVertices {D : ℕ} {B : Box D}
    (anchor : Anchor D B) (is : List (Fin D)) (c : Cell D B)
    (hc : xyAllVertices c) : xyAllVertices (xyProjectCellList anchor is c) := by
  induction is with
  | nil => exact hc
  | cons i is ih =>
      intro j
      by_cases hji : j = i
      · subst j
        simp [xyProjectCellList, vertexUpdate, coordIsEdge]
      · simpa [xyProjectCellList, vertexUpdate, Function.update_of_ne hji] using ih j

private theorem xyProjectCellList_apply_of_mem {D : ℕ} {B : Box D}
    (anchor : Anchor D B) (is : List (Fin D)) (c : Cell D B) (i : Fin D)
    (hi : i ∈ is) :
    xyProjectCellList anchor is c i = Sum.inl (anchor i) := by
  induction is with
  | nil => simp at hi
  | cons j is ih =>
      rcases List.mem_cons.mp hi with hji | hiTail
      · subst j
        simp [xyProjectCellList, vertexUpdate]
      · by_cases hEq : i = j
        · subst j
          simp [xyProjectCellList, vertexUpdate]
        · simp [xyProjectCellList, vertexUpdate, Function.update_of_ne hEq, ih hiTail]

private theorem orderedPrismProjection_basis_projectCell {D : ℕ} {B : Box D}
    (anchor : Anchor D B) (is : List (Fin D)) (c : Cell D B)
    (hc : xyAllVertices c) :
    orderedPrismProjection anchor is (basisChain c) =
      basisChain (xyProjectCellList anchor is c) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      change projection anchor i (orderedPrismProjection anchor is (basisChain c)) =
        basisChain (xyProjectCellList anchor (i :: is) c)
      rw [ih, projection_basis]
      have htail := xyProjectCellList_allVertices anchor is c hc
      cases hcoord : xyProjectCellList anchor is c i with
      | inl v => simp [projectionBasis, xyProjectCellList, vertexUpdate, hcoord]
      | inr e => exact False.elim (htail i (by simp [hcoord, coordIsEdge]))

private theorem orderedPrismProjection_basis_anchor {D : ℕ} {B : Box D}
    (anchor : Anchor D B) (x : XYSites B) :
    finalProjection anchor (basisChain x.1) =
      basisChain (fun i => Sum.inl (anchor i)) := by
  rw [show finalProjection anchor = orderedPrismProjection anchor (List.finRange D) by rfl,
    orderedPrismProjection_basis_projectCell anchor (List.finRange D) x.1 (xySite_allVertices x)]
  congr 1
  funext i
  exact xyProjectCellList_apply_of_mem anchor (List.finRange D) x.1 i (by simp)

private theorem xySite_coord_vertex {D : ℕ} {B : Box D} (x : XYSites B) (i : Fin D) :
    ∃ v, x.1 i = Sum.inl v := by
  cases hcoord : x.1 i with
  | inl v => exact ⟨v, rfl⟩
  | inr e =>
      have hi : i ∈ cellAxes x.1 := by
        simp only [cellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hcoord]
        simp [coordIsEdge]
      have hpos : 0 < cellDegree x.1 := Finset.card_pos.mpr ⟨i, hi⟩
      omega

private theorem xySite_basis_boundary_zero {D : ℕ} {B : Box D}
    (x : XYSites B) : boundary (basisChain x.1) = 0 := by
  rw [boundary_basis]
  unfold boundaryBasis
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨v, hv⟩ := xySite_coord_vertex x i
  simp [hv]

theorem xyEndpointSource_homogeneousSupport {D : ℕ} {B : Box D}
    (x y : XYSites B) : homogeneousSupport (xyEndpointSource x y) 0 := by
  have hx := homogeneousSupport_basis x.1
  rw [x.2] at hx
  have hy := homogeneousSupport_basis y.1
  rw [y.2] at hy
  simpa [xyEndpointSource, sub_eq_add_neg] using
    homogeneousSupport_add hx (homogeneousSupport_smul (-1 : ℤ) hy)

/-- The cubical prism source is an integer path from `y` to `x`. -/
theorem xyEndpointPath_boundary {D : ℕ} {B : Box D} (x y : XYSites B) :
    boundary (xyEndpointPath x y) = xyEndpointSource x y := by
  let anchor : Anchor D B := fun i => ⟨0, Nat.zero_lt_succ (B i)⟩
  let q : Chain D B := xyEndpointSource x y
  have hq : boundary q = 0 := by
    dsimp [q, xyEndpointSource]
    rw [map_sub, xySite_basis_boundary_zero, xySite_basis_boundary_zero, sub_self]
  have hproj : finalProjection anchor q = 0 := by
    dsimp [q, xyEndpointSource]
    rw [map_sub, orderedPrismProjection_basis_anchor anchor x,
      orderedPrismProjection_basis_anchor anchor y]
    simp
  have hprism := congrArg (fun T : Chain D B →ₗ[ℤ] Chain D B => T q)
    (fillingOperator_prism_identity anchor)
  change boundary (fillingOperator anchor q) + fillingOperator anchor (boundary q) =
      q - finalProjection anchor q at hprism
  rw [hq, map_zero, hproj, sub_zero, add_zero] at hprism
  simpa [xyEndpointPath, xyEndpointSource, anchor, q] using hprism

theorem xyEndpointPath_homogeneousSupport {D : ℕ} {B : Box D}
    (x y : XYSites B) : homogeneousSupport (xyEndpointPath x y) 1 := by
  change homogeneousSupport
    (fillingOperator (fun i : Fin D => ⟨0, Nat.zero_lt_succ (B i)⟩)
      (xyEndpointSource x y)) 1
  exact fillingOperator_homogeneousSupport
    (fun i : Fin D => ⟨0, Nat.zero_lt_succ (B i)⟩)
    (xyEndpointSource x y) 0 (xyEndpointSource_homogeneousSupport x y)

theorem xyEndpointPathModes_divergence {D : ℕ} {B : Box D}
    (x y : XYSites B) : xyBondModeDivergence (xyEndpointPathModes x y) =
      xyEndpointFrequency x y := by
  funext z
  change boundary (xyBondModeChain (fun b : XYBonds B => xyEndpointPath x y b.1)) z.1 =
    xyEndpointFrequency x y z
  rw [xyBondModeChain_restrict (xyEndpointPath x y)
    (xyEndpointPath_homogeneousSupport x y)]
  rw [xyEndpointPath_boundary]
  rfl

/-- Boundary lowers the homogeneous cubical degree by one.  The proof passes
through the real incidence map, whose degree statement is dimension-generic,
and reflects support back to integer coefficients. -/
theorem xyIntegerBoundary_homogeneousSupport {D : ℕ} {B : Box D}
    (q : Chain D B) (k : ℕ) (hk : 0 < k)
    (hq : homogeneousSupport q k) :
    homogeneousSupport (boundary q) (k - 1) := by
  have hqR : realHomogeneousSupport (castIntegerChain q) k := by
    intro c hc
    exact hq c (Finsupp.support_mapRange hc)
  have hbdR := realBoundary_homogeneousSupport (castIntegerChain q) k hk hqR
  have hcast : castIntegerChain (boundary q) = realBoundary (castIntegerChain q) := by
    simpa [realBoundary] using (realifyLinearMap_cast boundary q).symm
  intro c hc
  have hcR : c ∈ (realBoundary (castIntegerChain q)).support := by
    rw [← hcast]
    rw [Finsupp.mem_support_iff] at hc ⊢
    intro hz
    apply hc
    have hzero : ((boundary q c : ℤ) : ℝ) = 0 := by
      simpa [castIntegerChain, Finsupp.mapRange_apply] using hz
    exact_mod_cast hzero
  exact hbdR c hcR

/-- Every divergence-free integer bond field fills by an integer plaquette
field, with the filling supported in degree two. -/
theorem xyBondCycle_has_plaquetteFilling {D : ℕ} {B : Box D}
    (m : XYBondModes (B := B)) (hdiv : xyBondModeDivergence m = 0) :
    ∃ p : Chain D B, homogeneousSupport p 2 ∧ boundary p = xyBondModeChain m := by
  let anchor : Anchor D B := fun i => ⟨0, Nat.zero_lt_succ (B i)⟩
  let q : Chain D B := xyBondModeChain m
  have hqdegree : homogeneousSupport q 1 := xyBondModeChain_homogeneousSupport m
  have hcycle : boundary q = 0 := by
    apply Finsupp.ext
    intro c
    by_cases hc : cellDegree c = 0
    · let x : XYSites B := ⟨c, hc⟩
      simpa [q, x, xyBondModeDivergence] using congrFun hdiv x
    · have hnot : c ∉ (boundary q).support := by
        intro hmem
        have hdeg := xyIntegerBoundary_homogeneousSupport q 1 (by omega) hqdegree c hmem
        omega
      by_contra hne
      exact hnot (Finsupp.mem_support_iff.mpr hne)
  have hproj : finalProjection anchor q = 0 :=
    orderedPrismProjection_kills_positiveSupport anchor q
      (by
        intro c hc
        have hk := hqdegree c hc
        omega)
  have hprism := congrArg (fun T : Chain D B →ₗ[ℤ] Chain D B => T q)
    (fillingOperator_prism_identity anchor)
  change boundary (fillingOperator anchor q) + fillingOperator anchor (boundary q) =
      q - finalProjection anchor q at hprism
  rw [hcycle, map_zero, hproj, sub_zero, add_zero] at hprism
  refine ⟨fillingOperator anchor q, fillingOperator_homogeneousSupport anchor q 1 hqdegree,
    hprism⟩


abbrev XYPlaquetteFillings {D : ℕ} {B : Box D} (q : Chain D B) :=
  {p : Chain D B // homogeneousSupport p 2 ∧ boundary p = q}

/-- Translation by the difference of two fillings is a bijection between the
two plaquette-filling fibers.  This is the constant-multiplicity identity in
(4.14), stated as an explicit equivalence of solution sets. -/
noncomputable def xyPlaquetteFillingsEquiv {D : ℕ} {B : Box D}
    {q r : Chain D B} (a : XYPlaquetteFillings q) (b : XYPlaquetteFillings r) :
    XYPlaquetteFillings q ≃ XYPlaquetteFillings r where
  toFun p := ⟨p.1 + (b.1 - a.1), by
    constructor
    · have hba : homogeneousSupport (b.1 - a.1) 2 := by
        simpa [sub_eq_add_neg] using
          homogeneousSupport_add b.2.1 (homogeneousSupport_smul (-1 : ℤ) a.2.1)
      exact homogeneousSupport_add p.2.1 hba
    · simp only [map_add, map_sub, p.2.2, b.2.2, a.2.2]
      abel⟩
  invFun p := ⟨p.1 + (a.1 - b.1), by
    constructor
    · have hab : homogeneousSupport (a.1 - b.1) 2 := by
        simpa [sub_eq_add_neg] using
          homogeneousSupport_add a.2.1 (homogeneousSupport_smul (-1 : ℤ) b.2.1)
      exact homogeneousSupport_add p.2.1 hab
    · simp only [map_add, map_sub, p.2.2, a.2.2, b.2.2]
      abel⟩
  left_inv p := by
    apply Subtype.ext
    simp only
    abel
  right_inv p := by
    apply Subtype.ext
    simp only
    abel

/-- Divergence-free bond fields have filling fibers of the same cardinality:
translation by the difference of chosen plaquette fillings is a bijection. -/
theorem xyBondCycle_fillingMultiplicityIndependent {D : ℕ} {B : Box D}
    (m n : XYBondModes (B := B))
    (hm : xyBondModeDivergence m = 0) (hn : xyBondModeDivergence n = 0) :
    Nonempty (XYPlaquetteFillings (xyBondModeChain m) ≃
      XYPlaquetteFillings (xyBondModeChain n)) := by
  obtain ⟨p, hpdeg, hpbd⟩ := xyBondCycle_has_plaquetteFilling m hm
  obtain ⟨q, hqdeg, hqbd⟩ := xyBondCycle_has_plaquetteFilling n hn
  exact ⟨xyPlaquetteFillingsEquiv ⟨p, hpdeg, hpbd⟩ ⟨q, hqdeg, hqbd⟩⟩


private def finSuccIntEquiv (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃ ℤ × (Fin n → ℤ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    rcases p with ⟨z, f⟩
    rfl

private theorem product_tsum_fin (n : ℕ) (g : ℤ → ℝ) (hg : Summable g)
    (hg0 : ∀ k, 0 ≤ g k) (phase : Fin n → ℤ → ℂ)
    (hphase : ∀ i k, ‖phase i k‖ = 1) :
    (∏ i : Fin n, ∑' k : ℤ, (g k : ℂ) * phase i k) =
      ∑' f : Fin n → ℤ, ∏ i : Fin n, (g (f i) : ℂ) * phase i (f i) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      let F : (Fin (n + 1) → ℤ) → ℂ := fun f =>
        ∏ i : Fin (n + 1), (g (f i) : ℂ) * phase i (f i)
      let R : (Fin n → ℤ) → ℂ := fun f =>
        ∏ i : Fin n, (g (f i) : ℂ) * phase i.succ (f i)
      let A : ℤ → ℂ := fun k => (g k : ℂ) * phase 0 k
      have hcoeff : Summable fun f : Fin (n + 1) → ℤ => ∏ i, g (f i) :=
        summable_pi_prod_of_summable g hg
      have hF : Summable F := by
        apply Summable.of_norm_bounded hcoeff
        intro f
        dsimp [F]
        rw [norm_prod]
        apply le_of_eq
        apply Finset.prod_congr rfl
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hg0 (f i)), hphase i (f i)]
        simp
      let e := finSuccIntEquiv n
      have hcomp : Summable (F ∘ e.symm) :=
        (Equiv.summable_iff (f := F) e.symm).2 hF
      have hrewrite (p : ℤ × (Fin n → ℤ)) : F (e.symm p) = A p.1 * R p.2 := by
        rcases p with ⟨k, f⟩
        change (∏ i : Fin (n + 1),
          (g ((e.symm (k, f)) i) : ℂ) * phase i ((e.symm (k, f)) i)) =
            ((g k : ℂ) * phase 0 k) *
              ∏ i : Fin n, (g (f i) : ℂ) * phase i.succ (f i)
        rw [show e.symm (k, f) = Fin.cases k f by rfl]
        simp only [Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
      have hcomp' : Summable (fun p : ℤ × (Fin n → ℤ) => A p.1 * R p.2) :=
        hcomp.congr fun p => hrewrite p
      have hprod : (∑' f : Fin (n + 1) → ℤ, F f) =
          ∑' p : ℤ × (Fin n → ℤ), A p.1 * R p.2 := by
        calc
          _ = ∑' p : ℤ × (Fin n → ℤ), F (e.symm p) :=
            (Equiv.tsum_eq e.symm F).symm
          _ = _ := tsum_congr hrewrite
      have hiter : (∑' p : ℤ × (Fin n → ℤ), A p.1 * R p.2) =
          ∑' k : ℤ, ∑' f : Fin n → ℤ, A k * R f := hcomp'.tsum_prod
      have hinner (k : ℤ) :
          (∑' f : Fin n → ℤ, A k * R f) =
            A k * ∏ i : Fin n, ∑' z : ℤ, (g z : ℂ) * phase i.succ z := by
        rw [tsum_mul_left]
        dsimp [A, R]
        rw [ih (fun i z => phase i.succ z) (fun i z => hphase i.succ z)]
      rw [Fin.prod_univ_succ]
      calc
        (∑' k : ℤ, (g k : ℂ) * phase 0 k) *
            ∏ i : Fin n, ∑' k : ℤ, (g k : ℂ) * phase i.succ k =
          ∑' k : ℤ, A k * ∏ i : Fin n, ∑' z : ℤ, (g z : ℂ) * phase i.succ z := by
            rw [← tsum_mul_right]
        _ = ∑' k : ℤ, ∑' f : Fin n → ℤ, A k * R f := by
            apply tsum_congr
            intro k
            exact (hinner k).symm
        _ = ∑' p : ℤ × (Fin n → ℤ), A p.1 * R p.2 := hiter.symm
        _ = ∑' f : Fin (n + 1) → ℤ, F f := hprod.symm

private theorem product_tsum_fintype {ι : Type*} [Fintype ι]
    (g : ℤ → ℝ) (hg : Summable g) (hg0 : ∀ k, 0 ≤ g k)
    (phase : ι → ℤ → ℂ) (hphase : ∀ i k, ‖phase i k‖ = 1) :
    (∏ i : ι, ∑' k : ℤ, (g k : ℂ) * phase i k) =
      ∑' f : ι → ℤ, ∏ i : ι, (g (f i) : ℂ) * phase i (f i) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eπ : (ι → ℤ) ≃ (Fin (Fintype.card ι) → ℤ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℤ) e
  have hfin := product_tsum_fin (Fintype.card ι) g hg hg0
    (fun i k => phase (e.symm i) k) (fun i k => hphase (e.symm i) k)
  calc
    (∏ i : ι, ∑' k : ℤ, (g k : ℂ) * phase i k) =
        ∏ i : Fin (Fintype.card ι), ∑' k : ℤ, (g k : ℂ) * phase (e.symm i) k := by
          symm
          exact Equiv.prod_comp e.symm (fun i => ∑' k : ℤ, (g k : ℂ) * phase i k)
    _ = ∑' f : Fin (Fintype.card ι) → ℤ,
          ∏ i : Fin (Fintype.card ι), (g (f i) : ℂ) * phase (e.symm i) (f i) := hfin
    _ = ∑' f : ι → ℤ, ∏ i : ι, (g (f i) : ℂ) * phase i (f i) := by
          let H : (ι → ℤ) → ℂ := fun f =>
            ∏ i : ι, (g (f i) : ℂ) * phase i (f i)
          have hsum := Equiv.tsum_eq eπ.symm H
          rw [← hsum]
          apply tsum_congr
          intro f
          dsimp [H, eπ]
          rw [← Equiv.prod_comp e (fun j : Fin (Fintype.card ι) =>
            (g (f j) : ℂ) * phase (e.symm j) (f j))]
          apply Finset.prod_congr rfl
          intro i hi
          simp [Equiv.piCongrLeft]

private theorem xyFourier_zsmul_argument {k n : ℤ} (x : UnitAddCircle) :
    fourier (T := (1 : ℝ)) n (k • x) = fourier (T := (1 : ℝ)) (n * k) x := by
  rw [fourier_apply, fourier_apply, smul_smul]

private theorem xyFourier_argument_add {n : ℤ} (x y : UnitAddCircle) :
    fourier (T := (1 : ℝ)) n (x + y) =
      fourier (T := (1 : ℝ)) n x * fourier (T := (1 : ℝ)) n y := by
  rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
    ← fourier_apply, ← fourier_apply]

private theorem xyFourier_finset_zsmul_sum {ι : Type*} (s : Finset ι) (n : ℤ)
    (a : ι → ℤ) (x : ι → UnitAddCircle) :
    fourier (T := (1 : ℝ)) n (∑ i ∈ s, a i • x i) =
      ∏ i ∈ s, fourier (T := (1 : ℝ)) (n * a i) (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        xyFourier_argument_add, xyFourier_zsmul_argument, ih]

private theorem xyFourier_sum_zsmul {ι : Type*} [Fintype ι] (n : ℤ)
    (a : ι → ℤ) (x : ι → UnitAddCircle) :
    fourier (T := (1 : ℝ)) n (∑ i, a i • x i) =
      ∏ i, fourier (T := (1 : ℝ)) (n * a i) (x i) := by
  simpa using xyFourier_finset_zsmul_sum (Finset.univ : Finset ι) n a x

@[expose] noncomputable def xyCircleCochainCoboundary {D : ℕ} {B : Box D}
    (f : Cell D B → UnitAddCircle) : Cell D B → UnitAddCircle := fun c =>
  xyCircleChainPairing (boundary (basisChain c)) f

theorem xyCircleChainPairing_boundary_eq_coboundary {D : ℕ} {B : Box D}
    (q : Chain D B) (f : Cell D B → UnitAddCircle) :
    xyCircleChainPairing (boundary q) f =
      xyCircleChainPairing q (xyCircleCochainCoboundary f) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [xyCircleChainPairing]
  | add q r hq hr =>
      rw [map_add, xyCircleChainPairing_add, hq, hr, ← xyCircleChainPairing_add]
  | single c n =>
      have hsingle : Finsupp.single c n = n • basisChain c := by
        ext x
        by_cases hx : x = c <;> simp [basisChain, hx]
      calc
        xyCircleChainPairing (boundary (Finsupp.single c n)) f =
            n • xyCircleChainPairing (boundary (basisChain c)) f := by
              rw [hsingle, map_smul]
              simp [xyCircleChainPairing]
        _ = xyCircleChainPairing (Finsupp.single c n)
              (xyCircleCochainCoboundary f) := by
              rw [hsingle]
              rw [xyCircleChainPairing_smul]
              simp [xyCircleChainPairing, xyCircleCochainCoboundary, basisChain]

theorem xyCircleChainPairing_eq_site_sum {D : ℕ} {B : Box D}
    (q : Chain D B) (θ : XYAngleConfig B) :
    xyCircleChainPairing q (xyAngleCochain θ) =
      ∑ x : XYSites B, q x.1 • θ x := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [xyCircleChainPairing]
  | add q r hq hr =>
      rw [xyCircleChainPairing_add, hq, hr]
      simp [Finsupp.add_apply, add_zsmul, Finset.sum_add_distrib]
  | single c z =>
      have hsingle : xyCircleChainPairing (Finsupp.single c z) (xyAngleCochain θ) =
          z • xyAngleCochain θ c := by
        simp [xyCircleChainPairing]
      by_cases hc : cellDegree c = 0
      · let x₀ : XYSites B := ⟨c, hc⟩
        have hangle : xyAngleCochain θ c = θ x₀ := by simp [xyAngleCochain, hc, x₀]
        have hsum :
            (∑ x : XYSites B, (Finsupp.single c z : Chain D B) x.1 • θ x) =
              (Finsupp.single c z : Chain D B) x₀.1 • θ x₀ :=
          Fintype.sum_eq_single x₀ (by
            intro x hx
            have hne : x.1 ≠ c := by
              intro hEq
              exact hx (Subtype.ext hEq)
            rw [Finsupp.single_eq_of_ne hne]
            simp)
        calc
          xyCircleChainPairing (Finsupp.single c z) (xyAngleCochain θ) =
              z • xyAngleCochain θ c := hsingle
          _ = z • θ x₀ := by rw [hangle]
          _ = ∑ x : XYSites B, (Finsupp.single c z : Chain D B) x.1 • θ x := by
                rw [hsum]
                simp [x₀, Finsupp.single_eq_same]
      · have hangle : xyAngleCochain θ c = 0 := by simp [xyAngleCochain, hc]
        have hsum :
            (∑ x : XYSites B, (Finsupp.single c z : Chain D B) x.1 • θ x) = 0 := by
          apply Fintype.sum_eq_zero
          intro x
          have hne : x.1 ≠ c := by
            intro hEq
            exact hc (hEq ▸ x.2)
          rw [Finsupp.single_eq_of_ne hne]
          simp
        calc
          xyCircleChainPairing (Finsupp.single c z) (xyAngleCochain θ) =
              z • xyAngleCochain θ c := hsingle
          _ = 0 := by rw [hangle]; simp
          _ = ∑ x : XYSites B, (Finsupp.single c z : Chain D B) x.1 • θ x := by
                rw [hsum]

theorem xyTorus_character_integral {D : ℕ} {B : Box D}
    (q : XYSites B → ℤ) :
    ∫ θ : XYAngleConfig B, UnitAddTorus.mFourier q θ = if q = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := XYSites B)))
      (0 : XYSites B → ℤ) q
  rw [MeasureTheory.ContinuousMap.inner_toLp] at h
  simpa [UnitAddTorus.mFourier_zero, eq_comm] using h

/-- Stokes transports the bond characters to the divergence character on
the site torus. -/
theorem xyBondMode_fourierProduct {D : ℕ} {B : Box D}
    (m : XYBondModes (B := B)) (θ : XYAngleConfig B) :
    (∏ b : XYBonds B,
      fourier (T := (1 : ℝ)) (-m b) (xyBondDifference θ b)) =
      UnitAddTorus.mFourier (fun x => -xyBondModeDivergence m x) θ := by
  classical
  let q : Chain D B := xyBondModeChain m
  let f : Cell D B → UnitAddCircle :=
    xyCircleCochainCoboundary (xyAngleCochain θ)
  have hq : homogeneousSupport q 1 := xyBondModeChain_homogeneousSupport m
  have hbond (b : XYBonds B) : xyBondDifference θ b = f b.1 := by
    simp [f, xyBondDifference, xyCircleCochainCoboundary, basisChain]
  have hpair : xyCircleChainPairing q f =
      ∑ b : XYBonds B, m b • f b.1 := by
    change Finsupp.linearCombination ℤ f
        (∑ b : XYBonds B, (m b) • basisChain b.1) = _
    rw [map_sum]
    simp [basisChain, Finsupp.linearCombination_single]
  have hprod := xyFourier_sum_zsmul (ι := XYBonds B) (-1) m (fun b => f b.1)
  have hstokes := xyCircleChainPairing_boundary_eq_coboundary q (xyAngleCochain θ)
  have hsites := xyCircleChainPairing_eq_site_sum (boundary q) θ
  have hsiteprod := xyFourier_sum_zsmul (ι := XYSites B) (-1)
    (fun x => (boundary q) x.1) θ
  calc
    (∏ b : XYBonds B,
        fourier (T := (1 : ℝ)) (-m b) (xyBondDifference θ b)) =
        ∏ b : XYBonds B,
          fourier (T := (1 : ℝ)) ((-1) * m b) (f b.1) := by
            apply Finset.prod_congr rfl
            intro b hb
            rw [hbond b]
            simp only [neg_one_mul]
    _ = fourier (T := (1 : ℝ)) (-1)
          (∑ b : XYBonds B, m b • f b.1) := by
          simpa only [neg_one_mul] using hprod.symm
    _ = fourier (T := (1 : ℝ)) (-1) (xyCircleChainPairing q f) :=
          congrArg (fourier (T := (1 : ℝ)) (-1)) hpair.symm
    _ = fourier (T := (1 : ℝ)) (-1)
          (xyCircleChainPairing (boundary q) (xyAngleCochain θ)) :=
          congrArg (fourier (T := (1 : ℝ)) (-1)) hstokes.symm
    _ = fourier (T := (1 : ℝ)) (-1)
          (∑ x : XYSites B, (boundary q) x.1 • θ x) :=
          congrArg (fourier (T := (1 : ℝ)) (-1)) hsites
    _ = ∏ x : XYSites B,
          fourier (T := (1 : ℝ)) ((-1) * (boundary q) x.1) (θ x) := hsiteprod
    _ = UnitAddTorus.mFourier (fun x => -xyBondModeDivergence m x) θ := by
          simp [UnitAddTorus.mFourier, xyBondModeDivergence, q]

theorem xyEndpointCharacter_eq_mFourier {D : ℕ} {B : Box D}
    (θ : XYAngleConfig B) (x y : XYSites B) :
    xyEndpointCharacter θ x y = UnitAddTorus.mFourier (xyEndpointFrequency x y) θ := by
  have hsource :
      xyCircleChainPairing (xyEndpointSource x y) (xyAngleCochain θ) = θ x - θ y := by
    simp [xyEndpointSource, xyCircleChainPairing, basisChain, xyAngleCochain,
      x.2, y.2, Finsupp.linearCombination_single]
  have hsites := xyCircleChainPairing_eq_site_sum (xyEndpointSource x y) θ
  have hfour := xyFourier_sum_zsmul (ι := XYSites B) 1
    (xyEndpointFrequency x y) θ
  calc
    xyEndpointCharacter θ x y =
        fourier (T := (1 : ℝ)) 1
          (xyCircleChainPairing (xyEndpointSource x y) (xyAngleCochain θ)) := by
            rw [xyEndpointCharacter, hsource]
    _ = fourier (T := (1 : ℝ)) 1
          (∑ z : XYSites B, xyEndpointFrequency x y z • θ z) := by
          rw [hsites]
          simp [xyEndpointFrequency]
    _ = ∏ z : XYSites B,
          fourier (T := (1 : ℝ)) (xyEndpointFrequency x y z) (θ z) := by
          simpa [mul_one] using hfour
    _ = UnitAddTorus.mFourier (xyEndpointFrequency x y) θ := by
          simp [UnitAddTorus.mFourier]

@[expose] noncomputable def xyVillainFourierScale (β : ℝ) : ℂ :=
  (1 / Real.sqrt (2 * Real.pi * β) : ℝ)

@[expose] noncomputable def xyVillainGaussianCoeff (β : ℝ) (k : ℤ) : ℝ :=
  Real.exp (-(k : ℝ) ^ 2 / (2 * β))

@[expose] noncomputable def xyVillainCharacterSeries (β : ℝ)
    (z : UnitAddCircle) : ℂ :=
  ∑' k : ℤ, (xyVillainGaussianCoeff β k : ℂ) *
    fourier (T := (1 : ℝ)) (-k) z

private theorem xyVillainFourierMap_eq_characterSeries (β : ℝ) (hβ : 0 < β)
    (z : UnitAddCircle) :
    villainCircleFourierMap β z =
      xyVillainFourierScale β * xyVillainCharacterSeries β z := by
  have hterms : Summable fun k : ℤ =>
      (Real.exp (-(k : ℝ) ^ 2 / (2 * β)) : ℂ) •
        fourier (T := (1 : ℝ)) (-k) := by
    apply Summable.of_norm_bounded (villainCharacterCoeff_summable β hβ)
    intro k
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.exp_nonneg _), fourier_norm]
    simp
  have hsum := ContinuousMap.tsum_apply hterms z
  rw [villainCircleFourierMap, ContinuousMap.smul_apply, hsum.symm]
  simp only [smul_eq_mul, xyVillainFourierScale]
  congr 1
  · norm_cast

private theorem xyVillainCircleWeight_complex (β : ℝ) (z : UnitAddCircle)
    (hβ : 0 < β) :
    (villainCircleWeight β z : ℂ) = villainCircleFourierMap β z := by
  rw [villainCircleWeight_eq_periodized β z hβ,
    villainCircleFourierMap_apply β z hβ]

@[expose] noncomputable def xyDualGaussianProduct {D : ℕ} {B : Box D}
    (β : ℝ) (m : XYBondModes (B := B)) : ℝ :=
  ∏ b : XYBonds B, xyVillainGaussianCoeff β (m b)

theorem xyDualGaussianProduct_nonneg {D : ℕ} {B : Box D} (β : ℝ)
    (m : XYBondModes (B := B)) : 0 ≤ xyDualGaussianProduct β m := by
  unfold xyDualGaussianProduct xyVillainGaussianCoeff
  exact Finset.prod_nonneg fun b hb => (Real.exp_pos _).le

theorem xyDualGaussianProduct_pos {D : ℕ} {B : Box D} (β : ℝ)
    (m : XYBondModes (B := B)) : 0 < xyDualGaussianProduct β m := by
  unfold xyDualGaussianProduct xyVillainGaussianCoeff
  exact Finset.prod_pos fun b hb => Real.exp_pos _

theorem xyDualGaussianProduct_summable {D : ℕ} {B : Box D} (β : ℝ)
    (hβ : 0 < β) : Summable (xyDualGaussianProduct (B := B) β) := by
  classical
  unfold xyDualGaussianProduct xyVillainGaussianCoeff
  exact summable_pi_prod_of_summable
    (fun k : ℤ => Real.exp (-(k : ℝ) ^ 2 / (2 * β)))
    (villainCharacterCoeff_summable β hβ)

@[expose] noncomputable def xyDualConstraintTerm {D : ℕ} {B : Box D}
    (β : ℝ) (source : XYSites B → ℤ) (m : XYBondModes (B := B)) : ℝ :=
  if xyBondModeDivergence m = source then xyDualGaussianProduct β m else 0

@[expose] noncomputable def xyDualPartition {D : ℕ} {B : Box D}
    (β : ℝ) (source : XYSites B → ℤ) : ℝ :=
  ∑' m : XYBondModes (B := B), xyDualConstraintTerm β source m

theorem xyDualConstraintTerm_nonneg {D : ℕ} {B : Box D} (β : ℝ)
    (source : XYSites B → ℤ) (m : XYBondModes (B := B)) :
    0 ≤ xyDualConstraintTerm β source m := by
  unfold xyDualConstraintTerm
  split_ifs <;> [exact xyDualGaussianProduct_nonneg β m; exact le_rfl]

theorem xyDualConstraintTerm_summable {D : ℕ} {B : Box D} (β : ℝ)
    (hβ : 0 < β) (source : XYSites B → ℤ) :
    Summable (xyDualConstraintTerm (B := B) β source) := by
  apply Summable.of_nonneg_of_le (fun m => xyDualConstraintTerm_nonneg β source m)
    (fun m => ?_) (xyDualGaussianProduct_summable (B := B) β hβ)
  unfold xyDualConstraintTerm
  split_ifs <;> simp [xyDualGaussianProduct_nonneg]


theorem xyDualPartition_pos_of_solution {D : ℕ} {B : Box D} (β : ℝ)
    (hβ : 0 < β) (source : XYSites B → ℤ) (m₀ : XYBondModes (B := B))
    (hm₀ : xyBondModeDivergence m₀ = source) :
    0 < xyDualPartition β source := by
  unfold xyDualPartition
  apply (xyDualConstraintTerm_summable β hβ source).tsum_pos
    (fun m => xyDualConstraintTerm_nonneg β source m) m₀
  simpa [xyDualConstraintTerm, hm₀] using xyDualGaussianProduct_pos β m₀

theorem xyDualPartition_zero_pos {D : ℕ} {B : Box D} (β : ℝ) (hβ : 0 < β) :
    0 < xyDualPartition (B := B) β (0 : XYSites B → ℤ) := by
  apply xyDualPartition_pos_of_solution β hβ 0 0
  funext x
  simp [xyBondModeDivergence, xyBondModeChain]

@[expose] noncomputable def xyDualCharacterTerm {D : ℕ} {B : Box D}
    (β : ℝ) (source : XYSites B → ℤ) (m : XYBondModes (B := B))
    (θ : XYAngleConfig B) : ℂ :=
  (xyDualGaussianProduct β m : ℂ) *
    UnitAddTorus.mFourier
      (fun x => -xyBondModeDivergence m x + source x) θ

theorem xyDualCharacterTerm_integral {D : ℕ} {B : Box D} (β : ℝ)
    (source : XYSites B → ℤ) (m : XYBondModes (B := B)) :
    ∫ θ : XYAngleConfig B, xyDualCharacterTerm β source m θ =
      (xyDualConstraintTerm β source m : ℂ) := by
  let q : XYSites B → ℤ := fun x => -xyBondModeDivergence m x + source x
  have horth := xyTorus_character_integral (B := B) q
  have hzero : q = 0 ↔ xyBondModeDivergence m = source := by
    constructor
    · intro h
      funext x
      have hx := congrFun h x
      dsimp [q] at hx
      omega
    · intro h
      funext x
      dsimp [q]
      rw [h]
      abel
  unfold xyDualCharacterTerm
  rw [MeasureTheory.integral_const_mul, horth]
  by_cases h : xyBondModeDivergence m = source
  · have hq : q = 0 := hzero.mpr h
    simp [xyDualConstraintTerm, h, hq]
  · have hq : q ≠ 0 := fun hq => h (hzero.mp hq)
    simp [xyDualConstraintTerm, h, hq]

theorem xyDualCharacterTerm_continuous {D : ℕ} {B : Box D} (β : ℝ)
    (source : XYSites B → ℤ) (m : XYBondModes (B := B)) :
    Continuous (fun θ : XYAngleConfig B => xyDualCharacterTerm β source m θ) := by
  exact continuous_const.mul
    (UnitAddTorus.mFourier
      (fun x => -xyBondModeDivergence m x + source x)).continuous

theorem xyDualCharacterTerm_integrable {D : ℕ} {B : Box D} (β : ℝ)
    (source : XYSites B → ℤ) (m : XYBondModes (B := B)) :
    Integrable (xyDualCharacterTerm β source m) := by
  apply MeasureTheory.integrableOn_univ.mp
  exact (xyDualCharacterTerm_continuous β source m).continuousOn.integrableOn_compact
    isCompact_univ

theorem xyDualCharacterTerm_norm {D : ℕ} {B : Box D} (β : ℝ)
    (source : XYSites B → ℤ) (m : XYBondModes (B := B))
    (θ : XYAngleConfig B) :
    ‖xyDualCharacterTerm β source m θ‖ = xyDualGaussianProduct β m := by
  unfold xyDualCharacterTerm
  rw [norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg (xyDualGaussianProduct_nonneg β m)]
  simp [UnitAddTorus.mFourier]

theorem xyDualCharacterTerm_integral_norm {D : ℕ} {B : Box D} (β : ℝ)
    (source : XYSites B → ℤ) (m : XYBondModes (B := B)) :
    ∫ θ : XYAngleConfig B, ‖xyDualCharacterTerm β source m θ‖ =
      xyDualGaussianProduct β m := by
  simp_rw [xyDualCharacterTerm_norm]
  simp

theorem xyDualCharacterSeries_integral_eq {D : ℕ} {B : Box D} (β : ℝ)
    (hβ : 0 < β) (source : XYSites B → ℤ) :
    ∫ θ : XYAngleConfig B,
      ∑' m : XYBondModes (B := B), xyDualCharacterTerm β source m θ =
        (xyDualPartition β source : ℂ) := by
  have hnormsum : Summable fun m : XYBondModes (B := B) =>
      ∫ θ : XYAngleConfig B, ‖xyDualCharacterTerm β source m θ‖ := by
    apply (xyDualGaussianProduct_summable (B := B) β hβ).congr
    intro m
    exact (xyDualCharacterTerm_integral_norm β source m).symm
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun m => xyDualCharacterTerm_integrable β source m) hnormsum
  rw [← hswap]
  calc
    _ = ∑' m : XYBondModes (B := B), (xyDualConstraintTerm β source m : ℂ) :=
      tsum_congr fun m => xyDualCharacterTerm_integral β source m
    _ = (xyDualPartition β source : ℂ) := by
      unfold xyDualPartition
      exact (Complex.ofReal_tsum (f := xyDualConstraintTerm (B := B) β source)).symm

/-- Character expansion of the finite free-box XY Villain density. -/
theorem xyVillainDensity_characterExpansion {D : ℕ} {B : Box D} (β : ℝ)
    (hβ : 0 < β) (θ : XYAngleConfig B) :
    (xyVillainDensity (B := B) β θ : ℂ) =
      xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
        ∑' m : XYBondModes (B := B),
          (xyDualGaussianProduct β m : ℂ) *
            UnitAddTorus.mFourier (fun x => -xyBondModeDivergence m x) θ := by
  classical
  let g : ℤ → ℝ := xyVillainGaussianCoeff β
  let phase : XYBonds B → ℤ → ℂ := fun b k =>
    fourier (T := (1 : ℝ)) (-k) (xyBondDifference θ b)
  have hg : Summable g := by
    change Summable (fun k : ℤ => Real.exp (-(k : ℝ) ^ 2 / (2 * β)))
    exact villainCharacterCoeff_summable β hβ
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    exact (Real.exp_pos _).le
  have hphase : ∀ b k, ‖phase b k‖ = 1 := by
    intro b k
    simp [phase, fourier_apply]
  have hproduct := product_tsum_fintype (ι := XYBonds B) g hg hg0 phase hphase
  have hcoeff (m : XYBondModes (B := B)) :
      (xyDualGaussianProduct β m : ℂ) =
        ∏ b : XYBonds B, (g (m b) : ℂ) := by
    simp [xyDualGaussianProduct, g, xyVillainGaussianCoeff]
  have hterm (m : XYBondModes (B := B)) :
      (∏ b : XYBonds B, (g (m b) : ℂ) * phase b (m b)) =
        (xyDualGaussianProduct β m : ℂ) *
          UnitAddTorus.mFourier (fun x => -xyBondModeDivergence m x) θ := by
    calc
      _ = (∏ b : XYBonds B, (g (m b) : ℂ)) *
            (∏ b : XYBonds B, phase b (m b)) := Finset.prod_mul_distrib
      _ = _ := by rw [← hcoeff, ← xyBondMode_fourierProduct]
  have hweights :
      (xyVillainDensity (B := B) β θ : ℂ) =
        ∏ b : XYBonds B,
          xyVillainFourierScale β * xyVillainCharacterSeries β
            (xyBondDifference θ b) := by
    unfold xyVillainDensity
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro b hb
    rw [xyVillainCircleWeight_complex β (xyBondDifference θ b) hβ,
      xyVillainFourierMap_eq_characterSeries β hβ]
  calc
    (xyVillainDensity (B := B) β θ : ℂ) =
        xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
          ∏ b : XYBonds B,
            xyVillainCharacterSeries β (xyBondDifference θ b) := by
          rw [hweights, Finset.prod_mul_distrib, Finset.prod_const]
          rfl
    _ = xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
          ∑' m : XYBondModes (B := B),
            ∏ b : XYBonds B, (g (m b) : ℂ) * phase b (m b) := by
          apply congrArg (fun z : ℂ =>
            xyVillainFourierScale β ^ Fintype.card (XYBonds B) * z)
          simpa [xyVillainCharacterSeries, phase, g, xyVillainGaussianCoeff] using hproduct
    _ = xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
          ∑' m : XYBondModes (B := B),
            (xyDualGaussianProduct β m : ℂ) *
              UnitAddTorus.mFourier (fun x => -xyBondModeDivergence m x) θ := by
          apply congrArg (fun z : ℂ =>
            xyVillainFourierScale β ^ Fintype.card (XYBonds B) * z)
          apply tsum_congr
          exact hterm

theorem xyVillainSpinIntegrand_characterExpansion {D : ℕ} {B : Box D}
    (β : ℝ) (hβ : 0 < β) (x y : XYSites B) (θ : XYAngleConfig B) :
    (xyVillainDensity (B := B) β θ : ℂ) * xyEndpointCharacter θ x y =
      xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
        ∑' m : XYBondModes (B := B),
          xyDualCharacterTerm β (xyEndpointFrequency x y) m θ := by
  rw [xyVillainDensity_characterExpansion β hβ θ,
    xyEndpointCharacter_eq_mFourier θ x y]
  calc
    _ = xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
          ((∑' m : XYBondModes (B := B),
            (xyDualGaussianProduct β m : ℂ) *
              UnitAddTorus.mFourier (fun z => -xyBondModeDivergence m z) θ) *
            UnitAddTorus.mFourier (xyEndpointFrequency x y) θ) := by ring
    _ = xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
          ∑' m : XYBondModes (B := B),
            ((xyDualGaussianProduct β m : ℂ) *
              UnitAddTorus.mFourier (fun z => -xyBondModeDivergence m z) θ) *
              UnitAddTorus.mFourier (xyEndpointFrequency x y) θ := by
          congr 1
          rw [← tsum_mul_right]
    _ = xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
          ∑' m : XYBondModes (B := B),
            xyDualCharacterTerm β (xyEndpointFrequency x y) m θ := by
          congr 1
          apply tsum_congr
          intro m
          unfold xyDualCharacterTerm
          have hm := UnitAddTorus.mFourier_add
            (m := fun z => -xyBondModeDivergence m z)
            (n := xyEndpointFrequency x y) (x := θ)
          have hfreq :
              (fun z => -xyBondModeDivergence m z + xyEndpointFrequency x y z) =
                (fun z => -xyBondModeDivergence m z) + xyEndpointFrequency x y := by
            funext z
            rfl
          calc
            _ = (xyDualGaussianProduct β m : ℂ) *
                  (UnitAddTorus.mFourier (fun z => -xyBondModeDivergence m z) θ *
                    UnitAddTorus.mFourier (xyEndpointFrequency x y) θ) := by ring
            _ = _ := by rw [← hm, hfreq]

theorem xyEndpointCharacterNumerator_eq_scale_mul_dualPartition {D : ℕ}
    {B : Box D} (β : ℝ) (hβ : 0 < β) (x y : XYSites B) :
    xyEndpointCharacterNumerator β x y =
      xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
        (xyDualPartition β (xyEndpointFrequency x y) : ℂ) := by
  calc
    xyEndpointCharacterNumerator β x y =
        ∫ θ : XYAngleConfig B,
          xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
            ∑' m : XYBondModes (B := B),
              xyDualCharacterTerm β (xyEndpointFrequency x y) m θ := by
          unfold xyEndpointCharacterNumerator
          apply integral_congr_ae
          filter_upwards with θ
          exact xyVillainSpinIntegrand_characterExpansion β hβ x y θ
    _ = xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
          ∫ θ : XYAngleConfig B,
            ∑' m : XYBondModes (B := B),
              xyDualCharacterTerm β (xyEndpointFrequency x y) m θ :=
          integral_const_mul _ _
    _ = _ := by
          rw [xyDualCharacterSeries_integral_eq β hβ (xyEndpointFrequency x y)]

theorem xyVillainPartition_complex_eq_sameEndpointNumerator {D : ℕ}
    {B : Box D} (β : ℝ) (x : XYSites B) :
    (xyVillainPartition (B := B) β : ℂ) =
      xyEndpointCharacterNumerator β x x := by
  unfold xyVillainPartition xyEndpointCharacterNumerator
  rw [← integral_complex_ofReal]
  congr 1
  funext θ
  simp [xyEndpointCharacter]

theorem xyEndpointCharacterExpectation_eq_dualPartition_ratio {D : ℕ}
    {B : Box D} (β : ℝ) (hβ : 0 < β) (x y : XYSites B) :
    xyEndpointCharacterExpectation β x y =
      (xyDualPartition β (xyEndpointFrequency x y) : ℂ) /
        (xyDualPartition β (0 : XYSites B → ℤ) : ℂ) := by
  have hnum := xyEndpointCharacterNumerator_eq_scale_mul_dualPartition β hβ x y
  have hfreqxx : xyEndpointFrequency x x = 0 := by
    funext z
    simp [xyEndpointFrequency, xyEndpointSource]
  have hden : (xyVillainPartition (B := B) β : ℂ) =
      xyVillainFourierScale β ^ Fintype.card (XYBonds B) *
        (xyDualPartition β (0 : XYSites B → ℤ) : ℂ) := by
    rw [xyVillainPartition_complex_eq_sameEndpointNumerator β x,
      xyEndpointCharacterNumerator_eq_scale_mul_dualPartition β hβ x x,
      hfreqxx]
  have hscale : xyVillainFourierScale β ^ Fintype.card (XYBonds B) ≠ 0 := by
    apply pow_ne_zero
    simp [xyVillainFourierScale]
    positivity
  have hdual : (xyDualPartition β (0 : XYSites B → ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (xyDualPartition_zero_pos (B := B) β hβ).ne'
  unfold xyEndpointCharacterExpectation
  rw [hnum, hden]
  field_simp [hscale, hdual]


abbrev XYEndpointCycleModes {D : ℕ} {B : Box D} :=
  {m : XYBondModes (B := B) // xyBondModeDivergence m = 0}

@[expose] noncomputable def xyShiftedCycleGaussianTerm {D : ℕ} {B : Box D}
    (β : ℝ) (x y : XYSites B) (m : XYBondModes (B := B)) : ℝ :=
    if xyBondModeDivergence m = 0 then
      xyDualGaussianProduct β (m + xyEndpointPathModes x y) else 0

@[expose] noncomputable def xyShiftedCycleGaussianSum {D : ℕ} {B : Box D}
    (β : ℝ) (x y : XYSites B) : ℝ :=
  ∑' m : XYBondModes (B := B), xyShiftedCycleGaussianTerm β x y m

theorem xyShiftedCycleGaussianTerm_nonneg {D : ℕ} {B : Box D}
    (β : ℝ) (x y : XYSites B) (m : XYBondModes (B := B)) :
    0 ≤ xyShiftedCycleGaussianTerm β x y m := by
  unfold xyShiftedCycleGaussianTerm
  split_ifs <;> [exact xyDualGaussianProduct_nonneg β _; exact le_rfl]

theorem xyShiftedCycleGaussianTerm_summable {D : ℕ} {B : Box D}
    (β : ℝ) (hβ : 0 < β) (x y : XYSites B) :
    Summable (xyShiftedCycleGaussianTerm (B := B) β x y) := by
  let path := xyEndpointPathModes x y
  let e : XYBondModes (B := B) ≃ XYBondModes (B := B) := Equiv.addRight (-path)
  have hshift : Summable fun m : XYBondModes (B := B) =>
      xyDualGaussianProduct β (m + path) := by
    have hbase := xyDualGaussianProduct_summable (B := B) β hβ
    have hcomp : Summable (xyDualGaussianProduct (B := B) β ∘ e.symm) :=
      (Equiv.summable_iff (f := xyDualGaussianProduct (B := B) β) e.symm).2 hbase
    apply hcomp.congr
    intro m
    simp [Function.comp_apply, e, Equiv.coe_addRight]
  apply Summable.of_nonneg_of_le
    (fun m => xyShiftedCycleGaussianTerm_nonneg β x y m)
    (fun m => ?_) hshift
  unfold xyShiftedCycleGaussianTerm
  split_ifs with h
  · exact le_rfl
  · exact xyDualGaussianProduct_nonneg β _


theorem xyDualPartition_eq_shiftedCycleGaussianSum {D : ℕ} {B : Box D}
    (β : ℝ) (x y : XYSites B) :
    xyDualPartition β (xyEndpointFrequency x y) =
      xyShiftedCycleGaussianSum β x y := by
  let e : XYBondModes (B := B) ≃ XYBondModes (B := B) :=
    Equiv.addRight (xyEndpointPathModes x y)
  have hpath := xyEndpointPathModes_divergence x y
  have hcondition (m : XYBondModes (B := B)) :
      (xyBondModeDivergence m + xyEndpointFrequency x y = xyEndpointFrequency x y) ↔
        xyBondModeDivergence m = 0 := by
    constructor
    · intro h
      funext z
      have hz := congrFun h z
      change xyBondModeDivergence m z + xyEndpointFrequency x y z =
        xyEndpointFrequency x y z at hz
      have hz' : xyBondModeDivergence m z + xyEndpointFrequency x y z =
          0 + xyEndpointFrequency x y z := by simpa using hz
      exact add_right_cancel hz'
    · intro h
      funext z
      have hz : xyBondModeDivergence m z = 0 := by
        simpa using congrFun h z
      simp [hz]
  unfold xyDualPartition xyShiftedCycleGaussianSum xyShiftedCycleGaussianTerm
  calc
    (∑' m : XYBondModes (B := B), xyDualConstraintTerm β
        (xyEndpointFrequency x y) m) =
        ∑' m : XYBondModes (B := B),
          xyDualConstraintTerm β (xyEndpointFrequency x y) (e m) :=
            (Equiv.tsum_eq e (xyDualConstraintTerm β (xyEndpointFrequency x y))).symm
    _ = ∑' m : XYBondModes (B := B),
          if xyBondModeDivergence m = 0 then
            xyDualGaussianProduct β (m + xyEndpointPathModes x y) else 0 := by
          apply tsum_congr
          intro m
          unfold e xyDualConstraintTerm
          rw [Equiv.coe_addRight, xyBondModeDivergence_add, hpath]
          by_cases hc : xyBondModeDivergence m = 0
          · simp [hc]
          · have hs : xyBondModeDivergence m + xyEndpointFrequency x y ≠
                xyEndpointFrequency x y := fun h => hc ((hcondition m).mp h)
            simp [hs, hc]

@[expose] noncomputable def xyCycleGaussianSum {D : ℕ} {B : Box D}
    (β : ℝ) : ℝ :=
  ∑' m : XYBondModes (B := B),
    if xyBondModeDivergence m = 0 then xyDualGaussianProduct β m else 0

theorem xyCycleGaussianSum_eq_dualPartition {D : ℕ} {B : Box D} (β : ℝ) :
    xyCycleGaussianSum (B := B) β =
      xyDualPartition (B := B) β (0 : XYSites B → ℤ) := by
  unfold xyCycleGaussianSum xyDualPartition xyDualConstraintTerm
  rfl

theorem xyShiftedCycleGaussianSum_eq_fourierCoefficientGaussian {D : ℕ}
    {B : Box D} (β : ℝ) (x y : XYSites B) :
    xyShiftedCycleGaussianSum β x y =
      ∑' m : XYBondModes (B := B),
        if xyBondModeDivergence m = 0 then
          ∏ b : XYBonds B,
            Real.exp (-(((m b + xyEndpointPathModes x y b : ℤ) : ℝ) ^ 2) /
              (2 * β)) else 0 := by
  unfold xyShiftedCycleGaussianSum xyShiftedCycleGaussianTerm
  apply tsum_congr
  intro m
  split_ifs with h
  · simp only [xyDualGaussianProduct, xyVillainGaussianCoeff]
    apply Finset.prod_congr rfl
    intro b hb
    simp only [Pi.add_apply, Int.cast_add]
  · simp

theorem xyEndpointCharacterExpectation_eq_shiftedGaussianRatio {D : ℕ}
    {B : Box D} (β : ℝ) (hβ : 0 < β) (x y : XYSites B) :
    xyEndpointCharacterExpectation β x y =
      (xyShiftedCycleGaussianSum β x y : ℂ) /
        (xyCycleGaussianSum (B := B) β : ℂ) := by
  rw [xyEndpointCharacterExpectation_eq_dualPartition_ratio β hβ x y,
    xyDualPartition_eq_shiftedCycleGaussianSum β x y,
    xyCycleGaussianSum_eq_dualPartition]

end

end FroehlichSpencer.FS82.XY

end
