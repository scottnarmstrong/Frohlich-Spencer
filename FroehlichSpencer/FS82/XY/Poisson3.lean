/- Finite Poisson phase infrastructure for the 3D XY model. -/
module

public import FroehlichSpencer.FS82.XY.Duality
public import FroehlichSpencer.FS82.XY.DualComplex3
public import FroehlichSpencer.FS82.Poisson.TreeGauge
public import FroehlichSpencer.FS82.Gaussian.FiniteGaussian
public import FroehlichSpencer.FS82.Gaussian.FiniteHodge
public import FroehlichSpencer.FS82.Poisson.QuadraticModel
public import FroehlichSpencer.FS82.Poisson.FiniteModel
public import FroehlichSpencer.FS82.Poisson.Scalar
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The D=3 XY Poisson phase model

This module proves the scalar shifted Poisson sanity identity and builds the
finite rooted tree gauge and Hodge quadratic for the three-dimensional dual
link complex.

The finite chord model is an adapter to the generic Poisson
summation theorem.

The source phase is FS82 journal (4.23)--(4.25) and (4.33),
Fröhlich–Spencer (1982); the finite
tree-gauge Poisson adapter is an explicit implementation of that change of
variables.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Poisson


/-- Convert the finite Poisson adapter's tested term to its quadratic Fourier
normalization. -/
theorem xyDual3TestedPrimalTerm_eq {ι : Type*} [Fintype ι]
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

/-- Complex bilinear extension of a real matrix quadratic. -/
def xyDual3ComplexBilinear {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x y : ι → ℝ) : ℂ :=
  ∑ i, ∑ j, (x i : ℂ) * (A i j : ℂ) * (y j : ℂ)

theorem xyDual3ComplexBilinear_eq_dotProduct {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    xyDual3ComplexBilinear A x y =
      (dotProduct x (Matrix.mulVec A y) : ℝ) := by
  simp [xyDual3ComplexBilinear, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_left_comm, mul_comm]

/-- A symmetric real matrix induces a symmetric complex bilinear form on
real vectors. -/
theorem xyDual3ComplexBilinear_comm {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (x y : ι → ℝ) :
    xyDual3ComplexBilinear M x y = xyDual3ComplexBilinear M y x := by
  classical
  have hsymm (i j : ι) : M i j = M j i := by
    have h := congrFun (congrFun hM.eq i) j
    simpa using h.symm
  unfold xyDual3ComplexBilinear
  calc
    _ = ∑ j, ∑ i, (x i : ℂ) * (M i j : ℂ) * (y j : ℂ) := by
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (y i : ℂ) * (M i j : ℂ) * (x j : ℂ) := by
          apply Fintype.sum_congr
          intro i
          apply Fintype.sum_congr
          intro j
          rw [hsymm j i]
          ring
    _ = _ := rfl

/-- Expand a complex quadratic with a real matrix into its real and mixed
bilinear terms. -/
theorem xyDual3ComplexQuadraticExpansion {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι ℝ) (w : ι → ℝ) (k : ι → ℤ) :
    Complex.exp ((Real.pi : ℂ) * ∑ i, ∑ j,
      ((w i : ℂ) - Complex.I * (k i : ℂ)) *
        ((M i j : ℝ) : ℂ) * ((w j : ℂ) - Complex.I * (k j : ℂ))) =
      Complex.exp ((Real.pi : ℂ) * xyDual3ComplexBilinear M w w) *
      Complex.exp (-(Real.pi : ℂ) *
        xyDual3ComplexBilinear M (fun i => (k i : ℝ))
          (fun i => (k i : ℝ))) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I *
        (xyDual3ComplexBilinear M w (fun i => (k i : ℝ)) +
          xyDual3ComplexBilinear M (fun i => (k i : ℝ)) w)) := by
  let kr : ι → ℝ := fun i => (k i : ℝ)
  let Qww := xyDual3ComplexBilinear M w w
  let Qkk := xyDual3ComplexBilinear M kr kr
  let Qwk := xyDual3ComplexBilinear M w kr
  let Qkw := xyDual3ComplexBilinear M kr w
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

/-- Expand the real-source dual Poisson summand into its real Gaussian
factor and Fourier phase. -/
theorem xyDual3DualQuadraticExp_real {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ)
    (w : ι → ℝ) (k : ι → ℤ) :
    dualQuadraticExp A (fun i => (w i : ℂ)) k =
      Complex.exp ((Real.pi : ℂ) *
        xyDual3ComplexBilinear A⁻¹ w w) *
      Complex.exp (-(Real.pi : ℂ) *
        xyDual3ComplexBilinear A⁻¹ (fun i => (k i : ℝ))
          (fun i => (k i : ℝ))) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I *
        (xyDual3ComplexBilinear A⁻¹ w (fun i => (k i : ℝ)) +
          xyDual3ComplexBilinear A⁻¹ (fun i => (k i : ℝ)) w)) := by
  simpa [dualQuadraticExp] using
    (xyDual3ComplexQuadraticExpansion (A⁻¹) w k)


abbrev XYDual3GraphVertex (B : Dual3Box) := Option (Dual3Vertices B)
abbrev XYDual3GraphEdge (B : Dual3Box) := Dual3Links B

def xyDual3Axis0 : Fin 3 := ⟨0, by decide⟩

theorem xyDual3Vertex_axis_left {B : Dual3Box}
    (v : Dual3Vertices B) (i : Fin 3) :
    ∃ n : Fin (B i), v.1 i = Sum.inl n := by
  classical
  cases h : v.1 i with
  | inl n => exact ⟨n, rfl⟩
  | inr e =>
      have hi : i ∈ dualCellAxes v.1 := by simp [dualCellAxes, h]
      have hpos : 0 < (dualCellAxes v.1).card := Finset.card_pos.mpr ⟨i, hi⟩
      rw [show (dualCellAxes v.1).card = 0 from by
        simpa [dualCellDegree] using v.2] at hpos
      omega

noncomputable def xyDual3VertexCoord {B : Dual3Box}
    (v : Dual3Vertices B) (i : Fin 3) : Fin (B i) :=
  Classical.choose (xyDual3Vertex_axis_left v i)

theorem xyDual3VertexCoord_spec {B : Dual3Box}
    (v : Dual3Vertices B) (i : Fin 3) :
    v.1 i = Sum.inl (xyDual3VertexCoord v i) :=
  Classical.choose_spec (xyDual3Vertex_axis_left v i)


noncomputable def xyDual3EdgeAxis {B : Dual3Box}
    (e : Dual3Links B) : Fin 3 := by
  classical
  exact if h : xyDual3Axis0 ∈ dualCellAxes e.1 then xyDual3Axis0 else
    (dualCellAxes e.1).min'
      (Finset.card_pos.mp (by
        have hpos : 0 < dualCellDegree e.1 := by rw [e.2]; norm_num
        exact hpos))

theorem xyDual3EdgeAxis_isRight {B : Dual3Box}
    (e : Dual3Links B) : (e.1 (xyDual3EdgeAxis e)).isRight := by
  classical
  by_cases h : xyDual3Axis0 ∈ dualCellAxes e.1
  · have hm : xyDual3EdgeAxis e ∈ dualCellAxes e.1 := by
      simp [xyDual3EdgeAxis, h]
    exact (Finset.mem_filter.mp hm).2
  · have hm : xyDual3EdgeAxis e ∈ dualCellAxes e.1 := by
      simp [xyDual3EdgeAxis, h]
      exact Finset.min'_mem _ _
    exact (Finset.mem_filter.mp hm).2

theorem xyDual3EdgeAxis_mem {B : Dual3Box}
    (e : Dual3Links B) : xyDual3EdgeAxis e ∈ dualCellAxes e.1 := by
  classical
  by_cases h : xyDual3Axis0 ∈ dualCellAxes e.1
  · simp [xyDual3EdgeAxis, h]
  · have hm : xyDual3EdgeAxis e ∈ dualCellAxes e.1 := by
      simp [xyDual3EdgeAxis, h]
      exact Finset.min'_mem _ _
    exact hm

theorem xyDual3EdgeAxis_unique {B : Dual3Box}
    (e : Dual3Links B) {i j : Fin 3}
    (hi : (e.1 i).isRight) (hj : (e.1 j).isRight) : i = j := by
  by_contra hne
  have hcard : (dualCellAxes e.1).card = 1 := by
    simpa [dualCellDegree] using e.2
  have hpair : i ∈ dualCellAxes e.1 ∧ j ∈ dualCellAxes e.1 := by
    simp [dualCellAxes, hi, hj]
  have hsub : ({i, j} : Finset (Fin 3)) ⊆ dualCellAxes e.1 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hpair.1
    · exact hpair.2
  have htwo : ({i, j} : Finset (Fin 3)).card = 2 := by simp [hne]
  have := Finset.card_le_card hsub
  rw [htwo, hcard] at this
  omega

noncomputable def xyDual3EdgeAxisCoordAtZero {B : Dual3Box}
    (e : Dual3Links B)
    (h : xyDual3Axis0 ∈ dualCellAxes e.1) : Fin (B xyDual3Axis0 + 1) :=
  Classical.choose (show ∃ n, e.1 xyDual3Axis0 = Sum.inr n from by
    cases hc : e.1 xyDual3Axis0 with
    | inl v =>
        have hright := (Finset.mem_filter.mp h).2
        rw [hc] at hright
        simp at hright
    | inr n => exact ⟨n, rfl⟩)

noncomputable def xyDual3EdgeAxisCoordElse {B : Dual3Box}
    (e : Dual3Links B) : Fin (B (xyDual3EdgeAxis e) + 1) :=
  Classical.choose (show ∃ n, e.1 (xyDual3EdgeAxis e) = Sum.inr n from by
    cases hc : e.1 (xyDual3EdgeAxis e) with
    | inl v =>
        have hright := xyDual3EdgeAxis_isRight e
        rw [hc] at hright
        simp at hright
    | inr n => exact ⟨n, rfl⟩)

theorem xyDual3EdgeAxisCoordAtZero_spec {B : Dual3Box}
    (e : Dual3Links B) (h : xyDual3Axis0 ∈ dualCellAxes e.1) :
    e.1 xyDual3Axis0 = Sum.inr (xyDual3EdgeAxisCoordAtZero e h) := by
  exact Classical.choose_spec (show ∃ n, e.1 xyDual3Axis0 = Sum.inr n from by
    cases hc : e.1 xyDual3Axis0 with
    | inl v =>
        have hright := (Finset.mem_filter.mp h).2
        rw [hc] at hright
        simp at hright
    | inr n => exact ⟨n, rfl⟩)

theorem xyDual3EdgeAxisCoordElse_spec {B : Dual3Box}
    (e : Dual3Links B) :
    e.1 (xyDual3EdgeAxis e) = Sum.inr (xyDual3EdgeAxisCoordElse e) := by
  exact Classical.choose_spec (show ∃ n, e.1 (xyDual3EdgeAxis e) = Sum.inr n from by
    cases hc : e.1 (xyDual3EdgeAxis e) with
    | inl v =>
        have hright := xyDual3EdgeAxis_isRight e
        rw [hc] at hright
        simp at hright
    | inr n => exact ⟨n, rfl⟩)

noncomputable def xyDual3EdgeAxisIndex {B : Dual3Box}
    (e : Dual3Links B) : ℕ :=
  (xyDual3EdgeAxisCoordElse e).val

theorem xyDual3EdgeAxisIndex_lt {B : Dual3Box}
    (e : Dual3Links B) :
    xyDual3EdgeAxisIndex e < B (xyDual3EdgeAxis e) + 1 := by
  exact (xyDual3EdgeAxisCoordElse e).isLt


theorem xyDual3Edge_otherCoord_left_of_mem {B : Dual3Box}
    (e : Dual3Links B) {i j : Fin 3}
    (hi : i ∈ dualCellAxes e.1) (hji : j ≠ i) :
    ∃ n : Fin (B j), e.1 j = Sum.inl n := by
  classical
  cases hj : e.1 j with
  | inl n => exact ⟨n, rfl⟩
  | inr n =>
      have hrighti := (Finset.mem_filter.mp hi).2
      have hrightj : (e.1 j).isRight := by simp [hj]
      exact (hji (xyDual3EdgeAxis_unique e
        (i := i) (j := j) hrighti hrightj).symm).elim

noncomputable def xyDual3VertexOfEdgeCoordAtAxis {B : Dual3Box}
    (e : Dual3Links B) (i : Fin 3)
    (hi : i ∈ dualCellAxes e.1) (n : Fin (B i)) :
    Dual3Vertices B :=
  ⟨Function.update e.1 i (Sum.inl n), by
    have haxes :
        dualCellAxes (Function.update e.1 i (Sum.inl n)) = ∅ := by
      ext j
      simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty]
      by_cases hji : j = i
      · subst j
        simp [Function.update]
      · obtain ⟨m, hm⟩ := xyDual3Edge_otherCoord_left_of_mem e hi hji
        rw [Function.update_of_ne hji]
        rw [hm]
        simp
    simp [dualCellDegree, haxes]⟩

@[simp] theorem xyDual3VertexOfEdgeCoordAtAxis_apply_axis {B : Dual3Box}
    (e : Dual3Links B) (i : Fin 3) (hi : i ∈ dualCellAxes e.1)
    (n : Fin (B i)) :
    (xyDual3VertexOfEdgeCoordAtAxis e i hi n).1 i = Sum.inl n := by
  simp [xyDual3VertexOfEdgeCoordAtAxis]

@[simp] theorem xyDual3VertexOfEdgeCoordAtAxis_apply_ne {B : Dual3Box}
    (e : Dual3Links B) (i j : Fin 3) (hi : i ∈ dualCellAxes e.1)
    (n : Fin (B i)) (hji : j ≠ i) :
    (xyDual3VertexOfEdgeCoordAtAxis e i hi n).1 j = e.1 j := by
  simp [xyDual3VertexOfEdgeCoordAtAxis, Function.update_of_ne hji]

noncomputable def xyDual3EdgeLowerVertex {B : Dual3Box}
    (e : Dual3Links B) : XYDual3GraphVertex B := by
  classical
  let k := xyDual3EdgeAxisIndex e
  exact if hk : k = 0 then none else
    some (xyDual3VertexOfEdgeCoordAtAxis e (xyDual3EdgeAxis e)
      (xyDual3EdgeAxis_mem e) ⟨k - 1, by
      have hklt := xyDual3EdgeAxisIndex_lt e
      omega⟩)

theorem xyDual3EdgeLowerVertex_of_index_ne_zero {B : Dual3Box}
    (e : Dual3Links B) (hk : xyDual3EdgeAxisIndex e ≠ 0) :
    xyDual3EdgeLowerVertex e =
      some (xyDual3VertexOfEdgeCoordAtAxis e (xyDual3EdgeAxis e)
        (xyDual3EdgeAxis_mem e)
        ⟨xyDual3EdgeAxisIndex e - 1, by
          have hklt := xyDual3EdgeAxisIndex_lt e
          omega⟩) := by
  simp [xyDual3EdgeLowerVertex, hk]

noncomputable def xyDual3EdgeUpperVertex {B : Dual3Box}
    (e : Dual3Links B) : XYDual3GraphVertex B := by
  classical
  let k := xyDual3EdgeAxisIndex e
  exact if hk : k = B (xyDual3EdgeAxis e) then none else
    some (xyDual3VertexOfEdgeCoordAtAxis e (xyDual3EdgeAxis e)
      (xyDual3EdgeAxis_mem e) ⟨k, by
      have hklt := xyDual3EdgeAxisIndex_lt e
      omega⟩)

theorem xyDual3EdgeAxisCoord_spec {B : Dual3Box}
    (e : Dual3Links B) :
    e.1 (xyDual3EdgeAxis e) =
      Sum.inr ⟨xyDual3EdgeAxisIndex e, xyDual3EdgeAxisIndex_lt e⟩ := by
  calc
    e.1 (xyDual3EdgeAxis e) =
        Sum.inr (xyDual3EdgeAxisCoordElse e) :=
          xyDual3EdgeAxisCoordElse_spec e
    _ = Sum.inr ⟨xyDual3EdgeAxisIndex e,
        xyDual3EdgeAxisIndex_lt e⟩ := by
      rfl

noncomputable def xyDual3TreeLinkCell {B : Dual3Box}
    (v : Dual3Vertices B) : DualCell 3 B :=
  Function.update v.1 xyDual3Axis0
    (Sum.inr ⟨(xyDual3VertexCoord v xyDual3Axis0).val,
      Nat.lt_succ_of_lt (xyDual3VertexCoord v xyDual3Axis0).isLt⟩)

theorem xyDual3TreeLinkCell_axes {B : Dual3Box}
    (v : Dual3Vertices B) :
    dualCellAxes (xyDual3TreeLinkCell v) = {xyDual3Axis0} := by
  ext j
  simp only [dualCellAxes, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  by_cases hji : j = xyDual3Axis0
  · subst j
    simp [xyDual3TreeLinkCell, Function.update]
  · obtain ⟨m, hm⟩ := xyDual3Vertex_axis_left v j
    constructor
    · intro hj
      rw [show xyDual3TreeLinkCell v j = v.1 j by
        simp [xyDual3TreeLinkCell, Function.update_of_ne hji], hm] at hj
      simp at hj
    · intro hj
      exact (hji hj).elim

noncomputable def xyDual3TreeLink {B : Dual3Box}
    (v : Dual3Vertices B) : Dual3Links B :=
  ⟨xyDual3TreeLinkCell v, by
    change (dualCellAxes (xyDual3TreeLinkCell v)).card = 1
    rw [xyDual3TreeLinkCell_axes]
    simp⟩


@[simp] theorem xyDual3TreeLink_axis {B : Dual3Box}
    (v : Dual3Vertices B) :
    (xyDual3TreeLink v).1 xyDual3Axis0 =
      Sum.inr ⟨(xyDual3VertexCoord v xyDual3Axis0).val,
        Nat.lt_succ_of_lt (xyDual3VertexCoord v xyDual3Axis0).isLt⟩ := by
  simp [xyDual3TreeLink, xyDual3TreeLinkCell]


theorem xyDual3TreeLink_axis_selected {B : Dual3Box}
    (v : Dual3Vertices B) :
    xyDual3EdgeAxis (xyDual3TreeLink v) = xyDual3Axis0 := by
  classical
  unfold xyDual3EdgeAxis
  simp [xyDual3TreeLink, xyDual3TreeLinkCell_axes]

@[simp] theorem xyDual3EdgeAxis_treeLink {B : Dual3Box}
    (v : Dual3Vertices B) :
    xyDual3EdgeAxis (xyDual3TreeLink v) = xyDual3Axis0 :=
  xyDual3TreeLink_axis_selected v

theorem xyDual3TreeLink_axisCoord {B : Dual3Box}
    (v : Dual3Vertices B) :
    xyDual3EdgeAxisIndex (xyDual3TreeLink v) =
      (xyDual3VertexCoord v xyDual3Axis0).val := by
  have hmemCell : xyDual3Axis0 ∈ dualCellAxes (xyDual3TreeLinkCell v) := by
    rw [xyDual3TreeLinkCell_axes]
    simp
  have hmem : xyDual3Axis0 ∈ dualCellAxes (xyDual3TreeLink v).1 := by
    simpa [xyDual3TreeLink] using hmemCell
  have hSpec := xyDual3EdgeAxisCoordAtZero_spec (xyDual3TreeLink v) hmem
  rw [xyDual3TreeLink_axis] at hSpec
  have hCoord :
      xyDual3EdgeAxisCoordAtZero (xyDual3TreeLink v) hmem =
        ⟨(xyDual3VertexCoord v xyDual3Axis0).val,
          Nat.lt_succ_of_lt (xyDual3VertexCoord v xyDual3Axis0).isLt⟩ :=
    (Sum.inr.inj hSpec).symm
  change (if h : xyDual3Axis0 ∈
      dualCellAxes (xyDual3TreeLink v).1 then
    (xyDual3EdgeAxisCoordAtZero (xyDual3TreeLink v) h).val
    else (xyDual3EdgeAxisCoordElse (xyDual3TreeLink v)).val) = _
  rw [dite_eq_left hmem]
  exact congrArg Fin.val hCoord

theorem xyDual3TreeLink_upperVertex {B : Dual3Box}
    (v : Dual3Vertices B) :
    xyDual3EdgeUpperVertex (xyDual3TreeLink v) = some v := by
  classical
  have hindexLt : xyDual3EdgeAxisIndex (xyDual3TreeLink v) <
      B (xyDual3Axis0) := by
    rw [xyDual3TreeLink_axisCoord]
    exact (xyDual3VertexCoord v xyDual3Axis0).isLt
  have hindexNe : xyDual3EdgeAxisIndex (xyDual3TreeLink v) ≠
      B (xyDual3EdgeAxis (xyDual3TreeLink v)) := by
    rw [xyDual3EdgeAxis_treeLink, xyDual3TreeLink_axisCoord]
    exact ne_of_lt (xyDual3VertexCoord v xyDual3Axis0).isLt
  unfold xyDual3EdgeUpperVertex
  rw [dite_eq_right hindexNe]
  apply congrArg some
  apply Subtype.ext
  funext j
  by_cases hji : j = xyDual3Axis0
  · subst j
    change Function.update (xyDual3TreeLink v).1 xyDual3Axis0
      (Sum.inl ⟨xyDual3EdgeAxisIndex (xyDual3TreeLink v), hindexLt⟩)
      xyDual3Axis0 = v.1 xyDual3Axis0
    rw [xyDual3VertexCoord_spec]
    exact congrArg Sum.inl (Fin.ext (xyDual3TreeLink_axisCoord v))
  · change Function.update (xyDual3TreeLink v).1 xyDual3Axis0
      (Sum.inl ⟨xyDual3EdgeAxisIndex (xyDual3TreeLink v), hindexLt⟩)
      j = v.1 j
    simp [xyDual3TreeLink, xyDual3TreeLinkCell, hji]

theorem xyDual3TreeLink_lowerVertex {B : Dual3Box}
    (v : Dual3Vertices B) :
    xyDual3EdgeLowerVertex (xyDual3TreeLink v) =
      if (xyDual3VertexCoord v xyDual3Axis0).val = 0 then none
      else some (xyDual3VertexOfEdgeCoordAtAxis
        (xyDual3TreeLink v) xyDual3Axis0 (by
          change xyDual3Axis0 ∈ dualCellAxes (xyDual3TreeLinkCell v)
          rw [xyDual3TreeLinkCell_axes]
          simp)
        ⟨(xyDual3VertexCoord v xyDual3Axis0).val - 1, by
          have h := (xyDual3VertexCoord v xyDual3Axis0).isLt
          omega⟩) := by
  classical
  by_cases hzero : (xyDual3VertexCoord v xyDual3Axis0).val = 0
  · simp [xyDual3EdgeLowerVertex, xyDual3TreeLink_axisCoord,
      hzero]
  · rw [xyDual3EdgeLowerVertex_of_index_ne_zero _ (by
      rw [xyDual3TreeLink_axisCoord]
      exact hzero)]
    simp only [xyDual3TreeLink_axisCoord, ite_eq_right hzero]
    rfl

noncomputable def xyDual3GraphSource {B : Dual3Box}
    (e : XYDual3GraphEdge B) : XYDual3GraphVertex B :=
  if Even (xyDual3EdgeAxis e).val then xyDual3EdgeLowerVertex e
  else xyDual3EdgeUpperVertex e

noncomputable def xyDual3GraphTarget {B : Dual3Box}
    (e : XYDual3GraphEdge B) : XYDual3GraphVertex B :=
  if Even (xyDual3EdgeAxis e).val then xyDual3EdgeUpperVertex e
  else xyDual3EdgeLowerVertex e

noncomputable def xyDual3TreeParent {B : Dual3Box}
    (x : XYDual3GraphVertex B) : XYDual3GraphVertex B :=
  match x with
  | none => none
  | some v => xyDual3EdgeLowerVertex (xyDual3TreeLink v)

noncomputable def xyDual3TreeDepth {B : Dual3Box}
    (x : XYDual3GraphVertex B) : ℕ :=
  match x with
  | none => 0
  | some v => (xyDual3VertexCoord v xyDual3Axis0).val + 1

theorem xyDual3TreeDepth_le {B : Dual3Box} (x : XYDual3GraphVertex B) :
    xyDual3TreeDepth x ≤ B xyDual3Axis0 := by
  cases x with
  | none => simp [xyDual3TreeDepth]
  | some v =>
    simp only [xyDual3TreeDepth]
    have h := (xyDual3VertexCoord v xyDual3Axis0).isLt
    omega

theorem xyDual3VertexCoord_ofEdgeCoordAtAxis {B : Dual3Box}
    (e : Dual3Links B) (i : Fin 3)
    (hi : i ∈ dualCellAxes e.1) (n : Fin (B i)) :
    xyDual3VertexCoord (xyDual3VertexOfEdgeCoordAtAxis e i hi n) i = n := by
  have hspec := xyDual3VertexCoord_spec
    (xyDual3VertexOfEdgeCoordAtAxis e i hi n) i
  have haxis := xyDual3VertexOfEdgeCoordAtAxis_apply_axis e i hi n
  rw [haxis] at hspec
  exact (Sum.inl.inj hspec).symm

theorem xyDual3Tree_depth_parent {B : Dual3Box}
    {x : XYDual3GraphVertex B} (hx : x ≠ none) :
    xyDual3TreeDepth (xyDual3TreeParent x) + 1 =
      xyDual3TreeDepth x := by
  cases x with
  | none => exact (hx rfl).elim
  | some v =>
    simp only [xyDual3TreeParent, xyDual3TreeDepth]
    by_cases hzero : (xyDual3VertexCoord v xyDual3Axis0).val = 0
    · simp [xyDual3TreeLink_lowerVertex, hzero]
    · rw [xyDual3TreeLink_lowerVertex]
      simp only [hzero, ↓reduceIte]
      rw [xyDual3VertexCoord_ofEdgeCoordAtAxis]
      simp only
      omega

noncomputable def xyDual3TreeEdge {B : Dual3Box}
    (x : {x : XYDual3GraphVertex B // x ≠ none}) : XYDual3GraphEdge B := by
  rcases x with ⟨x, hx⟩
  cases x with
  | none => exact (hx rfl).elim
  | some v => exact xyDual3TreeLink v

theorem xyDual3TreeEdge_target {B : Dual3Box}
    (x : {x : XYDual3GraphVertex B // x ≠ none}) :
    xyDual3EdgeUpperVertex (xyDual3TreeEdge x) = x.1 := by
  rcases x with ⟨x, hx⟩
  cases x with
  | none => exact (hx rfl).elim
  | some v => simpa [xyDual3TreeEdge] using xyDual3TreeLink_upperVertex v

theorem xyDual3TreeEdge_source {B : Dual3Box}
    (x : {x : XYDual3GraphVertex B // x ≠ none}) :
    xyDual3EdgeLowerVertex (xyDual3TreeEdge x) = xyDual3TreeParent x.1 := by
  rcases x with ⟨x, hx⟩
  cases x with
  | none => exact (hx rfl).elim
  | some v => rfl

noncomputable def xyDual3RootedTree (B : Dual3Box) :
    RootedTreeGauge (XYDual3GraphVertex B) (XYDual3GraphEdge B) where
  root := none
  parent := xyDual3TreeParent
  depth := xyDual3TreeDepth
  height := B xyDual3Axis0
  depth_le_height := xyDual3TreeDepth_le
  edgeSource := xyDual3GraphSource
  edgeTarget := xyDual3GraphTarget
  treeEdge := xyDual3TreeEdge
  treeEdge_injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    apply Subtype.ext
    have hxy := congrArg xyDual3EdgeUpperVertex h
    have hleft := xyDual3TreeEdge_target ⟨x, hx⟩
    have hright := xyDual3TreeEdge_target ⟨y, hy⟩
    rw [hleft, hright] at hxy
    exact hxy
  treeEdge_source := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x with
    | none => exact (hx rfl).elim
    | some v =>
      change xyDual3GraphSource (xyDual3TreeLink v) = _
      rw [xyDual3GraphSource, xyDual3EdgeAxis_treeLink]
      simp only [xyDual3Axis0, Even.zero]
      exact xyDual3TreeEdge_source ⟨some v, by simp⟩
  treeEdge_target := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x with
    | none => exact (hx rfl).elim
    | some v =>
      change xyDual3GraphTarget (xyDual3TreeLink v) = _
      rw [xyDual3GraphTarget, xyDual3EdgeAxis_treeLink]
      simp only [xyDual3Axis0, Even.zero]
      exact xyDual3TreeEdge_target ⟨some v, by simp⟩
  depth_root := rfl
  depth_pos := by
    intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some v => simp [xyDual3TreeDepth]
  depth_parent := xyDual3Tree_depth_parent

open FroehlichSpencer.FS82.Gaussian

noncomputable def xyDual3PoissonMatrix {B : Dual3Box} :
    Matrix (Dual3Links B) (Dual3Links B) ℝ :=
  matrixOfLinearMap (formLaplacian (dual3ExactOneComplex B))

theorem xyDual3D0_single_eq_stencil {B : Dual3Box}
    (v : Dual3Vertices B) (e : Dual3Links B) :
    (dual3ExactOneComplex B).d₀ (EuclideanSpace.single v 1) e =
      dualExteriorDifferenceStencilBasis v.1 e.1 := by
  have hvec : euclideanToFinsupp (EuclideanSpace.single v (1 : ℝ)) =
      Finsupp.single v (1 : ℝ) := by
    ext a
    by_cases h : a = v <;> simp [euclideanToFinsupp_apply, h]
  have hv : dual3VerticesToChain (EuclideanSpace.single v (1 : ℝ)) =
      Finsupp.single v.1 (1 : ℝ) := by
    change dual3EmbedSubtype dual3VerticesEmbedding
      (euclideanToFinsupp (EuclideanSpace.single v (1 : ℝ))) = _
    rw [hvec]
    simp [dual3VerticesEmbedding, dual3EmbedSubtype_apply_single]
  have h := congrArg (fun q : DualRealChain 3 B => q e.1)
    (dual3D₀_embed_eq_derivative (EuclideanSpace.single v 1))
  have hleft :
      (dual3LinksToChain (dual3D₀ (EuclideanSpace.single v 1))) e.1 =
        dual3D₀ (EuclideanSpace.single v 1) e := by
    change (dual3EmbedSubtype dual3LinksEmbedding
        (euclideanToFinsupp (dual3D₀ (EuclideanSpace.single v 1))))
          (dual3LinksEmbedding e) = _
    rw [dual3EmbedSubtype_apply_at_image]
    simp [euclideanToFinsupp_apply]
  rw [hleft, hv] at h
  rw [dualExteriorDifference_basis_eq_coordinateStencil] at h
  change dual3D₀ (EuclideanSpace.single v 1) e = _
  exact h

theorem xyDual3VertexRankBefore_eq {B : Dual3Box}
    (v : Dual3Vertices B) (i : Fin 3) :
    dualVertexRankBefore v.1 i = i.val := by
  have hleft (j : Fin 3) : ¬ (v.1 j).isRight := by
    obtain ⟨n, hn⟩ := xyDual3Vertex_axis_left v j
    rw [hn]
    simp
  unfold dualVertexRankBefore
  have hset :
      Finset.univ.filter (fun j : Fin 3 => j < i ∧ ¬ (v.1 j).isRight) =
        Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · rintro ⟨hji, _⟩
      exact hji
    · intro hji
      refine ⟨hji, ?_⟩
      obtain ⟨n, hn⟩ := xyDual3Vertex_axis_left v j
      simp [hn]
  rw [hset]
  simp

theorem xyDual3D0_single_faces {B : Dual3Box}
    (v : Dual3Vertices B) (e : Dual3Links B) :
    (dual3ExactOneComplex B).d₀ (EuclideanSpace.single v 1) e =
      (-1 : ℝ) ^ (xyDual3EdgeAxis e).val *
        ((if e.1 = dualUpperFace v.1 (xyDual3EdgeAxis e)
              (xyDual3VertexCoord v (xyDual3EdgeAxis e)) then 1 else 0) -
         (if e.1 = dualLowerFace v.1 (xyDual3EdgeAxis e)
              (xyDual3VertexCoord v (xyDual3EdgeAxis e)) then 1 else 0)) := by
  rw [xyDual3D0_single_eq_stencil]
  unfold dualExteriorDifferenceStencilBasis
  rw [← Finsupp.lapply_apply (R := ℝ) (M := ℝ) e.1]
  simp only [map_sum, Finsupp.lapply_apply]
  let i := xyDual3EdgeAxis e
  have hi : i ∈ dualCellAxes e.1 := xyDual3EdgeAxis_mem e
  rw [Finset.sum_eq_single i]
  · obtain ⟨n, hn⟩ := xyDual3Vertex_axis_left v i
    have hcoord : n = xyDual3VertexCoord v i := by
      have h := xyDual3VertexCoord_spec v i
      rw [hn] at h
      exact (Sum.inl.inj h)
    rw [hn, hcoord]
    simp only [i, xyDual3VertexRankBefore_eq]
    simp [Finsupp.single_apply, smul_eq_mul, eq_comm]
  · intro j hj hji
    have hupper : dualUpperFace v.1 j (xyDual3VertexCoord v j) ≠ e.1 := by
      intro heq
      have hjmem : j ∈ dualCellAxes e.1 := by
        rw [← heq]
        change j ∈ Finset.univ.filter (fun k : Fin 3 =>
          (dualUpperFace v.1 j (xyDual3VertexCoord v j) k).isRight)
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · simp [dualUpperFace]
      have hAxis := xyDual3EdgeAxis_unique e
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hjmem).2
      exact hji hAxis.symm
    have hupper' : e.1 ≠ dualUpperFace v.1 j (xyDual3VertexCoord v j) :=
      fun h => hupper h.symm
    have hlower : dualLowerFace v.1 j (xyDual3VertexCoord v j) ≠ e.1 := by
      intro heq
      have hjmem : j ∈ dualCellAxes e.1 := by
        rw [← heq]
        change j ∈ Finset.univ.filter (fun k : Fin 3 =>
          (dualLowerFace v.1 j (xyDual3VertexCoord v j) k).isRight)
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · simp [dualLowerFace]
      have hAxis := xyDual3EdgeAxis_unique e
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hjmem).2
      exact hji hAxis.symm
    have hlower' : e.1 ≠ dualLowerFace v.1 j (xyDual3VertexCoord v j) :=
      fun h => hlower h.symm
    obtain ⟨n, hn⟩ := xyDual3Vertex_axis_left v j
    have hncoord : n = xyDual3VertexCoord v j := by
      have h := xyDual3VertexCoord_spec v j
      rw [hn] at h
      exact (Sum.inl.inj h)
    rw [hn, hncoord]
    simp [hupper, hlower]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem xyDual3_upperFace_eq_linkLower {B : Dual3Box}
    (v : Dual3Vertices B) (e : Dual3Links B) :
    e.1 = dualUpperFace v.1 (xyDual3EdgeAxis e)
        (xyDual3VertexCoord v (xyDual3EdgeAxis e)) ↔
      xyDual3EdgeLowerVertex e = some v := by
  constructor
  · intro h
    let i := xyDual3EdgeAxis e
    have haxis := congrFun h i
    rw [xyDual3EdgeAxisCoord_spec, dualUpperFace, Function.update_self] at haxis
    have hk : xyDual3EdgeAxisIndex e =
        (xyDual3VertexCoord v i).val + 1 :=
      congrArg Fin.val (Sum.inr.inj haxis)
    have hk0 : xyDual3EdgeAxisIndex e ≠ 0 := by omega
    rw [xyDual3EdgeLowerVertex_of_index_ne_zero e hk0]
    apply congrArg some
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      rw [xyDual3VertexOfEdgeCoordAtAxis_apply_axis]
      rw [xyDual3VertexCoord_spec]
      congr 1
      apply Fin.ext
      simp only [i] at hk ⊢
      omega
    · rw [xyDual3VertexOfEdgeCoordAtAxis_apply_ne _ _ _ _ _ hji]
      have hj := congrFun h j
      change e.1 j = Function.update v.1 i
        (Sum.inr ⟨(xyDual3VertexCoord v i).val + 1, _⟩) j at hj
      rw [Function.update_of_ne hji] at hj
      exact hj
  · intro h
    let i := xyDual3EdgeAxis e
    by_cases hzero : xyDual3EdgeAxisIndex e = 0
    · simp [xyDual3EdgeLowerVertex, hzero] at h
    · rw [xyDual3EdgeLowerVertex_of_index_ne_zero e hzero] at h
      have hv := Option.some.inj h
      have hcoord :
          (⟨xyDual3EdgeAxisIndex e - 1, by
            have hk := xyDual3EdgeAxisIndex_lt e
            omega⟩ : Fin (B (xyDual3EdgeAxis e))) =
            xyDual3VertexCoord v (xyDual3EdgeAxis e) := by
        have haxis := congrArg (fun w : Dual3Vertices B =>
          w.1 (xyDual3EdgeAxis e)) hv
        rw [xyDual3VertexOfEdgeCoordAtAxis_apply_axis,
          xyDual3VertexCoord_spec] at haxis
        exact (Sum.inl.inj haxis)
      funext j
      by_cases hji : j = i
      · subst j
        have hk := xyDual3EdgeAxisIndex_lt e
        have hval := congrArg Fin.val hcoord
        rw [xyDual3EdgeAxisCoord_spec]
        simp only [dualUpperFace, i, Function.update_self]
        apply congrArg Sum.inr
        apply Fin.ext
        have hval' : xyDual3EdgeAxisIndex e - 1 =
            (xyDual3VertexCoord v (xyDual3EdgeAxis e)).val :=
          congrArg Fin.val hcoord
        have hpos : 0 < xyDual3EdgeAxisIndex e := Nat.pos_of_ne_zero hzero
        change xyDual3EdgeAxisIndex e =
          (xyDual3VertexCoord v (xyDual3EdgeAxis e)).val + 1
        omega
      · have hother := congrArg (fun w : Dual3Vertices B => w.1 j) hv
        rw [xyDual3VertexOfEdgeCoordAtAxis_apply_ne _ _ _ _ _ hji] at hother
        rw [dualUpperFace, Function.update_of_ne hji]
        exact hother

theorem xyDual3_lowerFace_eq_linkUpper {B : Dual3Box}
    (v : Dual3Vertices B) (e : Dual3Links B) :
    e.1 = dualLowerFace v.1 (xyDual3EdgeAxis e)
        (xyDual3VertexCoord v (xyDual3EdgeAxis e)) ↔
      xyDual3EdgeUpperVertex e = some v := by
  constructor
  · intro h
    let i := xyDual3EdgeAxis e
    have haxis := congrFun h i
    rw [xyDual3EdgeAxisCoord_spec, dualLowerFace, Function.update_self] at haxis
    have hk : xyDual3EdgeAxisIndex e =
        (xyDual3VertexCoord v i).val :=
      congrArg Fin.val (Sum.inr.inj haxis)
    have htop : xyDual3EdgeAxisIndex e ≠ B (xyDual3EdgeAxis e) := by
      have hn := (xyDual3VertexCoord v i).isLt
      have hn' : (xyDual3VertexCoord v (xyDual3EdgeAxis e)).val <
          B (xyDual3EdgeAxis e) := hn
      rw [hk]
      exact ne_of_lt hn
    have hUpper : xyDual3EdgeUpperVertex e =
        some (xyDual3VertexOfEdgeCoordAtAxis e (xyDual3EdgeAxis e)
          (xyDual3EdgeAxis_mem e)
          ⟨xyDual3EdgeAxisIndex e, by
            have hn := xyDual3EdgeAxisIndex_lt e
            omega⟩) := by
      simp [xyDual3EdgeUpperVertex, htop]
    rw [hUpper]
    apply congrArg some
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      rw [xyDual3VertexOfEdgeCoordAtAxis_apply_axis]
      rw [xyDual3VertexCoord_spec]
      congr 1
      apply Fin.ext
      have hk' := hk
      simp only [i] at hk' ⊢
      omega
    · rw [xyDual3VertexOfEdgeCoordAtAxis_apply_ne _ _ _ _ _ hji]
      have hj := congrFun h j
      change e.1 j = Function.update v.1 i
        (Sum.inr ⟨(xyDual3VertexCoord v i).val, _⟩) j at hj
      rw [Function.update_of_ne hji] at hj
      exact hj
  · intro h
    let i := xyDual3EdgeAxis e
    by_cases htop : xyDual3EdgeAxisIndex e = B (xyDual3EdgeAxis e)
    · simp [xyDual3EdgeUpperVertex, htop] at h
    · have hUpper : xyDual3EdgeUpperVertex e =
          some (xyDual3VertexOfEdgeCoordAtAxis e (xyDual3EdgeAxis e)
            (xyDual3EdgeAxis_mem e)
            ⟨xyDual3EdgeAxisIndex e, by
              have hn := xyDual3EdgeAxisIndex_lt e
              omega⟩) := by
        simp [xyDual3EdgeUpperVertex, htop]
      rw [hUpper] at h
      have hv := Option.some.inj h
      have hcoord :
          (⟨xyDual3EdgeAxisIndex e, by
            have hn := xyDual3EdgeAxisIndex_lt e
            omega⟩ : Fin (B (xyDual3EdgeAxis e))) =
            xyDual3VertexCoord v i := by
        have haxis := congrArg (fun w : Dual3Vertices B => w.1 i) hv
        rw [xyDual3VertexOfEdgeCoordAtAxis_apply_axis,
          xyDual3VertexCoord_spec] at haxis
        exact Sum.inl.inj haxis
      funext j
      by_cases hji : j = i
      · subst j
        rw [xyDual3EdgeAxisCoord_spec]
        simp only [dualLowerFace, i, Function.update_self]
        apply congrArg Sum.inr
        apply Fin.ext
        have hval := congrArg Fin.val hcoord
        simp only at hval ⊢
        exact hval
      · have hother := congrArg (fun w : Dual3Vertices B => w.1 j) hv
        rw [xyDual3VertexOfEdgeCoordAtAxis_apply_ne _ _ _ _ _ hji] at hother
        rw [dualLowerFace, Function.update_of_ne hji]
        exact hother

noncomputable def xyDual3VertexPotentialVector {B : Dual3Box}
    (p : XYDual3GraphVertex B → ℝ) : EuclideanSpace ℝ (Dual3Vertices B) :=
  finsuppToEuclidean (Finsupp.equivFunOnFinite.symm
    (fun v : Dual3Vertices B => p (some v) - p none))

@[simp] theorem xyDual3VertexPotentialVector_apply {B : Dual3Box}
    (p : XYDual3GraphVertex B → ℝ) (v : Dual3Vertices B) :
    xyDual3VertexPotentialVector p v = p (some v) - p none := by
  simp [xyDual3VertexPotentialVector, finsuppToEuclidean]

theorem xyDual3VertexPotentialVector_repr {B : Dual3Box}
    (p : XYDual3GraphVertex B → ℝ) :
    xyDual3VertexPotentialVector p =
      ∑ v : Dual3Vertices B, (p (some v) - p none) • EuclideanSpace.single v 1 := by
  ext v
  rw [xyDual3VertexPotentialVector_apply]
  rw [WithLp.ofLp_sum]
  rw [Finset.sum_apply v]
  calc
    p (some v) - p none =
        ∑ x : Dual3Vertices B, (if v = x then p (some x) - p none else 0) := by
          symm
          exact Fintype.sum_ite_eq v (fun x : Dual3Vertices B => p (some x) - p none)
    _ = ∑ x : Dual3Vertices B,
        (p (some x) - p none) * EuclideanSpace.single x 1 v := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : v = x
          · subst x
            simp [EuclideanSpace.single]
          · simp [EuclideanSpace.single, h]

theorem xyDual3_vertexIndicator_sum {B : Dual3Box}
    (p : XYDual3GraphVertex B → ℝ) (x : XYDual3GraphVertex B) :
    (∑ v : Dual3Vertices B, (p (some v) - p none) *
      (if x = some v then 1 else 0)) = p x - p none := by
  classical
  cases x with
  | none => simp
  | some w =>
    simp

theorem xyDual3D0_potential_eq_neg_treeCoboundary {B : Dual3Box}
    (p : XYDual3GraphVertex B → ℝ) (e : Dual3Links B) :
    (dual3ExactOneComplex B).d₀ (xyDual3VertexPotentialVector p) e =
      -RootedTreeGauge.coboundary (xyDual3RootedTree B) p e := by
  let i := xyDual3EdgeAxis e
  let lower := xyDual3EdgeLowerVertex e
  let upper := xyDual3EdgeUpperVertex e
  have hrepr := xyDual3VertexPotentialVector_repr p
  calc
    (dual3ExactOneComplex B).d₀ (xyDual3VertexPotentialVector p) e =
        (dual3ExactOneComplex B).d₀
          (∑ v : Dual3Vertices B, (p (some v) - p none) •
            EuclideanSpace.single v 1) e := by rw [hrepr]
    _ = ∑ v : Dual3Vertices B, (p (some v) - p none) *
          (dual3ExactOneComplex B).d₀ (EuclideanSpace.single v 1) e := by
          simp [map_sum, map_smul]
    _ = (-1 : ℝ) ^ i.val *
          ((p lower - p none) - (p upper - p none)) := by
          simp_rw [xyDual3D0_single_faces]
          have hUF (v : Dual3Vertices B) :
              (if e.1 = dualUpperFace v.1 (xyDual3EdgeAxis e)
                (xyDual3VertexCoord v (xyDual3EdgeAxis e))
                then (1 : ℝ) else 0) =
              (if xyDual3EdgeLowerVertex e = some v then 1 else 0) := by
            have hiff := xyDual3_upperFace_eq_linkLower v e
            by_cases h : e.1 = dualUpperFace v.1 (xyDual3EdgeAxis e)
                (xyDual3VertexCoord v (xyDual3EdgeAxis e))
            · simp [h, hiff.mp h]
            · have h' : xyDual3EdgeLowerVertex e ≠ some v :=
                fun h' => h (hiff.mpr h')
              simp [h, h']
          have hLF (v : Dual3Vertices B) :
              (if e.1 = dualLowerFace v.1 (xyDual3EdgeAxis e)
                (xyDual3VertexCoord v (xyDual3EdgeAxis e))
                then (1 : ℝ) else 0) =
              (if xyDual3EdgeUpperVertex e = some v then 1 else 0) := by
            have hiff := xyDual3_lowerFace_eq_linkUpper v e
            by_cases h : e.1 = dualLowerFace v.1 (xyDual3EdgeAxis e)
                (xyDual3VertexCoord v (xyDual3EdgeAxis e))
            · simp [h, hiff.mp h]
            · have h' : xyDual3EdgeUpperVertex e ≠ some v :=
                fun h' => h (hiff.mpr h')
              simp [h, h']
          simp_rw [hUF, hLF]
          have hsum :
              (∑ x : Dual3Vertices B, (p (some x) - p none) *
                ((-1 : ℝ) ^ (xyDual3EdgeAxis e).val *
                  ((if lower = some x then 1 else 0) -
                    (if upper = some x then 1 else 0)))) =
                (-1 : ℝ) ^ i.val *
                  ((∑ x : Dual3Vertices B, (p (some x) - p none) *
                      (if lower = some x then 1 else 0)) -
                    (∑ x : Dual3Vertices B, (p (some x) - p none) *
                      (if upper = some x then 1 else 0))) := by
            calc
              _ = ∑ x : Dual3Vertices B,
                    (((-1 : ℝ) ^ i.val * (p (some x) - p none) *
                        (if lower = some x then 1 else 0)) -
                      ((-1 : ℝ) ^ i.val * (p (some x) - p none) *
                        (if upper = some x then 1 else 0))) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    ring
              _ = _ := by
                    rw [Finset.sum_sub_distrib, mul_sub]
                    apply congrArg₂ (fun a b : ℝ => a - b)
                    · calc
                        (∑ x : Dual3Vertices B,
                            (-1 : ℝ) ^ i.val * (p (some x) - p none) *
                              (if lower = some x then 1 else 0)) =
                            ∑ x : Dual3Vertices B,
                              (-1 : ℝ) ^ i.val *
                                ((p (some x) - p none) *
                                  (if lower = some x then 1 else 0)) := by
                                  apply Finset.sum_congr rfl
                                  intro x hx
                                  ring
                        _ = (-1 : ℝ) ^ i.val *
                              ∑ x : Dual3Vertices B,
                                (p (some x) - p none) *
                                  (if lower = some x then 1 else 0) := by
                              exact (Finset.mul_sum Finset.univ
                                (fun x : Dual3Vertices B =>
                                  (p (some x) - p none) *
                                    (if lower = some x then 1 else 0))
                                ((-1 : ℝ) ^ i.val)).symm
                    · calc
                        (∑ x : Dual3Vertices B,
                            (-1 : ℝ) ^ i.val * (p (some x) - p none) *
                              (if upper = some x then 1 else 0)) =
                            ∑ x : Dual3Vertices B,
                              (-1 : ℝ) ^ i.val *
                                ((p (some x) - p none) *
                                  (if upper = some x then 1 else 0)) := by
                                  apply Finset.sum_congr rfl
                                  intro x hx
                                  ring
                        _ = (-1 : ℝ) ^ i.val *
                              ∑ x : Dual3Vertices B,
                                (p (some x) - p none) *
                                  (if upper = some x then 1 else 0) := by
                              exact (Finset.mul_sum Finset.univ
                                (fun x : Dual3Vertices B =>
                                  (p (some x) - p none) *
                                    (if upper = some x then 1 else 0))
                                ((-1 : ℝ) ^ i.val)).symm
          have hsumL :
              (∑ x : Dual3Vertices B, (p (some x) - p none) *
                (if lower = some x then 1 else 0)) = p lower - p none := by
            simpa [eq_comm] using xyDual3_vertexIndicator_sum p lower
          have hsumU :
              (∑ x : Dual3Vertices B, (p (some x) - p none) *
                (if upper = some x then 1 else 0)) = p upper - p none := by
            simpa [eq_comm] using xyDual3_vertexIndicator_sum p upper
          rw [hsum, hsumL, hsumU]
    _ = -RootedTreeGauge.coboundary (xyDual3RootedTree B) p e := by
          have hCob : RootedTreeGauge.coboundary (xyDual3RootedTree B) p e =
              (if Even i.val then p upper - p lower else p lower - p upper) := by
            by_cases he : Even (xyDual3EdgeAxis e).val <;>
              simp [RootedTreeGauge.coboundary, xyDual3RootedTree,
                xyDual3GraphSource, xyDual3GraphTarget, lower, upper, i, he]
          rw [hCob]
          have hpow : (-1 : ℝ) ^ i.val =
              if Even i.val then 1 else -1 := by
            by_cases hEven : Even i.val
            · rw [hEven.neg_one_pow]
              simp [hEven]
            · have hOdd : Odd i.val := Nat.not_even_iff_odd.mp hEven
              rw [hOdd.neg_one_pow]
              simp [hEven]
          rw [hpow]
          split_ifs <;> ring

theorem xyDual3PoissonMatrix_posSemidef {B : Dual3Box} :
    (xyDual3PoissonMatrix (B := B)).PosSemidef := by
  apply matrixOfLinearMap_posSemidef
  · intro x y
    exact LinearMap.isSymmetric_adjoint_comp_self
      (dual3ExactOneComplex B).d₁ x y
  · intro x
    rw [real_inner_comm]
    exact formLaplacian_inner_nonneg (dual3ExactOneComplex B) x

theorem xyDual3PoissonMatrix_mulVec {B : Dual3Box}
    (x : EuclideanSpace ℝ (Dual3Links B)) :
    (xyDual3PoissonMatrix (B := B)).mulVec x.ofLp =
      (formLaplacian (dual3ExactOneComplex B) x).ofLp :=
  matrixOfLinearMap_mulVec _ _

theorem xyDual3PoissonMatrix_kernel_range {B : Dual3Box}
    (x : Dual3Links B → ℝ) :
    (xyDual3PoissonMatrix (B := B)).mulVec x = 0 ↔
      ∃ u : EuclideanSpace ℝ (Dual3Vertices B),
        (dual3ExactOneComplex B).d₀ u = WithLp.toLp 2 x := by
  rw [xyDual3PoissonMatrix_mulVec]
  change (formLaplacian (dual3ExactOneComplex B) (WithLp.toLp 2 x)).ofLp = 0 ↔ _
  rw [WithLp.ofLp_eq_zero]
  constructor
  · intro h
    have hker : WithLp.toLp 2 x ∈
        (formLaplacian (dual3ExactOneComplex B)).ker :=
      LinearMap.mem_ker.mpr h
    rw [formLaplacian, LinearMap.ker_adjoint_comp_self] at hker
    exact LinearMap.mem_range.mp ((dual3ExactOneComplex B).exactOne hker)
  · rintro ⟨u, hu⟩
    apply LinearMap.mem_ker.mpr
    have hx : WithLp.toLp 2 x = (dual3ExactOneComplex B).d₀ u := hu.symm
    rw [formLaplacian, hx]
    change (dual3ExactOneComplex B).d₁.adjoint
      ((dual3ExactOneComplex B).d₁ ((dual3ExactOneComplex B).d₀ u)) = 0
    have hd : (dual3ExactOneComplex B).d₁
        ((dual3ExactOneComplex B).d₀ u) = 0 := by
      have hcomp := congrArg (fun f => f u) (dual3ExactOneComplex B).complex
      simpa [LinearMap.comp_apply] using hcomp
    rw [hd]
    simp


noncomputable def xyDual3VertexPotentialOfVector {B : Dual3Box}
    (u : EuclideanSpace ℝ (Dual3Vertices B)) : XYDual3GraphVertex B → ℝ
  | none => 0
  | some v => u v

theorem xyDual3VertexPotentialOfVector_eq_vector {B : Dual3Box}
    (u : EuclideanSpace ℝ (Dual3Vertices B)) :
    xyDual3VertexPotentialVector (xyDual3VertexPotentialOfVector u) = u := by
  ext v
  simp [xyDual3VertexPotentialVector_apply, xyDual3VertexPotentialOfVector]

theorem xyDual3PoissonMatrix_kernel_gradient {B : Dual3Box}
    (x : Dual3Links B → ℝ) :
    (xyDual3PoissonMatrix (B := B)).mulVec x = 0 ↔
      ∃ p : XYDual3GraphVertex B → ℝ,
        ∀ e, RootedTreeGauge.coboundary (xyDual3RootedTree B) p e = x e := by
  rw [xyDual3PoissonMatrix_kernel_range]
  constructor
  · rintro ⟨u, hu⟩
    let q := xyDual3VertexPotentialOfVector u
    have hq : xyDual3VertexPotentialVector q = u := by
      dsimp [q]
      exact xyDual3VertexPotentialOfVector_eq_vector u
    refine ⟨fun v => -q v, ?_⟩
    intro e
    have he := congrArg (fun z : EuclideanSpace ℝ (Dual3Links B) => z e) hu
    change (dual3ExactOneComplex B).d₀ u e = x e at he
    rw [← hq] at he
    rw [xyDual3D0_potential_eq_neg_treeCoboundary] at he
    simp only [RootedTreeGauge.coboundary] at he ⊢
    linarith
  · rintro ⟨p, hp⟩
    refine ⟨-xyDual3VertexPotentialVector p, ?_⟩
    ext e
    have h := xyDual3D0_potential_eq_neg_treeCoboundary p e
    change (dual3ExactOneComplex B).d₀
      (xyDual3VertexPotentialVector p) e =
      -(RootedTreeGauge.coboundary (xyDual3RootedTree B) p e) at h
    rw [map_neg]
    change -((dual3ExactOneComplex B).d₀
      (xyDual3VertexPotentialVector p) e) = x e
    rw [h, hp e]
    simp

noncomputable def xyDual3FinitePoissonModel {B : Dual3Box} :
    FinitePoissonModel (xyDual3RootedTree B) where
  K := xyDual3PoissonMatrix
  K_posSemidef := xyDual3PoissonMatrix_posSemidef
  K_kernel_iff_gradient := xyDual3PoissonMatrix_kernel_gradient


/-- The integer primal plaquette chain corresponding to a dual integer
one-form. Coefficients are transported by the cubical star, which is a
coefficient preserving bijection on the degree-two/degree-one carriers. -/
noncomputable def xyDual3IntegerPlaquetteChain {B : Dual3Box}
    (a : Dual3Links B → ℤ) : Chain 3 B :=
  Finsupp.equivFunOnFinite.symm (fun c =>
    if hc : cellDegree c = 2 then
      a ⟨primalDualCellEquiv c, by
        have h := dual3StarComplementaryDegree c
        rw [hc] at h
        change dualCellDegree (primalDualCellEquiv c) = 1
        omega⟩
    else 0)

theorem xyDual3IntegerPlaquetteChain_homogeneous {B : Dual3Box}
    (a : Dual3Links B → ℤ) :
    homogeneousSupport (xyDual3IntegerPlaquetteChain a) 2 := by
  intro c hc
  have hval : xyDual3IntegerPlaquetteChain a c ≠ 0 :=
    Finsupp.mem_support_iff.mp hc
  simp only [xyDual3IntegerPlaquetteChain,
    Finsupp.equivFunOnFinite_symm_apply_apply] at hval
  split_ifs at hval with h
  · exact h
  · simp at hval

/-- The Euclidean dual link vector whose integer coordinates are transported
from a by the 3D star. -/
noncomputable def xyDual3IntegerLinkVector {B : Dual3Box}
    (a : Dual3Links B → ℤ) : EuclideanSpace ℝ (Dual3Links B) :=
  finsuppToEuclidean (dual3CompressSubtype dual3LinksEmbedding
    (starMap (castIntegerChain (xyDual3IntegerPlaquetteChain a))))

theorem xyDual3IntegerLinkVector_embed {B : Dual3Box}
    (a : Dual3Links B → ℤ) :
    dual3LinksToChain (xyDual3IntegerLinkVector a) =
      starMap (castIntegerChain (xyDual3IntegerPlaquetteChain a)) := by
  have hq : realHomogeneousSupport
      (castIntegerChain (xyDual3IntegerPlaquetteChain a)) 2 := by
    intro c hc
    exact xyDual3IntegerPlaquetteChain_homogeneous a c
      (Finsupp.support_mapRange hc)
  have hs : dualRealHomogeneousSupport
      (starMap (castIntegerChain (xyDual3IntegerPlaquetteChain a))) 1 := by
    simpa using dual3StarMap_homogeneousSupport
      (castIntegerChain (xyDual3IntegerPlaquetteChain a)) 2 hq
  have hsupport :
      ((starMap (castIntegerChain (xyDual3IntegerPlaquetteChain a))).support :
        Set (DualCell 3 B)) ⊆ Set.range dual3LinksEmbedding := by
    intro c hc
    exact ⟨⟨c, hs c hc⟩, rfl⟩
  dsimp [dual3LinksToChain, xyDual3IntegerLinkVector]
  rw [euclideanToFinsupp_finsuppToEuclidean]
  exact dual3EmbedCompress_eq_self_of_support dual3LinksEmbedding _ hsupport

/-- The coefficient function of the integer star vector recovers the input
dual one-form exactly. -/
theorem xyDual3IntegerLinkVector_apply {B : Dual3Box}
    (a : Dual3Links B → ℤ) (e : Dual3Links B) :
    xyDual3IntegerLinkVector a e = (a e : ℝ) := by
  have h := congrArg (fun q : DualRealChain 3 B => q (dual3LinksEmbedding e))
    (xyDual3IntegerLinkVector_embed a)
  have hvec : xyDual3IntegerLinkVector a e =
      starMap (castIntegerChain (xyDual3IntegerPlaquetteChain a))
        (dual3LinksEmbedding e) := by
    change dual3EmbedSubtype dual3LinksEmbedding
        (euclideanToFinsupp (xyDual3IntegerLinkVector a))
        (dual3LinksEmbedding e) = _ at h
    rw [dual3EmbedSubtype_apply_at_image] at h
    simpa [euclideanToFinsupp_apply] using h
  rw [hvec]
  change ((xyDual3IntegerPlaquetteChain a)
    (primalDualCellEquiv.symm (dual3LinksEmbedding e)) : ℝ) = _
  have hdeg : cellDegree (primalDualCellEquiv.symm e.1) = 2 := by
    have h := dual3StarComplementaryDegree
      (primalDualCellEquiv.symm e.1)
    simp only [Equiv.apply_symm_apply] at h
    have he : dualCellDegree e.1 = 1 := e.2
    rw [he] at h
    omega
  simp only [xyDual3IntegerPlaquetteChain,
    Finsupp.equivFunOnFinite_symm_apply_apply]
  simp [hdeg, dual3LinksEmbedding]

/-- The dual of an arbitrary integer primal plaquette chain, read on the dual
link carrier. -/
def xyDual3IntegerStarLink {B : Dual3Box} (p : Chain 3 B)
    (e : Dual3Links B) : ℤ :=
  p (primalDualCellEquiv.symm e.1)

theorem xyDual3IntegerPlaquetteChain_star {B : Dual3Box}
    (p : Chain 3 B) (hp : homogeneousSupport p 2) :
    xyDual3IntegerPlaquetteChain (xyDual3IntegerStarLink p) = p := by
  classical
  ext c
  by_cases hc : cellDegree c = 2
  · simp [xyDual3IntegerPlaquetteChain, xyDual3IntegerStarLink,
      Finsupp.equivFunOnFinite_symm_apply_apply, hc]
  · have hp0 : p c = 0 := by
      by_contra hne
      exact hc (hp c (Finsupp.mem_support_iff.mpr hne))
    simp [xyDual3IntegerPlaquetteChain,
      Finsupp.equivFunOnFinite_symm_apply_apply, hc, hp0]

/-- Every dual integer one-form defines an integer primal plaquette chain. -/
theorem xyDual3IntegerStarLink_chain {B : Dual3Box}
    (a : Dual3Links B → ℤ) :
    xyDual3IntegerStarLink (xyDual3IntegerPlaquetteChain a) = a := by
  classical
  funext e
  have hdeg : cellDegree (primalDualCellEquiv.symm e.1) = 2 := by
    have h := dual3StarComplementaryDegree (primalDualCellEquiv.symm e.1)
    simp only [Equiv.apply_symm_apply] at h
    have he : dualCellDegree e.1 = 1 := e.2
    omega
  simp [xyDual3IntegerStarLink, xyDual3IntegerPlaquetteChain,
    Finsupp.equivFunOnFinite_symm_apply_apply, hdeg]

/-- The dual curl of an integer dual one-form, represented as primal bond
coefficients. -/
noncomputable def xyDual3IntegerCurlModes {B : Dual3Box}
    (a : Dual3Links B → ℤ) : XYBondModes (B := B) :=
  fun b => boundary (xyDual3IntegerPlaquetteChain a) b.1

theorem xyDual3IntegerPlaquetteChain_boundary_homogeneous {B : Dual3Box}
    (a : Dual3Links B → ℤ) :
    homogeneousSupport (boundary (xyDual3IntegerPlaquetteChain a)) 1 := by
  exact xyIntegerBoundary_homogeneousSupport
    (xyDual3IntegerPlaquetteChain a) 2 (by omega)
    (xyDual3IntegerPlaquetteChain_homogeneous a)

theorem xyDual3IntegerCurlModes_chain {B : Dual3Box}
    (a : Dual3Links B → ℤ) :
    xyBondModeChain (xyDual3IntegerCurlModes a) =
      boundary (xyDual3IntegerPlaquetteChain a) := by
  exact xyBondModeChain_restrict _
    (xyDual3IntegerPlaquetteChain_boundary_homogeneous a)

theorem xyDual3IntegerCurlModes_cycle {B : Dual3Box}
    (a : Dual3Links B → ℤ) :
    xyBondModeDivergence (xyDual3IntegerCurlModes a) = 0 := by
  have hzero : boundary (boundary (xyDual3IntegerPlaquetteChain a)) = 0 := by
    have h := congrArg
      (fun T : Chain 3 B →ₗ[ℤ] Chain 3 B => T (xyDual3IntegerPlaquetteChain a))
      (boundary_square_zero (d := 3) (B := B))
    simpa [LinearMap.comp_apply] using h
  funext x
  change boundary (xyBondModeChain (xyDual3IntegerCurlModes a)) x.1 = 0
  rw [xyDual3IntegerCurlModes_chain]
  exact congrArg (fun q : Chain 3 B => q x.1) hzero

theorem xyBondModeChain_apply {B : Dual3Box}
    (m : XYBondModes (B := B)) (b : XYBonds B) :
    xyBondModeChain m b.1 = m b := by
  classical
  have hsum : (∑ b' : XYBonds B, (m b') • basisChain b'.1) b.1 = m b := by
    rw [Finsupp.finsetSum_apply]
    calc
      _ = ((m b) • basisChain b.1) b.1 := by
        apply Fintype.sum_eq_single b
        intro b' hne
        have hcell : b'.1 ≠ b.1 := fun heq => hne (Subtype.ext heq)
        simp [basisChain, hcell]
      _ = m b := by simp [basisChain]
  simpa [xyBondModeChain] using hsum

theorem xyBondModeChain_injective {B : Dual3Box} :
    Function.Injective (xyBondModeChain (B := B)) := by
  intro m n h
  funext b
  have hb := congrArg (fun q : Chain 3 B => q b.1) h
  simpa only [xyBondModeChain_apply] using hb

/-- The curl produces an XY cycle. This map forgets the exact integer gauge
directions, which the tree gauge fixes in the next equivalence. -/
noncomputable def xyDual3CycleOfIntegerLink {B : Dual3Box}
    (a : Dual3Links B → ℤ) : XYEndpointCycleModes (B := B) :=
  ⟨xyDual3IntegerCurlModes a, xyDual3IntegerCurlModes_cycle a⟩


noncomputable def xyDual3CycleFilling {B : Dual3Box}
    (c : XYEndpointCycleModes (B := B)) :
    {p : Chain 3 B // homogeneousSupport p 2 ∧
      boundary p = xyBondModeChain c.1} := by
  let h := xyBondCycle_has_plaquetteFilling c.1 c.2
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- The chosen filling indeed has the source cycle as its boundary. -/
theorem xyDual3CycleFilling_spec {B : Dual3Box}
    (c : XYEndpointCycleModes (B := B)) :
    homogeneousSupport (xyDual3CycleFilling c).1 2 ∧
      boundary (xyDual3CycleFilling c).1 = xyBondModeChain c.1 :=
  (xyDual3CycleFilling c).property

/-- A cycle is represented by its plaquette filling, Hodge-starred to dual
links and put in the chosen tree gauge. -/
noncomputable def xyDual3TreeGaugeOfCycle {B : Dual3Box}
    (c : XYEndpointCycleModes (B := B)) :
    {a : Dual3Links B → ℤ //
      RootedTreeGauge.InTreeGauge (xyDual3RootedTree B) a} := by
  let raw := xyDual3IntegerStarLink (xyDual3CycleFilling c).1
  exact ⟨RootedTreeGauge.normalize (xyDual3RootedTree B) raw,
    RootedTreeGauge.normalize_mem (xyDual3RootedTree B)⟩

/-- The integer curl agrees with the grounded dual complex's real dual exterior derivative after
transporting coefficients through the primal/dual star. -/
theorem xyDual3IntegerCurl_intertwining {B : Dual3Box}
    (a : Dual3Links B → ℤ) :
    dual3PlaquettesToChain (dual3D₁ (xyDual3IntegerLinkVector a)) =
      starMap (castIntegerChain
        (boundary (xyDual3IntegerPlaquetteChain a))) := by
  have hq : realHomogeneousSupport
      (castIntegerChain (xyDual3IntegerPlaquetteChain a)) 2 := by
    intro c hc
    exact xyDual3IntegerPlaquetteChain_homogeneous a c
      (Finsupp.support_mapRange hc)
  have hcast : castIntegerChain
      (boundary (xyDual3IntegerPlaquetteChain a)) =
      realBoundary (castIntegerChain (xyDual3IntegerPlaquetteChain a)) := by
    simpa [realBoundary] using
      (realifyLinearMap_cast boundary (xyDual3IntegerPlaquetteChain a)).symm
  rw [dual3D₁_embed_eq_derivative,
    xyDual3IntegerLinkVector_embed,
    primalDualStar_incidence_identity, ← hcast]

/-- Normalizing an integer dual link field subtracts a tree coboundary. Under
the grounded dual complex's sign convention that is addition of its `d₀` image. -/
theorem xyDual3IntegerLinkVector_normalize {B : Dual3Box}
    (a : Dual3Links B → ℤ) :
    xyDual3IntegerLinkVector (RootedTreeGauge.normalize
      (xyDual3RootedTree B) a) =
        xyDual3IntegerLinkVector a +
      dual3D₀ (xyDual3VertexPotentialVector
            (fun v => ((RootedTreeGauge.treePotential (R := ℤ)
              (xyDual3RootedTree B) a v : ℤ) : ℝ))) := by
  ext e
  simp only [xyDual3IntegerLinkVector_apply, PiLp.add_apply]
  have hd0 := xyDual3D0_potential_eq_neg_treeCoboundary
    (fun v => ((RootedTreeGauge.treePotential (R := ℤ)
      (xyDual3RootedTree B) a v : ℤ) : ℝ)) e
  change dual3D₀ (xyDual3VertexPotentialVector (fun v =>
    ((RootedTreeGauge.treePotential (R := ℤ)
      (xyDual3RootedTree B) a v : ℤ) : ℝ))) e = _ at hd0
  rw [hd0]
  simp [RootedTreeGauge.normalize, RootedTreeGauge.coboundary,
    Int.cast_sub]
  ring

/-- The primal boundary of the integer plaquette chain is unchanged by tree
normalization. This is the discrete statement that exact 3-cell boundaries
are precisely the dual integer gauge directions on the finite box. -/
theorem xyDual3IntegerPlaquetteChain_boundary_normalize {B : Dual3Box}
    (a : Dual3Links B → ℤ) :
    boundary (xyDual3IntegerPlaquetteChain
      (RootedTreeGauge.normalize (xyDual3RootedTree B) a)) =
    boundary (xyDual3IntegerPlaquetteChain a) := by
  have hvec := xyDual3IntegerLinkVector_normalize a
  have hd₁ := congrArg dual3D₁ hvec
  have hD0 : dual3D₁ (dual3D₀ (xyDual3VertexPotentialVector
      (fun v => ((RootedTreeGauge.treePotential (R := ℤ)
        (xyDual3RootedTree B) a v : ℤ) : ℝ)))) = 0 := by
    have h := congrArg (fun L : EuclideanSpace ℝ (Dual3Vertices B) →ₗ[ℝ]
        EuclideanSpace ℝ (Dual3Plaquettes B) =>
          L (xyDual3VertexPotentialVector (fun v =>
            ((RootedTreeGauge.treePotential (R := ℤ)
              (xyDual3RootedTree B) a v : ℤ) : ℝ))))
      (dual3D₁_comp_D₀_zero (B := B))
    simpa [LinearMap.comp_apply] using h
  rw [map_add, hD0, add_zero] at hd₁
  have hstar : starMap (castIntegerChain
        (boundary (xyDual3IntegerPlaquetteChain
          (RootedTreeGauge.normalize (xyDual3RootedTree B) a)))) =
      starMap (castIntegerChain
        (boundary (xyDual3IntegerPlaquetteChain a))) := by
    calc
      _ = dual3PlaquettesToChain
          (dual3D₁ (xyDual3IntegerLinkVector
            (RootedTreeGauge.normalize (xyDual3RootedTree B) a))) :=
        (xyDual3IntegerCurl_intertwining
          (RootedTreeGauge.normalize (xyDual3RootedTree B) a)).symm
      _ = dual3PlaquettesToChain (dual3D₁ (xyDual3IntegerLinkVector a)) :=
        congrArg dual3PlaquettesToChain hd₁
      _ = _ := xyDual3IntegerCurl_intertwining a
  have hcast : castIntegerChain
      (boundary (xyDual3IntegerPlaquetteChain
        (RootedTreeGauge.normalize (xyDual3RootedTree B) a))) =
      castIntegerChain (boundary (xyDual3IntegerPlaquetteChain a)) := by
    have h := congrArg starMapInverse hstar
    simpa only [starMapInverse_starMap] using h
  apply Finsupp.ext
  intro c
  have hc := congrArg (fun q : RealChain 3 B => q c) hcast
  exact Int.cast_injective hc

/-- A dual integer one-form with zero curl is an integer gauge gradient; its
tree-normalized representative is therefore zero. The real exact-one theorem
and integer tree integration together give the integral conclusion. -/
theorem xyDual3IntegerCurl_zero_normalize {B : Dual3Box}
    (a : Dual3Links B → ℤ) (hcurl : xyDual3IntegerCurlModes a = 0) :
    RootedTreeGauge.normalize (xyDual3RootedTree B) a = 0 := by
  let T := xyDual3RootedTree B
  let b := RootedTreeGauge.normalize T a
  have hcycleA : boundary (xyDual3IntegerPlaquetteChain a) = 0 := by
    have h := congrArg xyBondModeChain hcurl
    rw [xyDual3IntegerCurlModes_chain] at h
    simpa [xyBondModeChain] using h
  have hcycleB : boundary (xyDual3IntegerPlaquetteChain b) = 0 := by
    rw [show b = RootedTreeGauge.normalize T a from rfl,
      xyDual3IntegerPlaquetteChain_boundary_normalize]
    exact hcycleA
  have hst := xyDual3IntegerCurl_intertwining b
  rw [hcycleB] at hst
  have hcastzero : castIntegerChain (0 : Chain 3 B) = 0 := by
    ext c
    simp [castIntegerChain]
  rw [hcastzero, map_zero] at hst
  have hd₁ : dual3D₁ (xyDual3IntegerLinkVector b) = 0 := by
    apply dual3PlaquettesToChain_injective
    simpa using hst
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (dual3D₀_exactOne
    (xyDual3IntegerLinkVector b) hd₁)
  let p : XYDual3GraphVertex B → ℝ := fun x =>
    match x with
    | none => 0
    | some w => v w
  have hpv : xyDual3VertexPotentialVector p = v := by
    ext w
    simp [p, xyDual3VertexPotentialVector_apply]
  have htree : ∀ x : {x : XYDual3GraphVertex B // x ≠ T.root},
      RootedTreeGauge.coboundary T p (T.treeEdge x) = 0 := by
    intro x
    have hb : b (T.treeEdge x) = 0 := by
      exact RootedTreeGauge.normalize_mem T x
    have hcoord := congrArg
      (fun w : EuclideanSpace ℝ (Dual3Links B) => w (T.treeEdge x)) hv
    rw [← hpv] at hcoord
    have hd0 := xyDual3D0_potential_eq_neg_treeCoboundary p (T.treeEdge x)
    change dual3D₀ (xyDual3VertexPotentialVector p) (T.treeEdge x) = _ at hd0
    rw [hd0] at hcoord
    have hvec : xyDual3IntegerLinkVector b (T.treeEdge x) = 0 := by
      rw [xyDual3IntegerLinkVector_apply, hb]
      simp
    rw [hvec] at hcoord
    linarith
  have hconstant := T.potential_constant_of_tree_zero p htree
  have hpzero : p = 0 := by
    funext x
    rw [hconstant x]
    have hroot : T.root = none := rfl
    rw [hroot]
    simp [p]
  have hpvzero : xyDual3VertexPotentialVector p = 0 := by
    rw [hpzero]
    ext w
    simp [xyDual3VertexPotentialVector_apply]
  have hvzero : v = 0 := by
    calc
      v = xyDual3VertexPotentialVector p := hpv.symm
      _ = 0 := hpvzero
  have hbzero : xyDual3IntegerLinkVector b = 0 := by
    calc
      _ = dual3D₀ v := hv.symm
      _ = 0 := by rw [hvzero]; simp
  funext e
  have he := congrArg (fun w : EuclideanSpace ℝ (Dual3Links B) => w e) hbzero
  rw [xyDual3IntegerLinkVector_apply] at he
  change b e = 0
  exact Int.cast_injective (α := ℝ) (by simpa using he)

/-- Two integer plaquette fillings of one cycle give the same tree-gauge dual
one-form. Their difference has zero dual curl; the grounded dual complex exactness makes that
integer field a gauge gradient, and `normalize_unique` removes it. -/
private theorem xyDual3GaugeEquivalent_symm {B : Dual3Box}
    (T : RootedTreeGauge (XYDual3GraphVertex B) (XYDual3GraphEdge B))
    {a b : XYDual3GraphEdge B → ℤ}
    (hab : RootedTreeGauge.GaugeEquivalent T a b) :
    RootedTreeGauge.GaugeEquivalent T b a := by
  rcases hab with ⟨p, hp, hfield⟩
  refine ⟨-p, by simp [hp], ?_⟩
  intro e
  rw [hfield e]
  simp [RootedTreeGauge.coboundary]
  ring

private theorem xyDual3GaugeEquivalent_trans {B : Dual3Box}
    (T : RootedTreeGauge (XYDual3GraphVertex B) (XYDual3GraphEdge B))
    {a b c : XYDual3GraphEdge B → ℤ}
    (hab : RootedTreeGauge.GaugeEquivalent T a b)
    (hbc : RootedTreeGauge.GaugeEquivalent T b c) :
    RootedTreeGauge.GaugeEquivalent T a c := by
  rcases hab with ⟨p, hp, hpfield⟩
  rcases hbc with ⟨q, hq, hqfield⟩
  refine ⟨p + q, by simp [hp, hq], ?_⟩
  intro e
  rw [hqfield, hpfield]
  simp [RootedTreeGauge.coboundary]
  abel

theorem xyDual3TreeGauge_filling_independent {B : Dual3Box}
    (p q : Chain 3 B) (hp : homogeneousSupport p 2)
    (hq : homogeneousSupport q 2)
    (hbd : boundary p = boundary q) :
    RootedTreeGauge.normalize (xyDual3RootedTree B)
        (xyDual3IntegerStarLink p) =
      RootedTreeGauge.normalize (xyDual3RootedTree B)
        (xyDual3IntegerStarLink q) := by
  let T := xyDual3RootedTree B
  let a := xyDual3IntegerStarLink p
  let b := xyDual3IntegerStarLink q
  have hdiffdeg : homogeneousSupport (p - q) 2 := by
    simpa [sub_eq_add_neg] using homogeneousSupport_add hp
      (homogeneousSupport_smul (-1 : ℤ) hq)
  have hchain : xyDual3IntegerPlaquetteChain (a - b) = p - q := by
    have hstar := xyDual3IntegerPlaquetteChain_star (p - q) hdiffdeg
    have hlink : xyDual3IntegerStarLink (p - q) = a - b := by
      funext e
      simp [a, b, xyDual3IntegerStarLink]
    simpa [hlink] using hstar
  have hcurl : xyDual3IntegerCurlModes (a - b) = 0 := by
    apply xyBondModeChain_injective
    rw [xyDual3IntegerCurlModes_chain, hchain, map_sub, hbd, sub_self]
    simp [xyBondModeChain]
  have hnormzero := xyDual3IntegerCurl_zero_normalize (a - b) hcurl
  have hgrad : ∀ e, a e - b e =
      RootedTreeGauge.coboundary T
        (RootedTreeGauge.treePotential T (a - b)) e := by
    intro e
    have he := congrFun hnormzero e
    have he' := sub_eq_zero.mp he
    simpa [Pi.sub_apply] using he'
  have hab : RootedTreeGauge.GaugeEquivalent T a b := by
    refine ⟨RootedTreeGauge.treePotential T (a - b),
      RootedTreeGauge.treePotential_root T (a - b), ?_⟩
    intro e
    have he := hgrad e
    dsimp [a, b] at he ⊢
    omega
  have hnA := RootedTreeGauge.normalize_gaugeEquivalent T a
  have hnB := RootedTreeGauge.normalize_gaugeEquivalent T b
  have hnormalized := xyDual3GaugeEquivalent_trans T
    (xyDual3GaugeEquivalent_trans T (xyDual3GaugeEquivalent_symm T hnA) hab) hnB
  exact RootedTreeGauge.normalize_unique T
    (RootedTreeGauge.normalize_mem T) (RootedTreeGauge.normalize_mem T) hnormalized


/-- Sending a cycle to its normalized filling and back recovers the original
cycle, using the unit-box cycle-filling theorem. -/
theorem xyDual3CycleOfTreeGaugeOfCycle {B : Dual3Box}
    (c : XYEndpointCycleModes (B := B)) :
    xyDual3CycleOfIntegerLink (xyDual3TreeGaugeOfCycle c).1 = c := by
  apply Subtype.ext
  change xyDual3IntegerCurlModes (xyDual3TreeGaugeOfCycle c).1 = c.1
  apply xyBondModeChain_injective
  rw [xyDual3IntegerCurlModes_chain]
  dsimp [xyDual3TreeGaugeOfCycle]
  rw [xyDual3IntegerPlaquetteChain_boundary_normalize]
  rw [xyDual3IntegerPlaquetteChain_star
    (xyDual3CycleFilling c).1 (xyDual3CycleFilling_spec c).1]
  exact (xyDual3CycleFilling_spec c).2


/-- The tree-gauge parameterization and the XY cycle set are inverse in both
directions, so their countable Gaussian sums may be reindexed without a
multiplicity factor. -/
noncomputable def xyDual3CycleTreeGaugeEquiv {B : Dual3Box} :
    XYEndpointCycleModes (B := B) ≃
      {a : Dual3Links B → ℤ //
        RootedTreeGauge.InTreeGauge (xyDual3RootedTree B) a} where
  toFun := xyDual3TreeGaugeOfCycle
  invFun := fun a => xyDual3CycleOfIntegerLink a.1
  left_inv := xyDual3CycleOfTreeGaugeOfCycle
  right_inv := by
    intro a
    apply Subtype.ext
    change RootedTreeGauge.normalize (xyDual3RootedTree B)
        (xyDual3IntegerStarLink
          (xyDual3CycleFilling (xyDual3CycleOfIntegerLink a.1)).1) = a.1
    have hbd : boundary (xyDual3CycleFilling
        (xyDual3CycleOfIntegerLink a.1)).1 =
        boundary (xyDual3IntegerPlaquetteChain a.1) := by
      calc
        _ = xyBondModeChain (xyDual3CycleOfIntegerLink a.1).1 :=
          (xyDual3CycleFilling_spec
            (xyDual3CycleOfIntegerLink a.1)).2
        _ = boundary (xyDual3IntegerPlaquetteChain a.1) := by
          change xyBondModeChain (xyDual3IntegerCurlModes a.1) = _
          exact xyDual3IntegerCurlModes_chain a.1
    have hfi := xyDual3TreeGauge_filling_independent
      (xyDual3CycleFilling (xyDual3CycleOfIntegerLink a.1)).1
      (xyDual3IntegerPlaquetteChain a.1)
      (xyDual3CycleFilling_spec (xyDual3CycleOfIntegerLink a.1)).1
      (xyDual3IntegerPlaquetteChain_homogeneous a.1) hbd
    have hna : RootedTreeGauge.normalize (xyDual3RootedTree B) a.1 = a.1 := by
      exact (RootedTreeGauge.normalize_unique (xyDual3RootedTree B)
        a.2 (RootedTreeGauge.normalize_mem (xyDual3RootedTree B))
        (RootedTreeGauge.normalize_gaugeEquivalent (xyDual3RootedTree B) a.1)).symm
    calc
      _ = RootedTreeGauge.normalize (xyDual3RootedTree B)
          (xyDual3IntegerStarLink (xyDual3IntegerPlaquetteChain a.1)) := hfi
      _ = RootedTreeGauge.normalize (xyDual3RootedTree B) a.1 := by
        rw [xyDual3IntegerStarLink_chain]
      _ = a.1 := hna


noncomputable def xyDual3CycleGaussianWeight {B : Dual3Box}
    (β : ℝ) (path : XYBondModes (B := B))
    (c : XYEndpointCycleModes (B := B)) : ℝ :=
  ∏ b : XYBonds B,
    Real.exp (-(((c.1 b + path b : ℤ) : ℝ) ^ 2) / (2 * β))

/-- Reindex the XY cycle Gaussian by the unique integer dual one-form in tree
gauge. The cycle/filling quotient has multiplicity one. -/
theorem xyDual3CycleGaussianWeight_reindex {B : Dual3Box}
    (β : ℝ) (path : XYBondModes (B := B)) :
    (∑' c : XYEndpointCycleModes (B := B),
      xyDual3CycleGaussianWeight β path c) =
    (∑' a : {a : Dual3Links B → ℤ //
        RootedTreeGauge.InTreeGauge (xyDual3RootedTree B) a},
      xyDual3CycleGaussianWeight β path
        (xyDual3CycleOfIntegerLink a.1)) := by
  let e := xyDual3CycleTreeGaugeEquiv (B := B)
  calc
    _ = ∑' c : XYEndpointCycleModes (B := B),
        xyDual3CycleGaussianWeight β path (e.symm (e c)) := by
      apply tsum_congr
      intro c
      simp
    _ = ∑' a : {a : Dual3Links B → ℤ //
        RootedTreeGauge.InTreeGauge (xyDual3RootedTree B) a},
        xyDual3CycleGaussianWeight β path (e.symm a) :=
      e.tsum_eq (fun a => xyDual3CycleGaussianWeight β path (e.symm a))
    _ = _ := by
      apply tsum_congr
      intro a
      rfl


theorem xyShiftedCycleGaussianSum_eq_cycleTsum {B : Box 3}
    (β : ℝ) (x y : XYSites B) :
    xyShiftedCycleGaussianSum β x y =
      ∑' c : XYEndpointCycleModes (B := B),
        xyDual3CycleGaussianWeight β (xyEndpointPathModes x y) c := by
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

/-- Primal bonds are in bijection with complementary dual plaquettes. -/
def xyDual3BondPlaquetteEquiv {B : Dual3Box} :
    XYBonds B ≃ Dual3Plaquettes B where
  toFun b := ⟨primalDualCellEquiv b.1, by
    have h := dual3StarComplementaryDegree b.1
    rw [b.2] at h
    omega⟩
  invFun e := ⟨primalDualCellEquiv.symm e.1, by
    have h := dual3StarComplementaryDegree
      (primalDualCellEquiv.symm e.1)
    simp only [Equiv.apply_symm_apply] at h
    rw [e.2] at h
    omega⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv e := by apply Subtype.ext; simp

/-- Compress the star of a primal bond field to the grounded dual complex's finite dual plaquette
carrier. -/
noncomputable def xyDual3StarBondVector {B : Dual3Box}
    (q : RealChain 3 B) : EuclideanSpace ℝ (Dual3Plaquettes B) :=
  finsuppToEuclidean (dual3CompressSubtype dual3PlaquettesEmbedding
    (starMap q))

theorem xyDual3StarBondVector_embed {B : Dual3Box}
    (q : RealChain 3 B) (hq : realHomogeneousSupport q 1) :
    dual3PlaquettesToChain (xyDual3StarBondVector q) = starMap q := by
  have hs : dualRealHomogeneousSupport (starMap q) 2 := by
    simpa using dual3StarMap_homogeneousSupport q 1 hq
  have hsupport : ((starMap q).support : Set (DualCell 3 B)) ⊆
      Set.range dual3PlaquettesEmbedding := by
    intro c hc
    exact ⟨⟨c, hs c hc⟩, rfl⟩
  dsimp [xyDual3StarBondVector, dual3PlaquettesToChain]
  rw [euclideanToFinsupp_finsuppToEuclidean]
  exact dual3EmbedCompress_eq_self_of_support dual3PlaquettesEmbedding
    (starMap q) hsupport

theorem xyDual3StarBondVector_apply {B : Dual3Box}
    (q : RealChain 3 B) (b : XYBonds B)
    (hq : realHomogeneousSupport q 1) :
    xyDual3StarBondVector q (xyDual3BondPlaquetteEquiv b) = q b.1 := by
  have h := congrArg (fun z : DualRealChain 3 B =>
      z (dual3PlaquettesEmbedding (xyDual3BondPlaquetteEquiv b)))
    (xyDual3StarBondVector_embed q hq)
  change dual3EmbedSubtype dual3PlaquettesEmbedding
      (euclideanToFinsupp (xyDual3StarBondVector q))
      (dual3PlaquettesEmbedding (xyDual3BondPlaquetteEquiv b)) = _ at h
  rw [dual3EmbedSubtype_apply_at_image] at h
  simpa [euclideanToFinsupp_apply, starMap, xyDual3BondPlaquetteEquiv,
    dual3PlaquettesEmbedding] using h

/-- Squared bond norm of a real one-chain. -/
noncomputable def xyDual3BondEnergy {B : Dual3Box} (q : RealChain 3 B) : ℝ :=
  ∑ b : XYBonds B, q b.1 ^ 2

/-- The complementary star preserves the squared norm of a primal bond field. -/
theorem xyDual3StarBondVector_energy {B : Dual3Box}
    (q : RealChain 3 B) (hq : realHomogeneousSupport q 1) :
    inner ℝ (xyDual3StarBondVector q) (xyDual3StarBondVector q) =
      xyDual3BondEnergy q := by
  rw [PiLp.inner_apply]
  calc
    (∑ e : Dual3Plaquettes B,
        xyDual3StarBondVector q e * xyDual3StarBondVector q e) =
      ∑ b : XYBonds B,
        xyDual3StarBondVector q (xyDual3BondPlaquetteEquiv b) *
          xyDual3StarBondVector q (xyDual3BondPlaquetteEquiv b) := by
        exact (Equiv.sum_comp (xyDual3BondPlaquetteEquiv (B := B))
          (fun e : Dual3Plaquettes B =>
            xyDual3StarBondVector q e * xyDual3StarBondVector q e)).symm
    _ = xyDual3BondEnergy q := by
      simp only [xyDual3BondEnergy]
      apply Finset.sum_congr rfl
      intro b hb
      rw [xyDual3StarBondVector_apply q b hq]
      simp [pow_two]

/-- The bond Gaussian product is the exponential of the squared bond-chain
norm. -/
theorem xyDual3CycleGaussianWeight_eq_energy {B : Dual3Box}
    (β : ℝ) (path : XYBondModes (B := B))
    (c : XYEndpointCycleModes (B := B)) :
    xyDual3CycleGaussianWeight β path c =
      Real.exp (-xyDual3BondEnergy
        (castIntegerChain (xyBondModeChain (c.1 + path))) / (2 * β)) := by
  unfold xyDual3CycleGaussianWeight xyDual3BondEnergy
  rw [← Real.exp_sum]
  congr 1
  calc
    (∑ b : XYBonds B,
        -(((c.1 b + path b : ℤ) : ℝ) ^ 2) / (2 * β)) =
      (∑ b : XYBonds B, -(((c.1 b + path b : ℤ) : ℝ) ^ 2)) / (2 * β) := by
        rw [Finset.sum_div]
    _ = -(∑ b : XYBonds B,
        (((castIntegerChain (xyBondModeChain (c.1 + path))) b.1) ^ 2)) /
          (2 * β) := by
      congr 1
      simp [castIntegerChain, xyBondModeChain_apply,
        Finset.sum_neg_distrib]

/-- The endpoint path as a real dual plaquette field. -/
noncomputable def xyDual3EndpointPathVector {B : Dual3Box}
    (x y : XYSites B) : EuclideanSpace ℝ (Dual3Plaquettes B) :=
  xyDual3StarBondVector (castIntegerChain (xyEndpointPath x y))

/-- The dual plaquette field whose norm is the shifted primal bond energy. -/
noncomputable def xyDual3ShiftedDualPlaquetteVector {B : Dual3Box}
    (a : Dual3Links B → ℤ) (x y : XYSites B) :
    EuclideanSpace ℝ (Dual3Plaquettes B) :=
  dual3D₁ (xyDual3IntegerLinkVector a) + xyDual3EndpointPathVector x y

/-- The finite-volume residual energy before Poisson summation. -/
noncomputable def xyDual3ShiftedDualEnergy {B : Dual3Box}
    (a : Dual3Links B → ℤ) (x y : XYSites B) : ℝ :=
  inner ℝ (xyDual3ShiftedDualPlaquetteVector a x y)
    (xyDual3ShiftedDualPlaquetteVector a x y)

/-- The star/boundary bridge identifies the dual field with the shifted XY
bond chain. -/
theorem xyDual3ShiftedVector_eq_starBond {B : Dual3Box}
    (a : Dual3Links B → ℤ) (x y : XYSites B) :
    xyDual3ShiftedDualPlaquetteVector a x y =
      xyDual3StarBondVector
        (castIntegerChain (xyBondModeChain
          (xyDual3IntegerCurlModes a + xyEndpointPathModes x y))) := by
  have hpath : xyBondModeChain (xyEndpointPathModes x y) =
      xyEndpointPath x y := by
    exact xyBondModeChain_restrict (xyEndpointPath x y)
      (xyEndpointPath_homogeneousSupport x y)
  have hcurl := xyDual3IntegerCurl_intertwining a
  have hpathStar := xyDual3StarBondVector_embed
    (castIntegerChain (xyEndpointPath x y)) (by
      intro c hc
      exact xyEndpointPath_homogeneousSupport x y c
        (Finsupp.support_mapRange hc))
  have hchain : boundary (xyDual3IntegerPlaquetteChain a) + xyEndpointPath x y =
      xyBondModeChain (xyDual3IntegerCurlModes a + xyEndpointPathModes x y) := by
    rw [xyBondModeChain_add, xyDual3IntegerCurlModes_chain, hpath]
  have hdual : dual3PlaquettesToChain
      (xyDual3ShiftedDualPlaquetteVector a x y) =
      starMap (castIntegerChain (xyBondModeChain
        (xyDual3IntegerCurlModes a + xyEndpointPathModes x y))) := by
    change dual3PlaquettesToChain
        (dual3D₁ (xyDual3IntegerLinkVector a) +
          xyDual3StarBondVector (castIntegerChain (xyEndpointPath x y))) = _
    rw [map_add, hcurl, hpathStar]
    rw [← map_add, ← castIntegerChain_add]
    rw [← hchain]
  have hq : realHomogeneousSupport (castIntegerChain
      (xyBondModeChain (xyDual3IntegerCurlModes a + xyEndpointPathModes x y))) 1 := by
    intro c hc
    exact xyBondModeChain_homogeneousSupport
      (xyDual3IntegerCurlModes a + xyEndpointPathModes x y) c
      (Finsupp.support_mapRange hc)
  apply dual3PlaquettesToChain_injective
  rw [xyDual3StarBondVector_embed _ hq]
  exact hdual

/-- The original shifted cycle weight is the Gaussian of the dual plaquette
field, with the path orientation fixed by the unit-cube sign check. -/
theorem xyDual3CycleGaussianWeight_eq_dualEnergy {B : Dual3Box}
    (β : ℝ) (x y : XYSites B)
    (a : Dual3Links B → ℤ) :
    xyDual3CycleGaussianWeight β (xyEndpointPathModes x y)
        (xyDual3CycleOfIntegerLink a) =
      Real.exp (-xyDual3ShiftedDualEnergy a x y / (2 * β)) := by
  rw [xyDual3CycleGaussianWeight_eq_energy]
  change Real.exp (-xyDual3BondEnergy (castIntegerChain
      (xyBondModeChain (xyDual3IntegerCurlModes a + xyEndpointPathModes x y))) /
        (2 * β)) = _
  rw [xyDual3ShiftedDualEnergy, xyDual3ShiftedVector_eq_starBond]
  have hq : realHomogeneousSupport (castIntegerChain
      (xyBondModeChain (xyDual3IntegerCurlModes a + xyEndpointPathModes x y))) 1 := by
    intro c hc
    exact xyBondModeChain_homogeneousSupport
      (xyDual3IntegerCurlModes a + xyEndpointPathModes x y) c
      (Finsupp.support_mapRange hc)
  rw [xyDual3StarBondVector_energy _ hq]

/-- A rooted-tree circulation, viewed as a real dual one-form, is in the
co-closed subspace of the grounded dual complex's grounded dual complex. -/
noncomputable def xyDual3IntegerCirculationToCoClosed {B : Dual3Box}
    (ρ : {j : Dual3Links B → ℤ //
      RootedTreeGauge.CoClosed (xyDual3RootedTree B) j}) :
    coClosed (dual3ExactOneComplex B) := by
  let μ : EuclideanSpace ℝ (Dual3Links B) :=
    WithLp.toLp 2 (fun e => (ρ.1 e : ℝ))
  refine ⟨μ, ?_⟩
  apply LinearMap.mem_ker.mpr
  let g : EuclideanSpace ℝ (Dual3Vertices B) :=
    (dual3ExactOneComplex B).d₀.adjoint μ
  have hρ : RootedTreeGauge.CoClosed (xyDual3RootedTree B)
      (fun e => (ρ.1 e : ℝ)) := by
    intro v hv
    have h := ρ.2 v hv
    change RootedTreeGauge.divergence (xyDual3RootedTree B) ρ.1 v = 0 at h
    change RootedTreeGauge.divergence (xyDual3RootedTree B)
      (fun e => (ρ.1 e : ℝ)) v = 0
    unfold RootedTreeGauge.divergence at h ⊢
    push_cast
    exact_mod_cast h
  have hp (p : XYDual3GraphVertex B → ℝ) :
      ∑ e : Dual3Links B, (ρ.1 e : ℝ) *
        RootedTreeGauge.coboundary (xyDual3RootedTree B) p e = 0 :=
    (RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries
      (xyDual3RootedTree B) (fun e => (ρ.1 e : ℝ))).1 hρ p
  have hg : inner ℝ g g = 0 := by
    have hAdj := LinearMap.adjoint_inner_left
      (dual3ExactOneComplex B).d₀ g μ
    have hpv := xyDual3VertexPotentialOfVector_eq_vector g
    let p := xyDual3VertexPotentialOfVector g
    have hD0 : (dual3ExactOneComplex B).d₀ g =
        -WithLp.toLp 2 (fun e : Dual3Links B =>
          RootedTreeGauge.coboundary (xyDual3RootedTree B) p e) := by
      ext e
      have h := xyDual3D0_potential_eq_neg_treeCoboundary p e
      have hEq := congrArg (fun z : EuclideanSpace ℝ (Dual3Vertices B) =>
        (dual3ExactOneComplex B).d₀ z e) hpv
      exact hEq.symm.trans h
    calc
      inner ℝ g g = inner ℝ μ
          ((dual3ExactOneComplex B).d₀ g) := hAdj
      _ = -∑ e : Dual3Links B, (ρ.1 e : ℝ) *
          RootedTreeGauge.coboundary (xyDual3RootedTree B) p e := by
        rw [hD0, PiLp.inner_apply]
        simp [μ, RCLike.inner_apply, mul_comm]
      _ = 0 := by rw [hp p]; simp
  have hgzero : g = 0 := inner_self_eq_zero.mp hg
  exact hgzero

/-- A the grounded dual complex real co-closed one-form is divergence-free for the rooted-tree
incidence convention. -/
theorem xyDual3CoClosedToRooted {B : Dual3Box}
    (μ : coClosed (dual3ExactOneComplex B)) :
    RootedTreeGauge.CoClosed (xyDual3RootedTree B)
      (fun e => (μ.1 e : ℝ)) := by
  apply (RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries
    (xyDual3RootedTree B) (fun e => (μ.1 e : ℝ))).2
  intro p
  let u := xyDual3VertexPotentialVector p
  have hD0 : (dual3ExactOneComplex B).d₀ u =
      -WithLp.toLp 2 (fun e : Dual3Links B =>
        RootedTreeGauge.coboundary (xyDual3RootedTree B) p e) := by
    ext e
    have h := xyDual3D0_potential_eq_neg_treeCoboundary p e
    exact h
  have hker : (dual3ExactOneComplex B).d₀.adjoint μ.1 = 0 :=
    LinearMap.mem_ker.mp μ.2
  have hpair := LinearMap.adjoint_inner_left
    (dual3ExactOneComplex B).d₀ u μ.1
  rw [hker] at hpair
  simp at hpair
  have hsum : inner ℝ μ.1
      ((dual3ExactOneComplex B).d₀ u) =
      -∑ e : Dual3Links B, (μ.1 e : ℝ) *
        RootedTreeGauge.coboundary (xyDual3RootedTree B) p e := by
    rw [hD0, PiLp.inner_apply]
    simp [RCLike.inner_apply, mul_comm]
  rw [hsum] at hpair
  exact neg_eq_zero.mp hpair.symm

/-- The inverse Hodge pairing on the grounded dual complex's grounded complex is the chord inverse
pairing supplied by the tree-gauge Poisson adapter. -/
theorem xyDual3HodgePairing_eq_chord {B : Dual3Box}
    (test source : coClosed (dual3ExactOneComplex B)) :
    inner ℝ test.1 (dual3HodgeInverse source) =
      dotProduct ((xyDual3RootedTree B).restrictChord (test.1.ofLp))
        (Matrix.mulVec
          ((reducedChordMatrix (xyDual3RootedTree B)
            (xyDual3FinitePoissonModel (B := B)))⁻¹)
          ((xyDual3RootedTree B).restrictChord (source.1.ofLp))) := by
  let T := xyDual3RootedTree B
  let M := xyDual3FinitePoissonModel (B := B)
  let C := dual3ExactOneComplex B
  let jr : {f : Dual3Links B → ℝ // RootedTreeGauge.CoClosed T f} :=
    ⟨test.1.ofLp, xyDual3CoClosedToRooted test⟩
  let sr : {f : Dual3Links B → ℝ // RootedTreeGauge.CoClosed T f} :=
    ⟨source.1.ofLp, xyDual3CoClosedToRooted source⟩
  let u : coClosed C := dual3HodgeInverse source
  have hu : xyDual3PoissonMatrix.mulVec u.1.ofLp = source.1.ofLp := by
    have hspec : hodgeOnCoClosed C u = source := dual3HodgeInverse_spec source
    have hspec' := congrArg Subtype.val hspec
    have hform : formLaplacian C u.1 = source.1 := by
      simpa [hodgeOnCoClosed] using hspec'
    calc
      xyDual3PoissonMatrix.mulVec u.1.ofLp =
          (formLaplacian C u.1).ofLp := xyDual3PoissonMatrix_mulVec u.1
      _ = source.1.ofLp := congrArg WithLp.ofLp hform
  have hvar := finiteModel_variational_identity_of_solution T M
    sr.2 jr.2 u.1.ofLp (by
      simpa [M, sr, xyDual3FinitePoissonModel] using hu)
  have hinner : inner ℝ test.1 u.1 = dotProduct jr.1 u.1.ofLp := by
    simp [jr, PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm]
  change inner ℝ test.1 u.1 =
    dotProduct (T.restrictChord test.1.ofLp)
      (Matrix.mulVec ((reducedChordMatrix T M)⁻¹)
        (T.restrictChord source.1.ofLp))
  rw [hinner]
  simpa [jr, sr, M, T] using hvar

/-- The oriented dual plaquette form of the endpoint path. -/
noncomputable def xyDual3PathSource {B : Dual3Box}
    (x y : XYSites B) : EuclideanSpace ℝ (Dual3Links B) :=
  (dual3ExactOneComplex B).d₁.adjoint (xyDual3EndpointPathVector x y)

/-- The path source is automatically co-closed because `d₁ d₀ = 0`. -/
noncomputable def xyDual3PathSourceCoClosed {B : Dual3Box}
    (x y : XYSites B) : coClosed (dual3ExactOneComplex B) := by
  refine ⟨xyDual3PathSource x y, ?_⟩
  apply LinearMap.mem_ker.mpr
  let φ := xyDual3EndpointPathVector x y
  let g := (dual3ExactOneComplex B).d₀.adjoint
    ((dual3ExactOneComplex B).d₁.adjoint φ)
  have hg : inner ℝ g g = 0 := calc
    inner ℝ g g = inner ℝ ((dual3ExactOneComplex B).d₁.adjoint φ)
        ((dual3ExactOneComplex B).d₀ g) := by
          exact LinearMap.adjoint_inner_left (dual3ExactOneComplex B).d₀
            g ((dual3ExactOneComplex B).d₁.adjoint φ)
    _ = inner ℝ φ ((dual3ExactOneComplex B).d₁
        ((dual3ExactOneComplex B).d₀ g)) := by
          exact LinearMap.adjoint_inner_left (dual3ExactOneComplex B).d₁
            ((dual3ExactOneComplex B).d₀ g) φ
    _ = 0 := by
          have h := congrArg (fun f => f g)
            (dual3ExactOneComplex B).complex
          simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
          rw [h]
          simp
  exact inner_self_eq_zero.mp hg

/-- Real dual-link representative of a chord vector in rooted-tree gauge. -/
noncomputable def xyDual3ChordEmbeddingVector {B : Dual3Box}
    (n : (xyDual3RootedTree B).Chord → ℝ) :
    EuclideanSpace ℝ (Dual3Links B) :=
  WithLp.toLp 2
    (Matrix.mulVec (chordEmbeddingMatrix (xyDual3RootedTree B)) n)

/-- The integer extension of chord data, after casting to real link values,
is the same tree-zero vector as the finite Poisson adapter. -/
theorem xyDual3IntegerLinkVector_extendChord_eq {B : Dual3Box}
    (n : (xyDual3RootedTree B).Chord → ℤ) :
    xyDual3IntegerLinkVector
      ((xyDual3RootedTree B).extendChord n) =
        xyDual3ChordEmbeddingVector (fun c => (n c : ℝ)) := by
  classical
  let T := xyDual3RootedTree B
  ext e
  rw [xyDual3IntegerLinkVector_apply]
  by_cases he : e ∈ Set.range T.treeEdge
  · rcases he with ⟨w, rfl⟩
    simp [xyDual3ChordEmbeddingVector, T, RootedTreeGauge.extendChord,
      chordEmbeddingMatrix_mulVec_at_tree]
  · let c : T.Chord := ⟨e, he⟩
    have hc := chordEmbeddingMatrix_mulVec_at_chord T
      (fun c => (n c : ℝ)) c
    simpa [xyDual3ChordEmbeddingVector, T, RootedTreeGauge.extendChord, c, he] using hc.symm

/-- The matrix quadratic of the finite the grounded dual complex Hodge Laplacian is the squared
dual curl norm. -/
theorem xyDual3PoissonMatrix_energy {B : Dual3Box}
    (u : EuclideanSpace ℝ (Dual3Links B)) :
    dotProduct u.ofLp ((xyDual3PoissonMatrix (B := B)).mulVec u.ofLp) =
      inner ℝ ((dual3ExactOneComplex B).d₁ u)
        ((dual3ExactOneComplex B).d₁ u) := by
  rw [xyDual3PoissonMatrix_mulVec]
  calc
    dotProduct u.ofLp (formLaplacian (dual3ExactOneComplex B) u).ofLp =
        inner ℝ u (formLaplacian (dual3ExactOneComplex B) u) := by
          simp [dotProduct, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    _ = inner ℝ ((dual3ExactOneComplex B).d₁ u)
        ((dual3ExactOneComplex B).d₁ u) := by
          change inner ℝ u
            ((dual3ExactOneComplex B).d₁.adjoint ((dual3ExactOneComplex B).d₁ u)) = _
          exact LinearMap.adjoint_inner_right (dual3ExactOneComplex B).d₁ u
            ((dual3ExactOneComplex B).d₁ u)

/-- Chord coordinates of the co-closed path source `δφ`. -/
noncomputable def xyDual3PathChordSource {B : Dual3Box}
    (x y : XYSites B) : (xyDual3RootedTree B).Chord → ℝ :=
  (xyDual3RootedTree B).restrictChord (xyDual3PathSource x y).ofLp

/-- The mixed path pairing is exactly the chord linear source in the Poisson
model. -/
theorem xyDual3ChordCross_eq_pathSource {B : Dual3Box}
    (n : (xyDual3RootedTree B).Chord → ℝ) (x y : XYSites B) :
    inner ℝ ((dual3ExactOneComplex B).d₁
        (xyDual3ChordEmbeddingVector n))
      (xyDual3EndpointPathVector x y) =
      dotProduct n (xyDual3PathChordSource x y) := by
  let T := xyDual3RootedTree B
  let u := xyDual3ChordEmbeddingVector n
  let src := xyDual3PathSource x y
  have htree : RootedTreeGauge.InTreeGauge T u.ofLp := by
    intro w
    change (Matrix.mulVec (chordEmbeddingMatrix T) n) (T.treeEdge w) = 0
    exact chordEmbeddingMatrix_mulVec_at_tree T n w
  have hsrc : RootedTreeGauge.CoClosed T src.ofLp :=
    xyDual3CoClosedToRooted (xyDual3PathSourceCoClosed x y)
  have hp := RootedTreeGauge.pairing_eq_chordPairing T htree ⟨src.ofLp, hsrc⟩
  have hadj : inner ℝ ((dual3ExactOneComplex B).d₁ u)
      (xyDual3EndpointPathVector x y) = inner ℝ u src := by
    exact (LinearMap.adjoint_inner_right (dual3ExactOneComplex B).d₁ u
      (xyDual3EndpointPathVector x y)).symm
  rw [hadj]
  have hinner : inner ℝ u src = dotProduct src.ofLp u.ofLp := by
    simp [PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm]
  rw [hinner]
  calc
    dotProduct src.ofLp u.ofLp =
        dotProduct (T.restrictChord src.ofLp) n := by
          simpa [dotProduct, T, u, xyDual3ChordEmbeddingVector,
            RootedTreeGauge.restrictChord,
            chordEmbeddingMatrix_mulVec_at_chord] using hp
    _ = dotProduct n (xyDual3PathChordSource x y) := by
          simp [xyDual3PathChordSource, T, src, dotProduct,
            RootedTreeGauge.restrictChord, mul_comm]

/-- Expanding the shifted dual curl energy gives the chord quadratic, the
linear path source, and the squared path norm. -/
theorem xyDual3ChordShiftedEnergy_expansion {B : Dual3Box}
    (n : (xyDual3RootedTree B).Chord → ℝ) (x y : XYSites B) :
    inner ℝ
        ((dual3ExactOneComplex B).d₁ (xyDual3ChordEmbeddingVector n) +
          xyDual3EndpointPathVector x y)
        ((dual3ExactOneComplex B).d₁ (xyDual3ChordEmbeddingVector n) +
          xyDual3EndpointPathVector x y) =
      inner ℝ (xyDual3EndpointPathVector x y)
          (xyDual3EndpointPathVector x y) +
        dotProduct n (Matrix.mulVec
          (reducedChordMatrix (xyDual3RootedTree B)
            xyDual3FinitePoissonModel) n) +
        2 * dotProduct n (xyDual3PathChordSource x y) := by
  let T := xyDual3RootedTree B
  let M := xyDual3FinitePoissonModel (B := B)
  let u := xyDual3ChordEmbeddingVector n
  simp only [inner_add_left, inner_add_right]
  have hnorm : inner ℝ ((dual3ExactOneComplex B).d₁ u)
      ((dual3ExactOneComplex B).d₁ u) =
      dotProduct n (Matrix.mulVec (reducedChordMatrix T M) n) := by
    calc
      _ = dotProduct u.ofLp (xyDual3PoissonMatrix.mulVec u.ofLp) :=
        (xyDual3PoissonMatrix_energy u).symm
      _ = dotProduct n (Matrix.mulVec (reducedChordMatrix T M) n) := by
        rw [reducedChord_energy_eq T M n]
        simp [u, xyDual3ChordEmbeddingVector, T, M,
          xyDual3FinitePoissonModel, xyDual3PoissonMatrix]
  have hcross := xyDual3ChordCross_eq_pathSource n x y
  rw [hnorm, hcross]
  rw [real_inner_comm ((dual3ExactOneComplex B).d₁ u)
    (xyDual3EndpointPathVector x y), hcross]
  ring

/-- The finite-box projection of the dual plaquette path: `δ Δ⁻¹ φ`. -/
noncomputable def xyDual3PathTau {B : Dual3Box} (x y : XYSites B) :
    coClosed (dual3ExactOneComplex B) :=
  dual3HodgeInverse (xyDual3PathSourceCoClosed x y)

/-- The positive-definite chord matrix at inverse temperature `β`. -/
noncomputable def xyDual3ChordMatrix {B : Dual3Box} (β : ℝ) :
    Matrix (xyDual3RootedTree B).Chord (xyDual3RootedTree B).Chord ℝ :=
  scaledChordMatrix (xyDual3RootedTree B) xyDual3FinitePoissonModel β

/-- Positive definiteness of the chord matrix follows from the grounded dual complex's exact
grounded complex and the tree gauge. -/
theorem xyDual3ChordMatrix_posDef {B : Dual3Box} {β : ℝ} (hβ : 0 < β) :
    (xyDual3ChordMatrix (B := B) β).PosDef := by
  exact scaledChordMatrix_posDef (xyDual3RootedTree B)
    xyDual3FinitePoissonModel hβ

set_option linter.style.haveILetI false in
/-- Inverse scaling for the chord quadratic. -/
theorem xyDual3ChordMatrix_inv {B : Dual3Box} {β : ℝ} (hβ : 0 < β) :
    (xyDual3ChordMatrix (B := B) β)⁻¹ =
      (2 * Real.pi * β) •
        (reducedChordMatrix (xyDual3RootedTree B)
          xyDual3FinitePoissonModel)⁻¹ := by
  let K := reducedChordMatrix (xyDual3RootedTree B)
    xyDual3FinitePoissonModel
  let c := (2 * Real.pi * β)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (by positivity : 2 * Real.pi * β ≠ 0)
  letI : Invertible c := invertibleOfNonzero hc
  have hKdet : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).mp
      (reducedChordMatrix_posDef (xyDual3RootedTree B)
        xyDual3FinitePoissonModel).isUnit
  rw [show xyDual3ChordMatrix β = c • K by
    simp [xyDual3ChordMatrix, scaledChordMatrix, K, c]]
  rw [Matrix.inv_smul K c hKdet]
  have hcinv : ⅟c = 2 * Real.pi * β := by
    simp [c]
  rw [hcinv]

/-- Bilinear evaluation against the scaled chord inverse is the grounded
Hodge inverse pairing in chord coordinates. -/
theorem xyDual3ChordBilinear_eq_scaledInverse {B : Dual3Box}
    {β : ℝ} (hβ : 0 < β)
    (u v : (xyDual3RootedTree B).Chord → ℝ) :
    xyDual3ComplexBilinear (xyDual3ChordMatrix (B := B) β)⁻¹ u v =
      ((2 * Real.pi * β * dotProduct u
        (Matrix.mulVec ((reducedChordMatrix (xyDual3RootedTree B)
          xyDual3FinitePoissonModel)⁻¹) v) : ℝ) : ℂ) := by
  rw [xyDual3ComplexBilinear_eq_dotProduct]
  rw [xyDual3ChordMatrix_inv hβ]
  simp [Matrix.smul_mulVec, dotProduct_smul]

/-- The residual path energy after projecting its dual source onto the
co-closed subspace. -/
noncomputable def xyDual3ResidualEnergy {B : Dual3Box}
    (x y : XYSites B) : ℝ :=
  inner ℝ (xyDual3EndpointPathVector x y) (xyDual3EndpointPathVector x y) -
    inner ℝ (xyDual3PathSourceCoClosed x y).1 (xyDual3PathTau x y).1

/-- Explicit determinant factor from finite-dimensional Poisson summation. -/
noncomputable def xyDual3PoissonConstant {B : Dual3Box} (β : ℝ) : ℂ :=
  ((Real.sqrt (xyDual3ChordMatrix (B := B) β).det : ℝ) : ℂ)⁻¹

abbrev XYDual3IntegerCirculations (B : Dual3Box) :=
  {ρ : Dual3Links B → ℤ //
    RootedTreeGauge.CoClosed (xyDual3RootedTree B) ρ}


/-- Integral chord frequencies are exactly the integer dual circulations. -/
noncomputable def xyDual3ChordCurrentEquiv {B : Dual3Box} :
    ((xyDual3RootedTree B).Chord → ℤ) ≃ XYDual3IntegerCirculations B :=
  RootedTreeGauge.circulationEquiv (R := ℤ) (xyDual3RootedTree B)

/-- The centered the grounded dual complex quotient-Gaussian characteristic at an integer
co-closed dual current, with the source frequency `2πρ`. -/
noncomputable def xyDual3Chi0 {B : Dual3Box} {β : ℝ} (hβ : 0 ≤ β)
    (ρ : XYDual3IntegerCirculations B) : ℂ :=
  MeasureTheory.charFun
    (MeasureTheory.Measure.map
      (finiteComplexQuotientTestFunctional (dual3ExactOneComplex B)
        ((2 * Real.pi) • xyDual3IntegerCirculationToCoClosed ρ))
      (dual3QuotientGaussian (B := B) β hβ)) 1

/-- Chord coordinates of an integer circulation, after realification. -/
def xyDual3IntegerCirculationChord {B : Dual3Box}
    (ρ : XYDual3IntegerCirculations B) :
    (xyDual3RootedTree B).Chord → ℝ :=
  fun c => (ρ.1 c.1 : ℝ)


theorem xyDual3ChordCurrentEquiv_chord {B : Dual3Box}
    (k : (xyDual3RootedTree B).Chord → ℤ) :
    xyDual3IntegerCirculationChord (xyDual3ChordCurrentEquiv (B := B) k) =
      fun c => (k c : ℝ) := by
  funext c
  simp [xyDual3IntegerCirculationChord, xyDual3ChordCurrentEquiv,
    RootedTreeGauge.circulationEquiv, RootedTreeGauge.cycleExtension]

/-- The grounded dual complex characteristic function evaluates to its covariance quadratic. -/
theorem xyDual3Chi0_characteristic {B : Dual3Box} {β : ℝ}
    (hβ : 0 ≤ β) (ρ : XYDual3IntegerCirculations B) :
    xyDual3Chi0 hβ ρ = Complex.exp
      (-↑(dual3CovarianceQuadratic β
        ((2 * Real.pi) • xyDual3IntegerCirculationToCoClosed ρ) / 2)) := by
  exact dual3QuotientGaussian_characteristic hβ
    ((2 * Real.pi) • xyDual3IntegerCirculationToCoClosed ρ)

/-- In chord coordinates, `χ₀(2πρ)` is the Gaussian lattice weight supplied
by the adapter. -/
theorem xyDual3Chi0_eq_chordGaussian {B : Dual3Box} {β : ℝ}
    (hβ : 0 ≤ β) (ρ : XYDual3IntegerCirculations B) :
    xyDual3Chi0 hβ ρ = Complex.exp
      (-(2 * Real.pi ^ 2 * β) * dotProduct
        (xyDual3IntegerCirculationChord ρ)
        (Matrix.mulVec ((reducedChordMatrix (xyDual3RootedTree B)
          xyDual3FinitePoissonModel)⁻¹)
          (xyDual3IntegerCirculationChord ρ))) := by
  rw [xyDual3Chi0_characteristic]
  let μ := xyDual3IntegerCirculationToCoClosed ρ
  let q := xyDual3IntegerCirculationChord ρ
  have hcoords :
      (xyDual3RootedTree B).restrictChord μ.1.ofLp = q := by
    funext c
    simp [μ, q, xyDual3IntegerCirculationChord,
      xyDual3IntegerCirculationToCoClosed,
      RootedTreeGauge.restrictChord]
  have hpair : inner ℝ μ.1 (dual3HodgeInverse μ) =
      dotProduct q (Matrix.mulVec
        ((reducedChordMatrix (xyDual3RootedTree B)
          xyDual3FinitePoissonModel)⁻¹) q) := by
    have h := xyDual3HodgePairing_eq_chord μ μ
    rw [hcoords] at h
    exact h
  have hcov : dual3CovarianceQuadratic β ((2 * Real.pi) • μ) =
      β * (2 * Real.pi) ^ 2 * dotProduct q (Matrix.mulVec
        ((reducedChordMatrix (xyDual3RootedTree B)
          xyDual3FinitePoissonModel)⁻¹) q) := by
    rw [dual3CovarianceQuadratic_eq_hodge, quotientCovarianceQuadratic]
    rw [map_smul]
    change β * inner ℝ ((2 * Real.pi) • μ.1)
      ((2 * Real.pi) • dual3HodgeInverse μ) = _
    rw [real_inner_smul_left, real_inner_smul_right, hpair]
    ring
  rw [hcov]
  congr 1
  push_cast
  ring

/-- The phase of the endpoint path at an integer co-closed dual current. -/
noncomputable def xyDual3PathPhase {B : Dual3Box} {β : ℝ} (hβ : 0 ≤ β)
    (x y : XYSites B) (ρ : XYDual3IntegerCirculations B) : ℂ :=
  xyDual3Chi0 hβ ρ * Complex.exp
    (Complex.I * (2 * Real.pi : ℂ) *
      ((inner ℝ (xyDual3IntegerCirculationToCoClosed ρ).1
        (xyDual3PathTau x y).1 : ℝ) : ℂ))


/-- The chord Poisson summand is the shifted dual-curl Gaussian after its
constant path energy is factored out. -/
theorem xyDual3TestedPrimalTerm_eq_chordEnergy {B : Dual3Box}
    {β : ℝ} (hβ : 0 < β) (x y : XYSites B)
    (n : (xyDual3RootedTree B).Chord → ℤ) :
    testedPrimalTerm (xyDual3ChordMatrix (B := B) β)
      (xyDual3PathChordSource x y) (-β⁻¹) n =
      Complex.exp (-(dotProduct (fun c => (n c : ℝ))
        (Matrix.mulVec (reducedChordMatrix (xyDual3RootedTree B)
          xyDual3FinitePoissonModel) (fun c => (n c : ℝ))) / (2 * β)) -
        dotProduct (fun c => (n c : ℝ)) (xyDual3PathChordSource x y) / β) := by
  let K := reducedChordMatrix (xyDual3RootedTree B)
    xyDual3FinitePoissonModel
  let A := xyDual3ChordMatrix (B := B) β
  let τ := xyDual3PathChordSource x y
  let nr : (xyDual3RootedTree B).Chord → ℝ := fun c => (n c : ℝ)
  rw [xyDual3TestedPrimalTerm_eq]
  unfold primalQuadraticExp realTiltParameter
  apply congrArg Complex.exp
  have hquad :
      (∑ i, ∑ j, (n i : ℂ) * (A i j : ℂ) * (n j : ℂ)) =
        ((dotProduct nr (A.mulVec nr) : ℝ) : ℂ) := by
    simpa [xyDual3ComplexBilinear, nr] using
      (xyDual3ComplexBilinear_eq_dotProduct A nr nr)
  have hscaled : dotProduct nr (A.mulVec nr) =
      (2 * Real.pi * β)⁻¹ * dotProduct nr (K.mulVec nr) := by
    simp [A, K, xyDual3ChordMatrix, scaledChordMatrix, Matrix.smul_mulVec,
      dotProduct_smul, nr]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hβ' : β ≠ 0 := ne_of_gt hβ
  have hlinReal :
      (2 * Real.pi) * ∑ i,
        ((-β⁻¹ * τ i / (2 * Real.pi)) * nr i) =
        -dotProduct nr τ / β := by
    have hcoeff (i : (xyDual3RootedTree B).Chord) :
        2 * Real.pi * (-β⁻¹ * τ i / (2 * Real.pi)) = -β⁻¹ * τ i := by
      field_simp [Real.pi_ne_zero]
    calc
      _ = ∑ i, (2 * Real.pi *
          (-β⁻¹ * τ i / (2 * Real.pi))) * nr i := by
            rw [Finset.mul_sum]
            apply Fintype.sum_congr
            intro i
            ring
      _ = ∑ i, (-β⁻¹ * τ i) * nr i := by
        apply Fintype.sum_congr
        intro i
        rw [hcoeff]
      _ = ∑ i, (-β⁻¹) * (τ i * nr i) := by
        apply Fintype.sum_congr
        intro i
        ring
      _ = -β⁻¹ * ∑ i, τ i * nr i := by
        rw [← Finset.mul_sum]
      _ = -dotProduct nr τ / β := by
        simp [dotProduct, mul_comm, div_eq_mul_inv]
  have hlin :
      (2 * Real.pi : ℂ) * ∑ i,
        (((-β⁻¹ * τ i / (2 * Real.pi) : ℝ) : ℂ) * (n i : ℂ)) =
        ((-dotProduct nr τ / β : ℝ) : ℂ) := by
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) hlinReal
    simpa [nr, Complex.ofReal_mul, Complex.ofReal_div]
      using hcast
  rw [hquad, hscaled, hlin]
  dsimp [nr, τ]
  push_cast
  field_simp [Real.pi_ne_zero, hpi, hβ']
  ring


/-- Each chord summand is the tested primal Gaussian times the path norm
factor. -/
theorem xyDual3CycleGaussianWeight_chord_term {B : Dual3Box}
    {β : ℝ} (hβ : 0 < β) (x y : XYSites B)
    (n : (xyDual3RootedTree B).Chord → ℤ) :
    ((xyDual3CycleGaussianWeight β (xyEndpointPathModes x y)
      (xyDual3CycleOfIntegerLink
        ((xyDual3RootedTree B).extendChord n)) : ℝ) : ℂ) =
      Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
        (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) *
        testedPrimalTerm (xyDual3ChordMatrix (B := B) β)
          (xyDual3PathChordSource x y) (-β⁻¹) n := by
  rw [xyDual3CycleGaussianWeight_eq_dualEnergy]
  have hvec := xyDual3IntegerLinkVector_extendChord_eq n
  have henergy : xyDual3ShiftedDualEnergy
      ((xyDual3RootedTree B).extendChord n) x y =
      inner ℝ (xyDual3EndpointPathVector x y)
          (xyDual3EndpointPathVector x y) +
        dotProduct (fun c => (n c : ℝ))
          (Matrix.mulVec (reducedChordMatrix (xyDual3RootedTree B)
            xyDual3FinitePoissonModel) (fun c => (n c : ℝ))) +
        2 * dotProduct (fun c => (n c : ℝ))
          (xyDual3PathChordSource x y) := by
    unfold xyDual3ShiftedDualEnergy xyDual3ShiftedDualPlaquetteVector
    rw [hvec]
    exact xyDual3ChordShiftedEnergy_expansion
      (fun c => (n c : ℝ)) x y
  rw [henergy, xyDual3TestedPrimalTerm_eq_chordEnergy hβ]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ne_of_gt hβ]
  ring


noncomputable def xyDual3CycleChordEquiv {B : Dual3Box} :
    XYEndpointCycleModes (B := B) ≃
      ((xyDual3RootedTree B).Chord → ℤ) :=
  (xyDual3CycleTreeGaugeEquiv (B := B)).trans
    (RootedTreeGauge.chordGaugeEquiv (R := ℤ) (xyDual3RootedTree B)).symm

theorem xyDual3CycleGaussianWeight_chord_summable {B : Dual3Box}
    {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    Summable (fun n : (xyDual3RootedTree B).Chord → ℤ =>
      xyDual3CycleGaussianWeight β (xyEndpointPathModes x y)
        (xyDual3CycleOfIntegerLink
          ((xyDual3RootedTree B).extendChord n))) := by
  have hcycle : Summable (fun c : XYEndpointCycleModes (B := B) =>
      xyDual3CycleGaussianWeight β (xyEndpointPathModes x y) c) := by
    have hsub : Summable (fun c : XYEndpointCycleModes (B := B) =>
        xyShiftedCycleGaussianTerm β x y c.1) :=
      (xyShiftedCycleGaussianTerm_summable β hβ x y).subtype
        (fun m => xyBondModeDivergence m = 0)
    apply hsub.congr
    intro c
    simp [xyShiftedCycleGaussianTerm, xyDual3CycleGaussianWeight,
      xyDualGaussianProduct, xyVillainGaussianCoeff, c.2]
  let e := xyDual3CycleChordEquiv (B := B)
  let f : XYEndpointCycleModes (B := B) → ℝ := fun c =>
    xyDual3CycleGaussianWeight β (xyEndpointPathModes x y) c
  have hcomp : Summable (fun n : (xyDual3RootedTree B).Chord → ℤ =>
      f (e.symm n)) :=
    (Equiv.summable_iff (f := f) e.symm).2 hcycle
  apply hcomp.congr
  intro n
  simp [f, e, xyDual3CycleChordEquiv, xyDual3CycleTreeGaugeEquiv,
    RootedTreeGauge.chordGaugeEquiv]

/-- The cycle sum, after the filling quotient and tree gauge, is a chord
lattice sum with the same multiplicity. -/
theorem xyDual3CycleGaussianWeight_chord_reindex {B : Dual3Box}
    (β : ℝ) (path : XYBondModes (B := B)) :
    (∑' c : XYEndpointCycleModes (B := B),
      xyDual3CycleGaussianWeight β path c) =
    (∑' n : (xyDual3RootedTree B).Chord → ℤ,
      xyDual3CycleGaussianWeight β path
        (xyDual3CycleOfIntegerLink
          ((xyDual3RootedTree B).extendChord n))) := by
  let e := xyDual3CycleTreeGaugeEquiv (B := B)
  let g := RootedTreeGauge.chordGaugeEquiv (R := ℤ) (xyDual3RootedTree B)
  let f : {a : Dual3Links B → ℤ //
      RootedTreeGauge.InTreeGauge (xyDual3RootedTree B) a} → ℝ := fun a =>
    xyDual3CycleGaussianWeight β path (xyDual3CycleOfIntegerLink a.1)
  calc
    _ = ∑' a : {a : Dual3Links B → ℤ //
        RootedTreeGauge.InTreeGauge (xyDual3RootedTree B) a}, f a :=
          xyDual3CycleGaussianWeight_reindex β path
    _ = ∑' n : (xyDual3RootedTree B).Chord → ℤ, f (g n) :=
          (g.tsum_eq f).symm
    _ = _ := by
          apply tsum_congr
          intro n
          rfl


set_option linter.style.haveILetI false in
/-- The chord inverse matrix is symmetric, so the two cross terms in the
complex quadratic give twice the Hodge pairing. -/
theorem xyDual3ChordDualTerm_eq_correctedPhase {B : Dual3Box}
    {β : ℝ} (hβ : 0 < β) (x y : XYSites B)
    (k : (xyDual3RootedTree B).Chord → ℤ) :
    dualQuadraticExp (xyDual3ChordMatrix (B := B) β)
        (realTiltParameter (xyDual3PathChordSource x y) (-β⁻¹)) k =
      Complex.exp ((inner ℝ (xyDual3PathSourceCoClosed x y).1
        (xyDual3PathTau x y).1 : ℝ) / (2 * β)) *
        xyDual3PathPhase (le_of_lt hβ) x y
          (xyDual3ChordCurrentEquiv (B := B) k) := by
  let T := xyDual3RootedTree B
  let K := reducedChordMatrix T xyDual3FinitePoissonModel
  let A := xyDual3ChordMatrix (B := B) β
  let σ := xyDual3PathChordSource x y
  let wr : T.Chord → ℝ := fun c => -β⁻¹ * σ c / (2 * Real.pi)
  let kr : T.Chord → ℝ := fun c => (k c : ℝ)
  let ρ := xyDual3ChordCurrentEquiv (B := B) k
  let μ := xyDual3IntegerCirculationToCoClosed ρ
  let τ := xyDual3PathTau x y
  let q := xyDual3IntegerCirculationChord ρ
  have hcoords : q = kr := by
    simpa [q, kr] using xyDual3ChordCurrentEquiv_chord k
  have hwr : wr = (-(2 * Real.pi * β)⁻¹) • σ := by
    funext c
    dsimp [wr]
    field_simp [Real.pi_ne_zero, ne_of_gt hβ]
  have hApos : A.PosDef := by
    exact xyDual3ChordMatrix_posDef hβ
  have hAsymm : A.IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp hApos.isHermitian
  have hAinvSymm : A⁻¹.IsSymm := hAsymm.inv
  have hcomm := xyDual3ComplexBilinear_comm A⁻¹ hAinvSymm wr kr
  have hPathChord :
      T.restrictChord ((xyDual3PathSourceCoClosed x y).1.ofLp) = σ := by
    funext c
    rfl
  have hMuChord : T.restrictChord μ.1.ofLp = q := by
    funext c
    simp [T, μ, q, xyDual3IntegerCirculationToCoClosed,
      xyDual3IntegerCirculationChord, RootedTreeGauge.restrictChord]
  have hsourcePair :
      inner ℝ (xyDual3PathSourceCoClosed x y).1
          (xyDual3PathTau x y).1 =
        dotProduct σ (K⁻¹.mulVec σ) := by
    have hraw := xyDual3HodgePairing_eq_chord
      (xyDual3PathSourceCoClosed x y) (xyDual3PathSourceCoClosed x y)
    change inner ℝ (xyDual3PathSourceCoClosed x y).1
        (dual3HodgeInverse (xyDual3PathSourceCoClosed x y)) =
      dotProduct (T.restrictChord ((xyDual3PathSourceCoClosed x y).1.ofLp))
        (K⁻¹.mulVec (T.restrictChord
          ((xyDual3PathSourceCoClosed x y).1.ofLp))) at hraw
    exact hraw
  have hpair : inner ℝ μ.1 τ.1 = dotProduct q (K⁻¹.mulVec σ) := by
    have hraw := xyDual3HodgePairing_eq_chord μ
      (xyDual3PathSourceCoClosed x y)
    change inner ℝ μ.1 (dual3HodgeInverse
        (xyDual3PathSourceCoClosed x y)) =
      dotProduct (T.restrictChord μ.1.ofLp)
        (K⁻¹.mulVec (T.restrictChord
          ((xyDual3PathSourceCoClosed x y).1.ofLp))) at hraw
    rw [hMuChord] at hraw
    exact hraw
  have hpairK : inner ℝ μ.1 τ.1 = dotProduct kr (K⁻¹.mulVec σ) := by
    rw [← hcoords]
    exact hpair
  have hscaleDot :
      dotProduct ((-(2 * Real.pi * β)⁻¹) • σ)
        (K⁻¹.mulVec ((-(2 * Real.pi * β)⁻¹) • σ)) =
        (-(2 * Real.pi * β)⁻¹) ^ 2 * dotProduct σ (K⁻¹.mulVec σ) := by
    calc
      _ = dotProduct ((-(2 * Real.pi * β)⁻¹) • σ)
          ((-(2 * Real.pi * β)⁻¹) • K⁻¹.mulVec σ) := by
            rw [Matrix.mulVec_smul]
      _ = (-(2 * Real.pi * β)⁻¹) ^ 2 *
          dotProduct σ (K⁻¹.mulVec σ) := by
            rw [smul_dotProduct, dotProduct_smul]
            simp only [smul_eq_mul]
            ring
  have hww : (Real.pi : ℂ) *
      xyDual3ComplexBilinear A⁻¹ wr wr =
        ((inner ℝ (xyDual3PathSourceCoClosed x y).1
          (xyDual3PathTau x y).1 / (2 * β) : ℝ) : ℂ) := by
    rw [xyDual3ChordBilinear_eq_scaledInverse hβ]
    rw [hwr, hscaleDot, ← hsourcePair]
    push_cast
    field_simp [Real.pi_ne_zero, ne_of_gt hβ]
  have hkk : -(Real.pi : ℂ) *
      xyDual3ComplexBilinear A⁻¹ kr kr =
        ((-(2 * Real.pi ^ 2 * β) *
          dotProduct kr (K⁻¹.mulVec kr) : ℝ) : ℂ) := by
    rw [xyDual3ChordBilinear_eq_scaledInverse hβ]
    push_cast
    ring
  have hchi := xyDual3Chi0_eq_chordGaussian
    (le_of_lt hβ) ρ
  rw [xyDual3ChordCurrentEquiv_chord k] at hchi
  have hgauss : Complex.exp (-(Real.pi : ℂ) *
      xyDual3ComplexBilinear A⁻¹ kr kr) = xyDual3Chi0 (le_of_lt hβ) ρ := by
    rw [hkk]
    convert hchi.symm using 1
    all_goals
      congr 1
      push_cast
      simp only [kr]
      dsimp [K]
  have hRightScale :
      dotProduct kr (K⁻¹.mulVec ((-(2 * Real.pi * β)⁻¹) • σ)) =
        (-(2 * Real.pi * β)⁻¹) * dotProduct kr (K⁻¹.mulVec σ) := by
    calc
      _ = dotProduct kr ((-(2 * Real.pi * β)⁻¹) • K⁻¹.mulVec σ) := by
            rw [Matrix.mulVec_smul]
      _ = (-(2 * Real.pi * β)⁻¹) •
          dotProduct kr (K⁻¹.mulVec σ) := by
            rw [dotProduct_smul]
      _ = _ := by simp [smul_eq_mul]
  have hkw : xyDual3ComplexBilinear A⁻¹ kr wr =
      -((dotProduct kr (K⁻¹.mulVec σ) : ℝ) : ℂ) := by
    rw [xyDual3ChordBilinear_eq_scaledInverse hβ]
    rw [hwr, hRightScale]
    push_cast
    field_simp [Real.pi_ne_zero, ne_of_gt hβ]
  have hmixed : -(Real.pi : ℂ) * Complex.I *
      (xyDual3ComplexBilinear A⁻¹ wr kr +
        xyDual3ComplexBilinear A⁻¹ kr wr) =
      Complex.I * (2 * Real.pi : ℂ) * ((inner ℝ μ.1 τ.1 : ℝ) : ℂ) := by
    rw [hcomm, hkw, hpairK]
    ring
  have hparam : (fun i => (wr i : ℂ)) =
      realTiltParameter σ (-β⁻¹) := by
    funext c
    simp [wr, realTiltParameter]
  have hexpand := xyDual3DualQuadraticExp_real A wr k
  rw [hparam, hww, hgauss, hmixed] at hexpand
  unfold xyDual3PathPhase
  change dualQuadraticExp A (realTiltParameter σ (-β⁻¹)) k =
    Complex.exp ((inner ℝ (xyDual3PathSourceCoClosed x y).1
      (xyDual3PathTau x y).1 : ℝ) / (2 * β)) *
      (xyDual3Chi0 (le_of_lt hβ) ρ * Complex.exp
        (Complex.I * (2 * Real.pi : ℂ) *
          ((inner ℝ μ.1 (xyDual3PathTau x y).1 : ℝ) : ℂ)))
  calc
    _ = Complex.exp ((inner ℝ (xyDual3PathSourceCoClosed x y).1
          (xyDual3PathTau x y).1 : ℝ) / (2 * β)) *
        xyDual3Chi0 (le_of_lt hβ) ρ *
          Complex.exp (Complex.I * (2 * Real.pi : ℂ) *
            ((inner ℝ μ.1 (xyDual3PathTau x y).1 : ℝ) : ℂ)) := by
              simpa only [Complex.ofReal_div, Complex.ofReal_mul,
                Complex.ofReal_ofNat, Complex.ofReal_natCast, τ] using hexpand
    _ = _ := by ring

set_option linter.style.haveILetI false in

theorem xyShiftedCycleGaussianSum_eq_chordPoisson {B : Dual3Box}
    {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    ((xyShiftedCycleGaussianSum β x y : ℝ) : ℂ) =
      xyDual3PoissonConstant (B := B) β *
        Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
          (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) *
        ∑' k : (xyDual3RootedTree B).Chord → ℤ,
          dualQuadraticExp (xyDual3ChordMatrix (B := B) β)
            (realTiltParameter (xyDual3PathChordSource x y) (-β⁻¹)) k := by
  let T := xyDual3RootedTree B
  let path := xyEndpointPathModes x y
  let A := xyDual3ChordMatrix (B := B) β
  let τ := xyDual3PathChordSource x y
  let w := realTiltParameter τ (-β⁻¹)
  let chordWeight : (T.Chord → ℤ) → ℝ := fun n =>
    xyDual3CycleGaussianWeight β path
      (xyDual3CycleOfIntegerLink (T.extendChord n))
  have hchord : Summable chordWeight :=
    xyDual3CycleGaussianWeight_chord_summable hβ x y
  letI : Summable chordWeight := hchord
  have hPoisson := tsum_cexp_neg_quadratic_pi A
    (xyDual3ChordMatrix_posDef hβ) w
  have hPoisson' :
      (∑' n : T.Chord → ℤ, primalQuadraticExp A w n) =
        ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
          ∑' k : T.Chord → ℤ, dualQuadraticExp A w k := by
    simpa [primalQuadraticExp, dualQuadraticExp] using hPoisson
  calc
    ((xyShiftedCycleGaussianSum β x y : ℝ) : ℂ) =
        Complex.ofReal (∑' c : XYEndpointCycleModes (B := B),
          xyDual3CycleGaussianWeight β path c) := by
          rw [xyShiftedCycleGaussianSum_eq_cycleTsum]
    _ = Complex.ofReal (∑' n : T.Chord → ℤ, chordWeight n) := by
          congr 1
          exact xyDual3CycleGaussianWeight_chord_reindex β path
    _ = ∑' n : T.Chord → ℤ, (chordWeight n : ℂ) :=
          Complex.ofReal_tsum (f := chordWeight)
    _ = ∑' n : T.Chord → ℤ,
          Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
            (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) *
            testedPrimalTerm A τ (-β⁻¹) n := by
          apply tsum_congr
          intro n
          simpa [A, τ, path, T] using
            xyDual3CycleGaussianWeight_chord_term hβ x y n
    _ = Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
          (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) *
          ∑' n : T.Chord → ℤ, testedPrimalTerm A τ (-β⁻¹) n := by
          rw [← tsum_mul_left]
    _ = Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
          (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) *
          ∑' n : T.Chord → ℤ, primalQuadraticExp A w n := by
          congr 1
          apply tsum_congr
          intro n
          exact xyDual3TestedPrimalTerm_eq A τ (-β⁻¹) n
    _ = Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
          (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) *
          (((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
            ∑' k : T.Chord → ℤ, dualQuadraticExp A w k) := by
          rw [hPoisson']
    _ = xyDual3PoissonConstant β *
          Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
            (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) *
          ∑' k : T.Chord → ℤ, dualQuadraticExp A w k := by
          simp [xyDual3PoissonConstant, A]
          ring


/-- The corrected three-dimensional Poisson identity, expressed in the grounded dual complex's
integer co-closed currents. The path correction in the exponent is the
residual energy left after the finite-box Hodge projection. -/
theorem xyShiftedCycleGaussianSum_eq_dualPhase {B : Dual3Box}
    {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    ((xyShiftedCycleGaussianSum β x y : ℝ) : ℂ) =
      xyDual3PoissonConstant (B := B) β *
        Complex.exp (-xyDual3ResidualEnergy x y / (2 * β)) *
        ∑' ρ : XYDual3IntegerCirculations B,
          xyDual3PathPhase (le_of_lt hβ) x y ρ := by
  let e := xyDual3ChordCurrentEquiv (B := B)
  let corr : ℂ := Complex.exp
    (((inner ℝ (xyDual3PathSourceCoClosed x y).1
      (xyDual3PathTau x y).1 : ℝ) : ℂ) / (2 * (β : ℂ)))
  have hdualTsum :
      (∑' k : (xyDual3RootedTree B).Chord → ℤ,
        dualQuadraticExp (xyDual3ChordMatrix (B := B) β)
          (realTiltParameter (xyDual3PathChordSource x y) (-β⁻¹)) k) =
        corr * ∑' ρ : XYDual3IntegerCirculations B,
          xyDual3PathPhase (le_of_lt hβ) x y ρ := by
    calc
      _ = ∑' k : (xyDual3RootedTree B).Chord → ℤ,
          corr * xyDual3PathPhase (le_of_lt hβ) x y (e k) := by
            apply tsum_congr
            intro k
            simpa [corr, Complex.ofReal_div, Complex.ofReal_mul,
              Complex.ofReal_ofNat, Complex.ofReal_natCast] using
              xyDual3ChordDualTerm_eq_correctedPhase hβ x y k
      _ = corr * ∑' k : (xyDual3RootedTree B).Chord → ℤ,
          xyDual3PathPhase (le_of_lt hβ) x y (e k) := by
            rw [← tsum_mul_left]
      _ = corr * ∑' ρ : XYDual3IntegerCirculations B,
          xyDual3PathPhase (le_of_lt hβ) x y ρ := by
            congr 1
            exact e.tsum_eq _
  have hexp :
      Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
        (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) * corr =
      Complex.exp (-xyDual3ResidualEnergy x y / (2 * β)) := by
    dsimp [corr]
    rw [← Complex.exp_add]
    congr 1
    dsimp [xyDual3ResidualEnergy]
    field_simp [ne_of_gt hβ]
    rw [Complex.ofReal_sub]
    ring
  calc
    _ = xyDual3PoissonConstant (B := B) β *
        Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
          (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) *
        (corr * ∑' ρ : XYDual3IntegerCirculations B,
          xyDual3PathPhase (le_of_lt hβ) x y ρ) := by
          rw [xyShiftedCycleGaussianSum_eq_chordPoisson hβ x y, hdualTsum]
    _ = xyDual3PoissonConstant (B := B) β *
        (Complex.exp (-(inner ℝ (xyDual3EndpointPathVector x y)
          (xyDual3EndpointPathVector x y) : ℝ) / (2 * β)) * corr) *
        ∑' ρ : XYDual3IntegerCirculations B,
          xyDual3PathPhase (le_of_lt hβ) x y ρ := by ring
    _ = xyDual3PoissonConstant (B := B) β *
        Complex.exp (-xyDual3ResidualEnergy x y / (2 * β)) *
        ∑' ρ : XYDual3IntegerCirculations B,
          xyDual3PathPhase (le_of_lt hβ) x y ρ := by
          rw [hexp]

/-- The dual plaquette field of a zero endpoint path vanishes. -/
theorem xyDual3EndpointPathVector_self {B : Dual3Box} (x : XYSites B) :
    xyDual3EndpointPathVector x x = 0 := by
  have hchain : xyEndpointPath x x = 0 := by
    simp [xyEndpointPath, xyEndpointSource]
  have hstar : xyDual3StarBondVector (0 : RealChain 3 B) = 0 := by
    simp [xyDual3StarBondVector]
  have hcast : castIntegerChain (0 : Chain 3 B) = 0 := by
    simp [castIntegerChain]
  change xyDual3StarBondVector (castIntegerChain (xyEndpointPath x x)) = 0
  rw [hchain, hcast, hstar]

theorem xyDual3PathTau_self {B : Dual3Box} (x : XYSites B) :
    xyDual3PathTau x x = 0 := by
  have hpath := xyDual3EndpointPathVector_self x
  have hsource : xyDual3PathSourceCoClosed x x = 0 := by
    apply Subtype.ext
    simp [xyDual3PathSourceCoClosed, xyDual3PathSource, hpath]
  simp [xyDual3PathTau, hsource]

/-- At equal endpoints the phase is exactly the grounded dual complex's centered characteristic. -/
theorem xyDual3PathPhase_self {B : Dual3Box} {β : ℝ}
    (hβ : 0 ≤ β) (x : XYSites B) (ρ : XYDual3IntegerCirculations B) :
    xyDual3PathPhase hβ x x ρ = xyDual3Chi0 hβ ρ := by
  simp [xyDual3PathPhase, xyDual3PathTau_self x]

/-- The unshifted XY cycle sum is the centered dual phase normalizer. -/
theorem xyCycleGaussianSum_eq_poissonChi0 {B : Dual3Box} {β : ℝ}
    (hβ : 0 < β) (x : XYSites B) :
    ((xyCycleGaussianSum (B := B) β : ℝ) : ℂ) =
      xyDual3PoissonConstant (B := B) β *
        ∑' ρ : XYDual3IntegerCirculations B,
          xyDual3Chi0 (le_of_lt hβ) ρ := by
  have hself : xyShiftedCycleGaussianSum β x x =
      xyCycleGaussianSum (B := B) β := by
    calc
      _ = xyDualPartition β (xyEndpointFrequency x x) :=
        (xyDualPartition_eq_shiftedCycleGaussianSum β x x).symm
      _ = xyDualPartition β (0 : XYSites B → ℤ) := by
        congr 1
        funext z
        simp [xyEndpointFrequency, xyEndpointSource]
      _ = xyCycleGaussianSum (B := B) β :=
        (xyCycleGaussianSum_eq_dualPartition β).symm
  have hzero : xyDual3ResidualEnergy x x = 0 := by
    simp [xyDual3ResidualEnergy, xyDual3PathTau_self x,
      xyDual3EndpointPathVector_self]
  calc
    _ = ((xyShiftedCycleGaussianSum β x x : ℝ) : ℂ) := by
      rw [hself]
    _ = xyDual3PoissonConstant (B := B) β *
        Complex.exp (-xyDual3ResidualEnergy x x / (2 * β)) *
        ∑' ρ : XYDual3IntegerCirculations B,
          xyDual3PathPhase (le_of_lt hβ) x x ρ :=
      xyShiftedCycleGaussianSum_eq_dualPhase hβ x x
    _ = xyDual3PoissonConstant (B := B) β *
        ∑' ρ : XYDual3IntegerCirculations B,
          xyDual3Chi0 (le_of_lt hβ) ρ := by
      rw [hzero]
      simp_rw [xyDual3PathPhase_self (le_of_lt hβ) x]
      simp


theorem xyEndpointCharacterExpectation_eq_dualPhaseRatio {B : Dual3Box}
    {β : ℝ} (hβ : 0 < β) (x y : XYSites B) :
    xyEndpointCharacterExpectation β x y =
      Complex.exp (-xyDual3ResidualEnergy x y / (2 * β)) *
        ((∑' ρ : XYDual3IntegerCirculations B,
            xyDual3PathPhase (le_of_lt hβ) x y ρ) /
          (∑' ρ : XYDual3IntegerCirculations B,
            xyDual3Chi0 (le_of_lt hβ) ρ)) := by
  let N : ℂ := ∑' ρ : XYDual3IntegerCirculations B,
    xyDual3PathPhase (le_of_lt hβ) x y ρ
  let D : ℂ := ∑' ρ : XYDual3IntegerCirculations B,
    xyDual3Chi0 (le_of_lt hβ) ρ
  let C := xyDual3PoissonConstant (B := B) β
  have hratio := xyEndpointCharacterExpectation_eq_shiftedGaussianRatio β hβ x y
  have hnum : (xyShiftedCycleGaussianSum β x y : ℂ) =
      C * Complex.exp (-xyDual3ResidualEnergy x y / (2 * β)) * N := by
    simpa [N, C] using xyShiftedCycleGaussianSum_eq_dualPhase hβ x y
  have hden : (xyCycleGaussianSum (B := B) β : ℂ) = C * D := by
    simpa [D, C] using xyCycleGaussianSum_eq_poissonChi0 hβ y
  have hcycle : (xyCycleGaussianSum (B := B) β : ℂ) ≠ 0 := by
    rw [xyCycleGaussianSum_eq_dualPartition]
    exact_mod_cast (xyDualPartition_zero_pos (B := B) β hβ).ne'
  have hD : D ≠ 0 := by
    intro hD0
    apply hcycle
    rw [hden, hD0]
    simp
  have hCD : C * D ≠ 0 := by
    rw [← hden]
    exact hcycle
  have hC : C ≠ 0 := (mul_ne_zero_iff.mp hCD).1
  rw [hratio, hnum, hden]
  change (C * Complex.exp (-xyDual3ResidualEnergy x y / (2 * β)) * N) /
      (C * D) = Complex.exp (-xyDual3ResidualEnergy x y / (2 * β)) * (N / D)
  field_simp [hC, hD]


end FroehlichSpencer.FS82.XY
