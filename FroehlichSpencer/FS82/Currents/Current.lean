/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.DualStokes
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# FS82 finite dual-lattice currents

Integer currents use the shared `LambdaStarLinks` carrier.

Their physical
real current is scaled by `2π`, as in the source normalization.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents

open Cubical
open FroehlichSpencer.FS82.Gaussian
open scoped InnerProductSpace
noncomputable section

/--
The finite set of oriented links in the dual box.

This is canonical
carrier, not a second link structure.
-/
abbrev Link (B : Cubical.Box 4) := Cubical.LambdaStarLinks B

/-- An integer-valued current on the finite dual-link carrier. -/
abbrev IntegerCurrent (B : Cubical.Box 4) := Cubical.LambdaStarChain B

/-- The current as a finitely supported real coefficient function on all dual
cells, before applying the physical `2π` normalization. -/
@[expose] def realCurrent {B : Cubical.Box 4} (j : IntegerCurrent B) :
    Cubical.DualRealChain 4 B :=
  Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩
    (Finsupp.mapRange (fun n : ℤ => (n : ℝ)) (by simp) j)

/-- The physical current density associated to an integer current, with the
source factor `2π`. -/
@[expose] def physicalCurrent {B : Cubical.Box 4} (j : IntegerCurrent B) :
    Cubical.DualRealChain 4 B :=
  Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩
    (Finsupp.mapRange (fun n : ℤ => (2 * Real.pi) * (n : ℝ)) (by simp) j)

/-!
On degree-one currents, the Euclidean adjoint of `dualExteriorDifference`
is the degree-lowering divergence.

Evaluating it on `SourceDualZeroCells`
restricts the output to the finite `Λ*` vertex carrier from (a).
-/

/-- The finite cubical dual differential represented on its Euclidean cell
space. -/
@[expose] noncomputable def dualExteriorDifferenceEuclidean {B : Cubical.Box 4} :
    EuclideanSpace ℝ (Cubical.DualCell 4 B) →ₗ[ℝ]
      EuclideanSpace ℝ (Cubical.DualCell 4 B) :=
  (finsuppToEuclidean).comp
    (Cubical.dualExteriorDifference.comp euclideanToFinsupp)

theorem euclideanToFinsupp_single {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (r : ℝ) :
    euclideanToFinsupp (EuclideanSpace.single a r) = Finsupp.single a r := by
  ext b
  simp [euclideanToFinsupp_apply, Finsupp.single_apply, eq_comm]

theorem finsuppToEuclidean_single {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (r : ℝ) :
    finsuppToEuclidean (Finsupp.single a r) = EuclideanSpace.single a r := by
  rw [← euclideanToFinsupp_single a r]
  exact finsuppToEuclidean_euclideanToFinsupp _

theorem dualExteriorDifferenceEuclidean_single {B : Cubical.Box 4}
    (v : Cubical.DualCell 4 B) (r : ℝ) :
    dualExteriorDifferenceEuclidean (EuclideanSpace.single v r) =
      finsuppToEuclidean
        (Cubical.dualExteriorDifference (Finsupp.single v r)) := by
  simp [dualExteriorDifferenceEuclidean, euclideanToFinsupp_single]

/-! The adapter's output restriction is isolated here: switching to divergence
on every vertex requires changing only the output carrier from
`SourceDualZeroCells B` to the chosen all-vertex type. -/
@[expose] noncomputable def sourceDualDivergenceOperator {B : Cubical.Box 4} :
    Cubical.DualRealChain 4 B →ₗ[ℝ]
      (Gaussian.SourceDualZeroCells B → ℝ) where
  toFun q := fun v =>
    (dualExteriorDifferenceEuclidean.adjoint (finsuppToEuclidean q)) v.1
  map_add' q r := by
    funext v
    simp [map_add]
  map_smul' a q := by
    funext v
    simp [map_smul]

/-- The finite-vertex divergence of an integer current, obtained by the
degree-lowering adjoint stencil. -/
@[expose] def currentDivergence {B : Cubical.Box 4} (j : IntegerCurrent B)
    (v : Gaussian.SourceDualZeroCells B) : ℝ :=
  sourceDualDivergenceOperator (realCurrent j) v


@[simp] theorem realCurrent_single {B : Cubical.Box 4} (e : Link B) (n : ℤ) :
    realCurrent (Finsupp.single e n) = Finsupp.single e.1 (n : ℝ) := by
  simp [realCurrent]


theorem physicalCurrent_eq_scaled_realCurrent {B : Cubical.Box 4}
    (j : IntegerCurrent B) :
    physicalCurrent j = (2 * Real.pi) • realCurrent j := by
  classical
  ext c
  simp [physicalCurrent, realCurrent, Finsupp.embDomain_apply,
    Finsupp.mapRange, mul_assoc]


theorem realCurrent_add {B : Cubical.Box 4} (j k : IntegerCurrent B) :
    realCurrent (j + k) = realCurrent j + realCurrent k := by
  classical
  ext c
  by_cases h : Cubical.dualCellDegree c = 1
  · simp [realCurrent, Finsupp.embDomain_apply, h, Int.cast_add]
  · simp [realCurrent, Finsupp.embDomain_apply, h]

theorem currentDivergence_add {B : Cubical.Box 4} (j k : IntegerCurrent B)
    (v : Gaussian.SourceDualZeroCells B) :
    currentDivergence (j + k) v = currentDivergence j v + currentDivergence k v := by
  rw [currentDivergence, currentDivergence, currentDivergence,
    realCurrent_add, map_add]
  rfl

theorem currentDivergence_single {B : Cubical.Box 4} (e : Link B) (n : ℤ)
    (v : Gaussian.SourceDualZeroCells B) :
    currentDivergence (Finsupp.single e n) v =
      (Cubical.dualExteriorDifference (Finsupp.single v.1 1) e.1) * (n : ℝ) := by
  rw [currentDivergence, realCurrent_single, sourceDualDivergenceOperator]
  calc
    (dualExteriorDifferenceEuclidean.adjoint
        (finsuppToEuclidean (Finsupp.single e.1 (n : ℝ)))) v.1 =
      inner ℝ (EuclideanSpace.single v.1 (1 : ℝ))
        (dualExteriorDifferenceEuclidean.adjoint
          (finsuppToEuclidean (Finsupp.single e.1 (n : ℝ)))) := by
            rw [EuclideanSpace.inner_single_left]
            simp
    _ = inner ℝ
        (dualExteriorDifferenceEuclidean (EuclideanSpace.single v.1 (1 : ℝ)))
        (finsuppToEuclidean (Finsupp.single e.1 (n : ℝ))) :=
          dualExteriorDifferenceEuclidean.adjoint_inner_right _ _
    _ = (Cubical.dualExteriorDifference (Finsupp.single v.1 1) e.1) * (n : ℝ) := by
          rw [dualExteriorDifferenceEuclidean_single, finsuppToEuclidean_single,
            EuclideanSpace.inner_single_right]
          simp [mul_comm]

/-- Pair a real link field with an integer frequency assignment. -/
@[expose] def currentPhase {B : Cubical.Box 4} (φ : Link B → ℝ)
    (j : Link B → ℤ) : ℝ :=
  ∑ e, φ e * (j e : ℝ)

/-! The source phase pairs the field `α` with the physical current density
`ϱ=2πj`; writing `φ=2πα` converts it to `currentPhase`. -/

/-- The source phase `α(ϱ)=Σ_e α_e ϱ_e` with `ϱ_e=2πj_e`. -/
@[expose] def sourceCurrentPhase {B : Cubical.Box 4}
    (α : Link B → ℝ) (j : Link B → ℤ) : ℝ :=
  ∑ e, α e * ((2 * Real.pi) * (j e : ℝ))

/-- With `φ=2πα`, the integer-frequency phase is the source phase on
`ϱ=2πj`. -/
theorem currentPhase_eq_sourceCurrentPhase {B : Cubical.Box 4}
    (α : Link B → ℝ) (j : Link B → ℤ) :
    currentPhase (fun e => (2 * Real.pi) * α e) j = sourceCurrentPhase α j := by
  unfold currentPhase sourceCurrentPhase
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem currentPhase_add {B : Cubical.Box 4} (φ : Link B → ℝ)
    (j k : Link B → ℤ) :
    currentPhase φ (j + k) = currentPhase φ j + currentPhase φ k := by
  simp [currentPhase, Pi.add_apply, Int.cast_add, mul_add,
    Finset.sum_add_distrib]

theorem currentPhase_sub {B : Cubical.Box 4} (φ : Link B → ℝ)
    (j k : Link B → ℤ) :
    currentPhase φ (j - k) = currentPhase φ j - currentPhase φ k := by
  simp [currentPhase, Pi.sub_apply, Int.cast_sub, mul_sub,
    Finset.sum_sub_distrib]

theorem fixedFrequency_cosinePair_rewrite {B : Cubical.Box 4}
    (φ : Link B → ℝ) (j k : Link B → ℤ) (K₁ K₂ : ℝ) :
    (1 + K₁ * Real.cos (currentPhase φ j)) *
        (1 + K₂ * Real.cos (currentPhase φ k)) =
      (1 / 3 : ℝ) * (1 + 3 * K₁ * Real.cos (currentPhase φ j)) +
        (1 / 3 : ℝ) * (1 + 3 * K₂ * Real.cos (currentPhase φ k)) +
        (1 / 6 : ℝ) *
          (1 + 3 * K₁ * K₂ * Real.cos (currentPhase φ (j - k))) +
        (1 / 6 : ℝ) *
          (1 + 3 * K₁ * K₂ * Real.cos (currentPhase φ (j + k))) := by
  rw [currentPhase_sub, currentPhase_add, Real.cos_sub, Real.cos_add]
  ring


/-- Support of a function-valued current on the finite link carrier. -/
@[expose] def currentSupport {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (j : Cell → ℤ) : Finset Cell :=
  Finset.univ.filter fun e => j e ≠ 0

theorem currentSupport_add_disjoint {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (j k : Cell → ℤ)
    (hdisj : Disjoint (currentSupport j) (currentSupport k)) :
    currentSupport (j + k) = currentSupport j ∪ currentSupport k := by
  ext e
  simp only [currentSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Pi.add_apply, Finset.mem_union]
  constructor
  · intro h
    by_cases hj : j e = 0
    · right
      intro hk
      apply h
      simp [hj, hk]
    · exact Or.inl hj
  · rintro (hj | hk)
    · by_contra hsum
      have hk0 : k e = 0 := by
        by_contra hkne
        have he₁ : e ∈ currentSupport j := by simp [currentSupport, hj]
        have he₂ : e ∈ currentSupport k := by simp [currentSupport, hkne]
        exact (Finset.disjoint_left.mp hdisj) he₁ he₂
      exact hj (by rw [← hsum, hk0]; simp)
    · by_contra hsum
      have hj0 : j e = 0 := by
        by_contra hjne
        have he₁ : e ∈ currentSupport j := by simp [currentSupport, hjne]
        have he₂ : e ∈ currentSupport k := by simp [currentSupport, hk]
        exact (Finset.disjoint_left.mp hdisj) he₁ he₂
      exact hk (by rw [← hsum, hj0]; simp)

theorem currentSupport_neg {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (j : Cell → ℤ) :
    currentSupport (-j) = currentSupport j := by
  ext e
  simp [currentSupport]

theorem currentSupport_sub_disjoint {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (j k : Cell → ℤ)
    (hdisj : Disjoint (currentSupport j) (currentSupport k)) :
    currentSupport (j - k) = currentSupport j ∪ currentSupport k := by
  rw [sub_eq_add_neg, currentSupport_add_disjoint]
  · rw [currentSupport_neg]
  · simpa only [currentSupport_neg] using hdisj

end

end FroehlichSpencer.FS82.Currents

end
