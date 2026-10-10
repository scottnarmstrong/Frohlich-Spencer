/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Poisson.TreeGauge
public import FroehlichSpencer.FS82.Poisson.IntegralDuality
public import FroehlichSpencer.FS82.Poisson.FiniteModel
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open Matrix
open scoped BigOperators

namespace FroehlichSpencer.FS82.Poisson

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The real coordinate embedding of tree-gauge chord fields into all links. -/
def chordEmbeddingMatrix (T : RootedTreeGauge V E) : Matrix E T.Chord ℝ :=
  fun e c => if e = c.1 then 1 else 0

@[simp] theorem chordEmbeddingMatrix_mulVec_at_chord (T : RootedTreeGauge V E)
    (x : T.Chord → ℝ) (c : T.Chord) :
    (chordEmbeddingMatrix T *ᵥ x) c.1 = x c := by
  classical
  change dotProduct (fun i : T.Chord => if c.1 = i.1 then 1 else 0) x = x c
  have hcond (i : T.Chord) : c.1 = i.1 ↔ i = c := by
    constructor
    · intro h
      exact Subtype.ext h.symm
    · intro h
      cases h
      rfl
  simp [dotProduct, hcond]

@[simp] theorem chordEmbeddingMatrix_mulVec_at_tree (T : RootedTreeGauge V E)
    (x : T.Chord → ℝ) (w : {x : V // x ≠ T.root}) :
    (chordEmbeddingMatrix T *ᵥ x) (T.treeEdge w) = 0 := by
  classical
  unfold chordEmbeddingMatrix Matrix.mulVec dotProduct
  apply Finset.sum_eq_zero
  intro c hc
  have hne : T.treeEdge w ≠ c.1 := by
    intro h
    exact c.property ⟨w, h⟩
  simp [hne]

/-- Abstract finite gauge quadratic form. `K` is positive semidefinite and
its nullspace is exactly the real coboundary range. -/
structure FinitePoissonModel (T : RootedTreeGauge V E) where
  K : Matrix E E ℝ
  K_posSemidef : K.PosSemidef
  K_kernel_iff_gradient : ∀ x : E → ℝ,
    K *ᵥ x = 0 ↔ ∃ p : V → ℝ, ∀ e, T.coboundary p e = x e

/-- The gauge-fixed positive quadratic form is the chord compression of `K`. -/
def reducedChordMatrix (T : RootedTreeGauge V E) (M : FinitePoissonModel T) :
    Matrix T.Chord T.Chord ℝ :=
  (chordEmbeddingMatrix T)ᴴ * M.K * chordEmbeddingMatrix T

/-- The energy of a tree-zero link field is its compressed chord quadratic
form. -/
theorem reducedChord_energy_eq (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) (x : T.Chord → ℝ) :
    dotProduct x (reducedChordMatrix T M *ᵥ x) =
      dotProduct (chordEmbeddingMatrix T *ᵥ x)
        (M.K *ᵥ (chordEmbeddingMatrix T *ᵥ x)) := by
  change dotProduct x
      (((chordEmbeddingMatrix T)ᴴ * M.K * chordEmbeddingMatrix T) *ᵥ x) = _
  rw [← Matrix.mulVec_mulVec x
    ((chordEmbeddingMatrix T)ᴴ * M.K) (chordEmbeddingMatrix T)]
  rw [← Matrix.mulVec_mulVec (chordEmbeddingMatrix T *ᵥ x)
    (chordEmbeddingMatrix T)ᴴ M.K]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
  calc
    dotProduct x ((chordEmbeddingMatrix T)ᵀ *ᵥ
        (M.K *ᵥ (chordEmbeddingMatrix T *ᵥ x))) =
        dotProduct (M.K *ᵥ (chordEmbeddingMatrix T *ᵥ x))
          (chordEmbeddingMatrix T *ᵥ x) :=
            Matrix.dotProduct_transpose_mulVec _ _ _
    _ = dotProduct (chordEmbeddingMatrix T *ᵥ x)
        (M.K *ᵥ (chordEmbeddingMatrix T *ᵥ x)) := dotProduct_comm _ _

private theorem chordEmbedding_mulVec_injective (T : RootedTreeGauge V E) :
    Function.Injective (chordEmbeddingMatrix T).mulVec := by
  intro x y hxy
  funext c
  have hc := congrFun hxy c.1
  simpa using hc

omit [Fintype V] in
private theorem reducedChordMatrix_psd (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) : (reducedChordMatrix T M).PosSemidef := by
  simpa [reducedChordMatrix] using
    M.K_posSemidef.conjTranspose_mul_mul_same (chordEmbeddingMatrix T)

private theorem reducedChordMatrix_mulVec_injective (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) :
    Function.Injective (reducedChordMatrix T M).mulVec := by
  intro x y hxy
  have hzero : (reducedChordMatrix T M) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hquad : dotProduct (x - y)
      ((reducedChordMatrix T M) *ᵥ (x - y)) = 0 := by simp [hzero]
  let z := chordEmbeddingMatrix T *ᵥ (x - y)
  have hquadK : dotProduct z (M.K *ᵥ z) = 0 := by
    exact (reducedChord_energy_eq T M (x - y)).symm.trans hquad
  have hKzero : M.K *ᵥ z = 0 := by
    exact M.K_posSemidef.dotProduct_mulVec_zero_iff.mp (by simpa using hquadK)
  obtain ⟨p, hp⟩ := (M.K_kernel_iff_gradient z).mp hKzero
  have hpTree (w : {x : V // x ≠ T.root}) :
      T.coboundary p (T.treeEdge w) = 0 := by
    rw [hp]
    exact chordEmbeddingMatrix_mulVec_at_tree T (x - y) w
  have hconst := T.potential_constant_of_tree_zero p hpTree
  have hz : z = 0 := by
    funext e
    change z e = 0
    rw [← hp e]
    unfold RootedTreeGauge.coboundary
    rw [hconst (T.edgeTarget e), hconst (T.edgeSource e)]
    simp
  funext c
  have hc := congrFun hz c.1
  have hcoord : x c - y c = 0 := by simpa [z] using hc
  exact sub_eq_zero.mp hcoord

/-- Positive definiteness of the gauge-fixed chord matrix follows from the
kernel/range identity, rather than being an additional model hypothesis. -/
theorem reducedChordMatrix_posDef (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) : (reducedChordMatrix T M).PosDef := by
  rw [Matrix.PosSemidef.posDef_iff_mulVec_injective (reducedChordMatrix_psd T M)]
  exact reducedChordMatrix_mulVec_injective T M

/-- Source-normalized chord matrix `K_CC/(2πβ)`. -/
noncomputable def scaledChordMatrix (T : RootedTreeGauge V E) (M : FinitePoissonModel T)
    (β : ℝ) : Matrix T.Chord T.Chord ℝ :=
  ((2 * Real.pi * β)⁻¹) • reducedChordMatrix T M

theorem scaledChordMatrix_posDef (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) {β : ℝ} (hβ : 0 < β) :
    (scaledChordMatrix T M β).PosDef := by
  have hc : 0 < (2 * Real.pi * β)⁻¹ := by positivity
  simpa [scaledChordMatrix] using (reducedChordMatrix_posDef T M).smul hc

omit [DecidableEq E] in
private theorem dotProduct_mulVec_eq_mulVec_dotProduct
    (K : Matrix E E ℝ) (hK : K.IsHermitian) (x y : E → ℝ) :
    dotProduct (K *ᵥ x) y = dotProduct x (K *ᵥ y) := by
  classical
  have hsymm (i j : E) : K i j = K j i := by
    have h := congrFun (congrFun hK.eq i) j
    simpa [Matrix.conjTranspose_apply] using h.symm
  simp only [dotProduct, Matrix.mulVec]
  calc
    (∑ i : E, (∑ j : E, K i j * x j) * y i) =
        ∑ i : E, ∑ j : E, (K i j * x j) * y i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
    _ = ∑ j : E, ∑ i : E, (K i j * x j) * y i := by
          rw [Finset.sum_comm]
    _ = ∑ j : E, ∑ i : E, (K j i * y i) * x j := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          rw [hsymm i j]
          ring
    _ = ∑ j : E, x j * (∑ i : E, K j i * y i) := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            _ = (∑ i : E, K j i * y i) * x j := by rw [Finset.sum_mul]
            _ = x j * ∑ i : E, K j i * y i := by ring

omit [Fintype V] in
/-- The transpose of the tree-gauge chord embedding restricts a link field
to its chord coordinates. -/
@[simp] theorem chordEmbeddingTranspose_mulVec_at_chord
    (T : RootedTreeGauge V E) (y : E → ℝ) (c : T.Chord) :
    ((chordEmbeddingMatrix T)ᵀ *ᵥ y) c = y c.1 := by
  classical
  simp [chordEmbeddingMatrix, Matrix.mulVec, dotProduct]

/-- Applying the compressed matrix to chord coordinates is restriction of
the full quadratic operator applied to the corresponding tree-zero field. -/
theorem reducedChord_mulVec_eq_restrict (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) (x : T.Chord → ℝ) :
    reducedChordMatrix T M *ᵥ x =
      T.restrictChord (M.K *ᵥ (chordEmbeddingMatrix T *ᵥ x)) := by
  classical
  funext c
  change (((chordEmbeddingMatrix T)ᴴ * M.K * chordEmbeddingMatrix T) *ᵥ x) c = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
    RootedTreeGauge.restrictChord] using
      chordEmbeddingTranspose_mulVec_at_chord T
        (M.K *ᵥ (chordEmbeddingMatrix T *ᵥ x)) c

/-- The canonical tree-zero representative of the inverse quadratic form on
the co-closed space. -/
noncomputable def finiteModelHodgeRepresentative (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) (j : E → ℝ) : E → ℝ :=
  chordEmbeddingMatrix T *ᵥ
    ((reducedChordMatrix T M)⁻¹ *ᵥ T.restrictChord j)

set_option linter.style.haveILetI false in
/-- The gauge-fixed inverse representative solves the full equation for every
co-closed source. -/
theorem finiteModelHodgeRepresentative_solves (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) {j : E → ℝ} (hj : RootedTreeGauge.CoClosed T j) :
    M.K *ᵥ finiteModelHodgeRepresentative T M j = j := by
  classical
  let A := reducedChordMatrix T M
  let x := A⁻¹ *ᵥ T.restrictChord j
  letI : Invertible A := (reducedChordMatrix_posDef T M).isUnit.invertible
  have hAx : A *ᵥ x = T.restrictChord j := by
    dsimp [x]
    calc
      A *ᵥ (A⁻¹ *ᵥ T.restrictChord j) = (A * A⁻¹) *ᵥ T.restrictChord j := by
        rw [Matrix.mulVec_mulVec]
      _ = T.restrictChord j := by
        rw [Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hKclosed : RootedTreeGauge.CoClosed T
      (M.K *ᵥ finiteModelHodgeRepresentative T M j) := by
    apply (RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries T _).2
    intro p
    change dotProduct (M.K *ᵥ finiteModelHodgeRepresentative T M j)
      (T.coboundary p) = 0
    rw [dotProduct_mulVec_eq_mulVec_dotProduct M.K M.K_posSemidef.isHermitian
      (finiteModelHodgeRepresentative T M j) (T.coboundary p)]
    have hker : M.K *ᵥ T.coboundary p = 0 :=
      (M.K_kernel_iff_gradient (T.coboundary p)).2 ⟨p, fun _ => rfl⟩
    simp [hker]
  have hrestrict : T.restrictChord
      (M.K *ᵥ finiteModelHodgeRepresentative T M j) = T.restrictChord j := by
    change T.restrictChord (M.K *ᵥ
      (chordEmbeddingMatrix T *ᵥ (A⁻¹ *ᵥ T.restrictChord j))) = _
    calc
      _ = reducedChordMatrix T M *ᵥ (A⁻¹ *ᵥ T.restrictChord j) :=
        (reducedChord_mulVec_eq_restrict T M _).symm
      _ = T.restrictChord j := by exact hAx
  calc
    M.K *ᵥ finiteModelHodgeRepresentative T M j =
        RootedTreeGauge.cycleExtension T
          (T.restrictChord (M.K *ᵥ finiteModelHodgeRepresentative T M j)) :=
        (RootedTreeGauge.cycleExtension_restrict_of_coClosed T hKclosed).symm
    _ = RootedTreeGauge.cycleExtension T (T.restrictChord j) := by rw [hrestrict]
    _ = j := RootedTreeGauge.cycleExtension_restrict_of_coClosed T hj

/-- Any co-closed solution of `K u = j` has the same pairing against
co-closed tests as the gauge-fixed representative. -/
theorem finiteModelHodge_pairing_independent_of_gauge
    (T : RootedTreeGauge V E) (M : FinitePoissonModel T)
    {j τ u : E → ℝ}
    (hj : RootedTreeGauge.CoClosed T j)
    (hτ : RootedTreeGauge.CoClosed T τ)
    (hu : M.K *ᵥ u = j) :
    dotProduct τ u = dotProduct τ (finiteModelHodgeRepresentative T M j) := by
  classical
  have hkernel : M.K *ᵥ (u - finiteModelHodgeRepresentative T M j) = 0 := by
    rw [Matrix.mulVec_sub, hu, finiteModelHodgeRepresentative_solves T M hj, sub_self]
  obtain ⟨p, hp⟩ := (M.K_kernel_iff_gradient _).mp hkernel
  have hpair : dotProduct τ (u - finiteModelHodgeRepresentative T M j) = 0 := by
    change (∑ e : E, τ e * (u e - finiteModelHodgeRepresentative T M j e)) = 0
    calc
      _ = ∑ e : E, τ e * T.coboundary p e := by
            apply Finset.sum_congr rfl
            intro e he
            simp [hp e]
      _ = 0 := (RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries T τ).1 hτ p
  have hsub : dotProduct τ u -
      dotProduct τ (finiteModelHodgeRepresentative T M j) = 0 := by
    calc
      _ = ∑ e : E, (τ e * u e -
          τ e * finiteModelHodgeRepresentative T M j e) :=
            (Finset.sum_sub_distrib ..).symm
      _ = ∑ e : E, τ e *
          (u e - finiteModelHodgeRepresentative T M j e) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [mul_sub]
      _ = 0 := hpair
  exact sub_eq_zero.mp hsub

/-- Variational inverse identity on the co-closed space, including the mixed
pairing used by the tested Poisson formula. -/
theorem finiteModel_variational_identity_of_solution
    (T : RootedTreeGauge V E) (M : FinitePoissonModel T)
    {j τ : E → ℝ}
    (hj : RootedTreeGauge.CoClosed T j)
    (hτ : RootedTreeGauge.CoClosed T τ)
    (u : E → ℝ) (hu : M.K *ᵥ u = j) :
    dotProduct τ u = dotProduct (T.restrictChord τ)
      ((reducedChordMatrix T M)⁻¹ *ᵥ T.restrictChord j) := by
  rw [finiteModelHodge_pairing_independent_of_gauge T M hj hτ hu]
  have htree : RootedTreeGauge.InTreeGauge T
      (finiteModelHodgeRepresentative T M j) := by
    intro x
    simp [finiteModelHodgeRepresentative,
      chordEmbeddingMatrix_mulVec_at_tree]
  change (∑ e : E, τ e * finiteModelHodgeRepresentative T M j e) =
    ∑ c : T.Chord, τ c.1 *
      ((reducedChordMatrix T M)⁻¹ *ᵥ T.restrictChord j) c
  rw [RootedTreeGauge.pairing_eq_chordPairing T htree ⟨τ, hτ⟩]
  apply Finset.sum_congr rfl
  intro c hc
  simp [finiteModelHodgeRepresentative,
    chordEmbeddingMatrix_mulVec_at_chord]

/-- The real co-closed subspace, presented by orthogonality to every
rooted-tree coboundary. -/
def finiteModelCoClosedSubmodule (T : RootedTreeGauge V E) :
    Submodule ℝ (E → ℝ) where
  carrier := {j | RootedTreeGauge.OrthogonalToCoboundaries T j}
  zero_mem' := by
    change RootedTreeGauge.OrthogonalToCoboundaries T 0
    intro p
    simp
  add_mem' := by
    intro x y hx hy
    change RootedTreeGauge.OrthogonalToCoboundaries T (x + y)
    intro p
    calc
      (∑ e : E, (x + y) e * T.coboundary p e) =
          (∑ e : E, x e * T.coboundary p e) +
            ∑ e : E, y e * T.coboundary p e := by
              simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      _ = 0 := by rw [hx p, hy p]; simp
  smul_mem' := by
    intro a x hx
    change RootedTreeGauge.OrthogonalToCoboundaries T (a • x)
    intro p
    calc
      (∑ e : E, (a • x) e * T.coboundary p e) =
          ∑ e : E, a * (x e * T.coboundary p e) := by
            simp only [Pi.smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro e he
            ring
      _ = a * ∑ e : E, x e * T.coboundary p e := by rw [Finset.mul_sum]
      _ = 0 := by rw [hx p]; simp

@[simp] theorem mem_finiteModelCoClosedSubmodule_iff
    (T : RootedTreeGauge V E) (j : E → ℝ) :
    j ∈ finiteModelCoClosedSubmodule T ↔ RootedTreeGauge.CoClosed T j :=
  RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries T j |>.symm

/-- A symmetric gauge quadratic operator maps co-closed forms to co-closed
forms because it annihilates every gradient. -/
theorem finiteModelK_mulVec_coClosed (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) (u : E → ℝ) :
    RootedTreeGauge.CoClosed T (M.K *ᵥ u) := by
  apply (RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries T _).2
  intro p
  change dotProduct (M.K *ᵥ u) (T.coboundary p) = 0
  rw [dotProduct_mulVec_eq_mulVec_dotProduct M.K M.K_posSemidef.isHermitian
    u (T.coboundary p)]
  have hker : M.K *ᵥ T.coboundary p = 0 :=
    (M.K_kernel_iff_gradient (T.coboundary p)).2 ⟨p, fun _ => rfl⟩
  simp [hker]

/-- The restriction of `K` to the co-closed subspace. -/
def finiteModelKOnCoClosed (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) :
    finiteModelCoClosedSubmodule T →ₗ[ℝ] finiteModelCoClosedSubmodule T where
  toFun u := ⟨M.K *ᵥ u.1,
    (mem_finiteModelCoClosedSubmodule_iff T _).2
      (finiteModelK_mulVec_coClosed T M u.1)⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add (M.K.mulVecLin) u.1 v.1
  map_smul' a u := by
    apply Subtype.ext
    exact map_smul (M.K.mulVecLin) a u.1

private theorem finiteModelK_zero_of_coClosed
    (T : RootedTreeGauge V E) (M : FinitePoissonModel T)
    {u : E → ℝ} (hu : RootedTreeGauge.CoClosed T u)
    (hKu : M.K *ᵥ u = 0) : u = 0 := by
  obtain ⟨p, hp⟩ := (M.K_kernel_iff_gradient u).mp hKu
  have hsum : (∑ e : E, u e * u e) = 0 := by
    have horth :=
      (RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries T u).1 hu p
    simpa [hp] using horth
  funext e
  have hle : u e * u e ≤ ∑ i : E, u i * u i := by
    simpa using
      (Finset.single_le_sum
        (s := Finset.univ) (f := fun i : E => u i * u i)
        (fun i hi => mul_self_nonneg (u i)) (Finset.mem_univ e))
  have hzero : u e * u e = 0 := by
    rw [hsum] at hle
    exact le_antisymm hle (mul_self_nonneg _)
  exact mul_self_eq_zero.mp hzero

theorem finiteModelKOnCoClosed_injective
    (T : RootedTreeGauge V E) (M : FinitePoissonModel T) :
    Function.Injective (finiteModelKOnCoClosed T M) := by
  intro u v huv
  have hval := congrArg Subtype.val huv
  change M.K *ᵥ u.1 = M.K *ᵥ v.1 at hval
  have hsub : M.K *ᵥ (u.1 - v.1) = 0 := by
    rw [Matrix.mulVec_sub, hval, sub_self]
  have hu : RootedTreeGauge.CoClosed T (u.1 - v.1) := by
    apply (RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries T _).2
    intro p
    have h := u.2 p
    have h' := v.2 p
    change (∑ e : E, u.1 e * T.coboundary p e) = 0 at h
    change (∑ e : E, v.1 e * T.coboundary p e) = 0 at h'
    calc
      (∑ e : E, (u.1 - v.1) e * T.coboundary p e) =
          ∑ e : E, (u.1 e * T.coboundary p e -
            v.1 e * T.coboundary p e) := by
              apply Finset.sum_congr rfl
              intro e he
              simp only [Pi.sub_apply]
              ring
      _ = (∑ e : E, u.1 e * T.coboundary p e) -
          ∑ e : E, v.1 e * T.coboundary p e := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [h, h']; simp
  have hzero := finiteModelK_zero_of_coClosed T M hu hsub
  apply Subtype.ext
  exact sub_eq_zero.mp hzero

/-- The restriction of `K` to co-closed forms is onto by finite
dimensionality, since its kernel is zero. -/
noncomputable def finiteModelKCoClosedEquiv (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) :
    finiteModelCoClosedSubmodule T ≃ₗ[ℝ] finiteModelCoClosedSubmodule T :=
  LinearEquiv.ofBijective (finiteModelKOnCoClosed T M)
    ⟨finiteModelKOnCoClosed_injective T M,
      LinearMap.injective_iff_surjective.mp
        (finiteModelKOnCoClosed_injective T M)⟩

/-- The inverse of `K` on the real co-closed subspace. -/
noncomputable def finiteModelHodgeInverse (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) (j : finiteModelCoClosedSubmodule T) :
    finiteModelCoClosedSubmodule T :=
  (finiteModelKCoClosedEquiv T M).symm j

/-- The Hodge inverse on the co-closed subspace solves `K u = j`. -/
theorem finiteModelHodgeInverse_solves (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) (j : finiteModelCoClosedSubmodule T) :
    M.K *ᵥ (finiteModelHodgeInverse T M j).1 = j.1 := by
  have h := (finiteModelKCoClosedEquiv T M).apply_symm_apply j
  exact congrArg Subtype.val h

/-- Variational inverse identity on the co-closed space, including its mixed
pairing. This is the finite-model version of `⟨τ, V j⟩` for
`V = (K|_W)⁻¹`. -/
theorem finiteModel_variational_identity
    (T : RootedTreeGauge V E) (M : FinitePoissonModel T)
    (j τ : finiteModelCoClosedSubmodule T) :
    dotProduct τ.1 (finiteModelHodgeInverse T M j).1 =
      dotProduct (T.restrictChord τ.1)
        ((reducedChordMatrix T M)⁻¹ *ᵥ T.restrictChord j.1) := by
  exact finiteModel_variational_identity_of_solution T M
    ((mem_finiteModelCoClosedSubmodule_iff T j.1).1 j.2)
    ((mem_finiteModelCoClosedSubmodule_iff T τ.1).1 τ.2)
    (finiteModelHodgeInverse T M j).1 (finiteModelHodgeInverse_solves T M j)

/-- The finite-model expectation in tree-gauge coordinates, with FS82's
`exp(-⟨n,Kn⟩/(2β))` normalization. -/
noncomputable def finiteModelTestedExpectation (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) (β : ℝ) (τ : T.Chord → ℝ) (t : ℝ) : ℂ :=
  testedExpectation (scaledChordMatrix T M β) τ t

/-- The tested Poisson identity after reducing the finite gauge model to its
positive-definite chord matrix. -/
theorem finiteModel_tested_poisson_ratio (T : RootedTreeGauge V E)
    (M : FinitePoissonModel T) {β : ℝ} (hβ : 0 < β)
    (τ : T.Chord → ℝ) (t : ℝ) :
    finiteModelTestedExpectation T M β τ t =
      (∑' k : T.Chord → ℤ,
        dualQuadraticExp (scaledChordMatrix T M β) (realTiltParameter τ t) k) /
        (xi (scaledChordMatrix T M β) : ℂ) := by
  exact tested_poisson_ratio (scaledChordMatrix T M β)
    (scaledChordMatrix_posDef T M hβ) τ t


end FroehlichSpencer.FS82.Poisson
