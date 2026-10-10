/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.Normalization
public import FroehlichSpencer.BKT.Fourier.Character
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring

/-!
# Root shear and charge selection for the rooted GFF

This module formalizes KP §2.3.1, Step 1, pp. 11–12: the root-coordinate shear separates the
compact root window from the relative field, so integration in the root coordinate removes every
integer charge with nonzero total charge.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FroehlichSpencer.BKT

universe u v

variable {V : Type u} {E : Type v}

/-- The root-coordinate shear `ψ_v = φ_v`, `ψ_j = φ_j - φ_v` for `j ≠ v`, as in KP §2.3.1,
Step 1. -/
def gffRootShear [DecidableEq V] (root : V) : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) where
  toFun φ j := if j = root then φ j else φ j - φ root
  invFun ψ j := if j = root then ψ j else ψ j + ψ root
  left_inv φ := by
    funext j
    by_cases hj : j = root <;> simp [hj]
  right_inv ψ := by
    funext j
    by_cases hj : j = root <;> simp [hj]
  map_add' φ χ := by
    funext j
    by_cases hj : j = root
    · simp [hj]
    · simp [hj]
      ring
  map_smul' c φ := by
    funext j
    by_cases hj : j = root
    · simp [hj]
    · simp [hj]
      ring

@[simp]
theorem gffRootShear_root [DecidableEq V] (root : V) (φ : V → ℝ) :
    gffRootShear root φ root = φ root := by
  simp [gffRootShear]

@[simp]
theorem gffRootShear_apply_of_ne [DecidableEq V] (root j : V) (φ : V → ℝ)
    (hj : j ≠ root) :
    gffRootShear root φ j = φ j - φ root := by
  simp [gffRootShear, hj]

@[simp]
theorem gffRootShear_symm_root [DecidableEq V] (root : V) (ψ : V → ℝ) :
    (gffRootShear root).symm ψ root = ψ root := by
  simp [gffRootShear]

@[simp]
theorem gffRootShear_symm_apply_of_ne [DecidableEq V] (root j : V) (ψ : V → ℝ)
    (hj : j ≠ root) :
    (gffRootShear root).symm ψ j = ψ j + ψ root := by
  simp [gffRootShear, hj]

/-- The matrix of the simultaneous root shear. -/
def gffRootShearMatrix [DecidableEq V] (root : V) : Matrix V V ℝ :=
  fun i j => if i = root then (if j = root then 1 else 0)
    else if j = root then -1 else if i = j then 1 else 0

/-- A partial shear changes only the rows indexed by `s`; the root row stays fixed. -/
def gffPartialShearMatrix [DecidableEq V] (root : V) (s : Finset V) : Matrix V V ℝ :=
  fun i j => if i ∈ s then (if i = j then 1 else 0) - (if j = root then 1 else 0)
    else if i = j then 1 else 0

private theorem gffPartialShearMatrix_insert [DecidableEq V]
    (root : V) (s : Finset V) (i : V) (hs : root ∉ s) (hi : i ∉ s) :
    gffPartialShearMatrix root (insert i s) =
      (gffPartialShearMatrix root s).updateRow i
        ((gffPartialShearMatrix root s) i + (-1 : ℝ) • (gffPartialShearMatrix root s) root) := by
  ext a b
  by_cases ha : a = i
  · subst a
    simp [gffPartialShearMatrix, hi, hs, eq_comm]
    ring
  · simp [gffPartialShearMatrix, ha]

private theorem gffPartialShearMatrix_det [Fintype V] [DecidableEq V]
    (root : V) (s : Finset V) (hs : root ∉ s) :
    (gffPartialShearMatrix root s).det = 1 := by
  induction s using Finset.induction_on with
  | empty =>
      have hmat : gffPartialShearMatrix root ∅ = (1 : Matrix V V ℝ) := by
        ext i j
        simp [gffPartialShearMatrix, Matrix.one_apply]
      rw [hmat]
      simp
  | @insert i s hi ih =>
      have hs' : root ∉ s := by
        intro hr
        exact hs (Finset.mem_insert_of_mem hr)
      have hir : i ≠ root := by
        intro hir
        subst i
        exact hs (Finset.mem_insert_self _ _)
      rw [gffPartialShearMatrix_insert root s i hs' hi]
      rw [Matrix.det_updateRow_add_smul_self _ hir (-1 : ℝ)]
      exact ih hs'

private theorem gffPartialShearMatrix_full [Fintype V] [DecidableEq V] (root : V) :
    gffPartialShearMatrix root (Finset.univ.erase root) = gffRootShearMatrix root := by
  ext i j
  by_cases hi : i = root
  · subst i
    by_cases hj : j = root
    · subst j
      simp [gffPartialShearMatrix, gffRootShearMatrix]
    · have hj' : root ≠ j := Ne.symm hj
      simp [gffPartialShearMatrix, gffRootShearMatrix, hj, hj']
  · by_cases hj : j = root
    · subst j
      simp [gffPartialShearMatrix, gffRootShearMatrix, hi]
    · by_cases hij : i = j
      · subst j
        simp [gffPartialShearMatrix, gffRootShearMatrix, hi]
      · simp [gffPartialShearMatrix, gffRootShearMatrix, hi, hj, hij]

/-- The root shear has determinant one. -/
theorem gffRootShear_det [Fintype V] [DecidableEq V] (root : V) :
    LinearMap.det (gffRootShear root).toLinearMap = 1 := by
  rw [← LinearMap.det_toMatrix' (gffRootShear root).toLinearMap]
  have hmatrix :
      LinearMap.toMatrix' (gffRootShear root).toLinearMap = gffRootShearMatrix root := by
    ext i j
    by_cases hir : i = root
    · subst i
      by_cases hjr : j = root
      · subst j
        simp [gffRootShear, gffRootShearMatrix, LinearMap.toMatrix'_apply]
      · simp [gffRootShear, gffRootShearMatrix, hjr, LinearMap.toMatrix'_apply]
    · by_cases hjr : j = root
      · subst j
        simp [gffRootShear, gffRootShearMatrix, hir, LinearMap.toMatrix'_apply]
      · by_cases hij : i = j
        · subst j
          simp [gffRootShear, gffRootShearMatrix, hir, LinearMap.toMatrix'_apply]
        · simp [gffRootShear, gffRootShearMatrix, hir, hjr, hij,
            LinearMap.toMatrix'_apply]
  rw [hmatrix, ← gffPartialShearMatrix_full root]
  exact gffPartialShearMatrix_det root (Finset.univ.erase root) (by simp)

/-- The root shear and its inverse preserve Lebesgue volume on the finite field space. -/
theorem measurePreserving_gffRootShear [Fintype V] [DecidableEq V] (root : V) :
    MeasurePreserving (gffRootShear root) (volume : Measure (V → ℝ)) volume := by
  let f : (V → ℝ) →ₗ[ℝ] V → ℝ := (gffRootShear root).toLinearMap
  have hdet : LinearMap.det f = 1 := gffRootShear_det root
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := f) (by rw [hdet]; norm_num)
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  change Measure.map (gffRootShear root) volume = volume
  calc
    Measure.map (gffRootShear root) volume = Measure.map f volume := rfl
    _ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • volume := hmap
    _ = volume := by rw [hdet]; norm_num

private theorem measurePreserving_linearMap_of_det_one [Fintype V] [DecidableEq V]
    (f : (V → ℝ) →ₗ[ℝ] (V → ℝ)) (hdet : LinearMap.det f = 1) :
    MeasurePreserving f (volume : Measure (V → ℝ)) volume := by
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := f) (by rw [hdet]; norm_num)
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  calc
    Measure.map f volume = ENNReal.ofReal |(LinearMap.det f)⁻¹| • volume := hmap
    _ = volume := by rw [hdet]; norm_num

theorem measurePreserving_gffRootShear_symm [Fintype V] [DecidableEq V] (root : V) :
    MeasurePreserving ((gffRootShear root).symm) (volume : Measure (V → ℝ)) volume := by
  have heqdet : (gffRootShear root).det = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det, gffRootShear_det]
    norm_num
  have hdet : LinearMap.det ((gffRootShear root).symm : (V → ℝ) →ₗ[ℝ] V → ℝ) = 1 := by
    rw [← LinearEquiv.coe_inv_det, heqdet]
    norm_num
  exact measurePreserving_linearMap_of_det_one _ hdet

/-- The root-zero representative of a relative field. -/
def gffRootZeroField [DecidableEq V] (root : V) (η : {j : V // j ≠ root} → ℝ) : V → ℝ :=
  fun j => if h : j = root then 0 else η ⟨j, h⟩

/-- The shear's root window is exactly the original root window. -/
theorem gffRootShear_rootWindow [DecidableEq V] (root : V) :
    {ψ : V → ℝ | (gffRootShear root ψ) root ∈ Set.Ico (-Real.pi) Real.pi} =
      gffRootWindow root := by
  ext ψ
  simp [gffRootWindow]

/-- Removing the root coordinate after shearing leaves exactly the original edge differences. -/
theorem energy_eq_rootZero_after_shear [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (root : V) (φ : V → ℝ) :
    G.energy φ = G.energy (gffRootZeroField root (fun j => gffRootShear root φ j)) := by
  unfold Multigraph.energy Multigraph.grad gffRootZeroField
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : G.src e = root <;> by_cases ht : G.tgt e = root <;>
    simp [gffRootShear, hs, ht]

/-- The charge pairing after the root shear splits into total charge times the root coordinate
plus a term depending only on non-root coordinates. -/
theorem pairing_charge_eq_rootCharge_add_rootFree [Fintype V] [DecidableEq V]
    (root : V) (ρ : V → ℤ) (ψ : V → ℝ) :
    Multigraph.pairing ((gffRootShear root).symm ψ) (fun j => (ρ j : ℝ)) =
      (∑ j, (ρ j : ℝ)) * ψ root +
        ∑ j, (if j = root then 0 else ψ j) * (ρ j : ℝ) := by
  unfold Multigraph.pairing
  calc
    ∑ j, ((gffRootShear root).symm ψ j) * (ρ j : ℝ) =
        ∑ j, ((if j = root then 0 else ψ j) + ψ root) * (ρ j : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : j = root
          · subst j
            simp [gffRootShear]
          · simp [gffRootShear, h]
    _ = (∑ j, (if j = root then 0 else ψ j) * (ρ j : ℝ)) +
          (∑ j, ψ root * (ρ j : ℝ)) := by
            calc
              _ = ∑ j, ((if j = root then 0 else ψ j) * (ρ j : ℝ) +
                    ψ root * (ρ j : ℝ)) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
              _ = _ := Finset.sum_add_distrib
    _ = (∑ j, (ρ j : ℝ)) * ψ root +
          ∑ j, (if j = root then 0 else ψ j) * (ρ j : ℝ) := by
            rw [← Finset.mul_sum]
            ring

/-- Reindex the vertices as the root and its complement. -/
def gffRootIndexEquiv [DecidableEq V] (root : V) :
    V ≃ Unit ⊕ {j : V // j ≠ root} where
  toFun j := if h : j = root then Sum.inl () else Sum.inr ⟨j, h⟩
  invFun
    | Sum.inl _ => root
    | Sum.inr j => j.1
  left_inv j := by
    by_cases hj : j = root
    · subst j
      simp
    · simp [hj]
  right_inv x := by
    cases x with
    | inl u => cases u; simp
    | inr j => simp [j.2]

/-- A field is identified with its root value and its other coordinates. -/
def gffRootCoordinatesEquiv [Fintype V] [DecidableEq V] (root : V) :
    (V → ℝ) ≃ᵐ ℝ × ({j : V // j ≠ root} → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Unit ⊕ {j : V // j ≠ root} => ℝ)
      (gffRootIndexEquiv root)).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ {j : V // j ≠ root} => ℝ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
        (MeasurableEquiv.refl _)))

@[simp]
theorem gffRootCoordinatesEquiv_apply [Fintype V] [DecidableEq V]
    (root : V) (ψ : V → ℝ) :
    gffRootCoordinatesEquiv root ψ = (ψ root, fun j => ψ j.1) := by
  ext <;> simp [gffRootCoordinatesEquiv,
    MeasurableEquiv.prodCongr, MeasurableEquiv.coe_piCongrLeft,
    MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.piCongrLeft,
    Equiv.sumPiEquivProdPi, gffRootIndexEquiv]

/-- The root-coordinate reindexing preserves the product Lebesgue measures. -/
theorem measurePreserving_gffRootCoordinatesEquiv [Fintype V] [DecidableEq V]
    (root : V) :
    MeasurePreserving (gffRootCoordinatesEquiv root)
      (volume : Measure (V → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ({j : V // j ≠ root} → ℝ))) := by
  let h₁ : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Unit ⊕ {j : V // j ≠ root} => ℝ) (gffRootIndexEquiv root))
      (volume : Measure (V → ℝ))
      (volume : Measure ((i : Unit ⊕ {j : V // j ≠ root}) → ℝ)) :=
    MeasureTheory.volume_measurePreserving_piCongrLeft _ _
  let h₂ : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Unit ⊕ {j : V // j ≠ root} => ℝ))
      (volume : Measure ((i : Unit ⊕ {j : V // j ≠ root}) → ℝ))
      ((volume : Measure (Unit → ℝ)).prod
        (volume : Measure ({j : V // j ≠ root} → ℝ))) :=
    MeasureTheory.volume_measurePreserving_sumPiEquivProdPi _
  let h₃ : MeasurePreserving
      (Prod.map (MeasurableEquiv.funUnique Unit ℝ) (id : _ → _))
      ((volume : Measure (Unit → ℝ)).prod
        (volume : Measure ({j : V // j ≠ root} → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure ({j : V // j ≠ root} → ℝ))) :=
    (MeasureTheory.volume_preserving_funUnique Unit ℝ).prod
      (MeasurePreserving.id (volume : Measure ({j : V // j ≠ root} → ℝ)))
  exact (h₃.comp h₂).comp h₁

/-- The measurable version of the linear root shear. -/
def gffRootShearMeasurableEquiv [Fintype V] [DecidableEq V] (root : V) :
    (V → ℝ) ≃ᵐ (V → ℝ) :=
  (gffRootShear root).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

/-- The full root decomposition first shears, then separates the root coordinate. -/
def gffRootDecompositionEquiv [Fintype V] [DecidableEq V] (root : V) :
    (V → ℝ) ≃ᵐ ℝ × ({j : V // j ≠ root} → ℝ) :=
  (gffRootShearMeasurableEquiv root).trans (gffRootCoordinatesEquiv root)

@[simp]
theorem gffRootDecompositionEquiv_apply [Fintype V] [DecidableEq V]
    (root : V) (φ : V → ℝ) :
    gffRootDecompositionEquiv root φ = (φ root, fun j => φ j.1 - φ root) := by
  change gffRootCoordinatesEquiv root (gffRootShear root φ) = _
  rw [gffRootCoordinatesEquiv_apply]
  congr 1
  · simp [gffRootShear]
  · funext j
    rw [gffRootShear_apply_of_ne root j.1 φ j.2]

/-- The inverse root-coordinate map reconstructs a field from its root value and relative
coordinates. -/
theorem gffRootDecompositionEquiv_symm_root [Fintype V] [DecidableEq V]
    (root : V) (t : ℝ) (η : {j : V // j ≠ root} → ℝ) :
    (gffRootDecompositionEquiv root).symm (t, η) root = t := by
  have h := congrArg Prod.fst
    ((gffRootDecompositionEquiv root).apply_symm_apply (t, η))
  simpa only [gffRootDecompositionEquiv_apply] using h

/-- At a nonroot vertex, inverse root coordinates add the root value to the relative field. -/
theorem gffRootDecompositionEquiv_symm_apply [Fintype V] [DecidableEq V]
    (root : V) (t : ℝ) (η : {j : V // j ≠ root} → ℝ) (j : {j : V // j ≠ root}) :
    (gffRootDecompositionEquiv root).symm (t, η) j.1 = η j + t := by
  have h := congrArg (fun p : ℝ × ({j : V // j ≠ root} → ℝ) => p.2 j)
    ((gffRootDecompositionEquiv root).apply_symm_apply (t, η))
  have h' : (gffRootDecompositionEquiv root).symm (t, η) j.1 -
      (gffRootDecompositionEquiv root).symm (t, η) root = η j := by
    simpa only [gffRootDecompositionEquiv_apply] using h
  rw [gffRootDecompositionEquiv_symm_root] at h'
  linarith

/-- A constant added to a field does not change its Dirichlet energy. -/
theorem energy_add_const [Fintype E] (G : Multigraph V E) (φ : V → ℝ) (c : ℝ) :
    G.energy (fun j => φ j + c) = G.energy φ := by
  unfold Multigraph.energy Multigraph.grad
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- The inverse root coordinates are the root-zero representative plus a constant field. -/
theorem gffRootDecompositionEquiv_symm_eq_rootZero_add [Fintype V] [DecidableEq V]
    (root : V) (t : ℝ) (η : {j : V // j ≠ root} → ℝ) :
    (gffRootDecompositionEquiv root).symm (t, η) =
      fun j => gffRootZeroField root η j + t := by
  funext j
  by_cases hj : j = root
  · subst j
    simp [gffRootZeroField, gffRootDecompositionEquiv_symm_root]
  · have h := gffRootDecompositionEquiv_symm_apply root t η ⟨j, hj⟩
    simpa [gffRootZeroField, hj] using h

/-- In root coordinates, the GFF energy depends only on the relative field. -/
theorem energy_gffRootDecompositionEquiv_symm [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (root : V) (t : ℝ)
    (η : {j : V // j ≠ root} → ℝ) :
    G.energy ((gffRootDecompositionEquiv root).symm (t, η)) =
      G.energy (gffRootZeroField root η) := by
  rw [gffRootDecompositionEquiv_symm_eq_rootZero_add]
  exact energy_add_const G (gffRootZeroField root η) t

/-- The total integer charge of a vertex charge density. -/
def gffChargeTotal [Fintype V] (ρ : V → ℤ) : ℤ := ∑ j, ρ j

/-- The relative part of a charge pairing in root coordinates. -/
def gffRootFreeChargePairing [Fintype V] [DecidableEq V] (root : V)
    (ρ : V → ℤ) (η : {j : V // j ≠ root} → ℝ) : ℝ :=
  Multigraph.pairing (gffRootZeroField root η) (fun j => (ρ j : ℝ))

/-- The charge pairing splits into the total charge times the root coordinate and a
root-pinned term. -/
theorem pairing_gffRootDecompositionEquiv_symm [Fintype V] [DecidableEq V]
    (root : V) (ρ : V → ℤ) (t : ℝ) (η : {j : V // j ≠ root} → ℝ) :
    Multigraph.pairing ((gffRootDecompositionEquiv root).symm (t, η))
      (fun j => (ρ j : ℝ)) =
      (∑ j, (ρ j : ℝ)) * t + gffRootFreeChargePairing root ρ η := by
  rw [gffRootDecompositionEquiv_symm_eq_rootZero_add]
  unfold Multigraph.pairing gffRootFreeChargePairing
  calc
    (∑ j, (gffRootZeroField root η j + t) * (ρ j : ℝ)) =
        (∑ j, gffRootZeroField root η j * (ρ j : ℝ)) +
          ∑ j, t * (ρ j : ℝ) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = (∑ j, gffRootZeroField root η j * (ρ j : ℝ)) +
        (∑ j, (ρ j : ℝ)) * t := by
          congr 1
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ j, (ρ j : ℝ)) * t +
        ∑ j, gffRootZeroField root η j * (ρ j : ℝ) := by ring

/-- A measurable real observable is invariant under constant shifts when it depends only on
field differences. -/
def GffShiftInvariant (F : (V → ℝ) → ℝ) : Prop :=
  ∀ φ c, F (fun j => φ j + c) = F φ

/-- The unnormalized complex charge integrand for the rooted GFF. -/
noncomputable def gffChargeIntegrand [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (β : ℝ) (root : V) (ρ : V → ℤ)
    (F : (V → ℝ) → ℝ) (φ : V → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((Multigraph.pairing (R := ℝ) φ
    (fun j => (ρ j : ℝ)) : ℝ) : ℂ)) *
    (F φ : ℂ) * (gffDensity G β root φ : ℂ)

/-- In root coordinates, the rooted density depends only on the root window and the relative
field energy. -/
theorem gffDensity_gffRootDecompositionEquiv_symm [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (β : ℝ) (root : V) (t : ℝ)
    (η : {j : V // j ≠ root} → ℝ) :
    gffDensity G β root ((gffRootDecompositionEquiv root).symm (t, η)) =
      Set.indicator (Set.Ico (-Real.pi) Real.pi)
        (fun _ : ℝ => Real.exp (-(β / 2) * G.energy (gffRootZeroField root η))) t := by
  by_cases ht : t ∈ Set.Ico (-Real.pi) Real.pi
  · have hroot : (gffRootDecompositionEquiv root).symm (t, η) root ∈
        Set.Ico (-Real.pi) Real.pi := by
      simpa [gffRootDecompositionEquiv_symm_root] using ht
    rw [gffDensity_of_root_mem G β root _ hroot,
      energy_gffRootDecompositionEquiv_symm, Set.indicator_of_mem ht]
  · have hroot : (gffRootDecompositionEquiv root).symm (t, η) root ∉
        Set.Ico (-Real.pi) Real.pi := by
      simpa [gffRootDecompositionEquiv_symm_root] using ht
    rw [gffDensity_of_root_not_mem G β root _ hroot,
      Set.indicator_of_notMem ht]

/-- The amplitude of a charge in relative root coordinates. -/
noncomputable def gffRootChargeAmplitude [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (β : ℝ) (root : V) (ρ : V → ℤ)
    (F : (V → ℝ) → ℝ) (η : {j : V // j ≠ root} → ℝ) : ℂ :=
  Complex.exp (Complex.I * (gffRootFreeChargePairing root ρ η : ℂ)) *
    (F (gffRootZeroField root η) : ℂ) *
    (Real.exp (-(β / 2) * G.energy (gffRootZeroField root η)) : ℂ)

/-- The charge integrand separates into a root character and a relative-field amplitude. -/
theorem gffChargeIntegrand_gffRootDecompositionEquiv_symm [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (β : ℝ) (root : V) (ρ : V → ℤ)
    (F : (V → ℝ) → ℝ) (hFshift : GffShiftInvariant F) (t : ℝ)
    (η : {j : V // j ≠ root} → ℝ) :
    gffChargeIntegrand G β root ρ F ((gffRootDecompositionEquiv root).symm (t, η)) =
      Set.indicator (Set.Ico (-Real.pi) Real.pi)
        (fun t => Complex.exp (Complex.I *
          ((gffChargeTotal ρ : ℝ) * t : ℂ)) *
            gffRootChargeAmplitude G β root ρ F η) t := by
  by_cases ht : t ∈ Set.Ico (-Real.pi) Real.pi
  · have hroot : (gffRootDecompositionEquiv root).symm (t, η) root ∈
        Set.Ico (-Real.pi) Real.pi := by
      simpa [gffRootDecompositionEquiv_symm_root] using ht
    rw [gffChargeIntegrand, pairing_gffRootDecompositionEquiv_symm,
      gffDensity_of_root_mem G β root _ hroot,
      energy_gffRootDecompositionEquiv_symm, Set.indicator_of_mem ht,
      gffRootDecompositionEquiv_symm_eq_rootZero_add, hFshift]
    rw [show (∑ j, (ρ j : ℝ)) = (gffChargeTotal ρ : ℝ) by
      simp [gffChargeTotal]]
    rw [show Complex.I * (((gffChargeTotal ρ : ℝ) * t +
        gffRootFreeChargePairing root ρ η : ℝ) : ℂ) =
        Complex.I * (((gffChargeTotal ρ : ℝ) * t : ℝ) : ℂ) +
          Complex.I * (gffRootFreeChargePairing root ρ η : ℂ) by
      push_cast
      ring]
    rw [Complex.exp_add]
    push_cast
    rw [gffRootChargeAmplitude]
    have hexp : Complex.exp
        (-((β : ℂ) / 2) * (G.energy (gffRootZeroField root η) : ℂ)) =
        (Real.exp (-(β / 2) * G.energy (gffRootZeroField root η)) : ℂ) := by
      rw [show -((β : ℂ) / 2) * (G.energy (gffRootZeroField root η) : ℂ) =
          ((-(β / 2) * G.energy (gffRootZeroField root η) : ℝ) : ℂ) by
        push_cast
        ring, ← Complex.ofReal_exp]
    rw [hexp]
    ring
  · have hroot : (gffRootDecompositionEquiv root).symm (t, η) root ∉
        Set.Ico (-Real.pi) Real.pi := by
      simpa [gffRootDecompositionEquiv_symm_root] using ht
    simp [gffChargeIntegrand, gffDensity_of_root_not_mem G β root _ hroot,
      Set.indicator_of_notMem ht]

/-- The bounded observable and charge character are integrable against the rooted GFF density.
The bound is a pointwise real absolute bound on the observable. -/
theorem integrable_gffChargeIntegrand [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (ρ : V → ℤ) (F : (V → ℝ) → ℝ) (hFmeas : Measurable F)
    (C : ℝ) (hFbounded : ∀ φ, |F φ| ≤ C) :
    Integrable (gffChargeIntegrand G β root ρ F) (volume : Measure (V → ℝ)) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg (F (fun _ => 0)))
    (hFbounded (fun _ => 0))
  have hden := integrable_gffDensity G hG β hβ root
  have hmajor : Integrable (fun φ : V → ℝ => C * gffDensity G β root φ)
      (volume : Measure (V → ℝ)) := hden.const_mul C
  have hmeas : Measurable (gffChargeIntegrand G β root ρ F) := by
    unfold gffChargeIntegrand
    have hpair : Measurable (fun φ : V → ℝ =>
        Multigraph.pairing (R := ℝ) φ (fun j => (ρ j : ℝ))) := by
      unfold Multigraph.pairing
      fun_prop
    have hchar : Measurable (fun φ : V → ℝ => Complex.exp (Complex.I *
        ((Multigraph.pairing (R := ℝ) φ (fun j => (ρ j : ℝ)) : ℝ) : ℂ))) := by
      fun_prop
    exact (hchar.mul hFmeas.complex_ofReal).mul
      (measurable_gffDensity G β root).complex_ofReal
  refine hmajor.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [] with φ
  have hd : 0 ≤ gffDensity G β root φ := gffDensity_nonneg G β root φ
  have hnorm : ‖gffChargeIntegrand G β root ρ F φ‖ = |F φ| * gffDensity G β root φ := by
    simp [gffChargeIntegrand, Complex.norm_exp_I_mul_ofReal,
      Complex.norm_real, abs_of_nonneg hd]
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right (hFbounded φ) hd

/-- The full shear/decomposition map preserves volume. -/
theorem measurePreserving_gffRootDecompositionEquiv [Fintype V] [DecidableEq V]
    (root : V) :
    MeasurePreserving (gffRootDecompositionEquiv root)
      (volume : Measure (V → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ({j : V // j ≠ root} → ℝ))) := by
  unfold gffRootDecompositionEquiv
  exact (measurePreserving_gffRootCoordinatesEquiv root).comp
    (measurePreserving_gffRootShear root)

/-- The inverse root decomposition also preserves volume. -/
theorem measurePreserving_gffRootDecompositionEquiv_symm [Fintype V] [DecidableEq V]
    (root : V) :
    MeasurePreserving (gffRootDecompositionEquiv root).symm
      ((volume : Measure ℝ).prod (volume : Measure ({j : V // j ≠ root} → ℝ)))
      (volume : Measure (V → ℝ)) :=
  MeasurePreserving.symm (gffRootDecompositionEquiv root)
    (measurePreserving_gffRootDecompositionEquiv root)

/-- Integrating a non-neutral integer charge against any bounded measurable shift-invariant
observable gives zero, by root-coordinate character orthogonality (KP §2.3.1, Step 1). -/
theorem gff_integral_charge_eq_zero [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (ρ : V → ℤ) (F : (V → ℝ) → ℝ)
    (hFshift : GffShiftInvariant F) (hFmeas : Measurable F)
    (C : ℝ) (hFbounded : ∀ φ, |F φ| ≤ C)
    (hcharge : gffChargeTotal ρ ≠ 0) :
    (∫ φ, gffChargeIntegrand G β root ρ F φ ∂(volume : Measure (V → ℝ))) = 0 := by
  let e := gffRootDecompositionEquiv root
  have hJ : Integrable (gffChargeIntegrand G β root ρ F)
      (volume : Measure (V → ℝ)) :=
    integrable_gffChargeIntegrand G hG β hβ root ρ F hFmeas C hFbounded
  have hmp := measurePreserving_gffRootDecompositionEquiv root
  have hmpInv := measurePreserving_gffRootDecompositionEquiv_symm root
  have hprod : Integrable
      (fun p : ℝ × ({j : V // j ≠ root} → ℝ) =>
        gffChargeIntegrand G β root ρ F (e.symm p))
      ((volume : Measure ℝ).prod
        (volume : Measure ({j : V // j ≠ root} → ℝ))) := by
    exact (hmpInv.integrable_comp hJ.aestronglyMeasurable).mpr hJ
  have hsection (η : {j : V // j ≠ root} → ℝ) :
      (∫ t : ℝ, gffChargeIntegrand G β root ρ F
        ((gffRootDecompositionEquiv root).symm (t, η)) ∂(volume : Measure ℝ)) = 0 := by
    simp_rw [gffChargeIntegrand_gffRootDecompositionEquiv_symm
      G β root ρ F hFshift]
    rw [integral_indicator measurableSet_Ico, integral_mul_const]
    rw [show (∫ a in Set.Ico (-Real.pi) Real.pi,
        Complex.exp (Complex.I * ((gffChargeTotal ρ : ℝ) * (a : ℝ) : ℂ))) =
        ∫ a in Set.Ico (-Real.pi) Real.pi,
          Complex.exp (Complex.I * (gffChargeTotal ρ : ℂ) * (a : ℂ)) by
      congr 1
      funext a
      congr 1
      push_cast
      ring]
    rw [integral_character_Ico]
    simp [hcharge]
  calc
    (∫ φ, gffChargeIntegrand G β root ρ F φ ∂(volume : Measure (V → ℝ))) =
        ∫ φ, gffChargeIntegrand G β root ρ F (e.symm (e φ))
          ∂(volume : Measure (V → ℝ)) := by
            apply integral_congr_ae
            filter_upwards [] with φ
            congr 1
            exact (e.symm_apply_apply φ).symm
    _ = ∫ p, gffChargeIntegrand G β root ρ F (e.symm p)
          ∂((volume : Measure ℝ).prod
            (volume : Measure ({j : V // j ≠ root} → ℝ))) :=
          hmp.integral_comp' (fun p => gffChargeIntegrand G β root ρ F (e.symm p))
    _ = (∫ η, (∫ t : ℝ, gffChargeIntegrand G β root ρ F
            (e.symm (t, η)) ∂(volume : Measure ℝ))
          ∂(volume : Measure ({j : V // j ≠ root} → ℝ))) :=
          integral_prod_symm _ hprod
    _ = 0 := by
          calc
            _ = ∫ η, (0 : ℂ) ∂(volume : Measure ({j : V // j ≠ root} → ℝ)) := by
              apply integral_congr_ae
              filter_upwards [] with η
              exact hsection η
            _ = 0 := by simp

/-- The complex charge observable without the rooted density factor. -/
noncomputable def gffChargeObservable [Fintype V] [DecidableEq V]
    (ρ : V → ℤ) (F : (V → ℝ) → ℝ) (φ : V → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((Multigraph.pairing (R := ℝ) φ
    (fun j => (ρ j : ℝ)) : ℝ) : ℂ)) * (F φ : ℂ)

/-- The GFF charge integrand is the observable multiplied by its density. -/
theorem gffChargeIntegrand_eq_observable_mul_density [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (β : ℝ) (root : V) (ρ : V → ℤ)
    (F : (V → ℝ) → ℝ) (φ : V → ℝ) :
    gffChargeIntegrand G β root ρ F φ =
      gffChargeObservable ρ F φ * (gffDensity G β root φ : ℂ) := rfl

/-- Integration against the normalized rooted GFF equals integration against its density,
normalized by the partition function, also for complex observables. -/
theorem gffMeasure_complex_integral_eq_div [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (H : (V → ℝ) → ℂ)
    (hH : Integrable (fun φ => H φ * (gffDensity G β root φ : ℂ))
      (volume : Measure (V → ℝ))) :
    Integrable H (gffMeasure G hG β hβ root) ∧
      (∫ φ, H φ ∂gffMeasure G hG β hβ root) =
        (∫ φ, H φ * (gffDensity G β root φ : ℂ)
          ∂(volume : Measure (V → ℝ))) / gffPartitionFunction G β root := by
  have hweight_lt : ∀ᵐ φ ∂(volume : Measure (V → ℝ)),
      ENNReal.ofReal (gffDensity G β root φ) < ⊤ := by
    filter_upwards [] with φ
    exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
  have hcoe : ∀ φ : V → ℝ,
      (ENNReal.ofReal (gffDensity G β root φ)).toReal = gffDensity G β root φ :=
    fun φ => ENNReal.toReal_ofReal (gffDensity_nonneg G β root φ)
  constructor
  · rw [gffMeasure,
      integrable_inv_smul_measure
        (ENNReal.ofReal_ne_zero_iff.mpr (gffPartitionFunction_pos G hG β hβ root))
        ENNReal.ofReal_ne_top,
      gffDensityMeasure]
    rw [integrable_withDensity_iff_integrable_smul'
      ((measurable_gffDensity G β root).ennreal_ofReal) hweight_lt]
    have hfun : (fun φ =>
        (ENNReal.ofReal (gffDensity G β root φ)).toReal • H φ) =
        (fun φ => H φ * (gffDensity G β root φ : ℂ)) := by
      funext φ
      rw [hcoe φ, Complex.real_smul, mul_comm]
    rw [hfun]
    exact hH
  · rw [gffMeasure, integral_smul_measure, gffDensityMeasure,
      integral_withDensity_eq_integral_toReal_smul
        ((measurable_gffDensity G β root).ennreal_ofReal) hweight_lt H]
    rw [integral_congr_ae (ae_of_all _ fun φ => by
      rw [hcoe φ, Complex.real_smul, mul_comm])]
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal
      (le_of_lt (gffPartitionFunction_pos G hG β hβ root))]
    simp only [Complex.real_smul]
    rw [div_eq_mul_inv]
    push_cast
    ring

/-- The normalized GFF expectation of a nonneutral charge times any bounded measurable
shift-invariant real observable is zero (KP §2.3.1, Step 1). -/
theorem gffMeasure_integral_charge_eq_zero [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (ρ : V → ℤ) (F : (V → ℝ) → ℝ)
    (hFshift : GffShiftInvariant F) (hFmeas : Measurable F)
    (C : ℝ) (hFbounded : ∀ φ, |F φ| ≤ C)
    (hcharge : gffChargeTotal ρ ≠ 0) :
    Integrable (gffChargeObservable ρ F) (gffMeasure G hG β hβ root) ∧
      (∫ φ, gffChargeObservable ρ F φ ∂gffMeasure G hG β hβ root) = 0 := by
  have hweighted : Integrable
      (fun φ => gffChargeObservable ρ F φ * (gffDensity G β root φ : ℂ))
      (volume : Measure (V → ℝ)) := by
    convert integrable_gffChargeIntegrand G hG β hβ root ρ F hFmeas C hFbounded using 1
    funext φ
    exact (gffChargeIntegrand_eq_observable_mul_density G β root ρ F φ).symm
  obtain ⟨hobs, hformula⟩ := gffMeasure_complex_integral_eq_div G hG β hβ root
    (gffChargeObservable ρ F) hweighted
  have hEq :
      (∫ φ, gffChargeObservable ρ F φ * (gffDensity G β root φ : ℂ)
        ∂(volume : Measure (V → ℝ))) =
      (∫ φ, gffChargeIntegrand G β root ρ F φ
        ∂(volume : Measure (V → ℝ))) := by
    apply integral_congr_ae
    filter_upwards [] with φ
    exact (gffChargeIntegrand_eq_observable_mul_density G β root ρ F φ).symm
  refine ⟨hobs, ?_⟩
  rw [hformula, hEq,
    gff_integral_charge_eq_zero G hG β hβ root ρ F hFshift hFmeas C
      hFbounded hcharge]
  simp
/-- Under a neutral integer charge, its character is invariant under adding a constant field. -/
theorem gffChargeObservable_character_shift_invariant [Fintype V]
    (ρ : V → ℤ) (hcharge : gffChargeTotal ρ = 0)
    (φ : V → ℝ) (c : ℝ) :
    Complex.exp (Complex.I * ((Multigraph.pairing (R := ℝ)
      (fun j => φ j + c) (fun j => (ρ j : ℝ)) : ℝ) : ℂ)) =
    Complex.exp (Complex.I * ((Multigraph.pairing (R := ℝ)
      φ (fun j => (ρ j : ℝ)) : ℝ) : ℂ)) := by
  have hsum : (∑ j, (ρ j : ℝ)) = 0 := by
    exact_mod_cast hcharge
  have hpair : Multigraph.pairing (R := ℝ)
      (fun j => φ j + c) (fun j => (ρ j : ℝ)) =
      Multigraph.pairing (R := ℝ) φ (fun j => (ρ j : ℝ)) := by
    unfold Multigraph.pairing
    calc
      (∑ j, (φ j + c) * (ρ j : ℝ)) =
          ∑ j, (φ j * (ρ j : ℝ) + c * (ρ j : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ j, φ j * (ρ j : ℝ)) + ∑ j, c * (ρ j : ℝ) :=
            Finset.sum_add_distrib
      _ = (∑ j, φ j * (ρ j : ℝ)) + c * ∑ j, (ρ j : ℝ) := by
            congr 1
            rw [Finset.mul_sum]
      _ = ∑ j, φ j * (ρ j : ℝ) := by rw [hsum]; ring
  rw [hpair]

/-- For a neutral charge, the unnormalized integral is `2π` times the integral over relative
(root-pinned) fields. This is the root-coordinate form of KP §2.3.1, Step 1. -/
theorem gff_integral_neutral_eq_two_pi_pinned [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (ρ : V → ℤ) (F : (V → ℝ) → ℝ)
    (hFshift : GffShiftInvariant F) (hFmeas : Measurable F)
    (C : ℝ) (hFbounded : ∀ φ, |F φ| ≤ C)
    (hcharge : gffChargeTotal ρ = 0) :
    (∫ φ, gffChargeIntegrand G β root ρ F φ ∂(volume : Measure (V → ℝ))) =
      (2 * Real.pi : ℂ) *
        ∫ η : {j : V // j ≠ root} → ℝ,
          gffRootChargeAmplitude G β root ρ F η := by
  let e := gffRootDecompositionEquiv root
  have hJ : Integrable (gffChargeIntegrand G β root ρ F)
      (volume : Measure (V → ℝ)) :=
    integrable_gffChargeIntegrand G hG β hβ root ρ F hFmeas C hFbounded
  have hmp := measurePreserving_gffRootDecompositionEquiv root
  have hmpInv := measurePreserving_gffRootDecompositionEquiv_symm root
  have hprod : Integrable
      (fun p : ℝ × ({j : V // j ≠ root} → ℝ) =>
        gffChargeIntegrand G β root ρ F (e.symm p))
      ((volume : Measure ℝ).prod
        (volume : Measure ({j : V // j ≠ root} → ℝ))) := by
    exact (hmpInv.integrable_comp hJ.aestronglyMeasurable).mpr hJ
  have hsection (η : {j : V // j ≠ root} → ℝ) :
      (∫ t : ℝ, gffChargeIntegrand G β root ρ F
        ((gffRootDecompositionEquiv root).symm (t, η)) ∂(volume : Measure ℝ)) =
        (2 * Real.pi : ℂ) * gffRootChargeAmplitude G β root ρ F η := by
    simp_rw [gffChargeIntegrand_gffRootDecompositionEquiv_symm
      G β root ρ F hFshift]
    rw [integral_indicator measurableSet_Ico, integral_mul_const]
    rw [show (∫ a in Set.Ico (-Real.pi) Real.pi,
        Complex.exp (Complex.I * ((gffChargeTotal ρ : ℝ) * (a : ℝ) : ℂ))) =
        ∫ a in Set.Ico (-Real.pi) Real.pi,
          Complex.exp (Complex.I * (gffChargeTotal ρ : ℂ) * (a : ℂ)) by
      congr 1
      funext a
      congr 1
      push_cast
      ring]
    rw [integral_character_Ico, hcharge]
    simp
  calc
    (∫ φ, gffChargeIntegrand G β root ρ F φ ∂(volume : Measure (V → ℝ))) =
        ∫ φ, gffChargeIntegrand G β root ρ F (e.symm (e φ))
          ∂(volume : Measure (V → ℝ)) := by
            apply integral_congr_ae
            filter_upwards [] with φ
            congr 1
            exact (e.symm_apply_apply φ).symm
    _ = ∫ p, gffChargeIntegrand G β root ρ F (e.symm p)
          ∂((volume : Measure ℝ).prod
            (volume : Measure ({j : V // j ≠ root} → ℝ))) :=
          hmp.integral_comp' (fun p => gffChargeIntegrand G β root ρ F (e.symm p))
    _ = (∫ η, (∫ t : ℝ, gffChargeIntegrand G β root ρ F
            (e.symm (t, η)) ∂(volume : Measure ℝ))
          ∂(volume : Measure ({j : V // j ≠ root} → ℝ))) :=
          integral_prod_symm _ hprod
    _ = (2 * Real.pi : ℂ) *
        ∫ η : {j : V // j ≠ root} → ℝ,
          gffRootChargeAmplitude G β root ρ F η := by
            rw [show (fun η => ∫ t : ℝ, gffChargeIntegrand G β root ρ F
                (e.symm (t, η)) ∂(volume : Measure ℝ)) =
                fun η => (2 * Real.pi : ℂ) * gffRootChargeAmplitude G β root ρ F η by
              funext η
              exact hsection η]
            rw [integral_const_mul]

end FroehlichSpencer.BKT

end
