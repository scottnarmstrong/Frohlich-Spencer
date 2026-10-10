/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.Site
public import FroehlichSpencer.Surface.Laplacian
public import FroehlichSpencer.Surface.DirichletLaplacian
public import FroehlichSpencer.Surface.Hamiltonian
public import FroehlichSpencer.Surface.HamiltonianHermitian
public import FroehlichSpencer.Surface.FiniteEigenvalueCount
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.ConfigurationSpace
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Infra.Stieltjes.EigenvalueKernel
public import FroehlichSpencer.Infra.Wegner.Averaging
public import FroehlichSpencer.Infra.Ergodic.Basic

/-!
# Averaged eigenvalue measures of the finite-volume Hamiltonians

Glue between the IDS statement and the generic infrastructure: the cube, the normalized
eigenvalue counting measure of `H_Λ(v)`, the kernel `v ↦ idsMeasure ν Λ v`, and the averaged
Wegner bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set FroehlichSpencer.Infra

namespace FroehlichSpencer.IDS

/--
The cube `[-L, L]^ν` of the IDS statement.
-/
abbrev idsCube (ν L : ℕ) : Finset (Site ν) :=
  Fintype.piFinset fun _ : Fin ν => Finset.Icc (-(L : ℤ)) (L : ℤ)

theorem idsCube_eq_cube (ν L : ℕ) : idsCube ν L = Infra.cube ν L := by
  ext x
  simp [Infra.mem_cube, Fintype.mem_piFinset]

theorem isHermitian_neg_dirichletLaplacian (ν : ℕ) (Λ : Finset (Site ν)) :
    (-dirichletLaplacian ν Λ).IsHermitian := by
  have h := hamiltonian_isHermitian ν Λ 0
  unfold hamiltonian at h
  simpa using h

/-- The normalized eigenvalue counting measure of `H_Λ(v)`. -/
noncomputable def idsMeasure (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) : Measure ℝ :=
  eigenvalueMeasure (hamiltonian_isHermitian ν Λ v)

instance (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) : IsFiniteMeasure (idsMeasure ν Λ v) := by
  unfold idsMeasure; infer_instance

theorem isProbabilityMeasure_idsMeasure (ν : ℕ) {Λ : Finset (Site ν)} (hΛ : Λ.Nonempty)
    (v : Site ν → ℝ) : IsProbabilityMeasure (idsMeasure ν Λ v) := by
  have : Nonempty {x // x ∈ Λ} := hΛ.to_subtype
  unfold idsMeasure
  exact isProbabilityMeasure_eigenvalueMeasure _

theorem idsMeasure_real_Iic (ν : ℕ) (Λ : Finset (Site ν)) (E : ℝ) (v : Site ν → ℝ) :
    (idsMeasure ν Λ v).real (Iic E) = (finiteEigenvalueCount ν Λ E v : ℝ) / Λ.card := by
  unfold idsMeasure
  rw [measureReal_eigenvalueMeasure_Iic]
  simp only [Fintype.card_coe]
  congr 1

/-- The kernel `v ↦ idsMeasure ν Λ v`. -/
noncomputable def idsKernel (ν : ℕ) (Λ : Finset (Site ν)) : Kernel (Site ν → ℝ) ℝ :=
  eigenvalueKernel (isHermitian_neg_dirichletLaplacian ν Λ) (Subtype.val : {x // x ∈ Λ} → Site ν)

theorem idsKernel_apply (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) :
    idsKernel ν Λ v = idsMeasure ν Λ v := by
  unfold idsKernel idsMeasure
  rw [eigenvalueKernel_apply]
  apply eigenvalueMeasure_congr
  unfold hamiltonian
  congr

instance (ν : ℕ) (Λ : Finset (Site ν)) : IsFiniteKernel (idsKernel ν Λ) := by
  unfold idsKernel; infer_instance

theorem measureReal_bind_idsKernel_Ioc_le (ν : ℕ) (Λ : Finset (Site ν)) (law : Measure ℝ)
    [IsProbabilityMeasure law] {δ : ℝ} (hlaw : HasBoundedDensity law δ) {a b : ℝ} (hab : a ≤ b) :
    ((configurationMeasure ν law).bind (idsKernel ν Λ)).real (Ioc a b) ≤ δ⁻¹ * (b - a) := by
  obtain ⟨hδ, g, -, hg, hgb⟩ := hlaw
  have hA := isHermitian_neg_dirichletLaplacian ν Λ
  set ρ : ENNReal := ENNReal.ofReal δ⁻¹ with hρ
  have key : ((configurationMeasure ν law).bind (idsKernel ν Λ)) (Ioc a b) ≤
      ρ * ENNReal.ofReal (b - a) := by
    rw [Measure.bind_apply measurableSet_Ioc (Kernel.aemeasurable _)]
    rcases Λ.eq_empty_or_nonempty with rfl | hne
    · simp [idsKernel, eigenvalueKernel_apply, eigenvalueMeasure_apply _ measurableSet_Ioc]
    have hw := lintegral_eigenvalueCount_add_diagonal_sub_le (ι := Site ν) (Λ := Λ) hA law
      hg (Filter.Eventually.of_forall hgb) a b
    have hcard : (Λ.card : ENNReal) ≠ 0 := by
      exact_mod_cast hne.card_pos.ne'
    have hpt : ∀ v : Site ν → ℝ, idsKernel ν Λ v (Ioc a b) =
        (Λ.card : ENNReal)⁻¹ * ((eigenvalueCount
          (isHermitian_add_diagonal hA fun x : {x // x ∈ Λ} => v x) b -
          eigenvalueCount (isHermitian_add_diagonal hA fun x : {x // x ∈ Λ} => v x) a : ℕ) :
          ENNReal) := by
      intro v
      rw [idsKernel, eigenvalueKernel_apply, eigenvalueMeasure_apply _ measurableSet_Ioc]
      have := eigenvalueCount_add_card_Ioc
        (isHermitian_add_diagonal hA fun x : {x // x ∈ Λ} => v x) hab
      simp only [Fintype.card_coe]
      congr 2
      rw [← this, Nat.add_sub_cancel_left]
      congr
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hcard)]
    calc _ ≤ (Λ.card : ENNReal)⁻¹ * (ρ * ENNReal.ofReal (b - a) * Λ.card) := by
          exact mul_le_mul_right hw _
      _ = _ := by
          rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _),
            mul_one]
  have hfin : ρ * ENNReal.ofReal (b - a) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [Measure.real]
  calc _ ≤ (ρ * ENNReal.ofReal (b - a)).toReal := ENNReal.toReal_mono hfin key
    _ = _ := by
      rw [ENNReal.toReal_mul, hρ, ENNReal.toReal_ofReal (inv_nonneg.mpr hδ.le),
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

end FroehlichSpencer.IDS
