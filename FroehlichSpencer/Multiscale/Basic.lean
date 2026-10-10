/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.LatticeLength
public import FroehlichSpencer.Surface.Hamiltonian
public import FroehlichSpencer.Infra.Lattice.Basic
public import FroehlichSpencer.Infra.Lattice.Balls

/-!
# Multiscale basics: scales, site distance, thickening, singular sites

Internal definitions for the multiscale construction of Fröhlich–Spencer (1983), Sect. 2.
-/

@[expose] public section

namespace FroehlichSpencer.Multiscale

/-- Parameters of the multiscale construction (FS83 Sect. 2): the energy `E`, the singular
threshold `Nthr` (FS83 `N(E, δ)`, (2.2)) and the scale parameter `K₀` ((2.4)). -/
structure Params where
  E : ℝ
  Nthr : ℝ
  K₀ : ℝ

/-- FS83 (2.4): `d_i = exp (K₀ (5/4)^i)`. -/
noncomputable def scaleD (K₀ : ℝ) (i : ℕ) : ℝ := Real.exp (K₀ * (5 / 4 : ℝ) ^ i)

/-- FS83 (2.5): `r_i = d_i ^ (5/4)`. -/
noncomputable def scaleR (K₀ : ℝ) (i : ℕ) : ℝ := scaleD K₀ i ^ (5 / 4 : ℝ)

theorem scaleD_pos (K₀ : ℝ) (i : ℕ) : 0 < scaleD K₀ i := Real.exp_pos _

theorem scaleR_pos (K₀ : ℝ) (i : ℕ) : 0 < scaleR K₀ i :=
  Real.rpow_pos_of_pos (scaleD_pos K₀ i) _

theorem scaleR_eq_scaleD_succ (K₀ : ℝ) (i : ℕ) : scaleR K₀ i = scaleD K₀ (i + 1) := by
  unfold scaleR scaleD
  rw [← Real.exp_mul, pow_succ]
  congr 1
  ring

theorem one_le_scaleD {K₀ : ℝ} (hK : 0 ≤ K₀) (i : ℕ) : 1 ≤ scaleD K₀ i := by
  unfold scaleD
  exact Real.one_le_exp (by positivity)

theorem scaleD_strictMono {K₀ : ℝ} (hK : 0 < K₀) : StrictMono (scaleD K₀) := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  unfold scaleD
  apply Real.exp_lt_exp.mpr
  have h : (0 : ℝ) < (5 / 4 : ℝ) ^ i := by positivity
  rw [pow_succ]
  nlinarith [mul_pos hK h]

theorem scaleD_le_scaleR {K₀ : ℝ} (hK : 0 ≤ K₀) (i : ℕ) : scaleD K₀ i ≤ scaleR K₀ i :=
  Real.self_le_rpow_of_one_le (one_le_scaleD hK i) (by norm_num)

theorem scaleD_zero (K₀ : ℝ) : scaleD K₀ 0 = Real.exp K₀ := by
  simp [scaleD]

/-- The Euclidean distance `|x − y|` between lattice sites (FS83). -/
noncomputable def siteDist (ν : ℕ) (x y : Site ν) : ℝ := latticeLength ν (x - y)

theorem siteDist_eq_norm (ν : ℕ) (x y : Site ν) :
    siteDist ν x y = ‖Infra.Lattice.latticeCast x - Infra.Lattice.latticeCast y‖ := by
  have h := Infra.Lattice.norm_sq_latticeCast_sub x y
  unfold siteDist latticeLength
  rw [← Real.sqrt_sq (norm_nonneg (Infra.Lattice.latticeCast x - Infra.Lattice.latticeCast y)),
    h]
  simp

theorem siteDist_nonneg (ν : ℕ) (x y : Site ν) : 0 ≤ siteDist ν x y := by
  rw [siteDist_eq_norm]; exact norm_nonneg _

theorem siteDist_self (ν : ℕ) (x : Site ν) : siteDist ν x x = 0 := by
  rw [siteDist_eq_norm]; simp

theorem siteDist_comm (ν : ℕ) (x y : Site ν) : siteDist ν x y = siteDist ν y x := by
  rw [siteDist_eq_norm, siteDist_eq_norm]
  exact Infra.Lattice.norm_latticeCast_sub_comm x y

theorem siteDist_triangle (ν : ℕ) (x y w : Site ν) :
    siteDist ν x y ≤ siteDist ν x w + siteDist ν w y := by
  simp only [siteDist_eq_norm]
  exact Infra.Lattice.norm_latticeCast_sub_le_add x w y

theorem finite_setOf_siteDist_le (ν : ℕ) (x : Site ν) (R : ℝ) :
    {y | siteDist ν x y ≤ R}.Finite := by
  rcases lt_or_ge R 0 with hR | hR
  · refine Set.Finite.subset (Set.finite_empty) ?_
    intro y hy
    exact absurd (lt_of_le_of_lt hy hR) (not_lt.mpr (siteDist_nonneg ν x y))
  · obtain ⟨s, hs, -⟩ := Infra.Lattice.exists_latticeBall_finset_sub x hR
    refine s.finite_toSet.subset ?_
    intro y hy
    rw [Finset.mem_coe, hs, Infra.Lattice.norm_latticeCast_sub_comm, ← siteDist_eq_norm]
    exact hy

theorem finite_thicken {ν : ℕ} (C : Finset (Site ν)) (R : ℝ) :
    {x : Site ν | ∃ c ∈ C, siteDist ν x c ≤ R}.Finite := by
  have : {x : Site ν | ∃ c ∈ C, siteDist ν x c ≤ R} =
      ⋃ c ∈ C, {x | siteDist ν c x ≤ R} := by
    ext x
    simp [siteDist_comm ν x]
  rw [this]
  exact Set.Finite.biUnion C.finite_toSet fun c _ => finite_setOf_siteDist_le ν c R

/-- The finite thickening `{x | ∃ c ∈ C, |x − c| ≤ R}` of a finite set (FS83 (2.7) uses
`R = 4 d_i`). -/
noncomputable def thicken {ν : ℕ} (C : Finset (Site ν)) (R : ℝ) : Finset (Site ν) :=
  (finite_thicken C R).toFinset

theorem mem_thicken {ν : ℕ} {C : Finset (Site ν)} {R : ℝ} {x : Site ν} :
    x ∈ thicken C R ↔ ∃ c ∈ C, siteDist ν x c ≤ R := by
  simp [thicken]

/-- FS83 (2.2): the singular sites `S₀(v) = {x | |v x − E + 2ν| ≤ N}`. -/
def singular0 {ν : ℕ} (P : Params) (v : Site ν → ℝ) : Set (Site ν) :=
  {x | |v x - P.E + 2 * (ν : ℝ)| ≤ P.Nthr}

theorem mem_singular0 {ν : ℕ} (P : Params) (v : Site ν → ℝ) (x : Site ν) :
    x ∈ singular0 P v ↔ |v x - P.E + 2 * (ν : ℝ)| ≤ P.Nthr := Iff.rfl

theorem hamiltonian_congr {ν : ℕ} (B : Finset (Site ν)) {v w : Site ν → ℝ}
    (h : ∀ y ∈ B, v y = w y) : hamiltonian ν B v = hamiltonian ν B w := by
  classical
  ext x y
  simp only [hamiltonian, Matrix.add_apply, Matrix.diagonal_apply]
  rw [h x.1 x.2]

end FroehlichSpencer.Multiscale

end
