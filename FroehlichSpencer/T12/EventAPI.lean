/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Events
public import FroehlichSpencer.T12.Lemma52
public import FroehlichSpencer.Multiscale.Measurability
public import FroehlichSpencer.Infra.ProductMeasure

/-!
# Gentle-event API and the `resScale` characterization
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

private theorem eigenvalues_eq_of_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A A' : Matrix n n ℂ} (hA : A.IsHermitian) (hA' : A'.IsHermitian) (h : A = A') :
    hA.eigenvalues = hA'.eigenvalues := by
  subst h
  rfl

private theorem isGentle_congr_of_eqOn {ν : ℕ} (P : Params) (Λ : Finset (Site ν)) (i : ℕ)
    {v w : Site ν → ℝ} (h : ∀ y ∈ Λ, v y = w y) {C : Set (Site ν)}
    (hg : IsGentle P (fun B => B ∩ Λ) i v C) : IsGentle P (fun B => B ∩ Λ) i w C := by
  obtain ⟨hC, hd, he⟩ := hg
  refine ⟨hC, hd, fun j => ?_⟩
  have hB : ∀ y ∈ (fun B => B ∩ Λ) (thicken hC.toFinset (4 * scaleD P.K₀ i)), v y = w y :=
    fun y hy => h y (Finset.mem_inter.1 hy).2
  have e := eigenvalues_eq_of_eq (hamiltonian_isHermitian ν _ v) (hamiltonian_isHermitian ν _ w)
    (hamiltonian_congr _ hB)
  exact le_of_le_of_eq (he j) (by rw [congrFun e j])


theorem singularSetsIn_congr_of_eqOn {ν : ℕ} (P : Params) (Λ : Finset (Site ν))
    {v w : Site ν → ℝ} (h : ∀ y ∈ Λ, v y = w y) (i : ℕ) :
    singularSetsIn P Λ v i = singularSetsIn P Λ w i := by
  induction i with
  | zero =>
    ext x
    change x ∈ singular0 P v ∩ (Λ : Set (Site ν)) ↔ x ∈ singular0 P w ∩ (Λ : Set (Site ν))
    simp only [Set.mem_inter_iff, mem_singular0, Finset.mem_coe]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [← h x h2], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [h x h2], h2⟩
  | succ i ih =>
    ext x
    have key : ∀ {v w : Site ν → ℝ}, (∀ y ∈ Λ, v y = w y) →
        singularSetsIn P Λ v i = singularSetsIn P Λ w i →
        x ∈ singularSetsIn P Λ v (i + 1) → x ∈ singularSetsIn P Λ w (i + 1) := by
      intro v w h ih hx
      unfold singularSetsIn at hx ih ⊢
      rw [mem_singularSetsGen_succ_iff] at hx ⊢
      rw [← ih]
      exact ⟨hx.1, fun hg => hx.2 (isGentle_congr_of_eqOn P Λ i (fun y hy => (h y hy).symm) hg)⟩
    exact ⟨key h ih, key (fun y hy => (h y hy).symm) ih.symm⟩


theorem gentleEventIn_congr_of_eqOn {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) (i : ℕ)
    {v w : Site ν → ℝ} (h : ∀ y ∈ Λ, v y = w y) :
    v ∈ gentleEventIn P Λ D i ↔ w ∈ gentleEventIn P Λ D i := by
  rw [mem_gentleEventIn, mem_gentleEventIn, singularSetsIn_congr_of_eqOn P Λ h i]
  exact and_congr_right fun _ =>
    ⟨isGentle_congr_of_eqOn P Λ i h, isGentle_congr_of_eqOn P Λ i fun y hy => (h y hy).symm⟩


theorem measurableSet_gentleEventIn {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) (i : ℕ) :
    MeasurableSet (gentleEventIn P Λ D i) :=
  measurableSet_isGentleClusterIn P Λ i D


theorem measurableSet_gentleEventAnyIn {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) :
    MeasurableSet (gentleEventAnyIn P Λ D) :=
  MeasurableSet.iUnion fun i => measurableSet_gentleEventIn P Λ D i


theorem dependsOn_gentleEventIn {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) (i : ℕ) :
    Infra.DependsOn (Λ : Set (Site ν)) (gentleEventIn P Λ D i) :=
  Infra.dependsOn_of_measurable_of_invariant (measurableSet_gentleEventIn P Λ D i)
    fun _ _ h => gentleEventIn_congr_of_eqOn P Λ D i fun y hy => h y hy


theorem dependsOn_gentleEventAnyIn {ν : ℕ} (P : Params) (Λ D : Finset (Site ν)) :
    Infra.DependsOn (Λ : Set (Site ν)) (gentleEventAnyIn P Λ D) :=
  MeasurableSet.iUnion fun i => dependsOn_gentleEventIn P Λ D i

private theorem exists_scaleD_ge' {K₀ : ℝ} (hK : 0 < K₀) (a : ℝ) : ∃ j, a ≤ scaleD K₀ j := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (a / K₀) (by norm_num : (1 : ℝ) < 5 / 4)
  refine ⟨j, ?_⟩
  have h1 : a ≤ K₀ * (5 / 4 : ℝ) ^ j := by
    have := (div_lt_iff₀ hK).1 hj
    linarith
  unfold scaleD
  linarith [Real.add_one_le_exp (K₀ * (5 / 4 : ℝ) ^ j)]


theorem isLeast_resScale {ν : ℕ} {K₀ : ℝ} (hK : 0 < K₀) (n : ℕ) :
    IsLeast {j : ℕ | 2 * Real.sqrt ν * 2 ^ n ≤ scaleD K₀ j} (resScale ν K₀ n) := by
  classical
  have h := exists_scaleD_ge' hK (2 * Real.sqrt ν * 2 ^ n)
  have e : resScale ν K₀ n = Nat.find h := by
    unfold resScale
    simp only [h, ↓reduceDIte]
  rw [e]
  exact ⟨Nat.find_spec h, fun j hj => Nat.find_min' h hj⟩


theorem resScale_eq_zero_of_nonpos (ν : ℕ) {K₀ : ℝ} (hK : K₀ ≤ 0) (n : ℕ) :
    resScale ν K₀ n = 0 := by
  classical
  unfold resScale
  split_ifs with h
  · refine (Nat.find_eq_zero h).2 ?_
    obtain ⟨j, hj⟩ := h
    refine hj.trans ?_
    unfold scaleD
    apply Real.exp_le_exp.mpr
    have h1 : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    simp only [pow_zero, mul_one]
    nlinarith
  · rfl

end FroehlichSpencer.T12

end
