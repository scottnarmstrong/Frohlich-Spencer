/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean geometry of the integer lattice

This module records the Euclidean norm of integer lattice points through their
coordinatewise real cast.

The setup is motivated by Fröhlich–Spencer (1983),
where distances on `ℤ^ν` are Euclidean and nearest neighbours differ by one
unit coordinate (Fröhlich–Spencer (1983), equation (1.5)).

## Main results

* `latticeCast`: the coordinatewise real cast into Euclidean space.
* Norm identities, metric properties, and comparison with the coordinate sup.
-/

@[expose] public section

namespace FroehlichSpencer.Infra.Lattice

/-- The coordinatewise real realization of an integer lattice point. -/
noncomputable abbrev latticeCast {ν : ℕ} (x : Fin ν → ℤ) : EuclideanSpace ℝ (Fin ν) :=
  WithLp.toLp 2 fun i => (x i : ℝ)

/-- The square of the Euclidean norm is the sum of the squared coordinate differences. -/
theorem norm_sq_latticeCast_sub {ν : ℕ} (x y : Fin ν → ℤ) :
    ‖latticeCast x - latticeCast y‖ ^ 2 =
      ∑ i, (((x i - y i : ℤ) : ℝ) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [latticeCast, Int.cast_sub]

/-- The coordinatewise real cast preserves subtraction. -/
theorem latticeCast_sub {ν : ℕ} (x y : Fin ν → ℤ) :
    latticeCast (x - y) = latticeCast x - latticeCast y := by
  apply PiLp.ext
  intro i
  simp [latticeCast, Int.cast_sub]

private theorem exists_single_coordinate_of_sum_sq_eq_one {ν : ℕ}
    (z : Fin ν → ℤ) (hsum : ∑ i, ((z i : ℝ) ^ 2) = 1) :
    ∃ i, (z i = 1 ∨ z i = -1) ∧ ∀ j, j ≠ i → z j = 0 := by
  classical
  have htermle (i : Fin ν) : ((z i : ℝ) ^ 2) ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin ν => ((z j : ℝ) ^ 2))
      (fun j hj => sq_nonneg (z j : ℝ)) (Finset.mem_univ i)
    rw [hsum] at h
    exact h
  have hreal (i : Fin ν) : |(z i : ℝ)| ≤ 1 := by
    apply (sq_le_sq₀ (abs_nonneg (z i : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa only [sq_abs, one_pow] using htermle i
  have hnonempty : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    have : (∑ i : Fin ν, ((z i : ℝ) ^ 2)) = 0 := by simp [h]
    rw [hsum] at this
    norm_num at this
  obtain ⟨i, hi⟩ := hnonempty
  have hiBound : -1 ≤ z i ∧ z i ≤ 1 := by
    have habs := abs_le.mp (hreal i)
    constructor
    · exact_mod_cast habs.1
    · exact_mod_cast habs.2
  have hiSign : z i = 1 ∨ z i = -1 := by omega
  have htermEq : ((z i : ℝ) ^ 2) = 1 := by
    rcases hiSign with h | h <;> simp [h]
  have hremain : (∑ j ∈ Finset.univ.erase i, ((z j : ℝ) ^ 2)) = 0 := by
    have hdecomp := Finset.sum_erase_add (Finset.univ : Finset (Fin ν))
      (fun j : Fin ν => ((z j : ℝ) ^ 2)) (Finset.mem_univ i)
    have hsum' := hsum
    rw [← hdecomp, htermEq] at hsum'
    linarith
  have hzero (j : Fin ν) (hji : j ≠ i) : z j = 0 := by
    have hjzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k hk => sq_nonneg (z k : ℝ))).mp hremain j
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    have hjcast : (z j : ℝ) = 0 := by nlinarith
    exact_mod_cast hjcast
  exact ⟨i, hiSign, hzero⟩

/-- Unit Euclidean distance is exactly a difference of `±1` at one coordinate. -/
theorem norm_latticeCast_sub_eq_one_iff {ν : ℕ} (x y : Fin ν → ℤ) :
    ‖latticeCast x - latticeCast y‖ = 1 ↔
      ∃ i, (x i - y i = 1 ∨ x i - y i = -1) ∧ ∀ j, j ≠ i → x j = y j := by
  constructor
  · intro h
    let z : Fin ν → ℤ := x - y
    have hnorm : ‖latticeCast z‖ = 1 := by
      simpa [z, latticeCast_sub]
    have hsum : (∑ i : Fin ν, ((z i : ℝ) ^ 2)) = 1 := by
      have hsq := norm_sq_latticeCast_sub z (0 : Fin ν → ℤ)
      have hzero : latticeCast (0 : Fin ν → ℤ) = 0 := by
        apply PiLp.ext
        intro i
        simp
      rw [hzero, sub_zero, hnorm, one_pow] at hsq
      simpa using hsq.symm
    obtain ⟨i, hi, hzero⟩ := exists_single_coordinate_of_sum_sq_eq_one z hsum
    refine ⟨i, ?_, ?_⟩
    · simpa [z] using hi
    · intro j hji
      have h := hzero j hji
      exact sub_eq_zero.mp (show x j - y j = 0 by simpa [z] using h)
  · rintro ⟨i, hi, hxy⟩
    have hsum : (∑ j : Fin ν, (((x j - y j : ℤ) : ℝ) ^ 2)) = 1 := by
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · rcases hi with h | h <;> simp [h]
      · intro j hj hji
        have hzero : x j - y j = 0 := sub_eq_zero.mpr (hxy j hji)
        simp [hzero]
    have hsq := norm_sq_latticeCast_sub x y
    rw [hsum] at hsq
    nlinarith [norm_nonneg (latticeCast x - latticeCast y)]

/-- Euclidean distance is symmetric on the lattice. -/
theorem norm_latticeCast_sub_comm {ν : ℕ} (x y : Fin ν → ℤ) :
    ‖latticeCast x - latticeCast y‖ = ‖latticeCast y - latticeCast x‖ := by
  rw [← norm_neg]
  congr 1
  abel

/-- The Euclidean lattice distance satisfies the triangle inequality. -/
theorem norm_latticeCast_sub_le_add {ν : ℕ} (x y z : Fin ν → ℤ) :
    ‖latticeCast x - latticeCast z‖ ≤
      ‖latticeCast x - latticeCast y‖ + ‖latticeCast y - latticeCast z‖ := by
  calc
    ‖latticeCast x - latticeCast z‖ =
        ‖(latticeCast x - latticeCast y) + (latticeCast y - latticeCast z)‖ := by
          congr 1
          abel
    _ ≤ _ := norm_add_le _ _

/-- The coordinatewise real cast is injective. -/
theorem latticeCast_injective {ν : ℕ} : Function.Injective (latticeCast (ν := ν)) := by
  intro x y h
  funext i
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin ν) => v i) h
  change (x i : ℝ) = (y i : ℝ) at hi
  exact Int.cast_injective hi

/-- The lattice distance vanishes exactly when the lattice points agree. -/
theorem norm_latticeCast_sub_eq_zero_iff {ν : ℕ} (x y : Fin ν → ℤ) :
    ‖latticeCast x - latticeCast y‖ = 0 ↔ x = y := by
  constructor
  · intro h
    apply latticeCast_injective
    exact sub_eq_zero.mp (norm_eq_zero.mp h)
  · rintro rfl
    simp

/-- Every coordinate magnitude is bounded by the Euclidean norm. -/
theorem abs_latticeCast_apply_le_norm {ν : ℕ} (x : Fin ν → ℤ) (i : Fin ν) :
    |(x i : ℝ)| ≤ ‖latticeCast x‖ := by
  simpa [latticeCast, Real.norm_eq_abs] using PiLp.norm_apply_le (latticeCast x) i

/-- The maximum coordinate magnitude is bounded by the Euclidean norm. -/
theorem sup_abs_latticeCast_le_norm {ν : ℕ} (hν : 0 < ν) (x : Fin ν → ℤ) :
    Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩)
      (fun i => |(x i : ℝ)|) ≤ ‖latticeCast x‖ := by
  classical
  apply Finset.sup'_le _ _
  intro i hi
  exact abs_latticeCast_apply_le_norm x i

/-- The Euclidean norm is bounded by `√ν` times the maximum coordinate magnitude. -/
theorem norm_latticeCast_le_sqrt_card_mul_sup {ν : ℕ} (hν : 0 < ν) (x : Fin ν → ℤ) :
    ‖latticeCast x‖ ≤ √(ν : ℝ) *
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩)
        (fun i => |(x i : ℝ)|) := by
  classical
  let hne : (Finset.univ : Finset (Fin ν)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
  let M : ℝ := Finset.univ.sup' hne (fun i : Fin ν => |(x i : ℝ)|)
  have hcoord (i : Fin ν) : |(x i : ℝ)| ≤ M :=
    Finset.le_sup' (f := fun j : Fin ν => |(x j : ℝ)|) (Finset.mem_univ i)
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hcoord ⟨0, by omega⟩)
  have hsum : (∑ i : Fin ν, ((x i : ℝ) ^ 2)) ≤ (ν : ℝ) * M ^ 2 := by
    calc
      (∑ i : Fin ν, ((x i : ℝ) ^ 2)) ≤ ∑ i : Fin ν, M ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (x i : ℝ)) hM).2 (hcoord i)
      _ = (ν : ℝ) * M ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
  rw [show ‖latticeCast x‖ = √(∑ i : Fin ν, ((x i : ℝ) ^ 2)) by
    rw [EuclideanSpace.norm_eq]
    simp]
  calc
    √(∑ i : Fin ν, ((x i : ℝ) ^ 2)) ≤ √((ν : ℝ) * M ^ 2) := Real.sqrt_le_sqrt hsum
    _ = √(ν : ℝ) * M := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM]

end FroehlichSpencer.Infra.Lattice

end
