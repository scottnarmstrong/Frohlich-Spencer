/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Lattice.Basic

/-!
# Nearest neighbors in the integer lattice

This module counts Euclidean nearest neighbors on `ℤ^ν`.

The characterization
is motivated by the nearest-neighbor Laplacian in Fröhlich–Spencer (1983),
equation (1.5), transcribed in Fröhlich–Spencer (1983).
-/

@[expose] public section

namespace FroehlichSpencer.Infra.Lattice

/-- Every lattice point has exactly `2 ν` Euclidean nearest neighbors. -/
theorem exists_nearestNeighbors_finset {ν : ℕ} (x : Fin ν → ℤ) :
    ∃ s : Finset (Fin ν → ℤ),
      (∀ y, y ∈ s ↔ ‖latticeCast x - latticeCast y‖ = 1) ∧
      s.card = 2 * ν := by
  classical
  let sign : Fin 2 → ℤ := fun b => if b = 0 then 1 else -1
  let neighbor (i : Fin ν) (b : Fin 2) : Fin ν → ℤ :=
    Function.update x i (x i + sign b)
  let e : (Fin ν × Fin 2) ↪ (Fin ν → ℤ) := {
    toFun := fun p => neighbor p.1 p.2
    inj' := by
      intro p q hpq
      rcases p with ⟨i, b⟩
      rcases q with ⟨j, c⟩
      change neighbor i b = neighbor j c at hpq
      have hval := congrFun hpq i
      by_cases hij : i = j
      · subst j
        have hsign : sign b = sign c := by
          have h := congrFun hpq i
          simpa [neighbor] using h
        have hbc : b = c := by
          fin_cases b <;> fin_cases c <;> simp_all [sign]
        subst c
        rfl
      · have hzero : sign b = 0 := by
          have h : x i + sign b = x i := by
            simpa [neighbor, hij] using hval
          omega
        have hne : sign b ≠ 0 := by fin_cases b <;> simp [sign]
        exact (hne hzero).elim
  }
  let s : Finset (Fin ν → ℤ) := Finset.univ.map e
  have hmem (y : Fin ν → ℤ) : y ∈ s ↔ ‖latticeCast x - latticeCast y‖ = 1 := by
    rw [norm_latticeCast_sub_eq_one_iff]
    constructor
    · intro hy
      rcases Finset.mem_map.mp hy with ⟨⟨i, b⟩, -, hyEq⟩
      change neighbor i b = y at hyEq
      subst y
      refine ⟨i, ?_, ?_⟩
      · change x i - (Function.update x i (x i + sign b)) i = 1 ∨
          x i - (Function.update x i (x i + sign b)) i = -1
        fin_cases b <;> simp [sign]
      · intro j hji
        change x j = (Function.update x i (x i + sign b)) j
        simp [hji]
    · rintro ⟨i, hi, hxy⟩
      rcases hi with hi | hi
      · have hcenter : y i = x i + sign 1 := by simp [sign]; omega
        have hfun : neighbor i 1 = y := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [neighbor, hcenter]
          · simpa [neighbor, hji] using hxy j hji
        exact Finset.mem_map.mpr ⟨(i, 1), Finset.mem_univ _, hfun⟩
      · have hcenter : y i = x i + sign 0 := by simp [sign]; omega
        have hfun : neighbor i 0 = y := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [neighbor, hcenter]
          · simpa [neighbor, hji] using hxy j hji
        exact Finset.mem_map.mpr ⟨(i, 0), Finset.mem_univ _, hfun⟩
  have hcard : s.card = 2 * ν := by
    simp [s, e, Nat.mul_comm]
  exact ⟨s, hmem, hcard⟩

end FroehlichSpencer.Infra.Lattice

end
