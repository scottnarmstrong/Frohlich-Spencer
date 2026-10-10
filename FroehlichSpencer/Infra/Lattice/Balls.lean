/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Lattice.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Pi

/-!
# Finite Euclidean balls in the integer lattice

This module counts lattice points in Euclidean balls and finite unions of
neighborhoods.

These estimates are motivated by Fröhlich–Spencer (1983),
equations (1.25)–(1.26) and Condition A, transcribed in
Fröhlich–Spencer (1983).
-/

@[expose] public section

namespace FroehlichSpencer.Infra.Lattice

/-- A Euclidean ball about the origin has an explicit finite coordinate-cube description.
The finset is the coordinate cube `Icc (-⌊R⌋₊) ⌊R⌋₊`, filtered by the Euclidean radius. -/
theorem exists_latticeBall_finset {ν : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : Finset (Fin ν → ℤ),
      (∀ x, x ∈ s ↔ ‖latticeCast x‖ ≤ R) ∧
      s.card ≤ (2 * ⌊R⌋₊ + 1) ^ ν := by
  classical
  let N : ℕ := ⌊R⌋₊
  let I : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let e : (Fin ν → {z : ℤ // z ∈ I}) ↪ (Fin ν → ℤ) := {
    toFun := fun f i => f i
    inj' := by
      intro f g h
      funext i
      apply Subtype.ext
      exact congrFun h i
  }
  let cube : Finset (Fin ν → ℤ) := Finset.univ.map e
  let s : Finset (Fin ν → ℤ) := cube.filter fun x => ‖latticeCast x‖ ≤ R
  have hcardI : I.card = 2 * N + 1 := by
    have h := Int.card_Icc_of_le (-(N : ℤ)) (N : ℤ) (by omega)
    change (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1
    exact_mod_cast (by omega :
      (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1)
  have hcube : cube.card = (2 * N + 1) ^ ν := by
    simp [cube, e, I, hcardI]
  have hcoord (x : Fin ν → ℤ) (hx : ‖latticeCast x‖ ≤ R) (i : Fin ν) :
      x i ∈ I := by
    have hreal : |(x i : ℝ)| ≤ R := (abs_latticeCast_apply_le_norm x i).trans hx
    have hnat : (x i).natAbs ≤ N := by
      rw [Nat.le_floor_iff hR]
      have hcast : ((x i).natAbs : ℝ) = |(x i : ℝ)| := by simp
      rw [hcast]
      exact hreal
    have hnatcast : ((x i).natAbs : ℤ) ≤ N := by exact_mod_cast hnat
    have hup : x i ≤ (x i).natAbs := Int.le_natAbs
    have hlow : -(x i) ≤ (x i).natAbs := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs : -(x i) ≤ (-(x i)).natAbs)
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hmemCube (x : Fin ν → ℤ) (hx : ‖latticeCast x‖ ≤ R) : x ∈ cube := by
    let f : Fin ν → {z : ℤ // z ∈ I} := fun i => ⟨x i, hcoord x hx i⟩
    apply Finset.mem_map.mpr
    refine ⟨f, Finset.mem_univ f, ?_⟩
    funext i
    rfl
  have hs : ∀ x, x ∈ s ↔ ‖latticeCast x‖ ≤ R := by
    intro x
    simp only [s, Finset.mem_filter]
    constructor
    · exact fun hx => hx.2
    · intro hx
      exact ⟨hmemCube x hx, hx⟩
  refine ⟨s, hs, ?_⟩
  calc
    s.card ≤ cube.card := Finset.card_filter_le _ _
    _ = (2 * N + 1) ^ ν := hcube
    _ = (2 * ⌊R⌋₊ + 1) ^ ν := by simp [N]

/-- A translated Euclidean ball has a finite coordinate-cube description with the
same cardinal bound as a ball about the origin. -/
theorem exists_latticeBall_finset_sub {ν : ℕ} (a : Fin ν → ℤ) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ s : Finset (Fin ν → ℤ),
      (∀ x, x ∈ s ↔ ‖latticeCast x - latticeCast a‖ ≤ R) ∧
      s.card ≤ (2 * ⌊R⌋₊ + 1) ^ ν := by
  classical
  obtain ⟨s, hs, hscard⟩ := exists_latticeBall_finset (ν := ν) hR
  let e : Equiv.Perm (Fin ν → ℤ) := Equiv.addRight a
  let t : Finset (Fin ν → ℤ) := s.map e.toEmbedding
  have hecast (x : Fin ν → ℤ) : latticeCast (x + a) = latticeCast x + latticeCast a := by
    apply PiLp.ext
    intro i
    simp [latticeCast, Int.cast_add]
  have ht : ∀ x, x ∈ t ↔ ‖latticeCast x - latticeCast a‖ ≤ R := by
    intro x
    change x ∈ s.map e.toEmbedding ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hx : x = y + a := by
        simpa [e] using hxy.symm
      rw [hx, hecast, add_sub_cancel_right]
      exact hs y |>.mp hy
    · intro hx
      refine ⟨x - a, ?_, ?_⟩
      · apply (hs (x - a)).mpr
        convert hx using 1
        rw [latticeCast_sub]
      · simp [e]
  refine ⟨t, ht, ?_⟩
  simpa [t] using hscard

/-- A closed Euclidean neighborhood of a finite lattice set is finite and is
contained in the union of the corresponding coordinate cubes. -/
theorem exists_latticeNeighborhood_finset {ν : ℕ} (C : Finset (Fin ν → ℤ))
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ s : Finset (Fin ν → ℤ),
      (∀ x, x ∈ s ↔ ∃ c ∈ C, ‖latticeCast x - latticeCast c‖ ≤ r) ∧
      s.card ≤ C.card * (2 * ⌊r⌋₊ + 1) ^ ν := by
  classical
  let balls : (Fin ν → ℤ) → Finset (Fin ν → ℤ) := fun c =>
    (exists_latticeBall_finset_sub c hr).choose
  have hballs (c : Fin ν → ℤ) :
      (∀ x, x ∈ balls c ↔ ‖latticeCast x - latticeCast c‖ ≤ r) ∧
      (balls c).card ≤ (2 * ⌊r⌋₊ + 1) ^ ν :=
    (exists_latticeBall_finset_sub c hr).choose_spec
  let s : Finset (Fin ν → ℤ) := C.biUnion balls
  have hs : ∀ x, x ∈ s ↔ ∃ c ∈ C, ‖latticeCast x - latticeCast c‖ ≤ r := by
    intro x
    simp only [s, Finset.mem_biUnion]
    constructor
    · rintro ⟨c, hc, hx⟩
      exact ⟨c, hc, (hballs c).1 x |>.mp hx⟩
    · rintro ⟨c, hc, hx⟩
      exact ⟨c, hc, (hballs c).1 x |>.mpr hx⟩
  refine ⟨s, hs, ?_⟩
  calc
    s.card ≤ ∑ c ∈ C, (balls c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, (2 * ⌊r⌋₊ + 1) ^ ν := by
      apply Finset.sum_le_sum
      intro c hc
      exact hballs c |>.2
    _ = C.card * (2 * ⌊r⌋₊ + 1) ^ ν := by simp

end FroehlichSpencer.Infra.Lattice

end
