/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.LatticeLength
public import FroehlichSpencer.Infra.Lattice.Balls
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Log

/-! # Dyadic radial shells on the lattice -/

public section

namespace FroehlichSpencer.Reduction

/-- The natural dyadic shell index associated to `|x|/R`. -/
@[expose] noncomputable def dyadicShellIndex (ν : ℕ) (R : ℝ) (x : Site ν) : ℕ :=
  Nat.log 2 ⌊latticeLength ν x / R⌋₊

/-- The scale `R 2^j / 8` used in the proof of Theorem 1.1 from Theorem 1.2. -/
@[expose] noncomputable def dyadicGreenScale (ν : ℕ) (R : ℝ) (x : Site ν) : ℝ :=
  R * (2 : ℝ) ^ dyadicShellIndex ν R x / 8

theorem latticeLength_eq_latticeCast_norm (ν : ℕ) (x : Site ν) :
    latticeLength ν x = ‖Infra.Lattice.latticeCast x‖ := by
  rw [latticeLength]
  rw [show ‖Infra.Lattice.latticeCast x‖ =
      Real.sqrt (∑ i : Fin ν, ((x i : ℝ) ^ 2)) by
        rw [EuclideanSpace.norm_eq]
        simp]

theorem latticeLength_nonneg (ν : ℕ) (x : Site ν) : 0 ≤ latticeLength ν x :=
  Real.sqrt_nonneg _

theorem dyadicShellIndex_floor_bounds {ν : ℕ} {R : ℝ} (hR : 0 < R) (x : Site ν) :
    (⌊latticeLength ν x / R⌋₊ : ℝ) ≤ latticeLength ν x / R ∧
      latticeLength ν x / R < (⌊latticeLength ν x / R⌋₊ : ℝ) + 1 := by
  have hnonneg : 0 ≤ latticeLength ν x / R := div_nonneg (latticeLength_nonneg ν x) hR.le
  refine ⟨Nat.floor_le hnonneg, ?_⟩
  simpa only [Nat.cast_succ] using Nat.lt_succ_floor (latticeLength ν x / R)

theorem dyadicShellIndex_nat_bounds {ν : ℕ} {R : ℝ} (_hR : 0 < R) (x : Site ν)
    (hn : ⌊latticeLength ν x / R⌋₊ ≠ 0) :
    2 ^ dyadicShellIndex ν R x ≤ ⌊latticeLength ν x / R⌋₊ ∧
      ⌊latticeLength ν x / R⌋₊ < 2 ^ (dyadicShellIndex ν R x + 1) := by
  let n := ⌊latticeLength ν x / R⌋₊
  let j := Nat.log 2 n
  have hlow : 2 ^ j ≤ n := by
    exact Nat.pow_le_of_le_log hn le_rfl
  have hhigh : n < 2 ^ (j + 1) := by
    apply (Nat.log_lt_iff_lt_pow Nat.one_lt_two hn).mp
    exact Nat.lt_succ_self j
  exact ⟨by simpa [n, j, dyadicShellIndex] using hlow,
    by simpa [n, j, dyadicShellIndex] using hhigh⟩

theorem dyadicShellIndex_radius_upper {ν : ℕ} {R : ℝ} (hR : 0 < R) (x : Site ν) :
    latticeLength ν x < 3 * R * (2 : ℝ) ^ dyadicShellIndex ν R x := by
  let n := ⌊latticeLength ν x / R⌋₊
  let j := Nat.log 2 n
  have hfloor := dyadicShellIndex_floor_bounds hR x
  have hn0 : 0 ≤ latticeLength ν x := latticeLength_nonneg ν x
  have hupperN : n < 2 ^ (j + 1) := by
    by_cases hn : n = 0
    · simp [j, hn]
    · exact (Nat.log_lt_iff_lt_pow Nat.one_lt_two hn).mp (Nat.lt_succ_self j)
  have hupperR : (n : ℝ) < (2 : ℝ) ^ (j + 1) := by exact_mod_cast hupperN
  have hpow : (2 : ℝ) ^ (j + 1) + 1 ≤ 3 * (2 : ℝ) ^ j := by
    rw [pow_succ]
    have hpos : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have hratio : latticeLength ν x / R < (3 : ℝ) * (2 : ℝ) ^ j := by
    have h₁ : latticeLength ν x / R < (n : ℝ) + 1 := hfloor.2
    exact lt_of_lt_of_le h₁ (le_trans (by linarith) hpow)
  simpa [dyadicShellIndex, j, n, mul_comm, mul_left_comm, mul_assoc] using
    (div_lt_iff₀ hR).mp hratio

theorem dyadicShellIndex_radius_lower {ν : ℕ} {R : ℝ} (hR : 0 < R) (x : Site ν)
    (hn : ⌊latticeLength ν x / R⌋₊ ≠ 0) :
    R * (2 : ℝ) ^ dyadicShellIndex ν R x ≤ latticeLength ν x := by
  have hfloor := dyadicShellIndex_floor_bounds hR x
  have hpow := (dyadicShellIndex_nat_bounds hR x hn).1
  have hcast : (2 : ℝ) ^ dyadicShellIndex ν R x ≤
      (⌊latticeLength ν x / R⌋₊ : ℝ) := by exact_mod_cast hpow
  have hmul := mul_le_mul_of_nonneg_left (hcast.trans hfloor.1) hR.le
  calc
    R * (2 : ℝ) ^ dyadicShellIndex ν R x ≤ R * (latticeLength ν x / R) := hmul
    _ = latticeLength ν x := by field_simp [hR.ne']

theorem dyadicGreenScale_le_inner_outer {ν : ℕ} {R : ℝ} (hR : 0 < R) (x : Site ν) :
    dyadicGreenScale ν R x ≤ R / 8 + latticeLength ν x / 8 := by
  let n := ⌊latticeLength ν x / R⌋₊
  by_cases hn : n = 0
  · have hj : dyadicShellIndex ν R x = 0 := by simp [dyadicShellIndex, n, hn]
    simp [dyadicGreenScale, hj]
    linarith [latticeLength_nonneg ν x]
  · have hlow := dyadicShellIndex_radius_lower hR x hn
    unfold dyadicGreenScale
    have hn' : dyadicGreenScale ν R x ≤ latticeLength ν x / 8 := by
      dsimp [dyadicGreenScale]
      exact (div_le_div_of_nonneg_right hlow (by norm_num : (0 : ℝ) ≤ 8))
    linarith

/-- Sites in one dyadic shell form a finite set, by containment in a lattice ball. -/
theorem finite_dyadicShell (ν : ℕ) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    {x : Site ν | dyadicShellIndex ν R x = j}.Finite := by
  let ρ : ℝ := 3 * R * (2 : ℝ) ^ j
  obtain ⟨B, hB, _hBcard⟩ := Infra.Lattice.exists_latticeBall_finset
    (ν := ν) (show 0 ≤ ρ by positivity)
  have hball : {x : Site ν | ‖Infra.Lattice.latticeCast x‖ ≤ ρ}.Finite :=
    Set.Finite.subset B.finite_toSet (by
      intro x hx
      exact (hB x).2 hx)
  apply hball.subset
  intro x hx
  change dyadicShellIndex ν R x = j at hx
  have hrad := dyadicShellIndex_radius_upper hR x
  have hnorm : latticeLength ν x = ‖Infra.Lattice.latticeCast x‖ :=
    latticeLength_eq_latticeCast_norm ν x
  rw [hx, hnorm] at hrad
  change ‖Infra.Lattice.latticeCast x‖ ≤ ρ
  dsimp [ρ]
  exact hrad.le

/-- A dyadic shell is contained in a ball whose cardinality is at most
`(9 R 2^j)^ν`, for `R ≥ 1`. -/
theorem exists_dyadicShell_ball_finset (ν : ℕ) {R : ℝ} (hR : 1 ≤ R) (j : ℕ) :
    ∃ B : Finset (Site ν),
      (∀ x, dyadicShellIndex ν R x = j → x ∈ B) ∧
      (B.card : ℝ) ≤ (9 * R * (2 : ℝ) ^ j) ^ ν := by
  let ρ : ℝ := 3 * R * (2 : ℝ) ^ j
  have hρ : 0 ≤ ρ := by positivity
  obtain ⟨B, hB, hBcard⟩ := Infra.Lattice.exists_latticeBall_finset (ν := ν) hρ
  have hρone : 1 ≤ ρ := by
    dsimp [ρ]
    have hpow : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    calc
      (1 : ℝ) ≤ 3 := by norm_num
      _ = (3 : ℝ) * 1 * 1 := by ring
      _ ≤ 3 * R * (2 : ℝ) ^ j := by gcongr
  have hfloor : (⌊ρ⌋₊ : ℝ) ≤ ρ := Nat.floor_le hρ
  have hcountBase : (2 * (⌊ρ⌋₊ : ℝ) + 1) ≤ 3 * ρ := by nlinarith
  have hcountCast : (B.card : ℝ) ≤
      ((2 * ⌊ρ⌋₊ + 1 : ℕ) : ℝ) ^ ν := by exact_mod_cast hBcard
  have hcount : (B.card : ℝ) ≤ (3 * ρ) ^ ν := by
    calc
      (B.card : ℝ) ≤ ((2 * ⌊ρ⌋₊ + 1 : ℕ) : ℝ) ^ ν := hcountCast
      _ = (2 * (⌊ρ⌋₊ : ℝ) + 1) ^ ν := by norm_cast
      _ ≤ (3 * ρ) ^ ν := (pow_le_pow_left₀ (by positivity) hcountBase) ν
  refine ⟨B, ?_, ?_⟩
  · intro x hx
    have hrad := dyadicShellIndex_radius_upper (lt_of_lt_of_le zero_lt_one hR) x
    rw [hx] at hrad
    have hnorm : latticeLength ν x = ‖Infra.Lattice.latticeCast x‖ :=
      latticeLength_eq_latticeCast_norm ν x
    rw [hnorm] at hrad
    change x ∈ B
    exact (hB x).2 (by simpa [ρ] using hrad.le)
  · calc
      (B.card : ℝ) ≤ (3 * ρ) ^ ν := hcount
      _ = (9 * R * (2 : ℝ) ^ j) ^ ν := by dsimp [ρ]; congr 1; ring

end FroehlichSpencer.Reduction

end
