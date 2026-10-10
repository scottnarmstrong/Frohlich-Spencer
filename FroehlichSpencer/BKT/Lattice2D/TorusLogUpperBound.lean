/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.TorusFourier
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Int.Interval

/-!
# Logarithmic upper bound for the torus Green function

The proof of KP (6.13) writes the point-source Green difference as a finite
Fourier sum, bounds each mode by its small-angle and reciprocal-frequency
estimates, and sums over square frequency shells.
-/

@[expose] public section

open Finset
open scoped BigOperators Real

namespace FroehlichSpencer.BKT.Lattice2D

variable {n : ℕ} [NeZero n]

/-! ### Integer frequency shells -/

/-- The centered integer square of radius `j`. -/
def latticeSquare (j : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(j : ℤ)) (j : ℤ)) ×ˢ (Finset.Icc (-(j : ℤ)) (j : ℤ))

/-- The square shell at radius `j+1`. -/
def latticeShell (j : ℕ) : Finset (ℤ × ℤ) :=
  latticeSquare (j + 1) \ latticeSquare j

theorem latticeSquare_mono {j k : ℕ} (hjk : j ≤ k) :
    latticeSquare j ⊆ latticeSquare k := by
  intro p hp
  simp only [latticeSquare, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  rcases hp with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

theorem latticeSquare_card (j : ℕ) : (latticeSquare j).card = (2 * j + 1) ^ 2 := by
  rw [latticeSquare, Finset.card_product]
  have hcard : (Finset.Icc (-(j : ℤ)) (j : ℤ)).card = 2 * j + 1 := by
    rw [Int.card_Icc]
    have hnonneg : 0 ≤ (j : ℤ) + 1 - -(j : ℤ) := by omega
    have hcast : (((j : ℤ) + 1 - -(j : ℤ)).toNat : ℤ) = ((2 * j + 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    exact_mod_cast hcast
  rw [hcard]
  ring

theorem latticeShell_card (j : ℕ) : (latticeShell j).card = 8 * (j + 1) := by
  rw [latticeShell, Finset.card_sdiff_of_subset]
  · rw [latticeSquare_card, latticeSquare_card]
    have houter : (2 * (j + 1) + 1) ^ 2 = (2 * j + 1) ^ 2 + 8 * (j + 1) := by ring
    rw [houter]
    omega
  · exact latticeSquare_mono (Nat.le_succ j)

theorem mem_latticeShell_iff (j : ℕ) (p : ℤ × ℤ) :
    p ∈ latticeShell j ↔
      p.1 ∈ Finset.Icc (-((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ) ∧
      p.2 ∈ Finset.Icc (-((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ) ∧
      (p.1 ∉ Finset.Icc (-(j : ℤ)) (j : ℤ) ∨
        p.2 ∉ Finset.Icc (-(j : ℤ)) (j : ℤ)) := by
  simp only [latticeShell, latticeSquare, Finset.mem_sdiff, Finset.mem_product]
  tauto

theorem latticeShell_sq_ge (j : ℕ) (p : ℤ × ℤ) (hp : p ∈ latticeShell j) :
    (((j + 1 : ℕ) : ℝ) ^ 2) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
  rw [mem_latticeShell_iff] at hp
  simp only [Finset.mem_Icc] at hp
  rcases hp with ⟨h₁, h₂, hnot⟩
  have hout (z : ℤ) (hz : -((j + 1 : ℕ) : ℤ) ≤ z ∧ z ≤ (j + 1 : ℕ))
      (hn : ¬ (-(j : ℤ) ≤ z ∧ z ≤ (j : ℤ))) :
      ((j + 1 : ℕ) : ℝ) ^ 2 ≤ (z : ℝ) ^ 2 := by
    rcases not_and_or.mp hn with hlow | hhigh
    · have hz' : (z : ℝ) ≤ -((j + 1 : ℕ) : ℝ) := by exact_mod_cast (show z ≤ -((j + 1 : ℕ) : ℤ) by omega)
      have habs : ((j + 1 : ℕ) : ℝ) ≤ |(z : ℝ)| := by
        rw [abs_of_nonpos (by linarith only [hz'])]
        linarith only [hz']
      have hpow := pow_le_pow_left₀ (by positivity) habs 2
      simpa only [sq_abs] using hpow
    · have hz' : ((j + 1 : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show (j + 1 : ℕ) ≤ z by omega)
      have habs : ((j + 1 : ℕ) : ℝ) ≤ |(z : ℝ)| := le_trans hz' (le_abs_self _)
      have hpow := pow_le_pow_left₀ (by positivity) habs 2
      simpa only [sq_abs] using hpow
  rcases hnot with hnot | hnot
  · have hsq := hout p.1 h₁ hnot
    nlinarith only [hsq, sq_nonneg (p.2 : ℝ)]
  · have hsq := hout p.2 h₂ hnot
    nlinarith only [hsq, sq_nonneg (p.1 : ℝ)]

theorem latticeShell_reciprocal_sum_le (j : ℕ) :
    ∑ p ∈ latticeShell j,
      (1 : ℝ) / ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤
        8 / ((j + 1 : ℕ) : ℝ) := by
  have hterm (p : ℤ × ℤ) (hp : p ∈ latticeShell j) :
      (1 : ℝ) / ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤
        1 / (((j + 1 : ℕ) : ℝ) ^ 2) := by
    have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    exact one_div_le_one_div_of_le (sq_pos_of_pos (by exact_mod_cast hj))
      (latticeShell_sq_ge j p hp)
  calc
    _ ≤ ∑ _ ∈ latticeShell j, 1 / (((j + 1 : ℕ) : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hterm p hp
    _ = ((latticeShell j).card : ℝ) * (1 / (((j + 1 : ℕ) : ℝ) ^ 2)) := by simp
    _ = 8 / ((j + 1 : ℕ) : ℝ) := by
      rw [latticeShell_card]
      push_cast
      field_simp

def latticeRadius (q : ℤ × ℤ) : ℕ := max q.1.natAbs q.2.natAbs

theorem mem_latticeShell_radius {q : ℤ × ℤ} (hq : q ≠ (0, 0)) :
    q ∈ latticeShell (latticeRadius q - 1) := by
  let r := latticeRadius q
  have hr : 0 < r := by
    rcases q with ⟨a, b⟩
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      exact hq (Prod.ext h.1 h.2)
    rcases hab with ha | hb
    · have hna : a.natAbs ≠ 0 := by simp [ha]
      dsimp [r, latticeRadius]
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero hna) (Nat.le_max_left _ _)
    · have hnb : b.natAbs ≠ 0 := by simp [hb]
      dsimp [r, latticeRadius]
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero hnb) (Nat.le_max_right _ _)
  have ha : q.1.natAbs ≤ r := by dsimp [r, latticeRadius]; exact Nat.le_max_left _ _
  have hb : q.2.natAbs ≤ r := by dsimp [r, latticeRadius]; exact Nat.le_max_right _ _
  have hqa : |q.1| ≤ (r : ℤ) := by
    have h := (show (q.1.natAbs : ℤ) ≤ (r : ℤ) by exact_mod_cast ha)
    simpa only [Int.natCast_natAbs] using h
  have hqb : |q.2| ≤ (r : ℤ) := by
    have h := (show (q.2.natAbs : ℤ) ≤ (r : ℤ) by exact_mod_cast hb)
    simpa only [Int.natCast_natAbs] using h
  have houter : q ∈ latticeSquare r := by
    simp only [latticeSquare, Finset.mem_product, Finset.mem_Icc]
    exact ⟨abs_le.mp hqa, abs_le.mp hqb⟩
  have hnot : q ∉ latticeSquare (r - 1) := by
    intro h
    simp only [latticeSquare, Finset.mem_product, Finset.mem_Icc] at h
    have h1 : q.1.natAbs ≤ r - 1 := by
      have habs : |q.1| ≤ ((r - 1 : ℕ) : ℤ) := abs_le.mpr h.1
      have hcast : (q.1.natAbs : ℤ) ≤ ((r - 1 : ℕ) : ℤ) := by
        simpa only [Int.natCast_natAbs] using habs
      exact_mod_cast hcast
    have h2 : q.2.natAbs ≤ r - 1 := by
      have habs : |q.2| ≤ ((r - 1 : ℕ) : ℤ) := abs_le.mpr h.2
      have hcast : (q.2.natAbs : ℤ) ≤ ((r - 1 : ℕ) : ℤ) := by
        simpa only [Int.natCast_natAbs] using habs
      exact_mod_cast hcast
    have hmax : r ≤ r - 1 := by
      dsimp [r, latticeRadius]
      exact max_le h1 h2
    dsimp [r] at hmax
    omega
  simpa [latticeShell, r, Nat.sub_add_cancel hr] using And.intro houter hnot

/-! ### Continuous frequency estimates -/

/-- The real Fourier angle for an integer frequency coordinate. -/
noncomputable def latticeFrequencyAngle (a : ℤ) : ℝ :=
  2 * Real.pi * (a : ℝ) / n

/-- The negative-Laplacian eigenvalue at an integer frequency. -/
noncomputable def latticeFourierEigenvalue (q : ℤ × ℤ) : ℝ :=
  2 * (1 - Real.cos (latticeFrequencyAngle (n := n) q.1)) +
    2 * (1 - Real.cos (latticeFrequencyAngle (n := n) q.2))

/-- The angle of a horizontal displacement at a lattice frequency. -/
noncomputable def latticeAxisAngle (a : ℤ) (m : ℕ) : ℝ :=
  2 * Real.pi * (a : ℝ) * (m : ℝ) / n

/-- One real Fourier summand for a horizontal displacement. -/
noncomputable def latticeFourierSummand (q : ℤ × ℤ) (m : ℕ) : ℝ :=
  (1 - Real.cos (latticeAxisAngle (n := n) q.1 m)) /
    ((n : ℝ) ^ 2 * latticeFourierEigenvalue (n := n) q)

local notation "frequencyAngle" => latticeFrequencyAngle (n := n)
local notation "axisAngle" => latticeAxisAngle (n := n)
local notation "frequencyEigenvalue" => latticeFourierEigenvalue (n := n)
local notation "frequencySummand" => latticeFourierSummand (n := n)

theorem latticeSquare_natAbs_le {j : ℕ} {q : ℤ × ℤ}
    (hq : q ∈ latticeSquare j) : q.1.natAbs ≤ j ∧ q.2.natAbs ≤ j := by
  simp only [latticeSquare, Finset.mem_product, Finset.mem_Icc] at hq
  rcases hq with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  constructor
  · have habs : |q.1| ≤ (j : ℤ) := abs_le.mpr ⟨h₁, h₂⟩
    have hcast : (q.1.natAbs : ℤ) ≤ (j : ℤ) := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hcast
  · have habs : |q.2| ≤ (j : ℤ) := abs_le.mpr ⟨h₃, h₄⟩
    have hcast : (q.2.natAbs : ℤ) ≤ (j : ℤ) := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hcast

/-- The union of shells between radii `M` and `N`. -/
def latticeTailShells (M N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (N - M)).biUnion (fun i => latticeShell (M + i))

theorem latticeRadius_le_of_mem_square {N : ℕ} {q : ℤ × ℤ}
    (hq : q ∈ latticeSquare N) : latticeRadius q ≤ N := by
  have h := latticeSquare_natAbs_le hq
  dsimp [latticeRadius]
  exact max_le h.1 h.2

theorem mem_latticeSquare_of_radius_le {N : ℕ} {q : ℤ × ℤ}
    (hq : latticeRadius q ≤ N) : q ∈ latticeSquare N := by
  have h1 : q.1.natAbs ≤ N := (Nat.le_max_left _ _).trans hq
  have h2 : q.2.natAbs ≤ N := (Nat.le_max_right _ _).trans hq
  have h1' : |q.1| ≤ (N : ℤ) := by
    have hc : (q.1.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
    simpa only [Int.natCast_natAbs] using hc
  have h2' : |q.2| ≤ (N : ℤ) := by
    have hc : (q.2.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast h2
    simpa only [Int.natCast_natAbs] using hc
  simp only [latticeSquare, Finset.mem_product, Finset.mem_Icc]
  exact ⟨abs_le.mp h1', abs_le.mp h2'⟩

theorem latticeSquare_union_tailShells {M N : ℕ} (hMN : M ≤ N) :
    latticeSquare N = latticeSquare M ∪ latticeTailShells M N := by
  ext q
  simp only [Finset.mem_union, latticeTailShells, Finset.mem_biUnion,
    Finset.mem_range]
  constructor
  · intro hqN
    by_cases hqM : q ∈ latticeSquare M
    · exact Or.inl hqM
    · right
      let r := latticeRadius q
      have hrle : r ≤ N := latticeRadius_le_of_mem_square hqN
      have hMlt : M < r := by
        by_contra hnot
        exact hqM (mem_latticeSquare_of_radius_le (Nat.le_of_not_gt hnot))
      have hrpos : 0 < r := by omega
      have hq0 : q ≠ (0, 0) := by
        intro hz
        subst q
        exact hqM (by simp [latticeSquare])
      let i := r - 1 - M
      have hi : i < N - M := by dsimp [i]; omega
      refine ⟨i, hi, ?_⟩
      have hrad : M + i = r - 1 := by dsimp [i]; omega
      rw [hrad]
      simpa [latticeShell, Nat.sub_add_cancel hrpos, r] using
        (mem_latticeShell_radius hq0)
  · rintro (hqM | ⟨i, hi, hqShell⟩)
    · exact latticeSquare_mono hMN hqM
    · have houter : q ∈ latticeSquare (M + i + 1) := by
        change q ∈ latticeSquare (M + i + 1) \ latticeSquare (M + i) at hqShell
        exact (Finset.mem_sdiff.mp hqShell).1
      exact latticeSquare_mono (by omega) houter

theorem latticeSquare_tailShells_disjoint (M N : ℕ) :
    Disjoint (latticeSquare M) (latticeTailShells M N) := by
  rw [Finset.disjoint_left]
  intro q hqM hqTail
  rcases Finset.mem_biUnion.mp hqTail with ⟨i, hi, hqShell⟩
  change q ∈ latticeSquare (M + i + 1) \ latticeSquare (M + i) at hqShell
  have hnot : q ∉ latticeSquare (M + i) := (Finset.mem_sdiff.mp hqShell).2
  exact hnot (latticeSquare_mono (by omega) hqM)

theorem latticeTailShells_pairwiseDisjoint (M N : ℕ) :
    (↑(Finset.range (N - M)) : Set ℕ).PairwiseDisjoint
      (fun i => latticeShell (M + i)) := by
  intro i hi k hk hik
  change Disjoint (latticeShell (M + i)) (latticeShell (M + k))
  rw [Finset.disjoint_left]
  intro q hqj hqk
  change q ∈ latticeSquare (M + i + 1) \ latticeSquare (M + i) at hqj
  change q ∈ latticeSquare (M + k + 1) \ latticeSquare (M + k) at hqk
  rcases Finset.mem_sdiff.mp hqj with ⟨hqouterJ, hqnotJ⟩
  rcases Finset.mem_sdiff.mp hqk with ⟨hqouterK, hqnotK⟩
  have hik' : i ≠ k := by simpa using hik
  rcases lt_or_gt_of_ne hik' with hlt | hgt
  · have hle : M + i + 1 ≤ M + k := by omega
    exact hqnotK (latticeSquare_mono hle hqouterJ)
  · have hle : M + k + 1 ≤ M + i := by omega
    exact hqnotJ (latticeSquare_mono hle hqouterK)

/-- The sum of reciprocal radii over a tail of square shells is logarithmic. -/
theorem reciprocal_shell_tail_le_log (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) :
    (∑ j ∈ Finset.Ico M N, (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) ≤
      1 + Real.log ((N : ℝ) / (M : ℝ)) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hNreal : (0 : ℝ) < N := lt_of_lt_of_le hMreal (by exact_mod_cast hMN)
  have hratio : (1 : ℝ) ≤ (N : ℝ) / (M : ℝ) := by
    rw [le_div_iff₀ hMreal]
    have hMNreal : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    nlinarith only [hMNreal]
  calc
    _ ≤ ∫ x in (M : ℝ)..(N : ℝ), x⁻¹ := by
      simpa only [one_div] using AntitoneOn.sum_le_integral_Ico hMN
        (inv_antitoneOn_Icc_right hMreal)
    _ = Real.log ((N : ℝ) / (M : ℝ)) := integral_inv_of_pos hMreal hNreal
    _ ≤ 1 + Real.log ((N : ℝ) / (M : ℝ)) := by
      linarith only [Real.log_nonneg hratio]

theorem latticeSquare_abs_real_le {j : ℕ} {q : ℤ × ℤ}
    (hq : q ∈ latticeSquare j) :
    |(q.1 : ℝ)| ≤ (j : ℝ) ∧ |(q.2 : ℝ)| ≤ (j : ℝ) := by
  simp only [latticeSquare, Finset.mem_product, Finset.mem_Icc] at hq
  rcases hq with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  constructor
  · exact abs_le.mpr ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
  · exact abs_le.mpr ⟨by exact_mod_cast h₃, by exact_mod_cast h₄⟩

theorem latticeFrequencyAngle_abs_le_pi {j : ℕ} {q : ℤ × ℤ}
    (hq : q ∈ latticeSquare j) (hj : j ≤ n / 2) (a : ℤ)
    (ha : a = q.1 ∨ a = q.2) :
    |frequencyAngle a| ≤ Real.pi := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcoord := latticeSquare_abs_real_le hq
  have hjn : 2 * j ≤ n := by omega
  have hjreal : (j : ℝ) ≤ (n : ℝ) / 2 := by
    have hcast : 2 * (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    nlinarith only [hcast]
  have hfreq : |(a : ℝ)| ≤ (n : ℝ) / 2 := by
    rcases ha with rfl | rfl
    · calc
        |(q.1 : ℝ)| ≤ (j : ℝ) := hcoord.1
        _ ≤ (n : ℝ) / 2 := hjreal
    · calc
        |(q.2 : ℝ)| ≤ (j : ℝ) := hcoord.2
        _ ≤ (n : ℝ) / 2 := hjreal
  rw [latticeFrequencyAngle, abs_div, abs_mul,
    abs_of_nonneg (show 0 ≤ 2 * Real.pi by positivity), abs_of_pos hn]
  calc
    (2 * Real.pi) * |(a : ℝ)| / n ≤
        (2 * Real.pi) * ((n : ℝ) / 2) / n := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hfreq (by positivity)
          · exact hn.le
    _ = Real.pi := by field_simp

theorem latticeFourierEigenvalue_lower {q : ℤ × ℤ} (hq : q ∈ latticeSquare (n / 2)) :
    16 / (n : ℝ) ^ 2 * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) ≤
      frequencyEigenvalue q := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hangle₁ := Real.cos_le_one_sub_mul_cos_sq
    (latticeFrequencyAngle_abs_le_pi hq le_rfl q.1 (Or.inl rfl))
  have hangle₂ := Real.cos_le_one_sub_mul_cos_sq
    (latticeFrequencyAngle_abs_le_pi hq le_rfl q.2 (Or.inr rfl))
  have hfreq₁ : 16 / (n : ℝ) ^ 2 * (q.1 : ℝ) ^ 2 ≤
      2 * (1 - Real.cos (frequencyAngle q.1)) := by
    have heq : 16 / (n : ℝ) ^ 2 * (q.1 : ℝ) ^ 2 =
        4 / Real.pi ^ 2 * (frequencyAngle q.1) ^ 2 := by
      simp only [latticeFrequencyAngle]
      field_simp [ne_of_gt hn, Real.pi_ne_zero]
      ring
    rw [heq]
    calc
      4 / Real.pi ^ 2 * (frequencyAngle q.1) ^ 2 =
          2 * (2 / Real.pi ^ 2 * (frequencyAngle q.1) ^ 2) := by ring
      _ ≤ 2 * (1 - Real.cos (frequencyAngle q.1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith only [hangle₁]
  have hfreq₂ : 16 / (n : ℝ) ^ 2 * (q.2 : ℝ) ^ 2 ≤
      2 * (1 - Real.cos (frequencyAngle q.2)) := by
    have heq : 16 / (n : ℝ) ^ 2 * (q.2 : ℝ) ^ 2 =
        4 / Real.pi ^ 2 * (frequencyAngle q.2) ^ 2 := by
      simp only [latticeFrequencyAngle]
      field_simp [ne_of_gt hn, Real.pi_ne_zero]
      ring
    rw [heq]
    calc
      4 / Real.pi ^ 2 * (frequencyAngle q.2) ^ 2 =
          2 * (2 / Real.pi ^ 2 * (frequencyAngle q.2) ^ 2) := by ring
      _ ≤ 2 * (1 - Real.cos (frequencyAngle q.2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith only [hangle₂]
  dsimp only [latticeFourierEigenvalue]
  calc
    16 / (n : ℝ) ^ 2 * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) =
        16 / (n : ℝ) ^ 2 * (q.1 : ℝ) ^ 2 +
          16 / (n : ℝ) ^ 2 * (q.2 : ℝ) ^ 2 := by ring
    _ ≤ 2 * (1 - Real.cos (frequencyAngle q.1)) +
        2 * (1 - Real.cos (frequencyAngle q.2)) := add_le_add hfreq₁ hfreq₂

theorem latticeFourierEigenvalue_pos {q : ℤ × ℤ} (hq : q ∈ latticeSquare (n / 2))
    (hq0 : q ≠ (0, 0)) : 0 < frequencyEigenvalue q := by
  have hnorm : 0 < (q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2 := by
    rcases q with ⟨a, b⟩
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      exact hq0 (Prod.ext h.1 h.2)
    rcases hab with ha | hb
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (by exact_mod_cast ha)) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (by exact_mod_cast hb))
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcoeff : 0 < (16 : ℝ) / (n : ℝ) ^ 2 := by positivity
  exact (mul_pos hcoeff hnorm).trans_le (latticeFourierEigenvalue_lower hq)

omit [NeZero n] in
theorem latticeFourierSummand_nonneg (q : ℤ × ℤ) (m : ℕ) :
    0 ≤ frequencySummand q m := by
  have hnum : 0 ≤ 1 - Real.cos (axisAngle q.1 m) := by
    linarith only [Real.cos_le_one (axisAngle q.1 m)]
  have hEigenNonneg : 0 ≤ frequencyEigenvalue q := by
    simp only [latticeFourierEigenvalue]
    have h₁ := Real.cos_le_one (frequencyAngle q.1)
    have h₂ := Real.cos_le_one (frequencyAngle q.2)
    positivity
  exact div_nonneg hnum (mul_nonneg (sq_nonneg _) hEigenNonneg)

/-- Small-angle estimate for one lattice Fourier summand. -/
theorem latticeFourierSummand_small_le {q : ℤ × ℤ} (m : ℕ)
    (hq : q ∈ latticeSquare (n / 2)) :
    frequencySummand q m ≤
      (Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  by_cases hq0 : q = (0, 0)
  · subst q
    simp [latticeFourierSummand, latticeAxisAngle, latticeFourierEigenvalue]
    positivity
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hEigPos := latticeFourierEigenvalue_pos hq hq0
  let θ := axisAngle q.1 m
  let S := (q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2
  have hnum : 1 - Real.cos θ ≤
      2 * Real.pi ^ 2 * (m : ℝ) ^ 2 * (q.1 : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    have hcos := Real.one_sub_sq_div_two_le_cos (x := θ)
    have hnum₀ : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by linarith only [hcos]
    have heq : θ ^ 2 / 2 =
        2 * Real.pi ^ 2 * (m : ℝ) ^ 2 * (q.1 : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
      dsimp [θ, latticeAxisAngle]
      field_simp [ne_of_gt hn]
    exact hnum₀.trans_eq heq
  have hdenLower : 16 * S ≤ (n : ℝ) ^ 2 * frequencyEigenvalue q := by
    have hLower := latticeFourierEigenvalue_lower hq
    calc
      16 * S = (n : ℝ) ^ 2 * (16 / (n : ℝ) ^ 2 * S) := by
        dsimp [S]
        field_simp [ne_of_gt hn]
      _ ≤ (n : ℝ) ^ 2 * frequencyEigenvalue q :=
        mul_le_mul_of_nonneg_left hLower (sq_nonneg _)
  have hdenPos : 0 < (n : ℝ) ^ 2 * frequencyEigenvalue q :=
    mul_pos (sq_pos_of_pos hn) hEigPos
  have hS : (q.1 : ℝ) ^ 2 ≤ S := by dsimp [S]; nlinarith only [sq_nonneg (q.2 : ℝ)]
  have hcoeff : 0 ≤ 2 * Real.pi ^ 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 2 := by positivity
  have hC : 0 ≤ (Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2 := by positivity
  have hbound : 1 - Real.cos θ ≤
      ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) *
        ((n : ℝ) ^ 2 * frequencyEigenvalue q) := by
    calc
      1 - Real.cos θ ≤
          (2 * Real.pi ^ 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) * S := by
            calc
              _ ≤ 2 * Real.pi ^ 2 * (m : ℝ) ^ 2 * (q.1 : ℝ) ^ 2 /
                    (n : ℝ) ^ 2 := hnum
              _ = (2 * Real.pi ^ 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) *
                    (q.1 : ℝ) ^ 2 := by ring
              _ ≤ (2 * Real.pi ^ 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) * S :=
                mul_le_mul_of_nonneg_left hS hcoeff
      _ = ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) * (16 * S) := by ring
      _ ≤ ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) *
            ((n : ℝ) ^ 2 * frequencyEigenvalue q) :=
          mul_le_mul_of_nonneg_left hdenLower hC
  rw [latticeFourierSummand]
  exact (div_le_iff₀ hdenPos).2 hbound

/-- Reciprocal-frequency estimate for one large lattice mode. -/
theorem latticeFourierSummand_large_le {j : ℕ} {q : ℤ × ℤ} (m : ℕ)
    (hqShell : q ∈ latticeShell j) (hqSquare : q ∈ latticeSquare (n / 2)) :
    frequencySummand q m ≤
      (1 / 8 : ℝ) / ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) := by
  have hq0 : q ≠ (0, 0) := by
    intro hzero
    subst q
    simp [latticeShell, latticeSquare] at hqShell
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hS : 0 < (q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2 := by
    rcases q with ⟨a, b⟩
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      exact hq0 (Prod.ext h.1 h.2)
    rcases hab with ha | hb
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (by exact_mod_cast ha)) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (by exact_mod_cast hb))
  have hEigPos := latticeFourierEigenvalue_pos hqSquare hq0
  have hdenPos : 0 < (n : ℝ) ^ 2 * frequencyEigenvalue q :=
    mul_pos (sq_pos_of_pos hn) hEigPos
  have hdenLower : 16 * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) ≤
      (n : ℝ) ^ 2 * frequencyEigenvalue q := by
    have hLower := latticeFourierEigenvalue_lower hqSquare
    calc
      16 * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) =
          (n : ℝ) ^ 2 * (16 / (n : ℝ) ^ 2 *
            ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) := by field_simp [ne_of_gt hn]
      _ ≤ _ := mul_le_mul_of_nonneg_left hLower (sq_nonneg _)
  have hnum : 1 - Real.cos (axisAngle q.1 m) ≤ 2 := by
    linarith only [Real.neg_one_le_cos (axisAngle q.1 m)]
  have hcoeff : 0 ≤ (1 / 8 : ℝ) /
      ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) := by positivity
  have hbound : 1 - Real.cos (axisAngle q.1 m) ≤
      ((1 / 8 : ℝ) / ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) *
        ((n : ℝ) ^ 2 * frequencyEigenvalue q) := by
    have heq : (2 : ℝ) = ((1 / 8 : ℝ) /
        ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) *
        (16 * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) := by
      field_simp [ne_of_gt hS]
      norm_num
    calc
      _ ≤ 2 := hnum
      _ = _ := heq
      _ ≤ _ := mul_le_mul_of_nonneg_left hdenLower hcoeff
  rw [latticeFourierSummand]
  exact (div_le_iff₀ hdenPos).2 hbound

/-! ### Reindexing the torus sum by centered integer frequencies -/

/-- Centered integer representative of a torus frequency. -/
def torusLatticeFrequencyRep (k : TorusVertex n) : ℤ × ℤ :=
  (k.1.valMinAbs, k.2.valMinAbs)

omit [NeZero n] in
theorem torusLatticeFrequencyRep_injective :
    Function.Injective (torusLatticeFrequencyRep (n := n)) := by
  intro k l h
  apply Prod.ext
  · exact ZMod.injective_valMinAbs (congrArg Prod.fst h)
  · exact ZMod.injective_valMinAbs (congrArg Prod.snd h)

/-- The real part of a horizontal torus character is the cosine at its
centered integer frequency. -/
theorem torusCharacter_axis_re (k : TorusVertex n) (m : ℕ) :
    (torusCharacter k ((m : ZMod n), 0)).re =
      Real.cos (axisAngle k.1.valMinAbs m) := by
  have hcast : k.1 * (m : ZMod n) =
      ((k.1.valMinAbs * (m : ℤ) : ℤ) : ZMod n) := by
    rw [← ZMod.coe_valMinAbs k.1]
    push_cast
    ring
  have hchar : ZMod.stdAddChar (k.1 * (m : ZMod n)) =
    Complex.exp (2 * Real.pi * Complex.I *
        ((k.1.valMinAbs * (m : ℤ) : ℤ) : ℝ) / n) := by
    rw [hcast]
    exact ZMod.stdAddChar_coe _
  have harg : (2 * Real.pi * Complex.I *
      ((k.1.valMinAbs * (m : ℤ) : ℤ) : ℝ) / n : ℂ) =
        (axisAngle k.1.valMinAbs m : ℂ) * Complex.I := by
    dsimp [latticeAxisAngle]
    push_cast
    ring
  calc
    (torusCharacter k ((m : ZMod n), 0)).re =
        (ZMod.stdAddChar (k.1 * (m : ZMod n))).re := by
          simp [torusCharacter]
    _ = (Complex.exp (2 * Real.pi * Complex.I *
        ((k.1.valMinAbs * (m : ℤ) : ℤ) : ℝ) / n)).re := by rw [hchar]
    _ = Real.cos (axisAngle k.1.valMinAbs m) := by
          rw [harg, Complex.exp_ofReal_mul_I_re]

omit [NeZero n] in
theorem torusFourierEigenvalue_eq_rep (k : TorusVertex n) :
    torusFourierEigenvalue k = frequencyEigenvalue (torusLatticeFrequencyRep k) := by
  simp [torusFourierEigenvalue, latticeFourierEigenvalue,
    torusFrequencyAngle, latticeFrequencyAngle, torusLatticeFrequencyRep]

/-- KP's Fourier formula with the frequency sum written over integer
representatives. -/
theorem torusGreenKernel_difference_eq_lattice_sum (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) (m : ℕ) :
    torusGreenKernel hn hG (0, 0) (0, 0) -
        torusGreenKernel hn hG ((m : ZMod n), 0) (0, 0) =
      ∑ k ∈ (Finset.univ.erase ((0, 0) : TorusVertex n)),
        frequencySummand (torusLatticeFrequencyRep k) m := by
  rw [torusGreenKernel_difference_eq_fourier_sum hn hG ((m : ZMod n), 0)]
  have hcard : (Fintype.card (TorusVertex n) : ℝ) = (n : ℝ) ^ 2 := by
    exact_mod_cast torusVertex_card
  calc
    (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
        ∑ k ∈ Finset.univ.erase (0, 0),
          (1 - (torusCharacter k ((m : ZMod n), 0)).re) /
            torusFourierEigenvalue k =
      ∑ k ∈ Finset.univ.erase (0, 0),
        (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
          ((1 - (torusCharacter k ((m : ZMod n), 0)).re) /
            torusFourierEigenvalue k) := by rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.univ.erase (0, 0),
          frequencySummand (torusLatticeFrequencyRep k) m := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [torusCharacter_axis_re, torusFourierEigenvalue_eq_rep, hcard]
            simp only [latticeFourierSummand, torusLatticeFrequencyRep]
            ring

/-- Centered representatives lie in the natural frequency square. -/
theorem torusLatticeFrequencyRep_mem_square (k : TorusVertex n) :
    torusLatticeFrequencyRep k ∈ latticeSquare (n / 2) := by
  apply mem_latticeSquare_of_radius_le
  dsimp [latticeRadius, torusLatticeFrequencyRep]
  exact max_le (ZMod.natAbs_valMinAbs_le k.1) (ZMod.natAbs_valMinAbs_le k.2)

private theorem latticeFourierSum_le_log (m : ℕ) (hm : 0 < m)
    (hmn : 2 * m ≤ n) :
    (∑ q ∈ latticeSquare (n / 2), frequencySummand q m) ≤
      41 * Real.log ((m + 1 : ℕ) : ℝ) := by
  let N := n / 2
  let M := max 1 (N / (m + 1))
  have hn2 : 2 ≤ n := by omega
  have hNpos : 1 ≤ N := by dsimp [N]; omega
  have hMpos : 1 ≤ M := by dsimp [M]; omega
  have hMN : M ≤ N := by
    dsimp [M]
    exact max_le hNpos (Nat.div_le_self _ _)
  have hMle : M ≤ N / (m + 1) + 1 := by
    change max 1 (N / (m + 1)) ≤ N / (m + 1) + 1
    exact max_le (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_succ _)
  have hqmul : N / (m + 1) * (m + 1) ≤ N := Nat.div_mul_le_self _ _
  have hMmul_le : M * (m + 1) ≤ n := by
    by_cases hqzero : N / (m + 1) = 0
    · have hMone : M = 1 := by simp [M, hqzero]
      rw [hMone]
      omega
    · have hqpos : 1 ≤ N / (m + 1) := Nat.one_le_iff_ne_zero.mpr hqzero
      have hdenN : m + 1 ≤ N := by
        have hmul := Nat.mul_le_mul_right (m + 1) hqpos
        have hmul' : m + 1 ≤ (N / (m + 1)) * (m + 1) := by simpa using hmul
        exact hmul'.trans hqmul
      have hMdiv : M = N / (m + 1) := by
        simp [M, hqpos]
      rw [hMdiv]
      exact hqmul.trans (Nat.div_le_self n 2)
  have hMmul : (M : ℝ) * ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hMmul_le
  have hmMle : (m : ℝ) * (M : ℝ) ≤ (n : ℝ) := by
    calc
      (m : ℝ) * (M : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (M : ℝ) := by
        gcongr
        omega
      _ = (M : ℝ) * ((m + 1 : ℕ) : ℝ) := by ring
      _ ≤ (n : ℝ) := hMmul
  have hratioNat : N ≤ 2 * M * (m + 1) := by
    by_cases hqzero : N / (m + 1) = 0
    · have hdivlt : N < m + 1 := (Nat.div_eq_zero_iff_lt (by omega)).mp hqzero
      have hMone : M = 1 := by simp [M, hqzero]
      rw [hMone]
      omega
    · have hqpos : 1 ≤ N / (m + 1) := Nat.one_le_iff_ne_zero.mpr hqzero
      have hmod : N % (m + 1) < m + 1 := Nat.mod_lt _ (by omega)
      have hdecomp := Nat.div_add_mod N (m + 1)
      have hMdiv : M = N / (m + 1) := by simp [M, hqpos]
      rw [hMdiv]
      nlinarith only [hqpos, hmod, hdecomp]
  have hNreal : (N : ℝ) ≤ 2 * (M : ℝ) * ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hratioNat
  have hMreal : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hratio : (N : ℝ) / (M : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hMreal]
    nlinarith only [hNreal]
  have hratioPos : 0 < (N : ℝ) / (M : ℝ) := div_pos (by exact_mod_cast hNpos) hMreal
  have hlogRatio : Real.log ((N : ℝ) / (M : ℝ)) ≤
      1 + Real.log ((m + 1 : ℕ) : ℝ) := by
    have hlog := Real.log_le_log hratioPos hratio
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [this]
    have hmul : 0 < (2 : ℝ) * ((m + 1 : ℕ) : ℝ) := by positivity
    rw [Real.log_mul (by norm_num) (by positivity)] at hlog
    linarith only [hlog, hlog2]
  have hsmall :
      (∑ q ∈ latticeSquare M, frequencySummand q m) ≤ 18 := by
    have hsmall' := Finset.sum_le_card_nsmul (latticeSquare M)
      (frequencySummand · m)
      ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2)
      (by
        intro q hq
        apply latticeFourierSummand_small_le
        exact latticeSquare_mono (by omega) hq)
    have hcardCast : ((latticeSquare M).card : ℝ) = (2 * (M : ℝ) + 1) ^ 2 := by
      exact_mod_cast latticeSquare_card M
    have hcardBound : (2 * (M : ℝ) + 1) ^ 2 ≤ 9 * (M : ℝ) ^ 2 := by
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
      nlinarith only [hM1]
    have hpiBound : Real.pi ^ 2 ≤ 16 := by
      have hpos : 0 ≤ (4 : ℝ) - Real.pi := by linarith only [Real.pi_le_four]
      have hsum : 0 ≤ (4 - Real.pi) * (4 + Real.pi) :=
        mul_nonneg hpos (by positivity)
      nlinarith only [hsum]
    have hcoef : 0 ≤ (Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2 := by positivity
    have hprodBound : ((m : ℝ) * (M : ℝ) / (n : ℝ)) ^ 2 ≤ 1 := by
      have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hquot : (m : ℝ) * (M : ℝ) / n ≤ 1 :=
        (div_le_one hnreal).2 hmMle
      have hquotNonneg : 0 ≤ (m : ℝ) * (M : ℝ) / n := by positivity
      have hmul : 0 ≤ ((m : ℝ) * (M : ℝ) / n) *
          (1 - ((m : ℝ) * (M : ℝ) / n)) :=
        mul_nonneg hquotNonneg (by linarith only [hquot])
      nlinarith only [hmul]
    have hsmallFinal :
        ((latticeSquare M).card : ℝ) *
          ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤ 18 := by
      rw [hcardCast]
      have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hMnonneg : 0 ≤ (M : ℝ) := by positivity
      have hmnonneg : 0 ≤ (m : ℝ) := by positivity
      have hscale :
          ((2 * (M : ℝ) + 1) ^ 2) *
              ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤
            (9 * (M : ℝ) ^ 2) * ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcardBound hcoef
      have hcalc :
          (9 * (M : ℝ) ^ 2) * ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤ 18 := by
        have heq :
            (9 * (M : ℝ) ^ 2) * ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) =
              (9 / 8 * Real.pi ^ 2) * ((m : ℝ) * (M : ℝ) / n) ^ 2 := by
          field_simp [ne_of_gt hnreal]
        rw [heq]
        have hcoeff' : 0 ≤ 9 / 8 * Real.pi ^ 2 := by positivity
        have hcoeff'' : 9 / 8 * Real.pi ^ 2 ≤ 18 := by nlinarith only [hpiBound]
        calc
          (9 / 8 * Real.pi ^ 2) * ((m : ℝ) * (M : ℝ) / n) ^ 2 ≤
              (9 / 8 * Real.pi ^ 2) * 1 :=
                mul_le_mul_of_nonneg_left hprodBound hcoeff'
          _ ≤ 18 := by nlinarith only [hcoeff'']
      exact hscale.trans hcalc
    calc
      _ ≤ ((latticeSquare M).card : ℝ) *
          ((Real.pi ^ 2 / 8) * (m : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
            simpa [nsmul_eq_mul] using hsmall'
      _ ≤ 18 := hsmallFinal
  have htail :
      (∑ q ∈ latticeTailShells M N, frequencySummand q m) ≤
        1 + Real.log ((N : ℝ) / (M : ℝ)) := by
    rw [latticeTailShells,
      Finset.sum_biUnion (latticeTailShells_pairwiseDisjoint M N)]
    calc
      _ ≤ ∑ i ∈ Finset.range (N - M),
          (1 : ℝ) / ((M + i + 1 : ℕ) : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            let j := M + i
            have hji : j + 1 ≤ N := by dsimp [j]; have := Finset.mem_range.mp hi; omega
            have hshell :
                (∑ q ∈ latticeShell j, frequencySummand q m) ≤
                  (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
              calc
                _ ≤ ∑ q ∈ latticeShell j,
                    ((1 / 8 : ℝ) /
                      ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) := by
                        apply Finset.sum_le_sum
                        intro q hq
                        apply latticeFourierSummand_large_le m hq
                        have houter := (Finset.mem_sdiff.mp hq).1
                        exact latticeSquare_mono (by dsimp [j] at hji; omega) houter
                _ = (1 / 8 : ℝ) *
                    (∑ q ∈ latticeShell j,
                      (1 : ℝ) / ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro q hq
                        ring
                _ ≤ (1 / 8 : ℝ) * (8 / ((j + 1 : ℕ) : ℝ)) := by
                      exact mul_le_mul_of_nonneg_left
                        (latticeShell_reciprocal_sum_le j) (by norm_num)
                _ = (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by ring
            simpa [j, Nat.add_assoc] using hshell
      _ = ∑ j ∈ Finset.Ico M N, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
          symm
          simpa [Nat.add_assoc] using
            (Finset.sum_Ico_eq_sum_range
              (fun j : ℕ => (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) M N)
      _ ≤ 1 + Real.log ((N : ℝ) / (M : ℝ)) :=
        reciprocal_shell_tail_le_log M N hMpos hMN
  have hwhole :
      (∑ q ∈ latticeSquare N, frequencySummand q m) ≤
        20 + Real.log ((m + 1 : ℕ) : ℝ) := by
    rw [latticeSquare_union_tailShells hMN,
      Finset.sum_union (latticeSquare_tailShells_disjoint M N)]
    calc
      _ = (∑ q ∈ latticeSquare M, frequencySummand q m) +
          (∑ q ∈ latticeTailShells M N, frequencySummand q m) := rfl
      _ ≤ 18 + (1 + Real.log ((N : ℝ) / (M : ℝ))) := add_le_add hsmall htail
      _ ≤ 20 + Real.log ((m + 1 : ℕ) : ℝ) := by linarith only [hlogRatio]
  have hlogLower : (1 / 2 : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
    have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
    have hlog := Real.le_log_one_add_of_nonneg (x := (m : ℝ)) (by positivity)
    have hmcast : (1 : ℝ) + (m : ℝ) = ((m + 1 : ℕ) : ℝ) := by norm_cast; ring
    rw [hmcast] at hlog
    have hlower : (1 / 2 : ℝ) ≤ 2 * (m : ℝ) / ((m : ℝ) + 2) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 2)]
      nlinarith only [hmreal]
    exact hlower.trans hlog
  have hfinal : 20 + Real.log ((m + 1 : ℕ) : ℝ) ≤
      41 * Real.log ((m + 1 : ℕ) : ℝ) := by nlinarith only [hlogLower]
  exact hwhole.trans hfinal

/-- KP (6.13), on the horizontal axis: the Green-kernel difference is bounded
by an absolute multiple of the logarithm of one plus the cyclic distance. -/
theorem torusGreenKernel_axis_log_upper_bound (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) (m : ℕ) (hmn : 2 * m ≤ n) :
    torusGreenKernel hn hG (0, 0) (0, 0) -
        torusGreenKernel hn hG ((m : ZMod n), 0) (0, 0) ≤
      41 * Real.log ((m + 1 : ℕ) : ℝ) := by
  by_cases hm : m = 0
  · subst m
    rw [torusGreenKernel_difference_eq_lattice_sum hn hG 0]
    simp [latticeFourierSummand, latticeAxisAngle]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hsum := latticeFourierSum_le_log (n := n) m hmpos hmn
    calc
      _ = ∑ k ∈ Finset.univ.erase ((0, 0) : TorusVertex n),
          frequencySummand (torusLatticeFrequencyRep k) m :=
            torusGreenKernel_difference_eq_lattice_sum hn hG m
      _ = ∑ q ∈ Finset.image torusLatticeFrequencyRep
          (Finset.univ.erase ((0, 0) : TorusVertex n)), frequencySummand q m := by
            symm
            apply Finset.sum_image
            intro k hk l hl hkl
            exact torusLatticeFrequencyRep_injective hkl
      _ ≤ ∑ q ∈ latticeSquare (n / 2), frequencySummand q m := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · apply Finset.image_subset_iff.mpr
              intro k hk
              exact torusLatticeFrequencyRep_mem_square k
            · intro q hq hqnot
              exact latticeFourierSummand_nonneg q m
      _ ≤ 41 * Real.log ((m + 1 : ℕ) : ℝ) := hsum

end FroehlichSpencer.BKT.Lattice2D

end
