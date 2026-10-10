/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.TorusPotential
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fourier characters on the finite square torus

The standard additive characters diagonalize the nearest-neighbour torus
Laplacian. This module also records orthogonality and the positive eigenvalue
used in the Green representation (KP (6.13)).
-/

@[expose] public section

open AddChar
open scoped Real

namespace FroehlichSpencer.BKT.Lattice2D

variable {n : ℕ} [NeZero n]

/-- The standard complex Fourier character on the square torus. -/
noncomputable def torusCharacter (k y : TorusVertex n) : ℂ :=
  ZMod.stdAddChar (k.1 * y.1 + k.2 * y.2)

/-- The one-dimensional character sum vanishes at nonzero frequency. -/
theorem stdAddChar_mul_sum (k : ZMod n) :
    (∑ y : ZMod n, ZMod.stdAddChar (k * y)) =
      if k = 0 then (n : ℂ) else 0 := by
  classical
  have h := AddChar.sum_mulShift k (ZMod.isPrimitive_stdAddChar n)
  simpa only [mul_comm, ZMod.card, Nat.cast_ite, Nat.cast_zero] using h

/-- Orthogonality of square-torus Fourier characters. -/
theorem torusCharacter_sum (k : TorusVertex n) :
    (∑ y : TorusVertex n, torusCharacter k y) =
      if k = (0, 0) then (n : ℂ) ^ 2 else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [torusCharacter, AddChar.map_add_eq_mul]
  rcases k with ⟨k₁, k₂⟩
  have h₁ := stdAddChar_mul_sum k₁
  have h₂ := stdAddChar_mul_sum k₂
  calc
    (∑ x : ZMod n, ∑ y : ZMod n,
        ZMod.stdAddChar (k₁ * x) * ZMod.stdAddChar (k₂ * y)) =
        (∑ x : ZMod n, ZMod.stdAddChar (k₁ * x)) *
          (∑ y : ZMod n, ZMod.stdAddChar (k₂ * y)) := by
            simp_rw [← Finset.mul_sum]
            rw [← Finset.sum_mul]
    _ = (if k₁ = 0 then (n : ℂ) else 0) *
        (if k₂ = 0 then (n : ℂ) else 0) := by rw [h₁, h₂]
    _ = if (k₁, k₂) = (0, 0) then (n : ℂ) ^ 2 else 0 := by
        by_cases h₁ : k₁ = 0
        · by_cases h₂ : k₂ = 0
          · simp [h₁, h₂]
            ring
          · simp [h₁, h₂]
        · by_cases h₂ : k₂ = 0 <;> simp [h₁, h₂]

/-- The centered real angle associated with a torus frequency. -/
noncomputable def torusFrequencyAngle (k : ZMod n) : ℝ :=
  2 * Real.pi * (k.valMinAbs : ℝ) / n

/-- The positive eigenvalue of the negative torus Laplacian at a frequency. -/
noncomputable def torusFourierEigenvalue (k : TorusVertex n) : ℝ :=
  2 * (1 - Real.cos (torusFrequencyAngle k.1)) +
    2 * (1 - Real.cos (torusFrequencyAngle k.2))

/-- The standard character at a centered representative has the corresponding
complex exponential value. -/
theorem stdAddChar_valMinAbs (k : ZMod n) :
    ZMod.stdAddChar k = Complex.exp
      (2 * Real.pi * Complex.I * (k.valMinAbs : ℝ) / n) := by
  have hcast : ((k.valMinAbs : ℤ) : ZMod n) = k := ZMod.coe_valMinAbs k
  calc
    ZMod.stdAddChar k =
        ZMod.stdAddChar ((k.valMinAbs : ℤ) : ZMod n) :=
      congrArg ZMod.stdAddChar hcast.symm
    _ = Complex.exp (2 * Real.pi * Complex.I * (k.valMinAbs : ℝ) / n) :=
      ZMod.stdAddChar_coe _

/-- The real part of the standard character is the cosine of its centered
frequency angle. -/
theorem stdAddChar_re (k : ZMod n) :
    (ZMod.stdAddChar k).re = Real.cos (torusFrequencyAngle k) := by
  rw [stdAddChar_valMinAbs]
  have harg :
      2 * Real.pi * Complex.I * (k.valMinAbs : ℝ) / n =
        (torusFrequencyAngle k : ℂ) * Complex.I := by
    simp only [torusFrequencyAngle]
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

/-- The standard additive character has unit modulus. -/
theorem stdAddChar_norm (k : ZMod n) : ‖ZMod.stdAddChar k‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Negating a frequency conjugates its character. -/
theorem stdAddChar_neg_eq_conj (k : ZMod n) :
    ZMod.stdAddChar (-k) = (starRingEnd ℂ) (ZMod.stdAddChar k) := by
  rw [AddChar.map_neg_eq_inv]
  exact Complex.inv_eq_conj (stdAddChar_norm k)

/-- Opposite one-dimensional frequencies sum to twice the real cosine mode. -/
theorem stdAddChar_pair_eq_two_cos (k : ZMod n) :
    ZMod.stdAddChar k + ZMod.stdAddChar (-k) =
      (2 * Real.cos (torusFrequencyAngle k) : ℂ) := by
  rw [stdAddChar_neg_eq_conj, Complex.add_conj, stdAddChar_re]
  push_cast
  ring

/-- Torus characters turn addition of vertices into multiplication. -/
theorem torusCharacter_add (k x y : TorusVertex n) :
    torusCharacter k (x + y) = torusCharacter k x * torusCharacter k y := by
  simp only [torusCharacter, Prod.fst_add, Prod.snd_add, mul_add,
    AddChar.map_add_eq_mul]
  ring

/-- A character's value after a rightward step. -/
theorem torusCharacter_right_step (k y : TorusVertex n) :
    torusCharacter k (y + (1, 0)) =
      torusCharacter k y * ZMod.stdAddChar k.1 := by
  rw [torusCharacter_add]
  simp [torusCharacter]

/-- A character's value after a leftward step. -/
theorem torusCharacter_left_step (k y : TorusVertex n) :
    torusCharacter k (y - (1, 0)) =
      torusCharacter k y * ZMod.stdAddChar (-k.1) := by
  rw [sub_eq_add_neg, torusCharacter_add]
  simp [torusCharacter]

/-- A character's value after an upward step. -/
theorem torusCharacter_up_step (k y : TorusVertex n) :
    torusCharacter k (y + (0, 1)) =
      torusCharacter k y * ZMod.stdAddChar k.2 := by
  rw [torusCharacter_add]
  simp [torusCharacter]

/-- A character's value after a downward step. -/
theorem torusCharacter_down_step (k y : TorusVertex n) :
    torusCharacter k (y - (0, 1)) =
      torusCharacter k y * ZMod.stdAddChar (-k.2) := by
  rw [sub_eq_add_neg, torusCharacter_add]
  simp [torusCharacter]

/-- The usual four-neighbour formula for the combinatorial torus Laplacian. -/
theorem torusLaplacian_neighbor_formula (hn : 2 < n)
    (f : TorusVertex n → ℂ) (y : TorusVertex n) :
    (torusGraph n hn).laplacian f y =
      f (y + (1, 0)) + f (y - (1, 0)) +
      f (y + (0, 1)) + f (y - (0, 1)) - 4 * f y := by
  classical
  have hright (q : TorusVertex n) :
      (q.1 + 1, q.2) = y ↔ q = (y.1 - 1, y.2) := by
    constructor
    · intro h
      have hproj : q.1 + 1 = y.1 ∧ q.2 = y.2 := by
        simpa only [Prod.ext_iff] using h
      rcases hproj with ⟨h1, h2⟩
      ext
      · calc
          q.1 = (q.1 + 1) - 1 := by ring
          _ = y.1 - 1 := by rw [h1]
      · exact h2
    · rintro rfl
      simp
  have hup (q : TorusVertex n) :
      (q.1, q.2 + 1) = y ↔ q = (y.1, y.2 - 1) := by
    constructor
    · intro h
      have hproj : q.1 = y.1 ∧ q.2 + 1 = y.2 := by
        simpa only [Prod.ext_iff] using h
      rcases hproj with ⟨h1, h2⟩
      ext
      · exact h1
      · calc
          q.2 = (q.2 + 1) - 1 := by ring
          _ = y.2 - 1 := by rw [h2]
    · rintro rfl
      simp
  simp only [Multigraph.laplacian]
  rw [Fintype.sum_prod_type]
  simp [torusGraph, torusStep]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [hright, hup]
  simp
  have hup' : (y.1, y.2 + 1) = y + (0, 1) := by ext <;> simp
  have hright' : (y.1 + 1, y.2) = y + (1, 0) := by ext <;> simp
  have hleft' : (y.1 - 1, y.2) = y - (1, 0) := by ext <;> simp
  have hdown' : (y.1, y.2 - 1) = y - (0, 1) := by ext <;> simp
  rw [hup', hright', hleft', hdown']
  ring

/-- The combinatorial torus Laplacian acts diagonally on Fourier characters. -/
theorem torusGraph_laplacian_character (hn : 2 < n)
    (k y : TorusVertex n) :
    (torusGraph n hn).laplacian (fun z => torusCharacter k z) y =
      -(torusFourierEigenvalue k : ℂ) * torusCharacter k y := by
  rw [torusLaplacian_neighbor_formula]
  rw [torusCharacter_right_step, torusCharacter_left_step,
    torusCharacter_up_step, torusCharacter_down_step]
  rw [show (torusFourierEigenvalue k : ℂ) =
      4 - (2 * Real.cos (torusFrequencyAngle k.1) : ℂ) -
        (2 * Real.cos (torusFrequencyAngle k.2) : ℂ) by
      simp only [torusFourierEigenvalue]
      push_cast
      ring]
  rw [← stdAddChar_pair_eq_two_cos k.1, ← stdAddChar_pair_eq_two_cos k.2]
  ring

/-- Every centered frequency angle has absolute value at most pi. -/
theorem abs_torusFrequencyAngle_le_pi (k : ZMod n) :
    |torusFrequencyAngle k| ≤ Real.pi := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hfreqNat : k.valMinAbs.natAbs ≤ n / 2 := ZMod.natAbs_valMinAbs_le k
  have hfreqNatCast : (k.valMinAbs.natAbs : ℝ) ≤ (n / 2 : ℕ) := by
    exact_mod_cast hfreqNat
  have hdivcast : (2 : ℝ) * (n / 2 : ℕ) ≤ n := by
    exact_mod_cast (by simpa [Nat.mul_comm] using Nat.div_mul_le_self n 2)
  have hfreq : |(k.valMinAbs : ℝ)| ≤ (n : ℝ) / 2 := by
    calc
      |(k.valMinAbs : ℝ)| = (k.valMinAbs.natAbs : ℝ) := by
        calc
          |(k.valMinAbs : ℝ)| = ((|k.valMinAbs| : ℤ) : ℝ) :=
            Int.cast_abs.symm
          _ = ((k.valMinAbs.natAbs : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
          _ = (k.valMinAbs.natAbs : ℝ) := rfl
      _ ≤ (n / 2 : ℕ) := hfreqNatCast
      _ ≤ (n : ℝ) / 2 := by nlinarith only [hdivcast]
  rw [torusFrequencyAngle, abs_div, abs_mul,
    abs_of_nonneg (show 0 ≤ 2 * Real.pi by positivity), abs_of_pos hn]
  calc
    (2 * Real.pi) * |(k.valMinAbs : ℝ)| / n ≤
        (2 * Real.pi) * ((n : ℝ) / 2) / n := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hfreq (by positivity)
          · exact hn.le
    _ = Real.pi := by field_simp

/-- The torus Laplacian eigenvalue is bounded below by the squared centered
frequency. -/
theorem torusFourierEigenvalue_lower (k : TorusVertex n) :
    16 / (n : ℝ) ^ 2 *
      ((k.1.valMinAbs : ℝ) ^ 2 + (k.2.valMinAbs : ℝ) ^ 2) ≤
        torusFourierEigenvalue k := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hangle₁ := Real.cos_le_one_sub_mul_cos_sq (abs_torusFrequencyAngle_le_pi k.1)
  have hangle₂ := Real.cos_le_one_sub_mul_cos_sq (abs_torusFrequencyAngle_le_pi k.2)
  have hfreq₁ : 16 / (n : ℝ) ^ 2 * (k.1.valMinAbs : ℝ) ^ 2 ≤
      2 * (1 - Real.cos (torusFrequencyAngle k.1)) := by
    have heq : 16 / (n : ℝ) ^ 2 * (k.1.valMinAbs : ℝ) ^ 2 =
        4 / Real.pi ^ 2 * (torusFrequencyAngle k.1) ^ 2 := by
      simp only [torusFrequencyAngle]
      field_simp [ne_of_gt hn, Real.pi_ne_zero]
      ring
    rw [heq]
    calc
      4 / Real.pi ^ 2 * (torusFrequencyAngle k.1) ^ 2 =
          2 * (2 / Real.pi ^ 2 * (torusFrequencyAngle k.1) ^ 2) := by ring
      _ ≤ 2 * (1 - Real.cos (torusFrequencyAngle k.1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hangle₁]
  have hfreq₂ : 16 / (n : ℝ) ^ 2 * (k.2.valMinAbs : ℝ) ^ 2 ≤
      2 * (1 - Real.cos (torusFrequencyAngle k.2)) := by
    have heq : 16 / (n : ℝ) ^ 2 * (k.2.valMinAbs : ℝ) ^ 2 =
        4 / Real.pi ^ 2 * (torusFrequencyAngle k.2) ^ 2 := by
      simp only [torusFrequencyAngle]
      field_simp [ne_of_gt hn, Real.pi_ne_zero]
      ring
    rw [heq]
    calc
      4 / Real.pi ^ 2 * (torusFrequencyAngle k.2) ^ 2 =
          2 * (2 / Real.pi ^ 2 * (torusFrequencyAngle k.2) ^ 2) := by ring
      _ ≤ 2 * (1 - Real.cos (torusFrequencyAngle k.2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hangle₂]
  dsimp only [torusFourierEigenvalue]
  calc
    16 / (n : ℝ) ^ 2 *
        ((k.1.valMinAbs : ℝ) ^ 2 + (k.2.valMinAbs : ℝ) ^ 2) =
      16 / (n : ℝ) ^ 2 * (k.1.valMinAbs : ℝ) ^ 2 +
        16 / (n : ℝ) ^ 2 * (k.2.valMinAbs : ℝ) ^ 2 := by ring
    _ ≤ 2 * (1 - Real.cos (torusFrequencyAngle k.1)) +
        2 * (1 - Real.cos (torusFrequencyAngle k.2)) := add_le_add hfreq₁ hfreq₂

/-- Every nonzero frequency has a strictly positive eigenvalue. -/
theorem torusFourierEigenvalue_pos {k : TorusVertex n} (hk : k ≠ (0, 0)) :
    0 < torusFourierEigenvalue k := by
  have hfreq : 0 <
      (k.1.valMinAbs : ℝ) ^ 2 + (k.2.valMinAbs : ℝ) ^ 2 := by
    have hnonzero :
        (k.1.valMinAbs : ℝ) ≠ 0 ∨ (k.2.valMinAbs : ℝ) ≠ 0 := by
      by_contra h
      push Not at h
      apply hk
      ext
      · have hz : k.1.valMinAbs = (0 : ℤ) := by exact_mod_cast h.1
        exact ZMod.injective_valMinAbs (by simpa using hz)
      · have hz : k.2.valMinAbs = (0 : ℤ) := by exact_mod_cast h.2
        exact ZMod.injective_valMinAbs (by simpa using hz)
    rcases hnonzero with h₁ | h₂
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h₁) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h₂)
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcoeff : 0 < (16 : ℝ) / (n : ℝ) ^ 2 := by positivity
  exact (mul_pos hcoeff hfreq).trans_le (torusFourierEigenvalue_lower k)

/-- The normalized contribution of one nonconstant Fourier mode to the
zero-mean Green potential. -/
noncomputable def torusFourierGreenMode (k : TorusVertex n) :
    TorusVertex n → ℂ :=
  fun y => ((Fintype.card (TorusVertex n) : ℂ)⁻¹ *
    (torusFourierEigenvalue k : ℂ)⁻¹) * torusCharacter k y

/-- The finite Fourier representation of the zero-mean Green potential. -/
noncomputable def torusFourierGreenComplex : TorusVertex n → ℂ :=
  fun y => ∑ k ∈ Finset.univ.erase (0, 0), torusFourierGreenMode k y

/-- Frequency orthogonality, with the sum taken over characters and the
vertex held fixed. -/
theorem torusCharacter_frequency_sum (y : TorusVertex n) :
    (∑ k : TorusVertex n, torusCharacter k y) =
      if y = (0, 0) then (Fintype.card (TorusVertex n) : ℂ) else 0 := by
  calc
    (∑ k : TorusVertex n, torusCharacter k y) =
        ∑ k : TorusVertex n, torusCharacter y k := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [torusCharacter]
          congr 1
          ring
    _ = if y = (0, 0) then (n : ℂ) ^ 2 else 0 := torusCharacter_sum y
    _ = if y = (0, 0) then (Fintype.card (TorusVertex n) : ℂ) else 0 := by
      congr 1
      simp [TorusVertex, ZMod.card, Fintype.card_prod]
      ring

/-- Applying the torus Laplacian to the finite Fourier potential gives a
point source with its constant mode removed. -/
theorem torusGraph_laplacian_torusFourierGreenComplex (hn : 2 < n)
    (y : TorusVertex n) :
    (torusGraph n hn).laplacian torusFourierGreenComplex y =
      -((deltaAt (0, 0) y : ℝ) : ℂ) +
        (Fintype.card (TorusVertex n) : ℂ)⁻¹ := by
  classical
  let G := torusGraph n hn
  let S : Finset (TorusVertex n) := Finset.univ.erase (0, 0)
  have hzero : (0, 0) ∈ (Finset.univ : Finset (TorusVertex n)) := Finset.mem_univ _
  have hcard : (Fintype.card (TorusVertex n) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (TorusVertex n) ≠ 0)
  have hsumChar :
      (∑ k ∈ S, torusCharacter k y) =
        (if y = (0, 0) then (Fintype.card (TorusVertex n) : ℂ) else 0) - 1 := by
    rw [show S = (Finset.univ : Finset (TorusVertex n)).erase (0, 0) from rfl,
      Finset.sum_erase_eq_sub hzero, torusCharacter_frequency_sum]
    simp [torusCharacter]
  have hmode (k : TorusVertex n) (hk : k ∈ S) :
      G.laplacianₗ ℂ (torusFourierGreenMode k) =
        fun z => -((Fintype.card (TorusVertex n) : ℂ)⁻¹) *
          torusCharacter k z := by
    have hknz : k ≠ (0, 0) := (Finset.mem_erase.mp hk).1
    have hposComplex : (torusFourierEigenvalue k : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (torusFourierEigenvalue_pos hknz))
    funext z
    change ((G.laplacianₗ ℂ)
      (((Fintype.card (TorusVertex n) : ℂ)⁻¹ *
        (torusFourierEigenvalue k : ℂ)⁻¹) •
          (fun z => torusCharacter k z))) z = _
    rw [map_smul]
    change ((Fintype.card (TorusVertex n) : ℂ)⁻¹ *
      (torusFourierEigenvalue k : ℂ)⁻¹) *
        ((G.laplacianₗ ℂ (fun z => torusCharacter k z)) z) = _
    rw [FroehlichSpencer.BKT.Multigraph.laplacianₗ_apply,
      torusGraph_laplacian_character hn]
    field_simp [hposComplex]

  have hrepresentation : torusFourierGreenComplex =
      ∑ k ∈ S, torusFourierGreenMode k := by
    unfold torusFourierGreenComplex
    funext z
    exact (Finset.sum_apply z S torusFourierGreenMode).symm
  change (G.laplacian torusFourierGreenComplex) y = _
  rw [← FroehlichSpencer.BKT.Multigraph.laplacianₗ_apply,
    hrepresentation, map_sum]
  simp only [Finset.sum_apply]
  calc
    (∑ k ∈ S, G.laplacianₗ ℂ (torusFourierGreenMode k) y) =
        ∑ k ∈ S, -((Fintype.card (TorusVertex n) : ℂ)⁻¹) *
          torusCharacter k y := by
            apply Finset.sum_congr rfl
            intro k hk
            exact congrFun (hmode k hk) y
    _ = -((Fintype.card (TorusVertex n) : ℂ)⁻¹) *
          (∑ k ∈ S, torusCharacter k y) := by rw [Finset.mul_sum]
    _ = -((Fintype.card (TorusVertex n) : ℂ)⁻¹) *
          ((if y = (0, 0) then (Fintype.card (TorusVertex n) : ℂ) else 0) - 1) := by
            rw [hsumChar]
    _ = -((deltaAt (0, 0) y : ℝ) : ℂ) +
          (Fintype.card (TorusVertex n) : ℂ)⁻¹ := by
            by_cases hy : y = (0, 0)
            · subst y
              simp [deltaAt]
              have hncomplex : (n : ℂ) ≠ 0 := by
                exact_mod_cast (show n ≠ 0 by omega)
              field_simp [hncomplex]
              ring
            · simp [deltaAt, hy]

/-- The pointwise Fourier sum is the sum of its mode functions. -/
theorem torusFourierGreenComplex_eq_sum_modes :
    torusFourierGreenComplex =
      ∑ k ∈ Finset.univ.erase ((0, 0) : TorusVertex n),
        torusFourierGreenMode k := by
  funext y
  unfold torusFourierGreenComplex
  exact (Finset.sum_apply y _ _).symm

/-- The real part of the finite graph Laplacian is the Laplacian of the real
part. -/
theorem laplacian_re {V E : Type*} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (f : V → ℂ) (y : V) :
    (G.laplacian f y).re = G.laplacian (fun z => (f z).re) y := by
  classical
  simp only [Multigraph.laplacian, Complex.re_sum, Complex.add_re]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hsrc : G.src e = y <;> by_cases htgt : G.tgt e = y <;>
    simp [hsrc, htgt, Complex.sub_re]

/-- The number of vertices in the square torus is `n²`. -/
theorem torusVertex_card : Fintype.card (TorusVertex n) = n ^ 2 := by
  simp [TorusVertex, ZMod.card, Fintype.card_prod, pow_two]

/-- The real part of a Fourier mode is its cosine mode with the real Green
coefficient. -/
theorem torusFourierGreenMode_re (k y : TorusVertex n) :
    (torusFourierGreenMode k y).re =
      (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
        (torusFourierEigenvalue k)⁻¹ * (torusCharacter k y).re := by
  simp [torusFourierGreenMode, Complex.mul_re]

/-- The real-valued finite Fourier Green potential. -/
noncomputable def torusFourierGreenPotential : TorusVertex n → ℝ :=
  fun y => (torusFourierGreenComplex y).re

/-- The complex Fourier potential has zero sum. -/
theorem torusFourierGreenComplex_sum_eq_zero :
    (∑ y : TorusVertex n, torusFourierGreenComplex y) = 0 := by
  classical
  rw [torusFourierGreenComplex_eq_sum_modes]
  simp_rw [Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : k ≠ (0, 0) := (Finset.mem_erase.mp hk).1
  change ∑ y : TorusVertex n,
      ((Fintype.card (TorusVertex n) : ℂ)⁻¹ *
        (torusFourierEigenvalue k : ℂ)⁻¹) * torusCharacter k y = 0
  rw [← Finset.mul_sum, torusCharacter_sum]
  simp [hk0]

/-- The real Fourier potential has zero sum. -/
theorem torusFourierGreenPotential_sum_eq_zero :
    (∑ y : TorusVertex n, torusFourierGreenPotential y) = 0 := by
  rw [show (∑ y : TorusVertex n, torusFourierGreenPotential y) =
      (∑ y : TorusVertex n, torusFourierGreenComplex y).re by simp
        [torusFourierGreenPotential]]
  rw [torusFourierGreenComplex_sum_eq_zero]
  simp

/-- The Fourier Green potential solves the point-source equation with its
constant mode removed. -/
theorem torusGraph_laplacian_torusFourierGreenPotential (hn : 2 < n)
    (y : TorusVertex n) :
    (torusGraph n hn).laplacian torusFourierGreenPotential y =
      -deltaAt (0, 0) y + (Fintype.card (TorusVertex n) : ℝ)⁻¹ := by
  unfold torusFourierGreenPotential
  rw [← laplacian_re (torusGraph n hn) torusFourierGreenComplex y,
    torusGraph_laplacian_torusFourierGreenComplex hn]
  simp [deltaAt]

/-- The real Fourier potential is the mean-zero inverse of the point source,
with the sign convention of the torus Green kernel. -/
theorem torusFourierGreenPotential_eq_greenOp (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) :
    torusFourierGreenPotential =
      fun x => -((torusGraph n hn).greenOp hG (deltaAt (0, 0))) x := by
  classical
  let G := torusGraph n hn
  let δ : TorusVertex n → ℝ := deltaAt (0, 0)
  let g : TorusVertex n → ℝ := torusFourierGreenPotential
  let u : TorusVertex n → ℝ := fun x => -(G.greenOp hG δ x)
  have hcardR : (Fintype.card (TorusVertex n) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (TorusVertex n) ≠ 0)
  have hmean : vertexMean (TorusVertex n) δ =
      (Fintype.card (TorusVertex n) : ℝ)⁻¹ := by
    rw [vertexMean, show (∑ x : TorusVertex n, δ x) = 1 by
      exact sum_deltaAt_eq_one (0, 0)]
    simp
  have hLapG : G.laplacian g =
      fun x => -δ x + (Fintype.card (TorusVertex n) : ℝ)⁻¹ := by
    funext x
    exact torusGraph_laplacian_torusFourierGreenPotential hn x
  have hLapU : G.laplacian u =
      fun x => -δ x + (Fintype.card (TorusVertex n) : ℝ)⁻¹ := by
    have hproj := G.laplacian_greenOp_eq_zeroSumProjection hG δ
    have hneg : G.laplacian (-(G.greenOp hG δ)) =
        -(G.laplacian (G.greenOp hG δ)) := by
      funext x
      change ((G.laplacianₗ ℝ) (-(G.greenOp hG δ))) x = _
      rw [map_neg]
      rfl
    calc
      G.laplacian u = G.laplacian (-(G.greenOp hG δ)) := by
        rfl
      _ = -(G.laplacian (G.greenOp hG δ)) := hneg
      _ = fun x => -δ x + (Fintype.card (TorusVertex n) : ℝ)⁻¹ := by
        rw [hproj]
        funext x
        simp [zeroSumProjection_apply, δ, hmean]
        ring
  have hsumG : ∑ x : TorusVertex n, g x = 0 := by
    exact torusFourierGreenPotential_sum_eq_zero
  have hsumU : ∑ x : TorusVertex n, u x = 0 := by
    calc
      ∑ x : TorusVertex n, u x = -∑ x, G.greenOp hG δ x := by simp [u]
      _ = 0 := by rw [G.greenOp_sum_eq_zero hG δ]; simp
  have hLapSub : G.laplacian (g - u) =
      G.laplacian g - G.laplacian u := by
    funext x
    exact congrFun ((G.laplacianₗ ℝ).map_sub g u) x
  have hharmonic : G.laplacian (g - u) = 0 := by
    rw [hLapSub, hLapG, hLapU]
    funext x
    change (-δ x + (Fintype.card (TorusVertex n) : ℝ)⁻¹) -
      (-δ x + (Fintype.card (TorusVertex n) : ℝ)⁻¹) = 0
    ring
  obtain ⟨c, hc⟩ := (G.laplacian_eq_zero_iff_exists_const hG (g - u)).mp hharmonic
  have hsumDiff : ∑ x : TorusVertex n, (g - u) x = 0 := by
    change (∑ x : TorusVertex n, (g x - u x)) = 0
    rw [Finset.sum_sub_distrib, hsumG, hsumU]
    simp
  have hsumConst : ∑ x : TorusVertex n, c = 0 := by
    calc
      ∑ x : TorusVertex n, c = ∑ x, (g - u) x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (congrFun hc x).symm
      _ = 0 := hsumDiff
  have hcardc : (Fintype.card (TorusVertex n) : ℝ) * c = 0 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsumConst
  have hc0 : c = 0 := (mul_eq_zero.mp hcardc).resolve_left hcardR
  have hdiffzero : g - u = 0 := by
    calc
      g - u = fun _ => c := hc
      _ = 0 := by funext x; simp [hc0]
  have hgu : g = u := sub_eq_zero.mp hdiffzero
  funext x
  change g x = u x
  exact congrFun hgu x

/-- The finite Fourier potential is the point-source Green kernel. -/
theorem torusFourierGreenPotential_eq_torusGreenKernel (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) (x : TorusVertex n) :
    torusFourierGreenPotential x = torusGreenKernel hn hG x (0, 0) := by
  rw [torusFourierGreenPotential_eq_greenOp hn hG]
  rfl

/-- Real Fourier series for the mean-zero torus Green potential. -/
theorem torusFourierGreenPotential_eq_real_sum (y : TorusVertex n) :
    torusFourierGreenPotential y =
      (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
        ∑ k ∈ Finset.univ.erase (0, 0),
          (torusCharacter k y).re / torusFourierEigenvalue k := by
  classical
  unfold torusFourierGreenPotential
  rw [torusFourierGreenComplex_eq_sum_modes, Finset.sum_apply, Complex.re_sum]
  simp_rw [torusFourierGreenMode_re]
  calc
    (∑ k ∈ Finset.univ.erase (0, 0),
        (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
          (torusFourierEigenvalue k)⁻¹ * (torusCharacter k y).re) =
      (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
        ∑ k ∈ Finset.univ.erase (0, 0),
          (torusFourierEigenvalue k)⁻¹ * (torusCharacter k y).re := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
          ∑ k ∈ Finset.univ.erase (0, 0),
            (torusCharacter k y).re / torusFourierEigenvalue k := by
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            simp only [div_eq_mul_inv]
            ring

/-- The point-source Green difference has the finite Fourier formula used in
KP (6.13). -/
theorem torusGreenKernel_difference_eq_fourier_sum (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) (x : TorusVertex n) :
    torusGreenKernel hn hG (0, 0) (0, 0) - torusGreenKernel hn hG x (0, 0) =
      (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
        ∑ k ∈ Finset.univ.erase (0, 0),
          (1 - (torusCharacter k x).re) / torusFourierEigenvalue k := by
  rw [← torusFourierGreenPotential_eq_torusGreenKernel hn hG (0, 0),
    ← torusFourierGreenPotential_eq_torusGreenKernel hn hG x,
    torusFourierGreenPotential_eq_real_sum,
    torusFourierGreenPotential_eq_real_sum]
  have horigin (k : TorusVertex n) : (torusCharacter k (0, 0)).re = 1 := by
    simp [torusCharacter]
  simp_rw [horigin]
  calc
    (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
        (∑ k ∈ Finset.univ.erase (0, 0), 1 / torusFourierEigenvalue k) -
      (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
        (∑ k ∈ Finset.univ.erase (0, 0), (torusCharacter k x).re /
          torusFourierEigenvalue k) =
        (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
          ((∑ k ∈ Finset.univ.erase (0, 0), 1 / torusFourierEigenvalue k) -
            (∑ k ∈ Finset.univ.erase (0, 0), (torusCharacter k x).re /
              torusFourierEigenvalue k)) := by ring
    _ = (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
          ∑ k ∈ Finset.univ.erase (0, 0),
            (1 / torusFourierEigenvalue k -
              (torusCharacter k x).re / torusFourierEigenvalue k) := by
            rw [← Finset.sum_sub_distrib]
    _ = (Fintype.card (TorusVertex n) : ℝ)⁻¹ *
          ∑ k ∈ Finset.univ.erase (0, 0),
            (1 - (torusCharacter k x).re) / torusFourierEigenvalue k := by
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            ring

end FroehlichSpencer.BKT.Lattice2D

end
