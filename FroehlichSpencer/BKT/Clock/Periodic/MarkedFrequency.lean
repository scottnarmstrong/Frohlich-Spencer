/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.IntegerTranslation
public import FroehlichSpencer.BKT.Generic.Marked.Gap

/-!
# Marked clock frequencies

This module connects the source's integer clock frequency to the real marked-charge API. It also
records one explicit countable frequency mixture. The mixture normalization is proved as a scalar
series; this does not assert a pointwise Fourier-series identity for the Dirac comb.

The source's marked formula immediately before (7.8) is printed with `≤`, whereas (7.8) is an
equality. The exact aggregation lemma below therefore takes exact branch identities as an input;
it never upgrades that printed inequality to an equality.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic (edgeRatio)
open FroehlichSpencer.BKT.Reduction (gffCharacter)

/-- Geometric mixture weight for source frequency `q = k + 1`: `ζ_q = 2^{-q}`. -/
def clockFrequencyWeight (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 1)

/-- The activity `z(q) = 2/ζ_q` in the clock mixture. -/
def clockFrequencyActivity (k : ℕ) : ℝ := 2 / clockFrequencyWeight k

theorem clockFrequencyWeight_pos (k : ℕ) : 0 < clockFrequencyWeight k := by
  unfold clockFrequencyWeight
  positivity

/-- The chosen positive site-frequency weights sum to one. -/
theorem tsum_clockFrequencyWeight : ∑' k : ℕ, clockFrequencyWeight k = 1 := by
  have hgeom := tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  calc
    ∑' k : ℕ, clockFrequencyWeight k =
        (1 / 2 : ℝ) * ∑' k : ℕ, (1 / 2 : ℝ) ^ k := by
          rw [show (fun k : ℕ => clockFrequencyWeight k) =
            (fun k => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k) by
              funext k
              rw [clockFrequencyWeight, pow_succ]
              ring]
          rw [tsum_mul_left]
    _ = 1 := by rw [hgeom]; norm_num

theorem summable_clockFrequencyWeight : Summable clockFrequencyWeight := by
  have hgeom := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hscaled := hgeom.mul_left (1 / 2 : ℝ)
  refine hscaled.congr fun k => ?_
  rw [clockFrequencyWeight, pow_succ]
  ring

theorem summable_norm_clockFrequencyWeight :
    Summable fun k => ‖clockFrequencyWeight k‖ := by
  refine summable_clockFrequencyWeight.congr fun k => ?_
  rw [Real.norm_eq_abs, abs_of_pos (clockFrequencyWeight_pos k)]

/-- A recursively indexed configuration of one natural frequency at each site of a finite
ordered box. -/
def ClockFrequencyTuple : ℕ → Type
  | 0 => Unit
  | m + 1 => ℕ × ClockFrequencyTuple m

/-- Product mixture coefficient of a finite frequency configuration. -/
def clockFrequencyTupleWeight : (m : ℕ) → ClockFrequencyTuple m → ℝ
  | 0, _ => 1
  | m + 1, p => clockFrequencyWeight p.1 * clockFrequencyTupleWeight m p.2

theorem clockFrequencyTupleWeight_nonneg (m : ℕ)
    (q : ClockFrequencyTuple m) : 0 ≤ clockFrequencyTupleWeight m q := by
  induction m with
  | zero => simp [clockFrequencyTupleWeight]
  | succ m ih =>
      cases q with
      | mk k tail =>
          exact mul_nonneg (clockFrequencyWeight_pos k).le (ih tail)

/-- The product weight on frequency tuples is summable at every finite depth. -/
theorem summable_clockFrequencyTupleWeight (m : ℕ) :
    Summable (clockFrequencyTupleWeight m) := by
  induction m with
  | zero =>
      change Summable (fun _ : Unit => 1)
      exact Summable.of_finite
  | succ m ih =>
      have htailNorm : Summable fun q : ClockFrequencyTuple m =>
          ‖clockFrequencyTupleWeight m q‖ := by
        refine ih.congr fun q => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (clockFrequencyTupleWeight_nonneg m q)]
      change Summable (fun p : ℕ × ClockFrequencyTuple m =>
        clockFrequencyWeight p.1 * clockFrequencyTupleWeight m p.2)
      exact summable_mul_of_summable_norm summable_norm_clockFrequencyWeight htailNorm

/-- The countable product mixture over a finite ordered box is normalized. -/
theorem tsum_clockFrequencyTupleWeight (m : ℕ) :
    ∑' q : ClockFrequencyTuple m, clockFrequencyTupleWeight m q = 1 := by
  induction m with
  | zero =>
      change ∑' _ : Unit, 1 = 1
      simp
  | succ m ih =>
      have htailNorm : Summable fun q : ClockFrequencyTuple m =>
          ‖clockFrequencyTupleWeight m q‖ := by
        refine (summable_clockFrequencyTupleWeight m).congr fun q => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (clockFrequencyTupleWeight_nonneg m q)]
      change ∑' p : ℕ × ClockFrequencyTuple m,
        clockFrequencyWeight p.1 * clockFrequencyTupleWeight m p.2 = 1
      rw [← tsum_mul_tsum_of_summable_norm summable_norm_clockFrequencyWeight htailNorm]
      rw [tsum_clockFrequencyWeight, ih]
      norm_num

theorem clockFrequencyActivity_pos (k : ℕ) : 0 < clockFrequencyActivity k :=
  div_pos (by norm_num) (clockFrequencyWeight_pos k)

/-- The frequency weight cancels its activity exactly, as in (7.6). -/
theorem clockFrequencyWeight_mul_activity (k : ℕ) :
    clockFrequencyWeight k * clockFrequencyActivity k = 2 := by
  unfold clockFrequencyActivity
  exact mul_div_cancel₀ 2 (ne_of_gt (clockFrequencyWeight_pos k))

/-- The product frequency weight for a finite box with `m` sites. The type `Fin m → ℕ` retains
one independent countable frequency index at every site. -/
def clockFrequencyConfigurationWeight (m : ℕ) (q : Fin m → ℕ) : ℝ :=
  ∏ j, clockFrequencyWeight (q j)

/-- Product of the site-dependent activities attached to a finite frequency configuration. -/
def clockFrequencyConfigurationActivity (m : ℕ) (q : Fin m → ℕ) : ℝ :=
  ∏ j, clockFrequencyActivity (q j)

theorem clockFrequencyConfigurationWeight_pos (m : ℕ) (q : Fin m → ℕ) :
    0 < clockFrequencyConfigurationWeight m q := by
  unfold clockFrequencyConfigurationWeight
  exact Finset.prod_pos fun j _ => clockFrequencyWeight_pos (q j)

/-- The configuration coefficient cancels its product activities site by site. The more refined
support-dependent multipole activity still requires the exact marked T2.3 reindexing. -/
theorem clockFrequencyConfigurationWeight_mul_activity (m : ℕ) (q : Fin m → ℕ) :
    clockFrequencyConfigurationWeight m q * clockFrequencyConfigurationActivity m q =
      (2 : ℝ) ^ m := by
  unfold clockFrequencyConfigurationWeight clockFrequencyConfigurationActivity
  rw [← Finset.prod_mul_distrib]
  simp_rw [clockFrequencyWeight_mul_activity]
  simp

private theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  norm_num at h
  exact h

private theorem two_pow_le_exp_nat (k : ℕ) :
    (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Nat.cast_succ, Real.exp_add]
      exact mul_le_mul ih two_le_exp_one (by positivity) (by positivity)

/-- The chosen activity has the source's required exponential-in-frequency bound. -/
theorem clockFrequencyActivity_le_exp (k : ℕ) :
    clockFrequencyActivity k ≤ Real.exp (2 * ((k + 1 : ℕ) : ℝ)) := by
  have hweight : clockFrequencyActivity k = (2 : ℝ) ^ (k + 2) := by
    unfold clockFrequencyActivity clockFrequencyWeight
    rw [div_eq_mul_inv]
    rw [one_div, inv_pow]
    norm_num
    ring
  rw [hweight]
  have hk : (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := two_pow_le_exp_nat k
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul two_le_exp_one two_le_exp_one
        (by norm_num) (by linarith [Real.exp_pos (1 : ℝ)])
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hpow : (2 : ℝ) ^ (k + 2) = 4 * (2 : ℝ) ^ k := by
    rw [show k + 2 = 2 + k by omega, pow_add]
    norm_num
  rw [hpow]
  calc
    4 * (2 : ℝ) ^ k ≤ Real.exp 2 * Real.exp (k : ℝ) :=
      mul_le_mul hfour hk (by positivity) (by positivity)
    _ = Real.exp (2 + k) := by rw [← Real.exp_add]
    _ ≤ Real.exp (2 * ((k + 1 : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      norm_cast
      omega

/-- On a finite clock box, an integer Fourier mode plus a marked fractional dipole is compatible
with the period `2πN`: `N(ξ/N · ϱ₀ + ϱ)` is integer-valued sitewise. -/
theorem natClock_markedDensity_compatible {d : ℕ} (N ξ : ℕ) (hN : 0 < N)
    (ϱ₀ ϱ : Fin d → ℤ) :
    ClockCompatibleCharge (N : ℝ)
      (fun j => markedDensity ((ξ : ℝ) / N) ϱ₀ ϱ j) := by
  intro j
  refine ⟨(ξ : ℤ) * ϱ₀ j + (N : ℤ) * ϱ j, ?_⟩
  simp only [markedDensity]
  push_cast
  field_simp

/-- Compact contour translation applied directly to the fractional marked density with integer
clock frequency `ξ` and integer branch charge `ϱ`. -/
theorem integral_clockBoxLaw_markedDensity_characterTranslation {d : ℕ} {E : Type*}
    [Fintype E] {G : Multigraph (Fin d) E} (N ξ : ℕ) (hN : 0 < N)
    {β : ℝ} (hβ : 0 ≤ β) (ϱ₀ ϱ a : Fin d → ℤ) :
    ∫ φ, gffCharacter (fun j => markedDensity ((ξ : ℝ) / N) ϱ₀ ϱ j) φ
        ∂clockBoxLaw β N G =
      Complex.exp (-((∑ j, (a j : ℝ) * markedDensity ((ξ : ℝ) / N) ϱ₀ ϱ j : ℝ) : ℂ)) *
        ∫ φ, gffCharacter (fun j => markedDensity ((ξ : ℝ) / N) ϱ₀ ϱ j) φ *
          edgeRatio (clockEdgeWeight β N) (G.grad (fun j => (a j : ℝ))) (G.grad φ)
          ∂clockBoxLaw β N G := by
  exact integral_clockBoxLaw_characterTranslation_compatible (n := (N : ℝ)) (β := β)
    (G := G) (by exact_mod_cast hN) hβ
    (fun j => markedDensity ((ξ : ℝ) / N) ϱ₀ ϱ j)
    (fun j => (a j : ℝ)) (natClock_markedDensity_compatible N ξ hN ϱ₀ ϱ)

/-- The restricted-harmonic hypothesis is exactly the marked gap input `η = q` for the exponential-moment estimate. -/
theorem clockRestrictedHarmonic_markedGap {N ξ : ℕ} {q : ℝ}
    (hN : 0 < N) (hξ : 0 < ξ) (hξN : ξ < N)
    (hq : q ≤ dipoleGap ((ξ : ℝ) / N)) :
    0 < (ξ : ℝ) / N ∧ (ξ : ℝ) / N < 1 ∧
      q ≤ dipoleGap ((ξ : ℝ) / N) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hξreal : (0 : ℝ) < ξ := by exact_mod_cast hξ
  have hξNreal : (ξ : ℝ) < N := by exact_mod_cast hξN
  refine ⟨div_pos hξreal hNreal, (div_lt_one hNreal).2 hξNreal, hq⟩

/-- Every nonzero marked patch charge retains the scaled-dipole gap required by the current expansion. -/
theorem clockMarkedChargedPatchGap {V : Type*} [DecidableEq V]
    {ξ' q : ℝ} (hq : q ≤ dipoleGap ξ') (o x : V) (ϱ : V → ℤ) (S : Finset V)
    (hcharge : setCharge (markedDensity ξ' (dipoleMark o x) ϱ) S ≠ 0) :
    q ≤ |setCharge (markedDensity ξ' (dipoleMark o x) ϱ) S| := by
  exact hq.trans (dipole_le_abs_setCharge o x ξ' ϱ S hcharge)

/-- If every frequency branch has an exact marked identity and the weighted branch series is
summable, their countable aggregate has the same sum. This requires equality at each branch, as
T2.3 does; the printed local `≤` before (7.8) is insufficient. -/
theorem clock_hasSum_exactMarkedBranches {ι : Type*} (w lhs rhs : ι → ℝ)
    (hExact : ∀ i, lhs i = rhs i) (hSum : Summable fun i => w i * lhs i) :
    HasSum (fun i => w i * rhs i) (∑' i, w i * lhs i) := by
  have hR : Summable fun i => w i * rhs i := hSum.congr fun i => by rw [hExact i]
  have hsum : (∑' i, w i * rhs i) = ∑' i, w i * lhs i :=
    tsum_congr fun i => by rw [hExact i]
  rw [← hsum]
  exact hR.hasSum

end FroehlichSpencer.BKT.Clock.Periodic

end
