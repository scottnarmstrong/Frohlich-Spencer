/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.MarkedFrequency

/-!
# Positive-type normalization comparison

This is the finite marked-ensemble numerator/normalizer comparison used in FS81 (5.34)–(5.35).
The hypothesis `hposType` is the positive-type step: adding the renormalized marked factor does
not lower the branch normalizer. The theorem proves the weighted comparison and strict
normalization once that branch fact holds. It does not assert that the positive-type premise has
yet been verified for the compact clock law, nor does it pass a countable frequency sum through an
integral.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

/-- Absolute numerator control passes through a finite nonnegative mixture when the unmarked
branch normalizers are bounded above by the positive-type marked normalizers. -/
theorem abs_sum_frequencyNumerator_le {ι : Type*} (S : Finset ι)
    (w a b d : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hposType : ∀ i ∈ S, b i ≤ d i)
    (hbranch : ∀ i ∈ S, |a i| ≤ M * b i) :
    |∑ i ∈ S, w i * a i| ≤ M * (∑ i ∈ S, w i * d i) := by
  have hterm : ∀ i ∈ S, |w i * a i| ≤ M * (w i * d i) := by
    intro i hi
    calc
      |w i * a i| = w i * |a i| := by rw [abs_mul, abs_of_nonneg (hw i hi)]
      _ ≤ w i * (M * b i) := mul_le_mul_of_nonneg_left (hbranch i hi) (hw i hi)
      _ ≤ w i * (M * d i) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hposType i hi) hM) (hw i hi)
      _ = M * (w i * d i) := by ring
  calc
    |∑ i ∈ S, w i * a i| ≤ ∑ i ∈ S, |w i * a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, M * (w i * d i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = M * (∑ i ∈ S, w i * d i) := by simp_rw [← Finset.mul_sum]

/-- The finite positive-type comparison after normalization. One positive branch witnesses strict
positivity of the mixed marked normalizer; the numerator may be signed. -/
theorem abs_normalized_sum_frequencyNumerator_le {ι : Type*} (S : Finset ι)
    (w a b d : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hb : ∀ i ∈ S, 0 ≤ b i)
    (hposType : ∀ i ∈ S, b i ≤ d i)
    (hbranch : ∀ i ∈ S, |a i| ≤ M * b i)
    (i₀ : ι) (hi₀ : i₀ ∈ S) (hwi₀ : 0 < w i₀) (hbi₀ : 0 < b i₀) :
    |(∑ i ∈ S, w i * a i) / (∑ i ∈ S, w i * d i)| ≤ M := by
  have htermNonneg : ∀ i ∈ S, 0 ≤ w i * d i := fun i hi =>
    mul_nonneg (hw i hi) (le_trans (hb i hi) (hposType i hi))
  have hden : 0 < ∑ i ∈ S, w i * d i := by
    have hpos : 0 < w i₀ * d i₀ :=
      mul_pos hwi₀ (lt_of_lt_of_le hbi₀ (hposType i₀ hi₀))
    exact lt_of_lt_of_le hpos (Finset.single_le_sum htermNonneg hi₀)
  rw [abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  exact abs_sum_frequencyNumerator_le S w a b d hM hw hposType hbranch

end FroehlichSpencer.BKT.Clock.Periodic

end
