module
public import FroehlichSpencer.FS82.Infinite.FourierGreen
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

open Filter Topology
open FroehlichSpencer.FS82.Infinite.Fourier

namespace FroehlichSpencer.FS82.Infinite.Nonsummability

abbrev SpectralIndex := Fin 4
abbrev WaveVector := SpectralIndex → ℝ

noncomputable def chordSquared (x : ℝ) : ℝ :=
  ‖Complex.exp ((Complex.I : ℂ) * x) - 1‖ ^ 2

theorem chordSquared_zero : chordSquared 0 = 0 := by
  simp [chordSquared]


theorem chordSquared_eq_fourier_chordSq (x : ℝ) :
    chordSquared (2 * Real.pi * x) = chordSq x := by
  rw [chordSquared, Complex.norm_exp_I_mul_ofReal_sub_one, chordSq_eq]
  have harg : (2 * Real.pi * x) / 2 = Real.pi * x := by ring
  rw [harg]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

theorem chordSquared_pos {x : ℝ} (hx : 0 < x) (hxp : x < 2 * Real.pi) :
    0 < chordSquared x := by
  have hsin : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith)
  have hnorm : 0 < ‖(2 * Real.sin (x / 2) : ℝ)‖ :=
    norm_pos_iff.mpr (by positivity)
  rw [chordSquared, Complex.norm_exp_I_mul_ofReal_sub_one]
  exact sq_pos_of_pos hnorm

noncomputable def curlMultiplier (i j : SpectralIndex) (k : WaveVector) : ℝ :=
  let denominator := ∑ a : SpectralIndex, chordSquared (k a)
  if denominator = 0 then 0 else
    (chordSquared (k i) + chordSquared (k j)) / denominator

def axisWave (i : SpectralIndex) (s : ℝ) : WaveVector :=
  fun a => if a = i then s else 0

theorem chordSquared_axis_sum (i : SpectralIndex) (s : ℝ) :
    (∑ a : SpectralIndex, chordSquared (axisWave i s a)) = chordSquared s := by
  classical
  rw [Finset.sum_eq_single i]
  · simp [axisWave]
  · intro a ha hai
    simp [axisWave, hai, chordSquared_zero]
  · simp

theorem curlMultiplier_axis_in (i j : SpectralIndex) (hij : i ≠ j)
    {s : ℝ} (hs : chordSquared s ≠ 0) :
    curlMultiplier i j (axisWave i s) = 1 := by
  have hden : (∑ a : SpectralIndex, chordSquared (axisWave i s a)) = chordSquared s :=
    chordSquared_axis_sum i s
  have hnum : chordSquared (axisWave i s i) + chordSquared (axisWave i s j) =
      chordSquared s := by
    have hji : j ≠ i := Ne.symm hij
    simp [axisWave, chordSquared_zero, hji]
  simp [curlMultiplier, hden, hnum, hs]

theorem curlMultiplier_axis_out (i j ℓ : SpectralIndex)
    (hli : ℓ ≠ i) (hlj : ℓ ≠ j) {s : ℝ} (hs : chordSquared s ≠ 0) :
    curlMultiplier i j (axisWave ℓ s) = 0 := by
  have hden : (∑ a : SpectralIndex, chordSquared (axisWave ℓ s a)) = chordSquared s :=
    chordSquared_axis_sum ℓ s
  have hnum : chordSquared (axisWave ℓ s i) + chordSquared (axisWave ℓ s j) = 0 := by
    have hil : i ≠ ℓ := Ne.symm hli
    have hjl : j ≠ ℓ := Ne.symm hlj
    simp [axisWave, chordSquared_zero, hil, hjl]
  simp [curlMultiplier, hden, hnum, hs]


noncomputable def directionalScale (n : ℕ) : ℝ := Real.pi / ((n : ℝ) + 1)

theorem directionalScale_tendsto_zero :
    Tendsto directionalScale atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv := tendsto_inv_atTop_zero.comp hden
  unfold directionalScale
  simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv

theorem directionalScale_pos (n : ℕ) : 0 < directionalScale n := by
  unfold directionalScale
  positivity

theorem directionalScale_lt_two_pi (n : ℕ) : directionalScale n < 2 * Real.pi := by
  unfold directionalScale
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 1 ≤ (n : ℝ) + 1 := by nlinarith
  have hle : Real.pi / ((n : ℝ) + 1) ≤ Real.pi := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [Real.pi_pos]
  linarith [Real.pi_pos]

theorem directionalScale_chord_ne_zero (n : ℕ) : chordSquared (directionalScale n) ≠ 0 :=
  (chordSquared_pos (directionalScale_pos n) (directionalScale_lt_two_pi n)).ne'


theorem axisWave_continuous (i : SpectralIndex) : Continuous (axisWave i) := by
  apply continuous_pi
  intro a
  by_cases h : a = i <;> simp [axisWave, h] <;> fun_prop

theorem axisWave_tendsto_zero (i : SpectralIndex) :
    Tendsto (fun n : ℕ => axisWave i (directionalScale n)) atTop (𝓝 (0 : WaveVector)) := by
  have h := (axisWave_continuous i).continuousAt.tendsto.comp directionalScale_tendsto_zero
  have hz : axisWave i 0 = (0 : WaveVector) := by
    funext a
    simp [axisWave]
  simpa [hz, Function.comp_def] using h


end FroehlichSpencer.FS82.Infinite.Nonsummability
