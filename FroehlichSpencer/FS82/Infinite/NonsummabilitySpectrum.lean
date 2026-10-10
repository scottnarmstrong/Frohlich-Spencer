/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.FourierApproximation
public import FroehlichSpencer.FS82.Infinite.NonsummabilityMultiplier
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

open Filter Topology
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Infinite.FourierApproximation
open scoped ComplexConjugate

namespace FroehlichSpencer.FS82.Infinite.Nonsummability

private theorem continuous_fourierChar (n : ℤ) :
    Continuous (fun t : AddCircle (1 : ℝ) => fourier n t) :=
  map_continuous (fourier n)

noncomputable def waveToTorus (k : WaveVector) : Torus4 :=
  ((k 0 / (2 * Real.pi) : ℝ),
    ((k 1 / (2 * Real.pi) : ℝ),
      ((k 2 / (2 * Real.pi) : ℝ), (k 3 / (2 * Real.pi) : ℝ))))

theorem waveToTorus_zero : waveToTorus 0 = (0 : Torus4) := by
  ext <;> simp [waveToTorus]

theorem continuous_waveToTorus : Continuous waveToTorus := by
  fun_prop [waveToTorus]

noncomputable def torusChordSquared (k : Torus4) (i : SpectralIndex) : ℝ :=
  Complex.normSq (1 - fourier 1 (torus4Coord k i))

noncomputable def torusCurlMultiplier (i j : SpectralIndex) (k : Torus4) : ℝ :=
  let denominator := ∑ a : SpectralIndex, torusChordSquared k a
  if denominator = 0 then 0 else
    (torusChordSquared k i + torusChordSquared k j) / denominator

theorem torusChordSquared_waveToTorus (k : WaveVector) (i : SpectralIndex) :
    torusChordSquared (waveToTorus k) i = chordSquared (k i) := by
  have hcoord : torus4Coord (waveToTorus k) i =
      ((k i / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) := by
    fin_cases i <;> rfl
  rw [torusChordSquared, hcoord]
  change chordSq (k i / (2 * Real.pi)) = chordSquared (k i)
  rw [← chordSquared_eq_fourier_chordSq (k i / (2 * Real.pi))]
  congr 1
  field_simp [ne_of_gt Real.pi_pos]

theorem torusCurlMultiplier_waveToTorus (i j : SpectralIndex) (k : WaveVector) :
    torusCurlMultiplier i j (waveToTorus k) = curlMultiplier i j k := by
  unfold torusCurlMultiplier curlMultiplier
  simp_rw [torusChordSquared_waveToTorus]


theorem torusChordSquared_zero (i : SpectralIndex) :
    torusChordSquared (0 : Torus4) i = 0 := by
  fin_cases i <;> simp [torusChordSquared, torus4Coord]

private theorem torus4Coord_neg (k : Torus4) (i : SpectralIndex) :
    torus4Coord (-k) i = -torus4Coord k i := by
  fin_cases i <;> simp [torus4Coord]

theorem torusChordSquared_neg (k : Torus4) (i : SpectralIndex) :
    torusChordSquared (-k) i = torusChordSquared k i := by
  unfold torusChordSquared
  rw [torus4Coord_neg]
  have hfourier : fourier 1 (-torus4Coord k i) =
      conj (fourier 1 (torus4Coord k i)) := by
    rw [fourier_one, fourier_one, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
  rw [hfourier]
  have hconj : (1 : ℂ) - conj (fourier 1 (torus4Coord k i)) =
      conj (1 - fourier 1 (torus4Coord k i)) := by simp
  rw [hconj, Complex.normSq_conj]

theorem torusCurlMultiplier_neg (i j : SpectralIndex) (k : Torus4) :
    torusCurlMultiplier i j (-k) = torusCurlMultiplier i j k := by
  simp [torusCurlMultiplier, torusChordSquared_neg]

private theorem continuous_torus4Coord (i : SpectralIndex) :
    Continuous (fun k : Torus4 => torus4Coord k i) := by
  fin_cases i <;> simp [torus4Coord] <;> fun_prop

theorem continuous_torusChordSquared (i : SpectralIndex) :
    Continuous (fun k : Torus4 => torusChordSquared k i) := by
  unfold torusChordSquared
  have hfourier : Continuous (fun k : Torus4 =>
      fourier 1 (torus4Coord k i)) :=
    (continuous_fourierChar 1).comp (continuous_torus4Coord i)
  exact Complex.continuous_normSq.comp (continuous_const.sub hfourier)

theorem continuousAt_torusCurlMultiplier_of_denominator_ne_zero
    (i j : SpectralIndex) (k : Torus4)
    (hden : (∑ a : SpectralIndex, torusChordSquared k a) ≠ 0) :
    ContinuousAt (torusCurlMultiplier i j) k := by
  let denominator : Torus4 → ℝ := fun z => ∑ a : SpectralIndex, torusChordSquared z a
  let numerator : Torus4 → ℝ := fun z =>
    torusChordSquared z i + torusChordSquared z j
  have hdenCont : ContinuousAt denominator k := by
    have h : Continuous denominator := by
      dsimp [denominator]
      exact continuous_finsetSum _ fun a ha => continuous_torusChordSquared a
    exact h.continuousAt
  have hnumCont : ContinuousAt numerator k := by
    dsimp [numerator]
    exact (continuous_torusChordSquared i).continuousAt.add
      (continuous_torusChordSquared j).continuousAt
  have hquot : ContinuousAt (fun z => numerator z / denominator z) k :=
    hnumCont.div hdenCont hden
  have heq : (fun z => torusCurlMultiplier i j z) =ᶠ[𝓝 k]
      (fun z => numerator z / denominator z) := by
    filter_upwards [hdenCont.eventually_ne hden] with z hz
    simp [torusCurlMultiplier, numerator, denominator, hz]
  exact hquot.congr heq.symm

theorem torusChordSquared_nonneg (k : Torus4) (i : SpectralIndex) :
    0 ≤ torusChordSquared k i :=
  Complex.normSq_nonneg _

theorem torusChordSquared_pos_of_coord_ne_zero {k : Torus4} {i : SpectralIndex}
    (hi : torus4Coord k i ≠ 0) : 0 < torusChordSquared k i := by
  have hfourier : fourier 1 (torus4Coord k i) ≠ 1 := by
    intro h
    have hcircleCoe :
        (AddCircle.toCircle (torus4Coord k i) : ℂ) =
          (AddCircle.toCircle (0 : AddCircle (1 : ℝ)) : ℂ) := by
      simpa [fourier_one] using h
    have hcircle : AddCircle.toCircle (torus4Coord k i) =
        AddCircle.toCircle (0 : AddCircle (1 : ℝ)) :=
      Circle.coe_inj.mp hcircleCoe
    exact hi (AddCircle.injective_toCircle
      (by norm_num : (1 : ℝ) ≠ 0) hcircle)
  have hne : (1 : ℂ) - fourier 1 (torus4Coord k i) ≠ 0 :=
    sub_ne_zero.mpr hfourier.symm
  have hnorm : 0 < ‖(1 : ℂ) - fourier 1 (torus4Coord k i)‖ :=
    norm_pos_iff.mpr hne
  rw [torusChordSquared, Complex.normSq_eq_norm_sq]
  positivity

theorem torusCurlDenominator_pos {k : Torus4} (hk : k ≠ 0) :
    0 < ∑ a : SpectralIndex, torusChordSquared k a := by
  have hcoord : ∃ i : SpectralIndex, torus4Coord k i ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : torus4Coord k 0 = 0 := h 0
    have h1 : torus4Coord k 1 = 0 := h 1
    have h2 : torus4Coord k 2 = 0 := h 2
    have h3 : torus4Coord k 3 = 0 := h 3
    cases k with
    | mk k0 k123 =>
      cases k123 with
      | mk k1 k23 =>
        cases k23 with
        | mk k2 k3 =>
          simp [torus4Coord] at h0 h1 h2 h3
          subst k0
          subst k1
          subst k2
          subst k3
          exact hk rfl
  obtain ⟨i, hi⟩ := hcoord
  apply Finset.sum_pos'
  · intro a ha
    exact torusChordSquared_nonneg k a
  · exact ⟨i, Finset.mem_univ _, torusChordSquared_pos_of_coord_ne_zero hi⟩

theorem torusCurlMultiplier_continuousAt {k : Torus4} (hk : k ≠ 0) :
    ContinuousAt (torusCurlMultiplier 0 1) k :=
  continuousAt_torusCurlMultiplier_of_denominator_ne_zero 0 1 k
    (torusCurlDenominator_pos hk).ne'

theorem torusCurlMultiplier_axis_in (i j : SpectralIndex) (hij : i ≠ j)
    (n : ℕ) :
    torusCurlMultiplier i j (waveToTorus (axisWave i (directionalScale n))) = 1 := by
  rw [torusCurlMultiplier_waveToTorus]
  exact curlMultiplier_axis_in i j hij (directionalScale_chord_ne_zero n)

theorem torusCurlMultiplier_axis_out (i j ℓ : SpectralIndex)
    (hli : ℓ ≠ i) (hlj : ℓ ≠ j) (n : ℕ) :
    torusCurlMultiplier i j (waveToTorus (axisWave ℓ (directionalScale n))) = 0 := by
  rw [torusCurlMultiplier_waveToTorus]
  exact curlMultiplier_axis_out i j ℓ hli hlj (directionalScale_chord_ne_zero n)

noncomputable def latticeFourierSeries (G : LatticePoint → ℝ) (k : Torus4) : ℂ :=
  ∑' x : LatticePoint, (G x : ℂ) * latticeCharacter x k

theorem continuous_latticeFourierSeries (G : LatticePoint → ℝ)
    (hG : Summable (fun x => |G x|)) :
    Continuous (latticeFourierSeries G) := by
  unfold latticeFourierSeries
  apply continuous_tsum
  · intro x
    exact continuous_const.mul (continuous_latticeCharacter x)
  · exact hG
  · intro x k
    simp [latticeCharacter]

noncomputable def latticeFourierSeriesReal (G : LatticePoint → ℝ) :
    Torus4 → ℝ := fun k => (latticeFourierSeries G k).re

theorem continuous_latticeFourierSeriesReal (G : LatticePoint → ℝ)
    (hG : Summable (fun x => |G x|)) :
    Continuous (latticeFourierSeriesReal G) := by
  exact Complex.continuous_re.comp (continuous_latticeFourierSeries G hG)

abbrev FiniteRealTest := LatticePoint →₀ ℂ

noncomputable def finiteTestFourierWeight (f : FiniteRealTest) (k : Torus4) : ℝ :=
  Complex.normSq (realFourierPoly f k)

noncomputable def finiteTestMass (f : FiniteRealTest) : ℝ :=
  ∫ k : Torus4, finiteTestFourierWeight f k ∂torus4Haar

noncomputable def finiteTestAverage (g : Torus4 → ℝ) (f : FiniteRealTest) : ℝ :=
  (∫ k : Torus4, g k * finiteTestFourierWeight f k ∂torus4Haar) /
    finiteTestMass f

/- A localizing family is a sequence of finite-support real tests whose normalized Fourier
   weights sample every even observable continuously at the selected frequency.  For the
   four-torus, the intended witnesses are the symmetrized plane-wave Fejér windows. -/


end FroehlichSpencer.FS82.Infinite.Nonsummability
