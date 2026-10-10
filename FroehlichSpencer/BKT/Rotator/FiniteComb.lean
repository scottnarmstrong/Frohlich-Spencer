/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselSchwartz
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Pi

/-!
# Finite frequency combs on pinned face fields

For a finite set of face coordinates, this module defines the symmetric finite-frequency comb,
proves its integral against an integrable density is the corresponding finite sum of Fourier
coefficients, and proves these box cutoffs converge whenever the coefficient family is summable.
The height-sampling identity is also recorded in bounded-face coordinates. The multidimensional
Poisson theorem needed to identify the Fourier-coefficient sum with the height partition sum
remains a separate proof obligation.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open scoped Real FourierTransform
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Lattice2D

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

/-- A frequency assignment on each coordinate of a finite face set. The proof field is retained
so that finite boxes are represented by `Finset.pi` without choosing an enumeration. -/
abbrev FaceFrequency (ι : Type*) [Fintype ι] :=
  ∀ i : ι, i ∈ (Finset.univ : Finset ι) → ℤ

/-- The symmetric frequency box `|qᵢ| ≤ N` in a finite-dimensional integer lattice. -/
def faceFrequencyBox {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) :
    Finset (FaceFrequency ι) :=
  Finset.pi Finset.univ fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

private theorem faceFrequencyBox_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (q : FaceFrequency ι) :
    q ∈ faceFrequencyBox (ι := ι) N ↔
      ∀ i, q i (Finset.mem_univ i) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  classical
  simp [faceFrequencyBox, Finset.mem_pi]

private theorem faceFrequencyBox_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : ℕ} (hMN : M ≤ N) :
    faceFrequencyBox (ι := ι) M ⊆ faceFrequencyBox N := by
  intro q hq
  rw [faceFrequencyBox_mem] at hq ⊢
  intro i
  have h := hq i
  rw [Finset.mem_Icc] at h ⊢
  constructor <;> omega

private theorem exists_faceFrequencyBox_superset {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : Finset (FaceFrequency ι)) :
    ∃ N, s ⊆ faceFrequencyBox (ι := ι) N := by
  classical
  let R : ℕ := s.sup fun q =>
    Finset.univ.sup fun i => (q i (Finset.mem_univ i)).natAbs
  refine ⟨R, fun q hq => (faceFrequencyBox_mem R q).2 fun i => ?_⟩
  have hnat : (q i (Finset.mem_univ i)).natAbs ≤ R := by
    dsimp [R]
    exact (Finset.le_sup (s := Finset.univ)
      (f := fun i => (q i (Finset.mem_univ i)).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (s := s)
        (f := fun q => Finset.univ.sup fun i => (q i (Finset.mem_univ i)).natAbs) hq)
  have hcast : ((q i (Finset.mem_univ i)).natAbs : ℤ) ≤ R := by exact_mod_cast hnat
  rw [Finset.mem_Icc]
  constructor
  · have hleft : -(q i (Finset.mem_univ i)) ≤
        ((q i (Finset.mem_univ i)).natAbs : ℤ) :=
    (by simpa [Int.natAbs_neg] using
      (Int.le_natAbs (a := -(q i (Finset.mem_univ i)))))
    linarith
  · exact (Int.le_natAbs (a := q i (Finset.mem_univ i))).trans hcast

private theorem faceFrequencyBox_tendsto_atTop {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    Tendsto (faceFrequencyBox (ι := ι)) atTop
      (atTop : Filter (Finset (FaceFrequency ι))) := by
  classical
  apply tendsto_atTop.2
  intro s
  obtain ⟨N, hN⟩ := exists_faceFrequencyBox_superset s
  filter_upwards [eventually_ge_atTop N] with M hM
  exact hN.trans (faceFrequencyBox_mono hM)

/-- The signed torus character for a multi-face frequency. -/
def faceCombMode {ι : Type*} [Fintype ι] (q : FaceFrequency ι)
    (x : ι → ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * ∑ i : ι, x i * (q i (Finset.mem_univ i) : ℝ) : ℝ) : ℂ) * I)

private theorem faceCombMode_norm {ι : Type*} [Fintype ι] (q : FaceFrequency ι)
    (x : ι → ℝ) : ‖faceCombMode q x‖ = 1 := by
  unfold faceCombMode
  have hre :
      (((( -2 * Real.pi * ∑ i : ι, x i * (q i (Finset.mem_univ i) : ℝ) : ℝ) : ℂ) * I).re) = 0 := by
    simp [Complex.mul_re]
  rw [Complex.norm_exp, hre, Real.exp_zero]

/-- The finite symmetric frequency cutoff for the pinned `|ι|`-coordinate comb. -/
def faceCombCutoff {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (x : ι → ℝ) : ℂ :=
  ∑ q ∈ faceFrequencyBox (ι := ι) N, faceCombMode q x

/-- A Fourier coefficient of a density on the real pinned-coordinate space, with the negative
phase convention used by the one-face cutoff. -/
def faceFourierCoefficient {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (q : FaceFrequency ι) : ℂ :=
  ∫ x : ι → ℝ, faceCombMode q x * f x

private theorem integrable_faceCombMode_mul {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℂ} (hf : Integrable f)
    (q : FaceFrequency ι) : Integrable (fun x => faceCombMode q x * f x) := by
  have hmode : Continuous fun x : ι → ℝ => faceCombMode q x := by
    fun_prop [faceCombMode]
  refine hf.norm.mono' (hmode.aestronglyMeasurable.mul hf.1) ?_
  filter_upwards with x
  rw [norm_mul, faceCombMode_norm, one_mul]

/-- Pairing a finite multi-face comb cutoff with an integrable density is exactly its finite sum
of Fourier coefficients. This also proves the required finite-sum / integral exchange. -/
theorem integral_faceCombCutoff_mul_eq_sum {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℂ} (hf : Integrable f) (N : ℕ) :
    (∫ x : ι → ℝ, faceCombCutoff (ι := ι) N x * f x) =
      ∑ q ∈ faceFrequencyBox (ι := ι) N, faceFourierCoefficient f q := by
  classical
  let s := faceFrequencyBox (ι := ι) N
  calc
    _ = ∫ x : ι → ℝ, ∑ q ∈ s, faceCombMode q x * f x := by
      congr 1
      funext x
      simp [faceCombCutoff, s, Finset.sum_mul]
    _ = ∑ q ∈ s, ∫ x : ι → ℝ, faceCombMode q x * f x := by
      rw [integral_finsetSum (s := s) (f := fun q x => faceCombMode q x * f x)
        (by intro q hq; exact integrable_faceCombMode_mul hf q)]
    _ = ∑ q ∈ s, faceFourierCoefficient f q := by
      rfl

/-- Symmetric frequency boxes exhaust every finite subset of the multi-face lattice. -/
theorem faceFrequencyBox_exhausts {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : FaceFrequency ι → ℂ} (hg : Summable g) :
    Tendsto (fun N : ℕ => ∑ q ∈ faceFrequencyBox (ι := ι) N, g q) atTop
      (𝓝 (∑' q, g q)) := by
  classical
  have hs := hg.hasSum
  change Tendsto (fun s : Finset (FaceFrequency ι) => ∑ q ∈ s, g q) atTop
      (𝓝 (∑' q, g q)) at hs
  exact hs.comp (faceFrequencyBox_tendsto_atTop (ι := ι))

/-- The multi-face finite comb pairings converge to the Fourier-coefficient sum whenever the
coefficient family is summable. -/
theorem faceCombCutoffPairing_tendsto_fourier {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℂ} (hf : Integrable f)
    (hcoeff : Summable (faceFourierCoefficient f)) :
    Tendsto (fun N : ℕ =>
      ∫ x : ι → ℝ, faceCombCutoff (ι := ι) N x * f x) atTop
      (𝓝 (∑' q, faceFourierCoefficient f q)) := by
  have hsum := faceFrequencyBox_exhausts hcoeff
  exact hsum.congr' (Filter.Eventually.of_forall fun N =>
    (integral_faceCombCutoff_mul_eq_sum hf N).symm)

/-- Embed bounded-face coordinates by pinning the exterior value to zero. -/
def rotatorPinnedRealFieldOfCoords {L : ℕ} (x : SquareFreeVertex L → ℝ) :
    RotatorPinnedRealField L :=
  ⟨fun p => p.elim 0 x, rfl⟩

/-- The literal interpolated density in bounded-face coordinates, with the exterior face fixed to
zero and every edge crossing the boundary retained. -/
def rotatorPinnedInterpolatedDensityCoords (L : ℕ) (β : ℝ)
    (x : SquareFreeVertex L → ℝ) : ℂ :=
  rotatorPinnedInterpolatedDensity L β (rotatorPinnedRealFieldOfCoords x)

/-- Integer height coordinates, omitting the pinned exterior value. -/
def rotatorFaceHeightCoords {L : ℕ} (h : RotatorFaceHeight L) : SquareFreeVertex L → ℤ :=
  fun v => h.1 (some v)

private theorem rotatorPinnedRealFieldOfCoords_height {L : ℕ}
    (h : RotatorFaceHeight L) :
    rotatorPinnedRealFieldOfCoords (fun v => (rotatorFaceHeightCoords h v : ℝ)) =
      rotatorPinnedRealFieldOfHeight h := by
  apply Subtype.ext
  funext p
  cases p with
  | none => simp [rotatorPinnedRealFieldOfCoords, rotatorPinnedRealFieldOfHeight, h.2]
  | some v => rfl

/-- The height partition factor is the sum of the coordinate density over pinned integer fields.
This is the sampling identity needed on the Poisson side of the multi-face comb. -/
theorem rotatorHeightPartitionFactor_eq_coordsSum {L : ℕ} (β : ℝ) (hβ : 0 < β) :
    rotatorHeightPartitionFactor L β =
      ∑' h : RotatorFaceHeight L,
        rotatorPinnedInterpolatedDensityCoords L β
          (fun v => (rotatorFaceHeightCoords h v : ℝ)) := by
  rw [rotatorHeightPartitionFactor_eq_pinnedRealLatticeSum (L := L) β hβ]
  apply tsum_congr
  intro h
  rw [rotatorPinnedInterpolatedDensityCoords, rotatorPinnedRealFieldOfCoords_height]

/-- The actual finite-frequency comb pairing against the pinned interpolated real-field density
in the `L²` bounded-face coordinates. -/
def rotatorPinnedCombCutoffPairing (L : ℕ) (β : ℝ) (N : ℕ) : ℂ :=
  ∫ x : SquareFreeVertex L → ℝ,
    faceCombCutoff (ι := SquareFreeVertex L) N x *
      rotatorPinnedInterpolatedDensityCoords L β x

/-- The literal finite-frequency identity in every volume, with the integral and finite frequency
sum exchanged exactly. -/
theorem rotatorPinnedCombCutoffPairing_eq_sum {L : ℕ} (β : ℝ) (N : ℕ)
    (hInt : Integrable (rotatorPinnedInterpolatedDensityCoords L β)) :
    rotatorPinnedCombCutoffPairing L β N =
      ∑ q ∈ faceFrequencyBox (ι := SquareFreeVertex L) N,
        faceFourierCoefficient (rotatorPinnedInterpolatedDensityCoords L β) q := by
  exact integral_faceCombCutoff_mul_eq_sum hInt N

end FroehlichSpencer.BKT.Rotator

end
