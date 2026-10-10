/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Properties
public import FroehlichSpencer.BKT.Rotator.XYDuality
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt

/-!
# Pinned interpolation and finite comb cutoffs

The exterior face is pinned to zero throughout. The first theorem records the integer-height
partition factor as the same finite-volume sum with the interpolated edge weight. The one-face
finite-volume comb theorem then uses symmetric finite frequency cutoffs and Mathlib's Poisson
summation theorem. Its remaining analytic interface is explicit: the pinned real density must be
realized as a Schwartz function. No probability measure on absolute fields or nonneutral
zero-mode identity is introduced.
-/

@[expose] public section

open Complex MeasureTheory
open Asymptotics
open Filter Topology
open scoped FourierTransform SchwartzMap
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.BesselInterp

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- The zero-exterior integer-height weight, written with Appendix-B interpolation factors. -/
def rotatorInterpolatedHeightWeight (L : ℕ) (β : ℝ) (h : RotatorFaceHeight L) : ℂ :=
  ∏ e : RotatorInternalBond L, besselInterp β (rotatorFaceHeightCurrent h e)

/-- Real dual-face fields with the exterior mode pinned to zero. This finite carrier removes the
constant mode before any comb pairing is taken. -/
abbrev RotatorPinnedRealField (L : ℕ) :=
  {φ : RotatorDualFace L → ℝ // φ none = 0}

/-- Embed an integer zero-exterior face height into the pinned real-field carrier. -/
def rotatorPinnedRealFieldOfHeight (h : RotatorFaceHeight L) : RotatorPinnedRealField L :=
  ⟨fun p => (h.1 p : ℝ), by
    change ((h.1 none : ℤ) : ℝ) = 0
    rw [h.2]
    simp⟩

/-- The finite-volume pinned real-field density with the literal interpolated bond factors. -/
def rotatorPinnedInterpolatedDensity (L : ℕ) (β : ℝ)
    (φ : RotatorPinnedRealField L) : ℂ :=
  ∏ e : RotatorInternalBond L,
    besselInterp β
      ((φ.1 ((rotatorDualGraph L).src e) - φ.1 ((rotatorDualGraph L).tgt e) : ℝ) : ℂ)

/-- Integer agreement converts the entire pinned-height partition sum to interpolated weights. -/
theorem rotatorHeightPartitionFactor_eq_interpolated (β : ℝ) (hβ : 0 < β) :
    rotatorHeightPartitionFactor L β =
      ∑' h : RotatorFaceHeight L, rotatorInterpolatedHeightWeight L β h := by
  unfold rotatorHeightPartitionFactor rotatorInterpolatedHeightWeight
  apply tsum_congr
  intro h
  apply Finset.prod_congr rfl
  intro e he
  exact (besselInterp_intCast_eq_rotatorI hβ (rotatorFaceHeightCurrent h e)).symm

/-- On integer fields the real pinned density is exactly the interpolated integer-height weight,
including every boundary-crossing bond to the zero exterior. -/
theorem rotatorPinnedInterpolatedDensity_on_integerHeight (β : ℝ)
    (h : RotatorFaceHeight L) :
    rotatorPinnedInterpolatedDensity L β (rotatorPinnedRealFieldOfHeight h) =
      rotatorInterpolatedHeightWeight L β h := by
  unfold rotatorPinnedInterpolatedDensity rotatorInterpolatedHeightWeight
  apply Finset.prod_congr rfl
  intro e he
  congr 1
  simp only [rotatorPinnedRealFieldOfHeight]
  simp [rotatorFaceHeightCurrent, Complex.ofReal_sub, Int.cast_sub]

/-- The full zero-exterior integer-height partition factor is the lattice sum of the pinned real
interpolated density. This is the discrete comb side of the finite-volume representation, with the
constant mode already removed. -/
theorem rotatorHeightPartitionFactor_eq_pinnedRealLatticeSum (β : ℝ) (hβ : 0 < β) :
    rotatorHeightPartitionFactor L β =
      ∑' h : RotatorFaceHeight L,
        rotatorPinnedInterpolatedDensity L β (rotatorPinnedRealFieldOfHeight h) := by
  rw [rotatorHeightPartitionFactor_eq_interpolated (L := L) β hβ]
  apply tsum_congr
  intro h
  exact (rotatorPinnedInterpolatedDensity_on_integerHeight (L := L) β h).symm

/-- The unique bounded face in the one-face free box. -/
def rotatorOneFace : SquareFreeVertex 1 :=
  (⟨0, by omega⟩, ⟨0, by omega⟩)

/-- Integer heights in the one-face box, with the exterior height pinned at zero. -/
def rotatorOneFaceIntegerHeight (n : ℤ) : RotatorFaceHeight 1 :=
  ⟨fun p => p.elim 0 (fun _ => n), rfl⟩

/-- The pinned one-face height carrier is canonically the integers. -/
def rotatorOneFaceHeightEquiv : ℤ ≃ RotatorFaceHeight 1 where
  toFun := rotatorOneFaceIntegerHeight
  invFun h := h.1 (some rotatorOneFace)
  left_inv := by intro n; rfl
  right_inv := by
    intro h
    apply Subtype.ext
    funext p
    cases p with
    | none => exact h.2.symm
    | some p =>
      have hp : p = rotatorOneFace := Subsingleton.elim _ _
      subst p
      rfl

/-- The real one-face field has its exterior/root value fixed at zero. -/
def rotatorOneFaceRealField (x : ℝ) : RotatorDualFace 1 → ℝ :=
  fun p => p.elim 0 (fun _ => x)

/-- The pinned one-face real density, with one interpolated factor for each internal free-box bond.
Each bond crosses a dual edge, and the endpoint at the exterior face reads zero. -/
def rotatorOneFacePinnedDensity (β x : ℝ) : ℂ :=
  ∏ e : RotatorInternalBond 1,
    besselInterp β
      ((rotatorOneFaceRealField x ((rotatorDualGraph 1).src e) -
        rotatorOneFaceRealField x ((rotatorDualGraph 1).tgt e) : ℝ) : ℂ)

/-- The finite symmetric frequency cutoff of the pinned integer comb. The sign is the Fourier
transform convention; symmetric frequency windows make it the same cutoff as the positive-phase
comb in FS81 (6.5). -/
def rotatorOneFaceCombCutoff (N : ℕ) (x : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    Complex.exp (((-2 * Real.pi * x * (q : ℝ) : ℝ) : ℂ) * Complex.I)

/-- Pair the finite comb cutoff with the actual pinned interpolated density. -/
def rotatorOneFaceCombCutoffPairing (β : ℝ) (N : ℕ) : ℂ :=
  ∫ x : ℝ, rotatorOneFaceCombCutoff N x * rotatorOneFacePinnedDensity β x

private theorem rotatorOneFaceIntegerDensity (β : ℝ) (n : ℤ) :
    rotatorOneFacePinnedDensity β n =
      rotatorInterpolatedHeightWeight 1 β (rotatorOneFaceIntegerHeight n) := by
  unfold rotatorOneFacePinnedDensity rotatorInterpolatedHeightWeight
  apply Finset.prod_congr rfl
  intro e he
  have hfield (p : RotatorDualFace 1) :
      rotatorOneFaceRealField (n : ℝ) p =
        ((rotatorOneFaceIntegerHeight n).1 p : ℝ) := by
    cases p with
    | none => simp [rotatorOneFaceRealField, rotatorOneFaceIntegerHeight]
    | some p => simp [rotatorOneFaceRealField, rotatorOneFaceIntegerHeight]
  congr 1
  rw [hfield, hfield]
  simp [rotatorFaceHeightCurrent, Int.cast_sub]

/-- In the one-face box, the pinned interpolated density sampled at integer heights is exactly the
height partition factor. -/
theorem rotatorOneFaceHeightFactor_eq_integerSamples (β : ℝ) (hβ : 0 < β) :
    rotatorHeightPartitionFactor 1 β = ∑' n : ℤ, rotatorOneFacePinnedDensity β n := by
  rw [rotatorHeightPartitionFactor_eq_interpolated (L := 1) β hβ]
  rw [show (∑' h : RotatorFaceHeight 1, rotatorInterpolatedHeightWeight 1 β h) =
      ∑' n : ℤ, rotatorInterpolatedHeightWeight 1 β (rotatorOneFaceIntegerHeight n) by
        symm
        exact Equiv.tsum_eq rotatorOneFaceHeightEquiv
          (fun h : RotatorFaceHeight 1 => rotatorInterpolatedHeightWeight 1 β h)]
  apply tsum_congr
  intro n
  exact (rotatorOneFaceIntegerDensity β n).symm

private theorem summable_fourier_of_schwartz (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => 𝓕 f n) := by
  let Ff : 𝓢(ℝ, ℂ) := (𝓕 f : 𝓢(ℝ, ℂ))
  have hdecay : Ff =O[cocompact ℝ] (|·| ^ (-2 : ℝ)) := by
    simpa only [Real.norm_eq_abs] using Ff.isBigO_cocompact_rpow (-2)
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num))
    (hdecay.comp_tendsto Int.tendsto_coe_cofinite)

private theorem rotatorCombCutoffPairing_eq_fourier_sum (f : 𝓢(ℝ, ℂ)) (N : ℕ) :
    (∫ x : ℝ, rotatorOneFaceCombCutoff N x * f x) =
      ∑ q ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), 𝓕 f q := by
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hterm (q : ℤ) : Integrable (fun x : ℝ =>
      Complex.exp (((-2 * Real.pi * x * (q : ℝ) : ℝ) : ℂ) * Complex.I) * f x) := by
    have hfI : Integrable (fun x : ℝ => f x) volume :=
      SchwartzMap.integrable (μ := volume) f
    have hcont : Continuous fun x : ℝ =>
        Complex.exp (((-2 * Real.pi * x * (q : ℝ) : ℝ) : ℂ) * Complex.I) * f x := by
      fun_prop
    refine hfI.norm.mono' hcont.aestronglyMeasurable ?_
    filter_upwards with x
    have hre : (((-2 * Real.pi * x * (q : ℝ) : ℝ) : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re]
    rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul]
  calc
    _ = ∫ x : ℝ, ∑ q ∈ s,
          Complex.exp (((-2 * Real.pi * x * (q : ℝ) : ℝ) : ℂ) * Complex.I) * f x := by
          congr 1
          funext x
          simp [rotatorOneFaceCombCutoff, s, Finset.sum_mul]
    _ = ∑ q ∈ s, ∫ x : ℝ,
          Complex.exp (((-2 * Real.pi * x * (q : ℝ) : ℝ) : ℂ) * Complex.I) * f x := by
          rw [integral_finsetSum (s := s) (f := fun (q : ℤ) (x : ℝ) =>
            Complex.exp (((-2 * Real.pi * x * (q : ℝ) : ℝ) : ℂ) * Complex.I) * f x)
            (by intro q hq; exact hterm q)]
    _ = ∑ q ∈ s, 𝓕 f q := by
          apply Finset.sum_congr rfl
          intro q hq
          calc
            _ = ∫ x : ℝ,
                Complex.exp (((-2 * Real.pi * x * (q : ℝ) : ℝ) : ℂ) * Complex.I) • f x := by
                  simp only [smul_eq_mul]
            _ = 𝓕 (f : ℝ → ℂ) (q : ℝ) :=
              (Real.fourier_real_eq_integral_exp_smul (f : ℝ → ℂ) (q : ℝ)).symm
            _ = 𝓕 f q := by rw [← SchwartzMap.fourier_coe]

private theorem tendsto_symmetricCutoff_sum (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), 𝓕 f n) atTop
      (𝓝 (∑' n : ℤ, 𝓕 f n)) := by
  let g : ℤ → ℂ := fun n => 𝓕 f n
  have hg : Summable g := by
    simpa [g] using summable_fourier_of_schwartz f
  have hs : Summable g (SummationFilter.symmetricIcc ℤ) :=
    hg.mono_filter (SummationFilter.le_atTop (L := SummationFilter.symmetricIcc ℤ))
  have hUncond : HasSum g (∑' n : ℤ, g n) := by exact hg.hasSum
  have hSymm : HasSum g (∑' n : ℤ, g n) (SummationFilter.symmetricIcc ℤ) :=
    hUncond.mono_left (SummationFilter.le_atTop (L := SummationFilter.symmetricIcc ℤ))
  have hvalue : ∑'[SummationFilter.symmetricIcc ℤ] n, g n = ∑' n : ℤ, g n :=
    hs.hasSum_iff.mp hSymm
  have hcut := (SummationFilter.hasSum_symmetricIcc_iff (f := g)
    (a := ∑'[SummationFilter.symmetricIcc ℤ] n, g n)).mp hs.hasSum
  simpa [g, hvalue] using hcut

/-- The one-face pinned comb identity in finite-frequency form. For every Schwartz representative
of the actual interpolated density, the symmetric finite frequency cutoffs converge to the
zero-exterior integer-height partition factor. Establishing the Schwartz representative for the
literal Appendix-B interpolation is the remaining analytic instance obligation. -/
theorem rotatorOneFacePinnedComb_cutoff_tendsto (β : ℝ) (hβ : 0 < β)
    (f : 𝓢(ℝ, ℂ))
    (hf : ∀ x : ℝ, f x = rotatorOneFacePinnedDensity β x) :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), 𝓕 f n) atTop
      (𝓝 (rotatorHeightPartitionFactor 1 β)) := by
  have hcut := tendsto_symmetricCutoff_sum f
  have hPoisson := SchwartzMap.tsum_eq_tsum_fourier f 0
  have hPoisson' : (∑' n : ℤ, f (n : ℝ)) = ∑' n : ℤ, 𝓕 f n := by
    simpa using hPoisson
  have hheight := rotatorOneFaceHeightFactor_eq_integerSamples β hβ
  rw [show rotatorHeightPartitionFactor 1 β = ∑' n : ℤ, f (n : ℝ) by
    rw [hheight]
    apply tsum_congr
    intro n
    exact (hf n).symm]
  rw [hPoisson']
  exact hcut

/-- The finite-frequency comb pairings against the actual pinned real density converge to the
integer-height partition factor. This is the finite-volume (6.5) representation for the one-face
box, conditional only on a Schwartz representative of the literal interpolated density. -/
theorem rotatorOneFaceCombCutoffPairing_tendsto (β : ℝ) (hβ : 0 < β)
    (f : 𝓢(ℝ, ℂ))
    (hf : ∀ x : ℝ, f x = rotatorOneFacePinnedDensity β x) :
    Tendsto (fun N : ℕ => rotatorOneFaceCombCutoffPairing β N) atTop
      (𝓝 (rotatorHeightPartitionFactor 1 β)) := by
  have hlimit := rotatorOneFacePinnedComb_cutoff_tendsto β hβ f hf
  have hpair (N : ℕ) : rotatorOneFaceCombCutoffPairing β N =
      ∑ q ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), 𝓕 f q := by
    unfold rotatorOneFaceCombCutoffPairing
    calc
      _ = ∫ x : ℝ, rotatorOneFaceCombCutoff N x * f x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hf x]
      _ = ∑ q ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), 𝓕 f q :=
        rotatorCombCutoffPairing_eq_fourier_sum f N
  exact hlimit.congr' (Filter.Eventually.of_forall fun N => (hpair N).symm)

end FroehlichSpencer.BKT.Rotator
end
