/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.Comb
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Root-mode orthogonality for the periodic all-site comb

This module records the exact finite-frequency bookkeeping for eliminating the common root mode.
Neutrality forces the eliminated root frequency to be the negative total of the rootless
frequencies, so its cutoff remains as the total-charge condition in
`periodicNeutralFrequencyBox`. The integral of one root Fourier mode over a full angle period is
zero except at frequency zero, where its mass is `2π`.
-/

@[expose] public section

open Complex MeasureTheory
open intervalIntegral
open FroehlichSpencer.BKT.Rotator

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction of an all-site frequency to the rootless coordinates. -/
def optionFaceFrequencyRestrict (q : FaceFrequency (Option ι)) : FaceFrequency ι :=
  fun i _ => q (some i) (Finset.mem_univ _)

/-- The total frequency on the option-indexed carrier, split into its root and rootless parts. -/
def optionFaceFrequencyTotal (q : FaceFrequency (Option ι)) : ℤ :=
  q none (Finset.mem_univ _) + periodicFrequencyTotal (optionFaceFrequencyRestrict q)

/-- Lift a rootless frequency by assigning its negative total frequency at the root. -/
def optionFaceFrequencyLift (q : FaceFrequency ι) : FaceFrequency (Option ι) := fun o _ =>
  match o with
  | none => -periodicFrequencyTotal q
  | some i => q i (Finset.mem_univ i)

/-- The all-site cutoff restricted to neutral modes. -/
def optionRootNeutralFrequencyBox (N : ℕ) : Finset (FaceFrequency (Option ι)) :=
  (faceFrequencyBox N).filter fun q => optionFaceFrequencyTotal q = 0

/-- Put a root-pinned coordinate field on the option carrier, with value zero at the root. -/
def optionRootField (x : ι → ℝ) : Option ι → ℝ := fun o => o.elim 0 x

private theorem mem_faceFrequencyBox_iff (N : ℕ) (q : FaceFrequency ι) :
    q ∈ faceFrequencyBox N ↔
      ∀ i, q i (Finset.mem_univ i) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  simp [faceFrequencyBox, Finset.mem_pi]

omit [DecidableEq ι] in
theorem optionFaceFrequencyTotal_eq (q : FaceFrequency (Option ι)) :
    optionFaceFrequencyTotal q =
      q none (Finset.mem_univ _) +
        ∑ i : ι, q (some i) (Finset.mem_univ (some i)) := rfl

omit [DecidableEq ι] in
theorem optionFaceFrequencyLift_total (q : FaceFrequency ι) :
    optionFaceFrequencyTotal (optionFaceFrequencyLift q) = 0 := by
  change -(periodicFrequencyTotal q) + periodicFrequencyTotal q = 0
  exact neg_add_cancel _

omit [DecidableEq ι] in
theorem optionFaceFrequencyRestrict_lift (q : FaceFrequency ι) :
    optionFaceFrequencyRestrict (optionFaceFrequencyLift q) = q := by
  funext i hi
  rfl

omit [DecidableEq ι] in
private theorem optionFaceFrequency_eq_lift_of_neutral
    (q : FaceFrequency (Option ι)) (hq : optionFaceFrequencyTotal q = 0) :
    optionFaceFrequencyLift (optionFaceFrequencyRestrict q) = q := by
  funext o _
  cases o with
  | none =>
      have hs := optionFaceFrequencyTotal_eq q
      have hneutral : q none (Finset.mem_univ _) +
          periodicFrequencyTotal (optionFaceFrequencyRestrict q) = 0 := by
        change q none (Finset.mem_univ _) +
          periodicFrequencyTotal (optionFaceFrequencyRestrict q) = 0 at hq
        exact hq
      change -periodicFrequencyTotal (optionFaceFrequencyRestrict q) = q none _
      omega
  | some i => rfl

/-- A neutral all-site cutoff frequency gives a rootless frequency obeying both the coordinate
cutoff and the retained cutoff on the eliminated root frequency. -/
theorem optionRootNeutral_mem_restrict {N : ℕ} {q : FaceFrequency (Option ι)}
    (hq : q ∈ optionRootNeutralFrequencyBox N) :
    optionFaceFrequencyRestrict q ∈ periodicNeutralFrequencyBox N := by
  rw [optionRootNeutralFrequencyBox, Finset.mem_filter] at hq
  rw [periodicNeutralFrequencyBox, Finset.mem_filter]
  constructor
  · rw [mem_faceFrequencyBox_iff]
    intro i
    have h := (mem_faceFrequencyBox_iff N q).mp hq.1 (some i)
    simpa [optionFaceFrequencyRestrict] using h
  · have hroot : q none (Finset.mem_univ _) ∈ Finset.Icc (-(N : ℤ)) N :=
      (mem_faceFrequencyBox_iff N q).mp hq.1 none
    have hneutral := hq.2
    change q none (Finset.mem_univ _) +
      periodicFrequencyTotal (optionFaceFrequencyRestrict q) = 0 at hneutral
    have hsum : periodicFrequencyTotal (optionFaceFrequencyRestrict q) =
        -q none (Finset.mem_univ _) := by omega
    rw [Finset.mem_Icc] at hroot ⊢
    rw [hsum]
    omega

/-- Every rootless neutral cutoff frequency lifts to a neutral all-site cutoff frequency. -/
theorem optionRootNeutral_mem_lift {N : ℕ} {q : FaceFrequency ι}
    (hq : q ∈ periodicNeutralFrequencyBox N) :
    optionFaceFrequencyLift q ∈ optionRootNeutralFrequencyBox N := by
  rw [periodicNeutralFrequencyBox, Finset.mem_filter] at hq
  rw [optionRootNeutralFrequencyBox, Finset.mem_filter]
  constructor
  · rw [mem_faceFrequencyBox_iff]
    intro o
    cases o with
    | none =>
        have htotal := Finset.mem_Icc.mp hq.2
        have hneg : -(periodicFrequencyTotal q) ∈ Finset.Icc (-(N : ℤ)) N := by
          rw [Finset.mem_Icc]
          change -(N : ℤ) ≤ -(periodicFrequencyTotal q) ∧
            -(periodicFrequencyTotal q) ≤ N
          omega
        simpa [optionFaceFrequencyLift] using hneg
    | some i =>
        have h := (mem_faceFrequencyBox_iff N q).mp hq.1 i
        simpa [optionFaceFrequencyLift] using h
  · exact optionFaceFrequencyLift_total q

/-- The neutral all-site frequency box and the rootless cutoff are in bijection by deleting the
root frequency (or restoring it as minus the total charge). -/
def optionRootNeutralFrequencyEquiv (N : ℕ) :
    {q : FaceFrequency (Option ι) // q ∈ optionRootNeutralFrequencyBox N} ≃
      {q : FaceFrequency ι // q ∈ periodicNeutralFrequencyBox N} where
  toFun q := ⟨optionFaceFrequencyRestrict q.1, optionRootNeutral_mem_restrict q.2⟩
  invFun q := ⟨optionFaceFrequencyLift q.1, optionRootNeutral_mem_lift q.2⟩
  left_inv q := by
    apply Subtype.ext
    exact optionFaceFrequency_eq_lift_of_neutral q.1 (Finset.mem_filter.mp q.2).2
  right_inv q := by
    apply Subtype.ext
    exact optionFaceFrequencyRestrict_lift q.1

omit [DecidableEq ι] in
theorem faceCombMode_optionRootPhase (q : FaceFrequency (Option ι))
    (x : ι → ℝ) (t : ℝ) :
    faceCombMode q (fun o => optionRootField x o + t / (2 * Real.pi)) =
      faceCombMode (optionFaceFrequencyRestrict q) x *
        Complex.exp (((-(optionFaceFrequencyTotal q : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  have hsome :
      (∑ i : ι, (x i + t / (2 * Real.pi)) *
          (q (some i) (Finset.mem_univ (some i)) : ℝ)) =
        (∑ i : ι, x i * (q (some i) (Finset.mem_univ (some i)) : ℝ)) +
          t / (2 * Real.pi) *
            ∑ i : ι, (q (some i) (Finset.mem_univ (some i)) : ℝ) := by
    calc
      _ = ∑ i : ι,
          (x i * (q (some i) (Finset.mem_univ (some i)) : ℝ) +
            t / (2 * Real.pi) * (q (some i) (Finset.mem_univ (some i)) : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have htotal : (optionFaceFrequencyTotal q : ℝ) =
      (q none (Finset.mem_univ _) : ℝ) +
        ∑ i : ι, (q (some i) (Finset.mem_univ (some i)) : ℝ) := by
    rw [optionFaceFrequencyTotal_eq]
    push_cast
    rfl
  have hsum :
      (∑ o : Option ι,
          (optionRootField x o + t / (2 * Real.pi)) *
            (q o (Finset.mem_univ o) : ℝ)) =
        (∑ i : ι, x i * (q (some i) (Finset.mem_univ (some i)) : ℝ)) +
          t / (2 * Real.pi) * (optionFaceFrequencyTotal q : ℝ) := by
    rw [Fintype.sum_option]
    simp only [optionRootField, Option.elim, zero_add]
    rw [hsome, htotal]
    ring
  unfold faceCombMode
  rw [hsum, ← Complex.exp_add]
  congr 1
  rw [optionFaceFrequencyTotal_eq]
  simp only [optionFaceFrequencyRestrict]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf

/-- A root Fourier mode integrates to zero unless it is neutral, when its integral is `2π`. -/
theorem integral_rootFourierMode (n : ℤ) :
    (∫ t in -Real.pi..Real.pi,
      Complex.exp ((((n : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
      if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst n
    calc
      _ = ∫ t in -Real.pi..Real.pi, (1 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp
      _ = (2 * Real.pi : ℂ) := by
        rw [intervalIntegral.integral_const]
        rw [Complex.real_smul, mul_one, Complex.ofReal_sub, Complex.ofReal_neg]
        ring_nf
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hparam (t : ℝ) :
        Complex.exp ((((n : ℝ) * t : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((t : ℂ) * ((n : ℝ) : ℂ) * Complex.I) := by
      congr 2
      push_cast
      ring_nf
    have hzero :
        (∫ t in -Real.pi..Real.pi,
          Complex.exp ((((n : ℝ) * t : ℝ) : ℂ) * Complex.I)) = 0 := by
      calc
        _ = ∫ t in -Real.pi..Real.pi,
            Complex.exp ((t : ℂ) * ((n : ℝ) : ℂ) * Complex.I) := by
              apply intervalIntegral.integral_congr
              intro t ht
              exact hparam t
        _ = (n : ℝ)⁻¹ • ∫ u in -Real.pi * n..Real.pi * n,
            Complex.exp ((u : ℂ) * Complex.I) := by
              have hc := intervalIntegral.integral_comp_mul_right
                (f := fun u : ℝ => Complex.exp ((u : ℂ) * Complex.I)) hnR
                (a := -Real.pi) (b := Real.pi)
              simpa [mul_assoc] using hc
        _ = 0 := by
          have hi : (∫ u in -Real.pi * n..Real.pi * n,
              Complex.exp ((u : ℂ) * Complex.I)) =
                2 * (Real.sin (Real.pi * n) : ℂ) := by
            simpa [neg_mul] using integral_exp_mul_I_eq_sin (Real.pi * n)
          have hs : Real.sin (Real.pi * n) = 0 := by
            simpa [mul_comm] using Real.sin_int_mul_pi n
          rw [hi, hs]
          simp
    simpa [hn] using hzero

/-- Integrating the all-site finite comb over the common root phase deletes precisely the root
frequency. The remaining finite frequency set is exactly the rootless cutoff, with its extra
total-charge bound, and the phase integration contributes the factor `2π`. -/
theorem integral_faceCombCutoff_optionRootPhase (N : ℕ) (x : ι → ℝ) :
    (∫ t in -Real.pi..Real.pi,
      faceCombCutoff (ι := Option ι) N
        (fun o => optionRootField x o + t / (2 * Real.pi))) =
      (2 * Real.pi : ℂ) * periodicNeutralCombCutoff N x := by
  classical
  unfold faceCombCutoff
  rw [intervalIntegral.integral_finsetSum]
  · have hmode (q : FaceFrequency (Option ι)) :
        (∫ t in -Real.pi..Real.pi,
          faceCombMode q (fun o => optionRootField x o + t / (2 * Real.pi))) =
          (if optionFaceFrequencyTotal q = 0 then (2 * Real.pi : ℂ) else 0) *
            faceCombMode (optionFaceFrequencyRestrict q) x := by
      calc
        _ = ∫ t in -Real.pi..Real.pi,
            faceCombMode (optionFaceFrequencyRestrict q) x *
              Complex.exp (((-(optionFaceFrequencyTotal q : ℝ) * t : ℝ) : ℂ) * I) := by
                apply intervalIntegral.integral_congr
                intro t ht
                exact faceCombMode_optionRootPhase q x t
        _ = faceCombMode (optionFaceFrequencyRestrict q) x *
            ∫ t in -Real.pi..Real.pi,
              Complex.exp (((-(optionFaceFrequencyTotal q : ℝ) * t : ℝ) : ℂ) * I) := by
                rw [intervalIntegral.integral_const_mul]
        _ = _ := by
                have hi : (∫ t in -Real.pi..Real.pi,
                    Complex.exp (((-(optionFaceFrequencyTotal q : ℝ) * t : ℝ) : ℂ) * I)) =
                    if optionFaceFrequencyTotal q = 0 then (2 * Real.pi : ℂ) else 0 := by
                  simpa using integral_rootFourierMode (-optionFaceFrequencyTotal q)
                rw [hi]
                by_cases hq : optionFaceFrequencyTotal q = 0 <;> simp [hq, mul_comm]
    calc
      _ = ∑ q ∈ faceFrequencyBox (ι := Option ι) N,
          (if optionFaceFrequencyTotal q = 0 then (2 * Real.pi : ℂ) else 0) *
            faceCombMode (optionFaceFrequencyRestrict q) x := by
              exact Finset.sum_congr rfl fun q hq => hmode q
      _ = ∑ q ∈ optionRootNeutralFrequencyBox N,
          (2 * Real.pi : ℂ) * faceCombMode (optionFaceFrequencyRestrict q) x := by
              calc
                _ = ∑ q ∈ faceFrequencyBox (ι := Option ι) N,
                    if optionFaceFrequencyTotal q = 0 then
                      (2 * Real.pi : ℂ) * faceCombMode (optionFaceFrequencyRestrict q) x
                    else 0 := by
                      apply Finset.sum_congr rfl
                      intro q hq
                      by_cases hz : optionFaceFrequencyTotal q = 0 <;> simp [hz, mul_comm]
                _ = _ := by
                      simpa [optionRootNeutralFrequencyBox] using
                        (Finset.sum_filter
                          (s := faceFrequencyBox (ι := Option ι) N)
                          (p := fun q => optionFaceFrequencyTotal q = 0)
                          (f := fun q =>
                            (2 * Real.pi : ℂ) *
                              faceCombMode (optionFaceFrequencyRestrict q) x)).symm
      _ = ∑ q ∈ periodicNeutralFrequencyBox N,
          (2 * Real.pi : ℂ) * faceCombMode q x := by
              apply Finset.sum_bij (fun q hq => optionFaceFrequencyRestrict q)
              · intro q hq
                exact optionRootNeutral_mem_restrict hq
              · intro q₁ h₁ q₂ h₂ heq
                have hq₁ := optionFaceFrequency_eq_lift_of_neutral q₁
                  (Finset.mem_filter.mp h₁).2
                have hq₂ := optionFaceFrequency_eq_lift_of_neutral q₂
                  (Finset.mem_filter.mp h₂).2
                calc
                  q₁ = optionFaceFrequencyLift (optionFaceFrequencyRestrict q₁) := hq₁.symm
                  _ = optionFaceFrequencyLift (optionFaceFrequencyRestrict q₂) := by rw [heq]
                  _ = q₂ := hq₂
              · intro q hq
                refine ⟨optionFaceFrequencyLift q, optionRootNeutral_mem_lift hq, ?_⟩
                exact optionFaceFrequencyRestrict_lift q
              · intro q hq
                rfl
      _ = (2 * Real.pi : ℂ) * periodicNeutralCombCutoff N x := by
              rw [← Finset.mul_sum, periodicNeutralCombCutoff]
  · intro q hq
    exact (by fun_prop [faceCombMode] : Continuous fun t : ℝ =>
      faceCombMode q (fun o => optionRootField x o + t / (2 * Real.pi))).intervalIntegrable
      (-Real.pi) Real.pi

/-- A shift pinned at the root acts only by translating the rootless coordinates in the eliminated
comb. This is the marked version of the same finite adapter. -/
theorem integral_faceCombCutoff_optionRootPhase_shift (N : ℕ) (x s : ι → ℝ) :
    (∫ t in -Real.pi..Real.pi,
      faceCombCutoff (ι := Option ι) N
        (fun o => optionRootField (x + s) o + t / (2 * Real.pi))) =
      (2 * Real.pi : ℂ) * periodicNeutralCombCutoff N (x + s) :=
  integral_faceCombCutoff_optionRootPhase N (x + s)

/-- Pairing the root-phase integral with any rootless weight gives exactly the rootless neutral
comb pairing, including the `2π` root-volume factor. -/
theorem integral_rootPhase_pairedCombCutoff (N : ℕ) (g : (ι → ℝ) → ℂ) :
    (∫ x : ι → ℝ,
      (∫ t in -Real.pi..Real.pi,
        faceCombCutoff (ι := Option ι) N
          (fun o => optionRootField x o + t / (2 * Real.pi))) * g x) =
      (2 * Real.pi : ℂ) *
        ∫ x : ι → ℝ, periodicNeutralCombCutoff N x * g x := by
  calc
    _ = ∫ x : ι → ℝ,
        ((2 * Real.pi : ℂ) * periodicNeutralCombCutoff N x) * g x := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          rw [integral_faceCombCutoff_optionRootPhase]
    _ = ∫ x : ι → ℝ,
        (2 * Real.pi : ℂ) * (periodicNeutralCombCutoff N x * g x) := by
          congr 1
          funext x
          ring
    _ = (2 * Real.pi : ℂ) *
        ∫ x : ι → ℝ, periodicNeutralCombCutoff N x * g x :=
          MeasureTheory.integral_const_mul _ _

/-- The shifted root-phase pairing is the marked rootless comb pairing. -/
theorem integral_rootPhase_pairedCombCutoff_shift (N : ℕ) (s : ι → ℝ)
    (g : (ι → ℝ) → ℂ) :
    (∫ x : ι → ℝ,
      (∫ t in -Real.pi..Real.pi,
        faceCombCutoff (ι := Option ι) N
          (fun o => optionRootField (x + s) o + t / (2 * Real.pi))) * g x) =
      (2 * Real.pi : ℂ) *
        ∫ x : ι → ℝ, periodicNeutralCombCutoff N (x + s) * g x := by
  calc
    _ = ∫ x : ι → ℝ,
        ((2 * Real.pi : ℂ) * periodicNeutralCombCutoff N (x + s)) * g x := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          rw [integral_faceCombCutoff_optionRootPhase_shift]
    _ = ∫ x : ι → ℝ,
        (2 * Real.pi : ℂ) * (periodicNeutralCombCutoff N (x + s) * g x) := by
          congr 1
          funext x
          ring
    _ = (2 * Real.pi : ℂ) *
        ∫ x : ι → ℝ, periodicNeutralCombCutoff N (x + s) * g x :=
          MeasureTheory.integral_const_mul _ _

end FroehlichSpencer.BKT.Rotator.Periodic

end
