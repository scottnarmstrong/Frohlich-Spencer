/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.FiniteLaw
public import FroehlichSpencer.BKT.Ginibre.SiteMeasure
import Mathlib.Tactic

/-!
# Fourier coefficients of the sampled Villain interaction

The discrete Fourier transform of the periodized Gaussian sampled at the N clock angles is a
Gaussian alias sum over frequencies congruent modulo N.

A fractional seam twist multiplies the
individual aliases by their own phases; it is a single character of the finite dual group only
when `N * ξ` is integral.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Ginibre
open MeasureTheory
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The discrete Fourier coefficient of a Villain edge sampled on the N clock angles. -/
def sampledFourierCoefficient (β : ℝ) (N : ℕ) (q : ℤ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k : Fin N,
    (villainWeight β (clockAngle N k) : ℂ) *
      Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))

/-- One Gaussian Fourier mode of the Villain weight. -/
def gaussianMode (β : ℝ) (p : ℤ) : ℂ :=
  ((Real.exp (-((p : ℝ) ^ 2) / (2 * β)) : ℝ) : ℂ)

/-- The Gaussian alias sum at residue `q` for the sampled Villain edge. -/
def gaussianAliasCoefficient (β : ℝ) (N : ℕ) (q : ℤ) : ℂ :=
  (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ∑' ell : ℤ, gaussianMode β (q + (N : ℤ) * ell)

/-- The phase contributed by a fractional seam twist in Fourier mode `p`. -/
def twistPhase (ξ : ℝ) (p : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (p : ℂ))

/-- The Fourier alias coefficient after inserting the seam twist in each integer mode. -/
def gaussianTwistedAliasCoefficient (β ξ : ℝ) (N : ℕ) (q : ℤ) : ℂ :=
  (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ∑' ell : ℤ, gaussianMode β (q + (N : ℤ) * ell) *
      twistPhase ξ (q + (N : ℤ) * ell)

/-- Frequencies congruent to `q` modulo `N` are parameterized by `q + N * ell`. -/
noncomputable def aliasModeEquiv (N : ℕ) (q : ℤ) (hN : 0 < N) :
    ℤ ≃ {p : ℤ // p ∈ {x : ℤ | (N : ℤ) ∣ x - q}} where
  toFun ell := ⟨q + (N : ℤ) * ell, by
    simp only [Set.mem_ofPred_eq]
    exact ⟨ell, by ring⟩⟩
  invFun p := Classical.choose (show (N : ℤ) ∣ p.1 - q from by
    simpa only [Set.mem_ofPred_eq] using p.2)
  left_inv ell := by
    have hNInt : (N : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    let h : ∃ k : ℤ, q + (N : ℤ) * ell - q = (N : ℤ) * k := ⟨ell, by ring⟩
    apply mul_left_cancel₀ hNInt
    change (N : ℤ) * Classical.choose
      (show (N : ℤ) ∣ q + (N : ℤ) * ell - q from ⟨ell, by ring⟩) = (N : ℤ) * ell
    have hc := Classical.choose_spec h
    calc
      (N : ℤ) * Classical.choose h = q + (N : ℤ) * ell - q := hc.symm
      _ = (N : ℤ) * ell := by ring
  right_inv p := by
    apply Subtype.ext
    have hdiv : (N : ℤ) ∣ p.1 - q := by
      simpa only [Set.mem_ofPred_eq] using p.2
    change q + (N : ℤ) * Classical.choose hdiv = p.1
    have hc := Classical.choose_spec hdiv
    linarith [hc]

/-- The normalized sum of a clock character vanishes unless its frequency is divisible by N. -/
theorem clockCharacterAverage (N : ℕ) (hN : 0 < N) (m : ℤ) :
    (N : ℂ)⁻¹ * ∑ k : Fin N,
      Complex.exp (Complex.I * (m : ℂ) * (clockAngle N k : ℂ)) =
        if (N : ℤ) ∣ m then 1 else 0 := by
  have hsum : ∑ k : Fin N,
      Complex.exp (Complex.I * (m : ℂ) * (clockAngle N k : ℂ)) =
        (clockFourier N m : ℂ) := by
    have hf := hasRealFourier_clock hN m
    rw [clockMeasure, integral_finsetSum_measure (fun k _ => integrable_dirac enorm_lt_top)] at hf
    simpa [clockAngle] using hf
  rw [hsum, clockFourier]
  by_cases h : (N : ℤ) ∣ m
  · simp [h]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  · simp [h]

/-- The DFT of sampled Villain weights is the Gaussian sum over its congruence class. -/
theorem sampledFourierCoefficient_eq_gaussianAlias
    (β : ℝ) {N : ℕ} (hN : 0 < N) (hβ : 0 < β) (q : ℤ) :
    sampledFourierCoefficient β N q = gaussianAliasCoefficient β N q := by
  let C : ℂ := (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  have hfourier (k : Fin N) :
      (villainWeight β (clockAngle N k) : ℂ) =
        C * ∑' p : ℤ, gaussianMode β p *
          Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) := by
    simpa [C, gaussianMode] using
      VillainWeight.villainWeight_fourier_complex_normalized hβ (clockAngle N k)
  have hseries (k : Fin N) :
      Summable (fun p : ℤ => gaussianMode β p *
        Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
        Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by
    have hs := VillainWeight.villainWeight_fourier_series_summable hβ (clockAngle N k)
    exact hs.mul_right (Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)))
  have hF : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      Summable (fun p : ℤ => gaussianMode β p *
        Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
        Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by
    intro k hk
    exact hseries k
  have hswap := Summable.tsum_finsetSum (f := fun k p =>
      gaussianMode β p *
        Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
        Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)))
    (s := (Finset.univ : Finset (Fin N))) hF
  have hphase (p : ℤ) (k : Fin N) :
      Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
        Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
      Complex.exp (Complex.I * ((p - q) : ℂ) * (clockAngle N k : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    sampledFourierCoefficient β N q =
        C * ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑' p : ℤ,
          gaussianMode β p *
            Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
            Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by
      unfold sampledFourierCoefficient
      have hterm (k : Fin N) :
          (villainWeight β (clockAngle N k) : ℂ) *
              Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
            C * ∑' p : ℤ,
              gaussianMode β p *
                Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
                Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) := by
        rw [hfourier k]
        calc
          (C * ∑' p : ℤ, gaussianMode β p *
              Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ))) *
              Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
            C * ((∑' p : ℤ, gaussianMode β p *
                Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ))) *
              Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by ring
          _ = C * ∑' p : ℤ, gaussianMode β p *
                Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
                Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) := by
            rw [← tsum_mul_right]
      calc
        (N : ℂ)⁻¹ * ∑ k : Fin N,
            (villainWeight β (clockAngle N k) : ℂ) *
              Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
          (N : ℂ)⁻¹ * ∑ k : Fin N, C * ∑' p : ℤ,
            gaussianMode β p *
              Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
              Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) := by
                congr 1
                exact Finset.sum_congr rfl (fun k _ => hterm k)
        _ = C * ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑' p : ℤ,
            gaussianMode β p *
              Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
              Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by
                calc
                  _ = ∑ k : Fin N, (N : ℂ)⁻¹ *
                      (C * ∑' p : ℤ, gaussianMode β p *
                        Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
                        Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by
                    rw [Finset.mul_sum]
                  _ = ∑ k : Fin N, C * ((N : ℂ)⁻¹ *
                      ∑' p : ℤ, gaussianMode β p *
                        Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
                        Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    ring
                  _ = C * ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑' p : ℤ,
                      gaussianMode β p *
                        Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
                        Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by
                    rw [Finset.mul_sum, Finset.mul_sum]
    _ = C * ((N : ℂ)⁻¹ * ∑' p : ℤ, ∑ k : Fin N,
          gaussianMode β p *
            Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
            Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by
      rw [← hswap]
    _ = C * ((N : ℂ)⁻¹ * ∑' p : ℤ,
          gaussianMode β p * ∑ k : Fin N,
            Complex.exp (Complex.I * ((p - q) : ℂ) * (clockAngle N k : ℂ))) := by
      congr 2
      apply tsum_congr
      intro p
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        gaussianMode β p *
            Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
            Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
          gaussianMode β p *
            (Complex.exp (Complex.I * (p : ℂ) * (clockAngle N k : ℂ)) *
              Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N k : ℂ))) := by ring
        _ = gaussianMode β p *
            Complex.exp (Complex.I * ((p - q) : ℂ) * (clockAngle N k : ℂ)) := by
          rw [hphase]
    _ = C * ∑' p : ℤ, gaussianMode β p * ((N : ℂ)⁻¹ *
            ∑ k : Fin N, Complex.exp (Complex.I * ((p - q) : ℂ) *
              (clockAngle N k : ℂ))) := by
      calc
        C * ((N : ℂ)⁻¹ * ∑' p : ℤ, gaussianMode β p *
            ∑ k : Fin N, Complex.exp (Complex.I * ((p - q) : ℂ) *
              (clockAngle N k : ℂ))) =
          C * ∑' p : ℤ, (N : ℂ)⁻¹ * (gaussianMode β p *
            ∑ k : Fin N, Complex.exp (Complex.I * ((p - q) : ℂ) *
              (clockAngle N k : ℂ))) := by
                rw [← tsum_mul_left]
        _ = C * ∑' p : ℤ, gaussianMode β p * ((N : ℂ)⁻¹ *
            ∑ k : Fin N, Complex.exp (Complex.I * ((p - q) : ℂ) *
              (clockAngle N k : ℂ))) := by
                congr 1
                apply tsum_congr
                intro p
                ring
    _ = C * ∑' p : ℤ,
          gaussianMode β p * (if (N : ℤ) ∣ p - q then 1 else 0) := by
      apply congrArg (fun z : ℂ => C * z)
      apply tsum_congr
      intro p
      have hc := clockCharacterAverage N hN (p - q)
      simpa only [Int.cast_sub] using congrArg (fun z : ℂ => gaussianMode β p * z) hc
    _ = C * ∑' p : {p : ℤ // p ∈ {x : ℤ | (N : ℤ) ∣ x - q}}, gaussianMode β p.1 := by
      have hfilter :
          (∑' p : ℤ, gaussianMode β p * (if (N : ℤ) ∣ p - q then 1 else 0)) =
            ∑' p : {p : ℤ // p ∈ {x : ℤ | (N : ℤ) ∣ x - q}}, gaussianMode β p.1 := by
        calc
          (∑' p : ℤ, gaussianMode β p * (if (N : ℤ) ∣ p - q then 1 else 0)) =
              ∑' p : ℤ, if (N : ℤ) ∣ p - q then gaussianMode β p else 0 := by
            apply tsum_congr
            intro p
            by_cases hp : (N : ℤ) ∣ p - q <;> simp [hp]
          _ = ∑' p : {p : ℤ // p ∈ {x : ℤ | (N : ℤ) ∣ x - q}}, gaussianMode β p.1 := by
            symm
            rw [tsum_subtype {p : ℤ | (N : ℤ) ∣ p - q} (gaussianMode β)]
            apply tsum_congr
            intro p
            simp [Set.indicator]
      apply congrArg (fun z : ℂ => C * z)
      exact hfilter
    _ = gaussianAliasCoefficient β N q := by
      rw [← (aliasModeEquiv N q hN).tsum_eq]
      simp only [aliasModeEquiv, gaussianMode]
      rfl

/-- At a grid twist, the phase is constant over all integer aliases of a residue class. -/
theorem grid_alias_phase_eq {N : ℕ} (ξ : ℝ)
    (hgrid : ∃ n : ℤ, (N : ℝ) * ξ = n) (q ell : ℤ) :
    twistPhase ξ (q + (N : ℤ) * ell) = twistPhase ξ q := by
  obtain ⟨n, hn⟩ := hgrid
  unfold twistPhase
  have harg :
      2 * Real.pi * Complex.I * (ξ : ℂ) * ((q + (N : ℤ) * ell : ℤ) : ℂ) =
        2 * Real.pi * Complex.I * (ξ : ℂ) * (q : ℂ) +
          (n * ell : ℂ) * (2 * Real.pi * Complex.I) := by
    have hnC : (N : ℂ) * (ξ : ℂ) = (n : ℂ) := by exact_mod_cast hn
    push_cast
    rw [← hnC]
    ring
  rw [harg, Complex.exp_add]
  have hperiodArg : (n : ℂ) * (ell : ℂ) * (2 * Real.pi * Complex.I) =
      ((n * ell : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hperiodArg, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- If `N ξ` is integral, the fractional seam phase factors out of the Gaussian alias sum. -/
theorem gaussianTwistedAliasCoefficient_eq_of_grid
    (β ξ : ℝ) (N : ℕ) (q : ℤ)
    (hgrid : ∃ n : ℤ, (N : ℝ) * ξ = n) :
    gaussianTwistedAliasCoefficient β ξ N q =
      twistPhase ξ q * gaussianAliasCoefficient β N q := by
  unfold gaussianTwistedAliasCoefficient
  let C : ℂ := (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  have hsumPointwise :
      (∑' ell : ℤ, gaussianMode β (q + (N : ℤ) * ell) *
        twistPhase ξ (q + (N : ℤ) * ell)) =
      ∑' ell : ℤ, gaussianMode β (q + (N : ℤ) * ell) * twistPhase ξ q := by
    apply tsum_congr
    intro ell
    rw [grid_alias_phase_eq ξ hgrid q ell]
  calc
    C * ∑' ell : ℤ, gaussianMode β (q + (N : ℤ) * ell) *
        twistPhase ξ (q + (N : ℤ) * ell) =
      C * ∑' ell : ℤ, gaussianMode β (q + (N : ℤ) * ell) * twistPhase ξ q := by
        exact congrArg (fun z : ℂ => C * z) hsumPointwise
    _ = twistPhase ξ q * gaussianAliasCoefficient β N q := by
        rw [tsum_mul_right]
        unfold gaussianAliasCoefficient
        ring

/-- Minimal non-grid example: aliases `0` and `0 + 2` have different phases at `ξ = 1/3`. -/
theorem fractional_alias_phase_obstruction :
    twistPhase (1 / 3) (0 : ℤ) ≠ twistPhase (1 / 3) (2 : ℤ) := by
  intro h
  have hraw : Complex.exp (2 * Real.pi * Complex.I * (3 : ℂ)⁻¹ * 2) = 1 := by
    have h0 : twistPhase (1 / 3) (0 : ℤ) = 1 := by simp [twistPhase]
    simpa [twistPhase] using h.symm.trans h0
  have harg : 2 * Real.pi * Complex.I * (3 : ℂ)⁻¹ * 2 =
      ((4 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    field_simp
    push_cast
    ring
  have hEq : Complex.exp (((4 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← harg]
    exact hraw
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp hEq
  have him := congrArg Complex.im hn
  have hnpi : 4 * Real.pi / 3 = (n : ℝ) * (2 * Real.pi) := by
    simpa using him
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hnpi
  have hn' : (3 * (n : ℝ) : ℝ) = 2 := by linarith
  have hnInt : 3 * n = 2 := by exact_mod_cast hn'
  omega
end FroehlichSpencer.BKT.Clock.VillainClock
end
