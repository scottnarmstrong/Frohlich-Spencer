/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.FourierAlias
import Mathlib.Tactic

/-!
# Finite residue Fourier expansion of the Villain clock edge

On the finite clock support, the sampled Villain edge has an exact finite Fourier expansion over
the residue group.

Its coefficient at each residue is the Gaussian alias sum over all integer
frequencies in that residue class.

This is the local adapter needed before a graph current or
marked expansion can be applied; the aliases remain grouped in the coefficient.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Ginibre

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- Finite Fourier inversion for the sampled Villain edge on the `N`-clock support. -/
theorem sampledVillain_eq_dft (β : ℝ) {N : ℕ} (hN : 0 < N) (k : Fin N) :
    (villainWeight β (clockAngle N k) : ℂ) =
      ∑ q : Fin N, sampledFourierCoefficient β N q *
        Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) := by
  classical
  let f : Fin N → ℂ := fun j => villainWeight β (clockAngle N j)
  have hchar (j : Fin N) :
      (N : ℂ)⁻¹ * ∑ q : Fin N,
        Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) * (clockAngle N q : ℂ)) =
        if j = k then 1 else 0 := by
    have h := clockCharacterAverage N hN ((k : ℤ) - j)
    have hphase (q : Fin N) :
        Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) * (clockAngle N q : ℂ)) =
          Complex.exp (Complex.I * (q : ℂ) *
            ((clockAngle N k - clockAngle N j : ℝ) : ℂ)) := by
      congr 1
      unfold clockAngle
      push_cast
      field_simp
    have hNdiv : ((N : ℤ) ∣ (k : ℤ) - j) ↔ j = k := by
      constructor
      · intro hd
        have hlt : |(k : ℤ) - j| < N := by
          rw [abs_lt]
          constructor <;> omega
        have hz : (k : ℤ) - j = 0 := Int.eq_zero_of_abs_lt_dvd hd hlt
        omega
      · intro hj
        subst j
        simp
    have hsum : (N : ℂ)⁻¹ * ∑ q : Fin N,
        Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) * (clockAngle N q : ℂ)) =
        (N : ℂ)⁻¹ * ∑ q : Fin N, Complex.exp (Complex.I * (q : ℂ) *
          ((clockAngle N k - clockAngle N j : ℝ) : ℂ)) := by
      congr 1
      exact Finset.sum_congr rfl (fun q _ => hphase q)
    calc
      (N : ℂ)⁻¹ * ∑ q : Fin N, Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) *
          (clockAngle N q : ℂ)) =
        (N : ℂ)⁻¹ * ∑ q : Fin N, Complex.exp (Complex.I * (q : ℂ) *
          ((clockAngle N k - clockAngle N j : ℝ) : ℂ)) := hsum
      _ = (N : ℂ)⁻¹ * ∑ q : Fin N, Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) *
            (clockAngle N q : ℂ)) := hsum.symm
      _ = if j = k then 1 else 0 := by simpa [hNdiv] using h
  calc
    (villainWeight β (clockAngle N k) : ℂ) =
      ∑ j : Fin N, f j * (if j = k then 1 else 0) := by simp [f]
    _ = ∑ j : Fin N, f j * ((N : ℂ)⁻¹ *
          ∑ q : Fin N, Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) *
            (clockAngle N q : ℂ))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hchar j]
    _ = (N : ℂ)⁻¹ * ∑ q : Fin N, ∑ j : Fin N,
          f j * Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N j : ℂ)) *
            Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) := by
      symm
      calc
        (N : ℂ)⁻¹ * ∑ q : Fin N, ∑ j : Fin N,
            f j * Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N j : ℂ)) *
              Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
          (N : ℂ)⁻¹ * ∑ j : Fin N, ∑ q : Fin N,
            f j * Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N j : ℂ)) *
              Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) := by
                congr 1
                exact Finset.sum_comm
        _ = ∑ j : Fin N, f j * ((N : ℂ)⁻¹ *
              ∑ q : Fin N, Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) *
                (clockAngle N q : ℂ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          have hphase (q : Fin N) :
              Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N j : ℂ)) *
                Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
              Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) *
                (clockAngle N q : ℂ)) := by
            rw [← Complex.exp_add]
            congr 1
            unfold clockAngle
            push_cast
            field_simp
            ring
          calc
            (N : ℂ)⁻¹ * ∑ q : Fin N,
                f j * Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N j : ℂ)) *
                  Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
              (N : ℂ)⁻¹ * (f j * ∑ q : Fin N,
                Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) *
                  (clockAngle N q : ℂ))) := by
                    congr 1
                    calc
                      ∑ q : Fin N, f j *
                          Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N j : ℂ)) *
                            Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
                        ∑ q : Fin N, f j * Complex.exp (Complex.I *
                            (((k : ℤ) - j : ℤ) : ℂ) * (clockAngle N q : ℂ)) := by
                          apply Finset.sum_congr rfl
                          intro q _
                          rw [show f j * Complex.exp (-Complex.I * (q : ℂ) *
                              (clockAngle N j : ℂ)) * Complex.exp (Complex.I * (q : ℂ) *
                              (clockAngle N k : ℂ)) = f j *
                                (Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N j : ℂ)) *
                                  Complex.exp (Complex.I * (q : ℂ) *
                                    (clockAngle N k : ℂ))) by ring]
                          rw [hphase q]
                      _ = f j * ∑ q : Fin N, Complex.exp (Complex.I *
                            (((k : ℤ) - j : ℤ) : ℂ) * (clockAngle N q : ℂ)) := by
                          rw [Finset.mul_sum]
            _ = f j * ((N : ℂ)⁻¹ * ∑ q : Fin N,
                  Complex.exp (Complex.I * (((k : ℤ) - j : ℤ) : ℂ) *
                    (clockAngle N q : ℂ))) := by ring
    _ = ∑ q : Fin N, sampledFourierCoefficient β N q *
          Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) := by
      unfold sampledFourierCoefficient
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      calc
        (N : ℂ)⁻¹ * ∑ j : Fin N,
            f j * Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N j : ℂ)) *
              Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) =
          ((N : ℂ)⁻¹ * ∑ j : Fin N,
              f j * Complex.exp (-Complex.I * (q : ℂ) * (clockAngle N j : ℂ))) *
              Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) := by
                rw [← Finset.sum_mul]
                ring
        _ = _ := by rfl

/-- The exact finite residue expansion, with each coefficient resolved into its Gaussian aliases.
The nonprincipal frequencies `q + Nℓ` are all retained in their class. -/
theorem sampledVillain_eq_gaussianAliasFourier (β : ℝ) {N : ℕ} (hN : 0 < N)
    (hβ : 0 < β) (k : Fin N) :
    (villainWeight β (clockAngle N k) : ℂ) =
      ∑ q : Fin N, gaussianAliasCoefficient β N q *
        Complex.exp (Complex.I * (q : ℂ) * (clockAngle N k : ℂ)) := by
  rw [sampledVillain_eq_dft β hN k]
  apply Finset.sum_congr rfl
  intro q _
  rw [sampledFourierCoefficient_eq_gaussianAlias β hN hβ]

end FroehlichSpencer.BKT.Clock.VillainClock

end
