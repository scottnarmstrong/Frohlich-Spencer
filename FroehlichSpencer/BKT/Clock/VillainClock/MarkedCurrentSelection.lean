/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.CurrentExpansion
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Modular current selection for Villain-clock Fourier expansions

Summing a residue-current character over the finite clock spins imposes divergence constraints
modulo `N`.

A marked character changes the constraint by its site charge.

This is the exact
finite-volume selection rule needed before any marked-current estimate can be applied.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Ginibre

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The pairing of a residue current with a vertex function is its divergence pairing. -/
theorem residueCurrentDivergence_pairing {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) {N : ℕ} (j : E → Fin N) (f : V → ℂ) :
    ∑ e, (j e : ℂ) * (f (G.src e) - f (G.tgt e)) =
      ∑ v, (residueCurrentDivergence G j v : ℂ) * f v := by
  classical
  have hsrc :
      ∑ e, (j e : ℂ) * f (G.src e) =
        ∑ v, (∑ e, if G.src e = v then (j e : ℂ) else 0) * f v := by
    calc
      ∑ e, (j e : ℂ) * f (G.src e) =
          ∑ e, ∑ v, (if G.src e = v then (j e : ℂ) else 0) * f v := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_eq_single (G.src e)]
        · simp
        · intro v hv hne
          simp [Ne.symm hne]
        · simp
      _ = ∑ v, ∑ e, (if G.src e = v then (j e : ℂ) else 0) * f v := Finset.sum_comm
      _ = ∑ v, (∑ e, if G.src e = v then (j e : ℂ) else 0) * f v := by
        congr 1
        funext v
        rw [Finset.sum_mul]
  have htgt :
      ∑ e, (j e : ℂ) * f (G.tgt e) =
        ∑ v, (∑ e, if G.tgt e = v then (j e : ℂ) else 0) * f v := by
    calc
      ∑ e, (j e : ℂ) * f (G.tgt e) =
          ∑ e, ∑ v, (if G.tgt e = v then (j e : ℂ) else 0) * f v := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_eq_single (G.tgt e)]
        · simp
        · intro v hv hne
          simp [Ne.symm hne]
        · simp
      _ = ∑ v, ∑ e, (if G.tgt e = v then (j e : ℂ) else 0) * f v := Finset.sum_comm
      _ = ∑ v, (∑ e, if G.tgt e = v then (j e : ℂ) else 0) * f v := by
        congr 1
        funext v
        rw [Finset.sum_mul]
  calc
    ∑ e, (j e : ℂ) * (f (G.src e) - f (G.tgt e)) =
        (∑ e, (j e : ℂ) * f (G.src e)) - (∑ e, (j e : ℂ) * f (G.tgt e)) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      funext e
      ring
    _ = (∑ v, (∑ e, if G.src e = v then (j e : ℂ) else 0) * f v) -
        (∑ v, (∑ e, if G.tgt e = v then (j e : ℂ) else 0) * f v) := by rw [hsrc, htgt]
    _ = ∑ v, (residueCurrentDivergence G j v : ℂ) * f v := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [residueCurrentDivergence, Int.cast_sub]
      have hsrcv :
          (↑(∑ e, if G.src e = v then (j e : ℤ) else 0) : ℂ) =
            ∑ e, if G.src e = v then (j e : ℂ) else 0 := by
        simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero]
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : G.src e = v <;> simp [h]
      have htgtv :
          (↑(∑ e, if G.tgt e = v then (j e : ℤ) else 0) : ℂ) =
            ∑ e, if G.tgt e = v then (j e : ℂ) else 0 := by
        simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero]
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : G.tgt e = v <;> simp [h]
      rw [hsrcv, htgtv]
      ring

/-- The edge phase of a residue current is the product of vertex characters of its divergence. -/
theorem residueCurrentEdgePhase_eq_divergenceCharacter {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (N : ℕ) (j : E → Fin N) (s : V → Fin N) :
    residueCurrentEdgePhase G N j s =
      ∏ v, Complex.exp (Complex.I * (residueCurrentDivergence G j v : ℂ) *
        (clockAngle N (s v) : ℂ)) := by
  classical
  let f : V → ℂ := fun v => (clockAngle N (s v) : ℂ)
  have hsum :
      ∑ e, Complex.I * (j e : ℂ) *
          ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ) =
        ∑ v, Complex.I * (residueCurrentDivergence G j v : ℂ) * f v := by
    calc
      _ = Complex.I * ∑ e, (j e : ℂ) * (f (G.src e) - f (G.tgt e)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        simp only [f, angleField, Complex.ofReal_sub]
        ring
      _ = Complex.I * ∑ v, (residueCurrentDivergence G j v : ℂ) * f v := by
        rw [residueCurrentDivergence_pairing]
      _ = ∑ v, Complex.I * (residueCurrentDivergence G j v : ℂ) * f v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
  calc
    residueCurrentEdgePhase G N j s =
        Complex.exp (∑ e, Complex.I * (j e : ℂ) *
          ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ)) := by
      simp only [residueCurrentEdgePhase]
      rw [← Complex.exp_sum]
    _ = Complex.exp (∑ v, Complex.I * (residueCurrentDivergence G j v : ℂ) * f v) := by
      rw [hsum]
    _ = ∏ v, Complex.exp (Complex.I * (residueCurrentDivergence G j v : ℂ) *
          (clockAngle N (s v) : ℂ)) := by
      simpa only [f] using (Complex.exp_sum Finset.univ
        (fun v => Complex.I * (residueCurrentDivergence G j v : ℂ) * f v))

/-- Summing one current character over all clock configurations imposes divergence conservation
modulo `N` at every vertex. An inserted character with charge `r` shifts each congruence by `r`. -/
theorem residueCurrent_spinCharacterSum {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) {N : ℕ} (hN : 0 < N)
    (j : E → Fin N) (r : V → ℤ) :
    ∑ s : V → Fin N,
      residueCurrentEdgePhase G N j s *
        ∏ v, Complex.exp (Complex.I * (r v : ℂ) * (clockAngle N (s v) : ℂ)) =
      ∏ v, ((N : ℂ) * if (N : ℤ) ∣ residueCurrentDivergence G j v + r v then 1 else 0) := by
  classical
  have hfactor (s : V → Fin N) :
      residueCurrentEdgePhase G N j s *
        ∏ v, Complex.exp (Complex.I * (r v : ℂ) * (clockAngle N (s v) : ℂ)) =
      ∏ v, Complex.exp (Complex.I *
        ((residueCurrentDivergence G j v + r v : ℤ) : ℂ) * (clockAngle N (s v) : ℂ)) := by
    rw [residueCurrentEdgePhase_eq_divergenceCharacter]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfun : (fun s : V → Fin N =>
      residueCurrentEdgePhase G N j s *
        ∏ v, Complex.exp (Complex.I * (r v : ℂ) * (clockAngle N (s v) : ℂ))) =
      fun s => ∏ v, Complex.exp (Complex.I *
        ((residueCurrentDivergence G j v + r v : ℤ) : ℂ) * (clockAngle N (s v) : ℂ)) := funext hfactor
  rw [hfun]
  have hsumfactor : (∑ s : V → Fin N,
      ∏ v, Complex.exp (Complex.I *
        ((residueCurrentDivergence G j v + r v : ℤ) : ℂ) * (clockAngle N (s v) : ℂ))) =
      ∏ v, ∑ k : Fin N, Complex.exp (Complex.I *
        ((residueCurrentDivergence G j v + r v : ℤ) : ℂ) * (clockAngle N k : ℂ)) := by
      symm
      simpa using (Finset.prod_univ_sum
        (t := fun _ : V => Finset.univ)
        (fun v k => Complex.exp (Complex.I *
          ((residueCurrentDivergence G j v + r v : ℤ) : ℂ) * (clockAngle N k : ℂ))))
  rw [hsumfactor]
  apply Finset.prod_congr rfl
  intro v hv
  have hchar := clockCharacterAverage N hN (residueCurrentDivergence G j v + r v)
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    ∑ k : Fin N, Complex.exp (Complex.I *
        ((residueCurrentDivergence G j v + r v : ℤ) : ℂ) * (clockAngle N k : ℂ)) =
      (N : ℂ) * ((N : ℂ)⁻¹ * ∑ k : Fin N, Complex.exp (Complex.I *
        ((residueCurrentDivergence G j v + r v : ℤ) : ℂ) * (clockAngle N k : ℂ))) := by
          field_simp
    _ = (N : ℂ) * if (N : ℤ) ∣ residueCurrentDivergence G j v + r v then 1 else 0 := by
      rw [hchar]

/-- Exact marked numerator/denominator current formula. For an external integer charge `r` at
each vertex, only residue currents with `div(j) + r = 0 (mod N)` at every vertex survive the
clock-spin sum. The denominator is the special case `r = 0`; a two-point numerator uses charges
`+ξ` and `−ξ` at its endpoints. -/
theorem configurationCharacterSum_eq_modularCurrentSum {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : Multigraph V E) (β : ℝ) {N : ℕ}
    (hN : 0 < N) (hβ : 0 < β) (r : V → ℤ) :
    ∑ s : V → Fin N,
      (configurationWeight G β N s : ℂ) *
        ∏ v, Complex.exp (Complex.I * (r v : ℂ) * (clockAngle N (s v) : ℂ)) =
      ∑ j : E → Fin N,
        (∏ e, gaussianAliasCoefficient β N (j e)) *
          ∏ v, ((N : ℂ) *
            if (N : ℤ) ∣ residueCurrentDivergence G j v + r v then 1 else 0) := by
  classical
  calc
    ∑ s : V → Fin N,
        (configurationWeight G β N s : ℂ) *
          ∏ v, Complex.exp (Complex.I * (r v : ℂ) * (clockAngle N (s v) : ℂ)) =
      ∑ s : V → Fin N,
        (∑ j : E → Fin N, ∏ e : E,
          gaussianAliasCoefficient β N (j e) * Complex.exp (Complex.I *
            (j e : ℂ) * ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ))) *
          ∏ v, Complex.exp (Complex.I * (r v : ℂ) * (clockAngle N (s v) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [configurationWeight_eq_residueCurrentSum G β hN hβ s]
    _ = ∑ s : V → Fin N, ∑ j : E → Fin N,
          (∏ e : E, gaussianAliasCoefficient β N (j e)) *
            residueCurrentEdgePhase G N j s *
              ∏ v, Complex.exp (Complex.I * (r v : ℂ) * (clockAngle N (s v) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.prod_mul_distrib]
          simp [residueCurrentEdgePhase]
    _ = ∑ j : E → Fin N, ∑ s : V → Fin N,
          (∏ e : E, gaussianAliasCoefficient β N (j e)) *
            residueCurrentEdgePhase G N j s *
              ∏ v, Complex.exp (Complex.I * (r v : ℂ) * (clockAngle N (s v) : ℂ)) :=
          Finset.sum_comm
    _ = ∑ j : E → Fin N,
          (∏ e : E, gaussianAliasCoefficient β N (j e)) *
            ∏ v, ((N : ℂ) *
              if (N : ℤ) ∣ residueCurrentDivergence G j v + r v then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            ∑ s : V → Fin N,
                (∏ e : E, gaussianAliasCoefficient β N (j e)) *
                  residueCurrentEdgePhase G N j s *
                    ∏ v, Complex.exp (Complex.I * (r v : ℂ) *
                      (clockAngle N (s v) : ℂ)) =
              (∏ e : E, gaussianAliasCoefficient β N (j e)) *
                ∑ s : V → Fin N, residueCurrentEdgePhase G N j s *
                  ∏ v, Complex.exp (Complex.I * (r v : ℂ) *
                    (clockAngle N (s v) : ℂ)) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro s hs
                      ring
            _ = (∏ e : E, gaussianAliasCoefficient β N (j e)) *
                ∏ v, ((N : ℂ) *
                  if (N : ℤ) ∣ residueCurrentDivergence G j v + r v then 1 else 0) := by
                    rw [residueCurrent_spinCharacterSum G hN j r]

/-- The exact partition-function Fourier sum: only residue currents with divergence zero modulo
`N` survive the sum over clock spins. -/
theorem partitionFunction_eq_modularCurrentSum {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : Multigraph V E) (β : ℝ) {N : ℕ}
    (hN : 0 < N) (hβ : 0 < β) :
    (partitionFunction G β N : ℂ) =
      ∑ j : E → Fin N,
        (∏ e, gaussianAliasCoefficient β N (j e)) *
          ∏ v, ((N : ℂ) * if (N : ℤ) ∣ residueCurrentDivergence G j v then 1 else 0) := by
  classical
  change (↑(∑ s : V → Fin N, configurationWeight G β N s) : ℂ) = _
  rw [Complex.ofReal_sum]
  simpa [partitionFunction] using
    (configurationCharacterSum_eq_modularCurrentSum G β hN hβ (fun _ => 0))

end FroehlichSpencer.BKT.Clock.VillainClock

end
