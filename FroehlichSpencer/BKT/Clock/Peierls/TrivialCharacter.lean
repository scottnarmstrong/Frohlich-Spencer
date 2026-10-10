/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Window.MasslessWindow
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Basic

/-!
# Trivial residue class of the free clock model

Every integer harmonic divisible by the number of clock states is the trivial character: its
finite-volume two-point function and its free limit are exactly one. This settles the full residue
class `ξ ≡ 0 (mod n)` in the all-harmonics quantifier of the clock Peierls statement. Nonzero
residue classes require the contour estimate in the Peierls argument.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Peierls

open Filter
open MeasureTheory
open Topology
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Window

/-- The zero-frequency two-point function of any free model is one. -/
theorem freeModel_twoPoint_zero (M : FreeModel) (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    M.twoPoint 0 Λ u v = 1 := by
  have hprob : (M.gibbs Λ) Set.univ = 1 := by
    change (pairGibbs M.ν (bondFrequency Λ) (M.bondWeight Λ)) Set.univ = 1
    exact (isProbabilityMeasure_pairGibbs M.mass_ne_zero (M.isBondWeight_bondWeight Λ)).measure_univ
  have hreal : (M.gibbs Λ).real Set.univ = 1 := by
    rw [measureReal_def, hprob]
    simp
  simp [FreeModel.twoPoint, hreal]

/-- The free infinite-volume clock correlation is exactly one at harmonic zero. -/
theorem clockCorr_zero (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (u v : ℤ × ℤ) :
    clockCorr n hn β hβ 0 u v = 1 := by
  change (clockModel n hn β hβ).twoPointLimit 0 u v = 1
  let M := clockModel n hn β hβ
  have hfinite : (fun L : ℕ => M.twoPoint 0 (freeBox L) u v) = fun _ => (1 : ℝ) := by
    funext L
    exact freeModel_twoPoint_zero M (freeBox L) u v
  have hlim : Tendsto (fun L : ℕ => M.twoPoint 0 (freeBox L) u v) atTop
      (𝓝 (M.twoPointLimit 0 u v)) := M.tendsto_twoPointLimit 0 u v
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  rw [hfinite] at hlim
  exact tendsto_nhds_unique hlim hconst

/-- On a finite clock square, a harmonic divisible by the number of clock states is the trivial
character, so its two-point function is exactly one. -/
theorem clockModel_twoPoint_squareBox_eq_one_of_dvd (n L : ℕ) (hn : 0 < n) {β : ℝ}
    (hβ : 0 ≤ β) (ξ : ℤ) (hdiv : (n : ℤ) ∣ ξ) (a b : RotatorSpinSite L) :
    (clockModel n hn β hβ).twoPoint ξ (squareBoxZ L) (siteToZ a) (siteToZ b) = 1 := by
  obtain ⟨q, hq⟩ := hdiv
  have hfreq : (ξ : ℝ) = (n : ℝ) * (q : ℝ) := by
    calc
      (ξ : ℝ) = ((n : ℤ) * q : ℤ) := by exact_mod_cast hq
      _ = (n : ℝ) * (q : ℝ) := by push_cast; ring
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcos (k : RotatorSpinSite L → Fin n) :
      Real.cos (ξ * (clockAngles n k a - clockAngles n k b)) = 1 := by
    have hangle : clockAngles n k a - clockAngles n k b =
        2 * Real.pi * (((k a : ℤ) - (k b : ℤ) : ℤ) : ℝ) / n := by
      unfold clockAngles
      push_cast
      ring
    have hphase : (ξ : ℝ) * (clockAngles n k a - clockAngles n k b) =
        ((q * ((k a : ℤ) - (k b : ℤ)) : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hfreq, hangle]
      push_cast
      field_simp [hnreal]
    rw [hphase]
    exact Real.cos_int_mul_two_pi _
  have hden : 0 < ∑ k : RotatorSpinSite L → Fin n, clockBoxWeight n L β k := by
    apply Finset.sum_pos (fun k _ => by simp only [clockBoxWeight]; exact Real.exp_pos _)
    exact ⟨fun _ => ⟨0, hn⟩, Finset.mem_univ _⟩
  have hnum :
      (∑ k : RotatorSpinSite L → Fin n,
        Real.cos (ξ * (clockAngles n k a - clockAngles n k b)) * clockBoxWeight n L β k) =
        ∑ k, clockBoxWeight n L β k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcos k]
    simp
  rw [clockModel_twoPoint_squareBox n L hn hβ ξ a b, hnum]
  exact div_self hden.ne'

/-- Every harmonic in the zero residue class modulo `n` has long-range order at every
nonnegative inverse temperature. -/
theorem clock_harmonicLongRangeOrder_of_dvd (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β)
    (ξ : ℤ) (hdiv : (n : ℤ) ∣ ξ) : ClockHasLongRangeOrder n hn β hβ ξ := by
  refine ⟨1, one_pos, fun R => ?_⟩
  let a : RotatorSpinSite R :=
    (squareBoxEquiv R).symm ⟨(0, 0), by simp [squareBoxZ]⟩
  let b : RotatorSpinSite R :=
    (squareBoxEquiv R).symm ⟨((R : ℤ), 0), by simp [squareBoxZ]⟩
  have ha : siteToZ a = (0, 0) := by
    rw [← squareBoxEquiv_apply_coe]
    dsimp [a]
    simp
  have hb : siteToZ b = ((R : ℤ), 0) := by
    rw [← squareBoxEquiv_apply_coe]
    dsimp [b]
    simp
  have hfinite := clockModel_twoPoint_squareBox_eq_one_of_dvd n R hn hβ ξ hdiv a b
  have hsites : 1 ≤ (clockModel n hn β hβ).twoPointLimit ξ (0, 0) ((R : ℤ), 0) := by
    rw [← ha, ← hb]
    exact hfinite.symm.le.trans ((clockModel n hn β hβ).twoPoint_le_twoPointLimit ξ
      (siteToZ_mem_squareBoxZ a) (siteToZ_mem_squareBoxZ b))
  refine ⟨(0, 0), ((R : ℤ), 0), ?_, ?_⟩
  · rw [l1Dist_zero_right]
  · exact hsites

end FroehlichSpencer.BKT.Clock.Peierls

end
