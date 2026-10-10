/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.MarkedCurrentSelection
import Mathlib.Tactic

/-!
# Integer quotient charges for the modular Villain-clock current constraints

The clock-spin sum requires `div j + r = 0 (mod N)` at every vertex.

Keeping this congruence
produces an exact integer quotient charge `q = (div j + r) / N`; when the inserted source is
neutral, these quotient charges are neutral as an integer configuration.

This is the charge
bookkeeping needed before comparing the modular-current formula with a neutral Coulomb gas.
-/

@[expose] public section

open FroehlichSpencer.BKT.Clock.VillainClock

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The integer quotient charge determined by a modular current and an external source. -/
def residueCurrentQuotientCharge {V E : Type*} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) {N : ℕ} (j : E → Fin N) (r : V → ℤ) (v : V) : ℤ :=
  (residueCurrentDivergence G j v + r v) / (N : ℤ)

/-- The two-point integer source in the spin-current selection rule. -/
def integerDipoleSource {V : Type*} [DecidableEq V] (x y : V) (ξ : ℤ) : V → ℤ :=
  fun v => (if v = x then ξ else 0) - (if v = y then ξ else 0)

theorem sum_integerDipoleSource_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (x y : V) (ξ : ℤ) : ∑ v, integerDipoleSource x y ξ v = 0 := by
  classical
  unfold integerDipoleSource
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq']

/-- The total divergence of a finite-graph current vanishes. -/
theorem sum_residueCurrentDivergence_eq_zero {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) {N : ℕ} (j : E → Fin N) :
    ∑ v, residueCurrentDivergence G j v = 0 := by
  classical
  unfold residueCurrentDivergence
  rw [Finset.sum_sub_distrib]
  have hsrc : (∑ v, ∑ e, if G.src e = v then (j e : ℤ) else 0) = ∑ e, (j e : ℤ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_ite_eq]
    simp
  have htgt : (∑ v, ∑ e, if G.tgt e = v then (j e : ℤ) else 0) = ∑ e, (j e : ℤ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_ite_eq]
    simp
  rw [hsrc, htgt]
  exact sub_self _

/-- A modular constraint determines the exact integer quotient at a vertex. -/
theorem residueCurrentQuotientCharge_spec {V E : Type*} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) {N : ℕ} (j : E → Fin N) (r : V → ℤ) (v : V)
    (hdiv : (N : ℤ) ∣ residueCurrentDivergence G j v + r v) :
    (N : ℤ) * residueCurrentQuotientCharge G j r v =
      residueCurrentDivergence G j v + r v := by
  unfold residueCurrentQuotientCharge
  exact Int.mul_ediv_cancel' hdiv

/-- After rescaling by `N`, a selected current divergence is an integer quotient charge minus
the fractional marked source `r/N`. -/
theorem real_residueCurrentDivergence_eq_quotient_sub_source {V E : Type*}
    [Fintype E] [DecidableEq V] (G : Multigraph V E) {N : ℕ} (hN : 0 < N)
    (j : E → Fin N) (r : V → ℤ) (v : V)
    (hdiv : (N : ℤ) ∣ residueCurrentDivergence G j v + r v) :
    ((residueCurrentDivergence G j v : ℤ) : ℝ) / N =
      (residueCurrentQuotientCharge G j r v : ℝ) - (r v : ℝ) / N := by
  have hspec := residueCurrentQuotientCharge_spec G j r v hdiv
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hcast : (N : ℝ) * (residueCurrentQuotientCharge G j r v : ℝ) =
      (residueCurrentDivergence G j v : ℝ) + r v := by
    exact_mod_cast hspec
  field_simp [hNne]
  nlinarith [hcast]

/-- If the source has total charge zero, the quotient charges are neutral integers. -/
theorem residueCurrentQuotientCharge_neutral {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) {N : ℕ} (hN : 0 < N) (j : E → Fin N)
    (r : V → ℤ) (hsource : ∑ v, r v = 0)
    (hdiv : ∀ v, (N : ℤ) ∣ residueCurrentDivergence G j v + r v) :
    ∑ v, residueCurrentQuotientCharge G j r v = 0 := by
  have hNne : (N : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hmul : (N : ℤ) * ∑ v, residueCurrentQuotientCharge G j r v = 0 := by
    calc
      (N : ℤ) * ∑ v, residueCurrentQuotientCharge G j r v =
          ∑ v, (N : ℤ) * residueCurrentQuotientCharge G j r v := by rw [Finset.mul_sum]
      _ = ∑ v, (residueCurrentDivergence G j v + r v) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact residueCurrentQuotientCharge_spec G j r v (hdiv v)
      _ = 0 := by
        rw [Finset.sum_add_distrib, sum_residueCurrentDivergence_eq_zero, hsource]
        simp
  apply (mul_left_cancel₀ hNne)
  simpa using hmul

/-- The zero-source quotient charges are neutral for every current selected by the unmarked
modular spin sum. -/
theorem unmarked_residueCurrentQuotientCharge_neutral {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) {N : ℕ} (hN : 0 < N) (j : E → Fin N)
    (hdiv : ∀ v, (N : ℤ) ∣ residueCurrentDivergence G j v) :
    ∑ v, residueCurrentQuotientCharge G j (fun _ => 0) v = 0 := by
  apply residueCurrentQuotientCharge_neutral G hN j (fun _ => 0)
  · simp
  · simpa using hdiv

/-- A marked two-point current has neutral integer quotient charges, and its rescaled divergence
is an integer charge configuration shifted by the fractional dipole `ξ/N`. -/
theorem marked_residueCurrentQuotientCharge_neutral {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) {N : ℕ} (hN : 0 < N) (j : E → Fin N)
    (x y : V) (ξ : ℤ)
    (hdiv : ∀ v, (N : ℤ) ∣
      residueCurrentDivergence G j v + integerDipoleSource x y ξ v) :
    ∑ v, residueCurrentQuotientCharge G j (integerDipoleSource x y ξ) v = 0 := by
  apply residueCurrentQuotientCharge_neutral G hN j (integerDipoleSource x y ξ)
  · exact sum_integerDipoleSource_eq_zero x y ξ
  · exact hdiv

/-- At each vertex, the marked current divergence differs from its neutral integer quotient by
the fractional dipole source of size `ξ/N`. -/
theorem marked_real_residueCurrentDivergence_eq_fractionalDipole {V E : Type*}
    [Fintype E] [DecidableEq V] (G : Multigraph V E) {N : ℕ} (hN : 0 < N)
    (j : E → Fin N) (x y : V) (ξ : ℤ) (v : V)
    (hdiv : (N : ℤ) ∣
      residueCurrentDivergence G j v + integerDipoleSource x y ξ v) :
    ((residueCurrentDivergence G j v : ℤ) : ℝ) / N =
      (residueCurrentQuotientCharge G j (integerDipoleSource x y ξ) v : ℝ) -
        (integerDipoleSource x y ξ v : ℝ) / N := by
  exact real_residueCurrentDivergence_eq_quotient_sub_source G hN j
    (integerDipoleSource x y ξ) v hdiv

end FroehlichSpencer.BKT.Clock.VillainClock

end
