/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.DualHeight
public import FroehlichSpencer.BKT.Clock.VillainClock.EdgeFourier
public import FroehlichSpencer.BKT.Clock.VillainClock.ConditionLambdaActivity
public import FroehlichSpencer.BKT.Clock.VillainClock.DisorderCarrier
import Mathlib.Tactic

/-!
# Self-duality of the Villain clock on the free square

FS81 Remark 4: the Villain-constrained `ℤ_N` clock is self-dual. On the free spin square, the seam
disorder operator at a grid twist `ξ = k/N` equals the two-point function
`⟨cos(k(θ*_a − θ*_b))⟩` of the dual Villain clock on the faces. The dual clock has exterior face
pinned to `0` (wired) and inverse temperature `β* = N² / (4π² β)`
(`gaussianAliasDualTemperature`). Here `a` and `b` are the faces at the two ends of the seam.

* `villainWeight_clock_eq_residueFourier`: the residue expansion at every integer clock angle;
* `twistedPartitionFunction_eq_modularCurrentSum`: the twisted partition function as a sum over
  residue currents, the twist entering as the phase `e^{2πi q t / N}` on the seam;
* **`freeSquareDisorderExpectation_grid_eq_dual`**: the exact duality on the free square.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Ginibre

/-! ### The residue expansion at integer clock angles -/

theorem villainWeight_add_int_mul_two_pi (β x : ℝ) (m : ℤ) :
    villainWeight β (x + m * (2 * Real.pi)) = villainWeight β x := by
  have hper : Function.Periodic (villainWeight β) (2 * Real.pi) :=
    fun y => VillainWeight.villainWeight_add_two_pi β y
  exact (hper.int_mul m) x

/-- The residue expansion of the Villain weight at an arbitrary integer clock angle `2πm/N`. -/
theorem villainWeight_clock_eq_residueFourier (β : ℝ) {N : ℕ} (hN : 0 < N) (hβ : 0 < β)
    (m : ℤ) :
    (villainWeight β (2 * Real.pi * m / N) : ℂ) =
      ∑ q : Fin N, gaussianAliasCoefficient β N q *
        Complex.exp (Complex.I * (q : ℂ) * ((2 * Real.pi * m / N : ℝ) : ℂ)) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set k : Fin N := intResidue hN m with hk
  have hkm : ((k : ℕ) : ℤ) = m - N * (m / N) := by
    rw [hk, intResidue_cast, Int.emod_def]
  have hangle : 2 * Real.pi * m / N = clockAngle N k + ((m / N : ℤ) : ℝ) * (2 * Real.pi) := by
    unfold clockAngle
    have hkm' : ((k : ℕ) : ℝ) = (m : ℝ) - N * ((m / N : ℤ) : ℝ) := by exact_mod_cast hkm
    rw [hkm']
    field_simp
    ring
  rw [hangle, villainWeight_add_int_mul_two_pi, sampledVillain_eq_gaussianAliasFourier β hN hβ k]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  have hphase : Complex.I * (q : ℂ) *
      (((clockAngle N k + ((m / N : ℤ) : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) =
      Complex.I * (q : ℂ) * (clockAngle N k : ℂ) +
        ((((q : ℕ) : ℤ) * (m / N) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hphase, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### The twisted residue-current expansion -/

/-- The seam phase of a residue on an edge, for the integer twist `t`. -/
def seamResiduePhase {E : Type*} [DecidableEq E] (M : Finset E) (N : ℕ) (t : ℤ) (e : E)
    (q : Fin N) : ℂ :=
  if e ∈ M then Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (t : ℂ) / N) else 1

theorem twistedConfigurationWeight_eq_residueCurrentSum {V E : Type*} [Fintype E]
    [DecidableEq E] (G : Multigraph V E) (M : Finset E) (β : ℝ) {N : ℕ} (hN : 0 < N)
    (hβ : 0 < β) (t : ℤ) (s : V → Fin N) :
    (twistedConfigurationWeight G M β ((t : ℝ) / N) N s : ℂ) =
      ∑ j : E → Fin N, (∏ e : E, gaussianAliasCoefficient β N (j e) *
        seamResiduePhase M N t e (j e)) * residueCurrentEdgePhase G N j s := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold twistedConfigurationWeight residueCurrentEdgePhase
  rw [Complex.ofReal_prod]
  have hedge : ∀ e : E, (villainWeight β (angleField N s (G.src e) - angleField N s (G.tgt e) +
      if e ∈ M then 2 * Real.pi * ((t : ℝ) / N) else 0) : ℂ) =
      ∑ q : Fin N, gaussianAliasCoefficient β N q * seamResiduePhase M N t e q *
        Complex.exp (Complex.I * (q : ℂ) *
          ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ)) := by
    intro e
    obtain ⟨m, hm⟩ : ∃ m : ℤ,
        m = ((s (G.src e) : ℕ) : ℤ) - ((s (G.tgt e) : ℕ) : ℤ) + if e ∈ M then t else 0 :=
      ⟨_, rfl⟩
    have harg : angleField N s (G.src e) - angleField N s (G.tgt e) +
        (if e ∈ M then 2 * Real.pi * ((t : ℝ) / N) else 0) = 2 * Real.pi * m / N := by
      rw [hm]
      simp only [angleField, clockAngle]
      split_ifs
      · push_cast
        field_simp
      · push_cast
        field_simp
        ring
    rw [harg, villainWeight_clock_eq_residueFourier β hN hβ m]
    refine Finset.sum_congr rfl fun q _ => ?_
    refine Eq.trans ?_ (mul_assoc _ _ _).symm
    congr 1
    unfold seamResiduePhase
    rw [hm]
    simp only [angleField, clockAngle]
    split_ifs
    · rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    · rw [one_mul]
      congr 1
      push_cast
      ring
  calc
    (∏ e : E, (villainWeight β (angleField N s (G.src e) - angleField N s (G.tgt e) +
        if e ∈ M then 2 * Real.pi * ((t : ℝ) / N) else 0) : ℂ)) =
      ∏ e : E, ∑ q : Fin N, gaussianAliasCoefficient β N q * seamResiduePhase M N t e q *
        Complex.exp (Complex.I * (q : ℂ) *
          ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ)) :=
        Finset.prod_congr rfl fun e _ => hedge e
    _ = ∑ j : E → Fin N, ∏ e : E, gaussianAliasCoefficient β N (j e) *
          seamResiduePhase M N t e (j e) * Complex.exp (Complex.I * (j e : ℂ) *
            ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ)) := by
      rw [Finset.prod_univ_sum]
      simp
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.prod_mul_distrib]

/-- **The twisted partition function as a residue-current sum.** Only the residue currents that are
divergence free modulo `N` survive the clock-spin sum; the seam twist `2πt/N` is the phase
`e^{2πi q t/N}` on each seam edge. -/
theorem twistedPartitionFunction_eq_modularCurrentSum {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : Multigraph V E) (M : Finset E) (β : ℝ) {N : ℕ}
    (hN : 0 < N) (hβ : 0 < β) (t : ℤ) :
    (twistedPartitionFunction G M β ((t : ℝ) / N) N : ℂ) =
      (N : ℂ) ^ Fintype.card V * ∑ j : E → Fin N,
        if ∀ v, (N : ℤ) ∣ residueCurrentDivergence G j v then
          ∏ e : E, gaussianAliasCoefficient β N (j e) * seamResiduePhase M N t e (j e)
        else 0 := by
  classical
  unfold twistedPartitionFunction
  push_cast
  simp_rw [twistedConfigurationWeight_eq_residueCurrentSum G M β hN hβ t]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  have hspin := residueCurrent_spinCharacterSum G hN j (fun _ => 0)
  simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, Finset.prod_const_one,
    mul_one, add_zero] at hspin
  have hv : (∏ v, ((N : ℂ) * if (N : ℤ) ∣ residueCurrentDivergence G j v then 1 else 0)) =
      (N : ℂ) ^ Fintype.card V *
        if ∀ v, (N : ℤ) ∣ residueCurrentDivergence G j v then 1 else 0 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies]
  rw [hspin, hv]
  split_ifs <;> ring

/-! ### Evaluation on clock face heights -/

section Heights

variable {L N : ℕ}

/-- The dual angle `2π h(f)/N` of a clock face height; `0` on the exterior face. -/
def dualFaceAngle (h : SquareFreeVertex L → Fin N) (f : RotatorDualFace L) : ℝ :=
  2 * Real.pi * (((clockFaceLift h).1 f : ℤ) : ℝ) / N

/-- The wired dual Villain weight of a clock face height at inverse temperature `βd`. -/
def dualFaceWeight (βd : ℝ) (h : SquareFreeVertex L → Fin N) : ℝ :=
  ∏ e : RotatorInternalBond L, villainWeight βd
    (dualFaceAngle h ((rotatorDualGraph L).src e) - dualFaceAngle h ((rotatorDualGraph L).tgt e))

theorem dualFaceWeight_pos {βd : ℝ} (hβd : 0 < βd) (h : SquareFreeVertex L → Fin N) :
    0 < dualFaceWeight βd h :=
  Finset.prod_pos fun _ _ => VillainWeight.villainWeight_pos hβd _

/-- The Poisson scalar of the Gaussian alias coefficients. -/
def aliasScalar (β : ℝ) : ℝ := (2 * Real.pi * β) ^ (-(1 / 2 : ℝ))

theorem aliasScalar_pos {β : ℝ} (hβ : 0 < β) : 0 < aliasScalar β := by
  unfold aliasScalar
  positivity

/-- The alias coefficient of a height current is the dual Villain weight of the height difference. -/
theorem gaussianAliasCoefficient_clockFaceCurrent {β : ℝ} (hβ : 0 < β) (hN : 0 < N)
    (h : SquareFreeVertex L → Fin N) (e : RotatorInternalBond L) :
    gaussianAliasCoefficient β N (clockFaceCurrent hN h e) =
      (aliasScalar β : ℂ) * (villainWeight (gaussianAliasDualTemperature β N)
        (dualFaceAngle h ((rotatorDualGraph L).src e) -
          dualFaceAngle h ((rotatorDualGraph L).tgt e)) : ℂ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [gaussianAliasCoefficient_eq_activity, gaussianAliasActivity_eq_dualVillainWeight hβ hN]
  congr 2
  set Hc := rotatorFaceHeightCurrent (clockFaceLift h) e with hHc
  have hcur : (((clockFaceCurrent hN h e : ℕ) : ℤ) : ℝ) = (Hc : ℝ) - N * ((Hc / N : ℤ) : ℝ) := by
    have h1 : ((clockFaceCurrent hN h e : ℕ) : ℤ) = Hc - N * (Hc / N) := by
      rw [clockFaceCurrent, intResidue_cast, Int.emod_def]
    exact_mod_cast h1
  have hdiff : dualFaceAngle h ((rotatorDualGraph L).src e) -
      dualFaceAngle h ((rotatorDualGraph L).tgt e) = 2 * Real.pi * (Hc : ℝ) / N := by
    rw [hHc]
    simp only [dualFaceAngle, rotatorFaceHeightCurrent]
    push_cast
    ring
  rw [hdiff, show (2 * Real.pi * (((clockFaceCurrent hN h e : ℕ) : ℤ) : ℝ) / N) =
      2 * Real.pi * (Hc : ℝ) / N + ((-(Hc / N) : ℤ) : ℝ) * (2 * Real.pi) by
    rw [hcur]
    push_cast
    field_simp
    ring]
  exact villainWeight_add_int_mul_two_pi _ _ _

/-- The seam phase of a height current depends only on the integer height difference. -/
theorem seamResiduePhase_clockFaceCurrent {M : Finset (RotatorInternalBond L)} (hN : 0 < N)
    (t : ℤ) (h : SquareFreeVertex L → Fin N) (e : RotatorInternalBond L) :
    seamResiduePhase M N t e (clockFaceCurrent hN h e) =
      if e ∈ M then Complex.exp (2 * Real.pi * Complex.I *
        (rotatorFaceHeightCurrent (clockFaceLift h) e : ℂ) * (t : ℂ) / N) else 1 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold seamResiduePhase
  split_ifs
  · set Hc := rotatorFaceHeightCurrent (clockFaceLift h) e
    have h1 : ((clockFaceCurrent hN h e : ℕ) : ℤ) = Hc - N * (Hc / N) := by
      rw [clockFaceCurrent, intResidue_cast, Int.emod_def]
    have h2 : ((clockFaceCurrent hN h e : ℕ) : ℂ) = (Hc : ℂ) - N * ((Hc / N : ℤ) : ℂ) := by
      exact_mod_cast h1
    rw [h2]
    have harg : 2 * Real.pi * Complex.I * ((Hc : ℂ) - N * ((Hc / N : ℤ) : ℂ)) * (t : ℂ) / N =
        2 * Real.pi * Complex.I * (Hc : ℂ) * (t : ℂ) / N +
          ((-(Hc / N) * t : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · rfl

/-- The product of the alias coefficients and seam phases of a height current. -/
theorem prod_alias_seam_clockFaceCurrent {β : ℝ} (hβ : 0 < β) (hN : 0 < N)
    (M : Finset (RotatorInternalBond L)) (t : ℤ) (h : SquareFreeVertex L → Fin N) :
    (∏ e : RotatorInternalBond L, gaussianAliasCoefficient β N (clockFaceCurrent hN h e) *
        seamResiduePhase M N t e (clockFaceCurrent hN h e)) =
      (aliasScalar β : ℂ) ^ Fintype.card (RotatorInternalBond L) *
        (dualFaceWeight (gaussianAliasDualTemperature β N) h : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) *
          ((∑ e ∈ M, rotatorFaceHeightCurrent (clockFaceLift h) e : ℤ) : ℂ) / N) := by
  classical
  simp only [gaussianAliasCoefficient_clockFaceCurrent hβ hN, seamResiduePhase_clockFaceCurrent hN]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  unfold dualFaceWeight
  rw [Complex.ofReal_prod]
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **The twisted partition function on clock face heights.** -/
theorem twistedPartitionFunction_eq_dualHeightSum {β : ℝ} (hβ : 0 < β) (hN : 0 < N)
    (M : Finset (RotatorInternalBond L)) (t : ℤ) :
    twistedPartitionFunction (rotatorFreeGraph L) M β ((t : ℝ) / N) N =
      (N : ℝ) ^ Fintype.card (RotatorSpinSite L) *
        aliasScalar β ^ Fintype.card (RotatorInternalBond L) *
        ∑ h : SquareFreeVertex L → Fin N, dualFaceWeight (gaussianAliasDualTemperature β N) h *
          Real.cos (2 * Real.pi * t *
            ((∑ e ∈ M, rotatorFaceHeightCurrent (clockFaceLift h) e : ℤ) : ℝ) / N) := by
  classical
  have hC := twistedPartitionFunction_eq_modularCurrentSum (rotatorFreeGraph L) M β hN hβ t
  rw [sum_neutralResidue_eq_sum_clockFaceHeight hN] at hC
  simp only [prod_alias_seam_clockFaceCurrent hβ hN M t] at hC
  have hre := congrArg Complex.re hC
  rw [Complex.ofReal_re] at hre
  rw [hre]
  rw [Finset.mul_sum, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hexp : 2 * Real.pi * Complex.I * (t : ℂ) *
      ((∑ e ∈ M, rotatorFaceHeightCurrent (clockFaceLift h) e : ℤ) : ℂ) / N =
      ((2 * Real.pi * t * ((∑ e ∈ M, rotatorFaceHeightCurrent (clockFaceLift h) e : ℤ) : ℝ) / N :
        ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp]
  have hreal : (N : ℂ) ^ Fintype.card (RotatorSpinSite L) *
      ((aliasScalar β : ℂ) ^ Fintype.card (RotatorInternalBond L) *
        (dualFaceWeight (gaussianAliasDualTemperature β N) h : ℂ)) =
      (((N : ℝ) ^ Fintype.card (RotatorSpinSite L) * aliasScalar β ^
        Fintype.card (RotatorInternalBond L) * dualFaceWeight (gaussianAliasDualTemperature β N) h
          : ℝ) : ℂ) := by
    push_cast
    ring
  rw [← mul_assoc, hreal, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  ring

end Heights

/-! ### The seam carrier -/

section Seam

variable {N : ℕ}

/-- The face at the start of the seam, `(L, L)` in face coordinates. -/
def seamStartFace {L : ℕ} (hL : 0 < L) : SquareFreeVertex (2 * L) :=
  (⟨L, by omega⟩, ⟨L, by omega⟩)

/-- The face at the end of a seam of length `r < L`, `(L + r, L)` in face coordinates. -/
def seamEndFace {r L : ℕ} (hrL : r < L) : SquareFreeVertex (2 * L) :=
  (⟨L + r, by omega⟩, ⟨L, by omega⟩)

/-- The seam phase telescopes to the height difference of the two end faces. -/
theorem sum_seam_rotatorFaceHeightCurrent {r L : ℕ} (hL : 0 < L) (hrL : r < L)
    (h : SquareFreeVertex (2 * L) → Fin N) :
    (∑ e ∈ freeSquareDisorderEdgeSet hL hrL.le,
        rotatorFaceHeightCurrent (clockFaceLift h) e) =
      ((h (seamStartFace hL) : ℕ) : ℤ) - ((h (seamEndFace hrL) : ℕ) : ℤ) := by
  classical
  rw [freeSquareDisorderEdgeSet, Finset.sum_image (disorderSeamEdge_injective hL hrL.le).injOn]
  let g : ℕ → ℤ := fun n =>
    if hn : L + n < 2 * L then ((h (⟨L + n, hn⟩, ⟨L, by omega⟩) : ℕ) : ℤ) else 0
  have hterm : ∀ i : Fin r, rotatorFaceHeightCurrent (clockFaceLift h)
      (disorderSeamEdge hL hrL.le i) = g i.val - g (i.val + 1) := by
    intro i
    have hedge : disorderSeamEdge hL hrL.le i =
        .inr (verticalDualEdgeData ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩) := rfl
    rw [hedge, rotatorFaceHeightCurrent_vertical]
    have h1 : 0 < L + i.val + 1 := by omega
    have h2 : L + i.val + 1 < 2 * L := by have := i.isLt; omega
    have h3 : L + i.val < 2 * L := by omega
    have h4 : L + (i.val + 1) < 2 * L := by omega
    simp only [h1, h2, dite_true, g, h3, h4, clockFaceLift]
    congr 3
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [Fin.sum_univ_eq_sum_range (fun n => g n - g (n + 1)) r, Finset.sum_range_sub']
  have hg0 : g 0 = ((h (seamStartFace hL) : ℕ) : ℤ) := by
    simp only [g, add_zero, show L < 2 * L by omega, dite_true, seamStartFace]
  have hgr : g r = ((h (seamEndFace hrL) : ℕ) : ℤ) := by
    simp only [g, show L + r < 2 * L by omega, dite_true, seamEndFace]
  rw [hg0, hgr]

/-- **Self-duality of the Villain clock on the free square** (FS81 Remark 4). At the grid twist
`ξ = k/N` the seam disorder expectation equals the two-point function `⟨cos(k(θ*_a − θ*_b))⟩` of
the dual Villain clock on the faces, with the exterior face pinned and inverse temperature
`N²/(4π²β)`; `a` and `b` are the faces at the two ends of the seam. -/
theorem freeSquareDisorderExpectation_grid_eq_dual {r L : ℕ} (β : ℝ) (hβ : 0 < β) (hN : 0 < N)
    (hL : 0 < L) (hrL : r < L) (k : ℤ) :
    freeSquareDisorderExpectation N β ((k : ℝ) / N) hβ hN hL hrL.le =
      (∑ h : SquareFreeVertex (2 * L) → Fin N,
          dualFaceWeight (gaussianAliasDualTemperature β N) h *
            Real.cos ((k : ℝ) * (dualFaceAngle h (some (seamStartFace hL)) -
              dualFaceAngle h (some (seamEndFace hrL))))) /
        ∑ h : SquareFreeVertex (2 * L) → Fin N,
          dualFaceWeight (gaussianAliasDualTemperature β N) h := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [freeSquareDisorderExpectation_eq_twistedPartition_ratio]
  have hneg : -((k : ℝ) / N) = ((-k : ℤ) : ℝ) / N := by push_cast; ring
  rw [hneg, twistedPartitionFunction_eq_dualHeightSum hβ hN]
  have hZ : freeSquarePartitionFunction N L β =
      twistedPartitionFunction (rotatorFreeGraph (2 * L)) ∅ β (((0 : ℤ) : ℝ) / N) N := by
    unfold freeSquarePartitionFunction partitionFunction twistedPartitionFunction
      configurationWeight twistedConfigurationWeight
    simp
  rw [hZ, twistedPartitionFunction_eq_dualHeightSum hβ hN]
  simp only [Finset.sum_empty, Int.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one]
  have hC : 0 < (N : ℝ) ^ Fintype.card (RotatorSpinSite (2 * L)) *
      aliasScalar β ^ Fintype.card (RotatorInternalBond (2 * L)) := by
    have := aliasScalar_pos hβ
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  rw [mul_div_mul_left _ _ hC.ne']
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  congr 1
  rw [sum_seam_rotatorFaceHeightCurrent hL hrL h]
  simp only [dualFaceAngle, clockFaceLift]
  rw [← Real.cos_neg]
  congr 1
  push_cast
  field_simp

end Seam

end FroehlichSpencer.BKT.Clock.VillainClock

end
