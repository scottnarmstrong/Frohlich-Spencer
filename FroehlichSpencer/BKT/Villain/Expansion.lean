/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Fourier.Character
public import FroehlichSpencer.BKT.Fourier.PeriodizedGaussian
public import FroehlichSpencer.BKT.Villain.CurrentExpansion
public import FroehlichSpencer.BKT.Villain.CurrentSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite-graph Villain Fourier expansion

The root angle is pinned to zero and the remaining angles have product restricted Lebesgue
measure on `[-π, π)`, following KP §1.4, p. 4. The Fourier modes are integer edge currents as in
KP §6.1, p. 33.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FroehlichSpencer.BKT.Villain

universe u v

/-- The vertices whose angles are integrated, with the root removed. -/
abbrev FreeVertices (V : Type u) (z : V) := {j : V // j ≠ z}

/-- Coordinates for a root-pinned angle configuration. -/
abbrev FreeAngles (V : Type u) (z : V) := FreeVertices V z → ℝ

/-- Extend the free angles to all vertices by setting the root angle to zero. -/
def pinnedAngle {V : Type u} [DecidableEq V] (z : V) (θ : FreeAngles V z) (j : V) : ℝ :=
  if hj : j ≠ z then θ ⟨j, hj⟩ else 0

@[simp] theorem pinnedAngle_root {V : Type u} [DecidableEq V] (z : V)
    (θ : FreeAngles V z) : pinnedAngle z θ z = 0 := by
  simp [pinnedAngle]

@[simp] theorem pinnedAngle_of_ne {V : Type u} [DecidableEq V] (z j : V)
    (θ : FreeAngles V z) (hj : j ≠ z) : pinnedAngle z θ j = θ ⟨j, hj⟩ := by
  simp [pinnedAngle, hj]

/-- Product Lebesgue measure on the non-root angle box `[-π, π)^(V \ {z})`, as in KP p. 4. -/
def rootedAngleMeasure {V : Type u} [Fintype V] [DecidableEq V] (z : V) :
    MeasureTheory.Measure (FreeAngles V z) :=
  MeasureTheory.Measure.pi
    (fun _ : FreeVertices V z => volume.restrict (Set.Ico (-Real.pi) Real.pi))

/-- The Fourier phase contributed by one edge at a single integer frequency. -/
def edgeFourierPhase {V E : Type*} [DecidableEq V] (G : Multigraph V E)
    (z : V) (θ : FreeAngles V z) (e : E) (m : ℤ) : ℂ :=
  Complex.exp (-Complex.I * (m : ℂ) *
    (((pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℝ) : ℂ))

/-- The product of the one-edge phases belonging to an integer current. -/
def edgeCurrentPhase {V E : Type*} [DecidableEq V] (G : Multigraph V E)
    (z : V) (q : E → ℤ) (θ : FreeAngles V z) (e : E) : ℂ :=
  edgeFourierPhase G z θ e (q e)

/-- The edge pairing with a vertex function is the divergence pairing. -/
theorem currentDivergence_pairing {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (q : E → ℤ) (f : V → ℂ) :
    ∑ e, (q e : ℂ) * (f (G.src e) - f (G.tgt e)) =
      ∑ j, (currentDivergence G q j : ℂ) * f j := by
  classical
  have hsrc :
      ∑ e, (q e : ℂ) * f (G.src e) =
        ∑ j, (∑ e, if G.src e = j then (q e : ℂ) else 0) * f j := by
    calc
      ∑ e, (q e : ℂ) * f (G.src e) =
          ∑ e, ∑ j, (if G.src e = j then (q e : ℂ) else 0) * f j := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_eq_single (G.src e)]
        · simp
        · intro j hj hne
          simp [Ne.symm hne]
        · simp
      _ = ∑ j, ∑ e, (if G.src e = j then (q e : ℂ) else 0) * f j :=
        Finset.sum_comm
      _ = ∑ j, (∑ e, if G.src e = j then (q e : ℂ) else 0) * f j := by
        congr 1
        funext j
        rw [Finset.sum_mul]
  have htgt :
      ∑ e, (q e : ℂ) * f (G.tgt e) =
        ∑ j, (∑ e, if G.tgt e = j then (q e : ℂ) else 0) * f j := by
    calc
      ∑ e, (q e : ℂ) * f (G.tgt e) =
          ∑ e, ∑ j, (if G.tgt e = j then (q e : ℂ) else 0) * f j := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_eq_single (G.tgt e)]
        · simp
        · intro j hj hne
          simp [Ne.symm hne]
        · simp
      _ = ∑ j, ∑ e, (if G.tgt e = j then (q e : ℂ) else 0) * f j :=
        Finset.sum_comm
      _ = ∑ j, (∑ e, if G.tgt e = j then (q e : ℂ) else 0) * f j := by
        congr 1
        funext j
        rw [Finset.sum_mul]
  calc
    ∑ e, (q e : ℂ) * (f (G.src e) - f (G.tgt e)) =
        (∑ e, (q e : ℂ) * f (G.src e)) - (∑ e, (q e : ℂ) * f (G.tgt e)) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      funext e
      ring
    _ = (∑ j, (∑ e, if G.src e = j then (q e : ℂ) else 0) * f j) -
        (∑ j, (∑ e, if G.tgt e = j then (q e : ℂ) else 0) * f j) := by rw [hsrc, htgt]
    _ = ∑ j, (currentDivergence G q j : ℂ) * f j := by
      symm
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [currentDivergence, Int.cast_sub]
      have hsrcj :
          (↑(∑ e, if G.src e = j then q e else 0) : ℂ) =
            ∑ e, if G.src e = j then (q e : ℂ) else 0 := by
        simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero]
      have htgtj :
          (↑(∑ e, if G.tgt e = j then q e else 0) : ℂ) =
            ∑ e, if G.tgt e = j then (q e : ℂ) else 0 := by
        simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero]
      rw [hsrcj, htgtj]
      ring

/-- The product of edge phases is the product of vertex characters with frequency minus the
current divergence. -/
theorem edgeCurrentPhase_prod_eq_vertexCharacter {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (z : V) (q : E → ℤ)
    (θ : FreeAngles V z) :
    (∏ e, edgeCurrentPhase G z q θ e) =
      ∏ j : FreeVertices V z,
        Complex.exp (Complex.I * (-(currentDivergence G q j.1) : ℂ) * (θ j : ℂ)) := by
  classical
  let f : V → ℂ := fun j => (pinnedAngle z θ j : ℂ)
  have hsum :
      ∑ e, -Complex.I * (q e : ℂ) *
          (((pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℝ) : ℂ) =
        ∑ j, Complex.I * (-(currentDivergence G q j : ℂ)) * f j := by
    calc
      _ = -Complex.I * ∑ e, (q e : ℂ) *
            (f (G.src e) - f (G.tgt e)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          simp only [f, Complex.ofReal_sub]
          ring
      _ = -Complex.I * ∑ j, (currentDivergence G q j : ℂ) * f j := by
          rw [currentDivergence_pairing]
      _ = ∑ j, Complex.I * (-(currentDivergence G q j : ℂ)) * f j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
  have hvertex :
      ∑ j : V, Complex.I * (-(currentDivergence G q j : ℂ)) * f j =
        ∑ j : FreeVertices V z,
          Complex.I * (-(currentDivergence G q j.1 : ℂ)) * (θ j : ℂ) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun j : V => Complex.I * (-(currentDivergence G q j : ℂ)) * f j) z]
    have hroot : Complex.I * (-(currentDivergence G q z : ℂ)) * f z = 0 := by
      simp [f]
    rw [hroot, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, pinnedAngle, j.2]
  calc
    ∏ e, edgeCurrentPhase G z q θ e =
        Complex.exp (∑ e, -Complex.I * (q e : ℂ) *
          (((pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℝ) : ℂ)) := by
      simp only [edgeCurrentPhase, edgeFourierPhase]
      rw [← Complex.exp_sum]
    _ = Complex.exp (∑ j, Complex.I * (-(currentDivergence G q j : ℂ)) * f j) := by
      rw [hsum]
    _ = Complex.exp (∑ j : FreeVertices V z,
          Complex.I * (-(currentDivergence G q j.1) : ℂ) * (θ j : ℂ)) := by
      exact congrArg Complex.exp hvertex
    _ = ∏ j : FreeVertices V z,
          Complex.exp (Complex.I * (-(currentDivergence G q j.1) : ℂ) * (θ j : ℂ)) := by
      rw [Complex.exp_sum]

/-- The current Fourier term after collecting edge Gaussian factors and grouping the phases by
vertex. -/
def currentFourierTerm {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (z : V) (β : ℝ) (q : E → ℤ) (θ : FreeAngles V z) : ℂ :=
  (currentGaussianWeight β q : ℂ) *
    ∏ j : FreeVertices V z,
      Complex.exp (Complex.I * (-(currentDivergence G q j.1) : ℂ) * (θ j : ℂ))

/-- The product of one-edge Fourier series is the single series over integer edge currents. -/
theorem villain_product_fourier_pointwise {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (z : V) (β : ℝ) (hβ : 0 < β)
    (θ : FreeAngles V z) :
    (∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ)) =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ, currentFourierTerm G z β q θ := by
  classical
  let coeff (e : E) (m : ℤ) : ℂ :=
    (Real.exp (-((m : ℝ) ^ 2) / (2 * β)) : ℂ) * edgeFourierPhase G z θ e m
  have hcoeff : ∀ e, Summable (fun m : ℤ => ‖coeff e m‖) := by
    intro e
    have hseries := FroehlichSpencer.BKT.VillainWeight.villainWeight_fourier_coeff_summable hβ
    have hphase (m : ℤ) : ‖edgeFourierPhase G z θ e m‖ = 1 := by
      rw [edgeFourierPhase, Complex.norm_exp]
      have hreal :
          (-Complex.I * (m : ℂ) *
            (((pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℝ) : ℂ)).re = 0 := by
        simp [Complex.mul_re]
      rw [hreal, Real.exp_zero]
    apply hseries.congr
    intro m
    change Real.exp (-((m : ℝ) ^ 2) / (2 * β)) =
      ‖(Real.exp (-((m : ℝ) ^ 2) / (2 * β)) : ℂ) * edgeFourierPhase G z θ e m‖
    symm
    rw [Complex.norm_mul, Complex.norm_real, hphase]
    simp [abs_of_pos (Real.exp_pos _)]
  have hseries := tsum_prod_currents coeff hcoeff
  have hscalar (e : E) :
      (villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ) =
        (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑' m : ℤ,
            (Real.exp (-((m : ℝ) ^ 2) / (2 * β)) : ℂ) *
              edgeFourierPhase G z θ e m := by
    simpa [edgeFourierPhase] using
      (FroehlichSpencer.BKT.VillainWeight.villainWeight_fourier_complex_normalized_neg hβ
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)))
  have hprod :
      ∏ e, (villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℂ) =
        (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ∑' q : E → ℤ, currentFourierTerm G z β q θ := by
    calc
      _ = ∏ e, ((((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑' m : ℤ,
              (Real.exp (-((m : ℝ) ^ 2) / (2 * β)) : ℂ) *
                edgeFourierPhase G z θ e m) := by
        apply Finset.prod_congr rfl
        intro e he
        exact hscalar e
      _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
            ∏ e, ∑' m : ℤ,
              (Real.exp (-((m : ℝ) ^ 2) / (2 * β)) : ℂ) *
                edgeFourierPhase G z θ e m := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        rfl
      _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
            ∑' q : E → ℤ, ∏ e, coeff e (q e) := by
        exact congrArg
          (fun x : ℂ => (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^
            Fintype.card E * x) (by simpa only [coeff] using hseries)
      _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
            ∑' q : E → ℤ, currentFourierTerm G z β q θ := by
        congr 1
        apply tsum_congr
        intro q
        simp only [coeff, currentFourierTerm]
        change ∏ e, (Real.exp (-((q e : ℝ) ^ 2) / (2 * β)) : ℂ) *
            edgeCurrentPhase G z q θ e = _
        rw [Finset.prod_mul_distrib]
        rw [edgeCurrentPhase_prod_eq_vertexCharacter]
        simp [currentGaussianWeight, Complex.ofReal_prod]
  exact hprod

end FroehlichSpencer.BKT.Villain

end
