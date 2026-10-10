/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.TwoPoint
public import FroehlichSpencer.BKT.Clock.HighTemp.RootCancellation
public import FroehlichSpencer.BKT.Clock.HighTemp.BondWeight
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic

/-!
# Rotating finite clock configurations

This module records how a cyclic shift acts on clock angles, bond cosines, and
finite spin configurations. The integer turn in the angle lift handles wraparound.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.HighTemp

open FroehlichSpencer.BKT.Clock.Compact

/-- Addition of clock labels lifts to angle addition modulo an integer turn. -/
theorem clockAngle_add (N : ℕ) (hN : 0 < N) (a r : Fin N) :
    clockAngles N (fun _ : Unit => a + r) () =
      clockAngles N (fun _ : Unit => a) () + clockAngles N (fun _ : Unit => r) () -
        2 * Real.pi * (((a.val + r.val) / N : ℕ) : ℝ) := by
  have hNat : (a + r).val + N * ((a.val + r.val) / N) = a.val + r.val := by
    rw [Fin.val_add, Nat.mod_add_div]
  have hReal : ((a + r).val : ℝ) + (N : ℝ) * (((a.val + r.val) / N : ℕ) : ℝ) =
      (a.val : ℝ) + (r.val : ℝ) := by exact_mod_cast hNat
  have hval : ((a + r).val : ℝ) =
      (a.val : ℝ) + (r.val : ℝ) - (N : ℝ) * (((a.val + r.val) / N : ℕ) : ℝ) := by
    linarith
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold clockAngles
  change 2 * Real.pi * ((a + r).val : ℝ) / N = _
  rw [hval]
  field_simp [hNreal]

/-- Rotating both endpoints of a bond leaves its cosine unchanged. -/
theorem cos_clockAngle_add_sub (N : ℕ) (hN : 0 < N) (a b r : Fin N) :
    Real.cos (clockAngles N (fun _ : Unit => a + r) () -
      clockAngles N (fun _ : Unit => b + r) ()) =
    Real.cos (clockAngles N (fun _ : Unit => a) () -
      clockAngles N (fun _ : Unit => b) ()) := by
  rw [clockAngle_add N hN a r, clockAngle_add N hN b r]
  have hqa : (((a.val + r.val) / N : ℕ) : ℝ) =
      ((((a.val + r.val) / N : ℕ) : ℤ) : ℝ) := by norm_cast
  have hqb : (((b.val + r.val) / N : ℕ) : ℝ) =
      ((((b.val + r.val) / N : ℕ) : ℤ) : ℝ) := by norm_cast
  rw [hqa, hqb]
  have harg :
      (clockAngles N (fun _ : Unit => a) () + clockAngles N (fun _ : Unit => r) () -
          2 * Real.pi * ((((a.val + r.val) / N : ℕ) : ℤ) : ℝ)) -
        (clockAngles N (fun _ : Unit => b) () + clockAngles N (fun _ : Unit => r) () -
          2 * Real.pi * ((((b.val + r.val) / N : ℕ) : ℤ) : ℝ)) =
      (clockAngles N (fun _ : Unit => a) () - clockAngles N (fun _ : Unit => b) ()) +
        ((((b.val + r.val) / N : ℕ) : ℤ) - (((a.val + r.val) / N : ℕ) : ℤ)) *
          (2 * Real.pi) := by
    ring
  rw [harg]
  simpa only [Int.cast_sub] using Real.cos_add_int_mul_two_pi
    (clockAngles N (fun _ : Unit => a) () - clockAngles N (fun _ : Unit => b) ())
    ((((b.val + r.val) / N : ℕ) : ℤ) - (((a.val + r.val) / N : ℕ) : ℤ))

/-- Rotating only the left endpoint adds the clock angle, modulo a full turn. -/
theorem cos_clockAngle_add_left (N : ℕ) (hN : 0 < N) (a b r : Fin N) :
    Real.cos (clockAngles N (fun _ : Unit => a + r) () -
      clockAngles N (fun _ : Unit => b) ()) =
    Real.cos ((clockAngles N (fun _ : Unit => a) () -
      clockAngles N (fun _ : Unit => b) ()) + clockAngles N (fun _ : Unit => r) ()) := by
  rw [clockAngle_add N hN a r]
  have hqa : (((a.val + r.val) / N : ℕ) : ℝ) =
      ((((a.val + r.val) / N : ℕ) : ℤ) : ℝ) := by norm_cast
  rw [hqa]
  have harg :
      (clockAngles N (fun _ : Unit => a) () + clockAngles N (fun _ : Unit => r) () -
          2 * Real.pi * ((((a.val + r.val) / N : ℕ) : ℤ) : ℝ)) -
        clockAngles N (fun _ : Unit => b) () =
      (clockAngles N (fun _ : Unit => a) () - clockAngles N (fun _ : Unit => b) () +
        clockAngles N (fun _ : Unit => r) ()) +
        (-(((a.val + r.val) / N : ℕ) : ℤ)) * (2 * Real.pi) := by
    ring
  rw [harg]
  simpa only [Int.cast_neg] using Real.cos_add_int_mul_two_pi
    (clockAngles N (fun _ : Unit => a) () - clockAngles N (fun _ : Unit => b) () +
      clockAngles N (fun _ : Unit => r) ()) (-(((a.val + r.val) / N : ℕ) : ℤ))

/-- Rotate all clock spins in `C` by `r`. -/
noncomputable def rotateClockConfig {V : Type*} {N : ℕ} [NeZero N]
    (C : Set V) (r : Fin N) (k : V → Fin N) : V → Fin N := by
  classical
  exact fun x => if x ∈ C then k x + r else k x

/-- The rotation of a clock configuration on a fixed vertex set is a bijection. -/
def rotateClockConfigEquiv {V : Type*} {N : ℕ} [NeZero N] (C : Set V) (r : Fin N) :
    (V → Fin N) ≃ (V → Fin N) where
  toFun := rotateClockConfig C r
  invFun := rotateClockConfig C (-r)
  left_inv k := by
    funext x
    by_cases hx : x ∈ C
    · simp [rotateClockConfig, hx, add_assoc]
    · simp [rotateClockConfig, hx]
  right_inv k := by
    funext x
    by_cases hx : x ∈ C
    · simp [rotateClockConfig, hx, add_assoc]
    · simp [rotateClockConfig, hx]

/-- The clock defect on an edge is unchanged when both endpoints are rotated. -/
theorem bondDefect_rotate_both (N : ℕ) [NeZero N] (hN : 0 < N) (β : ℝ)
    {V : Type*} (C : Set V) (k : V → Fin N) (r : Fin N) {x y : V}
    (hxy : x ∈ C ↔ y ∈ C) :
    bondDefect β (clockAngles N (rotateClockConfig C r k) x -
      clockAngles N (rotateClockConfig C r k) y) =
    bondDefect β (clockAngles N k x - clockAngles N k y) := by
  by_cases hx : x ∈ C
  · have hy : y ∈ C := hxy.mp hx
    have hcos := cos_clockAngle_add_sub N hN (k x) (k y) r
    simp only [bondDefect]
    rw [show Real.cos (clockAngles N (rotateClockConfig C r k) x -
        clockAngles N (rotateClockConfig C r k) y) =
        Real.cos (clockAngles N k x - clockAngles N k y) by
          simpa [rotateClockConfig, clockAngles, hx, hy] using hcos]
  · have hy : y ∉ C := fun hy => hx (hxy.mpr hy)
    simp [bondDefect, rotateClockConfig, clockAngles, hx, hy]

/-- Averaging a marked clock character over rotations of a set kills the term when the two marks
lie on opposite sides of that set and every selected bond has both endpoints on the same side. -/
theorem clockMarkedBondTerm_eq_zero_of_cut
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : FroehlichSpencer.BKT.Multigraph V E) (N : ℕ) [NeZero N] (hN : 2 ≤ N)
    (C : Set V) (u v : V) (hu : u ∈ C) (hv : v ∉ C) (β : ℝ) (A : Finset E)
    (hA : ∀ e ∈ A, G.src e ∈ C ↔ G.tgt e ∈ C) :
    ∑ k : V → Fin N,
      Real.cos (clockAngles N k u - clockAngles N k v) *
        ∏ e ∈ A, bondDefect β
          (clockAngles N k (G.src e) - clockAngles N k (G.tgt e)) = 0 := by
  classical
  have hNpos : 0 < N := by omega
  let f : (V → Fin N) → ℝ := fun k =>
    Real.cos (clockAngles N k u - clockAngles N k v) *
      ∏ e ∈ A, bondDefect β (clockAngles N k (G.src e) - clockAngles N k (G.tgt e))
  have hweight (k : V → Fin N) (r : Fin N) :
      (∏ e ∈ A, bondDefect β
        (clockAngles N (rotateClockConfig C r k) (G.src e) -
          clockAngles N (rotateClockConfig C r k) (G.tgt e))) =
      ∏ e ∈ A, bondDefect β
        (clockAngles N k (G.src e) - clockAngles N k (G.tgt e)) := by
    apply Finset.prod_congr rfl
    intro e he
    exact bondDefect_rotate_both N hNpos β C k r
      (x := G.src e) (y := G.tgt e) (hA e he)
  have hmark (k : V → Fin N) (r : Fin N) :
      Real.cos (clockAngles N (rotateClockConfig C r k) u -
        clockAngles N (rotateClockConfig C r k) v) =
        Real.cos ((clockAngles N k u - clockAngles N k v) +
          clockAngles N (fun _ : Unit => r) ()) := by
    have hcos := cos_clockAngle_add_left N hNpos (k u) (k v) r
    simpa [rotateClockConfig, clockAngles, hu, hv] using hcos
  have hreindex (r : Fin N) :
      (∑ k : V → Fin N, f k) =
        ∑ k : V → Fin N, f (rotateClockConfig C r k) := by
    change (∑ k : V → Fin N, f k) =
      ∑ k : V → Fin N, f ((rotateClockConfigEquiv C r) k)
    exact (Equiv.sum_comp (rotateClockConfigEquiv C r) f).symm
  have hrotChar (k : V → Fin N) :
      ∑ r : Fin N,
        Real.cos ((clockAngles N k u - clockAngles N k v) +
          clockAngles N (fun _ : Unit => r) ()) = 0 := by
    have hsum := fin_clockRotation_cos_sum_zero N hN
      (clockAngles N k u - clockAngles N k v)
    calc
      ∑ r : Fin N,
          Real.cos ((clockAngles N k u - clockAngles N k v) +
            clockAngles N (fun _ : Unit => r) ()) =
        ∑ r : Fin N,
          Real.cos ((clockAngles N k u - clockAngles N k v) +
            (r.val : ℝ) * (2 * Real.pi / N)) := by
              apply Finset.sum_congr rfl
              intro r hr
              congr 1
              simp [clockAngles]
              ring
      _ = 0 := hsum
  have hinner (k : V → Fin N) :
      ∑ r : Fin N, f (rotateClockConfig C r k) = 0 := by
    calc
      ∑ r : Fin N, f (rotateClockConfig C r k) =
          (∑ r : Fin N,
            Real.cos ((clockAngles N k u - clockAngles N k v) +
              clockAngles N (fun _ : Unit => r) ())) *
            ∏ e ∈ A, bondDefect β
              (clockAngles N k (G.src e) - clockAngles N k (G.tgt e)) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro r hr
                simp [f, hmark, hweight]
      _ = 0 := by rw [hrotChar k, zero_mul]
  have htotal : (N : ℝ) * (∑ k : V → Fin N, f k) = 0 := by
    calc
      (N : ℝ) * (∑ k : V → Fin N, f k) =
          ∑ r : Fin N, ∑ k : V → Fin N, f k := by simp
      _ = ∑ r : Fin N, ∑ k : V → Fin N,
            f (rotateClockConfig C r k) := by
              apply Finset.sum_congr rfl
              intro r hr
              exact hreindex r
      _ = ∑ k : V → Fin N, ∑ r : Fin N, f (rotateClockConfig C r k) := by
            exact Finset.sum_comm
      _ = 0 := by simp_rw [hinner]; simp
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  exact (mul_eq_zero.mp htotal).resolve_left hNreal

end FroehlichSpencer.BKT.Clock.HighTemp

end
