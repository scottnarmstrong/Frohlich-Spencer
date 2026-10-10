/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Cubical.DualStokes

/-!
# Primal cubical pairing and Stokes identity
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

/-- The coefficient pairing between a finite real cubical chain and a real
cochain on the same cells. -/
@[expose] noncomputable def chainPairing {d : ℕ} {B : Box d}
    (q : RealChain d B) (f : Cell d B → ℝ) : ℝ :=
  Finsupp.linearCombination ℝ f q

@[simp] theorem chainPairing_add {d : ℕ} {B : Box d}
    (q r : RealChain d B) (f : Cell d B → ℝ) :
    chainPairing (q + r) f = chainPairing q f + chainPairing r f := by
  simp only [chainPairing, map_add]

@[simp] theorem chainPairing_smul {d : ℕ} {B : Box d}
    (a : ℝ) (q : RealChain d B) (f : Cell d B → ℝ) :
    chainPairing (a • q) f = a * chainPairing q f := by
  simp [chainPairing, map_smul, smul_eq_mul]

@[simp] theorem chainPairing_single {d : ℕ} {B : Box d}
    (c : Cell d B) (a : ℝ) (f : Cell d B → ℝ) :
    chainPairing (Finsupp.single c a) f = a * f c := by
  simp [chainPairing, Finsupp.linearCombination_single]

/-- Coboundary of a cochain, defined as the transpose of the repository's
cubical boundary incidence. -/
@[expose] noncomputable def cochainCoboundary {d : ℕ} {B : Box d}
    (f : Cell d B → ℝ) : Cell d B → ℝ := fun c =>
  chainPairing (realBoundary (Finsupp.single c 1)) f

/-- Discrete Stokes: the cochain coboundary is adjoint to the cubical boundary. -/
theorem chainPairing_boundary_eq_coboundary {d : ℕ} {B : Box d}
    (q : RealChain d B) (f : Cell d B → ℝ) :
    chainPairing (realBoundary q) f = chainPairing q (cochainCoboundary f) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [chainPairing]
  | add q r hq hr =>
      rw [map_add, chainPairing_add, hq, hr, ← chainPairing_add]
  | single c z =>
      have hsingle : Finsupp.single c z = z • Finsupp.single c (1 : ℝ) := by
        ext x
        by_cases hx : x = c <;> simp [hx]
      calc
        chainPairing (realBoundary (Finsupp.single c z)) f =
            chainPairing (z • realBoundary (Finsupp.single c 1)) f := by
              rw [hsingle, map_smul]
        _ = z * chainPairing (realBoundary (Finsupp.single c 1)) f := by rw [chainPairing_smul]
        _ = z * cochainCoboundary f c := rfl
        _ = chainPairing (Finsupp.single c z) (cochainCoboundary f) := by
              rw [hsingle, chainPairing_smul]
              simp [cochainCoboundary]

end FroehlichSpencer.FS82.Wilson

end
