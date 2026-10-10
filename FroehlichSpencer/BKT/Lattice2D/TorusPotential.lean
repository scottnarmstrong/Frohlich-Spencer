/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Lattice2D.Torus
public import FroehlichSpencer.BKT.Potential.Transport
import Mathlib.Tactic.Ring

/-!
# Green kernels on the internal square torus

Translations of the torus preserve the oriented right/up edge presentation.
This gives translation invariance of the mean-zero Green kernel and the usual
identity between a point-source Green difference and half the dipole energy.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Lattice2D

open Multigraph

section

variable {n : ℕ} [NeZero n]

/-- Translation by `a` on torus vertices. -/
def torusVertexTranslation (a : TorusVertex n) : TorusVertex n ≃ TorusVertex n where
  toFun p := p + a
  invFun p := p - a
  left_inv p := by simp
  right_inv p := by simp

/-- Translation by `a` on torus edges, preserving their right/up direction. -/
def torusEdgeTranslation (a : TorusVertex n) : TorusEdge n ≃ TorusEdge n where
  toFun e := (e.1 + a, e.2)
  invFun e := (e.1 - a, e.2)
  left_inv e := by cases e with | mk p b => simp
  right_inv e := by cases e with | mk p b => simp

omit [NeZero n] in
/-- A translated right/up step is the translate of the original step. -/
lemma torusStep_translation (a p : TorusVertex n) (direction : Bool) :
    torusStep n direction (p + a) = torusStep n direction p + a := by
  cases direction <;> rcases p with ⟨x, y⟩ <;> rcases a with ⟨a₁, a₂⟩ <;>
    simp [torusStep] <;> ring

/-- Translation is an isomorphism of the torus multigraph. -/
def torusTranslationIso (hn : 2 < n) (a : TorusVertex n) :
    Multigraph.Isomorphism (torusGraph n hn) (torusGraph n hn) where
  vertices := torusVertexTranslation a
  edges := torusEdgeTranslation a
  endpoints := by
    rintro ⟨p, direction⟩
    refine Or.inl ⟨rfl, ?_⟩
    change torusStep n direction (p + a) = torusStep n direction p + a
    exact torusStep_translation a p direction

/-- The Green kernel of the positive operator `-Δ` on the torus. -/
noncomputable def torusGreenKernel (hn : 2 < n) (hG : (torusGraph n hn).Connected)
    (x y : TorusVertex n) : ℝ :=
  (-(torusGraph n hn).greenOp hG (deltaAt y)) x

/-- The torus Green kernel is invariant under simultaneous translation of its
two arguments. -/
theorem torusGreenKernel_translation (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) (a x y : TorusVertex n) :
    torusGreenKernel hn hG (x + a) (y + a) = torusGreenKernel hn hG x y := by
  let I := torusTranslationIso hn a
  have hT := I.greenOp_transport hG (deltaAt y)
  have hdelta : I.pushField (deltaAt y) = deltaAt (y + a) := by
    funext z
    simp [deltaAt, Multigraph.Isomorphism.pushField, I, torusTranslationIso,
      torusVertexTranslation, sub_eq_iff_eq_add]
  have hpoint :
      (torusGraph n hn).greenOp hG (deltaAt y) x =
        (torusGraph n hn).greenOp hG (deltaAt (y + a)) (x + a) := by
    have hp := congrFun hT (x + a)
    rw [hdelta] at hp
    simpa [I, torusTranslationIso, torusVertexTranslation,
      Multigraph.Isomorphism.pushField] using hp
  unfold torusGreenKernel
  exact (congrArg Neg.neg hpoint).symm

/-- The Green kernel is symmetric in its two torus vertices. -/
theorem torusGreenKernel_symm (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) (x y : TorusVertex n) :
    torusGreenKernel hn hG x y = torusGreenKernel hn hG y x := by
  unfold torusGreenKernel
  calc
    -((torusGraph n hn).greenOp hG (deltaAt y)) x =
        -pairing (deltaAt x) ((torusGraph n hn).greenOp hG (deltaAt y)) := by
          rw [pairing_deltaAt_left]
    _ = -pairing ((torusGraph n hn).greenOp hG (deltaAt x)) (deltaAt y) := by
          rw [(torusGraph n hn).pairing_greenOp_comm hG (deltaAt x) (deltaAt y)]
    _ = -pairing (deltaAt y) ((torusGraph n hn).greenOp hG (deltaAt x)) := by
          rw [pairing_comm]
    _ = -((torusGraph n hn).greenOp hG (deltaAt x)) y := by
          rw [pairing_deltaAt_left]

/-- The point-source kernel is the Green bilinear form on unit masses. -/
theorem torusGreenKernel_eq_pairing (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) (x y : TorusVertex n) :
    torusGreenKernel hn hG x y =
      pairing (deltaAt x) (-(torusGraph n hn).greenOp hG (deltaAt y)) := by
  simp [torusGreenKernel, pairing_deltaAt_left]

/-- Pairing is additive in the second argument. -/
theorem pairing_add_right {V : Type*} [Fintype V] (f g h : V → ℝ) :
    pairing f (g + h) = pairing f g + pairing f h := by
  unfold pairing
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Pairing is subtractive in the second argument. -/
theorem pairing_sub_right {V : Type*} [Fintype V] (f g h : V → ℝ) :
    pairing f (g - h) = pairing f g - pairing f h := by
  rw [pairing_comm, pairing_sub_left, pairing_comm g f, pairing_comm h f]

/-- The Green bilinear form associated to the positive inverse `(-Δ)⁻¹`. -/
noncomputable def greenBilinear {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.Connected) (f g : V → ℝ) : ℝ :=
  pairing f (-G.greenOp hG g)

/-- The Green bilinear form is symmetric. -/
theorem greenBilinear_symm {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.Connected)
    (f g : V → ℝ) : greenBilinear G hG f g = greenBilinear G hG g f := by
  unfold greenBilinear
  calc
    pairing f (-G.greenOp hG g) = -pairing f (G.greenOp hG g) :=
      pairing_neg_right _ _
    _ = -pairing (G.greenOp hG f) g :=
      congrArg Neg.neg (G.pairing_greenOp_comm hG f g)
    _ = -pairing g (G.greenOp hG f) :=
      congrArg Neg.neg (pairing_comm _ _)
    _ = pairing g (-G.greenOp hG f) := (pairing_neg_right _ _).symm

/-- Subtracting in the first argument of the Green form. -/
theorem greenBilinear_sub_left {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.Connected)
    (f g h : V → ℝ) :
    greenBilinear G hG (f - g) h = greenBilinear G hG f h - greenBilinear G hG g h := by
  exact pairing_sub_left f g (-G.greenOp hG h)

/-- Subtracting in the second argument of the Green form. -/
theorem greenBilinear_sub_right {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.Connected)
    (f g h : V → ℝ) :
    greenBilinear G hG f (g - h) = greenBilinear G hG f g - greenBilinear G hG f h := by
  unfold greenBilinear
  calc
    pairing f (-G.greenOp hG (g - h)) =
        pairing f (G.greenOp hG h - G.greenOp hG g) := by
      congr 1
      rw [(G.greenOp hG).map_sub, neg_sub]
    _ = pairing f (G.greenOp hG h) - pairing f (G.greenOp hG g) :=
      pairing_sub_right _ _ _
    _ = pairing f (-G.greenOp hG g) - pairing f (-G.greenOp hG h) := by
      rw [pairing_neg_right, pairing_neg_right]
      ring

/-- Expansion of the Green quadratic form of a dipole. -/
theorem greenBilinear_sub_self {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.Connected)
    (f g : V → ℝ) :
    greenBilinear G hG (f - g) (f - g) =
      greenBilinear G hG f f + greenBilinear G hG g g -
        greenBilinear G hG f g - greenBilinear G hG g f := by
  calc
    greenBilinear G hG (f - g) (f - g) =
        greenBilinear G hG f (f - g) - greenBilinear G hG g (f - g) :=
      greenBilinear_sub_left G hG f g (f - g)
    _ = (greenBilinear G hG f f - greenBilinear G hG f g) -
        (greenBilinear G hG g f - greenBilinear G hG g g) := by
      simp only [greenBilinear_sub_right]
    _ = greenBilinear G hG f f + greenBilinear G hG g g -
        greenBilinear G hG f g - greenBilinear G hG g f := by ring

/-- Source form used in KP (6.13): the Green kernel difference from the origin
is half the dipole Green quadratic form. -/
theorem torusGreenKernel_eq_half_dipoleEnergy (hn : 2 < n)
    (hG : (torusGraph n hn).Connected) (x : TorusVertex n) :
    torusGreenKernel hn hG (0, 0) (0, 0) - torusGreenKernel hn hG x (0, 0) =
      (1 / 2 : ℝ) * pairing (dipole (0, 0) x)
        (-(torusGraph n hn).greenOp hG (dipole (0, 0) x)) := by
  let G := torusGraph n hn
  let δ₀ : TorusVertex n → ℝ := deltaAt (0, 0)
  let δₓ : TorusVertex n → ℝ := deltaAt x
  have hdipole : dipole (0, 0) x = δ₀ - δₓ := by
    funext v
    simp [δ₀, δₓ, dipole, deltaAt]
  have hkernel (p q : TorusVertex n) :
      greenBilinear G hG (deltaAt p) (deltaAt q) =
        torusGreenKernel hn hG p q := by
    rw [torusGreenKernel_eq_pairing]
    rfl
  have htrans : torusGreenKernel hn hG x x =
      torusGreenKernel hn hG (0, 0) (0, 0) := by
    have hzero : (0, 0) + x = x := by ext <;> simp
    simpa only [hzero] using torusGreenKernel_translation hn hG x (0, 0) (0, 0)
  have hsym := torusGreenKernel_symm hn hG x (0, 0)
  have henergy :
      pairing (dipole (0, 0) x) (-G.greenOp hG (dipole (0, 0) x)) =
        2 * (torusGreenKernel hn hG (0, 0) (0, 0) -
          torusGreenKernel hn hG x (0, 0)) := by
    rw [hdipole]
    change greenBilinear G hG (δ₀ - δₓ) (δ₀ - δₓ) = _
    rw [greenBilinear_sub_self G hG δ₀ δₓ]
    dsimp [δ₀, δₓ]
    rw [hkernel (0, 0) (0, 0), hkernel x x,
      hkernel (0, 0) x, hkernel x (0, 0)]
    rw [htrans, hsym.symm]
    ring
  rw [henergy]
  ring

end

end FroehlichSpencer.BKT.Lattice2D

end
