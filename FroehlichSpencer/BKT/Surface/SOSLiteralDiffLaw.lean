/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Sum
public import FroehlichSpencer.BKT.Surface.SOSInterpolation
public import FroehlichSpencer.BKT.Surface.SquareZero

/-! # FS81's solid-on-solid state (7.16) in a box: the law of the height differences -/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81's solid-on-solid state (7.16) (§7.2, J p. 590) for a finite region `A ⊂ ℤ²` inside the box
`Ω_R = [-R, R]²` (`φ = 0` off `Ω_R`, the zero-exterior measure `dμ_{I_β,Ω}`), read through the
height differences `φ(z) - φ(w)`, `z ∈ A`, from a base point `w ∈ A`. The comb
`∏_{j ∈ A}[1 + 2 ∑_{q ≥ 1} cos (2πq φ(j))]` is the Dirac comb `∑_{n ∈ ℤ} δ(φ(j) - n)`, so the
heights `n : A → ℤ` on `A` are integers, and the heights `y` on `Ω_R ∖ A` are integrated against
Lebesgue measure. The box site `x` of `Fin (2R + 1) × Fin (2R + 1)` is the plane site
`(x₁ - R, x₂ - R)`; the bonds `|i - j| = 1`, `i ∈ Ω_R` are the edges of the wired box
`squareZero (2R + 1)` (each once; the wired vertex carries the height `0`), each carrying `I_β`
(`sosInterpolation`, (C.1)). The measure gives the difference configuration
`d = n - n(w)` the mass `∑_{n : n - n(w) = d} ∫ ∏_e I_β(∇φ_{n,y}(e)) dy`, divided by the total mass;
`0 < β ≤ 1`. The comb is inserted in each finite box before taking limit points. -/
noncomputable def sosLiteralDiffLaw (β : ℝ) (hβ : 0 < β) (_hβ1 : β ≤ 1) (A : Finset (ℤ × ℤ))
    (w : ℤ × ℤ) (hw : w ∈ A) (R : ℕ)
    (_hA : A ⊆ Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R) : Measure (A → ℤ) :=
  let plane : Fin (2 * R + 1) × Fin (2 * R + 1) → ℤ × ℤ :=
    fun x => (((x.1 : ℕ) : ℤ) - R, ((x.2 : ℕ) : ℤ) - R)
  let field : (A → ℤ) → ({x // plane x ∉ A} → ℝ) → Fin (2 * R + 1) × Fin (2 * R + 1) → ℝ :=
    fun n y x => if h : plane x ∈ A then (n ⟨plane x, h⟩ : ℝ) else y ⟨x, h⟩
  let mass : (A → ℤ) → ℝ≥0∞ := fun n => ∫⁻ y, ENNReal.ofReal (∏ e, sosInterpolation β hβ
      (((squareZero (2 * R + 1)).src e).elim 0 (field n y) -
        ((squareZero (2 * R + 1)).tgt e).elim 0 (field n y)))
  let μ : Measure (A → ℤ) := Measure.sum fun n : A → ℤ =>
    mass n • Measure.dirac (fun z => n z - n ⟨w, hw⟩)
  (μ Set.univ)⁻¹ • μ

end FroehlichSpencer.BKT

end
