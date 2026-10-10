/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Integral duality for an exact integer complex

For an integral exact-one complex, the integer co-closed lattice is the
character lattice of the integer image of the second differential. This is
the algebraic lattice identification needed before applying finite Poisson
summation; it does not assume a graph structure on the middle carrier.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

/-- An exact integer complex at its middle module. -/
structure IntegerExactOneComplex (V E P : Type*)
    [AddCommGroup V] [Module ℤ V]
    [AddCommGroup E] [Module ℤ E]
    [AddCommGroup P] [Module ℤ P] where
  d₀ : V →ₗ[ℤ] E
  d₁ : E →ₗ[ℤ] P
  complex : d₁.comp d₀ = 0
  exactOne : LinearMap.ker d₁ ≤ LinearMap.range d₀

namespace IntegerExactOneComplex

variable {V E P : Type*}
    [AddCommGroup V] [Module ℤ V]
    [AddCommGroup E] [Module ℤ E]
    [AddCommGroup P] [Module ℤ P]
    (C : IntegerExactOneComplex V E P)


/-- Exactness at the middle term, written as equality of the kernel and
preceding image. -/
theorem kernel_eq_image : LinearMap.ker C.d₁ = LinearMap.range C.d₀ := by
  apply le_antisymm C.exactOne
  intro x hx
  rcases hx with ⟨v, rfl⟩
  apply LinearMap.mem_ker.mpr
  have h := congrArg (fun f : V →ₗ[ℤ] P => f v) C.complex
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

/-- Integer co-closed functionals on the middle module. They annihilate the
gauge directions `range d₀`, equivalently `ker d₁` by exactness. -/
abbrev IntegerCoClosed := (LinearMap.ker C.d₁).dualAnnihilator


/-- The same co-closed lattice, described as the annihilator of the actual
gauge image. -/
theorem integerCoClosed_eq_gaugeAnnihilator :
    C.IntegerCoClosed = (LinearMap.range C.d₀).dualAnnihilator := by
  rw [← C.kernel_eq_image]

end IntegerExactOneComplex

end FroehlichSpencer.FS82.XY
