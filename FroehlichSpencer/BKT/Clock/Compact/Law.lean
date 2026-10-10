/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.IntegerTranslation
import Mathlib.Tactic

/-!
# The compact clock law on a finite vertex set

FS81 (7.9), the clock edge law after the change of variables `φ = n θ`, on a general finite vertex
set. the periodic clock model's `clockBoxLaw` lives on `Fin d → ℝ`; here it is transported along `V ≃ Fin |V|`
(`siteEquiv`), so that it can be used on KP's square domains `Fin L × Fin L`.

* `clockLaw β n G`: the normalized product of the edge weights `exp(β cos(∇φ/n))` on the box
  `(−πn, πn]^V`. It is a probability measure for `β ≥ 0`, `n > 0` (`isProbabilityMeasure_clockLaw`).
* `IsClockCompatible n τ`: the charges with `n τ(j) ∈ ℤ`, whose characters are periodic on the
  compact box.
* **`integral_clockLaw_characterTranslation`**: the compact clock model's compact character translation
  `∫ χ_τ dμ = e^{−⟨a, τ⟩} ∫ χ_τ R_{∇a}(∇φ) dμ`, for every compatible `τ` (no neutrality needed)
  and every real `a` (no strip condition).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Compact

open MeasureTheory Complex
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Generic (edgeRatio)
open FroehlichSpencer.BKT.Reduction (gffCharacter norm_gffCharacter)

variable {V : Type*} [Fintype V] {E : Type*} [Fintype E]

/-! ### The clock law on a finite vertex set -/

/-- The relabeling of a multigraph along a bijection of its vertices. -/
def relabelGraph {W : Type*} (G : Multigraph V E) (e : V ≃ W) : Multigraph W E where
  src x := e (G.src x)
  tgt x := e (G.tgt x)
  src_ne_tgt x h := G.src_ne_tgt x (e.injective h)

/-- The ordered relabeling of the sites, `V ≃ Fin |V|`. -/
abbrev siteEquiv (V : Type*) [Fintype V] : V ≃ Fin (Fintype.card V) := Fintype.equivFin V

/-- The relabeled field `φ ∘ e`. -/
def pullField (V : Type*) [Fintype V] (φ : Fin (Fintype.card V) → ℝ) : V → ℝ :=
  fun v => φ (siteEquiv V v)

/-- `pullField` as a measurable equivalence. -/
def pullFieldEquiv (V : Type*) [Fintype V] : (Fin (Fintype.card V) → ℝ) ≃ᵐ (V → ℝ) where
  toFun := pullField V
  invFun ψ j := ψ ((siteEquiv V).symm j)
  left_inv φ := by funext j; simp [pullField]
  right_inv ψ := by funext v; simp [pullField]
  measurable_toFun := by
    change Measurable fun φ : Fin (Fintype.card V) → ℝ => fun v => φ (siteEquiv V v)
    fun_prop
  measurable_invFun := by
    change Measurable fun ψ : V → ℝ => fun j => ψ ((siteEquiv V).symm j)
    fun_prop

theorem measurableEmbedding_pullField : MeasurableEmbedding (pullField V) := by
  have h : (pullFieldEquiv V : (Fin (Fintype.card V) → ℝ) → (V → ℝ)) = pullField V := rfl
  rw [← h]
  exact (pullFieldEquiv V).measurableEmbedding

/-- **The compact-angle clock law on a finite vertex set** (FS81 (7.9) after `φ = n θ`): the
normalized product of the edge weights `exp(β cos(∇φ/n))` on the box `(−πn, πn]^V`, transported
from the ordered box law `clockBoxLaw` along `V ≃ Fin |V|`. -/
def clockLaw (β n : ℝ) (G : Multigraph V E) : Measure (V → ℝ) :=
  (clockBoxLaw β n (relabelGraph G (siteEquiv V))).map (pullField V)

theorem isProbabilityMeasure_clockLaw {β n : ℝ} (G : Multigraph V E) (hβ : 0 ≤ β)
    (hn : 0 < n) : IsProbabilityMeasure (clockLaw β n G) := by
  have := isProbabilityMeasure_clockBoxLaw (relabelGraph G (siteEquiv V)) hβ hn
  unfold clockLaw
  infer_instance

theorem integral_clockLaw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (β n : ℝ)
    (G : Multigraph V E) (f : (V → ℝ) → F) :
    ∫ φ, f φ ∂clockLaw β n G =
      ∫ φ, f (pullField V φ) ∂clockBoxLaw β n (relabelGraph G (siteEquiv V)) :=
  measurableEmbedding_pullField.integral_map _

omit [Fintype E] in
theorem grad_pullField (G : Multigraph V E) (φ : Fin (Fintype.card V) → ℝ) :
    G.grad (pullField V φ) = (relabelGraph G (siteEquiv V)).grad φ := rfl

/-- The charges whose characters are periodic on the compact box: `n τ(j) ∈ ℤ`. -/
def IsClockCompatible (n : ℝ) (τ : V → ℝ) : Prop :=
  ∀ j, ∃ k : ℤ, n * τ j = k

theorem gffCharacter_pullField (τ : V → ℝ) (φ : Fin (Fintype.card V) → ℝ) :
    gffCharacter τ (pullField V φ) = gffCharacter (fun j => τ ((siteEquiv V).symm j)) φ := by
  unfold gffCharacter pullField
  congr 2
  rw [← (siteEquiv V).sum_comp fun j => (φ j : ℂ) * (τ ((siteEquiv V).symm j) : ℂ)]
  simp only [Equiv.symm_apply_apply]

/-- **The compact character translation on a finite vertex set**: for a charge with
`n τ(j) ∈ ℤ` (no neutrality needed) and every real shift `a`,
`∫ χ_τ dμ = e^{−⟨a, τ⟩} ∫ χ_τ R_{∇a}(∇φ) dμ`
(the compact clock model's `integral_clockBoxLaw_characterTranslation_compatible`,
transported). -/
theorem integral_clockLaw_characterTranslation {n β : ℝ} (hn : 0 < n) (hβ : 0 ≤ β)
    (G : Multigraph V E) (τ a : V → ℝ) (hτ : IsClockCompatible n τ) :
    ∫ φ, gffCharacter τ φ ∂clockLaw β n G =
      Complex.exp (-((∑ j, a j * τ j : ℝ) : ℂ)) *
        ∫ φ, gffCharacter τ φ * edgeRatio (clockEdgeWeight β n) (G.grad a) (G.grad φ)
          ∂clockLaw β n G := by
  set e := siteEquiv V
  set G' := relabelGraph G e
  set τ' : Fin (Fintype.card V) → ℝ := fun j => τ (e.symm j)
  set a' : Fin (Fintype.card V) → ℝ := fun j => a (e.symm j)
  have hτ' : ClockCompatibleCharge n τ' := fun j => hτ (e.symm j)
  have hga : G'.grad a' = G.grad a := by
    funext x
    simp only [Multigraph.grad, G', relabelGraph, a', Equiv.symm_apply_apply]
  have hsum : ∑ j, a' j * τ' j = ∑ j, a j * τ j :=
    e.symm.sum_comp fun j => a j * τ j
  rw [integral_clockLaw, integral_clockLaw]
  simp_rw [gffCharacter_pullField, grad_pullField]
  have key := integral_clockBoxLaw_characterTranslation_compatible hn hβ (G := G') τ' a' hτ'
  rw [hga, hsum] at key
  exact key

end FroehlichSpencer.BKT.Clock.Compact

end
