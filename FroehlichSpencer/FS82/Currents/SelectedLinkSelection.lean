/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Eight-class selection for one-link decoupling

A color class in a finite support carries at least one eighth of its nonnegative
mass. If conflicts always have distinct colors, that class is conflict-free.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Currents.SelectedLinkSelection

variable {E : Type*}

/-- The links of `S` having a specified color. -/
def colorClass (S : Finset E) (color : E → Fin 8) (c : Fin 8) : Finset E :=
  S.filter fun e => color e = c

/-- The mass carried by one color class. -/
def classMass (S : Finset E) (color : E → Fin 8) (w : E → ℝ) (c : Fin 8) : ℝ :=
  ∑ e ∈ colorClass S color c, w e

/-- Summing class masses recovers the total support mass. -/
theorem classMass_sum (S : Finset E) (color : E → Fin 8) (w : E → ℝ) :
    (∑ c : Fin 8, classMass S color w c) = ∑ e ∈ S, w e := by
  simp only [classMass, colorClass]
  exact Finset.sum_fiberwise S color w

/-- Some color class carries at least one eighth of the total nonnegative mass. -/
theorem exists_colorClass_large (S : Finset E) (color : E → Fin 8) (w : E → ℝ)
    :
    ∃ c : Fin 8, (∑ e ∈ S, w e) / 8 ≤ classMass S color w c := by
  classical
  let mass : Fin 8 → ℝ := classMass S color w
  obtain ⟨c, _, hmax⟩ := Finset.exists_max_image Finset.univ mass Finset.univ_nonempty
  have hsum : (∑ c : Fin 8, mass c) = ∑ e ∈ S, w e := by
    exact classMass_sum S color w
  have hbound : (∑ e ∈ S, w e) ≤ 8 * mass c := by
    calc
      (∑ e ∈ S, w e) = ∑ d : Fin 8, mass d := hsum.symm
      _ ≤ ∑ _d : Fin 8, mass c := Finset.sum_le_sum fun d _ => hmax d (Finset.mem_univ d)
      _ = 8 * mass c := by simp [Fintype.card_fin]
  refine ⟨c, ?_⟩
  change (∑ e ∈ S, w e) / 8 ≤ mass c
  linarith

/-- A maximum-mass color class is conflict-free when every conflict has distinct colors. -/
theorem selectedClass_noConflict (S : Finset E) (color : E → Fin 8) (w : E → ℝ)
    (conflict : E → E → Prop)
    (hcolor : ∀ ⦃e f⦄, conflict e f → color e ≠ color f)
    :
    ∃ c : Fin 8,
      (∑ e ∈ S, w e) / 8 ≤ classMass S color w c ∧
      ∀ e ∈ colorClass S color c, ∀ f ∈ colorClass S color c, ¬ conflict e f := by
  obtain ⟨c, hc⟩ := exists_colorClass_large S color w
  refine ⟨c, hc, ?_⟩
  intro e he f hf hconf
  have hec : color e = c := (Finset.mem_filter.mp he).2
  have hfc : color f = c := (Finset.mem_filter.mp hf).2
  exact (hcolor hconf) (hec.trans hfc.symm)

end FroehlichSpencer.FS82.Currents.SelectedLinkSelection

end
