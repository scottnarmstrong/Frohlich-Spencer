/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Splitting off one coordinate of a finite product measure

For a finite site set `V` and a site `j₀`, Lebesgue measure on `V → ℝ` is the product of Lebesgue
measure on the other coordinates and on the coordinate `j₀`. Hence an integrable function
satisfies `∫ φ, f φ = ∫ ψ, ∫ u, f (glue j₀ ψ u)`, where `glue j₀ ψ u` takes the value `u` at `j₀`
and `ψ` elsewhere. This is the Fubini step that reduces a finite-box contour translation at one
site to a one-dimensional contour identity.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Contour

open MeasureTheory

variable {V : Type*} [DecidableEq V]

/-- The field equal to `u` at `j₀` and to `ψ` at the other sites. -/
def glue (j₀ : V) (ψ : {j // j ≠ j₀} → ℝ) (u : ℝ) : V → ℝ :=
  fun j => if h : j = j₀ then u else ψ ⟨j, h⟩

lemma glue_self (j₀ : V) (ψ : {j // j ≠ j₀} → ℝ) (u : ℝ) : glue j₀ ψ u j₀ = u := by
  simp [glue]

lemma glue_of_ne {j₀ j : V} (ψ : {j // j ≠ j₀} → ℝ) (u : ℝ) (h : j ≠ j₀) :
    glue j₀ ψ u j = ψ ⟨j, h⟩ := by
  simp [glue, h]

lemma glue_eq_update (j₀ : V) (ψ : {j // j ≠ j₀} → ℝ) (u : ℝ) :
    glue j₀ ψ u = Function.update (glue j₀ ψ 0) j₀ u := by
  funext j
  by_cases h : j = j₀
  · subst h; simp [glue_self]
  · rw [Function.update_of_ne h, glue_of_ne _ _ h, glue_of_ne _ _ h]

/-- The complement of `j₀` in the singleton-subtype sense has exactly one element. -/
instance instUniqueNotNe (j₀ : V) : Unique {j // ¬ j ≠ j₀} where
  default := ⟨j₀, fun h => h rfl⟩
  uniq := fun ⟨j, h⟩ => Subtype.ext (by simpa using h)

variable [Fintype V]

/-- Fubini along one coordinate of `V → ℝ`. -/
theorem integral_eq_integral_integral_glue (j₀ : V) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : (V → ℝ) → E} (hf : Integrable f) :
    ∫ φ, f φ = ∫ ψ : {j // j ≠ j₀} → ℝ, ∫ u : ℝ, f (glue j₀ ψ u) := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => ℝ) (fun j => j ≠ j₀) with he
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : V => ℝ) (fun j => j ≠ j₀)
  have hint : Integrable (f ∘ e.symm) (volume.prod volume) :=
    (hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding |>.mpr hf
  have h1 : ∫ φ, f φ = ∫ p, (f ∘ e.symm) p ∂(volume.prod volume) := by
    rw [← hmp.integral_comp' (f ∘ e.symm)]
    simp
  rw [h1, integral_prod _ hint]
  congr 1
  funext ψ
  have hu := volume_preserving_funUnique {j // ¬ j ≠ j₀} ℝ
  refine Eq.trans (?_ : _ = ∫ u : ℝ, (f ∘ e.symm) (ψ, (MeasurableEquiv.funUnique _ ℝ).symm u))
    ?_
  · convert ((hu.symm _).integral_comp' (fun w => (f ∘ e.symm) (ψ, w))).symm using 3
    congr 1
    exact Subsingleton.elim _ _
  congr 1
  funext u
  simp only [Function.comp_apply]
  congr 1
  funext j
  by_cases h : j = j₀
  · subst h
    simp [e, glue, MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique]
  · simp [e, glue, h, MeasurableEquiv.piEquivPiSubtypeProd]

end FroehlichSpencer.BKT.Rotator.Contour
