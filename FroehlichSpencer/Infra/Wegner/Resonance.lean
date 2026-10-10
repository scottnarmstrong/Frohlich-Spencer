/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Wegner.Gershgorin
public import FroehlichSpencer.Infra.Wegner.Averaging

/-!
# Resonance events: measurability, locality, and the combined Wegner/Gershgorin bound

For `H(v) = A + diagonal (v|_Λ)`, the resonance event
`{v | ∃ i, |λ_i(v) - E| ≤ κ}` is measurable, depends only on the coordinates in `Λ`, and has
`productMeasure μ`-probability at most the minimum of the Wegner bound
`ρ · 2κ · |Λ|` and the Gershgorin bound `|Λ| μ {t | |t - E| ≤ K + κ}`
(Fröhlich–Spencer (1983), Appendix C, Fröhlich–Spencer (1983)).
-/

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ENNReal

namespace FroehlichSpencer.Infra

variable {ι : Type*} [DecidableEq ι] {Λ : Finset ι} {A : Matrix Λ Λ ℂ}

theorem measurableSet_exists_abs_eigenvalues_sub_le (hA : A.IsHermitian) (E κ : ℝ) :
    MeasurableSet {v : ι → ℝ |
      ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E| ≤ κ} := by
  have : {v : ι → ℝ | ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E|
      ≤ κ} = ⋃ i, (fun v : ι → ℝ =>
        (isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i) ⁻¹' {t | |t - E| ≤ κ} := by
    ext v; simp
  rw [this]
  exact MeasurableSet.iUnion fun i =>
    measurable_eigenvalues (measurable_add_diagonal_comp A (Subtype.val : Λ → ι))
      (fun v => isHermitian_add_diagonal hA fun x : Λ => v x) i
      (measurableSet_le (by fun_prop) measurable_const)

theorem dependsOn_exists_abs_eigenvalues_sub_le (hA : A.IsHermitian) (E κ : ℝ) :
    DependsOn (Λ : Set ι) {v : ι → ℝ |
      ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E| ≤ κ} := by
  refine dependsOn_of_measurable_of_invariant (measurableSet_exists_abs_eigenvalues_sub_le hA E κ)
    fun v w hvw => ?_
  have h : (fun x : Λ => v x) = fun x : Λ => w x := funext fun x => hvw x x.2
  have key : ∀ p q : Λ → ℝ, p = q → ((∃ i, |(isHermitian_add_diagonal hA p).eigenvalues i - E|
      ≤ κ) ↔ ∃ i, |(isHermitian_add_diagonal hA q).eigenvalues i - E| ≤ κ) := by
    intro p q hpq
    subst hpq
    exact Iff.rfl
  exact key _ _ h

theorem productMeasure_exists_abs_eigenvalues_sub_le_le_min (hA : A.IsHermitian) {K : ℝ}
    (hK : ∀ x, ∑ y, ‖A x y‖ ≤ K) (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞}
    {ρ : ℝ≥0∞} (hμ : μ = volume.withDensity g) (hg : ∀ᵐ t ∂(volume : Measure ℝ), g t ≤ ρ)
    (hρ : ρ ≠ ⊤) (E κ : ℝ) :
    productMeasure μ {v : ι → ℝ |
        ∃ i, |(isHermitian_add_diagonal hA fun x : Λ => v x).eigenvalues i - E| ≤ κ} ≤
      min (ρ * ENNReal.ofReal (2 * κ) * Λ.card) (Λ.card * μ {t | |t - E| ≤ K + κ}) :=
  le_min (productMeasure_exists_abs_eigenvalues_sub_le_le hA μ hμ hg hρ E κ)
    (productMeasure_exists_abs_eigenvalues_sub_le_le_card_mul hA hK μ E κ)

end FroehlichSpencer.Infra
