/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.InfiniteVolumeRegularity
public import FroehlichSpencer.Infra.Spectral.Regularity
public import FroehlichSpencer.Infra.Resolvent
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Regularity of "for all `ε ≠ 0`" resolvent events

Events `{v | ∀ ε ≠ 0, ‖G(E + iε; x, y)(v)‖ ≤ c}` (Fröhlich–Spencer (1983), Theorems 1.2 and
1.2_Λ, Fröhlich–Spencer (1983)): in finite volume the event is closed in `v` (hence
measurable, also through a restriction `v ↦ v ∘ f`); in infinite volume, for any family of `ℓ²`
solutions, it is measurable (a countable intersection, by continuity in `z`).
-/

@[expose] public section

open MeasureTheory Complex Set Matrix

namespace FroehlichSpencer.Infra

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem continuous_entry_inv_add_diagonal {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (x y : ι) :
    Continuous fun v : ι → ℝ =>
      ((A + diagonal (fun i => (v i : ℂ))) - z • (1 : Matrix ι ι ℂ))⁻¹ x y := by
  have hM : Continuous fun v : ι → ℝ =>
      (A + diagonal (fun i => (v i : ℂ))) - z • (1 : Matrix ι ι ℂ) :=
    (continuous_add_diagonal_comp A (id : ι → ι)).sub continuous_const
  have h : ∀ v : ι → ℝ, ((A + diagonal (fun i => (v i : ℂ))) - z • (1 : Matrix ι ι ℂ))⁻¹ x y =
      (((A + diagonal (fun i => (v i : ℂ))) - z • (1 : Matrix ι ι ℂ)).det)⁻¹ *
        ((A + diagonal (fun i => (v i : ℂ))) - z • (1 : Matrix ι ι ℂ)).adjugate x y := by
    intro v
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  simp_rw [h]
  refine Continuous.mul (hM.matrix_det.inv₀ fun v => ?_) (hM.matrix_adjugate.matrix_elem x y)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (isHermitian_add_diagonal hA v) z hz)).ne_zero

/-- The finite-volume event `∀ ε ≠ 0, ‖G(E + iε; x, y)‖ ≤ c` is closed in the potential. -/
theorem isClosed_setOf_forall_norm_inv_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (E : ℝ)
    (x y : ι) (c : ℝ) :
    IsClosed {v : ι → ℝ | ∀ ε : ℝ, ε ≠ 0 →
      ‖((A + diagonal (fun i => (v i : ℂ))) - ((E : ℂ) + ε * I) • (1 : Matrix ι ι ℂ))⁻¹ x y‖
        ≤ c} := by
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun ε => isClosed_iInter fun hε => ?_
  refine isClosed_le (continuous_norm.comp (continuous_entry_inv_add_diagonal hA ?_ x y))
    continuous_const
  simpa using hε

/-- The finite-volume event is measurable, also through a restriction `v ↦ v ∘ f`. -/
theorem measurableSet_setOf_forall_norm_inv_le_comp {J : Type*} {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ι → J) (E : ℝ) (x y : ι) (c : ℝ) :
    MeasurableSet {v : J → ℝ | ∀ ε : ℝ, ε ≠ 0 →
      ‖((A + diagonal (fun i => (v (f i) : ℂ))) - ((E : ℂ) + ε * I) • (1 : Matrix ι ι ℂ))⁻¹ x y‖
        ≤ c} := by
  have hm : Measurable fun v : J → ℝ => fun i => v (f i) :=
    Measurable.of_eval fun i => measurable_pi_apply (f i)
  exact (isClosed_setOf_forall_norm_inv_le hA E x y c).measurableSet.preimage hm

end Finite

section Infinite

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

/-- The infinite-volume event `∀ ε ≠ 0, ‖Ψ(E + iε)(x)‖ ≤ c` is measurable for any family of
`ℓ²` solutions. Here `Ψ v z` is the column with source `y`, i.e. `G(z; ·, y)`, so the event is
about `G(E + iε; x, y)`; for an entry `G(0, x)` take source `y := x` and evaluation point `0`. -/
theorem measurableSet_setOf_forall_norm_le_of_forall_eq_single [Countable X]
    (ha : ∀ x y, a y x = star (a x y)) (hfin : ∀ x, {y | a x y ≠ 0}.Finite)
    (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K) (E : ℝ) (y x : X) (c : ℝ)
    {Ψ : (X → ℝ) → ℂ → X → ℂ}
    (hΨ : ∀ v z, z.im ≠ 0 → Memℓp (Ψ v z) 2 ∧
      ∀ x', ∑' w, a x' w * Ψ v z w + ((v x' : ℂ) - z) * Ψ v z x' = (Pi.single y 1 : X → ℂ) x') :
    MeasurableSet {v : X → ℝ | ∀ ε : ℝ, ε ≠ 0 → ‖Ψ v ((E : ℂ) + ε * I) x‖ ≤ c} := by
  have key : ∀ v : X → ℝ, (∀ ε : ℝ, ε ≠ 0 → ‖Ψ v ((E : ℂ) + ε * I) x‖ ≤ c) ↔
      ∀ q : ℚ, q ≠ 0 → ‖Ψ v ((E : ℂ) + ((q : ℝ) : ℂ) * I) x‖ ≤ c := by
    intro v
    refine ⟨fun h q hq => h _ (by exact_mod_cast hq), fun h ε hε => ?_⟩
    have hcont : ContinuousOn (fun ε : ℝ => ‖Ψ v ((E : ℂ) + ε * I) x‖) {ε | ε ≠ 0} := by
      refine continuous_norm.comp_continuousOn ?_
      refine (continuousOn_of_forall_eq_single ha hfin hK v y x
        (Ψ := Ψ v) fun z hz => hΨ v z hz).comp (by fun_prop) ?_
      intro t ht
      simpa using ht
    by_contra hlt
    push Not at hlt
    have hat : ContinuousAt (fun ε : ℝ => ‖Ψ v ((E : ℂ) + ε * I) x‖) ε :=
      hcont.continuousAt (isOpen_ne.mem_nhds hε)
    have h1 : {t : ℝ | c < ‖Ψ v ((E : ℂ) + t * I) x‖} ∈ nhds ε :=
      hat.eventually (lt_mem_nhds hlt)
    have h2 : {t : ℝ | t ≠ 0} ∈ nhds ε := isOpen_ne.mem_nhds hε
    obtain ⟨V, hV, hVo, hεV⟩ := mem_nhds_iff.1 (Filter.inter_mem h1 h2)
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hVo ⟨ε, hεV⟩
    have hq' := hV hq
    have hq0 : q ≠ 0 := by have := hq'.2; simp only [mem_ofPred_eq] at this; exact_mod_cast this
    exact absurd (h q hq0) (not_le.2 hq'.1)
  simp_rw [key]
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_
  have hz : (((E : ℂ) + ((q : ℝ) : ℂ) * I)).im ≠ 0 := by
    simpa using hq
  exact measurableSet_le
    (continuous_norm.measurable.comp
      (measurable_of_forall_eq_single ha hfin hK hz y x
        (Ψ := fun v => Ψ v ((E : ℂ) + ((q : ℝ) : ℂ) * I)) fun v => hΨ v _ hz))
    measurable_const

end Infinite

end FroehlichSpencer.Infra
